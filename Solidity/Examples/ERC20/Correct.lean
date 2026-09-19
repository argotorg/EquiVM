import Solidity.Examples.ERC20.TotalSupply
import Solidity.Examples.ERC20.BalanceOf
import Solidity.Examples.ERC20.Allowance
import Solidity.Examples.ERC20.Approve
import Solidity.Examples.ERC20.Transfer
import Solidity.Examples.ERC20.TransferFrom
import Solidity.Examples.ERC20.Constructor

/-!
# ERC20 — the pinned bytecode refines the Solidity specification (core relation)

The dispatcher is driven by the generic solc machinery from the Sol⁻ proof (`erc20ReachBody`,
`erc20Matches`, and the shared revert traces); each arm is handed to the per-function coupled
result.  `erc20ContractCore` combines deployment and every message call.
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace ERC20.SolidityProof

/-! ## The rejecting and non-payable branches -/

theorem erc20SolNoDispatch {cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 6 → (erc20SelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceForCore erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · have h := RDrev.specNoDispatchCore (cfg := erc20Cfg) (σ_spec := σ_spec) (g := Sat256.ofUInt256 g) hcode
      (erc20X_noMatch (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) hcode hwv hsz hsize hnm)
      (by rw [erc20Dispatches, erc20Dispatch_none hsz hnm]; rfl)
    simpa [Sat256.ofUInt256, Sat256.toUInt256] using h
  · have hshort : I.calldata.size < 4 := by omega
    have h := RDrev.specNoDispatchCore (cfg := erc20Cfg) (σ_spec := σ_spec) (g := Sat256.ofUInt256 g) hcode
      (erc20X_short (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) hcode hwv hshort)
      (by rw [erc20Dispatches, erc20Dispatch_none_short hshort]; rfl)
    simpa [Sat256.ofUInt256, Sat256.toUInt256] using h

/-- `callvalue ≠ 0`: the bytecode reverts; the spec either rejects the call (no selector) or
    dispatches to a non-payable function. -/
theorem erc20SolNonPayable {cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceForCore erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
  have hX := erc20X_callvalue_ne (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode hwv
  have rev : ∀ {e fn retTys}, selectorDispatch erc20Flat I.calldata = some e → erc20Flat.fns[e.fn]? = some fn →
      fn.decl.mutability ≠ .payable → returnAbiTys erc20Flat.types fn.decl = some retTys →
      runtimeEquivalenceForCore erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
    intro e fn retTys he hfn hne hret
    have h := RDrev.specRevertCore (cfg := erc20Cfg) (σ_spec := σ_spec) (g := Sat256.ofUInt256 g) noOracle hcode hX
      (solidityExec.nonPayable (cfg := erc20Cfg) (σ := σ_spec) he hfn hne hwv hret)
    simpa [Sat256.ofUInt256, Sat256.toUInt256] using h
  by_cases h0 : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
  · exact rev (erc20Dispatch_approve h0) erc20Flat_fns2 (by decide) rfl
  by_cases h1 : selIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩
  · exact rev (erc20Dispatch_totalSupply h1) erc20Flat_fns6 (by decide) rfl
  by_cases h2 : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩
  · exact rev (erc20Dispatch_transferFrom h2) erc20Flat_fns3 (by decide) rfl
  by_cases h3 : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
  · exact rev (erc20Dispatch_balanceOf h3) erc20Flat_fns4 (by decide) rfl
  by_cases h4 : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩
  · exact rev (erc20Dispatch_transfer h4) erc20Flat_fns1 (by decide) rfl
  by_cases h5 : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩
  · exact rev (erc20Dispatch_allowance h5) erc20Flat_fns5 (by decide) rfl
  have hnm : ∀ i, i < 6 → (erc20SelBytes i == I.calldata.extract 0 4) = false := by
    intro i hi
    interval_cases i
    · simpa [selIs, erc20SelBytes] using h0
    · simpa [selIs, erc20SelBytes] using h1
    · simpa [selIs, erc20SelBytes] using h2
    · simpa [selIs, erc20SelBytes] using h3
    · simpa [selIs, erc20SelBytes] using h4
    · simpa [selIs, erc20SelBytes] using h5
  have hd : dispatches erc20Flat I.calldata = false := by
    by_cases hsz : 4 ≤ I.calldata.size
    · rw [erc20Dispatches, erc20Dispatch_none hsz hnm]; rfl
    · rw [erc20Dispatches, erc20Dispatch_none_short (by omega)]; rfl
  have h := RDrev.specNoDispatchCore (cfg := erc20Cfg) (σ_spec := σ_spec) (g := Sat256.ofUInt256 g) hcode hX hd
  simpa [Sat256.ofUInt256, Sat256.toUInt256] using h

/-! ## Runtime -/

/-- The deployed ERC20 runtime bytecode refines the Solidity specification (accounts and return
    data), for every initial state. -/
theorem erc20RuntimeCore : runtimeEquivalenceCore erc20Cfg erc20Bytecode erc20Flat := by
  refine ⟨fun cA gh bl σ_evm σ_spec σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · by_cases h0 : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
      · exact erc20ApproveCore hcode hsize hperm hwv h0
          (erc20ReachBody 0 (by omega) ⟨100⟩ hcode hwv hsz hsize (erc20Matches 0 (by omega) hsz h0).1
            (erc20Matches 0 (by omega) hsz h0).2 (by jump_dest) (by decide)) hAccounts
      · by_cases h1 : selIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩
        · exact erc20TotalSupplyCore hcode hwv h1
            (erc20ReachBody 1 (by omega) ⟨148⟩ hcode hwv hsz hsize (erc20Matches 1 (by omega) hsz h1).1
              (erc20Matches 1 (by omega) hsz h1).2 (by jump_dest) (by decide)) hAccounts
        · by_cases h2 : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩
          · exact erc20TransferFromCore hcode hsize hperm hwv h2
              (erc20ReachBody 2 (by omega) ⟨178⟩ hcode hwv hsz hsize (erc20Matches 2 (by omega) hsz h2).1
                (erc20Matches 2 (by omega) hsz h2).2 (by jump_dest) (by decide)) hAccounts
          · by_cases h3 : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
            · exact erc20BalanceOfCore hcode hsize hwv h3
                (erc20ReachBody 3 (by omega) ⟨226⟩ hcode hwv hsz hsize (erc20Matches 3 (by omega) hsz h3).1
                  (erc20Matches 3 (by omega) hsz h3).2 (by jump_dest) (by decide)) hAccounts
            · by_cases h4 : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩
              · exact erc20TransferCore hcode hsize hperm hwv h4
                  (erc20ReachBody 4 (by omega) ⟨274⟩ hcode hwv hsz hsize (erc20Matches 4 (by omega) hsz h4).1
                    (erc20Matches 4 (by omega) hsz h4).2 (by jump_dest) (by decide)) hAccounts
              · by_cases h5 : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩
                · exact erc20AllowanceCore hcode hsize hwv h5
                    (erc20ReachBody 5 (by omega) ⟨322⟩ hcode hwv hsz hsize (erc20Matches 5 (by omega) hsz h5).1
                      (erc20Matches 5 (by omega) hsz h5).2 (by jump_dest) (by decide)) hAccounts
                · refine erc20SolNoDispatch hcode hsize hwv ?_
                  intro i hi
                  interval_cases i
                  · simpa [selIs, erc20SelBytes] using h0
                  · simpa [selIs, erc20SelBytes] using h1
                  · simpa [selIs, erc20SelBytes] using h2
                  · simpa [selIs, erc20SelBytes] using h3
                  · simpa [selIs, erc20SelBytes] using h4
                  · simpa [selIs, erc20SelBytes] using h5
    · have hshort : I.calldata.size < 4 := by omega
      have h := RDrev.specNoDispatchCore (cfg := erc20Cfg) (σ_spec := σ_spec) (g := Sat256.ofUInt256 g) hcode
        (erc20X_short (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) hcode hwv hshort)
        (by rw [erc20Dispatches, erc20Dispatch_none_short hshort]; rfl)
      simpa [Sat256.ofUInt256, Sat256.toUInt256] using h
  · exact erc20SolNonPayable hcode hwv

/-! ## The capstone -/

/-- Deployment and every message call of the pinned ERC20 bytecode refine the Solidity
    specification `ERC20.SoliditySpec.erc20`, on accounts and return data. -/
theorem erc20ContractCore : contractEquivalenceCore erc20Cfg erc20Initcode erc20Bytecode erc20Flat :=
  contractEquivalenceCore.intro erc20ConstructorCore erc20RuntimeCore

end ERC20.SolidityProof
