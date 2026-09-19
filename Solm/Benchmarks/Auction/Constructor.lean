import Solm.Benchmarks.Auction.Bytecode
import Solm.Benchmarks.Auction.Spec
import Solm.Benchmarks.Auction.Common
import Solm.Reasoning.Constructor

/-!
# Auction constructor correctness

The creation prefix enforces the nonpayable guard and returns the exact 6150-byte runtime
embedded at offset 29. It preserves the account map and created-account set.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

theorem auctionConstructorBodyCore :
    constructorEquivalence auctionConfig auctionCreationBytecode Auction.auctionContract
      auctionBytecode := by
  refine constructorEquivalence.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I args deployed hdeploy hcode _hcalldata _hperm hAccounts
  have hdeployed := emptyCtorDeployment_eq_initcode
    (cfg := auctionConfig) (contract := Auction.auctionContract) rfl rfl hdeploy
  rw [hdeployed] at hcode
  have hlen := emptyCtorDeployment_args_length
    (cfg := auctionConfig) (contract := Auction.auctionContract) rfl rfl hdeploy
  have hargs : args = [] := List.eq_nil_of_length_eq_zero hlen
  subst args
  have rd0 := RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (g := Sat256.ofUInt256 g) hcode
  have rd5 := evm_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by native_decide) mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov) ]
  have rd8 := evm_run rd5 with [callvalue, dup1, iszero]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd25 := evm_run rd8 with [
      push2 ⟨15⟩, jumpiT (by rw [hwv]; decide) (by jump_dest), jumpdest, pop,
      push2 ⟨6150⟩, dup1, push2 ⟨29⟩, push0 ]
    have rd26 := rd25.codecopy 642 auctionBytecode (UInt256.ofNat 193)
      (by native_decide) mem_cost (by native_decide) (by decide) (by evm_ov)
    have hr := evm_run rd26 with [
      push0, raw ret 0 auctionBytecode (by native_decide) mem_cost
        (by native_decide) (by evm_ov) ]
    rcases hr.xiResult hcode with hoog | ⟨g', A', hsuccess⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa using hoog)
    · have hsolm : solmCtorExec auctionConfig Auction.auctionContract [] cA gh bl σ_solm σ₀ g A I
          (.returned { contract := Auction.auctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) none) :=
        solmCtorExec.intro
          (evmState := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (argsStore := ∅) rfl rfl rfl
          (ExecFuncBody.execBlockOK
            (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ExecBlock.nil))
      exact constructorEquivalenceFor.execution hsuccess hsolm
        (ctorResultEquiv.success rfl rfl rfl hAccounts rfl)
  · have hr := evm_run rd8 with [
      push2 ⟨15⟩, jumpiNT (isZero_eq_zero_of_ne hwv),
      raw auctionRevert0 (by native_decide) (by native_decide) (by native_decide) (by evm_ov) ]
    rcases hr.xiResult hcode with hoog | ⟨g', o, hrevert⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa using hoog)
    · refine constructorEquivalenceFor.execution hrevert ?_ (ctorResultEquiv.revert rfl rfl)
      exact solmCtorExec.intro
        (evmState := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (argsStore := ∅) rfl rfl rfl (bodyReverts_nonPayable hwv)

theorem auctionConstructorCorrect :
    constructorEquivalence auctionConfig auctionCreationBytecode Auction.auctionContract
      auctionBytecode :=
  auctionConstructorBodyCore
