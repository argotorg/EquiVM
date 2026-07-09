import Examples.VyperERC20.TransferFromStoresAfterFromLoadKeyReady

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAfterFromLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨493⟩
      [transferFromSelectorWord]
      (transferFromAllowanceScratchMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
        (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨508⟩
      [transferFromFromBalanceRawAfterAllowance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g),
        transferFromFromSlot I, transferFromSelectorWord]
      (transferFromFromBalanceHashMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := by
  let evm0 := initState cA gh bl σ σ₀ g A I
  let evm1 := transferFromAfterAllowanceState evm0 I
  have hreach493 :
      ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨493⟩
        [transferFromSelectorWord]
        (transferFromAllowanceScratchMem
          (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
          (transferFromCurrentAllowanceRaw σ I))
        (UInt256.ofNat 5) ByteArray.empty
        (cA, transferFromAccountMapAfterAllowanceI σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := by
    simpa [transferFromAccountMapAfterAllowanceI, transferFromAllowanceDebitI] using hreach
  obtain ⟨k497, C497, rd497⟩ := erc20X_transferFromAfterFromLoadSetup
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hreach493
  have hreach497 :
      ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨497⟩
        [transferFromFromWord I, ⟨0⟩, transferFromSelectorWord]
        (transferFromAllowanceScratchMemI σ I)
        (UInt256.ofNat 5) ByteArray.empty
        (cA, transferFromAccountMapAfterAllowanceI σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)) k C := by
    exact ⟨k497, C497, by simpa [transferFromAllowanceScratchMemI] using rd497⟩
  obtain ⟨k499, C499, rd499⟩ := erc20X_transferFromAfterFromLoadKeyReady
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hreach497
  have hslot := transferFromFromBalanceKeccakSlot I hcanonFrom
    (transferFromCurrentAllowanceRaw σ I)
  have hfromLoadRaw :
      transferFromFromBalanceRawAfterAllowance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g) =
        transferFromFromBalanceWord evm1 I := by
    simpa [evm0, evm1] using
      (transferFromFromBalanceRawAfterAllowance_initState (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
  have rd500 := rd499.mstore 0
    (transferFromFromBalanceKeyMemI σ I)
    (UInt256.ofNat 5)
    (by native_decide) mem_cost rfl (by decide) (by evm_ov)
  have rd501 := rd500.push0 (by native_decide) (by evm_ov)
  have rd502 := rd501.mstore 0
    (transferFromFromBalanceHashMemI σ I)
    (UInt256.ofNat 5)
    (by native_decide) mem_cost rfl (by decide) (by evm_ov)
  have rd504 := rd502.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd505 := rd504.push0 (by native_decide) (by evm_ov)
  have rd506 := rd505.keccak256 0
    (transferFromFromSlot I)
    (UInt256.ofNat 5)
    (by native_decide) mem_cost hslot (by decide) (by evm_ov)
  have rd507 := rd506.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k1, C1, rdAfterLoad⟩ := rd507.sload
    (by vyper_erc20_transferFrom_decode) (by evm_ov)
  exact ⟨_, _, by
    simpa [evm0, evm1, hfromLoadRaw] using rdAfterLoad⟩

end VyperERC20
