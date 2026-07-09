import Benchmarks.Dss.Cat.ConstructorBase

/-!
# MakerDAO/Sky DSS Cat constructor argument and guard traces
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cat

set_option maxRecDepth 2000000

theorem catInitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress)
    (hcode : I.code = catCtorCode vat)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (catCtorCode vat) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (catCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd12 := cat_ctor_run rd0 with [
    push1 ⟨128⟩, push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3)
      (by cat_ctor_decode) mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push2 ⟨16⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact cat_ctor_run rd12 with [
    push1 ⟨0⟩, dup1,
    raw rev 0 (by cat_ctor_decode) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem catCtorArgCopyTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat : AccountAddress)
    (h : RD (catCtorCode vat) I g s0 ⟨18⟩ []
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C) :
    ∃ k' C', RD (catCtorCode vat) I g s0 ⟨38⟩
      [(UInt256.ofNat (catCtorCode vat).size).sub ⟨3999⟩, ⟨128⟩]
      (catCtorArgFreeMem vat) (UInt256.ofNat 5) rdata acc k' C' := by
  have hcopy : (catCtorCode vat).write 3999 solcFreePtrMem 128 32 = catCtorArgMem vat := by
    rfl
  have hfree :
      (((UInt256.ofNat (catCtorCode vat).size).sub ⟨3999⟩ + (⟨128⟩ : UInt256)).toByteArray).write
          0 (catCtorArgMem vat) 64 32 =
        catCtorArgFreeMem vat := by
    rw [catCtorArgLen_eq]
    rfl
  have rd38 := cat_ctor_run h with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3)
      (by cat_ctor_decode) mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push2 ⟨3999⟩, codesize, sub, dup1, push2 ⟨3999⟩, dup4,
    raw codecopy
      6
      (catCtorArgMem vat) (UInt256.ofNat 5)
      (by cat_ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
        rw [catCtorArgLen_eq]
        decide)
      (by
        rw [catCtorArgLen_eq]
        exact hcopy)
      (by rw [catCtorArgLen_eq]; decide) (by evm_ov),
    dup2, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (catCtorArgFreeMem vat) (UInt256.ofNat 5)
      (by cat_ctor_decode) mem_cost hfree (by decide) (by evm_ov)]
  have rd38' : RD (catCtorCode vat) I g s0 ⟨38⟩
      [(UInt256.ofNat (catCtorCode vat).size).sub ⟨3999⟩, ⟨128⟩]
      (catCtorArgFreeMem vat) (UInt256.ofNat 5) rdata acc
      (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (C + 3 + (0 + 3) + 3 + 2 + 3 + 3 + 3 + 3 +
        (6 + (GasConstants.Gverylow + GasConstants.Gcopy *
          ((((UInt256.ofNat (catCtorCode vat).size).sub ⟨3999⟩).toNat + 31) / 32))) +
        3 + 3 + 3 + 3 + (0 + 3)) := by
    simpa [
      show (⟨18⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 3 +
            ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ = ⟨38⟩
        from by native_decide] using rd38
  exact ⟨_, _, rd38'⟩

set_option maxHeartbeats 1000000 in
theorem catCtorArgSizeGuardTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat : AccountAddress)
    (h : RD (catCtorCode vat) I g s0 ⟨38⟩
      [(UInt256.ofNat (catCtorCode vat).size).sub ⟨3999⟩, ⟨128⟩]
      (catCtorArgFreeMem vat) (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD (catCtorCode vat) I g s0 ⟨54⟩
      [EVM.word vat.val] (catCtorArgFreeMem vat) (UInt256.ofNat 5) rdata acc k' C' := by
  have rdBeforeJump := cat_ctor_run h with [
    push1 ⟨32⟩, dup2, lt, iszero, push2 ⟨51⟩]
  have rd51 := rdBeforeJump.jumpiT (by cat_ctor_decode)
    (by rw [catCtorArgLen_eq]; decide) (by cat_ctor_jd) (by evm_ov)
  have rd54 := cat_ctor_run rd51 with [
    raw jumpdest (by cat_ctor_decode) (by evm_ov),
    pop,
    raw mload 0 (EVM.word vat.val) (UInt256.ofNat 5)
      (by cat_ctor_decode) mem_cost (catCtorArgFreeMem_mload128 vat)
      (by decide) (by evm_ov)]
  have rd54' : RD (catCtorCode vat) I g s0 ⟨54⟩
      [EVM.word vat.val] (catCtorArgFreeMem vat) (UInt256.ofNat 5) rdata acc
      (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
      (C + 3 + 3 + 3 + 3 + 3 + 10 + 1 + 2 + (0 + 3)) := by
    simpa [show (⟨51⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨54⟩
      from by native_decide] using rd54
  exact ⟨_, _, rd54'⟩

theorem catCtorArgsReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress)
    (hcode : I.code = catCtorCode vat)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (catCtorCode vat) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨54⟩
      [EVM.word vat.val] (catCtorArgFreeMem vat) (UInt256.ofNat 5) ByteArray.empty
      (createdAccounts, σ) k C := by
  have rd8 :
      RD (catCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨8⟩
        [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (createdAccounts, σ) 6 26 := by
    exact solcGuardPrologueRD (code := catCtorCode vat) hcode
      (by cat_ctor_decode) (by cat_ctor_decode) (by cat_ctor_decode)
      (by cat_ctor_decode) (by cat_ctor_decode) (by cat_ctor_decode)
  obtain ⟨k18, C18, rd18⟩ :=
    solcGuardCallvalueZero (code := catCtorCode vat) (ctgt := ⟨16⟩) (wC := 2)
      (opC := .PUSH2) rd8 hwv (by decide)
      (by cat_ctor_decode) (by cat_ctor_decode) (by cat_ctor_decode) (by cat_ctor_decode)
      (by cat_ctor_jd)
  have rd18' :
      RD (catCtorCode vat) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨18⟩
        [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σ) k18 C18 := by
    simpa [show ((⟨16⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = ⟨18⟩ from by native_decide]
      using rd18
  obtain ⟨_, _, rd38⟩ := catCtorArgCopyTrace vat rd18'
  exact catCtorArgSizeGuardTrace vat rd38

end Benchmarks.Dss.Cat
