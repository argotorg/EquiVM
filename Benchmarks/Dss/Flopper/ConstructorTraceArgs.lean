import Benchmarks.Dss.Flopper.ConstructorTraceDefaults

/-!
# MakerDAO/Sky DSS Flopper constructor argument-copy trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flopper

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem flopperCtorArgCopyTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat gem : AccountAddress)
    (h : RD (flopperCtorCode vat gem) I g s0 ⟨91⟩ []
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C) :
    ∃ k' C', RD (flopperCtorCode vat gem) I g s0 ⟨111⟩
      [(UInt256.ofNat (flopperCtorCode vat gem).size).sub ⟨5000⟩, ⟨128⟩]
      (flopperCtorArgsMem vat gem) (UInt256.ofNat 6) rdata acc k' C' := by
  have hcopy : (flopperCtorCode vat gem).write 5000 solcFreePtrMem 128 64 =
      flopperCtorCopiedMem vat gem := by
    rfl
  have hfree :
      (((UInt256.ofNat (flopperCtorCode vat gem).size).sub ⟨5000⟩ +
          (⟨128⟩ : UInt256)).toByteArray).write
          0 (flopperCtorCopiedMem vat gem) 64 32 =
        flopperCtorArgsMem vat gem := by
    rw [flopperCtorArgLen_eq]
    rfl
  have rd111 := flopper_ctor_run h with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3)
      (by flopper_ctor_decode) mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push2 ⟨5000⟩, codesize, sub, dup1, push2 ⟨5000⟩, dup4,
    raw codecopy
      9
      (flopperCtorCopiedMem vat gem) (UInt256.ofNat 6)
      (by flopper_ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
        rw [flopperCtorArgLen_eq]
        decide)
      (by
        rw [flopperCtorArgLen_eq]
        exact hcopy)
      (by rw [flopperCtorArgLen_eq]; decide) (by evm_ov),
    dup2, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (flopperCtorArgsMem vat gem) (UInt256.ofNat 6)
      (by flopper_ctor_decode) mem_cost hfree (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [show (⟨91⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 3 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ = ⟨111⟩
        from by native_decide] using rd111⟩

set_option maxHeartbeats 1000000 in
theorem flopperCtorArgSizeGuardTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat gem : AccountAddress)
    (h : RD (flopperCtorCode vat gem) I g s0 ⟨111⟩
      [(UInt256.ofNat (flopperCtorCode vat gem).size).sub ⟨5000⟩, ⟨128⟩]
      (flopperCtorArgsMem vat gem) (UInt256.ofNat 6) rdata acc k C) :
    ∃ k' C', RD (flopperCtorCode vat gem) I g s0 ⟨134⟩
      [EVM.word gem.val, EVM.word vat.val, ⟨32⟩]
      (flopperCtorArgsMem vat gem) (UInt256.ofNat 6) rdata acc k' C' := by
  have rdBeforeJump := flopper_ctor_run h with [
    push1 ⟨64⟩, dup2, lt, iszero, push2 ⟨124⟩]
  have rd124 := rdBeforeJump.jumpiT (by flopper_ctor_decode)
    (by rw [flopperCtorArgLen_eq]; decide) (by flopper_ctor_jd) (by evm_ov)
  have rd128 := flopper_ctor_run rd124 with [
    jumpdest, pop, dup1,
    raw mload 0 (EVM.word vat.val) (UInt256.ofNat 6)
      (by flopper_ctor_decode) mem_cost (flopperCtorArgsMem_mload_vat vat gem)
      (by decide) (by evm_ov)]
  have rd134 := flopper_ctor_run rd128 with [
    push1 ⟨32⟩, swap2, dup3, add,
    raw mload 0 (EVM.word gem.val) (UInt256.ofNat 6)
      (by flopper_ctor_decode) mem_cost (flopperCtorArgsMem_mload_gem vat gem)
      (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [show (⟨124⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨134⟩
        from by native_decide] using rd134⟩

theorem flopperCtorArgsReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress)
    (hcode : I.code = flopperCtorCode vat gem)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (flopperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨134⟩
      [EVM.word gem.val, EVM.word vat.val, ⟨32⟩]
      (flopperCtorArgsMem vat gem) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts, flopperCtorAfterKicksMap σ I) k C := by
  obtain ⟨_, _, rd91⟩ :=
    flopperCtorGuardSuccessReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat gem hcode hperm hwv
  obtain ⟨_, _, rd111⟩ := flopperCtorArgCopyTrace vat gem rd91
  exact flopperCtorArgSizeGuardTrace vat gem rd111

end Benchmarks.Dss.Flopper
