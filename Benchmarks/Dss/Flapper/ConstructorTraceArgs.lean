import Benchmarks.Dss.Flapper.ConstructorTraceDefaults

/-!
# MakerDAO/Sky DSS Flapper constructor argument-copy trace
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem flapperCtorArgCopyTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat gem : AccountAddress)
    (h : RD (flapperCtorCode vat gem) I g s0 ⟨79⟩ []
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C) :
    ∃ k' C', RD (flapperCtorCode vat gem) I g s0 ⟨99⟩
      [(UInt256.ofNat (flapperCtorCode vat gem).size).sub ⟨5216⟩, ⟨128⟩]
      (flapperCtorArgsMem vat gem) (UInt256.ofNat 6) rdata acc k' C' := by
  have hcopy : (flapperCtorCode vat gem).write 5216 solcFreePtrMem 128 64 =
      flapperCtorCopiedMem vat gem := by
    rfl
  have hfree :
      (((UInt256.ofNat (flapperCtorCode vat gem).size).sub ⟨5216⟩ +
          (⟨128⟩ : UInt256)).toByteArray).write
          0 (flapperCtorCopiedMem vat gem) 64 32 =
        flapperCtorArgsMem vat gem := by
    rw [flapperCtorArgLen_eq]
    rfl
  have rd99 := flapper_ctor_run h with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3)
      (by flapper_ctor_decode) mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push2 ⟨5216⟩, codesize, sub, dup1, push2 ⟨5216⟩, dup4,
    raw codecopy
      9
      (flapperCtorCopiedMem vat gem) (UInt256.ofNat 6)
      (by flapper_ctor_decode)
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
        rw [flapperCtorArgLen_eq]
        decide)
      (by
        rw [flapperCtorArgLen_eq]
        exact hcopy)
      (by rw [flapperCtorArgLen_eq]; decide) (by evm_ov),
    dup2, dup2, add, push1 ⟨64⟩,
    raw mstore 0 (flapperCtorArgsMem vat gem) (UInt256.ofNat 6)
      (by flapper_ctor_decode) mem_cost hfree (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [show (⟨79⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 3 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ = ⟨99⟩
        from by native_decide] using rd99⟩

set_option maxHeartbeats 1000000 in
theorem flapperCtorArgSizeGuardTrace
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (vat gem : AccountAddress)
    (h : RD (flapperCtorCode vat gem) I g s0 ⟨99⟩
      [(UInt256.ofNat (flapperCtorCode vat gem).size).sub ⟨5216⟩, ⟨128⟩]
      (flapperCtorArgsMem vat gem) (UInt256.ofNat 6) rdata acc k C) :
    ∃ k' C', RD (flapperCtorCode vat gem) I g s0 ⟨122⟩
      [EVM.word gem.val, EVM.word vat.val, ⟨32⟩]
      (flapperCtorArgsMem vat gem) (UInt256.ofNat 6) rdata acc k' C' := by
  have rdBeforeJump := flapper_ctor_run h with [
    push1 ⟨64⟩, dup2, lt, iszero, push2 ⟨112⟩]
  have rd112 := rdBeforeJump.jumpiT (by flapper_ctor_decode)
    (by rw [flapperCtorArgLen_eq]; decide) (by flapper_ctor_jd) (by evm_ov)
  have rd116 := flapper_ctor_run rd112 with [
    jumpdest, pop, dup1,
    raw mload 0 (EVM.word vat.val) (UInt256.ofNat 6)
      (by flapper_ctor_decode) mem_cost (flapperCtorArgsMem_mload_vat vat gem)
      (by decide) (by evm_ov)]
  have rd122 := flapper_ctor_run rd116 with [
    push1 ⟨32⟩, swap2, dup3, add,
    raw mload 0 (EVM.word gem.val) (UInt256.ofNat 6)
      (by flapper_ctor_decode) mem_cost (flapperCtorArgsMem_mload_gem vat gem)
      (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [show (⟨112⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨122⟩
        from by native_decide] using rd122⟩

theorem flapperCtorArgsReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress)
    (hcode : I.code = flapperCtorCode vat gem)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (flapperCtorCode vat gem) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨122⟩
      [EVM.word gem.val, EVM.word vat.val, ⟨32⟩]
      (flapperCtorArgsMem vat gem) (UInt256.ofNat 6) ByteArray.empty
      (createdAccounts, flapperCtorAfterKicksMap σ I) k C := by
  obtain ⟨_, _, rd79⟩ :=
    flapperCtorGuardSuccessReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      vat gem hcode hperm hwv
  obtain ⟨_, _, rd99⟩ := flapperCtorArgCopyTrace vat gem rd79
  exact flapperCtorArgSizeGuardTrace vat gem rd99

end Benchmarks.Dss.Flapper
