import Benchmarks.UniswapV4PoolManager.AllocationCostTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

/-- The specialized four-word allocator, retaining the capacity-failure branch. -/
theorem allocate128CheckedTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨11738⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    (¬AllocationBounds ptr ⟨128⟩ ∧ RD (deployedRuntime v) I g s0 ⟨7857⟩
      ((ptr+⟨128⟩) :: ret :: R) mem aw rdata σ (k+13) (C+44)) ∨
    (AllocationBounds ptr ⟨128⟩ ∧ RD (deployedRuntime v) I g s0 ret R
      (writeWord mem 64 (ptr+⟨128⟩)) (M aw (UInt256.ofNat 64) ⟨32⟩) rdata σ
        (k+16) (C+58+memExpansionCost aw (UInt256.ofNat 64) ⟨32⟩)) := by
  have he : allocationEnd ptr ⟨128⟩ = ptr+⟨128⟩ := rfl
  by_cases hb : AllocationBounds ptr ⟨128⟩
  · have hlo := hb.1
    have hhi := hb.2
    rw [he] at hlo hhi
    have rd1 := poolManagerBlocks.poolManager_block_11738_fallthrough
      (by simp only [List.length_cons]; omega)
      (by change UInt256.lor (UInt256.gt (ptr+⟨128⟩) (UInt256.ofNat solcMaxU64))
            (UInt256.lt (ptr+⟨128⟩) ptr) = ⟨0⟩
          rw [ugt_zero hhi, ult_zero hlo]; rfl) h
    have rd2 := poolManagerBlocks.poolManager_block_11762 (by omega) hret rd1
    exact .inr ⟨hb, RD.normalizeCounters rd2 (by omega) (by omega)⟩
  · have hc : UInt256.lor (UInt256.gt (ptr+⟨128⟩) (UInt256.ofNat solcMaxU64))
        (UInt256.lt (ptr+⟨128⟩) ptr) ≠ ⟨0⟩ := by
      by_cases hh : (ptr+⟨128⟩).toNat ≤ solcMaxU64
      · have hlo : ¬ptr.toNat ≤ (ptr+⟨128⟩).toNat := by
          intro hp
          exact hb ⟨he ▸ hp, he ▸ hh⟩
        rw [ugt_zero hh, ult_one (by omega)]
        decide
      · rw [ugt_one (show (UInt256.ofNat solcMaxU64).toNat < (ptr+⟨128⟩).toNat from Nat.lt_of_not_ge hh)]
        exact u256_lor_one_left_ne_zero _
    have rd := poolManagerBlocks.poolManager_block_11738_taken
      (by simp only [List.length_cons]; omega) hc
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact .inl ⟨hb, rd⟩

theorem allocate128CostTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024)
    (hf : ptr.toNat+128 ≤ solcMaxU64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨11738⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    RD (deployedRuntime v) I g s0 ret R
      (writeWord mem 64 (ptr+⟨128⟩)) (M aw (UInt256.ofNat 64) ⟨32⟩) rdata σ
        (k+16) (C+58+memExpansionCost aw (UInt256.ofNat 64) ⟨32⟩) := by
  have he : (ptr+⟨128⟩).toNat = ptr.toNat+128 :=
    uadd_word_ofNat_toNat ptr 128 (by change _ < 2^256; change _ ≤ 2^64-1 at hf; omega)
  have hb : AllocationBounds ptr ⟨128⟩ := by
    change ptr.toNat ≤ (ptr+⟨128⟩).toNat ∧ (ptr+⟨128⟩).toNat ≤ solcMaxU64
    rw [he]
    exact ⟨by omega, hf⟩
  rcases allocate128CheckedTrace v hstack hret h with ⟨hbad, _⟩ | ⟨_, hr⟩
  · exact False.elim (hbad hb)
  · exact hr

theorem allocate128Trace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024)
    (hf : ptr.toNat+128 ≤ solcMaxU64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨11738⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R
      (writeWord mem 64 (ptr+⟨128⟩)) aw' rdata σ k' C' := by
  exact ⟨_, _, _, allocate128CostTrace v hstack hf hret h⟩

end Benchmarks.UniswapV4PoolManager
