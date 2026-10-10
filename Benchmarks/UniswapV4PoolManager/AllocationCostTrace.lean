import Benchmarks.UniswapV4PoolManager.AllocationTrace
import Benchmarks.UniswapV4PoolManager.BytesMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 3000

-- LIBRARY CANDIDATE: the exact rounded allocation end, before any word overflow.
theorem allocationEnd_toNat (ptr len : UInt256)
    (hf : ptr.toNat+len.toNat+31 < UInt256.size) :
    (allocationEnd ptr len).toNat = ptr.toNat+paddedSize len.toNat := by
  change (ptr+paddedWord len).toNat = _
  rw [uadd_toNat, paddedWord_toNat len (by omega), Nat.mod_eq_of_lt]
  have := paddedSize_le_add31 len.toNat
  omega

def bytesAllocationSize (len : UInt256) : UInt256 := paddedWord len+⟨32⟩

theorem bytesAllocationSize_toNat (len : UInt256) (hf : len.toNat+63 < UInt256.size) :
    (bytesAllocationSize len).toNat = 32+paddedSize len.toNat := by
  have hp := paddedSize_le_add31 len.toNat
  have hl := paddedWord_toNat len (by omega)
  change (paddedWord len+UInt256.ofNat 32).toNat = _
  rw [uadd_word_ofNat_toNat _ 32 (by rw [hl]; omega), hl]
  omega

theorem bytesAllocationEnd_toNat (ptr len : UInt256)
    (hf : ptr.toNat+len.toNat+94 < UInt256.size) :
    (allocationEnd ptr (bytesAllocationSize len)).toNat = ptr.toNat+32+paddedSize len.toNat := by
  have hp := paddedSize_le_add31 len.toNat
  have hl := bytesAllocationSize_toNat len (by omega)
  rw [allocationEnd_toNat _ _ (by rw [hl]; omega), hl]
  have he : paddedSize (32+paddedSize len.toNat) = 32+paddedSize len.toNat := by
    unfold paddedSize
    omega
  rw [he]
  omega

/-- The allocator's exact guard, without the extra slack in `allocateTrace`. -/
def AllocationBounds (ptr len : UInt256) : Prop :=
  ptr.toNat ≤ (allocationEnd ptr len).toNat ∧ (allocationEnd ptr len).toNat ≤ solcMaxU64

instance (ptr len : UInt256) : Decidable (AllocationBounds ptr len) := by
  unfold AllocationBounds
  infer_instance

theorem allocateCheckedTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr len ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨11822⟩ (ptr :: len :: ret :: R) mem aw rdata σ k C) :
    (¬AllocationBounds ptr len ∧ RD (deployedRuntime v) I g s0 ⟨7857⟩
      (allocationEnd ptr len :: ret :: R) mem aw rdata σ (k+18) (C+59)) ∨
    (AllocationBounds ptr len ∧ RD (deployedRuntime v) I g s0 ret R
      (writeWord mem 64 (allocationEnd ptr len)) (M aw (UInt256.ofNat 64) ⟨32⟩) rdata σ
        (k+21) (C+73+memExpansionCost aw (UInt256.ofNat 64) ⟨32⟩)) := by
  by_cases hb : AllocationBounds ptr len
  · have rd1 := poolManager_block_11822_fallthrough (by simp only [List.length_cons]; omega)
      (by change UInt256.lor (UInt256.gt (allocationEnd ptr len) (UInt256.ofNat solcMaxU64))
            (UInt256.lt (allocationEnd ptr len) ptr) = ⟨0⟩
          rw [ugt_zero hb.2, ult_zero hb.1]; rfl) h
    have rd2 := poolManager_block_11883 (by omega) hret rd1
    exact .inr ⟨hb, RD.normalizeCounters rd2 (by omega) (by omega)⟩
  · have hc : UInt256.lor (UInt256.gt (allocationEnd ptr len) (UInt256.ofNat solcMaxU64))
        (UInt256.lt (allocationEnd ptr len) ptr) ≠ ⟨0⟩ := by
      by_cases hh : (allocationEnd ptr len).toNat ≤ solcMaxU64
      · rw [ugt_zero hh, ult_one (by
          have : ¬ptr.toNat ≤ (allocationEnd ptr len).toNat := fun hp => hb ⟨hp, hh⟩
          omega)]
        decide
      · rw [ugt_one (show (UInt256.ofNat solcMaxU64).toNat < (allocationEnd ptr len).toNat from Nat.lt_of_not_ge hh)]
        exact u256_lor_one_left_ne_zero _
    have rd := poolManager_block_11822_taken (by simp only [List.length_cons]; omega) hc
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact .inl ⟨hb, rd⟩

end Benchmarks.UniswapV4PoolManager
