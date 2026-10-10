import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_033

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def allocationEnd (ptr len : UInt256) : UInt256 :=
  ptr + UInt256.land (len + ⟨31⟩) ⟨115792089237316195423570985008687907853269984665640564039457584007913129639904⟩

-- LIBRARY CANDIDATE: the rounded end remains above the pointer and below the u64 allocation bound.
theorem allocationEnd_bounds (ptr len : UInt256) (hf : ptr.toNat+len.toNat+31 ≤ solcMaxU64) :
    ptr.toNat ≤ (allocationEnd ptr len).toNat ∧ (allocationEnd ptr len).toNat ≤ solcMaxU64 := by
  have hl : (len+⟨31⟩).toNat = len.toNat+31 :=
    uadd_word_ofNat_toNat len 31 (by change _ < 2^256; change _ ≤ 2^64-1 at hf; omega)
  have hr : (UInt256.land (len+⟨31⟩)
      ⟨115792089237316195423570985008687907853269984665640564039457584007913129639904⟩).toNat ≤ len.toNat+31 := by
    rw [uland_toNat, ← hl]
    exact Nat.and_le_left
  unfold allocationEnd
  rw [uadd_toNat, Nat.mod_eq_of_lt (by change _ < 2^256; change _ ≤ 2^64-1 at hf; omega)]
  omega

theorem allocateTraceWords {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ptr len ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024)
    (hf : ptr.toNat+len.toNat+31 ≤ solcMaxU64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨11822⟩ (ptr :: len :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret R (writeWord mem 64 (allocationEnd ptr len)) (M aw (UInt256.ofNat 64) ⟨32⟩) rdata σ k' C' := by
  have hb := allocationEnd_bounds ptr len hf
  have hr := poolManagerBlocks.poolManager_block_11822_fallthrough (by simp; omega)
    (by change UInt256.lor (UInt256.gt (allocationEnd ptr len) ⟨18446744073709551615⟩)
          (UInt256.lt (allocationEnd ptr len) ptr) = ⟨0⟩
        rw [ugt_zero hb.2, ult_zero hb.1]; rfl) h
  exact RD.pack (poolManagerBlocks.poolManager_block_11883 (by omega) hret hr)

theorem allocateTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ptr len ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024)
    (hf : ptr.toNat+len.toNat+31 ≤ solcMaxU64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨11822⟩ (ptr :: len :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R (writeWord mem 64 (allocationEnd ptr len)) aw' rdata σ k' C' := by
  obtain ⟨k', C', hr⟩ := allocateTraceWords v hstack hf hret h
  exact ⟨_, k', C', hr⟩

end Benchmarks.UniswapV4PoolManager
