import Benchmarks.UniswapV4PoolManager.BeforeSwapEncodeTrace
import Benchmarks.UniswapV4PoolManager.WordBytesCallTailAllocation
import Benchmarks.UniswapV4PoolManager.WordBytesCallAllocationGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem beforeSwapPrepareTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr src len hook : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {key : PoolKeyWords} {p : SwapParamsWords}
    (v : PoolManagerImmutables) (hstack : R.length+20 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (swapParamsWordList p)))
    (hc : PoolKeyCanonical key) (hl : p.priceLimit.toNat < 2^160)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+96 ≤ free.toNat)
    (hf : free.toNat+len.toNat+480 < UInt256.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨15230⟩
      (src :: len :: paramsPtr :: hook :: keyPtr :: R) mem aw rdata σ k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    (AllocationBounds free (beforeSwapAllocationSize len) ∧
      ∃ aw' k' C', Cₘ aw' ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨16165⟩
        (hook :: free :: UInt256.ofNat 15462 :: hook :: keyPtr :: R)
        (beforeSwapMemory I.calldata mem src.toNat free len I.source key p) aw' rdata σ k' C') := by
  obtain ⟨aw1, k1, C1, hs1, hc1, rd1⟩ := beforeSwapEncodeTrace v hstack hk hp hc hl hkb hpb (by omega) hfree h
  have hp1 : Cₘ aw1 ≤ C1 := by omega
  by_cases hb : AllocationBounds free (beforeSwapAllocationSize len)
  · have hr := wordBytesCallTailAllocationTrace (ptr := free) (src := src) (len := len)
      (words := swapHookHeadWords false I.source key p ⟨0⟩) (ret := UInt256.ofNat 15456)
      (R := UInt256.ofNat 15462 :: hook :: keyPtr :: R) v
      (by simp only [List.length_cons]; omega) (by change free.toNat+99+32*10+len.toNat < UInt256.size; omega)
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
    rcases hr with ⟨hbad, _⟩ | ⟨_, aw2, k2, C2, hc2, rd2⟩
    · exact (hbad hb).elim
    · have rd3 := poolManager_block_15456 (by simp only [List.length_cons]; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact .inr ⟨hb, _, _, _, by omega, rd3⟩
  · apply Or.inl
    apply wordBytesCallAllocationGas (words := swapHookHeadWords false I.source key p ⟨0⟩)
      v hgas (by change free.toNat+130+32*10+len.toNat < UInt256.size; omega) hb hp1 ?_ rd1
    change (free.toNat+131+32*10+len.toNat)/32 ≤ aw1.toNat
    convert hs1 using 1 <;> congr 1 <;> omega

end Benchmarks.UniswapV4PoolManager
