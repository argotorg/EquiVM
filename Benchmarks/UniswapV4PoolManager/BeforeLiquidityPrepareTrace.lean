import Benchmarks.UniswapV4PoolManager.BeforeLiquidityStartTrace
import Benchmarks.UniswapV4PoolManager.BeforeLiquidityEncodeTrace
import Benchmarks.UniswapV4PoolManager.BeforeLiquidityAllocationGas
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_015

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem beforeLiquidityPrepareTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free a b hook keyPtr paramsPtr src len : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {key : PoolKeyWords} {p : ModifyLiquidityWords}
    (v : PoolManagerImmutables) (add : Bool) (hstack : R.length+26 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)))
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+128 ≤ free.toNat)
    (hf : free.toNat+len.toNat+512 < UInt256.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 (beforeLiquidityEncodePc add)
      (beforeLiquidityEncodeStack add a b hook src paramsPtr len keyPtr R) mem aw rdata σ k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    (AllocationBounds free (beforeLiquidityAllocationSize len) ∧
      ∃ aw' k' C', Cₘ aw' ≤ C' ∧
        RD (deployedRuntime v) I g s0 ⟨16165⟩
          (hook :: free :: beforeLiquidityCallRet add :: src :: paramsPtr :: len :: keyPtr :: R)
          (beforeLiquidityMemory add I.calldata mem src.toNat free len I.source key p) aw' rdata σ k' C') := by
  obtain ⟨aw1, k1, C1, hc1, rd1⟩ := beforeLiquidityStartTrace v add (by omega) hfree h
  obtain ⟨aw2, k2, C2, hs2, hc2, rd2⟩ := beforeLiquidityEncodeTrace v
    (by simp only [List.length_cons]; omega) hk hp hc hl hu hkb hpb (by omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  have hp2 : Cₘ aw2 ≤ C2 := by omega
  by_cases hb : AllocationBounds free (beforeLiquidityAllocationSize len)
  · have hr := wordBytesCallAllocationTrace (ptr := free) (src := src) (len := len)
      (words := liquidityHookHeadWords false I.source key p ⟨0⟩ ⟨0⟩) (ret := UInt256.ofNat 4778) (arg := hook)
      (R := beforeLiquidityCallRet add :: src :: paramsPtr :: len :: keyPtr :: R) v
      (by simp only [List.length_cons]; omega) (by change free.toNat+99+32*11+len.toNat < UInt256.size; omega)
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd2
    rcases hr with ⟨hbad, _⟩ | ⟨_, aw3, k3, C3, hc3, rd3⟩
    · exact (hbad hb).elim
    · have rd4 := poolManager_block_4778 (by simp only [List.length_cons]; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
      exact .inr ⟨hb, _, _, _, by omega, rd4⟩
  · exact .inl (beforeLiquidityAllocationGas v hgas hf hb hp2 hs2 rd2)

end Benchmarks.UniswapV4PoolManager
