import Benchmarks.UniswapV4PoolManager.AfterLiquidityStartTrace
import Benchmarks.UniswapV4PoolManager.AfterLiquidityEncodeTrace
import Benchmarks.UniswapV4PoolManager.WordBytesCallAllocationGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem afterLiquidityPrepareTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr delta fees src len ret : UInt256}
    {hook : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    {key : PoolKeyWords} {p : ModifyLiquidityWords}
    (v : PoolManagerImmutables) (add : Bool) (hstack : R.length+27 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)))
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+128 ≤ free.toNat)
    (hf : free.toNat+len.toNat+576 < UInt256.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 (afterLiquidityEncodePc add)
      (afterLiquidityEncodeStack add (accountWord hook) keyPtr paramsPtr delta fees src len ret R)
      mem aw rdata σ k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    (AllocationBounds free (afterLiquidityAllocationSize len) ∧
      ∃ aw' k' C', Cₘ aw' ≤ C' ∧
        RD (deployedRuntime v) I g s0 ⟨17823⟩
          (accountWord hook :: free :: UInt256.fromBool (afterLiquidityParse hook add) ::
            UInt256.ofNat 14631 :: UInt256.ofNat 14638 :: delta :: ret :: R)
          (afterLiquidityMemory add I.calldata mem src.toNat free len I.source key p delta fees) aw' rdata σ k' C') := by
  obtain ⟨aw1, k1, C1, hc1, rd1⟩ := afterLiquidityStartTrace v add (by omega) hfree h
  obtain ⟨aw2, k2, C2, hs2, hc2, rd2⟩ := afterLiquidityEncodeTrace v
    (by simp only [List.length_cons]; omega) hk hp hc hl hu hkb hpb (by omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  have hp2 : Cₘ aw2 ≤ C2 := by omega
  by_cases hb : AllocationBounds free (afterLiquidityAllocationSize len)
  · have hr := wordBytesCallTailAllocationTrace (ptr := free) (src := src) (len := len)
      (words := liquidityHookHeadWords true I.source key p delta fees) (ret := afterLiquidityAllocationRet add)
      (R := accountWord hook :: UInt256.ofNat 14631 :: UInt256.ofNat 14638 :: delta :: ret :: R) v
      (by simp only [List.length_cons]; omega) (by change free.toNat+99+32*13+len.toNat < UInt256.size; omega)
      (by cases add <;> rw [poolManagerPatchedValidJumps v] <;> jump_dest) rd2
    rcases hr with ⟨hbad, _⟩ | ⟨_, aw3, k3, C3, hc3, rd3⟩
    · exact (hbad hb).elim
    · obtain ⟨k4, C4, hc4, rd4⟩ := afterLiquidityInvokeTrace v add
        (by simp only [List.length_cons]; omega) rd3
      exact .inr ⟨hb, _, _, _, by omega, rd4⟩
  · apply Or.inl
    apply wordBytesCallAllocationGas (words := liquidityHookHeadWords true I.source key p delta fees)
      v hgas (by change free.toNat+130+32*13+len.toNat < UInt256.size; omega) hb hp2 ?_ rd2
    change (free.toNat+131+32*13+len.toNat)/32 ≤ aw2.toNat
    convert hs2 using 1 <;> congr 1 <;> omega

end Benchmarks.UniswapV4PoolManager
