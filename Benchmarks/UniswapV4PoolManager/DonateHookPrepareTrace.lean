import Benchmarks.UniswapV4PoolManager.DonateHookStartTrace
import Benchmarks.UniswapV4PoolManager.DonateHookEncodeTrace
import Benchmarks.UniswapV4PoolManager.WordBytesCallAllocationGas
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_015

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem donateHookPrepareTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free hook hookPtr keyPtr src amount0 amount1 len delta : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {key : PoolKeyWords}
    (v : PoolManagerImmutables) (after : Bool) (hstack : R.length+30 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+len.toNat+448 < UInt256.size)
    (hgas : g.toNat < 324518553658429321982441292826060) (hpaid : Cₘ aw ≤ C)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 (donateHookEncodePc after)
      (donateHookEncodeStack after hook hookPtr keyPtr src amount0 amount1 len delta R) mem aw rdata σ k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    (AllocationBounds free (donateHookAllocationSize len) ∧
      ∃ aw' k' C', Cₘ aw' ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨16165⟩
        (hook :: free :: donateHookCallRet after :: donateHookSavedStack after hookPtr keyPtr src amount0 amount1 len delta R)
        (donateHookMemory after I.calldata mem src.toNat free len I.source key amount0 amount1) aw' rdata σ k' C') := by
  have hsaved : (donateHookSavedStack after hookPtr keyPtr src amount0 amount1 len delta R).length ≤ R.length+6 := by
    cases after <;> simp only [donateHookSavedStack, Bool.false_eq_true, if_false, if_true, List.length_cons] <;> omega
  obtain ⟨aw1, k1, C1, hc1, rd1⟩ := donateHookStartTrace v after (by omega) hfree h
  obtain ⟨aw2, k2, C2, hs2, hc2, rd2⟩ := donateHookEncodeTrace v
    (by simp only [List.length_cons]; omega) hk hc hb (by omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  have hp2 : Cₘ aw2 ≤ C2 := by omega
  by_cases halloc : AllocationBounds free (donateHookAllocationSize len)
  · have hr := wordBytesCallAllocationTrace (ptr := free) (src := src) (len := len)
      (words := donateHookHeadWords I.source key amount0 amount1) (ret := UInt256.ofNat 4778) (arg := hook)
      (R := donateHookCallRet after :: donateHookSavedStack after hookPtr keyPtr src amount0 amount1 len delta R) v
      (by simp only [List.length_cons]; omega) (by change free.toNat+99+32*9+len.toNat < UInt256.size; omega)
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd2
    rcases hr with ⟨hbad, _⟩ | ⟨_, aw3, k3, C3, hc3, rd3⟩
    · exact (hbad halloc).elim
    · have rd4 := poolManager_block_4778 (by simp only [List.length_cons]; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
      exact .inr ⟨halloc, _, _, _, by omega, rd4⟩
  · apply Or.inl
    apply wordBytesCallAllocationGas (words := donateHookHeadWords I.source key amount0 amount1) v hgas
      (by change free.toNat+130+32*9+len.toNat < UInt256.size; omega) halloc hp2 ?_ rd2
    change (free.toNat+131+32*9+len.toNat)/32 ≤ aw2.toNat
    convert hs2 using 1 <;> congr 1 <;> omega

end Benchmarks.UniswapV4PoolManager
