import Benchmarks.UniswapV4PoolManager.PoolModifyLimits
import Benchmarks.UniswapV4PoolManager.TickSpacingCheckTrace
import Benchmarks.UniswapV4PoolManager.BlockResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyLimitsActiveWords (aw params ptr : UInt256) (delta : Int) : UInt256 :=
  if 0 ≤ delta then M (M (M aw (params+UInt256.ofNat 128) ⟨32⟩) (ptr+UInt256.ofNat 32) ⟨32⟩) (ptr+UInt256.ofNat 96) ⟨32⟩ else aw

theorem poolModifyLimitsExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw spacing gl gu x0 x1 x2 ptr x4 x5 x6 x7 x8 x9 params : UInt256}
    {delta : Int} {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hc : int24Canonical spacing)
    (hs : memLoad (params+UInt256.ofNat 128) mem = spacing)
    (hl : memLoad (ptr+UInt256.ofNat 32) mem = gl)
    (hu : memLoad (ptr+UInt256.ofNat 96) mem = gu)
    (hgl : gl.toNat < 2^128) (hgu : gu.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 (if 0 ≤ delta then ⟨7329⟩ else ⟨7256⟩)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: params :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post = evm ∧ ∃ k' C',
      RD (deployedRuntime v) I g s0 ⟨7256⟩
        (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: params :: R)
        mem (poolModifyLimitsActiveWords aw params ptr delta) rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyLimitsResult f evm delta (EVM.signed spacing) gl gu) := by
  unfold poolModifyLimitsActiveWords
  by_cases hd : 0 ≤ delta
  · rw [if_pos hd] at h
    simp only [poolModifyLimitsResult, if_pos hd]
    have ht := tickSpacingCheckExactTrace v hstack hc hs hl hu hgl hgu h
    by_cases hb : tickSpacingLimit (EVM.signed spacing) < Int.ofNat gl.toNat ∨
        tickSpacingLimit (EVM.signed spacing) < Int.ofNat gu.toNat
    · rw [if_pos hb] at ht ⊢
      exact ht
    · rw [if_neg hb] at ht ⊢
      exact ⟨rfl, ht⟩
  · rw [if_neg hd] at h
    simp only [poolModifyLimitsResult, if_neg hd]
    exact ⟨rfl, _, _, h⟩

theorem poolModifyLimitsTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw spacing gl gu x0 x1 x2 ptr x4 x5 x6 x7 x8 x9 params : UInt256}
    {delta : Int} {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hc : int24Canonical spacing)
    (hs : memLoad (params+UInt256.ofNat 128) mem = spacing)
    (hl : memLoad (ptr+UInt256.ofNat 32) mem = gl)
    (hu : memLoad (ptr+UInt256.ofNat 96) mem = gu)
    (hgl : gl.toNat < 2^128) (hgu : gu.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 (if 0 ≤ delta then ⟨7329⟩ else ⟨7256⟩)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: params :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post = evm ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨7256⟩
        (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: params :: R)
        mem aw' rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyLimitsResult f evm delta (EVM.signed spacing) gl gu) := by
  have hr := poolModifyLimitsExactTrace f v hstack hc hs hl hu hgl hgu h
  apply blockResultTrace_mono hr
  intro f' post _ ht
  exact ⟨ht.1, _, ht.2⟩

end Benchmarks.UniswapV4PoolManager
