import Benchmarks.UniswapV4PoolManager.TickBitmapTrace
import Benchmarks.UniswapV4PoolManager.FunctionTraceMono

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

def tickBitmapReturnTrace (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (id tick spacing ret : UInt256) (R : List UInt256) :
    State → Option (List Value) → Prop
  | post, none => post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ ∃ aw k C,
    RD (deployedRuntime v) I g s0 ret R
      (twoWordHashMem (EVM.wordOfInt (tickBitmapPosition (EVM.signed tick) (EVM.signed spacing)))
        (poolSlot id+⟨5⟩) mem) aw rdata post.accountMap k C
  | _, _ => False

def tickBitmapReturnTraceAtAW (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (id tick spacing ret : UInt256) (R : List UInt256) (aw : UInt256) :
    State → Option (List Value) → Prop
  | post, none => post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ ∃ k C,
    RD (deployedRuntime v) I g s0 ret R
      (twoWordHashMem (EVM.wordOfInt (tickBitmapPosition (EVM.signed tick) (EVM.signed spacing)))
        (poolSlot id+⟨5⟩) mem) aw rdata post.accountMap k C
  | _, _ => False

theorem tickBitmapExactResultTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick spacing ret : UInt256} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024) (hI : evm.executionEnv = I)
    (ht : int24Canonical tick) (hs : int24Canonical spacing) (hb : (EVM.signed tick).natAbs ≤ 887272)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16652⟩ ((poolSlot id+⟨5⟩) :: tick :: spacing :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (tickBitmapReturnTraceAtAW v I g s0 evm.σ₀ mem rdata id tick spacing ret R (tickBitmapActiveWords aw))
      (tickBitmapResult f evm id (EVM.signed tick) (EVM.signed spacing)) := by
  have hr := tickBitmapExactTrace v hstack hI ht hs hb hret h
  simp only [tickBitmapResult, hI]
  by_cases ha : tickBitmapAligned (EVM.signed tick) (EVM.signed spacing)
  · rw [if_pos ha] at hr ⊢
    by_cases hp : I.perm = false
    · rw [if_pos hp] at hr ⊢
      exact hr
    · rw [if_neg hp] at hr ⊢
      refine ⟨?_, ?_, hr⟩
      · rw [tickBitmapPost, storageStore_executionEnv, hI]
      · rw [tickBitmapPost, storageStore_σ₀]
  · rw [if_neg ha] at hr ⊢
    exact hr

theorem tickBitmapResultTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick spacing ret : UInt256} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024) (hI : evm.executionEnv = I)
    (ht : int24Canonical tick) (hs : int24Canonical spacing) (hb : (EVM.signed tick).natAbs ≤ 887272)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16652⟩ ((poolSlot id+⟨5⟩) :: tick :: spacing :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (tickBitmapReturnTrace v I g s0 evm.σ₀ mem rdata id tick spacing ret R)
      (tickBitmapResult f evm id (EVM.signed tick) (EVM.signed spacing)) := by
  have hr := tickBitmapExactResultTrace f v hstack hI ht hs hb hret h
  apply functionResultTrace_mono hr
  intro post values ht
  cases values with
  | none => exact ⟨ht.1, ht.2.1, _, ht.2.2⟩
  | some _ => exact False.elim ht

end Benchmarks.UniswapV4PoolManager
