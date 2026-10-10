import Benchmarks.UniswapV4PoolManager.TickClearTrace
import Benchmarks.UniswapV4PoolManager.FunctionTraceMono

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

def tickClearReturnTrace (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (id tick pc : UInt256) (stack : List UInt256) :
    State → Option (List Value) → Prop
  | post, none => post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ ∃ aw k C,
      RD (deployedRuntime v) I g s0 pc stack (twoWordHashMem tick (poolSlot id+⟨4⟩) mem)
        aw rdata post.accountMap k C
  | _, _ => False

def tickClearReturnTraceAtAW (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (id tick pc : UInt256) (stack : List UInt256) (aw : UInt256) :
    State → Option (List Value) → Prop
  | post, none => post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ ∃ k C,
      RD (deployedRuntime v) I g s0 pc stack (twoWordHashMem tick (poolSlot id+⟨4⟩) mem)
        aw rdata post.accountMap k C
  | _, _ => False

theorem tickClearUpperExactResultTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 : UInt256} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hc : int24Canonical tick)
    (h : RD (deployedRuntime v) I g s0 ⟨6642⟩ (x0 :: tick :: R) mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (tickClearReturnTraceAtAW v I g s0 evm.σ₀ mem rdata id tick ⟨6681⟩ (x0 :: tick :: R) (tickClearActiveWords aw))
      (tickClearResult f evm id (EVM.signed tick)) := by
  have hr := tickClearUpperExactTrace v hstack hI hm hc h
  simp only [tickClearResult]
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp] at hr ⊢
    exact hr
  · rw [if_neg hp] at hr ⊢
    refine ⟨?_, ?_, hr⟩
    · simp only [tickClearPost, storageStore_executionEnv, hI]
    · simp only [tickClearPost, storageStore_σ₀]

theorem tickClearUpperResultTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 : UInt256} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hc : int24Canonical tick)
    (h : RD (deployedRuntime v) I g s0 ⟨6642⟩ (x0 :: tick :: R) mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (tickClearReturnTrace v I g s0 evm.σ₀ mem rdata id tick ⟨6681⟩ (x0 :: tick :: R))
      (tickClearResult f evm id (EVM.signed tick)) := by
  have hr := tickClearUpperExactResultTrace f v hstack hI hm hc h
  apply functionResultTrace_mono hr
  intro post values ht
  cases values with
  | none => exact ⟨ht.1, ht.2.1, _, ht.2.2⟩
  | some _ => exact False.elim ht

theorem tickClearLowerExactResultTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 x1 : UInt256} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hc : int24Canonical tick)
    (h : RD (deployedRuntime v) I g s0 ⟨6686⟩ (x0 :: x1 :: tick :: R) mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (tickClearReturnTraceAtAW v I g s0 evm.σ₀ mem rdata id tick ⟨6725⟩ (x0 :: x1 :: tick :: R) (tickClearActiveWords aw))
      (tickClearResult f evm id (EVM.signed tick)) := by
  have hr := tickClearLowerExactTrace v hstack hI hm hc h
  simp only [tickClearResult]
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp] at hr ⊢
    exact hr
  · rw [if_neg hp] at hr ⊢
    refine ⟨?_, ?_, hr⟩
    · simp only [tickClearPost, storageStore_executionEnv, hI]
    · simp only [tickClearPost, storageStore_σ₀]

theorem tickClearLowerResultTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 x1 : UInt256} {k C : Nat} {R : List UInt256}
    (f : Frame) (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hc : int24Canonical tick)
    (h : RD (deployedRuntime v) I g s0 ⟨6686⟩ (x0 :: x1 :: tick :: R) mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (tickClearReturnTrace v I g s0 evm.σ₀ mem rdata id tick ⟨6725⟩ (x0 :: x1 :: tick :: R))
      (tickClearResult f evm id (EVM.signed tick)) := by
  have hr := tickClearLowerExactResultTrace f v hstack hI hm hc h
  apply functionResultTrace_mono hr
  intro post values ht
  cases values with
  | none => exact ⟨ht.1, ht.2.1, _, ht.2.2⟩
  | some _ => exact False.elim ht

end Benchmarks.UniswapV4PoolManager
