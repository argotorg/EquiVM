import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueFinish
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueStoreStatic
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueTailSource

/-! Full storage replacement and return, with its matching source result. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueStoreAndFinish {evm s0 : State} {g : Sat256}
    {mem out : ByteArray} {aw : UInt256} {k C curr : Nat} {R : List UInt256}
    {seen : List Bool} {queue : List UInt256} {cursor : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hperm : evm.executionEnv.perm = true)
    (hm : UpdateWithdrawQueueHeap mem curr queue.length seen queue cursor)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨8213⟩
      ([UInt256.ofNat queue.length, UInt256.ofNat (160 + 32 * curr),
        UInt256.ofNat (192 + 32 * curr)] ++ R) mem aw out evm.accountMap k C) :
    RDret (deployedRuntime v) g s0 (updateWithdrawQueueSourceState evm queue).accountMap
      ByteArray.empty := by
  rcases updateWithdrawQueuePrepareStore v
      (by change R.length + 9 ≤ 1024; exact hstack) hperm hm rd with
    hoog | ⟨hold, junk, mem1, hm1, aw1, k1, C1, r1⟩
  · exact .inl hoog
  · have r2 := metaMorphoV1_1_block_8227 (immWords := wordsOf (immStore v))
      (by change R.length + 6 ≤ 1024; omega) r1
    have hm2 := hm1.scratch ⟨21⟩
    obtain ⟨aw3, k3, C3, r3⟩ := updateWithdrawQueueWriteLoop v queue.length
      (R := [UInt256.ofNat (160 + 32 * curr), UInt256.ofNat (192 + 32 * curr)] ++ R)
      (by change R.length + 9 ≤ 1024; exact hstack) hm2.queue hperm (i := 0) (by omega)
      (by simpa only [metaMorphoV1_1_block_8227_stack, Nat.mul_zero, Nat.add_zero,
        show 160 + 32 * curr + 32 = 192 + 32 * curr by omega] using r2)
    have hret := updateWithdrawQueueFinish v hstack hperm r3
    rw [updateWithdrawQueueAccounts_match evm queue hold
      (by have := hm.cursorLo; have := hm.cursorHi; omega)]
    exact hret

theorem updateWithdrawQueueTailSimulation {I : ExecutionEnv} {evm s0 : State} {g : Sat256}
    {frame : Frame} {mem out : ByteArray} {aw : UInt256} {k C curr i : Nat}
    {indexes : List Value} {seen : List Bool} {queue : List UInt256} {cursor : UInt256}
    {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hr : UpdateWithdrawQueueReady frame (immStore v) indexes curr i seen queue cursor)
    (hm : UpdateWithdrawQueueHeap mem curr queue.length seen queue cursor)
    (hs : SourceState s0 I evm.accountMap evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨8183⟩
      ([UInt256.ofNat i, ⟨128⟩, UInt256.ofNat curr,
        UInt256.ofNat (160 + 32 * curr), UInt256.ofNat (192 + 32 * curr)] ++ R)
      mem aw out evm.accountMap k C) :
    (ExecBlock config frame evm updateWithdrawQueueTail .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    ∃ final evm', ExecBlock config frame evm updateWithdrawQueueTail (.ok final evm') ∧
      RDret (deployedRuntime v) g s0 evm'.accountMap ByteArray.empty := by
  obtain ⟨aw1, k1, C1, r1⟩ := updateWithdrawQueueStoreGuards v
    (by change R.length + 6 ≤ 1024; omega)
    (by have := hm.cursorLo; have := hm.cursorHi; omega) hm.queue.length rd
  by_cases hperm : I.perm = true
  · obtain ⟨final, hsource⟩ := updateWithdrawQueueTailReturns hr
    exact .inr ⟨final, updateWithdrawQueueSourceState evm queue, hsource,
      updateWithdrawQueueStoreAndFinish v hstack (by rw [hs.env]; exact hperm) hm
        (by simpa only [hs.env] using r1)⟩
  · have hfalse : I.perm = false := Bool.eq_false_of_not_eq_true hperm
    exact .inl ⟨updateWithdrawQueueTailStatic hr (by rw [hs.env]; exact hfalse),
      updateWithdrawQueueStoreStatic v (by change R.length + 6 ≤ 1024; omega) hfalse r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
