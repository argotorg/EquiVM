import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueMemory
import Benchmarks.Morpho.MetaMorphoV1_1.MappingScratchMemory

/-! Preserve the completed queue arrays while external readers advance the allocation cursor. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

structure UpdateWithdrawQueueHeap (mem : ByteArray) (curr len : Nat)
    (seen : List Bool) (queue : List UInt256) (cursor : UInt256) : Prop where
  seenLength : seen.length = curr
  queueLength : queue.length = len
  seen : WordArrayPrefix mem 128 (seenWords seen) curr
  queue : WordArrayPrefix mem (160 + 32 * curr) queue len
  cursorLo : 192 + 32 * curr + 32 * len ≤ cursor.toNat
  cursorHi : cursor.toNat < 2 ^ 64
  size : cursor.toNat ≤ mem.size
  free : memLoad ⟨64⟩ mem = cursor

theorem UpdateWithdrawQueueMemory.heap {mem : ByteArray} {curr len : Nat}
    {seen : List Bool} {queue : List UInt256}
    (h : UpdateWithdrawQueueMemory mem curr len len seen queue)
    (hfit : 192 + 32 * curr + 32 * len < 2 ^ 64) :
    UpdateWithdrawQueueHeap mem curr len seen queue
      (UInt256.ofNat (192 + 32 * curr + 32 * len)) := by
  have hp := ulit_toNat' _ (lt_trans hfit (by decide : 2 ^ 64 < UInt256.size))
  refine ⟨h.seenLength, h.queueLength, h.seen, h.queue, ?_, ?_, ?_, h.free⟩
  · rw [hp]
  · rwa [hp]
  · rw [hp]; have := h.queue.size; omega

theorem UpdateWithdrawQueueHeap.preserved {before after : ByteArray} {curr len : Nat}
    {seen : List Bool} {queue : List UInt256} {cursor cursor' : UInt256}
    (h : UpdateWithdrawQueueHeap before curr len seen queue cursor)
    (hp : MemoryPrefix before after cursor.toNat) (hmono : cursor.toNat ≤ cursor'.toNat)
    (hbound : cursor'.toNat < 2 ^ 64) (hsize : cursor'.toNat ≤ after.size)
    (hfree : memLoad ⟨64⟩ after = cursor') :
    UpdateWithdrawQueueHeap after curr len seen queue cursor' := by
  have hlo := h.cursorLo
  exact ⟨h.seenLength, h.queueLength,
    h.seen.preserved hp (by decide) (by omega), h.queue.preserved hp (by omega) (by omega),
    le_trans hlo hmono, hbound, hsize, hfree⟩

theorem UpdateWithdrawQueueHeap.scratch {mem : ByteArray} {curr len : Nat}
    {seen : List Bool} {queue : List UInt256} {cursor : UInt256}
    (h : UpdateWithdrawQueueHeap mem curr len seen queue cursor) (word : UInt256) :
    UpdateWithdrawQueueHeap (wordAt0Mem word mem) curr len seen queue cursor := by
  have hp : MemoryPrefix mem (wordAt0Mem word mem) cursor.toNat :=
    memoryPrefix_sparse_writeWord _ _ _ _ (.inr (by decide))
  apply h.preserved hp (le_refl _) h.cursorHi (le_trans h.size hp.size)
  rw [wordAt0Mem, memLoad_write_disjoint _ _ _ _
    (by change 96 ≤ mem.size; have := h.seen.size; omega) (.inr (by decide))]
  exact h.free

theorem UpdateWithdrawQueueHeap.mappingScratch {mem : ByteArray} {curr len : Nat}
    {seen : List Bool} {queue : List UInt256} {cursor : UInt256}
    (h : UpdateWithdrawQueueHeap mem curr len seen queue cursor) (key slot : UInt256) :
    UpdateWithdrawQueueHeap (twoWordHashMem key slot mem) curr len seen queue cursor := by
  have hp := twoWordHashMem_prefix mem key slot cursor.toNat
  apply h.preserved hp (le_refl _) h.cursorHi (le_trans h.size hp.size)
  rw [twoWordHashMem_free key slot (by have := h.seen.size; omega), h.free]

end Benchmarks.Morpho.MetaMorphoV1_1
