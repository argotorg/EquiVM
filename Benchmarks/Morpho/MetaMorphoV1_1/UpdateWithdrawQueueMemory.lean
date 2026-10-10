import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayPrefix

/-! The two arrays used while updating the withdrawal queue. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def seenWords (seen : List Bool) : List UInt256 := seen.map fun b ↦ if b then ⟨1⟩ else ⟨0⟩

structure UpdateWithdrawQueueMemory (mem : ByteArray) (curr len i : Nat)
    (seen : List Bool) (queue : List UInt256) : Prop where
  seenLength : seen.length = curr
  queueLength : queue.length = len
  seen : WordArrayPrefix mem 128 (seenWords seen) curr
  queue : WordArrayPrefix mem (160 + 32 * curr) queue i
  free : memLoad ⟨64⟩ mem = UInt256.ofNat (192 + 32 * curr + 32 * len)

def updateWithdrawQueueInitMem (mem : ByteArray) (curr len : Nat) : ByteArray :=
  wordArrayInitMemory (wordArrayInitMemory mem ⟨128⟩ curr)
    (UInt256.ofNat (160 + 32 * curr)) len

theorem updateWithdrawQueueInitialMemory (mem : ByteArray) (curr len : Nat)
    (hmem : mem.size ≤ 128) (hfit : 192 + 32 * curr + 32 * len < UInt256.size) :
    UpdateWithdrawQueueMemory (updateWithdrawQueueInitMem mem curr len) curr len 0
      (List.replicate curr false) (List.replicate len ⟨0⟩) := by
  have hp : (UInt256.ofNat (160 + 32 * curr)).toNat = 160 + 32 * curr :=
    ulit_toNat' _ (by omega)
  have hs : (wordArrayInitMemory mem ⟨128⟩ curr).size = 160 :=
    wordArrayInitMemory_size _ _ _ hmem (by decide)
  have hs' : (updateWithdrawQueueInitMem mem curr len).size = 192 + 32 * curr := by
    rw [updateWithdrawQueueInitMem,
      wordArrayInitMemory_size _ _ _ (by rw [hs, hp]; omega) (by rw [hp]; omega), hp]
    omega
  refine ⟨List.length_replicate, List.length_replicate, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [seenWords, List.length_map, List.length_replicate]
      omega
    · simp only [seenWords, List.length_map, List.length_replicate, le_refl]
    · rw [hs']; omega
    · have hpres := wordArrayInitMemory_prefix (wordArrayInitMemory mem ⟨128⟩ curr)
        (UInt256.ofNat (160 + 32 * curr)) len
      rw [updateWithdrawQueueInitMem, hpres.load_preserved (by decide)
        (by rw [hp]; omega) (by rw [hs]) (by decide)]
      simpa only [seenWords, List.length_map, List.length_replicate] using
        wordArrayInitMemory_length mem ⟨128⟩ curr
    · intro j hj
      simp only [seenWords, List.getElem_map, List.getElem_replicate]
      apply loadedWord_of_read
      · rw [ulit_toNat' _ (by omega), hs']; omega
      · change (wordArrayInitMemory _ _ _).readWithPadding _ _ = _
        rw [wordArrayInitMemory, hp, ulit_toNat' _ (by omega)]
        apply writeWord_read_zero_gap
        · rw [writeWord_sparse_size, hs]; omega
        · omega
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_replicate]; omega
    · omega
    · rw [hs']; omega
    · simpa only [List.length_replicate] using wordArrayInitMemory_length
        (wordArrayInitMemory mem ⟨128⟩ curr) (UInt256.ofNat (160 + 32 * curr)) len
    · intro j hj; omega
  · rw [updateWithdrawQueueInitMem,
      wordArrayInitMemory_free _ _ _ (by rw [hp]; omega), hp]
    congr 1
    omega

theorem UpdateWithdrawQueueMemory.scratch {mem : ByteArray} {curr len i : Nat}
    {seen : List Bool} {queue : List UInt256}
    (h : UpdateWithdrawQueueMemory mem curr len i seen queue) (word : UInt256) :
    UpdateWithdrawQueueMemory (wordAt0Mem word mem) curr len i seen queue := by
  refine ⟨h.seenLength, h.queueLength, h.seen.write_disjoint word (.inr (by decide)),
    h.queue.write_disjoint word (.inr (by omega)), ?_⟩
  rw [wordAt0Mem, memLoad_write_disjoint _ _ _ _
    (by change 96 ≤ mem.size; have := h.seen.size; omega) (.inr (by decide))]
  exact h.free

def updateWithdrawQueueBuildMem (mem : ByteArray) (curr prev i : Nat)
    (id : UInt256) : ByteArray :=
  writeWord (writeWord mem (160 + 32 * prev) ⟨1⟩) (192 + 32 * curr + 32 * i) id

theorem UpdateWithdrawQueueMemory.step {mem : ByteArray} {curr len i prev : Nat}
    {seen : List Bool} {queue : List UInt256}
    (h : UpdateWithdrawQueueMemory mem curr len i seen queue)
    (hp : prev < curr) (hi : i < len) (id : UInt256) :
    UpdateWithdrawQueueMemory (updateWithdrawQueueBuildMem mem curr prev i id)
      curr len (i + 1) (seen.set prev true) (queue.set i id) := by
  have hs : WordArrayPrefix (writeWord mem (160 + 32 * prev) ⟨1⟩)
      128 (seenWords (seen.set prev true)) curr := by
    simpa only [seenWords, List.map_set] using h.seen.set hp ⟨1⟩
  have hq := h.queue.write_disjoint (off := 160 + 32 * prev) ⟨1⟩ (.inr (by omega))
  refine ⟨by rw [List.length_set, h.seenLength],
    by rw [List.length_set, h.queueLength], ?_, ?_, ?_⟩
  · exact hs.write_disjoint id (.inl (by omega))
  · have he := hq.extend (by rw [h.queueLength]; exact hi) id
    simpa only [updateWithdrawQueueBuildMem,
      show 160 + 32 * curr + 32 = 192 + 32 * curr by omega] using he
  · rw [updateWithdrawQueueBuildMem, Reasoning.Theory.writeWord,
      memLoad_write_disjoint _ _ _ _
        (by change 96 ≤ (writeWord mem _ _).size
            rw [writeWord_sparse_size]; have := h.seen.size; omega)
        (.inl (by change 96 ≤ _; omega)),
      Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
        (by change 96 ≤ mem.size; have := h.seen.size; omega)
        (.inl (by change 96 ≤ _; omega))]
    exact h.free

end Benchmarks.Morpho.MetaMorphoV1_1
