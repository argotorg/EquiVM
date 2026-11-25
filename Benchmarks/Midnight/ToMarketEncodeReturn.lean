import Benchmarks.Midnight.MarketEncoder

variable {fork : Ethereum.Fork}

/-! Completing the market record, ABI encoding it, and executing the getter's RETURN. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightToMarketEncodeReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr root : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 18 ≤ 1024)
    (hm : MemoryWords mem ptr.toNat ((m.words arrayPtr).take 7))
    (hn : memLoad arrayPtr mem = UInt256.ofNat m.collaterals.length)
    (hnin : arrayPtr.toNat + 32 ≤ mem.size)
    (hc : CollateralListStored mem (arrayPtr + UInt256.ofNat 32) root.toNat m.collaterals)
    (hptr : 96 ≤ ptr.toNat) (harray : ptr.toNat + 256 ≤ arrayPtr.toNat)
    (hroot : arrayPtr.toNat + 32 ≤ root.toNat) (hsmall : root.toNat < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hout : root.toNat + 320 + 128 * m.collaterals.length < UInt256.size)
    (rd : RD fork midnightBytecode I g s0 ⟨1159⟩
      (UInt256.ofNat m.liquidatorGate.val :: ptr :: ⟨1184⟩ :: R) mem aw rdata σ k C) :
    RDret fork midnightBytecode g s0 σ (wordArrayBytes m.encodedWords) := by
  have hlen : ((m.words arrayPtr).take 7).length = 7 := rfl
  have hp224 : (ptr + UInt256.ofNat 224).toNat = ptr.toNat + 224 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have ha32 : (arrayPtr + UInt256.ofNat 32).toNat = arrayPtr.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hr32 : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  let doneMem := writeWord mem (ptr.toNat + 224) (UInt256.ofNat m.liquidatorGate.val)
  let packetMem := writeWord doneMem root.toNat (UInt256.ofNat 32)
  have hm1 : MemoryWords doneMem ptr.toNat (m.words arrayPtr) := by
    simpa only [hlen, Nat.reduceMul] using
      hm.append_writeWordArray [UInt256.ofNat m.liquidatorGate.val] (by
        simp only [List.length_append, List.length_cons, List.length_nil, hlen]
        change ptr.toNat + 32 * (7 + (0 + 1)) < 2^256
        omega)
  have hn1 : memLoad arrayPtr doneMem = UInt256.ofNat m.collaterals.length := by
    rw [memLoad_writeWord_preserved _ _ _ _ hnin (Or.inr (by omega)), hn]
  have hs1 := hc.writeWord_below (UInt256.ofNat m.liquidatorGate.val) hsmall
    (off := ptr.toNat + 224) (by rw [ha32]; omega)
  have hf1 : memLoad (UInt256.ofNat 64) doneMem = root := by
    rw [memLoad_writeWord_preserved _ _ _ _ (by
      have hs := hm.size
      rw [hlen] at hs
      change 64 + 32 ≤ mem.size
      omega) (Or.inl (by change 64 + 32 ≤ ptr.toNat + 224; omega)), hfree]
  have hm2 : MemoryWords packetMem ptr.toNat (m.words arrayPtr) :=
    hm1.writeWord _ (Or.inl (by change ptr.toNat + 32 * 8 ≤ root.toNat; omega))
  have hn2 : memLoad arrayPtr packetMem = UInt256.ofNat m.collaterals.length := by
    rw [memLoad_writeWord_preserved _ _ _ _ (by
      dsimp only [doneMem]
      rw [writeWord_sparse_size]
      omega) (Or.inl hroot), hn1]
  have hs2 := hs1.preserve (memoryPrefix_writeWord doneMem root.toNat root.toNat
    (UInt256.ofNat 32) (Or.inl le_rfl))
  have rd1 := midnightBlocks.midnight_block_1159 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_1159_stack, midnightBlocks.midnight_block_1159_memory,
    hp224] at rd1
  change RD fork midnightBytecode I g s0 ⟨19181⟩
    (ptr :: (memLoad (UInt256.ofNat 64) doneMem + UInt256.ofNat 32) :: ⟨1184⟩ ::
      memLoad (UInt256.ofNat 64) doneMem :: memLoad (UInt256.ofNat 64) doneMem :: R)
    (writeWord doneMem (memLoad (UInt256.ofNat 64) doneMem).toNat (UInt256.ofNat 32))
    _ rdata σ _ _ at rd1
  rw [hf1] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := midnightMarketEncoder m
    (by simp only [List.length_cons]; omega) hm2 hn2 (by
      dsimp only [packetMem, doneMem]
      rw [writeWord_sparse_size, writeWord_sparse_size]
      omega) hs2 (by omega) hroot (by rw [hr32]; omega)
      (by rw [hr32]; omega) (by jump_dest) rd1
  have hret := midnightBlocks.midnight_block_1184 (by omega) rd2
  let finalMem := marketEncodeMemory packetMem (root + UInt256.ofNat 32).toNat m
  have hpref := marketEncodeMemory_prefix packetMem (root + UInt256.ofNat 32).toNat
    (root.toNat + 32) m (by rw [hr32])
  have hr : MemoryWords packetMem root.toNat [UInt256.ofNat 32] :=
    MemoryWords.of_writeWordArray doneMem root.toNat [UInt256.ofNat 32]
      (by simp only [List.length_cons, List.length_nil]; omega) (by simp)
  have hr' : MemoryWords finalMem root.toNat [UInt256.ofNat 32] := by
    apply hr.preserve hpref.size
    intro read hlo hhi
    exact hpref.load read (by omega) (by simpa using hhi) (hhi.trans hr.size)
  have hmout : MemoryWords finalMem (root + UInt256.ofNat 32).toNat
      (m.words (UInt256.ofNat 256) ++ UInt256.ofNat m.collaterals.length ::
        m.collaterals.flatMap CollateralData.words) :=
    marketEncodeMemory_words packetMem (root + UInt256.ofNat 32).toNat m (by rw [hr32]; omega)
  have hfull : MemoryWords finalMem root.toNat m.encodedWords :=
    hr'.append (by simpa only [hr32, List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceMul] using hmout)
  have he : ((root + UInt256.ofNat 32) +
      UInt256.ofNat (288 + 128 * m.collaterals.length)).toNat =
      root.toNat + 320 + 128 * m.collaterals.length := by
    rw [uadd_word_ofNat_toNat _ _ (by rw [hr32]; omega), hr32]
    omega
  have hl : (UInt256.sub ((root + UInt256.ofNat 32) +
      UInt256.ofNat (288 + 128 * m.collaterals.length)) root).toNat =
      32 * m.encodedWords.length := by
    rw [usub_toNat (by rw [he]; omega), he, MarketData.encodedWords_length]
    omega
  rw [hl] at hret
  change RDret fork midnightBytecode g s0 σ
    (finalMem.readWithPadding root.toNat (32 * m.encodedWords.length)) at hret
  rw [hfull.read] at hret
  exact hret

end Benchmarks.Midnight
