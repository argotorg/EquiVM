import Benchmarks.Midnight.MarketEncodeStart
import Benchmarks.Midnight.MarketEncodeEnd
import Benchmarks.Midnight.MarketEncode

/-! The ABI output region assembled by the market encoder's three phases. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem collateralWords_length (cs : List CollateralData) :
    (cs.flatMap CollateralData.words).length = 4 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, CollateralData.words, List.length_cons,
      List.length_nil, ih]
    omega

def marketEncodeMemory (mem : ByteArray) (output : Nat) (m : MarketData) : ByteArray :=
  writeWordArray
    (writeWordArray (marketEncodeHeadMemory mem output m) (output + 288)
      (m.collaterals.flatMap CollateralData.words))
    (output + 128) m.tailWords

theorem marketEncodeHeadMemory_prefix (mem : ByteArray) (output limit : Nat) (m : MarketData)
    (hbelow : limit ≤ output) : MemoryPrefix mem (marketEncodeHeadMemory mem output m) limit :=
  (memoryPrefix_writeWordArray mem output limit m.headWords hbelow).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega)))

theorem marketEncodeMemory_prefix (mem : ByteArray) (output limit : Nat) (m : MarketData)
    (hbelow : limit ≤ output) : MemoryPrefix mem (marketEncodeMemory mem output m) limit :=
  ((marketEncodeHeadMemory_prefix mem output limit m hbelow).trans
    (memoryPrefix_writeWordArray _ _ _ _ (by omega))).trans
    (memoryPrefix_writeWordArray _ _ _ _ (by omega))

theorem marketEncodeHeadMemory_preserve {mem : ByteArray} {output base : Nat}
    {words : List UInt256} (m : MarketData) (h : MemoryWords mem base words)
    (hbelow : base + 32 * words.length ≤ output) :
    MemoryWords (marketEncodeHeadMemory mem output m) base words :=
  (h.writeWords _ (Or.inl hbelow)).writeWord _ (Or.inl (by omega))

theorem marketEncodeMemory_words (mem : ByteArray) (output : Nat) (m : MarketData)
    (hb : output + 288 + 128 * m.collaterals.length < UInt256.size) :
    MemoryWords (marketEncodeMemory mem output m) output
      (m.words (UInt256.ofNat 256) ++ UInt256.ofNat m.collaterals.length ::
        m.collaterals.flatMap CollateralData.words) := by
  have hhead : m.headWords.length = 4 := rfl
  have htail : m.tailWords.length = 4 := rfl
  have hwords := collateralWords_length m.collaterals
  let headMem := marketEncodeHeadMemory mem output m
  let loopMem := writeWordArray headMem (output + 288) (m.collaterals.flatMap CollateralData.words)
  have hh : MemoryWords headMem output m.headWords :=
    (MemoryWords.of_writeWordArray mem output m.headWords (by simp only [hhead]; omega)
      (by simp [MarketData.headWords, MarketData.firstWords])).writeWord _
      (Or.inl (by simp only [hhead]; omega))
  have hn : MemoryWords headMem (output + 256) [UInt256.ofNat m.collaterals.length] := by
    exact MemoryWords.of_writeWordArray (writeWordArray mem output m.headWords) (output + 256)
      [UInt256.ofNat m.collaterals.length]
      (by simp only [List.length_cons, List.length_nil]; omega) (by simp)
  have hn' : MemoryWords loopMem (output + 256)
      (UInt256.ofNat m.collaterals.length :: m.collaterals.flatMap CollateralData.words) := by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc,
      List.cons_append, List.nil_append] using
      hn.append_writeWordArray (m.collaterals.flatMap CollateralData.words) (by
        simp only [List.length_append, List.length_cons, List.length_nil, hwords]; omega)
  have hh' : MemoryWords (marketEncodeMemory mem output m) output m.headWords :=
    (hh.writeWords _ (Or.inl (by simp only [hhead]; omega))).writeWords _
      (Or.inl (by simp only [hhead]; omega))
  have ht : MemoryWords (marketEncodeMemory mem output m) (output + 128) m.tailWords :=
    MemoryWords.of_writeWordArray loopMem _ _ (by simp only [htail]; omega)
      (by simp [MarketData.tailWords])
  have hn'' : MemoryWords (marketEncodeMemory mem output m) (output + 256)
      (UInt256.ofNat m.collaterals.length :: m.collaterals.flatMap CollateralData.words) :=
    hn'.writeWords _ (Or.inr (by simp only [htail]; omega))
  have hfull : MemoryWords (marketEncodeMemory mem output m) output
      (m.headWords ++ m.tailWords) := hh'.append (by simpa only [hhead, Nat.reduceMul] using ht)
  exact hfull.append (by
    simpa only [List.length_append, hhead, htail, Nat.reduceAdd, Nat.reduceMul] using hn'')

end Benchmarks.Midnight
