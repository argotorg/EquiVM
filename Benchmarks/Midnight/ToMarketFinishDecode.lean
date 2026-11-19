import Benchmarks.Midnight.ToMarketLastFields
import Benchmarks.Midnight.ToMarketFirstFields
import Benchmarks.Midnight.ToMarketEncodeReturn

/-! Completing the stored-market decoder and returning its typed ABI result. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightToMarketFinishDecode {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem bytes rdata : ByteArray} {aw ptr arrayPtr root anchor x0 x1 x2 x3 : UInt256}
    {σ : AccountMap} {base start k C : Nat} {R : List UInt256} (cs : List CollateralData)
    (hstack : R.length + 25 ≤ 1024)
    (hb : MemoryBytes mem base bytes) (hbase : 96 ≤ base)
    (hhead : start + 256 ≤ bytes.size) (hanchor : anchor.toNat + 32 = base + start)
    (hregion : base + bytes.size ≤ ptr.toNat) (hptr : ptr.toNat + 256 < 2^64)
    (hfirst : MemoryWords mem ptr.toNat (marketFirstWords bytes start))
    (hn : memLoad arrayPtr mem = UInt256.ofNat cs.length)
    (hnin : arrayPtr.toNat + 32 ≤ mem.size)
    (hc : CollateralListStored mem (arrayPtr + UInt256.ofNat 32) root.toNat cs)
    (harray : ptr.toNat + 256 ≤ arrayPtr.toNat)
    (hroot : arrayPtr.toNat + 32 ≤ root.toNat) (hsmall : root.toNat < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hm : (calldataWord bytes (start + 32)).toNat < EVM.addressModulus)
    (hl : (calldataWord bytes (start + 64)).toNat < EVM.addressModulus)
    (hoff : (calldataWord bytes (start + 96)).toNat < 2^64)
    (harrayhead : start + (calldataWord bytes (start + 96)).toNat + 32 ≤ bytes.size)
    (hcount : (calldataWord bytes (start + (calldataWord bytes (start + 96)).toNat)).toNat < 2^64)
    (hdecode : decodeCollateralElements
      (calldataWord bytes (start + (calldataWord bytes (start + 96)).toNat)).toNat bytes
      (start + (calldataWord bytes (start + 96)).toNat + 32) = some cs)
    (rd : RD midnightBytecode I g s0 ⟨1100⟩
      (x0 :: x1 :: x2 :: x3 :: arrayPtr :: ptr :: anchor :: R) mem aw rdata σ k C) :
    (decodeMarketData bytes start = none ∧ RDrev midnightBytecode g s0) ∨
    (decodeMarketData bytes start = some (MarketData.at bytes start cs) ∧
      RDret midnightBytecode g s0 σ (wordArrayBytes (MarketData.at bytes start cs).encodedWords)) := by
  rcases midnightToMarketLastFields (by omega) hb hhead hanchor hregion hptr rd with
    ⟨hd, hr⟩ | ⟨he, hliq, aw1, k1, C1, rd1⟩
  · exact Or.inl ⟨hd, hr⟩
  right
  refine ⟨decodeMarketData_of_elements hhead ⟨hm, hl, he, hliq⟩ hoff harrayhead hcount hdecode, ?_⟩
  let m := MarketData.at bytes start cs
  let tailMem := marketTailMemory mem ptr arrayPtr bytes start
  have hlen : cs.length < 2^64 := by rw [decodeCollateralElements_length hdecode]; exact hcount
  have hptrlo : 96 ≤ ptr.toNat := by omega
  have ha32 : (arrayPtr + UInt256.ofNat 32).toNat = arrayPtr.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hm7 : MemoryWords tailMem ptr.toNat ((m.words arrayPtr).take 7) := by
    have hh := hfirst.append_writeWordArray (marketTailWords bytes start arrayPtr) (by
      change ptr.toNat + 32 * 7 < 2^256
      omega)
    have hmid : UInt256.ofNat (AccountAddress.ofNat
        (calldataWord bytes (start + 32)).toNat).val = calldataWord bytes (start + 32) :=
      addressWord_eq_ofNat_address hm
    have hloan : UInt256.ofNat (AccountAddress.ofNat
        (calldataWord bytes (start + 64)).toNat).val = calldataWord bytes (start + 64) :=
      addressWord_eq_ofNat_address hl
    have henter : UInt256.ofNat (AccountAddress.ofNat
        (calldataWord bytes (start + 192)).toNat).val = calldataWord bytes (start + 192) :=
      addressWord_eq_ofNat_address he
    simpa only [m, MarketData.at, MarketData.words, List.take_succ_cons, List.take_zero,
      marketFirstWords, marketTailWords, List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceMul, List.cons_append, List.nil_append, hmid, hloan, henter] using hh
  have hn1 : memLoad arrayPtr tailMem = UInt256.ofNat cs.length := by
    dsimp only [tailMem]
    rw [marketTailMemory, memLoad_writeWordArray_preserved _ _ _ _ hnin (Or.inr (by
      change ptr.toNat + 96 + 32 * 4 ≤ arrayPtr.toNat
      omega)), hn]
  have hc1 : CollateralListStored tailMem (arrayPtr + UInt256.ofNat 32) root.toNat cs :=
    hc.writeWords_below (marketTailWords bytes start arrayPtr) hsmall (by
      change ptr.toNat + 96 + 32 * 4 ≤ (arrayPtr + UInt256.ofNat 32).toNat
      rw [ha32]; omega)
  have hf1 : memLoad (UInt256.ofNat 64) tailMem = root := by
    dsimp only [tailMem]
    rw [marketTailMemory, memLoad_writeWordArray_preserved _ _ _ _ (by
      have hs := hb.size
      change 64 + 32 ≤ mem.size
      omega) (Or.inl (by change 64 + 32 ≤ ptr.toNat + 96; omega)), hfree]
  have hliquid : UInt256.ofNat m.liquidatorGate.val = calldataWord bytes (start + 224) :=
    addressWord_eq_ofNat_address hliq
  rw [← hliquid] at rd1
  exact midnightToMarketEncodeReturn m (by simp only [List.length_cons]; omega) hm7 hn1
    (hnin.trans (writeWordArray_size_ge _ _ _)) hc1 hptrlo harray hroot hsmall hf1
    (by change root.toNat + 320 + 128 * cs.length < 2^256; omega) rd1

end Benchmarks.Midnight
