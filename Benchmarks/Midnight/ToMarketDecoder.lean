import Benchmarks.Midnight.ToMarketAllocation
import Benchmarks.Midnight.ToMarketArrayHeader
import Benchmarks.Midnight.ToMarketArrayDecode

variable {fork : Ethereum.Fork}

/-! Complete stored-market decoding, allocation checks, and ABI return from pc 949. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightToMarketDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem bytes rdata : ByteArray} {aw ptr x finish anchor : UInt256}
    {σ : AccountMap} {base start k C : Nat} {R : List UInt256}
    (hstack : R.length + 25 ≤ 1024)
    (hb : MemoryBytes mem base bytes) (hbase : 96 ≤ base)
    (hhead : start + 256 ≤ bytes.size) (hanchor : anchor.toNat + 32 = base + start)
    (hregion : base + bytes.size ≤ ptr.toNat) (hptr : ptr.toNat < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hend : x.toNat + 32 = finish.toNat) (hfinish : finish.toNat = base + bytes.size)
    (hsmall : base + bytes.size < 2^128)
    (rd : RD fork midnightBytecode I g s0 ⟨949⟩ (finish :: x :: anchor :: R)
      mem aw rdata σ k C) :
    ((∀ m, decodeMarketData bytes start = some m →
        ¬ ptr.toNat + 288 + 160 * m.collaterals.length < 2^64) ∧ RDrev fork midnightBytecode g s0) ∨
    (∃ m, decodeMarketData bytes start = some m ∧
      ptr.toNat + 288 + 160 * m.collaterals.length < 2^64 ∧
      RDret fork midnightBytecode g s0 σ (wordArrayBytes m.encodedWords)) := by
  rcases midnightToMarketAllocation (by omega) hfree hptr rd with
    ⟨hcap, hr⟩ | ⟨hfit, aw1, k1, C1, rd1⟩
  · exact Or.inl ⟨fun _ _ ↦ by omega, hr⟩
  let allocMem := writeWord mem 64 (ptr + UInt256.ofNat 256)
  have hb1 : MemoryBytes allocMem base bytes := hb.writeWord _ (Or.inr hbase)
  rcases midnightToMarketFirstFields (by omega) hb1 hhead hanchor hregion hfit rd1 with
    ⟨hnone, hr⟩ | ⟨hm, hl, hoff, aw2, k2, C2, rd2⟩
  · left
    refine ⟨?_, hr⟩
    intro m hm
    rw [hnone] at hm
    cases hm
  let firstMem := marketFirstMemory allocMem ptr bytes start
  have hb2 : MemoryBytes firstMem base bytes := marketFirstMemory_bytes hb1 hregion
  have hf2 : memLoad (UInt256.ofNat 64) firstMem = ptr + UInt256.ofNat 256 :=
    marketFirstMemory_free (memLoad_writeWord mem (UInt256.ofNat 64) _)
      (by dsimp only [allocMem]; rw [writeWord_sparse_size]; omega) (by omega)
  have hm2 : MemoryWords firstMem ptr.toNat (marketFirstWords bytes start) :=
    MemoryWords.of_writeWordArray allocMem ptr.toNat (marketFirstWords bytes start)
      (by change ptr.toNat + 32 * 3 < 2^256; omega) (by simp [marketFirstWords])
  rcases midnightToMarketArrayHeader (by omega) hb2 hhead hanchor hfinish hsmall hoff rd2 with
    ⟨hnone, hr⟩ | ⟨harrayhead, hn, k3, C3, rd3⟩
  · left
    refine ⟨?_, hr⟩
    intro m hm
    rw [hnone] at hm
    cases hm
  have har : (anchor + calldataWord bytes (start + 96)).toNat =
      anchor.toNat + (calldataWord bytes (start + 96)).toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
  have hh : ((anchor + calldataWord bytes (start + 96)) + UInt256.ofNat 32).toNat =
      base + start + (calldataWord bytes (start + 96)).toNat := by
    rw [uadd_word_ofNat_toNat _ _ (by rw [har]; change _ < 2^256; omega), har]
    omega
  exact midnightToMarketArrayDecode hstack hb2 hbase hhead hanchor hregion hfit hm2 hf2
    hend hfinish hsmall hm hl hoff harrayhead rfl hn hh rd3

end Benchmarks.Midnight
