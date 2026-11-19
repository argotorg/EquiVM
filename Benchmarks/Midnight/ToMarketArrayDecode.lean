import Benchmarks.Midnight.ToMarketHeapMemory
import Benchmarks.Midnight.ToMarketCollateralLoop
import Benchmarks.Midnight.ToMarketFinishDecode

/-! Composing pointer-array allocation, collateral decoding, and the getter's final fields. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightToMarketArrayDecode {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem bytes rdata : ByteArray} {aw ptr n header x finish anchor : UInt256}
    {σ : AccountMap} {base start k C : Nat} {R : List UInt256}
    (hstack : R.length + 25 ≤ 1024)
    (hb : MemoryBytes mem base bytes) (hbase : 96 ≤ base)
    (hhead : start + 256 ≤ bytes.size) (hanchor : anchor.toNat + 32 = base + start)
    (hregion : base + bytes.size ≤ ptr.toNat) (hptr : ptr.toNat + 256 < 2^64)
    (hfirst : MemoryWords mem ptr.toNat (marketFirstWords bytes start))
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr + UInt256.ofNat 256)
    (hend : x.toNat + 32 = finish.toNat) (hfinish : finish.toNat = base + bytes.size)
    (hsmall : base + bytes.size < 2^128)
    (hm : (calldataWord bytes (start + 32)).toNat < EVM.addressModulus)
    (hl : (calldataWord bytes (start + 64)).toNat < EVM.addressModulus)
    (hoff : (calldataWord bytes (start + 96)).toNat < 2^64)
    (harrayhead : start + (calldataWord bytes (start + 96)).toNat + 32 ≤ bytes.size)
    (hnword : n = calldataWord bytes (start + (calldataWord bytes (start + 96)).toNat))
    (hn : n.toNat < 2^64)
    (hheader : header.toNat = base + start + (calldataWord bytes (start + 96)).toNat)
    (rd : RD midnightBytecode I g s0 ⟨1051⟩
      (UInt256.ofNat (pointerArrayAllocation n.toNat) :: x :: finish :: n :: header :: ptr :: anchor :: R)
      mem aw rdata σ k C) :
    ((∀ m, decodeMarketData bytes start = some m →
        ¬ ptr.toNat + 288 + 160 * m.collaterals.length < 2^64) ∧ RDrev midnightBytecode g s0) ∨
    (∃ m, decodeMarketData bytes start = some m ∧
      ptr.toNat + 288 + 160 * m.collaterals.length < 2^64 ∧
      RDret midnightBytecode g s0 σ (wordArrayBytes m.encodedWords)) := by
  have count {m : MarketData} (hd : decodeMarketData bytes start = some m) :
      m.collaterals.length = n.toNat := by
    rw [decodeMarketData_collateralCount hd, hnword]
  let arrayPtr := ptr + UInt256.ofNat 256
  let dataPtr := arrayPtr + UInt256.ofNat (pointerArrayAllocation n.toNat)
  have ha : arrayPtr.toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hd : dataPtr.toNat = ptr.toNat + 288 + 32 * n.toNat := by
    rw [show dataPtr = arrayPtr + UInt256.ofNat (pointerArrayAllocation n.toNat) from rfl,
      uadd_word_ofNat_toNat _ _ (by rw [ha]; change _ + (32 + 32 * n.toNat) < 2^256; omega),
      ha, pointerArrayAllocation]
    omega
  rcases midnightToMarketArrayAllocation (by simp only [List.length_cons]; omega)
      hfree (by rw [ha]; exact hptr) hn (by rw [hheader]; omega) rd with
    ⟨hcap, hr⟩ | ⟨hshort, hr⟩ | ⟨hfit, hbound, aw1, k1, C1, rd1⟩
  · left
    refine ⟨fun m hm ↦ ?_, hr⟩
    rw [count hm]
    change ¬ arrayPtr.toNat + (32 + 32 * n.toNat) < 2^64 at hcap
    rw [ha] at hcap
    omega
  · left
    refine ⟨fun m hm ↦ ?_, hr⟩
    rcases decodeMarketData_success hm with ⟨_, _, _, _, _, cs, hc, _⟩
    rw [← hnword] at hc
    have hb' := decodeCollateralElements_bound hc
    rw [hheader, hfinish] at hshort
    omega
  · let arrayMem := marketArrayMemory mem arrayPtr n
    have haw : (arrayPtr + UInt256.ofNat 32).toNat = arrayPtr.toNat + 32 :=
      uadd_word_ofNat_toNat _ _ (by rw [ha]; change _ < 2^256; omega)
    have hread : (UInt256.ofNat 32 + header).toNat = header.toNat + 32 := by
      rw [uadd_toNat]
      change (32 + header.toNat) % UInt256.size = header.toNat + 32
      rw [Nat.mod_eq_of_lt (by rw [hheader]; change _ < 2^256; omega)]
      omega
    have hstop : (UInt256.ofNat (header.toNat + 32 + 128 * n.toNat)).toNat =
        header.toNat + 32 + 128 * n.toNat :=
      UInt256.toNat_ofNat_of_lt (by have hf : finish.toNat < UInt256.size := finish.val.isLt; omega)
    have hb1 : MemoryBytes arrayMem base bytes := marketArrayMemory_bytes hb hbase (by rw [ha]; omega)
    have hf1 : memLoad (UInt256.ofNat 64) arrayMem = dataPtr := marketArrayMemory_free (by rw [ha]; omega)
    have hdata : dataPtr.toNat < 2^64 := by
      change arrayPtr.toNat + pointerArrayAllocation n.toNat < 2^64 at hfit
      rw [show dataPtr.toNat = arrayPtr.toNat + pointerArrayAllocation n.toNat from
        uadd_word_ofNat_toNat _ _ (by rw [ha]; change _ + (32 + 32 * n.toNat) < 2^256; omega)]
      exact hfit
    have hptrarray : (arrayPtr + UInt256.ofNat 32).toNat + 32 * n.toNat ≤ dataPtr.toNat := by
      simp only [haw, ha, hd]; omega
    rcases midnightToMarketCollateralLoop
        (start := start + (calldataWord bytes (start + 96)).toNat + 32)
        (ptr := dataPtr) (readPtr := UInt256.ofNat 32 + header)
        (writePtr := arrayPtr + UInt256.ofNat 32)
        (by simp only [List.length_cons]; omega)
        hb1 hbase (by rw [hheader, hfinish] at hbound; omega)
        (by rw [hread, hheader]; omega) (hend.trans hfinish) hsmall
        (by rw [hstop, hread]) hdata hf1 (by rw [haw, ha]; omega) hptrarray rd1 with
      ⟨hnone, hr⟩ | ⟨hcap, hr⟩ | ⟨cs, hc, hfit', hb2, hf2, aw2, k2, C2, rd2⟩
    · left
      refine ⟨fun m hm ↦ ?_, hr⟩
      rcases decodeMarketData_success hm with ⟨_, _, _, _, _, cs, hc, _⟩
      rw [← hnword] at hc
      rw [hnone] at hc
      cases hc
    · left
      refine ⟨fun m hm ↦ ?_, hr⟩
      rw [count hm]
      rw [hd] at hcap
      omega
    · have hclen : cs.length = n.toNat := decodeCollateralElements_length hc
      let root := dataPtr + UInt256.ofNat (128 * n.toNat)
      have hroot : root.toNat = dataPtr.toNat + 128 * n.toNat :=
        uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
      have hrootsmall : root.toNat < 2^64 := by rw [hroot]; exact hfit'
      have hm1 : MemoryWords arrayMem ptr.toNat (marketFirstWords bytes start) :=
        marketArrayMemory_preserve hfirst (by omega) (by
          change ptr.toNat + 32 * 3 ≤ arrayPtr.toNat
          rw [ha]; omega)
      have hm2 := hm1.collateralLoop (ptr := dataPtr) (writePtr := arrayPtr + UInt256.ofNat 32) cs (by omega) (by
        change ptr.toNat + 32 * 3 ≤ (arrayPtr + UInt256.ofNat 32).toNat
        rw [haw, ha]; omega) (by rw [hclen]; exact hfit') (by rw [hclen]; exact hptrarray)
      have hh := (marketArrayMemory_header (mem := mem) (ptr := arrayPtr) (n := n)
        (by rw [ha]; change _ < 2^256; omega)).collateralLoop (ptr := dataPtr) (writePtr := arrayPtr + UInt256.ofNat 32) cs (by rw [ha]; omega)
        (by simp only [haw, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]; omega) (by rw [hclen]; exact hfit') (by rw [hclen]; exact hptrarray)
      have hn2 : memLoad arrayPtr (collateralLoopMemory arrayMem dataPtr (arrayPtr + UInt256.ofNat 32) cs) =
          UInt256.ofNat cs.length := by
        have hreadn : memLoad arrayPtr
            (collateralLoopMemory arrayMem dataPtr (arrayPtr + UInt256.ofNat 32) cs) = n :=
          hh.load_word ⟨0, by simp⟩ (by simp)
        rw [hreadn, hclen, u256_ofNat_toNat]
      have hc2 := collateralLoopMemory_stored (mem := arrayMem) (ptr := dataPtr)
        (writePtr := arrayPtr + UInt256.ofNat 32) cs (by rw [hclen]; exact hfit')
        (by rw [hclen]; exact hptrarray) (by rw [haw, ha]; omega)
      rw [hclen, ← hroot] at hc2
      rcases midnightToMarketFinishDecode cs hstack hb2 hbase hhead hanchor hregion hptr
          hm2 hn2 hh.size hc2 (by rw [ha]) (by rw [hroot, ha, hd]; omega) hrootsmall hf2 hm hl hoff
          harrayhead (by rw [← hnword]; exact hn) (by simpa only [hnword] using hc) rd2 with
        ⟨hnone, hr⟩ | ⟨hdecoded, hr⟩
      · left
        refine ⟨?_, hr⟩
        intro m hm
        rw [hnone] at hm
        cases hm
      · right
        refine ⟨MarketData.at bytes start cs, hdecoded, ?_, hr⟩
        change ptr.toNat + 288 + 160 * cs.length < 2^64
        rw [hclen]
        rw [hd] at hfit'
        omega

end Benchmarks.Midnight
