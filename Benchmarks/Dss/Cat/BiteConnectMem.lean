import Benchmarks.Dss.Cat.BiteTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-- **Return-data-copy span read.**  An EVM `STATICCALL`/`CALL` return copy is modeled as
    `o.write 0 base destAddr len` (copy `o[0,len)` into `base` at byte offset `destAddr`, extending
    `base` if it runs past the end).  A 32-byte read at an offset inside the copied region
    `[destAddr, destAddr+len)` returns the corresponding slice of `o`.

    (Hypothesis `destAddr ≤ base.size` added: without it the extending write uses `USize` gap
    arithmetic that can wrap, so the identity is not clean; `destAddr ≤ base.size` covers both the
    in-bounds and the memory-extending cases.) -/
theorem writeReturnCopy_read32 (o base : ByteArray) (destAddr len readAddr : ℕ)
    (hlen : len ≤ o.size)
    (hdest : destAddr ≤ base.size)
    (hlo : destAddr ≤ readAddr)
    (hhi : readAddr + 32 ≤ destAddr + len) :
    (o.write 0 base destAddr len).readWithPadding readAddr 32
      = o.extract (readAddr - destAddr) (readAddr - destAddr + 32) := by
  have hlne : len ≠ 0 := by omega
  have hPsz : (base.extract 0 destAddr).size = destAddr := by rw [ByteArray.size_extract]; omega
  have hMsz : (o.extract 0 len).size = len := by rw [ByteArray.size_extract]; omega
  have hPMsz : (base.extract 0 destAddr ++ o.extract 0 len).size = destAddr + len := by
    rw [ByteArray.size_append, hPsz, hMsz]
  -- The read lands inside the copied middle segment `o.extract 0 len`.
  have key : (base.extract 0 destAddr ++ o.extract 0 len).extract readAddr (readAddr + 32)
      = o.extract (readAddr - destAddr) (readAddr - destAddr + 32) := by
    rw [extract_append_right_window _ _ _ _ (by rw [hPsz]; omega), hPsz, extract_extract_BA,
      show 0 + (readAddr - destAddr) = readAddr - destAddr from by omega,
      show min (0 + (readAddr + 32 - destAddr)) len = readAddr - destAddr + 32 from by omega]
  by_cases hb : destAddr + len ≤ base.size
  · -- in-bounds splice: base[0,destAddr) ++ o[0,len) ++ base[destAddr+len, size)
    rw [write_eq_gen o base destAddr len hlne hlen hb]
    rw [readWithPadding_eq_extract _ readAddr
      (by rw [ByteArray.size_append, hPMsz, ByteArray.size_extract]; omega)]
    rw [extract_append_left _ _ _ _ (by rw [hPMsz]; omega)]
    exact key
  · -- extending splice: base[0,destAddr) ++ o[0,len)
    rw [write_eq_gen_extend o base destAddr len hlne hlen hdest (by omega)]
    rw [readWithPadding_eq_extract _ readAddr (by rw [hPMsz]; omega)]
    exact key

/-- **Word roundtrip.**  Reading 32 in-bounds bytes and big-endian decoding-then-re-encoding is the
    identity: the read equals `toByteArray` of its decoded word. -/
theorem readWithPadding_eq_toByteArray_ofNat (o : ByteArray) (readAddr : ℕ)
    (h : readAddr + 32 ≤ o.size) :
    o.readWithPadding readAddr 32 =
      UInt256.toByteArray (UInt256.ofNat (fromByteArrayBigEndian (o.extract readAddr (readAddr + 32)))) := by
  have hsize : (o.extract readAddr (readAddr + 32)).size = 32 := by
    rw [ByteArray.size_extract]; omega
  rw [readWithPadding_eq_extract o readAddr h]
  symm
  rw [← uInt256OfByteArray_eq (o.extract readAddr (readAddr + 32))]
  rw [← word_toBytesBE_toByteArray_eq_toByteArray (uInt256OfByteArray (o.extract readAddr (readAddr + 32)))]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [List.toList_data_toByteArray]
  simpa [byteArray_toList_eq] using toBytesBE_uInt256OfByteArray_of_size hsize

end Benchmarks.Dss.Cat
