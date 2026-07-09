import Benchmarks.Dss.Cat.BiteTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite` — external-call return-decode lemmas

`decode? "ilks"/"urns"/"kick"` computed on the raw returndata `o`, in the natural
`bytesToWord ((o.drop 32·i).take 32)` per-word form (matching the STATICCALL/CALL return-copy that
`Seg2b`/`Seg3`/`Seg8b1` read from memory). -/

private theorem oTake_len {o : ByteArray} {start : Nat} (h : start + 32 ≤ o.size) :
    ((o.toList.drop start).take 32).length = 32 := by
  have hlen : o.toList.length = o.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [List.length_take, List.length_drop, hlen]; omega

/-- `urns` returns `(uint256 ink, uint256 art)`. -/
theorem catBiteUrnsDecode_ok {o : ByteArray} (ho64 : 64 ≤ o.size) :
    config.externalABI.decode? "urns" o =
      some [.int (Int.ofNat (ABI.bytesToWord ((o.toList.drop 0).take 32)).toNat),
            .int (Int.ofNat (ABI.bytesToWord ((o.toList.drop 32).take 32)).toNat)] := by
  show ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [abiUInt256, abiUInt256] o = _
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiUInt256, abiUInt256]) (bytes := o.toList) (cursor := 0)
    (total := 32 * [abiUInt256, abiUInt256].length) (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05) (bytes := o.toList)
    (start := 0) (oTake_len (by omega))]
  simp only [bind, Option.bind]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05) (bytes := o.toList)
    (start := 32) (oTake_len (by omega))]

/-- `ilks` returns `(uint256 Art, uint256 rate, uint256 spot, uint256 line, uint256 dust)`. -/
theorem catBiteIlksDecode_ok {o : ByteArray} (ho160 : 160 ≤ o.size) :
    config.externalABI.decode? "ilks" o =
      some [.int (Int.ofNat (ABI.bytesToWord ((o.toList.drop 0).take 32)).toNat),
            .int (Int.ofNat (ABI.bytesToWord ((o.toList.drop 32).take 32)).toNat),
            .int (Int.ofNat (ABI.bytesToWord ((o.toList.drop 64).take 32)).toNat),
            .int (Int.ofNat (ABI.bytesToWord ((o.toList.drop 96).take 32)).toNat),
            .int (Int.ofNat (ABI.bytesToWord ((o.toList.drop 128).take 32)).toNat)] := by
  show ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
    [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256] o = _
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256]) (bytes := o.toList)
    (cursor := 0)
    (total := 32 * [abiUInt256, abiUInt256, abiUInt256, abiUInt256, abiUInt256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05) (bytes := o.toList)
    (start := 0) (oTake_len (by omega))]
  simp only [bind, Option.bind]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05) (bytes := o.toList)
    (start := 32) (oTake_len (by omega))]
  simp only [bind, Option.bind]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05) (bytes := o.toList)
    (start := 64) (oTake_len (by omega))]
  simp only [bind, Option.bind]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05) (bytes := o.toList)
    (start := 96) (oTake_len (by omega))]
  simp only [bind, Option.bind]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05) (bytes := o.toList)
    (start := 128) (oTake_len (by omega))]

/-- `kick` returns `(uint256 id)`. -/
theorem catBiteKickDecode_ok {o : ByteArray} (ho32 : 32 ≤ o.size) :
    config.externalABI.decode? "kick" o =
      some [.int (Int.ofNat (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))).toNat)] := by
  have hdec := decodeReturnValueWithMode_legacy_uint256_ok (returndata := o) ho32
  have hlt := fromByteArrayBigEndian_extract0_32_lt (returndata := o) ho32
  have hdec' :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 o =
        some (.int (Int.ofNat (fromByteArrayBigEndian (o.extract 0 32)))) := by
    simpa [uint256, uint256Int, abiUInt256] using hdec
  show decodeReturn? uint256 o =
    some [.int (Int.ofNat (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))).toNat)]
  unfold decodeReturn?
  rw [hdec']
  simp [UInt256.toNat_ofNat_of_lt hlt, Int.ofNat_eq_natCast]

/-- **`kick` return-decode short.** A `< 32`-byte return does not ABI-decode to the single `uint256`
`id` — the `returndatasize < 32` guard reverts. Dual of `catBiteKickDecode_ok`. -/
theorem catBiteKickDecode_none {o : ByteArray} (hoLt : o.size < 32) :
    config.externalABI.decode? "kick" o = none := by
  have hdec := decodeReturnValueWithMode_legacy_uint256_none_short (returndata := o) hoLt
  have hdec' :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 o = none := by
    simpa [uint256, uint256Int, abiUInt256] using hdec
  show decodeReturn? uint256 o = none
  unfold decodeReturn?
  rw [hdec']; rfl

end Benchmarks.Dss.Cat
