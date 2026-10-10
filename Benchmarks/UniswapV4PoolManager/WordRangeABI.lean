import Benchmarks.UniswapV4PoolManager.Values

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: the static bytes32/uint256 ABI pair.
theorem decodeABIValues_bytes32_uint256_ok {bytes : List UInt8}
    (h0 : (bytes.take 32).length = 32) (h32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiUInt256] bytes 0 0 64 64 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, abiBytes32, abiUInt256, abiBytes32Width, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, zeroPadding?, h0]
  simp [readWord?, readBytes?, decodeABIWord?, h32, UInt256.toNat]
  have hw : ((ABI.bytesToWord ((bytes.drop 32).take 32)).val : Nat) < EVM.twoPow 256 :=
    (ABI.bytesToWord ((bytes.drop 32).take 32)).val.isLt
  rw [if_pos hw]
  simp [List.take_take]

theorem decodeCalldata_bytes32_uint256_ok {cd : ByteArray} {x y : Ident}
    (hlen : 68 ≤ cd.size) (hbig : cd.size < 2^255+4) :
    decodeCalldata [x, y] [abiBytes32, abiUInt256] cd =
      some (((∅ : Store).insert x (wordBytes32Value (calldataWord cd 4))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have h4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have h36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hw36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq_any cd 36 hlen
  have hw4 : (cd.toList.drop 4).take 32 = EVM.Word.toBytesBE (calldataWord cd 4) := by
    have hw : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
      decode_word_at_eq_any cd 4 (by omega)
    rw [← hw, toBytesBE_bytesToWord_of_length h4]
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]
  rw [decodeABIValues_bytes32_uint256_ok h4
    (by simpa only [List.drop_drop, show (4:Nat)+32=36 from rfl] using h36)]
  simp only [bind, Option.bind, decodeCalldata.insertValues, List.drop_drop,
    show (4:Nat)+32=36 from rfl, hw36, hw4, wordBytes32Value]

theorem decodeCalldata_bytes32_uint256_none_short {cd : ByteArray} {x y : Ident}
    (h4 : 4 ≤ cd.size) (hlen : cd.size < 68) :
    decodeCalldata [x,y] [abiBytes32,abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [if_pos (by rw [List.length_drop, htlen]; omega : (cd.toList.drop 4).length < 64)]

theorem decodeCalldata_bytes32_uint256_none_huge {cd : ByteArray} {x y : Ident}
    (hlen : 2^255+4 ≤ cd.size) :
    decodeCalldata [x,y] [abiBytes32,abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  rw [if_pos ⟨rfl, by rw [List.length_drop, htlen]; omega⟩]

end Benchmarks.UniswapV4PoolManager
