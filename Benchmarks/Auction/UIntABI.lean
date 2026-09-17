import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: a scalar uint word's range guard, for an arbitrary bit width and position.
theorem decodeScalarWord_uint_result (bits : BitWidth) {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWord? (.elem (.int (.uint bits))) bytes start =
      if (ABI.bytesToWord ((bytes.drop start).take 32)).toNat < EVM.twoPow bits.val then
        some (.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat), start + 32)
      else none := by
  simp only [decodeScalarWord?, readWord?, readBytes?, hlen, if_true, bind, Option.bind,
    decodeABIWord?]
  rw [if_neg (Nat.ne_of_gt bits.property.1)]
  by_cases hc : (ABI.bytesToWord ((bytes.drop start).take 32)).toNat < EVM.twoPow bits.val
  · dsimp only [UInt256.toNat] at hc
    simp only [UInt256.toNat, if_pos hc]
  · dsimp only [UInt256.toNat] at hc
    simp only [UInt256.toNat, if_neg hc]


-- GENERALIZES Reasoning.Theory.decodeCalldata_uint256_ok by parameterizing the bit width.
theorem decodeCalldata_uint_result (bits : BitWidth) {cd : ByteArray} {name : Ident}
    (hlen : 36 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4) :
    decodeCalldata [name] [.elem (.int (.uint bits))] cd =
      if (calldataWord cd 4).toNat < EVM.twoPow bits.val then
        some ((∅ : Store).insert name (.int (Int.ofNat (calldataWord cd 4).toNat)))
      else none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (by rfl)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_uint_result bits (by simpa only [List.drop_zero] using htake)]
  simp only [List.drop_zero, hword]
  by_cases hc : (calldataWord cd 4).toNat < EVM.twoPow bits.val
  · simp [hc, decodeCalldata.insertValues]
  · simp [hc]

-- GENERALIZES Reasoning.Theory.decodeCalldata_uint256_none_short by bit width.
theorem decodeCalldata_uint_none_short (bits : BitWidth) {cd : ByteArray} {name : Ident}
    (hshort : cd.size < 36) :
    decodeCalldata [name] [.elem (.int (.uint bits))] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (by rfl)]
  by_cases hsz4 : cd.toList.length < 4
  · rw [if_pos hsz4]
  · rw [if_neg hsz4]
    rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
    simp only [decodeScalarWords?, decodeScalarWord?, readWord?, readBytes?, List.drop_zero]
    rw [if_neg (by rw [List.length_take, List.length_drop, htlen]; omega)]
    rfl

-- GENERALIZES Reasoning.Theory.decodeCalldata_uint256_none_huge by bit width.
theorem decodeCalldata_uint_none_huge (bits : BitWidth) {cd : ByteArray} {name : Ident}
    (hhuge : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [name] [.elem (.int (.uint bits))] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (by rfl)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos ⟨rfl, by rw [List.length_drop, htlen]; omega⟩]

end Auction
