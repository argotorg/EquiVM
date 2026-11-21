import Benchmarks.Midnight.MulticallTailBounds

/-! ABI decoding of one direct bytes reference in a multicall array. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

set_option maxHeartbeats 1000000

def decodeMulticallTail (bytes : ByteArray) (base : UInt256) (index : Nat) : Option ByteArray :=
  if MulticallTailValid bytes base index then some (multicallBytesAt bytes base index) else none

-- LIBRARY CANDIDATE: the ABI signed comparison agrees with the EVM Boolean operation.
theorem solcSLT_words (a b : UInt256) : solcSLT a.toNat b.toNat = UInt256.sltBool a b := by
  unfold solcSLT
  change decide (EVM.signed (UInt256.ofNat a.toNat) < EVM.signed (UInt256.ofNat b.toNat)) = _
  rw [u256_ofNat_toNat, u256_ofNat_toNat, sltBool_signed]

theorem sgtBool_eq_sltBool (a b : UInt256) : UInt256.sgtBool a b = UInt256.sltBool b a := by
  unfold UInt256.sgtBool UInt256.sltBool
  by_cases ha : 2^255 ≤ a.toNat <;> by_cases hb : 2^255 ≤ b.toNat <;>
    simp only [ha, hb, if_true, if_false]

theorem solcMulticallTailTarget {bytes : ByteArray} {base : UInt256} {index : Nat}
    (hs : bytes.size < UInt256.size) (hb : base.toNat + 32 * index + 32 ≤ bytes.size) :
    solcTailTarget? true .bytes bytes.toList base.toNat (solcAdd base.toNat (32 * index)) =
      if UInt256.sltBool (multicallTailOffset bytes base index) (multicallTailBound bytes base)
        then some (multicallTailHead bytes base index).toNat else none := by
  have hslot : solcAdd base.toNat (32 * index) = base.toNat + 32 * index :=
    Nat.mod_eq_of_lt (by change _ < UInt256.size; omega)
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hbound : solcSub (solcSub bytes.size base.toNat) (solcSub 32 1) =
      (multicallTailBound bytes base).toNat := by
    change (UInt256.sub (UInt256.ofNat (UInt256.sub (UInt256.ofNat bytes.size)
      (UInt256.ofNat base.toNat)).toNat) (UInt256.ofNat 31)).toNat = _
    rw [u256_ofNat_toNat, u256_ofNat_toNat]
    rfl
  have hhead : solcAdd base.toNat (multicallTailOffset bytes base index).toNat =
      (multicallTailHead bytes base index).toNat := (uadd_toNat _ _).symm
  simp only [solcTailTarget?, tailSize?, if_true, bind, Option.bind, hslot,
    solcReadNat_bounded hb hs, hl]
  change (if !(solcSLT (multicallTailOffset bytes base index).toNat
    (solcSub (solcSub bytes.size base.toNat) (solcSub 32 1))) then none
    else some (solcAdd base.toNat (multicallTailOffset bytes base index).toNat)) = _
  rw [hbound, solcSLT_words, hhead]
  cases UInt256.sltBool (multicallTailOffset bytes base index) (multicallTailBound bytes base) <;>
    rfl

theorem solcMulticallTailExtent (bytes : ByteArray) (base : UInt256) (index : Nat) :
    badExtent false true bytes.toList (multicallTailHead bytes base index).toNat
      (multicallTailLength bytes base index).toNat 1 =
      UInt256.sgtBool (multicallTailPointer bytes base index)
        (UInt256.sub (UInt256.ofNat bytes.size) (multicallTailLength bytes base index)) := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hp : solcAdd (multicallTailHead bytes base index).toNat 32 =
      (multicallTailPointer bytes base index).toNat := by
    rw [multicallTailPointer, u256_add_comm, uadd_toNat]
    rfl
  simp only [badExtent, Bool.not_true, Bool.false_and, Bool.not_false, Bool.and_self,
    if_true, Bool.false_or, hl, Nat.mul_one, hp]
  unfold solcSub
  change solcSLT (UInt256.sub (UInt256.ofNat bytes.size)
    (UInt256.ofNat (multicallTailLength bytes base index).toNat)).toNat
      (multicallTailPointer bytes base index).toNat = _
  rw [u256_ofNat_toNat, solcSLT_words, sgtBool_eq_sltBool]

theorem solcMulticallTailPayload {bytes : ByteArray} {base : UInt256} {index : Nat}
    (hs : bytes.size < 2^255) (hb : base.toNat + 32 ≤ bytes.size)
    (hv : MulticallTailValid bytes base index) :
    (decodeABIValue? .bytes
      (solcReadBytes bytes.toList (multicallTailHead bytes base index).toNat
        (32 + (multicallTailLength bytes base index).toNat)) 0).map Prod.fst =
      some (.bytes (multicallBytesAt bytes base index)) := by
  rcases hv.bounds hs hb with hz | hbound
  · rw [hz, Nat.add_zero]
    rw [solcBytesPayload_empty hz]
    simp only [multicallBytesAt, hz, byteArray_readWithPadding_zero]
  · have hp := solcBytesPayload (by change bytes.size < 2^256; omega) hv.2.1 hbound
    change (decodeABIValue? .bytes
      (solcReadBytes bytes.toList (multicallTailHead bytes base index).toNat
        (32 + (multicallTailLength bytes base index).toNat)) 0).map Prod.fst =
      some (.bytes (bytes.extract ((multicallTailHead bytes base index).toNat + 32)
        ((multicallTailHead bytes base index).toNat + 32 +
          (multicallTailLength bytes base index).toNat))) at hp
    rw [hp]
    congr 2
    unfold multicallBytesAt
    rw [multicallTailPointer, u256_add_comm,
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)]
    by_cases hz : (multicallTailLength bytes base index).toNat = 0
    · rw [hz, byteArray_readWithPadding_zero]
      exact byteArray_extract_empty_of_le _ (by omega)
    · exact (readWithPadding_eq_extract_unbounded _ _ _ (by omega) hbound).symm

theorem solcDecodeMulticallTail {bytes : ByteArray} {base : UInt256} {index : Nat}
    (hs : bytes.size < 2^255) (hb : base.toNat + 32 * index + 32 ≤ bytes.size) :
    (do
      let target ← solcTailTarget? true .bytes bytes.toList base.toNat
        (solcAdd base.toNat (32 * index))
      decodeValue? .bytes bytes.toList target { materialize := [] } true) =
      (decodeMulticallTail bytes base index).map Value.bytes := by
  rw [solcMulticallTailTarget (by change bytes.size < 2^256; omega) hb]
  unfold decodeMulticallTail
  by_cases ho : UInt256.sltBool (multicallTailOffset bytes base index)
      (multicallTailBound bytes base) = true
  · rw [if_pos ho]
    simp only [bind, Option.bind]
    rw [decodeValue?, solcReadNat_word]
    change (if decide (solcMaxU64 < (multicallTailLength bytes base index).toNat) ||
        badExtent false true bytes.toList (multicallTailHead bytes base index).toNat
          (multicallTailLength bytes base index).toNat 1 then none else _) = _
    rw [solcMulticallTailExtent]
    change (if decide (solcMaxU64 < (multicallTailLength bytes base index).toNat) ||
        UInt256.sgtBool (multicallTailPointer bytes base index)
          (UInt256.sub (UInt256.ofNat bytes.size) (multicallTailLength bytes base index)) then none
      else _) = _
    by_cases hn : (multicallTailLength bytes base index).toNat < 2^64
    · have hmax : ¬ solcMaxU64 < (multicallTailLength bytes base index).toNat := by
        change ¬ (2^64 - 1 < _); omega
      simp only [hmax, decide_false, Bool.false_or]
      by_cases he : UInt256.sgtBool (multicallTailPointer bytes base index)
          (UInt256.sub (UInt256.ofNat bytes.size) (multicallTailLength bytes base index)) = false
      · have hv : MulticallTailValid bytes base index := ⟨ho, hn, he⟩
        rw [he, if_neg Bool.false_ne_true, if_pos hv, Option.map_some]
        exact solcMulticallTailPayload hs (by omega) hv
      · have he' := Bool.eq_true_of_not_eq_false he
        have hv : ¬ MulticallTailValid bytes base index := fun h ↦ he h.2.2
        rw [he', if_pos rfl, if_neg hv]
        rfl
    · have hmax : solcMaxU64 < (multicallTailLength bytes base index).toNat := by
        change 2^64 - 1 < _; omega
      have hv : ¬ MulticallTailValid bytes base index := fun h ↦ hn h.2.1
      simp only [hmax, decide_true, Bool.true_or, if_true, if_neg hv, Option.map_none]
  · have hv : ¬ MulticallTailValid bytes base index := fun h ↦ ho h.1
    simp only [if_neg ho, if_neg hv, bind, Option.bind, Option.map_none]

end Benchmarks.Midnight
