import Benchmarks.Morpho.MorphoBlue.BodyCommon
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: dynamic bytes are bounded by their length word and their payload.
def CalldataBytesBounds (cd : ByteArray) (start : Nat) : Prop :=
  start + 32 ≤ cd.size ∧ (calldataWord cd start).toNat ≤ solcMaxU64 ∧
    start + 32 + (calldataWord cd start).toNat ≤ cd.size

instance (cd : ByteArray) (start : Nat) : Decidable (CalldataBytesBounds cd start) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def calldataBytesPayload (cd : ByteArray) (start : Nat) : ByteArray :=
  ByteArray.mk (((cd.toList.drop (start + 32)).take (calldataWord cd start).toNat).toArray)

-- GENERALIZES decodeABIValue_legacyBytes_ok to modern decoding and all failing bounds.
theorem decodeABIValue_bytes_calldata_eq (cd : ByteArray) (off : Nat) :
    decodeABIValue? .bytes (cd.toList.drop 4) off =
      if CalldataBytesBounds cd (4 + off) then
        some (.bytes (calldataBytesPayload cd (4 + off)),
          off + 32 + paddedSize (calldataWord cd (4 + off)).toNat)
      else none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  by_cases hh : 4 + off + 32 ≤ cd.size
  · have hr := readNat_drop4_at_eq_calldataWord (cd := cd) off hh
    rw [decodeABIValue?]
    simp only [hr, bind, Option.bind, solcMaxLen]
    by_cases hn : (calldataWord cd (4 + off)).toNat ≤ solcMaxU64
    · simp only [show ¬ solcMaxU64 < (calldataWord cd (4 + off)).toNat by omega, ↓reduceIte]
      by_cases hp : 4 + off + 32 + (calldataWord cd (4 + off)).toNat ≤ cd.size
      · have hl : (((cd.toList.drop 4).drop (off + 32)).take (calldataWord cd (4 + off)).toNat).length =
            (calldataWord cd (4 + off)).toNat := by
          simp only [List.length_take, List.length_drop, htlen]; omega
        simp only [readBytes?, hl, ↓reduceIte, Option.bind_some,
          show CalldataBytesBounds cd (4 + off) from ⟨hh, hn, hp⟩]
        simp only [calldataBytesPayload, List.drop_drop, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · have hl : ¬ (((cd.toList.drop 4).drop (off + 32)).take (calldataWord cd (4 + off)).toNat).length =
            (calldataWord cd (4 + off)).toNat := by
          simp only [List.length_take, List.length_drop, htlen]; omega
        simp only [readBytes?, hl, ↓reduceIte, Option.bind_none,
          show ¬ CalldataBytesBounds cd (4 + off) from fun h => hp h.2.2]
    · simp only [show solcMaxU64 < (calldataWord cd (4 + off)).toNat by omega, ↓reduceIte,
        show ¬ CalldataBytesBounds cd (4 + off) from fun h => hn h.2.1]
  · have hr : readNat? (cd.toList.drop 4) off = none := by
      have hl : ¬ (((cd.toList.drop 4).drop off).take 32).length = 32 := by
        simp only [List.length_take, List.length_drop, htlen]; omega
      simp only [readNat?, readWord?, readBytes?, hl, ↓reduceIte, bind, Option.bind_none]
    rw [decodeABIValue?]
    simp only [hr, bind, Option.bind_none,
      show ¬ CalldataBytesBounds cd (4 + off) from fun h => hh h.1, ↓reduceIte]

theorem calldataBytesPayload_size {cd : ByteArray} {start : Nat}
    (hb : CalldataBytesBounds cd start) :
    (calldataBytesPayload cd start).size = (calldataWord cd start).toNat := by
  simp only [calldataBytesPayload, ByteArray.size, List.size_toArray,
    List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
  have hp := hb.2.2
  change start + 32 + (calldataWord cd start).toNat ≤ cd.data.size at hp
  omega

theorem calldataBytesPayload_read {cd : ByteArray} {start : Nat}
    (hb : CalldataBytesBounds cd start) :
    cd.readWithPadding (start + 32) (calldataWord cd start).toNat = calldataBytesPayload cd start := by
  by_cases hz : (calldataWord cd start).toNat = 0
  · simp only [hz, byteArray_readWithPadding_zero, calldataBytesPayload, List.take_zero]
    rfl
  · rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) hb.2.2]
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
      Nat.add_sub_cancel_left, calldataBytesPayload, List.toList_toArray, byteArray_toList_eq]

end Benchmarks.Morpho.MorphoBlue
