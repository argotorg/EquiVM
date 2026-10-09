import Benchmarks.Safe.Calldata
import Reasoning.ABIComposite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: expose the guards for a modern dynamic ABI tuple.
theorem decodeDynamicCalldata {cd : ByteArray} {names : List Ident}
    {ty : ABIType} {types : List ABIType} {headSize : Nat}
    (hlong : 4 ≤ cd.size) (hdyn : (ty :: types).any isDynamicABIType = true)
    (hhead : abiTupleHeadSize? (ty :: types) = some headSize) :
    decodeCalldata names (ty :: types) cd =
      if 2 ^ 255 ≤ cd.size then none
      else if cd.size - 4 < headSize then none
      else (do
        let (values, _) ← decodeABIValues? (ty :: types) (cd.toList.drop 4) 0 0 headSize headSize
        decodeCalldata.insertValues names values ∅) := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeCalldata
  simp only [hlist, if_neg (by omega : ¬cd.size < 4), hdyn, true_and]
  by_cases hs : 2 ^ 255 ≤ cd.size
  · simp only [hs, if_true]
  · simp only [hs, if_false, List.isEmpty_cons, Bool.false_eq, true_and,
      List.length_drop, hlist, if_neg (by omega : ¬2 ^ 255 ≤ cd.size - 4), and_false]
    simp only [decodeCalldata.decodeArgs, hhead, bind, Option.bind, List.length_drop, hlist]
    by_cases hh : cd.size - 4 < headSize
    · simp [hh]
    · simp only [hh, if_false]
      cases decodeABIValues? (ty :: types) (cd.toList.drop 4) 0 0 headSize headSize with
      | none => rfl
      | some v =>
        rcases v with ⟨values, endOffset⟩
        simp only []
        cases decodeCalldata.insertValues names values ∅ <;> rfl

-- GENERALIZES readNat_drop4_at_eq_calldataWord to the underlying word read.
theorem readWordCalldata {cd : ByteArray} (off : Nat) (hin : 4 + off + 32 ≤ cd.size) :
    readWord? (cd.toList.drop 4) off = some (calldataWord cd (4 + off)) := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : (((cd.toList.drop 4).drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlist]; omega
  unfold readWord? readBytes?
  rw [if_pos htake]
  simp only [bind, Option.bind, List.drop_drop]
  rw [decode_word_at_eq_any cd (4 + off) hin]

-- LIBRARY CANDIDATE: an in-bounds ABI bytes read is a ByteArray extraction.
theorem readBytesCalldata {cd : ByteArray} {off len : Nat} (hin : 4 + off + len ≤ cd.size) :
    readBytes? (cd.toList.drop 4) off len =
      some (cd.extract (4 + off) (4 + off + len)).toList := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : (((cd.toList.drop 4).drop off).take len).length = len := by
    simp only [List.length_take, List.length_drop, hlist]; omega
  unfold readBytes?
  rw [if_pos htake, byteArray_extract_toList]
  simp only [List.drop_drop, Nat.add_sub_cancel_left]

-- LIBRARY CANDIDATE: scalar calldata decoders stated using the EVM word read.
theorem decodeAddressCalldata {cd : ByteArray} (off : Nat) (hin : 4 + off + 32 ≤ cd.size) :
    decodeABIValue? (.elem .address) (cd.toList.drop 4) off =
      if (calldataWord cd (4 + off)).toNat < EVM.addressModulus then
        some (.address (AccountAddress.ofNat (calldataWord cd (4 + off)).toNat), off + 32)
      else none := by
  simp only [decodeABIValue?, readWordCalldata off hin, bind, Option.bind, decodeABIWord?]
  by_cases hc : (calldataWord cd (4 + off)).val.val < EVM.addressModulus <;>
    simp only [UInt256.toNat, hc, ↓reduceIte]

theorem decodeUint256Calldata {cd : ByteArray} (off : Nat) (hin : 4 + off + 32 ≤ cd.size) :
    decodeABIValue? (.elem (.int (.uint ⟨256, by decide⟩))) (cd.toList.drop 4) off =
      some (.int (Int.ofNat (calldataWord cd (4 + off)).toNat), off + 32) := by
  have hv : (calldataWord cd (4 + off)).val.val < EVM.twoPow 256 :=
    (calldataWord cd (4 + off)).val.isLt
  simp only [decodeABIValue?, readWordCalldata off hin, bind, Option.bind, decodeABIWord?,
    Fin.reduceFinMk, hv, if_true, if_false, Nat.reduceEqDiff]
  rfl

theorem decodeUint8Calldata {cd : ByteArray} (off : Nat) (hin : 4 + off + 32 ≤ cd.size) :
    decodeABIValue? (.elem (.int (.uint ⟨8, by decide⟩))) (cd.toList.drop 4) off =
      if (calldataWord cd (4 + off)).toNat < 256 then
        some (.int (Int.ofNat (calldataWord cd (4 + off)).toNat), off + 32) else none := by
  simp only [decodeABIValue?, readWordCalldata off hin, bind, Option.bind, decodeABIWord?,
    Fin.reduceFinMk, if_false, Nat.reduceEqDiff]
  by_cases hc : (calldataWord cd (4 + off)).val.val < 256 <;>
    simp only [show EVM.twoPow 8 = 256 by decide +kernel, UInt256.toNat, hc, ↓reduceIte]

-- LIBRARY CANDIDATE: recover the bounds and extraction from successful ABI byte reads.
theorem readCalldataBytesEvidence {cd : ByteArray} {off len : Nat} {payload : List UInt8}
    (hlong : 4 ≤ cd.size) (hread : readNat? (cd.toList.drop 4) off = some len)
    (hp : readBytes? (cd.toList.drop 4) (off + 32) len = some payload) :
    calldataWord cd (4 + off) = UInt256.ofNat len ∧ 4 + off + 32 + len ≤ cd.size ∧
      payload = (cd.extract (4 + off + 32) (4 + off + 32 + len)).toList := by
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hhead := readNat?_some_length hread
  simp only [List.length_drop, hlist] at hhead
  have htake : (((cd.toList.drop 4).drop (off + 32)).take len).length = len := by
    unfold readBytes? at hp
    dsimp only at hp
    split at hp
    · assumption
    · cases hp
  have hin : 4 + off + 32 + len ≤ cd.size := by
    simp only [List.length_take, List.length_drop, hlist] at htake
    omega
  have hw := readNat_drop4_at_eq_calldataWord (cd := cd) off (by omega)
  rw [hread, Option.some.injEq] at hw
  refine ⟨?_, hin, ?_⟩
  · rw [hw]; exact (u256_ofNat_toNat _).symm
  · have hb := readBytesCalldata (cd := cd) (off := off + 32) (len := len) (by omega)
    rw [hp, Option.some.injEq] at hb
    simpa only [← Nat.add_assoc] using hb

end Benchmarks.Safe
