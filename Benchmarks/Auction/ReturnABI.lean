import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def BoolReturnValid (out : ByteArray) : Prop :=
  32 ≤ out.size ∧ (calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩)

theorem decodeReturnBool_long {out : ByteArray} (hl : 32 ≤ out.size) (hb : out.size < 2 ^ 255) :
    ABI.decodeReturnValue? boolTy out =
      if calldataWord out 0 = ⟨0⟩ then some (.bool false)
      else if calldataWord out 0 = ⟨1⟩ then some (.bool true) else none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hword := decode_word_at_eq out 0 (by omega) (by decide)
  have h32 : ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, hlen]
    omega
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide)]
  rw [if_neg (by simp only [List.isEmpty_cons, hlen]; omega)]
  by_cases hz : calldataWord out 0 = ⟨0⟩
  · have hd := decodeScalarWord_bool_ok_zero h32 (hword.trans hz)
    simp only [boolTy, decodeScalarWords?, hd, bind, Option.bind, if_pos hz]
  · by_cases ho : calldataWord out 0 = ⟨1⟩
    · have hd := decodeScalarWord_bool_ok_one h32 (hword.trans ho)
      simp only [boolTy, decodeScalarWords?, hd, bind, Option.bind, if_neg hz, if_pos ho]
    · have hd := decodeScalarWord_bool_none_noncanon h32
        (fun he => hz (hword.symm.trans he)) (fun he => ho (hword.symm.trans he))
      simp only [boolTy, decodeScalarWords?, hd, bind, Option.bind, if_neg hz, if_neg ho]

theorem decodeReturnBool_short {out : ByteArray} (hl : out.size < 32) :
    ABI.decodeReturnValue? boolTy out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have h32 : ¬ ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, hlen]
    omega
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide)]
  rw [if_neg (by simp only [List.isEmpty_cons, hlen]; omega)]
  simp only [boolTy, decodeScalarWords?, decodeScalarWord_bool_none_short h32, bind, Option.bind]

theorem decodeReturnBool_valid {out : ByteArray} (hv : BoolReturnValid out)
    (hb : out.size < 2 ^ 255) :
    ABI.decodeReturnValue? boolTy out = some (.bool (decide (calldataWord out 0 ≠ ⟨0⟩))) := by
  rw [decodeReturnBool_long hv.1 hb]
  rcases hv.2 with hz | ho
  · rw [hz]
    decide
  · rw [ho]
    decide

theorem decodeReturnBool_invalid {out : ByteArray} (hv : ¬ BoolReturnValid out)
    (hb : out.size < 2 ^ 255) : ABI.decodeReturnValue? boolTy out = none := by
  by_cases hl : 32 ≤ out.size
  · have hz : calldataWord out 0 ≠ ⟨0⟩ := fun he => hv ⟨hl, Or.inl he⟩
    have ho : calldataWord out 0 ≠ ⟨1⟩ := fun he => hv ⟨hl, Or.inr he⟩
    rw [decodeReturnBool_long hl hb, if_neg hz, if_neg ho]
  · exact decodeReturnBool_short (by omega)

end Auction
