import Benchmarks.Morpho.MorphoBlue.BodyCommon
import Reasoning.ABIViews
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue

-- LIBRARY CANDIDATE: consecutive ABI word writes and their returned byte sequence.
def returnWordWrites (off : Nat) : List UInt256 → List (Nat × UInt256)
  | [] => []
  | w :: ws => (off, w) :: returnWordWrites (off + 32) ws

def returnWordBytes : List UInt256 → ByteArray
  | [] => ByteArray.empty
  | w :: ws => w.toByteArray ++ returnWordBytes ws

theorem returnWordBytes_size (ws : List UInt256) :
    (returnWordBytes ws).size = 32 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [returnWordBytes, ih, toByteArray_size, Nat.mul_add, Nat.add_comm]

theorem writeWord_at_end (mem : ByteArray) (w : UInt256) :
    writeWord mem mem.size w = mem ++ w.toByteArray := by
  rw [Reasoning.Theory.writeWord, toByteArray_write_eq _ _ _ le_rfl (by
    simp only [Nat.sub_self]
    exact lt_usize _ (by decide)), Nat.sub_self, zeroes_zero rfl]
  simp

theorem writeReturnWords_at_end (ws : List UInt256) (mem : ByteArray) :
    writeCascade mem (returnWordWrites mem.size ws) = mem ++ returnWordBytes ws := by
  induction ws generalizing mem with
  | nil => simp [returnWordWrites, returnWordBytes]
  | cons w ws ih =>
    simp only [returnWordWrites, writeCascade_cons, writeWord_at_end]
    rw [show mem.size + 32 = (mem ++ w.toByteArray).size by
      rw [ByteArray.size_append, toByteArray_size]]
    rw [ih]
    simp [returnWordBytes, ByteArray.append_assoc]

theorem writeReturnWords_after_gap (w : UInt256) (ws : List UInt256) (mem : ByteArray)
    (off : Nat) (hbefore : mem.size ≤ off) (hgap : off - mem.size < USize.size) :
    writeCascade mem (returnWordWrites off (w :: ws)) =
      (mem ++ ByteArray.zeroes (off - mem.size)) ++ returnWordBytes (w :: ws) := by
  simp only [returnWordWrites, writeCascade_cons, Reasoning.Theory.writeWord]
  rw [toByteArray_write_eq w mem off hbefore hgap]
  have hsize : ((mem ++ ByteArray.zeroes (off - mem.size)) ++ w.toByteArray).size = off + 32 := by
    simp only [ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
    omega
  rw [← hsize, writeReturnWords_at_end]
  simp only [returnWordBytes, ByteArray.append_assoc]

theorem readReturnWords_after_gap (w : UInt256) (ws : List UInt256) (mem : ByteArray)
    (off : Nat) (hbefore : mem.size ≤ off) (hgap : off - mem.size < USize.size) :
    (writeCascade mem (returnWordWrites off (w :: ws))).readWithPadding off
      (32 * (w :: ws).length) = returnWordBytes (w :: ws) := by
  rw [writeReturnWords_after_gap w ws mem off hbefore hgap]
  have hprefix : (mem ++ ByteArray.zeroes (off - mem.size)).size = off := by
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    omega
  rw [← returnWordBytes_size]
  rw [readWithPadding_eq_extract_unbounded _ _ _
    (by rw [returnWordBytes_size]; simp)
    (by rw [ByteArray.size_append, hprefix])]
  simpa only [hprefix] using extract_append_right
    (mem ++ ByteArray.zeroes (off - mem.size)) (returnWordBytes (w :: ws))

-- LIBRARY CANDIDATE: ABI-encode any list of elementary values represented by words.
theorem encodeElementaryWordsFrom (entries : List (ElemType × Value × UInt256))
    (headSize : Nat) (head tail : List UInt8)
    (henc : ∀ e ∈ entries, encodeABIValue? (.elem e.1) e.2.1 = some (EVM.Word.toBytesBE e.2.2)) :
    encodeABIValuesFrom? (entries.map (fun e => .elem e.1)) (entries.map (fun e => e.2.1))
      headSize head tail =
      some (head ++ entries.flatMap (fun e => EVM.Word.toBytesBE e.2.2) ++ tail) := by
  induction entries generalizing head with
  | nil => simp [encodeABIValuesFrom?]
  | cons e es ih =>
    simp only [List.map_cons, encodeABIValuesFrom?, henc e (by simp),
      isDynamicABIType, bind, Option.bind, Bool.false_eq_true, if_false]
    rw [ih _ (fun e he => henc e (by simp [he]))]
    simp [List.append_assoc]

theorem returnWordBytes_toList (ws : List UInt256) :
    (returnWordBytes ws).toList = ws.flatMap EVM.Word.toBytesBE := by
  induction ws with
  | nil => simp [returnWordBytes, byteArray_toList_eq]
  | cons w ws ih =>
    simp only [byteArray_toList_eq] at ih
    simp [returnWordBytes, byteArray_toList_eq, toByteArray_eq_toBytesBE, ih]

theorem elementaryWordsReturnEncoding (entries : List (ElemType × Value × UInt256))
    (henc : ∀ e ∈ entries, encodeABIValue? (.elem e.1) e.2.1 = some (EVM.Word.toBytesBE e.2.2)) :
    encodeReturnValues? (entries.map (fun e => .elem e.1)) (entries.map (fun e => e.2.1)) =
      some (returnWordBytes (entries.map (fun e => e.2.2))) := by
  have hhead : abiTupleHeadSize? (entries.map (fun e => .elem e.1)) = some (32 * entries.length) := by
    clear henc
    induction entries with
    | nil => simp [abiTupleHeadSize?]
    | cons e es ih => simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, ih,
        Nat.mul_add, Nat.add_comm]
  simp only [encodeReturnValues?, encodeABIValues?, hhead, bind, Option.bind,
    encodeElementaryWordsFrom entries _ _ _ henc, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa [byteArray_toList_eq, List.flatMap_map] using
    (returnWordBytes_toList (entries.map (fun e => e.2.2))).symm

-- LIBRARY CANDIDATE: the tuple form of elementary-word return encoding.
theorem elementaryWordsTupleEncoding (entries : List (ElemType × Value × UInt256))
    (henc : ∀ e ∈ entries, encodeABIValue? (.elem e.1) e.2.1 =
      some (EVM.Word.toBytesBE e.2.2)) :
    encodeABIValue? (.tuple (entries.map (fun e ↦ .elem e.1)))
      (.tuple (entries.map (fun e ↦ e.2.1))) =
      some (returnWordBytes (entries.map (fun e ↦ e.2.2))).toList := by
  rw [encodeABIValue?]
  have hret := elementaryWordsReturnEncoding entries henc
  unfold encodeReturnValues? at hret
  cases h : encodeABIValues? (entries.map (fun e ↦ .elem e.1))
      (entries.map (fun e ↦ e.2.1)) with
  | none => simp [h] at hret
  | some bytes =>
    have heq : ByteArray.mk bytes.toArray = returnWordBytes (entries.map (fun e ↦ e.2.2)) :=
      Option.some.inj (by simpa [h] using hret)
    rw [← heq]
    simp only [byteArray_toList_eq, List.toList_toArray]

-- GENERALIZES Reasoning.Theory.encodeABIValue_uint256: parameterize the unsigned width.
theorem encodeABIValue_uint (width : BitWidth) (w : UInt256)
    (hfit : w.toNat < EVM.twoPow width.val) :
    encodeABIValue? (.elem (.int (.uint width))) (.int (Int.ofNat w.toNat)) =
      some (EVM.Word.toBytesBE w) := by
  rcases width with ⟨bits, hbits⟩
  have hcond : 0 ≤ Int.ofNat w.toNat ∧ Int.ofNat w.toNat < Int.ofNat (EVM.twoPow bits) :=
    ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hfit⟩
  simp only [encodeABIValue?, encodeABIWord?, if_neg (Nat.ne_of_gt hbits.1), if_pos hcond,
    bind, Option.bind]
  simp [show EVM.word w.toNat = w from u256_ofNat_toNat w]

end Benchmarks.Morpho.MorphoBlue
