import Benchmarks.CompoundIII.Comet.PackedGetter
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES scalarReturnEncoding to a list of independently encoded elementary values.
structure ScalarReturn where
  type : ElemType
  value : Value
  word : UInt256
  encoded : encodeABIValue? (.elem type) value = some (EVM.Word.toBytesBE word)

theorem scalarReturnsEncoding (xs : List ScalarReturn) :
    encodeReturnValues? (xs.map (fun x ↦ .elem x.type)) (xs.map ScalarReturn.value) =
      some (wordBytes (xs.map ScalarReturn.word)) := by
  have hhead : abiTupleHeadSize? (xs.map (fun x ↦ .elem x.type)) = some (32 * xs.length) := by
    induction xs with
    | nil => simp [abiTupleHeadSize?]
    | cons x xs ih =>
      simp only [List.map_cons, abiTupleHeadSize?, ih, isDynamicABIType,
        staticABIEncodedSize?, bind, Option.bind, List.length_cons, Bool.false_eq_true, if_false]
      congr 1
      omega
  have hfrom (ys : List ScalarReturn) (n : Nat) (head tail : List UInt8) :
      encodeABIValuesFrom? (ys.map (fun x ↦ .elem x.type)) (ys.map ScalarReturn.value) n head tail =
        some (head ++ (ys.flatMap (fun x ↦ EVM.Word.toBytesBE x.word)) ++ tail) := by
    induction ys generalizing head with
    | nil => simp [encodeABIValuesFrom?]
    | cons y ys ih =>
      simp only [List.map_cons, encodeABIValuesFrom?, y.encoded, isDynamicABIType,
        Bool.false_eq_true, if_false, bind, Option.bind, ih, List.flatMap_cons, List.append_assoc]
  rw [encodeReturnValues?, encodeABIValues?, hhead]
  simp only [bind, Option.bind, hfrom, List.nil_append, List.append_nil, wordBytes_eq_list]
  congr 1
  apply ByteArray.ext
  simp [List.flatMap_map]

-- LIBRARY CANDIDATE: return words appended after a preserved scratch prefix.
def scratchWordsMem (mem : ByteArray) (ws : List UInt256) : ByteArray :=
  (mem ++ ByteArray.zeroes 32) ++ wordBytes ws

theorem scratchWordsMem_size {mem : ByteArray} (hmem : mem.size = 96) (ws : List UInt256) :
    (scratchWordsMem mem ws).size = 128 + 32 * ws.length := by
  simp [scratchWordsMem, ByteArray.size_append, hmem, ByteArray_zeroes_size, wordBytes_size]

theorem scratchWordsMem_single {mem : ByteArray} (hmem : mem.size = 96) (w : UInt256) :
    solcScratchReturnMem mem w = scratchWordsMem mem [w] := by
  unfold solcScratchReturnMem
  rw [toByteArray_write_eq _ _ _ (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  simp only [scratchWordsMem, wordBytes, ByteArray.append_empty, hmem]

theorem scratchWordsMem_write {mem : ByteArray} (hmem : mem.size = 96)
    (ws : List UInt256) (w : UInt256) :
    w.toByteArray.write 0 (scratchWordsMem mem ws) (128 + 32 * ws.length) 32 =
      scratchWordsMem mem (ws ++ [w]) := by
  rw [← scratchWordsMem_size hmem ws, write_at_end_eq _ _ 32 (by decide)
    (by rw [toByteArray_size]), toByteArray_extract_all]
  simp only [scratchWordsMem, wordBytes_append, wordBytes, ByteArray.append_empty,
    ByteArray.append_assoc]

theorem scratchWordsMem_read128 {mem : ByteArray} (hmem : mem.size = 96) (ws : List UInt256)
    (hpos : 0 < ws.length) (hsize : 32 * ws.length < 2 ^ 64) :
    (scratchWordsMem mem ws).readWithPadding 128 (32 * ws.length) = wordBytes ws := by
  rw [readWithPadding_eq_extract' _ _ _ (by omega) hsize (by rw [scratchWordsMem_size hmem ws])]
  exact extract_append_right' _ _ _ _
    (by simp [ByteArray.size_append, hmem, ByteArray_zeroes_size])
    (by simp [ByteArray.size_append, hmem, ByteArray_zeroes_size, wordBytes_size])

end Benchmarks.CompoundIII.Comet
