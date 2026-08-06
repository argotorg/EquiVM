import Examples.UniswapV2Pair.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

/-! Packed-word encoding shared by Permit and the constructor. Existing public names are retained. -/

abbrev permitWordBytes32Value (w : UInt256) : Value :=
  .fixedBytes bytes32Width (EVM.Word.toBytesBE w)

theorem permitWordBytes32Value_matches (w : UInt256) :
    valueMatchesOptionalABIType (some bytes32) (permitWordBytes32Value w) = true := by
  apply valueMatchesOptionalABIType_fixedBytes
  simpa [fixedBytesSize, bytes32Width] using word_toBytesBE_toByteArray_size w

theorem evalExpr_keccak256_matches_bytes32 {cfg : Config} {solm : Frame} {evm : EVM.State}
    {expr : Expr} {value : Value}
    (heval : evalExpr? cfg solm evm (.keccak256 expr) = .ok value) :
    valueMatchesOptionalABIType (some bytes32) value = true := by
  simp only [evalExpr?] at heval
  generalize hresult : evalExpr? cfg solm evm expr = result at heval
  cases result with
  | ok inner =>
      cases inner <;> simp only [EvalResult.bind, bind, pure] at heval <;> cases heval
      case ok.bytes.refl bytes =>
        apply valueMatchesOptionalABIType_fixedBytes
        rw [byteArray_toList_eq, Array.length_toList]
        simpa [fixedBytesSize, bytes32Width] using keccak_size bytes
  | revert => cases heval
  | error error => cases heval

-- LIBRARY CANDIDATE: ByteArray round trip through its list representation.
theorem byteArray_mk_toList_toArray (b : ByteArray) :
    ByteArray.mk b.toList.toArray = b := by
  apply ByteArray.ext
  rw [byteArray_toList_eq]

-- LIBRARY CANDIDATE: ByteArray concatenation commutes with conversion to lists.
theorem byteArray_toList_append (a b : ByteArray) :
    (a ++ b).toList = a.toList ++ b.toList := by
  rw [byteArray_toList_eq, byteArray_toList_eq, byteArray_toList_eq]
  simp [ByteArray.data_append]

-- LIBRARY CANDIDATE: correspondence between the two word-byte representations.
theorem word_toBytesBE_eq_toByteArray_toList (w : UInt256) :
    EVM.Word.toBytesBE w = (UInt256.toByteArray w).toList := by
  have h := congrArg ByteArray.toList (word_toBytesBE_toByteArray_eq_toByteArray w)
  simpa [byteArray_toList_eq] using h

theorem permitEncodePacked_uint256 (w : UInt256) :
    encodePackedValue? uint256 (.int (Int.ofNat w.toNat)) =
      some (EVM.Word.toBytesBE w) := by
  have hword : EVM.word w.toNat = w := u256_ofNat_toNat w
  have hlt : w.toNat < EVM.twoPow 256 := by
    change w.val.val < EVM.twoPow 256
    exact w.val.isLt
  simp [encodePackedValue?, uint256, uint256Int, encodeABIWord?, hword, hlt]

theorem permitEncodePacked_bytes32 (w : UInt256) :
    encodePackedValue? bytes32 (permitWordBytes32Value w) =
      some (EVM.Word.toBytesBE w) := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  simp [encodePackedValue?, bytes32, bytes32Width, permitWordBytes32Value,
    fixedBytesSize, hlen]

-- LIBRARY CANDIDATE: packed argument evaluation composed from a head and tail.
theorem permitEvalPackedArgs_cons {cfg : Config} {solm : Frame} {evm : EVM.State}
    {ty : ABIType} {e : Expr} {v : Value} {head tailBytes : List UInt8}
    {rest : List (ABIType × Expr)}
    (he : evalExpr? cfg solm evm e = .ok v)
    (henc : encodePackedValue? ty v = some head)
    (htail : evalPackedArgs? cfg solm evm rest = .ok tailBytes) :
    evalPackedArgs? cfg solm evm ((ty, e) :: rest) = .ok (head ++ tailBytes) := by
  rw [evalPackedArgs?]
  simp only [he, henc, htail, EvalResult.bind, EvalResult.ofOption, bind, pure]

-- LIBRARY CANDIDATE: singleton packed argument evaluation.
theorem permitEvalPackedArgs_single {cfg : Config} {solm : Frame} {evm : EVM.State}
    {ty : ABIType} {e : Expr} {v : Value} {head : List UInt8}
    (he : evalExpr? cfg solm evm e = .ok v)
    (henc : encodePackedValue? ty v = some head) :
    evalPackedArgs? cfg solm evm [(ty, e)] = .ok head := by
  simp [evalPackedArgs?, he, henc, EvalResult.bind, EvalResult.ofOption, bind, pure]

end UniswapV2Pair
