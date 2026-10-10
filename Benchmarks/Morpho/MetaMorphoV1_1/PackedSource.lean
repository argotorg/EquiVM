import Benchmarks.Morpho.MetaMorphoV1_1.Arithmetic

/-! Source evaluation of packed word encodings and their hashes. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

-- LIBRARY CANDIDATE: compose packed argument evaluation from one value and the tail.
theorem evalPackedArgs_cons {cfg : Config} {frame : Frame} {evm : EVM.State}
    {ty : ABIType} {expr : Expr} {args : List (ABIType × Expr)} {value : Value}
    {head tail : List UInt8}
    (heval : evalExpr? cfg frame evm expr = .ok value)
    (hencode : encodePackedValue? ty value = some head)
    (hrest : evalPackedArgs? cfg frame evm args = .ok tail) :
    evalPackedArgs? cfg frame evm ((ty, expr) :: args) = .ok (head ++ tail) := by
  simp only [evalPackedArgs?, heval, hencode, hrest, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

-- LIBRARY CANDIDATE: encode a successfully evaluated sequence of packed arguments.
theorem evalExpr_packed {cfg : Config} {frame : Frame} {evm : EVM.State}
    {args : List (ABIType × Expr)} {bytes : List UInt8}
    (heval : evalPackedArgs? cfg frame evm args = .ok bytes) :
    evalExpr? cfg frame evm (.abiEncodePacked args) = .ok (.bytes bytes.toByteArray) := by
  simp only [evalExpr?, heval, bind, EvalResult.bind, pure]
  rw [byteArray_mk_toArray_eq_toByteArray]

-- LIBRARY CANDIDATE: express the source hash as the same word used by the EVM.
theorem evalExpr_keccakWord {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {bytes : ByteArray}
    (heval : evalExpr? cfg frame evm expr = .ok (.bytes bytes)) :
    evalExpr? cfg frame evm (.keccak256 expr) =
      .ok (wordBytes32Value (uInt256OfByteArray (KEC bytes))) := by
  simp only [evalExpr?, heval, bind, EvalResult.bind, pure, wordBytes32Value]
  rw [toBytesBE_uInt256OfByteArray_of_size (keccak_size bytes)]
  rfl

-- LIBRARY CANDIDATE: cast an address to its unsigned 256-bit representation.
theorem evalExpr_addressToUint {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {address : AccountAddress}
    (heval : evalExpr? cfg frame evm expr = .ok (.address address)) :
    evalExpr? cfg frame evm (.cast expr (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat address.toNat)) := by
  have hfit : address.toNat < EVM.twoPow 256 :=
    lt_of_lt_of_le address.isLt (by decide)
  simp only [evalExpr?, heval, bind, EvalResult.bind, castValue?,
    hfit, ↓reduceIte, EvalResult.ofOption]

theorem evalExpr_addressToWord {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {address : AccountAddress}
    (heval : evalExpr? cfg frame evm expr = .ok (.address address)) :
    evalExpr? cfg frame evm (.cast expr (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (uint256Value (UInt256.ofNat address.toNat)) := by
  have hfit : address.toNat < UInt256.size := lt_trans address.isLt (by decide)
  simpa only [uint256Value, UInt256.toNat_ofNat_of_lt hfit] using evalExpr_addressToUint heval

-- LIBRARY CANDIDATE: cast an unsigned word to bytes32.
theorem evalExpr_uintToBytes32 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {value : UInt256}
    (heval : evalExpr? cfg frame evm expr = .ok (uint256Value value)) :
    evalExpr? cfg frame evm (.cast expr (.elem (.bytes abiBytes32Width))) =
      .ok (wordBytes32Value value) := by
  have hnonneg : ¬ ((value.toNat : Int) < 0) := not_lt_of_ge (Int.natCast_nonneg _)
  simp only [evalExpr?, heval, uint256Value, bind, EvalResult.bind, castValue?,
    Int.ofNat_eq_natCast, hnonneg, ↓reduceIte,
    Int.toNat_natCast, abiBytes32Width, Nat.reduceAdd, Nat.sub_self, List.drop_zero,
    EvalResult.ofOption, wordBytes32Value]
  rw [show EVM.Word.ofNat value.toNat = value from u256_ofNat_toNat value]

-- LIBRARY CANDIDATE: cast bytes32 to its unsigned word value.
theorem evalExpr_bytes32ToUint {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {value : UInt256}
    (heval : evalExpr? cfg frame evm expr = .ok (wordBytes32Value value)) :
    evalExpr? cfg frame evm (.cast expr (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (uint256Value value) := by
  have hlen : (EVM.Word.toBytesBE value).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size value
  simp only [evalExpr?, heval, wordBytes32Value, bind, EvalResult.bind, castValue?,
    abiBytes32Width, fixedBytesToNat?, fixedBytesValid, fixedBytesSize,
    Nat.reduceAdd, Nat.reduceMul, hlen, ↓reduceIte, fromBytesBE_word,
    EvalResult.ofOption, uint256Value, decide_true]

end Benchmarks.Morpho.MetaMorphoV1_1
