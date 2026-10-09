import Benchmarks.Safe.LocalArrays
import Benchmarks.Safe.Bytes32ReturnDecoder

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: evaluate a bytes slice from the values of its three expressions.
theorem evalBytesSlice {cfg : Config} {frame : Frame} {evm : EVM.State}
    {base start finish : Expr} {bytes : ByteArray} {i j : Nat}
    (hb : evalExpr? cfg frame evm base = .ok (.bytes bytes))
    (hi : evalExpr? cfg frame evm start = .ok (.int (Int.ofNat i)))
    (hj : evalExpr? cfg frame evm finish = .ok (.int (Int.ofNat j)))
    (hij : i ≤ j) (hin : j ≤ bytes.size) :
    evalExpr? cfg frame evm (.bytesSlice base start finish) =
      .ok (.bytes (bytes.extract i j)) := by
  simp only [evalExpr?, hb, hi, hj, bind, EvalResult.bind, sliceBytes_nat hij hin]

theorem evalSignatureUintAt {frame : Frame} {evm : EVM.State}
    {base offset : Expr} {bytes : ByteArray} {i : Nat}
    (hb : evalExpr? config frame evm base = .ok (.bytes bytes))
    (hi : evalExpr? config frame evm offset = .ok (.int (Int.ofNat i)))
    (hin : i + 32 ≤ bytes.size) :
    evalExpr? config frame evm (signatureUintAt base offset) =
      .ok (uint256Value (calldataWord bytes i)) := by
  have hs := evalBytesSlice hb hi
    (naturalAddSource hi (rhs := .intLit 32) (by simp [evalExpr?]; rfl) (b := 32))
    (by omega) hin
  have hd := decodeReturnUint_extract (out := bytes) (start := i) (finish := i + 32)
    (by omega) hin (by omega)
  change ABI.decodeReturnValueWithMode? config.abiDecodeMode uint256
    (bytes.extract i (i + 32)) = some (uint256Value (calldataWord bytes i)) at hd
  rw [signatureUintAt, evalExpr?, addE, hs]
  simp only [bind, EvalResult.bind, hd, pure]

theorem evalSignatureWordAt {frame : Frame} {evm : EVM.State}
    {base offset : Expr} {bytes : ByteArray} {i : Nat}
    (hb : evalExpr? config frame evm base = .ok (.bytes bytes))
    (hi : evalExpr? config frame evm offset = .ok (.int (Int.ofNat i)))
    (hin : i + 32 ≤ bytes.size) :
    evalExpr? config frame evm (signatureWordAt base offset) =
      .ok (wordBytes32Value (calldataWord bytes i)) := by
  have hs := evalBytesSlice hb hi
    (naturalAddSource hi (rhs := .intLit 32) (by simp [evalExpr?]; rfl) (b := 32))
    (by omega) hin
  have hd := decodeBytes32ReturnLong (out := bytes.extract i (i + 32))
    (by rw [ByteArray.size_extract]; omega) (by rw [ByteArray.size_extract]; omega)
  rw [calldataWord_extract_zero (by omega) hin] at hd
  change ABI.decodeReturnValueWithMode? config.abiDecodeMode bytes32
    (bytes.extract i (i + 32)) = some (wordBytes32Value (calldataWord bytes i)) at hd
  rw [signatureWordAt, evalExpr?, addE, hs]
  simp only [bind, EvalResult.bind, hd, pure]

theorem evalSignatureByteAt {frame : Frame} {evm : EVM.State}
    {base offset : Expr} {bytes : ByteArray} {i : Nat}
    (hb : evalExpr? config frame evm base = .ok (.bytes bytes))
    (hi : evalExpr? config frame evm offset = .ok (.int (Int.ofNat i)))
    (hin : i < bytes.size) :
    evalExpr? config frame evm (signatureByteAt base offset) =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (bytes.extract i (i + 1))))) := by
  have hl : i < bytes.toList.length := by
    simpa only [byteArray_toList_eq, Array.length_toList] using hin
  have he : (bytes.extract i (i + 1)).toList = [bytes.toList[i]] := by
    simp only [byteArray_toList_eq, ByteArray.data_extract, Array.toList_extract,
      List.extract_eq_take_drop, Nat.add_sub_cancel_left]
    exact List.take_one_drop_eq_of_lt_length (by simpa only [Array.length_toList] using hin)
  rw [signatureByteAt, bytes1AsUint8, evalExpr?, evalExpr?, hb, hi]
  have hnonneg : ¬ (i : Int) < 0 := by omega
  simp [evalIndex?, evalByteIndex?, Int.ofNat_eq_natCast, hnonneg, hl,
    lookupNth_eq_getElem bytes.toList i hl, castValue?, uint8St, uint8Int, fixedBytesToNat?,
    fixedBytesValid, fixedBytesSize, EvalResult.ofOption, EvalResult.bind, bind,
    fromByteArrayBigEndian, he, pure]

end Benchmarks.Safe
