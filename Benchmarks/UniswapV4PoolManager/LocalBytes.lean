import Benchmarks.UniswapV4PoolManager.Values

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: length and prefix decoding for locally bound bytes.
theorem evalLocalBytesLength {cfg f evm name} {bytes : ByteArray}
    (h : f.locals.get? name = some (.bytes bytes)) :
    evalExpr? cfg f evm (.arrayLength .localVar ⟨name, []⟩) =
      .ok (.int (Int.ofNat bytes.size)) := by
  simp only [evalExpr?, h, readLocalPath?, pure, bind, EvalResult.bind, Int.ofNat_eq_natCast]

theorem evalNatEqLiteral {cfg f evm e} {n k : Nat}
    (he : evalExpr? cfg f evm e = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg f evm (.binary .eq e (.intLit (Int.ofNat k))) =
      .ok (.bool (decide (n = k))) := by
  simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?,
    BEq.beq, Value.int.injEq, Int.ofNat_eq_natCast, Nat.cast_inj]

theorem evalNatGtLiteral {cfg f evm e} {n k : Nat}
    (he : evalExpr? cfg f evm e = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg f evm (.binary .gt e (.intLit (Int.ofNat k))) =
      .ok (.bool (decide (k < n))) := by
  simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?,
    Int.ofNat_eq_natCast, Nat.cast_lt]

-- LIBRARY CANDIDATE: natural-valued lower bounds and bytes equality.
theorem evalNatGeLiteral {cfg f evm e} {n k : Nat}
    (he : evalExpr? cfg f evm e = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg f evm (.binary .ge e (.intLit (Int.ofNat k))) =
      .ok (.bool (decide (k ≤ n))) := by
  simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?,
    Int.ofNat_eq_natCast, Nat.cast_le]

theorem evalEqBytes {cfg f evm a b} {xs ys : ByteArray}
    (ha : evalExpr? cfg f evm a = .ok (.bytes xs))
    (hb : evalExpr? cfg f evm b = .ok (.bytes ys)) :
    evalExpr? cfg f evm (.binary .eq a b) = .ok (.bool (decide (xs = ys))) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, BEq.beq, Value.bytes.injEq]

theorem evalBytesPrefix {cfg f evm e} {bytes : ByteArray} {n : Nat}
    (he : evalExpr? cfg f evm e = .ok (.bytes bytes)) (hn : n ≤ bytes.size) :
    evalExpr? cfg f evm (.bytesSlice e (.intLit 0) (.intLit (Int.ofNat n))) =
      .ok (.bytes (bytes.extract 0 n)) := by
  simp only [evalExpr?, he, pure, bind, EvalResult.bind, sliceBytes?,
    Int.ofNat_eq_natCast, Int.toNat_natCast, Int.reduceLT, decide_false, Bool.false_or,
    show ¬ (n : Int) < 0 by omega, Nat.not_lt.mpr hn, if_false,
    Int.toNat_zero, Nat.not_lt_zero, Bool.false_eq_true]

theorem evalDecodeUint256Prefix {cfg : Config} {f evm e} {bytes : ByteArray}
    (hmode : cfg.abiDecodeMode = .modern) (he : evalExpr? cfg f evm e = .ok (.bytes bytes))
    (hn : 32 ≤ bytes.size) :
    evalExpr? cfg f evm (.abiDecode abiUInt256 (.bytesSlice e (.intLit 0) (.intLit 32))) =
      .ok (.int (Int.ofNat (UInt256.ofNat (fromByteArrayBigEndian (bytes.extract 0 32))).toNat)) := by
  have hs : (bytes.extract 0 32).size = 32 := by simp only [ByteArray.size_extract]; omega
  have hd := decodeReturnValues_uint256_ok (returndata := bytes.extract 0 32)
    (by omega) (by rw [hs]; decide)
  have hw := UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hn)
  simp only [extract_extract_BA, Nat.zero_add, Nat.min_self] at hd
  have hp : evalExpr? cfg f evm (.bytesSlice e (.intLit 0) (.intLit 32)) =
      .ok (.bytes (bytes.extract 0 32)) := evalBytesPrefix he hn
  rw [evalExpr?, hp]
  simp only [bind, EvalResult.bind, hmode, ABI.decodeReturnValueWithMode?,
    ABI.decodeReturnValue?, hd, hw, pure]

end Benchmarks.UniswapV4PoolManager
