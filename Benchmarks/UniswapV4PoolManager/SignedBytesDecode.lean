import Benchmarks.UniswapV4PoolManager.LocalBytes

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: all full-width signed ABI words are canonical.
theorem decodeABIWord_signed256 (w : UInt256) :
    decodeABIWord? abiInt256 w = some (.int (EVM.signed w)) := by
  simp only [decodeABIWord?, abiInt256, abiInt256Int, EVM.signed, EVM.signBit,
    EVM.wordModulus, EVM.twoPow, UInt256.toNat, show ¬(256 : Nat) = 0 by decide, if_false]
  split_ifs <;> first | rfl | omega

-- GENERALIZES Reasoning.Theory.decodeReturnUint_long to signed words.
theorem decodeReturnSigned256 {out : ByteArray} (hl : 32 ≤ out.size) (hb : out.size < 2^255) :
    ABI.decodeReturnValue? abiInt256 out = some (.int (EVM.signed (calldataWord out 0))) := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have h32 : ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, hlen]; omega
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide)]
  rw [if_neg (by simp only [List.isEmpty_cons, hlen]; omega)]
  simp only [decodeScalarWords?, decodeScalarWord?, readWord?, readBytes?, h32,
    if_true, bind, Option.bind, decodeABIWord_signed256,
    decode_word_at_eq_any out 0 (by omega)]

-- GENERALIZES evalBytesPrefix to any in-bounds slice.
theorem evalBytesWindow {cfg : Config} {f : Frame} {evm : State} {e : Expr}
    {bytes : ByteArray} {start finish : Nat}
    (he : evalExpr? cfg f evm e = .ok (.bytes bytes)) (ho : start ≤ finish) (hb : finish ≤ bytes.size) :
    evalExpr? cfg f evm (.bytesSlice e (.intLit (Int.ofNat start)) (.intLit (Int.ofNat finish))) =
      .ok (.bytes (bytes.extract start finish)) := by
  simp only [evalExpr?, he, pure, bind, EvalResult.bind, sliceBytes?, Int.ofNat_eq_natCast,
    Int.toNat_natCast, show ¬(start : Int) < 0 by omega, show ¬(finish : Int) < 0 by omega,
    Nat.not_lt.mpr ho, Nat.not_lt.mpr hb, decide_false, Bool.false_or, Bool.false_eq_true, if_false]

-- LIBRARY CANDIDATE: decoding one signed ABI word from an in-bounds bytes slice.
theorem evalDecodeSigned256Slice {cfg : Config} {f : Frame} {evm : State} {e : Expr}
    {bytes : ByteArray} {start : Nat} (hmode : cfg.abiDecodeMode = .modern)
    (he : evalExpr? cfg f evm e = .ok (.bytes bytes)) (hb : start+32 ≤ bytes.size) :
    evalExpr? cfg f evm (.abiDecode abiInt256
      (.bytesSlice e (.intLit (Int.ofNat start)) (.intLit (Int.ofNat (start+32))))) =
      .ok (.int (EVM.signed (calldataWord bytes start))) := by
  have hs : (bytes.extract start (start+32)).size = 32 := by rw [ByteArray.size_extract]; omega
  have hd := decodeReturnSigned256 (out := bytes.extract start (start+32))
    (by rw [hs]) (by rw [hs]; decide)
  rw [calldataWord_extract_zero (by omega) hb] at hd
  rw [evalExpr?, evalBytesWindow he (by omega) hb]
  simp only [bind, EvalResult.bind, hmode, ABI.decodeReturnValueWithMode?, hd, pure]

end Benchmarks.UniswapV4PoolManager
