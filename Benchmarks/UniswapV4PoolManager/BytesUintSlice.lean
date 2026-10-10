import Benchmarks.UniswapV4PoolManager.SignedBytesDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: an unsigned ABI word decoded from any in-bounds bytes slice.
theorem evalDecodeUint256Slice {cfg : Config} {f : Frame} {evm : State} {e : Expr}
    {bytes : ByteArray} {start : Nat} (hmode : cfg.abiDecodeMode = .modern)
    (he : evalExpr? cfg f evm e = .ok (.bytes bytes)) (hb : start+32 ≤ bytes.size) :
    evalExpr? cfg f evm (.abiDecode abiUInt256
      (.bytesSlice e (.intLit (Int.ofNat start)) (.intLit (Int.ofNat (start+32))))) =
      .ok (.int (Int.ofNat (calldataWord bytes start).toNat)) := by
  have hd := decodeReturnUint_extract (out := bytes) (start := start) (finish := start+32)
    (by omega) hb (by simp only [Nat.add_sub_cancel_left]; decide)
  rw [evalExpr?, evalBytesWindow he (by omega) hb]
  simp only [bind, EvalResult.bind, hmode, ABI.decodeReturnValueWithMode?, hd, pure]

end Benchmarks.UniswapV4PoolManager
