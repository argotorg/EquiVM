import Benchmarks.UniswapV4PoolManager.SignedRangeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: checked signed subtraction at any source width.
theorem evalCheckedSignedSub {cfg : Config} {f : Frame} {evm : State} {ea eb : Expr} {a b : Int}
    (bits : BitWidth) (ha : evalExpr? cfg f evm ea = .ok (.int a))
    (hb : evalExpr? cfg f evm eb = .ok (.int b)) :
    evalExpr? cfg f evm (.inRange (.sint bits) (.binary .sub ea eb)) =
      if signedFits bits (a-b) then .ok (.int (a-b)) else .revert := by
  apply evalSignedRange
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  rfl

end Benchmarks.UniswapV4PoolManager
