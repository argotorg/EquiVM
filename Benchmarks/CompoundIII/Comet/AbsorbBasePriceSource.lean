import Benchmarks.CompoundIII.Comet.AbsorbBasePriceModel
import Benchmarks.CompoundIII.Comet.AbsorbLoopTailSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem absorbBasePrice_source {v : CometWithExtendedAssetListImmutables}
    {absorber account : AccountAddress} {basic : UserBasicData} {old : UInt256}
    {evm : State} {result : InternalOutcome}
    (ht : AbsorbBasePriceTrace v account basic old evm result)
    (frame : Frame) (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (hf : ∀ price, AbsorbLoopFrame v absorber account basic old price 0 ⟨0⟩
      (absorbInitialFrame frame price)) :
    internalBlockResult config frame evm absorbBasePriceBlock result := by
  have he : evalExpr? config frame evm (.immutable "baseTokenPriceFeed") =
      .ok (.address v.baseTokenPriceFeed) := by
    simp only [evalExpr?, hi, immStore_get_baseTokenPriceFeed, EvalResult.ofOption]
  cases ht with
  | priceFailed hcall hh hv =>
      exact ExecBlock.consRevert (price_call_revert frame evm _ _ _ "basePrice" _ _ hc he hcall hh hv)
  | finished hcall hh hv htail =>
      have hp := price_call_ok frame evm _ _ _ "basePrice" _ hc he hcall hh hv
      have hb := absorbLoopTail_source htail _ (hf _) (Nat.zero_le _)
      exact ((hb.prepend (ExecStmt.letDecl (by simp only [evalExpr?, pure]))).prepend
        (ExecStmt.letDecl (by simp only [evalExpr?, pure]))).prepend hp

end Benchmarks.CompoundIII.Comet
