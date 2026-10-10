import Benchmarks.CompoundIII.Comet.RateSource
import Benchmarks.CompoundIII.Comet.UintFunction

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def rateTransition (borrow : Bool) : TransitionDecl :=
  if borrow then getBorrowRateTransition else getSupplyRateTransition

theorem rateTransition_body (borrow : Bool) :
    (rateTransition borrow).body = calldataPrologue
      [.internalCall (rateCallableName borrow) [.var "utilization"] "result",
       .return [.var "result"]] := by
  cases borrow <;> rfl

theorem getRate_returns {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) (borrow : Bool)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hvalid : RateValid (rateParams v borrow) (calldataWord I.calldata 4)) :
    ∃ frame, ExecTransitionBody config contract (initState σ σ₀ g A I)
      (uintFunctionArgs "utilization" I) (rateTransition borrow).body
      (.returned frame (initState σ σ₀ g A I)
        (some [.int (rateWord (rateParams v borrow) (calldataWord I.calldata 4)).toNat]))
      (immStore v) := by
  let u := calldataWord I.calldata 4
  let frame := calldataLocalFrame
    { contract := contract, locals := uintFunctionArgs "utilization" I, immutables := immStore v }
    (initState σ σ₀ g A I)
  let val := rateWord (rateParams v borrow) u
  have hu : evalExpr? config frame (initState σ σ₀ g A I) (.var "utilization") =
      .ok (.int u.toNat) := by
    simp only [evalExpr?, frame, calldataLocalFrame, uintFunctionArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  rw [rateTransition_body]
  refine ⟨{ frame with locals := frame.locals.insert "result" (.int val.toNat) }, .execBlockRet ?_⟩
  apply (calldataPrologue_ok hv hhi).run
  apply ExecBlock.consNormal
    (rate_call_ok v borrow frame (initState σ σ₀ g A I) u _ "result" rfl rfl hu hvalid)
  exact ABlock.start.returns (by
    simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    rfl)

theorem getRate_reverts {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) (borrow : Bool)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hvalid : ¬ RateValid (rateParams v borrow) (calldataWord I.calldata 4)) :
    ExecTransitionBody config contract (initState σ σ₀ g A I)
      (uintFunctionArgs "utilization" I) (rateTransition borrow).body .reverted (immStore v) := by
  let u := calldataWord I.calldata 4
  let frame := calldataLocalFrame
    { contract := contract, locals := uintFunctionArgs "utilization" I, immutables := immStore v }
    (initState σ σ₀ g A I)
  have hu : evalExpr? config frame (initState σ σ₀ g A I) (.var "utilization") =
      .ok (.int u.toNat) := by
    simp only [evalExpr?, frame, calldataLocalFrame, uintFunctionArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  rw [rateTransition_body]
  apply ExecFuncBody.execBlockRevert
  apply (calldataPrologue_ok hv hhi).run
  exact ExecBlock.consRevert
    (rate_call_revert v borrow frame (initState σ σ₀ g A I) u _ "result" rfl rfl hu hvalid)

end Benchmarks.CompoundIII.Comet
