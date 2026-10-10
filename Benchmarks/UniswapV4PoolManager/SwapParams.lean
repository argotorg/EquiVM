import Benchmarks.UniswapV4PoolManager.InitializeHookABI
import Benchmarks.UniswapV4PoolManager.SignedWordBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

structure SwapParamsWords where
  zeroForOne : Bool
  amountSpecified : UInt256
  priceLimit : UInt256

def swapParamsTypes : List ABIType := [.elem .bool, abiInt256, .elem (.int (.uint ⟨160, by decide⟩))]
def abiSwapParams : ABIType := .tuple swapParamsTypes
def swapParamsWordList (p : SwapParamsWords) : List UInt256 :=
  [UInt256.fromBool p.zeroForOne, p.amountSpecified, p.priceLimit]
def swapParamsValues (p : SwapParamsWords) : List Value :=
  [.bool p.zeroForOne, .int (EVM.signed p.amountSpecified), .int (Int.ofNat p.priceLimit.toNat)]
def swapParamsValue (p : SwapParamsWords) : Value :=
  .struct "SwapParams_8914" [("zeroForOne", .bool p.zeroForOne),
    ("amountSpecified", .int (EVM.signed p.amountSpecified)), ("sqrtPriceLimitX96", .int (Int.ofNat p.priceLimit.toNat))]
def swapParamsTupleExpr (e : Expr) : Expr :=
  .tupleLit [.field e "zeroForOne", .field e "amountSpecified", .field e "sqrtPriceLimitX96"]

theorem evalSwapParamsTuple {cfg : Config} {f : Frame} {evm : State} {e : Expr} {p : SwapParamsWords}
    (hp : evalExpr? cfg f evm e = .ok (swapParamsValue p)) :
    evalExpr? cfg f evm (swapParamsTupleExpr e) = .ok (.tuple (swapParamsValues p)) := by
  have hz := evalStructField hp (field := "zeroForOne") rfl
  have ha := evalStructField hp (field := "amountSpecified") rfl
  have hl := evalStructField hp (field := "sqrtPriceLimitX96") rfl
  rw [swapParamsTupleExpr, evalExpr?]
  simp only [evalExprList?, hz, ha, hl, bind, EvalResult.bind, pure]
  rfl

theorem swapParamsEncoding {p : SwapParamsWords} (hp : p.priceLimit.toNat < 2^160) :
    encodeABIValue? abiSwapParams (.tuple (swapParamsValues p)) =
      some ((swapParamsWordList p).flatMap EVM.Word.toBytesBE) := by
  have hz : encodeABIValue? (.elem .bool) (.bool p.zeroForOne) =
      some (EVM.Word.toBytesBE (UInt256.fromBool p.zeroForOne)) := by
    simpa only [Bool.toUInt256, UInt256.fromBool] using encodeABIValue_bool p.zeroForOne
  have ha := encodeSignedWord ⟨256, by decide⟩ p.amountSpecified (signedWord_fits p.amountSpecified)
  have hl := encodeUnsignedWord ⟨160, by decide⟩ p.priceLimit hp
  rw [abiSwapParams, encodeABIValue?, encodeABIValues?,
    show abiTupleHeadSize? swapParamsTypes = some 96 by native_decide]
  simp only [swapParamsTypes, swapParamsValues, encodeABIValuesFrom?, hz, ha, hl,
    isDynamicABIType, Bool.false_eq_true, if_false, bind, Option.bind, List.nil_append,
    List.append_nil, swapParamsWordList, List.flatMap_cons, List.flatMap_nil, List.append_assoc]

end Benchmarks.UniswapV4PoolManager
