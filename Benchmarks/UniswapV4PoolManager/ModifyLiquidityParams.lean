import Benchmarks.UniswapV4PoolManager.InitializeHookABI
import Benchmarks.UniswapV4PoolManager.SignedWordBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

structure ModifyLiquidityWords where
  lower : UInt256
  upper : UInt256
  delta : UInt256
  salt : UInt256

def modifyLiquidityTypes : List ABIType := [abiInt24, abiInt24, abiInt256, abiBytes32]
def abiModifyLiquidityParams : ABIType := .tuple modifyLiquidityTypes
def modifyLiquidityWords (p : ModifyLiquidityWords) : List UInt256 := [p.lower, p.upper, p.delta, p.salt]
def modifyLiquidityValues (p : ModifyLiquidityWords) : List Value :=
  [.int (EVM.signed p.lower), .int (EVM.signed p.upper), .int (EVM.signed p.delta), wordBytes32Value p.salt]
def modifyLiquidityParamsValue (p : ModifyLiquidityWords) : Value :=
  .struct "ModifyLiquidityParams_8903"
    [("tickLower", .int (EVM.signed p.lower)), ("tickUpper", .int (EVM.signed p.upper)),
     ("liquidityDelta", .int (EVM.signed p.delta)), ("salt", wordBytes32Value p.salt)]
def modifyLiquidityTupleExpr (e : Expr) : Expr :=
  .tupleLit [.field e "tickLower", .field e "tickUpper", .field e "liquidityDelta", .field e "salt"]

theorem evalModifyLiquidityTuple {cfg : Config} {f : Frame} {evm : State} {e : Expr} {p : ModifyLiquidityWords}
    (hp : evalExpr? cfg f evm e = .ok (modifyLiquidityParamsValue p)) :
    evalExpr? cfg f evm (modifyLiquidityTupleExpr e) = .ok (.tuple (modifyLiquidityValues p)) := by
  have hl := evalStructField hp (field := "tickLower") rfl
  have hu := evalStructField hp (field := "tickUpper") rfl
  have hd := evalStructField hp (field := "liquidityDelta") rfl
  have hs := evalStructField hp (field := "salt") rfl
  rw [modifyLiquidityTupleExpr, evalExpr?]
  simp only [evalExprList?, hl, hu, hd, hs, bind, EvalResult.bind, pure]
  rfl

theorem modifyLiquidityEncoding {p : ModifyLiquidityWords}
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) :
    encodeABIValue? abiModifyLiquidityParams (.tuple (modifyLiquidityValues p)) =
      some ((modifyLiquidityWords p).flatMap EVM.Word.toBytesBE) := by
  have hle := encodeSignedWord ⟨24, by decide⟩ p.lower (int24Canonical_signed_bounds hl)
  have hue := encodeSignedWord ⟨24, by decide⟩ p.upper (int24Canonical_signed_bounds hu)
  have hde := encodeSignedWord ⟨256, by decide⟩ p.delta (signedWord_fits p.delta)
  have hse := encodeABIValue_bytes32_word p.salt
  rw [abiModifyLiquidityParams, encodeABIValue?, encodeABIValues?,
    show abiTupleHeadSize? modifyLiquidityTypes = some 128 by native_decide]
  simp only [modifyLiquidityTypes, modifyLiquidityValues, encodeABIValuesFrom?, hle, hue, hde,
    wordBytes32Value, hse, isDynamicABIType, Bool.false_eq_true, if_false, bind, Option.bind,
    List.nil_append, List.append_nil, modifyLiquidityWords, List.flatMap_cons, List.flatMap_nil,
    List.append_assoc, toByteArray_eq_toBytesBE, byteArray_toList_eq, List.toList_toArray]

end Benchmarks.UniswapV4PoolManager
