import Benchmarks.UniswapV3.Pool.PositionUpdatePrefix
import Benchmarks.UniswapV3.Pool.PositionScalarStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def positionUpdateGrowthName (second : Bool) : Ident :=
  if second then "feeGrowthInside1X128" else "feeGrowthInside0X128"

def positionUpdateRawName (second : Bool) : Ident := if second then "__c2" else "__c1"

def positionUpdateFeeArgs (second : Bool) : List Expr :=
  [.cast (.binary .sub (.var (positionUpdateGrowthName second))
     (.field (.var "_self") (positionLastField second))) (.elem (.int (.uint ⟨256, by decide⟩))),
   .field (.var "_self") "liquidity", .intLit (2 ^ 128)]

def positionUpdateFeeBody (second : Bool) : List Stmt :=
  [.internalCall "FullMath_mulDiv" (positionUpdateFeeArgs second) (positionUpdateRawName second),
   .letDecl (positionOwedField second) (some (.elem (.int (.uint ⟨128, by decide⟩))))
     (.cast (.var (positionUpdateRawName second)) (.elem (.int (.uint ⟨128, by decide⟩))))]

def positionUpdateFeeCallFrame (frame : Frame) (a : PositionUpdateArgs) (evm : EVM.State)
    (second : Bool) : Frame :=
  let locals := frame.locals.insert (positionUpdateRawName second)
    (.int (Int.ofNat (positionUpdateFeeRaw a evm second).toNat))
  {frame with locals := locals}

def positionUpdateFeeReadyFrame (frame : Frame) (a : PositionUpdateArgs) (evm : EVM.State)
    (second : Bool) : Frame :=
  let frame' := positionUpdateFeeCallFrame frame a evm second
  let locals := frame'.locals.insert (positionOwedField second)
    (.int (Int.ofNat (positionUpdateOwed a evm second).toNat))
  {frame' with locals := locals}

theorem evalPositionSnapshotLast (locals imms : Store) (evm : EVM.State) (a : PositionUpdateArgs)
    (second : Bool)
    (hget : locals.get? "_self" = some (positionStructValue a.key evm.accountMap evm.executionEnv)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.field (.var "_self") (positionLastField second)) =
      .ok (.int (Int.ofNat (positionFieldWord a.key (if second then 2 else 1) 0 32
        evm.accountMap evm.executionEnv).toNat)) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) hget
  simp only [evalExpr?, he, bind, EvalResult.bind]
  cases second <;> rfl

theorem evalPositionUpdateFeeArgs (locals imms : Store) (evm : EVM.State)
    (a : PositionUpdateArgs) (second : Bool)
    (hself : locals.get? "_self" = some (positionStructValue a.key evm.accountMap evm.executionEnv))
    (hgrowth : locals.get? (positionUpdateGrowthName second) =
      some (.int (Int.ofNat (a.growth second).toNat))) :
    evalExprs? config {contract := contract, locals := locals, immutables := imms} evm
      (positionUpdateFeeArgs second) =
      .ok [.int (Int.ofNat (positionUpdateFeeDelta a evm second).toNat),
        .int (positionUpdateLiquidityBefore a evm), .int (2 ^ 128)] := by
  have hg := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) hgrowth
  have hlast := evalPositionSnapshotLast locals imms evm a second hself
  have hdelta := evalExpr_word_sub hg hlast
  have hliq := evalPositionSnapshotLiquidity locals imms evm evm a hself
  simp only [positionUpdateFeeArgs, evalExprs?, hdelta, hliq, evalExpr?, bind, EvalResult.bind, pure]
  rfl

theorem positionUpdateFeeBind (a : PositionUpdateArgs) (evm : EVM.State) (second : Bool) :
    bindParams? fullMathFunction.params
      [.int (Int.ofNat (positionUpdateFeeDelta a evm second).toNat),
        .int (positionUpdateLiquidityBefore a evm), .int (2 ^ 128)] =
      some (fullMathLocals (positionUpdateFeeDelta a evm second) (positionUpdateLiquidityWord a evm)
        (UInt256.ofNat (2 ^ 128))) := by
  rfl

theorem positionUpdateFeeSource (locals imms : Store) (evm : EVM.State)
    (a : PositionUpdateArgs) (second : Bool)
    (hself : locals.get? "_self" = some (positionStructValue a.key evm.accountMap evm.executionEnv))
    (hgrowth : locals.get? (positionUpdateGrowthName second) =
      some (.int (Int.ofNat (a.growth second).toNat))) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (positionUpdateFeeBody second)
      (.ok (positionUpdateFeeReadyFrame {contract := contract, locals := locals, immutables := imms}
        a evm second) evm) := by
  let frame : Frame := {contract := contract, locals := locals, immutables := imms}
  have hcall : ExecStmt config frame evm
      (.internalCall "FullMath_mulDiv" (positionUpdateFeeArgs second) (positionUpdateRawName second))
      (.ok (positionUpdateFeeCallFrame frame a evm second) evm) :=
    internalCallFunctionReturn (callee := fullMathFunction)
      (locals := fullMathLocals (positionUpdateFeeDelta a evm second)
        (positionUpdateLiquidityWord a evm) (UInt256.ofNat (2 ^ 128)))
      (calleeSolm := fullMathProductFrame imms (positionUpdateFeeDelta a evm second)
        (positionUpdateLiquidityWord a evm) (UInt256.ofNat (2 ^ 128)))
      (value := some [.int (Int.ofNat (positionUpdateFeeRaw a evm second).toNat)])
      (evalPositionUpdateFeeArgs locals imms evm a second hself hgrowth) fullMathLookup
      (positionUpdateFeeBind a evm second)
      (fullMathReturns imms evm (positionUpdateFeeDelta a evm second)
        (positionUpdateLiquidityWord a evm) (UInt256.ofNat (2 ^ 128))
        (positionUpdateFeeValid a evm second))
  refine ExecBlock.consNormal hcall (ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil)
  have he : evalExpr? config (positionUpdateFeeCallFrame frame a evm second) evm
      (.var (positionUpdateRawName second)) =
      .ok (.int (Int.ofNat (positionUpdateFeeRaw a evm second).toNat)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  have hn : normalizeInt (.uint ⟨128, by decide⟩)
      (Int.ofNat (positionUpdateFeeRaw a evm second).toNat) =
      Int.ofNat (positionUpdateOwed a evm second).toNat := by
    simpa only [positionUpdateOwed, uint128Word, u256_land_comm] using
      normalizeUIntWord_mask ⟨128, by decide⟩ (positionUpdateFeeRaw a evm second)
        (UInt256.ofNat (2 ^ 128 - 1)) (by decide)
  simp only [evalExpr?, he, castValue?, hn, EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
