import Benchmarks.UniswapV3.Pool.FlashProtocolSource
import Benchmarks.UniswapV3.Pool.FullMathSource
import Benchmarks.UniswapV3.Pool.FeeGrowthStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def flashGrowthCallName (second : Bool) : Ident := if second then "__c13" else "__c12"

def flashGrowthArgs (second : Bool) : List Expr :=
  [.cast (.binary .sub (.var (flashPaidName second)) (.var (flashProtocolFeesName second)))
      (.elem (.int (.uint ⟨256, by decide⟩))),
    .intLit 340282366920938463463374607431768211456, .var "_liquidity"]

def flashGrowthStmts (second : Bool) : List Stmt :=
  [.internalCall "FullMath_mulDiv" (flashGrowthArgs second) (flashGrowthCallName second),
    .assign .storage ⟨feeGrowthName second, []⟩
      (.cast (.binary .add (.storage ⟨feeGrowthName second, []⟩) (.var (flashGrowthCallName second)))
        (.elem (.int (.uint ⟨256, by decide⟩))))]

def flashGrowthResult (paid fees liquidity : UInt256) : UInt256 :=
  fullMathResult (UInt256.sub paid fees) (UInt256.ofNat (2 ^ 128)) liquidity

def flashGrowthFrame (locals imms : Store) (second : Bool) (paid fees liquidity : UInt256) : Frame :=
  {contract := contract, immutables := imms,
    locals := locals.insert (flashGrowthCallName second)
      (.int (Int.ofNat (flashGrowthResult paid fees liquidity).toNat))}

theorem evalFlashGrowthArgs (locals imms : Store) (evm : EVM.State) (second : Bool)
    (paid fees liquidity : UInt256)
    (hp : locals.get? (flashPaidName second) = some (.int (Int.ofNat paid.toNat)))
    (hf : locals.get? (flashProtocolFeesName second) = some (.int (Int.ofNat fees.toNat)))
    (hl : locals.get? "_liquidity" = some (.int (Int.ofNat liquidity.toNat))) :
    evalExprs? config {contract := contract, locals := locals, immutables := imms} evm
      (flashGrowthArgs second) = .ok [.int (Int.ofNat (UInt256.sub paid fees).toNat),
        .int (Int.ofNat (UInt256.ofNat (2 ^ 128)).toNat), .int (Int.ofNat liquidity.toNat)] := by
  have hp' := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) hp
  have hs := evalExpr_word_sub hp' (evalExpr_var_get hf)
  simp only [flashGrowthArgs, evalExprs?, hs, bind, EvalResult.bind,
    evalExpr?, hl, EvalResult.ofOption, pure]
  rfl

theorem flashGrowthReturns (locals imms : Store) (evm : EVM.State) (second : Bool)
    (paid fees liquidity : UInt256)
    (hp : locals.get? (flashPaidName second) = some (.int (Int.ofNat paid.toNat)))
    (hf : locals.get? (flashProtocolFeesName second) = some (.int (Int.ofNat fees.toNat)))
    (hl : locals.get? "_liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hbase : locals.get? (feeGrowthName second) = none)
    (hv : fullMathValid (UInt256.sub paid fees) (UInt256.ofNat (2 ^ 128)) liquidity) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (flashGrowthStmts second) (.ok (flashGrowthFrame locals imms second paid fees liquidity)
        (addFeeGrowth evm second (flashGrowthResult paid fees liquidity))) := by
  have hcall := internalCallFunctionReturn (callee := fullMathFunction)
    (locals := fullMathLocals (UInt256.sub paid fees) (UInt256.ofNat (2 ^ 128)) liquidity)
    (calleeSolm := fullMathProductFrame imms (UInt256.sub paid fees)
      (UInt256.ofNat (2 ^ 128)) liquidity)
    (value := some [.int (Int.ofNat (flashGrowthResult paid fees liquidity).toNat)])
    (retVar := flashGrowthCallName second)
    (evalFlashGrowthArgs locals imms evm second paid fees liquidity hp hf hl) fullMathLookup
    (fullMathBind _ _ _) (fullMathReturns imms evm _ _ _ hv)
  change ExecStmt _ _ _ _ (.ok (flashGrowthFrame locals imms second paid fees liquidity) evm)
    at hcall
  refine ExecBlock.consNormal hcall (ExecBlock.consNormal ?_ ExecBlock.nil)
  have hbase' : (flashGrowthFrame locals imms second paid fees liquidity).locals.get?
      (feeGrowthName second) = none := by
    cases second <;>
      simpa [flashGrowthFrame, flashGrowthCallName, feeGrowthName,
        Std.HashMap.getElem?_insert] using hbase
  exact ExecStmt.assign (evalExpr_word_add
    (evalFeeGrowth _ imms evm second hbase')
    (evalExpr_var_get (by simp [flashGrowthFrame, Std.HashMap.getElem?_insert])))
    (assignFeeGrowth _ imms evm second _ hbase')

theorem flashGrowthReverts (locals imms : Store) (evm : EVM.State) (second : Bool)
    (paid fees liquidity : UInt256)
    (hp : locals.get? (flashPaidName second) = some (.int (Int.ofNat paid.toNat)))
    (hf : locals.get? (flashProtocolFeesName second) = some (.int (Int.ofNat fees.toNat)))
    (hl : locals.get? "_liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hv : ¬ fullMathValid (UInt256.sub paid fees) (UInt256.ofNat (2 ^ 128)) liquidity) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (flashGrowthStmts second) .reverted := by
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (callee := fullMathFunction)
    (locals := fullMathLocals (UInt256.sub paid fees) (UInt256.ofNat (2 ^ 128)) liquidity)
    (evalFlashGrowthArgs locals imms evm second paid fees liquidity hp hf hl) fullMathLookup
    (fullMathBind _ _ _) (fullMathReverts imms evm _ _ _ hv)

end Benchmarks.UniswapV3.Pool
