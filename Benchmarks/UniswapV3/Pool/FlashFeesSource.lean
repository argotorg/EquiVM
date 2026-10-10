import Benchmarks.UniswapV3.Pool.FlashPrefix
import Benchmarks.UniswapV3.Pool.FullMathRoundSource
import Benchmarks.UniswapV3.Pool.PoolTokenTransfer

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def poolFeeWord (v : UniswapV3PoolImmutables) : UInt256 :=
  UInt256.land v.fee (UInt256.ofNat 16777215)

def flashFeeName (second : Bool) : Ident := if second then "fee1" else "fee0"

def flashFeeArgs (second : Bool) : List Expr :=
  [.var (poolAmountName second), .cast (.immutable "fee") (.elem (.int (.uint ⟨24, by decide⟩))),
    .intLit 1000000]

def flashFeeStmt (second : Bool) : Stmt :=
  .internalCall "FullMath_mulDivRoundingUp" (flashFeeArgs second) (flashFeeName second)

theorem evalPoolFee (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State) :
    evalExpr? config {contract := contract, locals := locals, immutables := immStore v} evm
      (.cast (.immutable "fee") (.elem (.int (.uint ⟨24, by decide⟩)))) =
      .ok (.int (Int.ofNat (poolFeeWord v).toNat)) := by
  have h := evalExpr_intCast (.uint ⟨24, by decide⟩) (evalImmutable_fee config contract locals evm v)
  rw [normalizeUIntWord_mask ⟨24, by decide⟩ v.fee (UInt256.ofNat 16777215) (by decide +kernel)] at h
  exact h

theorem evalFlashFeeArgs (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (amount : UInt256)
    (ha : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat))) :
    evalExprs? config {contract := contract, locals := locals, immutables := immStore v} evm
      (flashFeeArgs second) = .ok [.int (Int.ofNat amount.toNat),
        .int (Int.ofNat (poolFeeWord v).toNat), .int 1000000] := by
  have hamount := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := immStore v}) ha
  simp only [flashFeeArgs, evalExprs?, hamount, evalPoolFee, bind, EvalResult.bind, evalExpr?, pure]

theorem flashFeeReturns (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (amount : UInt256)
    (ha : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hv : fullMathRoundValid amount (poolFeeWord v) ⟨1000000⟩) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (flashFeeStmt second)
      (.ok { contract := contract
             locals := locals.insert (flashFeeName second)
               (.int (Int.ofNat (fullMathRoundResult amount (poolFeeWord v) ⟨1000000⟩).toNat))
             immutables := immStore v } evm) := by
  exact internalCallFunctionReturn (callee := fullMathRoundFunction)
    (locals := fullMathLocals amount (poolFeeWord v) ⟨1000000⟩)
    (calleeSolm := fullMathRoundFinalFrame (immStore v) amount (poolFeeWord v) ⟨1000000⟩)
    (value := some [.int (Int.ofNat (fullMathRoundResult amount (poolFeeWord v) ⟨1000000⟩).toNat)])
    (evalFlashFeeArgs v locals evm second amount ha) fullMathRoundLookup
    (fullMathRoundBind amount (poolFeeWord v) ⟨1000000⟩)
    (fullMathRoundReturns (immStore v) evm amount (poolFeeWord v) ⟨1000000⟩ hv)

theorem flashFeeReverts (v : UniswapV3PoolImmutables) (locals : Store) (evm : EVM.State)
    (second : Bool) (amount : UInt256)
    (ha : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hv : ¬ fullMathRoundValid amount (poolFeeWord v) ⟨1000000⟩) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (flashFeeStmt second) .reverted :=
  internalCallFunctionRevert (callee := fullMathRoundFunction)
    (locals := fullMathLocals amount (poolFeeWord v) ⟨1000000⟩)
    (evalFlashFeeArgs v locals evm second amount ha) fullMathRoundLookup
    (fullMathRoundBind amount (poolFeeWord v) ⟨1000000⟩)
    (fullMathRoundReverts (immStore v) evm amount (poolFeeWord v) ⟨1000000⟩ hv)

def flashFee0Frame (v : UniswapV3PoolImmutables) (a : FlashArgs) (liquidity fee0 : UInt256) : Frame :=
  {flashReadyFrame v a liquidity with
    locals := (flashReadyFrame v a liquidity).locals.insert "fee0" (.int (Int.ofNat fee0.toNat))}

def flashFeesFrame (v : UniswapV3PoolImmutables) (a : FlashArgs)
    (liquidity fee0 fee1 : UInt256) : Frame :=
  {flashFee0Frame v a liquidity fee0 with
    locals := (flashFee0Frame v a liquidity fee0).locals.insert "fee1" (.int (Int.ofNat fee1.toNat))}

theorem flashFeesSource (v : UniswapV3PoolImmutables) (evm : EVM.State) (a : FlashArgs)
    (liquidity : UInt256)
    (hv0 : fullMathRoundValid a.amount0 (poolFeeWord v) ⟨1000000⟩)
    (hv1 : fullMathRoundValid a.amount1 (poolFeeWord v) ⟨1000000⟩) :
    ExecBlock config (flashReadyFrame v a liquidity) evm ((flashTransition.body.drop 6).take 2)
      (.ok (flashFeesFrame v a liquidity
        (fullMathRoundResult a.amount0 (poolFeeWord v) ⟨1000000⟩)
        (fullMathRoundResult a.amount1 (poolFeeWord v) ⟨1000000⟩)) evm) := by
  refine ExecBlock.consNormal (flashFeeReturns v _ evm false a.amount0 ?_ hv0) ?_
  · simp [flashReadyFrame, flashCheckedFrame, flashFrame, flashLocals, poolAmountName, Std.HashMap.getElem_insert]
  refine ExecBlock.consNormal (flashFeeReturns v _ evm true a.amount1 ?_ hv1) ExecBlock.nil
  simp [flashReadyFrame, flashCheckedFrame, flashFrame, flashLocals, poolAmountName,
    flashFee0Frame, flashFeeName, Std.HashMap.getElem_insert]


theorem flashFeesSourceReverts (v : UniswapV3PoolImmutables) (evm : EVM.State) (a : FlashArgs)
    (liquidity : UInt256)
    (hv : ¬ (fullMathRoundValid a.amount0 (poolFeeWord v) ⟨1000000⟩ ∧
      fullMathRoundValid a.amount1 (poolFeeWord v) ⟨1000000⟩)) :
    ExecBlock config (flashReadyFrame v a liquidity) evm ((flashTransition.body.drop 6).take 2)
      .reverted := by
  have h0 : (flashReadyFrame v a liquidity).locals.get? (poolAmountName false) =
      some (.int (Int.ofNat a.amount0.toNat)) := by
    simp [flashReadyFrame, flashCheckedFrame, flashFrame, flashLocals, poolAmountName,
      Std.HashMap.getElem_insert]
  by_cases hv0 : fullMathRoundValid a.amount0 (poolFeeWord v) ⟨1000000⟩
  · refine ExecBlock.consNormal (flashFeeReturns v _ evm false a.amount0 h0 hv0)
      (ExecBlock.consRevert (flashFeeReverts v _ evm true a.amount1 ?_ (fun h ↦ hv ⟨hv0, h⟩)))
    simp [flashReadyFrame, flashCheckedFrame, flashFrame, flashLocals, poolAmountName,
      flashFeeName, Std.HashMap.getElem_insert]
  · exact ExecBlock.consRevert (flashFeeReverts v _ evm false a.amount0 h0 hv0)

end Benchmarks.UniswapV3.Pool
