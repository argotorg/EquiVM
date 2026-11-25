import Benchmarks.Midnight.LiquidatePayer
import Benchmarks.Midnight.MarketLossStorage

variable {fork : Ethereum.Fork}

/-! Evaluation of the liquidation event and its selected collateral token. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def liquidateTokenExpr : Expr := .field (marketCollateralExpr "collateralIndex") "token"

def liquidateEventArgs : List Expr :=
  [.env .caller, .var "id", liquidateTokenExpr, .var "seizedAssets", .var "repaidUnits",
    .var "borrower", .var "postMaturityMode", .var "receiver", .var "payer", .var "badDebt",
    .storage { base := "_marketState", steps := [.field "lossFactor"] },
    .storage { base := "_marketState", steps := [.field "continuousFeeCredit"] }]

theorem evalLiquidateToken {frame : Frame} {evm : State} {m : MarketData} {index : UInt256}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hi : frame.locals.get? "collateralIndex" = some (.int index.toNat))
    (hidx : index.toNat < m.collaterals.length) :
    evalExpr? config frame evm liquidateTokenExpr =
      .ok (.address m.collaterals[index.toNat].token) := by
  rw [liquidateTokenExpr, evalExpr?, evalMarketCollateralAt "collateralIndex" hm hi hidx]
  rfl

theorem evalLiquidateTokenRevert {frame : Frame} {evm : State} {m : MarketData} {index : UInt256}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hi : frame.locals.get? "collateralIndex" = some (.int index.toNat))
    (hidx : ¬ index.toNat < m.collaterals.length) :
    evalExpr? config frame evm liquidateTokenExpr = .revert := by
  rw [liquidateTokenExpr, evalExpr?, evalMarketCollateralAtRevert "collateralIndex" hm hi hidx]
  rfl

theorem liquidateEventArgs_eval {frame : Frame} {evm : State} {m : MarketData}
    {id index seized repaid borrower mode badDebt : UInt256} {receiver callback payer : AccountAddress}
    {data : ByteArray}
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (hpay : frame.locals.get? "payer" = some (.address payer))
    (hbad : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hidx : index.toNat < m.collaterals.length) :
    evalExprs? config frame evm liquidateEventArgs = .ok
      [.address evm.executionEnv.source, wordBytes32Value id,
        .address m.collaterals[index.toNat].token, .int seized.toNat, .int repaid.toNat,
        .address (AccountAddress.ofNat borrower.toNat), wordToElem .bool mode,
        .address receiver, .address payer, .int badDebt.toNat,
        .int (marketLossWord evm id).toNat, .int (marketBalanceWord evm id 2).toNat] := by
  have hc := evalMarketBalance (evm := evm) 2 hf.marketState
  change evalExpr? config frame evm
    (.storage { base := "_marketState", steps := [.field "continuousFeeCredit"] }) = _ at hc
  simp only [liquidateEventArgs, evalExprs?, evalLiquidateToken hf.market hf.index hidx,
    evalMarketAliasLoss hf.marketState, hc, evalExpr?, hf.idValue, hf.seized, hf.repaid,
    hf.borrowerValue, hf.mode, hf.receiver, hpay, hbad, envValue,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem liquidateEventIndexRevert {frame : Frame} {evm : State} {m : MarketData}
    {id index seized repaid borrower mode : UInt256} {receiver callback : AccountAddress}
    {data : ByteArray}
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (hidx : ¬ index.toNat < m.collaterals.length) :
    ExecStmt fork config frame evm (liquidateTransition.body[20]!) .reverted := by
  apply ExecStmt.emitArgsRevert
  change evalExprs? config frame evm liquidateEventArgs = .revert
  simp only [liquidateEventArgs, evalExprs?, evalLiquidateTokenRevert hf.market hf.index hidx,
    evalExpr?, hf.idValue, envValue, EvalResult.ofOption, EvalResult.bind, bind, pure]

end Benchmarks.Midnight
