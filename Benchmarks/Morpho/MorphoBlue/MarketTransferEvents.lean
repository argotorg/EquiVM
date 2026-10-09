import Benchmarks.Morpho.MorphoBlue.MarketTransferLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue

theorem MarketTransferLocals.emit {p assets shares account receiver locals}
    (hl : MarketTransferLocals p assets shares account receiver locals) (imms : Store) (evm : EVM.State) (name : Ident) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.emit name [.var "id", .env .caller, .var "onBehalf", .var "receiver", .var "assets", .var "shares"])
      (.ok { contract := contract, locals := locals, immutables := imms } evm) := by
  apply ExecStmt.emit
  simp only [evalExprs?, hl.evalId imms evm, hl.evalAccount imms evm, hl.evalReceiver imms evm,
    hl.evalAssets imms evm, hl.evalShares imms evm, evalExpr?, envValue, EvalResult.bind, bind, pure]
  rfl

end Benchmarks.Morpho.MorphoBlue
