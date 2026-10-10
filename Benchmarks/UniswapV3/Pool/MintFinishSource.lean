import Benchmarks.UniswapV3.Pool.MintCoreValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

theorem mintFinishSource (v : UniswapV3PoolImmutables) (a : MintArgs) (locals : Store)
    (amount0 amount1 : UInt256) (evm : EVM.State) (hv : MintCoreValues locals a amount0 amount1) :
    ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
      (mintTransition.body.drop 21)
      (.returned {contract := contract, locals := locals, immutables := immStore v}
        (storeSlot0Unlocked evm true)
        (some [.int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat)])) := by
  refine ExecBlock.consNormal (ExecStmt.emit (vals :=
    [.address evm.executionEnv.source, .address a.recipient, .int a.lower, .int a.upper,
      .int (Int.ofNat a.amount.toNat), .int (Int.ofNat amount0.toNat),
      .int (Int.ofNat amount1.toNat)]) ?_) ?_
  · simp only [evalExprs?, evalExpr?, hv.recipient, hv.lower, hv.upper, hv.amount,
      hv.amount0, hv.amount1, EvalResult.ofOption, envValue, bind, EvalResult.bind, pure]
  refine ExecBlock.consNormal (ExecStmt.assign (by simp only [evalExpr?, pure])
    (assignSlot0Unlocked _ _ _ true hv.slot0)) ?_
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, hv.amount0, hv.amount1, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
