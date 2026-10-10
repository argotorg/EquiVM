import Benchmarks.UniswapV4PoolManager.TickPriceWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickPriceScaleSource {f : Frame} {evm : EVM.State} {log2 : UInt256}
    (hl : f.locals.get? "log_2" = some (.int (EVM.signed log2))) :
    ExecStmt config f evm tickPriceFunction.body[49]!
      (.ok {f with locals := f.locals.insert "log_sqrt10001" (.int (EVM.signed (tickPriceScaled log2)))} evm) := by
  exact ExecStmt.letDecl ( evalSignedWordMul (evalLocalValue (cfg := config) (evm := evm) hl)
    (show evalExpr? config f evm (.intLit 255738958999603826347141) =
      .ok (.int (EVM.signed (UInt256.ofNat 255738958999603826347141))) by simp only [evalExpr?, pure]; rfl))

theorem tickPriceLowSource {f : Frame} {evm : EVM.State} {scaled : UInt256}
    (hl : f.locals.get? "log_sqrt10001" = some (.int (EVM.signed scaled))) :
    ExecStmt config f evm tickPriceFunction.body[50]!
      (.ok {f with locals := f.locals.insert "tickLow" (.int (EVM.signed
        (UInt256.signextend (UInt256.ofNat 2) (UInt256.sar (UInt256.ofNat 128) (UInt256.sub scaled (UInt256.ofNat 3402992956809132418596140100660247210))))))} evm) := by
  exact ExecStmt.letDecl (evalSignedWord24 (evalSignedWordSar (b := .intLit 128) (n := 128) (by decide)
    (evalSignedWordSub (evalLocalValue (cfg := config) (evm := evm) hl)
      (show evalExpr? config f evm (.intLit 3402992956809132418596140100660247210) =
        .ok (.int (EVM.signed (UInt256.ofNat 3402992956809132418596140100660247210))) by simp only [evalExpr?, pure]; rfl))
    (by simp only [evalExpr?, pure]; rfl)))

theorem tickPriceHighSource {f : Frame} {evm : EVM.State} {scaled : UInt256}
    (hl : f.locals.get? "log_sqrt10001" = some (.int (EVM.signed scaled))) :
    ExecStmt config f evm tickPriceFunction.body[51]!
      (.ok {f with locals := f.locals.insert "tickHi" (.int (EVM.signed
        (UInt256.signextend (UInt256.ofNat 2) (UInt256.sar (UInt256.ofNat 128) (scaled + UInt256.ofNat 291339464771989622907027621153398088495)))))} evm) := by
  exact ExecStmt.letDecl (evalSignedWord24 (evalSignedWordSar (b := .intLit 128) (n := 128) (by decide)
    (evalSignedWordAdd (evalLocalValue (cfg := config) (evm := evm) hl)
      (show evalExpr? config f evm (.intLit 291339464771989622907027621153398088495) =
        .ok (.int (EVM.signed (UInt256.ofNat 291339464771989622907027621153398088495))) by simp only [evalExpr?, pure]; rfl))
    (by simp only [evalExpr?, pure]; rfl)))

end Benchmarks.UniswapV4PoolManager
