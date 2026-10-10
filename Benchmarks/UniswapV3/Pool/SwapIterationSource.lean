import Benchmarks.UniswapV3.Pool.SwapLoopGuardSource
import Benchmarks.UniswapV3.Pool.SwapIterationAllocation
import Benchmarks.UniswapV3.Pool.SourceStructs

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure SwapIterationData where
  priceStart : UInt256
  tickNext : Int
  initialized : Bool
  priceNext : UInt256
  amountIn : UInt256
  amountOut : UInt256
  feeAmount : UInt256

def SwapIterationData.value (d : SwapIterationData) : Value :=
  .struct "StepComputations" [
    ("sqrtPriceStartX96", .int (Int.ofNat d.priceStart.toNat)),
    ("tickNext", .int d.tickNext), ("initialized", .bool d.initialized),
    ("sqrtPriceNextX96", .int (Int.ofNat d.priceNext.toNat)),
    ("amountIn", .int (Int.ofNat d.amountIn.toNat)),
    ("amountOut", .int (Int.ofNat d.amountOut.toNat)),
    ("feeAmount", .int (Int.ofNat d.feeAmount.toNat))]

def SwapIterationData.words (d : SwapIterationData) : List UInt256 :=
  [d.priceStart, EVM.wordOfInt d.tickNext, d.initialized.toUInt256, d.priceNext,
    d.amountIn, d.amountOut, d.feeAmount]

def swapIterationInitial (price : UInt256) : SwapIterationData :=
  {priceStart := price, tickNext := 0, initialized := false, priceNext := ⟨0⟩,
    amountIn := ⟨0⟩, amountOut := ⟨0⟩, feeAmount := ⟨0⟩}

def SwapIterationMemory (mem : ByteArray) (p : UInt256) (d : SwapIterationData) : Prop :=
  WordArrayMemory mem p d.words

def swapIterationFrame (frame : Frame) (d : SwapIterationData) : Frame :=
  {frame with locals := frame.locals.insert "step" d.value}

theorem swapIterationZeroSource (frame : Frame) (evm : EVM.State) :
    ExecStmt config frame evm swapLoopBody[0]!
      (.ok (swapIterationFrame frame (swapIterationInitial ⟨0⟩)) evm) := by
  apply ExecStmt.letDecl
  change evalExpr? config frame evm
    (.structLit "StepComputations" [
      ("sqrtPriceStartX96", .intLit 0), ("tickNext", .intLit 0),
      ("initialized", .boolLit false), ("sqrtPriceNextX96", .intLit 0),
      ("amountIn", .intLit 0), ("amountOut", .intLit 0), ("feeAmount", .intLit 0)]) = _
  simp only [evalExpr?, evalStructFields?, bind, EvalResult.bind, pure]
  rfl

theorem swapIterationStartSource {frame : Frame} {evm : EVM.State}
    (s : SwapStateData) (d : SwapIterationData)
    (hs : frame.locals.get? "state" = some s.value)
    (hd : frame.locals.get? "step" = some d.value) :
    ExecStmt config frame evm
      (.assign .localVar ⟨"step", [.field "sqrtPriceStartX96"]⟩
        (.field (.var "state") "sqrtPriceX96"))
      (.ok (swapIterationFrame frame {d with priceStart := s.price}) evm) := by
  exact ExecStmt.assign
    (evalExpr_structField (name := "sqrtPriceX96") (evalExpr_var_get hs) rfl)
    (assignLocalField_frame hd rfl rfl)

end Benchmarks.UniswapV3.Pool
