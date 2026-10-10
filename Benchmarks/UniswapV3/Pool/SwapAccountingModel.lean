import Benchmarks.UniswapV3.Pool.SwapIterationResultSource
import Benchmarks.UniswapV3.Pool.SafeSignedMathWords
import Benchmarks.UniswapV3.Pool.SourceWordArithmetic
import Benchmarks.UniswapV3.Pool.SwapMemoryModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapAccountingBody (exactInput : Bool) : List Stmt :=
  match swapLoopBody[13]! with
  | .ite _ yes no => if exactInput then yes else no
  | _ => []

def swapAccountingFirst (exactInput : Bool) (d : SwapIterationData) : UInt256 :=
  if exactInput then d.amountIn + d.feeAmount else d.amountOut

def swapAccountingSecond (exactInput : Bool) (d : SwapIterationData) : UInt256 :=
  swapAccountingFirst (!exactInput) d

def swapAccountingFirstName (exactInput : Bool) : Ident := if exactInput then "__c5" else "__c8"
def swapAccountingSecondName (exactInput : Bool) : Ident := if exactInput then "__c6" else "__c9"
def swapAccountingResultName (exactInput : Bool) : Ident := if exactInput then "__c7" else "__c10"

def swapAccountingSumExpr : Expr :=
  .cast (.binary .add (.field (.var "step") "amountIn") (.field (.var "step") "feeAmount"))
    (.elem (.int (.uint ⟨256, by decide⟩)))

def swapAccountingFirstArgs (exactInput : Bool) : List Expr :=
  if exactInput then [swapAccountingSumExpr] else [.field (.var "step") "amountOut"]

def swapAccountingSecondArgs (exactInput : Bool) : List Expr :=
  swapAccountingFirstArgs (!exactInput)

def swapAccountingMathArgs (exactInput : Bool) : List Expr :=
  [.field (.var "state") "amountCalculated", .var (swapAccountingSecondName exactInput)]

def swapAccountingRemaining (exactInput : Bool) (s : SwapStateData) (d : SwapIterationData) : Int :=
  safeSignedMathResult exactInput s.remaining (Int.ofNat (swapAccountingFirst exactInput d).toNat)

def swapAccountingCalculated (exactInput : Bool) (s : SwapStateData)
    (d : SwapIterationData) : Int :=
  safeSignedMathResult exactInput s.calculated (Int.ofNat (swapAccountingSecond exactInput d).toNat)

def swapAccountingState (exactInput : Bool) (s : SwapStateData) (d : SwapIterationData) :
    SwapStateData :=
  {s with
    remaining := swapAccountingRemaining exactInput s d
    calculated := swapAccountingCalculated exactInput s d}

def swapAccountingFirstFrame (frame : Frame) (exactInput : Bool) (d : SwapIterationData) : Frame :=
  resumeAfterInternalCall frame (swapAccountingFirstName exactInput)
    (some [.int (Int.ofNat (swapAccountingFirst exactInput d).toNat)])

def swapAccountingRemainingFrame (frame : Frame) (exactInput : Bool)
    (s : SwapStateData) (d : SwapIterationData) : Frame :=
  swapStateFrame (swapAccountingFirstFrame frame exactInput d)
    {s with remaining := swapAccountingRemaining exactInput s d}

def swapAccountingSecondFrame (frame : Frame) (exactInput : Bool)
    (s : SwapStateData) (d : SwapIterationData) : Frame :=
  resumeAfterInternalCall (swapAccountingRemainingFrame frame exactInput s d)
    (swapAccountingSecondName exactInput)
    (some [.int (Int.ofNat (swapAccountingSecond exactInput d).toNat)])

def swapAccountingMathFrame (frame : Frame) (exactInput : Bool)
    (s : SwapStateData) (d : SwapIterationData) : Frame :=
  resumeAfterInternalCall (swapAccountingSecondFrame frame exactInput s d)
    (swapAccountingResultName exactInput) (some [.int (swapAccountingCalculated exactInput s d)])

def swapAccountingFrame (frame : Frame) (exactInput : Bool) (s : SwapStateData)
    (d : SwapIterationData) : Frame :=
  swapStateFrame (swapAccountingMathFrame frame exactInput s d) (swapAccountingState exactInput s d)

theorem swapAccountingState_fits (exactInput : Bool) (s : SwapStateData) (d : SwapIterationData)
    (hs : s.Fits) : (swapAccountingState exactInput s d).Fits :=
  ⟨normalizeSint_bounds ⟨256, by decide⟩ _, normalizeSint_bounds ⟨256, by decide⟩ _, hs.2.2⟩

theorem swapAccountingStmt : swapLoopBody[13]! =
    .ite (.var "exactInput") (swapAccountingBody true) (swapAccountingBody false) := rfl

theorem swapAccountingFirstStmt (exactInput : Bool) : (swapAccountingBody exactInput)[0]! =
    .internalCall "SafeCast_toInt256" (swapAccountingFirstArgs exactInput)
      (swapAccountingFirstName exactInput) := by cases exactInput <;> rfl

theorem swapAccountingSecondStmt (exactInput : Bool) : (swapAccountingBody exactInput)[2]! =
    .internalCall "SafeCast_toInt256" (swapAccountingSecondArgs exactInput)
      (swapAccountingSecondName exactInput) := by cases exactInput <;> rfl

theorem swapAccountingMathStmt (exactInput : Bool) : (swapAccountingBody exactInput)[3]! =
    .internalCall (if exactInput then "LowGasSafeMath_sub" else "LowGasSafeMath_add_int256_int256")
      (swapAccountingMathArgs exactInput) (swapAccountingResultName exactInput) := by
  cases exactInput <;> rfl

end Benchmarks.UniswapV3.Pool
