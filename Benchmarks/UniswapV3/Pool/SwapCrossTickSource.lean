import Benchmarks.UniswapV3.Pool.SwapPriceChangedSource
import Benchmarks.UniswapV3.Pool.SwapIterationMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapCrossTick (zeroForOne : Bool) (d : SwapIterationData) : Int :=
  if zeroForOne then normalizeInt (.sint ⟨24, by decide⟩) (d.tickNext - 1) else d.tickNext

def swapCrossTickState (zeroForOne : Bool) (s : SwapStateData) (d : SwapIterationData) :
    SwapStateData := {s with tick := swapCrossTick zeroForOne d}

def swapCrossTickFrame (frame : Frame) (zeroForOne : Bool) (s : SwapStateData)
    (d : SwapIterationData) : Frame := swapStateFrame frame (swapCrossTickState zeroForOne s d)

theorem swapCrossTickSource {frame : Frame} {evm : EVM.State}
    (zeroForOne : Bool) (s : SwapStateData) (d : SwapIterationData)
    (hz : frame.locals.get? "zeroForOne" = some (.bool zeroForOne))
    (hs : frame.locals.get? "state" = some s.value)
    (hd : frame.locals.get? "step" = some d.value) :
    ExecStmt config frame evm swapCrossBody[1]!
      (.ok (swapCrossTickFrame frame zeroForOne s d) evm) := by
  have hez := evalExpr_var_get (cfg := config) (evm := evm) hz
  have het := evalExpr_structField (name := "tickNext")
    (evalExpr_var_get (cfg := config) (evm := evm) hd) rfl
  apply ExecStmt.assign _ (assignLocalField_frame hs rfl rfl)
  cases zeroForOne <;>
    simp only [evalExpr?, hez, het, evalBinaryOp?, castValue?, EvalResult.ofOption,
      bind, EvalResult.bind, pure] <;> rfl

theorem swapCrossTick_bounds (zeroForOne : Bool) (d : SwapIterationData)
    (ht : -(2 ^ 23 : Int) ≤ d.tickNext ∧ d.tickNext < 2 ^ 23) :
    -(2 ^ 23 : Int) ≤ swapCrossTick zeroForOne d ∧ swapCrossTick zeroForOne d < 2 ^ 23 := by
  cases zeroForOne
  · exact ht
  · exact normalizeSint_bounds ⟨24, by decide⟩ _

theorem swapCrossTickState_fits (zeroForOne : Bool) (s : SwapStateData) (d : SwapIterationData)
    (hs : s.Fits) (ht : -(2 ^ 23 : Int) ≤ d.tickNext ∧ d.tickNext < 2 ^ 23) :
    (swapCrossTickState zeroForOne s d).Fits :=
  hs.tick _ (swapCrossTick_bounds zeroForOne d ht)

theorem swapCrossTick_word (zeroForOne : Bool) (d : SwapIterationData)
    (ht : -(2 ^ 23 : Int) ≤ d.tickNext ∧ d.tickNext < 2 ^ 23) :
    UInt256.signextend (UInt256.ofNat 2)
        (if zeroForOne then UInt256.sub (EVM.wordOfInt d.tickNext) (UInt256.ofNat 1)
          else EVM.wordOfInt d.tickNext) = EVM.wordOfInt (swapCrossTick zeroForOne d) := by
  cases zeroForOne
  · simp only [Bool.false_eq_true, if_false]
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ d.tickNext (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ ht.1 ht.2]
    rfl
  · simp only [if_true, swapCrossTick]
    rw [show UInt256.ofNat 1 = EVM.wordOfInt 1 by decide +kernel, ← wordOfInt_sub]
    exact signextend_wordOfInt ⟨24, by decide⟩ _ (d.tickNext - 1) (by decide) (by decide)

end Benchmarks.UniswapV3.Pool
