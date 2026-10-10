import Benchmarks.UniswapV3.Pool.SwapFeeGrowthSource
import Benchmarks.UniswapV3.Pool.TickLogSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapCrossBody : List Stmt :=
  match swapLoopBody[16]! with
  | .ite _ yes _ => yes
  | _ => []

def swapNoCrossBody : List Stmt :=
  match swapLoopBody[16]! with
  | .ite _ _ no => no
  | _ => []

def swapPriceChangedBody : List Stmt :=
  match swapNoCrossBody[0]! with
  | .ite _ yes _ => yes
  | _ => []

def swapPriceTick (s : SwapStateData) : Int := tickLogChoice (tickLogResult s.price) s.price

def swapPriceChangedState (s : SwapStateData) (d : SwapIterationData) : SwapStateData :=
  if s.price = d.priceStart then s else {s with tick := swapPriceTick s}

def swapPriceTickFrame (frame : Frame) (s : SwapStateData) : Frame :=
  resumeAfterInternalCall frame "__c15" (some [.int (swapPriceTick s)])

def swapPriceChangedFrame (frame : Frame) (s : SwapStateData) (d : SwapIterationData) : Frame :=
  if s.price = d.priceStart then frame
  else swapStateFrame (swapPriceTickFrame frame s) {s with tick := swapPriceTick s}

theorem evalSwapPriceChanged {frame : Frame} {evm : EVM.State}
    (s : SwapStateData) (d : SwapIterationData)
    (hs : frame.locals.get? "state" = some s.value)
    (hd : frame.locals.get? "step" = some d.value) :
    evalExpr? config frame evm
      (.binary .ne (.field (.var "state") "sqrtPriceX96")
        (.field (.var "step") "sqrtPriceStartX96")) =
      .ok (.bool (decide (s.price ≠ d.priceStart))) := by
  have hp := evalExpr_structField (name := "sqrtPriceX96")
    (evalExpr_var_get (cfg := config) (evm := evm) hs) rfl
  have hstart := evalExpr_structField (name := "sqrtPriceStartX96")
    (evalExpr_var_get (cfg := config) (evm := evm) hd) rfl
  have hinj : Int.ofNat s.price.toNat = Int.ofNat d.priceStart.toNat ↔
      s.price = d.priceStart := by
    simp only [Int.ofNat_eq_natCast, Int.natCast_inj]
    exact ⟨u256_inj, congrArg UInt256.toNat⟩
  simpa only [ne_eq, hinj] using evalExpr_int_ne hp hstart

theorem evalSwapPriceTickArgs {frame : Frame} {evm : EVM.State} (s : SwapStateData)
    (hs : frame.locals.get? "state" = some s.value) :
    evalExprs? config frame evm [.field (.var "state") "sqrtPriceX96"] =
      .ok [.int (Int.ofNat s.price.toNat)] := by
  have hp := evalExpr_structField (name := "sqrtPriceX96")
    (evalExpr_var_get (cfg := config) (evm := evm) hs) rfl
  simp only [evalExprs?, hp, bind, EvalResult.bind, pure]

theorem swapPriceTickAssignValueSource {frame : Frame} {evm : EVM.State}
    (s : SwapStateData) (tick : Int) (hs : frame.locals.get? "state" = some s.value)
    (hr : frame.locals.get? "__c15" = some (.int tick)) :
    ExecStmt config frame evm swapPriceChangedBody[1]!
      (.ok (swapStateFrame frame {s with tick := tick}) evm) :=
  ExecStmt.assign (evalExpr_var_get hr) (assignLocalField_frame hs rfl rfl)

theorem swapPriceTickAssignSource {frame : Frame} {evm : EVM.State} (s : SwapStateData)
    (hs : frame.locals.get? "state" = some s.value) :
    ExecStmt config (swapPriceTickFrame frame s) evm swapPriceChangedBody[1]!
      (.ok (swapStateFrame (swapPriceTickFrame frame s) {s with tick := swapPriceTick s}) evm) := by
  have hs' := (resumeAfterInternalCall_get frame "__c15" "state"
    (some [.int (swapPriceTick s)]) (by decide)).trans hs
  exact swapPriceTickAssignValueSource s (swapPriceTick s) hs'
    Std.HashMap.getElem?_insert_self

theorem SwapStateData.Fits.tick {s : SwapStateData} (hs : s.Fits) (tick : Int)
    (ht : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23) :
    SwapStateData.Fits {s with tick := tick} :=
  ⟨hs.1, hs.2.1, hs.2.2.1, ht, hs.2.2.2.2⟩

theorem swapPriceTick_bounds (s : SwapStateData) :
    -(2 ^ 23 : Int) ≤ swapPriceTick s ∧ swapPriceTick s < 2 ^ 23 :=
  tickLogTick_bounds (tickLogChoiceRaw (tickLogResult s.price) s.price)

theorem swapPriceChangedState_fits (s : SwapStateData) (d : SwapIterationData) (hs : s.Fits) :
    (swapPriceChangedState s d).Fits := by
  unfold swapPriceChangedState
  split
  · exact hs
  · exact hs.tick (swapPriceTick s) (swapPriceTick_bounds s)

end Benchmarks.UniswapV3.Pool
