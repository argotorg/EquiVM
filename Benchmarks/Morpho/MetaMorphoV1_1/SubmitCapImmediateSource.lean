import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapGuardsSource
import Benchmarks.Morpho.MetaMorphoV1_1.Uint184Cast
import Benchmarks.Morpho.MetaMorphoV1_1.SetCapSyntax

/-! Source composition of the checked cast and the immediate cap setter. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

def submitCapCastFrame (frame : Frame) (immediate : Bool) (cap : UInt256) : Frame :=
  { frame with
    locals := frame.locals.insert (if immediate then "__c5" else "__c7") (uint256Value cap) }

theorem SubmitCapReady.cast {frame : Frame} {p : MarketParamsData}
    {id cap last cursor : UInt256} (h : SubmitCapReady frame p id cap last cursor)
    (immediate : Bool) :
    SubmitCapReady (submitCapCastFrame frame immediate cap) p id cap last cursor := by
  cases immediate <;>
    refine ⟨h.contract, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [submitCapCastFrame, store_get_ne _ _ (by decide)] <;>
    first | exact h.config | exact h.pending | exact h.timelock | exact h.params
          | exact h.id | exact h.cap | exact h.last | exact h.cursor

theorem submitCapCastCall {frame : Frame} {evm : State} {p : MarketParamsData}
    {id cap last cursor : UInt256} (h : SubmitCapReady frame p id cap last cursor)
    (immediate : Bool) (hfit : cap.toNat < 2 ^ 184) :
    ExecStmt config frame evm
      (.internalCall "SafeCast_toUint184" [.var "newSupplyCap"]
        (if immediate then "__c5" else "__c7"))
      (.ok (submitCapCastFrame frame immediate cap) evm) := by
  apply internalCallFunctionReturn (callee := toUint184Function)
    (value := some [uint256Value cap]) (argVals := [uint256Value cap])
  · simp only [evalExprs?, evalExpr?, h.cap, EvalResult.ofOption, bind, EvalResult.bind, pure]
  · rw [h.contract]; rfl
  · rfl
  · simpa only [toUint184Frame, h.contract] using toUint184Body frame.immutables cap evm hfit

theorem submitCapCastCallReverts {frame : Frame} {evm : State} {p : MarketParamsData}
    {id cap last cursor : UInt256} (h : SubmitCapReady frame p id cap last cursor)
    (immediate : Bool) (hover : 2 ^ 184 ≤ cap.toNat) :
    ExecStmt config frame evm
      (.internalCall "SafeCast_toUint184" [.var "newSupplyCap"]
        (if immediate then "__c5" else "__c7")) .reverted := by
  apply internalCallFunctionRevert (callee := toUint184Function) (argVals := [uint256Value cap])
  · simp only [evalExprs?, evalExpr?, h.cap, EvalResult.ofOption, bind, EvalResult.bind, pure]
  · rw [h.contract]; rfl
  · rfl
  · simpa only [toUint184Frame, h.contract] using
      toUint184BodyReverts frame.immutables cap evm hover

theorem submitCapImmediateArgs {frame : Frame} {evm : State} {p : MarketParamsData}
    {id cap last cursor : UInt256} (h : SubmitCapReady frame p id cap last cursor) :
    evalExprs? config (submitCapCastFrame frame true cap) evm
      [.var "marketParams", .var "id", .var "__c5", .var cursorName] =
      .ok [p.value, wordBytes32Value id, uint256Value cap, uint256Value cursor] := by
  have h' := h.cast true
  have hc : (submitCapCastFrame frame true cap).locals.get? "__c5" =
      some (uint256Value cap) := store_get_self _ _ _
  simp only [evalExprs?, evalExpr?, h'.params, h'.id, hc, h'.cursor,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem submitCapImmediateReverts {frame : Frame} {evm : State} {p : MarketParamsData}
    {id cap last cursor : UInt256} (h : SubmitCapReady frame p id cap last cursor)
    (hfit : cap.toNat < 2 ^ 184)
    (hcallee : ExecFuncBody config (setCapFrame frame.immutables p id cap cursor) evm
      allocatedSetCapFunction.body .reverted) :
    ExecBlock config frame evm submitCapImmediate .reverted := by
  apply ExecBlock.consNormal (submitCapCastCall h true hfit)
  apply ExecBlock.consRevert
  apply internalCallFunctionRevert (callee := allocatedSetCapFunction)
    (submitCapImmediateArgs h)
    (by rw [(h.cast true).contract]; exact allocatedSetCapFunction_lookup)
    rfl
  simpa only [setCapFrame, submitCapCastFrame, h.contract] using hcallee

theorem submitCapImmediateStatic {frame : Frame} {evm : State} {p : MarketParamsData}
    {id cap last cursor : UInt256} (h : SubmitCapReady frame p id cap last cursor)
    (hfit : cap.toNat < 2 ^ 184)
    (hcallee : ExecFuncBody config (setCapFrame frame.immutables p id cap cursor) evm
      allocatedSetCapFunction.body .staticViolation) :
    ExecBlock config frame evm submitCapImmediate .staticViolation := by
  apply ExecBlock.consNormal (submitCapCastCall h true hfit)
  apply ExecBlock.consStatic
  apply ExecStmt.internalCallStatic (callee := allocatedSetCapFunction.toCallable)
    (submitCapImmediateArgs h)
    (by rw [(h.cast true).contract]; exact allocatedSetCapFunction_lookup)
    rfl
  simpa only [setCapFrame, submitCapCastFrame, h.contract] using hcallee

theorem submitCapImmediateReturns {frame final : Frame} {evm evm' : State}
    {p : MarketParamsData} {id cap last cursor next : UInt256}
    (h : SubmitCapReady frame p id cap last cursor) (hfit : cap.toNat < 2 ^ 184)
    (hcallee : ExecFuncBody config (setCapFrame frame.immutables p id cap cursor) evm
      allocatedSetCapFunction.body (.returned final evm' (some [uint256Value next]))) :
    ExecBlock config frame evm submitCapImmediate
      (.ok (resumeAfterInternalCall (submitCapCastFrame frame true cap) "__c6"
        (some [uint256Value next])) evm') := by
  apply ExecBlock.consNormal (submitCapCastCall h true hfit)
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  apply internalCallFunctionReturn (callee := allocatedSetCapFunction)
    (submitCapImmediateArgs h)
    (by rw [(h.cast true).contract]; exact allocatedSetCapFunction_lookup)
    rfl
  simpa only [setCapFrame, submitCapCastFrame, h.contract] using hcallee

end Benchmarks.Morpho.MetaMorphoV1_1
