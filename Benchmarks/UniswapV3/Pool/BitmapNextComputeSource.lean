import Benchmarks.UniswapV3.Pool.BitmapNextReadSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def bitmapNextScanName (lte : Bool) : String := if lte then "__c1" else "__c4"

def bitmapNextScanCount (lte : Bool) (masked : UInt256) : Nat :=
  if lte then tickLogMsbCount masked else bitLsbCount masked

def bitmapNextScanFrame (imms locals : Store) (lte : Bool) (masked : UInt256) : Frame :=
  {contract := contract, immutables := imms,
    locals := locals.insert (bitmapNextScanName lte)
      (.int (Int.ofNat (bitmapNextScanCount lte masked)))}

def bitmapNextComputeBranch (lte hit : Bool) : List Stmt :=
  match (bitmapNextBranch lte)[7]! with
  | .ite _ yes no => if hit then yes else no
  | _ => []

def bitmapNextResultExpr (lte hit : Bool) : Expr :=
  let narrow (e : Expr) := .cast e (.elem (.int (.sint ⟨24, by decide⟩)))
  let byte (e : Expr) := .cast e (.elem (.int (.uint ⟨8, by decide⟩)))
  let bit := .var "bitPos"
  let scan := .var (bitmapNextScanName lte)
  let distance := if hit then
      byte (.binary .sub (if lte then bit else scan) (if lte then scan else bit))
    else if lte then bit else byte (.binary .sub (.intLit 255) bit)
  let next := if lte then .binary .sub (.var "compressed") (narrow distance)
    else .binary .add (narrow (.binary .add (.var "compressed") (.intLit 1))) (narrow distance)
  narrow (.binary .mul (narrow next) (.var "tickSpacing"))

theorem bitmapNextScanSource (imms locals : Store) (evm : EVM.State) (lte : Bool) (masked : UInt256)
    (hm : locals.get? "masked" = some (.int (Int.ofNat masked.toNat))) (hn : masked ≠ ⟨0⟩) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} evm
      (bitmapNextComputeBranch lte true)[0]!
      (.ok (bitmapNextScanFrame imms locals lte masked) evm) := by
  have hx : 0 < masked.toNat := by
    by_contra h
    exact hn (uint256_toNat_eq_zero (by omega))
  have he := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) hm
  cases lte
  · obtain ⟨out, hbody⟩ := bitLsbReturns imms evm masked hx
    exact internalCallFunctionReturn (callee := bitLsbFunction) (locals := bitLsbLocals masked)
      (calleeSolm := out) (value := some [.int (Int.ofNat (bitLsbCount masked))])
      (by simp only [evalExprs?, he, bind, EvalResult.bind, pure])
      bitLsbLookup (bitLsbBind masked) hbody
  · obtain ⟨out, hbody⟩ := bitMsbReturns imms evm masked hx
    exact internalCallFunctionReturn (callee := bitMsbFunction) (locals := bitMsbLocals masked)
      (calleeSolm := out) (value := some [.int (Int.ofNat (tickLogMsbCount masked))])
      (by simp only [evalExprs?, he, bind, EvalResult.bind, pure])
      bitMsbLookup (bitMsbBind masked) hbody

theorem evalBitmapNextResult {frame : Frame} {evm : EVM.State}
    (compressed spacing : Int) (lte : Bool) (masked : UInt256)
    (hc : frame.locals.get? "compressed" = some (.int compressed))
    (hs : frame.locals.get? "tickSpacing" = some (.int spacing))
    (hb : frame.locals.get? "bitPos" =
      some (.int (bitmapBitPos (bitmapNextPosition compressed lte))))
    (hr : masked ≠ ⟨0⟩ → frame.locals.get? (bitmapNextScanName lte) =
      some (.int (Int.ofNat (bitmapNextScanCount lte masked)))) :
    evalExpr? config frame evm (bitmapNextResultExpr lte (decide (masked ≠ ⟨0⟩))) =
      .ok (.int (bitmapNextResult compressed spacing lte masked)) := by
  have ec := evalExpr_var_get (cfg := config) (evm := evm) hc
  have es := evalExpr_var_get (cfg := config) (evm := evm) hs
  have eb := evalExpr_var_get (cfg := config) (evm := evm) hb
  by_cases hz : masked = ⟨0⟩
  · cases lte <;>
      simp only [hz, ne_eq, not_true_eq_false, decide_false, bitmapNextResultExpr,
        evalExpr?, ec, es, eb,
        evalBinaryOp?, castValue?, bind, EvalResult.bind, EvalResult.ofOption, pure,
        bitmapNextResult, Bool.false_eq_true, ↓reduceIte]
  · have er := evalExpr_var_get (cfg := config) (evm := evm) (hr hz)
    cases lte <;>
      simp only [ne_eq, hz, not_false_eq_true, decide_true, bitmapNextResultExpr,
        evalExpr?, ec, es, eb, er, bitmapNextScanCount,
        evalBinaryOp?, castValue?, bind, EvalResult.bind, EvalResult.ofOption, pure,
        bitmapNextResult, Bool.false_eq_true, ↓reduceIte]

theorem bitmapNextScanGet (imms locals : Store) (lte : Bool) (masked : UInt256)
    (name : String) (hne : name ≠ bitmapNextScanName lte) :
    (bitmapNextScanFrame imms locals lte masked).locals.get? name = locals.get? name := by
  simp only [bitmapNextScanFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, beq_iff_eq, if_neg (Ne.symm hne)]

def bitmapNextComputedFrame (imms locals : Store) (compressed spacing : Int)
    (lte : Bool) (masked : UInt256) : Frame :=
  {contract := contract, immutables := imms,
    locals := (if masked = ⟨0⟩ then locals else (bitmapNextScanFrame imms locals lte masked).locals)
      |>.insert (bitmapNextCondName lte) (.int (bitmapNextResult compressed spacing lte masked))}

theorem bitmapNextComputeSource (imms locals : Store) (evm : EVM.State)
    (compressed spacing : Int) (lte : Bool) (masked : UInt256)
    (hc : locals.get? "compressed" = some (.int compressed))
    (hs : locals.get? "tickSpacing" = some (.int spacing))
    (hb : locals.get? "bitPos" = some (.int (bitmapBitPos (bitmapNextPosition compressed lte))))
    (hm : locals.get? "masked" = some (.int (Int.ofNat masked.toNat)))
    (hi : locals.get? "initialized" = some (.bool (decide (masked ≠ ⟨0⟩))))
    (hh : locals.get? (bitmapNextCondName lte) = some (.int 0)) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} evm
      (bitmapNextBranch lte)[7]!
      (.ok (bitmapNextComputedFrame imms locals compressed spacing lte masked) evm) := by
  let frame : Frame := {contract := contract, locals := locals, immutables := imms}
  have eg := evalExpr_var_get (cfg := config) (frame := frame) (evm := evm) hi
  by_cases hz : masked = ⟨0⟩
  · have he := evalBitmapNextResult (frame := frame) (evm := evm) compressed spacing lte masked
      hc hs hb (fun hn ↦ (hn hz).elim)
    have hfalse : decide (masked ≠ ⟨0⟩) = false := by
      simp only [hz, ne_eq, not_true_eq_false, decide_false]
    rw [hfalse] at he eg
    have ha : ExecStmt config frame evm
        (.assign .localVar ⟨bitmapNextCondName lte, []⟩ (bitmapNextResultExpr lte false))
        (.ok (bitmapNextComputedFrame imms locals compressed spacing lte masked) evm) := by
      simp only [bitmapNextComputedFrame, if_pos hz]
      exact ExecStmt.assign he (assignLocalVarBase_frame hh)
    cases lte <;> exact ExecStmt.iteFalse eg (ExecBlock.consNormal ha ExecBlock.nil)
  · have he := evalBitmapNextResult (frame := bitmapNextScanFrame imms locals lte masked)
      (evm := evm) compressed spacing lte masked
      ((bitmapNextScanGet imms locals lte masked "compressed" (by cases lte <;> decide)).trans hc)
      ((bitmapNextScanGet imms locals lte masked "tickSpacing" (by cases lte <;> decide)).trans hs)
      ((bitmapNextScanGet imms locals lte masked "bitPos" (by cases lte <;> decide)).trans hb)
      (fun _ ↦ Std.HashMap.getElem?_insert_self)
    have hh' := (bitmapNextScanGet imms locals lte masked (bitmapNextCondName lte)
      (by cases lte <;> decide)).trans hh
    have htrue : decide (masked ≠ ⟨0⟩) = true := decide_eq_true hz
    rw [htrue] at he eg
    have ha : ExecStmt config (bitmapNextScanFrame imms locals lte masked) evm
        (.assign .localVar ⟨bitmapNextCondName lte, []⟩ (bitmapNextResultExpr lte true))
        (.ok (bitmapNextComputedFrame imms locals compressed spacing lte masked) evm) := by
      simp only [bitmapNextComputedFrame, if_neg hz]
      exact ExecStmt.assign he (assignLocalVarBase_frame hh')
    have hscan := bitmapNextScanSource imms locals evm lte masked hm hz
    cases lte <;> exact ExecStmt.iteTrue eg
      (ExecBlock.consNormal hscan (ExecBlock.consNormal ha ExecBlock.nil))

end Benchmarks.UniswapV3.Pool
