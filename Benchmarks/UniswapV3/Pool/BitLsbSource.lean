import Benchmarks.UniswapV3.Pool.BitLsbStepSource
import Benchmarks.UniswapV3.Pool.BitMsbSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def bitLsbFunction : FunctionDecl := contract.functions[35]!

theorem bitLsbLookup :
    lookupCallable? contract "BitMath_leastSignificantBit" = some bitLsbFunction.toCallable := rfl

-- Both BitMath functions have the same parameter and initial local declaration.
abbrev bitLsbLocals := bitMsbLocals
abbrev bitLsbFrame := bitMsbFrame
abbrev bitLsbZeroFrame := bitMsbZeroFrame

def bitLsbReadyFrame (imms : Store) (x : UInt256) : Frame :=
  {bitLsbZeroFrame imms x with locals := (bitLsbZeroFrame imms x).locals.insert "r" (.int 255)}

theorem bitLsbBind (x : UInt256) :
    bindParams? bitLsbFunction.params [.int (Int.ofNat x.toNat)] = some (bitLsbLocals x) := rfl

theorem bitLsbReverts (imms : Store) (evm : EVM.State) (x : UInt256) (hx : ¬0 < x.toNat) :
    ExecFuncBody config (bitLsbFrame imms x) evm bitLsbFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consNormal (solm' := bitLsbZeroFrame imms x)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (by simpa only [hx, decide_false] using evalBitMsbGuard imms evm x))

theorem bitLsbReturns (imms : Store) (evm : EVM.State) (x : UInt256) (hx : 0 < x.toNat) :
    ∃ out, ExecFuncBody config (bitLsbFrame imms x) evm bitLsbFunction.body
      (.returned out evm (some [.int (Int.ofNat (bitLsbCount x))])) := by
  have hr : (bitLsbReadyFrame imms x).locals.get? "r" = some (.int 255) :=
    Std.HashMap.getElem?_insert_self
  have hget : (bitLsbReadyFrame imms x).locals.get? "x" = some (.int (Int.ofNat x.toNat)) := by
    simp only [bitLsbReadyFrame, bitLsbZeroFrame, bitMsbZeroFrame, bitMsbLocals,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  obtain ⟨mid, hs, hr', hx'⟩ := bitLsbFoldSource (evm := evm) (255, x) (tickLogMsbBits.take 7)
    hr hget (by change 255 < 256; decide) (by change 254 ≤ 255; decide)
  obtain ⟨out, ht, hr'', _⟩ := bitLsbStepSource (evm := evm) (bitLsbPrefix x) 1 false
    hr' hx' (bitLsbPrefix_bounds x).2 (bitLsbPrefix_bounds x).1
  refine ⟨out, ExecFuncBody.execBlockRet ?_⟩
  refine ExecBlock.consNormal (solm' := bitLsbZeroFrame imms x)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (by simpa only [hx, decide_true] using evalBitMsbGuard imms evm x)) ?_
  refine ExecBlock.consNormal (solm' := bitLsbReadyFrame imms x)
    (ExecStmt.assign (value := .int 255) (by simp only [evalExpr?, pure])
      (assignLocalVarBase_frame (old := .int 0) Std.HashMap.getElem?_insert_self)) ?_
  change ExecBlock _ _ _ (((tickLogMsbBits.take 7).map (fun b ↦ bitLsbStepStmt b true)) ++
    [bitLsbStepStmt 1 false, .return [.var "r"]]) _
  apply execBlock_append_ok hs
  refine ExecBlock.consNormal ht (ExecBlock.consReturn (ExecStmt.return ?_))
  have he := evalExpr_var_get (cfg := config) (evm := evm) hr''
  simp only [evalExprs?, he, bind, EvalResult.bind, pure]
  rfl

end Benchmarks.UniswapV3.Pool
