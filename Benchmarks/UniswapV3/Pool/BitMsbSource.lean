import Benchmarks.UniswapV3.Pool.BitMsbStepSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def bitMsbFunction : FunctionDecl := contract.functions[34]!

theorem bitMsbLookup :
    lookupCallable? contract "BitMath_mostSignificantBit" = some bitMsbFunction.toCallable := rfl

def bitMsbLocals (x : UInt256) : Store := (∅ : Store).insert "x" (.int (Int.ofNat x.toNat))

def bitMsbFrame (imms : Store) (x : UInt256) : Frame :=
  {contract := contract, locals := bitMsbLocals x, immutables := imms}

def bitMsbZeroFrame (imms : Store) (x : UInt256) : Frame :=
  {bitMsbFrame imms x with locals := (bitMsbLocals x).insert "r" (.int 0)}

theorem bitMsbBind (x : UInt256) :
    bindParams? bitMsbFunction.params [.int (Int.ofNat x.toNat)] = some (bitMsbLocals x) := rfl

def bitMsbPrefixBits : List Nat := [128, 64, 32, 16, 8, 4, 2]

def bitMsbPrefix (x : UInt256) : Nat × UInt256 :=
  bitMsbPrefixBits.foldl tickLogMsbStep (0, x)

theorem bitMsbPrefix_bound (x : UInt256) : (bitMsbPrefix x).1 ≤ 254 :=
  tickLogMsbFold_count_le (0, x) bitMsbPrefixBits

theorem bitMsbPrefix_result (x : UInt256) :
    (tickLogMsbStep (bitMsbPrefix x) 1).1 = tickLogMsbCount x := by
  have h := congrArg Prod.fst (tickLogMsbFold_eq x)
  simpa only [tickLogMsbBits, bitMsbPrefix, bitMsbPrefixBits,
    List.foldl_cons, List.foldl_nil] using h

theorem evalBitMsbGuard (imms : Store) (evm : EVM.State) (x : UInt256) :
    evalExpr? config (bitMsbZeroFrame imms x) evm (.binary .gt (.var "x") (.intLit 0)) =
      .ok (.bool (decide (0 < x.toNat))) :=
  evalExpr_word_gt (b := ⟨0⟩) (evalExpr_var_get (by
    simp only [bitMsbZeroFrame, bitMsbLocals, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
    rfl)) (by simp only [evalExpr?, pure]; rfl)

theorem bitMsbReverts (imms : Store) (evm : EVM.State) (x : UInt256) (hx : ¬0 < x.toNat) :
    ExecFuncBody config (bitMsbFrame imms x) evm bitMsbFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consNormal (solm' := bitMsbZeroFrame imms x)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (by simpa only [hx, decide_false] using evalBitMsbGuard imms evm x))

theorem bitMsbReturns (imms : Store) (evm : EVM.State) (x : UInt256) (hx : 0 < x.toNat) :
    ∃ out, ExecFuncBody config (bitMsbFrame imms x) evm bitMsbFunction.body
      (.returned out evm (some [.int (Int.ofNat (tickLogMsbCount x))])) := by
  have hr : (bitMsbZeroFrame imms x).locals.get? "r" = some (.int 0) :=
    Std.HashMap.getElem?_insert_self
  have hget : (bitMsbZeroFrame imms x).locals.get? "x" = some (.int (Int.ofNat x.toNat)) := by
    simp only [bitMsbZeroFrame, bitMsbLocals, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
    rfl
  obtain ⟨mid, hs, hr', hx'⟩ := bitMsbFoldSource (evm := evm) (0, x) bitMsbPrefixBits
    hr hget (by change 254 < 256; decide)
  obtain ⟨out, ht, hr'', _⟩ := bitMsbStepSource (evm := evm) (bitMsbPrefix x) 1 false
    hr' hx' (by have hb := bitMsbPrefix_bound x; omega)
  refine ⟨out, ExecFuncBody.execBlockRet ?_⟩
  refine ExecBlock.consNormal (solm' := bitMsbZeroFrame imms x)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (by simpa only [hx, decide_true] using evalBitMsbGuard imms evm x)) ?_
  change ExecBlock _ _ _ ((bitMsbPrefixBits.map (fun b ↦ bitMsbStepStmt b true)) ++
    [bitMsbStepStmt 1 false, .return [.var "r"]]) _
  apply execBlock_append_ok hs
  refine ExecBlock.consNormal ht (ExecBlock.consReturn (ExecStmt.return ?_))
  rw [bitMsbPrefix_result] at hr''
  have he := evalExpr_var_get (cfg := config) (evm := evm) hr''
  simp only [evalExprs?, he, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
