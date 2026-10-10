import Benchmarks.UniswapV4PoolManager.PoolModifyValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyInputsFrame (f : Frame) (p : PoolModifyParams) : Frame :=
  {f with locals := (((((f.locals.insert "delta" (.int 0)).insert "feeDelta" (.int 0)).insert
    "liquidityDelta" (.int p.delta)).insert "tickLower" (.int (EVM.signed p.lower))).insert
    "tickUpper" (.int (EVM.signed p.upper)))}
def poolModifyPreludeFrame (f : Frame) (p : PoolModifyParams) : Frame :=
  let f1 := poolModifyInputsFrame f p
  {f1 with locals := (f1.locals.insert "__c0" .unit).insert "state" (poolModifyStateValue false ⟨0⟩ false ⟨0⟩)}

theorem poolModifyInitialState {f : Frame} {evm : State} :
    ExecStmt config f evm poolModifyFunction.body[6]!
      (.ok {f with locals := f.locals.insert "state" (poolModifyStateValue false ⟨0⟩ false ⟨0⟩)} evm) := by
  apply ExecStmt.letDecl
  simp only [evalExpr?, evalStructFields?, bind, EvalResult.bind, pure]
  rfl

theorem poolModifyInputs {f : Frame} {evm : EVM.State} {p : PoolModifyParams}
    (hp : f.locals.get? "params" = some (poolModifyParamsValue p)) :
    ExecBlock config f evm (poolModifyFunction.body.take 5) (.ok (poolModifyInputsFrame f p) evm) := by
  let f1 := {f with locals := f.locals.insert "delta" (.int 0)}
  let f2 := {f1 with locals := f1.locals.insert "feeDelta" (.int 0)}
  let f3 := {f2 with locals := f2.locals.insert "liquidityDelta" (.int p.delta)}
  let f4 := {f3 with locals := f3.locals.insert "tickLower" (.int (EVM.signed p.lower))}
  have h0 : ExecStmt config f evm poolModifyFunction.body[0]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  have h1 : ExecStmt config f1 evm poolModifyFunction.body[1]! (.ok f2 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  have hp2 : f2.locals.get? "params" = some (poolModifyParamsValue p) :=
    (store_get_ne2 _ _ _ (by decide : ("delta" == "params") = false)
      (by decide : ("feeDelta" == "params") = false)).trans hp
  have h2 : ExecStmt config f2 evm poolModifyFunction.body[2]! (.ok f3 evm) :=
    ExecStmt.letDecl (evalStructField (evalLocalValue hp2) rfl)
  have hp3 : f3.locals.get? "params" = some (poolModifyParamsValue p) :=
    (store_get_ne _ _ (by decide : ("liquidityDelta" == "params") = false)).trans hp2
  have h3 : ExecStmt config f3 evm poolModifyFunction.body[3]! (.ok f4 evm) :=
    ExecStmt.letDecl (evalStructField (evalLocalValue hp3) rfl)
  have hp4 : f4.locals.get? "params" = some (poolModifyParamsValue p) :=
    (store_get_ne _ _ (by decide : ("tickLower" == "params") = false)).trans hp3
  have h4 : ExecStmt config f4 evm poolModifyFunction.body[4]! (.ok (poolModifyInputsFrame f p) evm) :=
    ExecStmt.letDecl (evalStructField (evalLocalValue hp4) rfl)
  exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2
    (ExecBlock.consNormal h3 (execBlock_singleton h4))))

theorem poolModifyPrelude {f : Frame} {evm : EVM.State} {p : PoolModifyParams}
    (hf : f.contract = contract) (hp : f.locals.get? "params" = some (poolModifyParamsValue p)) :
    ExecBlock config f evm (poolModifyFunction.body.take 7)
      (if poolTicksValid p.lower p.upper then .ok (poolModifyPreludeFrame f p) evm else .reverted) := by
  let f5 := poolModifyInputsFrame f p
  let f6 := {f5 with locals := f5.locals.insert "__c0" .unit}
  have hi := poolModifyInputs (f := f) (p := p) (evm := evm) hp
  have hl : f5.locals.get? "tickLower" = some (.int (EVM.signed p.lower)) :=
    (store_get_ne _ _ (by decide : ("tickUpper" == "tickLower") = false)).trans (store_get_self _ _ _)
  have hu : f5.locals.get? "tickUpper" = some (.int (EVM.signed p.upper)) := store_get_self _ _ _
  have hf5 : f5.contract = contract := by dsimp only [f5, poolModifyInputsFrame]; exact hf
  have ht := poolTicksCall (f := f5) (evm := evm) (lower := p.lower) (upper := p.upper)
    (el := .var "tickLower") (eu := .var "tickUpper")
    hf5 (evalLocalValue (cfg := config) (f := f5) (evm := evm) hl)
    (evalLocalValue (cfg := config) (f := f5) (evm := evm) hu) "__c0"
  by_cases hv : poolTicksValid p.lower p.upper
  · rw [if_pos hv] at ht ⊢
    have hs := poolModifyInitialState (f := f6) (evm := evm)
    have hb := execBlock_append hi (ExecBlock.consNormal ht (execBlock_singleton hs))
    simpa only [f6, f5, poolModifyPreludeFrame] using hb
  · rw [if_neg hv] at ht ⊢
    exact execBlock_append hi (ExecBlock.consRevert ht)

end Benchmarks.UniswapV4PoolManager
