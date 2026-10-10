import Benchmarks.UniswapV4PoolManager.BalanceDeltaComponentSource
import Benchmarks.UniswapV4PoolManager.BalanceDeltaSource
import Benchmarks.UniswapV4PoolManager.SafeCast128Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def balanceDeltaCombineOp (sub : Bool) : BinaryOp := if sub then .sub else .add
def balanceDeltaCombineInt (sub : Bool) (a b : Int) : Int := if sub then a-b else a+b
def balanceDeltaCombineAmount (sub one : Bool) (a b : UInt256) : Int :=
  balanceDeltaCombineInt sub (balanceDeltaComponent one a) (balanceDeltaComponent one b)
def balanceDeltaCombineFits (sub : Bool) (a b : UInt256) : Prop :=
  signedFits ⟨128, by decide⟩ (balanceDeltaCombineAmount sub false a b) ∧
    signedFits ⟨128, by decide⟩ (balanceDeltaCombineAmount sub true a b)
instance (sub : Bool) (a b : UInt256) : Decidable (balanceDeltaCombineFits sub a b) :=
  inferInstanceAs (Decidable (_ ∧ _))
def balanceDeltaCombineWord (sub : Bool) (a b : UInt256) : UInt256 :=
  balanceDeltaWord (EVM.wordOfInt (balanceDeltaCombineAmount sub false a b))
    (EVM.wordOfInt (balanceDeltaCombineAmount sub true a b))
def balanceDeltaCombineFrame (f : Frame) (sub : Bool) (a b : UInt256) : Frame :=
  let f0 := {f with locals := f.locals.insert "amount0" (.int (balanceDeltaCombineAmount sub false a b))}
  let f1 := {f0 with locals := f0.locals.insert "amount1" (.int (balanceDeltaCombineAmount sub true a b))}
  {f1 with locals := f1.locals.insert "result" (.int (EVM.signed (balanceDeltaCombineWord sub a b)))}
def balanceDeltaCombineResult (f : Frame) (evm : State) (sub : Bool) (a b : UInt256) : ExecResult :=
  if balanceDeltaCombineFits sub a b then .returned (balanceDeltaCombineFrame f sub a b) evm
    (some [.int (EVM.signed (balanceDeltaCombineWord sub a b))]) else .reverted
def balanceDeltaCombineName (sub : Bool) : Ident := if sub then "BalanceDelta_sub" else "BalanceDelta_add"
def balanceDeltaCombineFunction (sub : Bool) : FunctionDecl :=
  if sub then contract.functions[29]! else contract.functions[28]!
def balanceDeltaCombineExpr (sub one : Bool) : Expr := .binary (balanceDeltaCombineOp sub)
  (balanceDeltaComponentExpr one (.var "a")) (balanceDeltaComponentExpr one (.var "b"))

theorem balanceDeltaCombine_lookup (sub : Bool) : lookupCallable? contract (balanceDeltaCombineName sub) =
    some (balanceDeltaCombineFunction sub).toCallable := by cases sub <;> rfl

theorem balanceDeltaCombine_body (sub : Bool) : (balanceDeltaCombineFunction sub).body =
    [.internalCall "SafeCast_toInt128" [balanceDeltaCombineExpr sub false] "amount0",
     .internalCall "SafeCast_toInt128" [balanceDeltaCombineExpr sub true] "amount1",
     .internalCall "toBalanceDelta" [.var "amount0", .var "amount1"] "result",
     .return [.var "result"]] := by cases sub <;> rfl

theorem balanceDeltaCombine_eval {f : Frame} {evm : State} {a b : UInt256}
    (ha : f.locals.get? "a" = some (.int (EVM.signed a)))
    (hb : f.locals.get? "b" = some (.int (EVM.signed b))) (sub one : Bool) :
    evalExpr? config f evm (balanceDeltaCombineExpr sub one) = .ok (.int (balanceDeltaCombineAmount sub one a b)) := by
  have h0 := balanceDeltaComponent_eval (cfg := config) (evm := evm) (evalLocalValue ha) one
  have h1 := balanceDeltaComponent_eval (cfg := config) (evm := evm) (evalLocalValue hb) one
  cases sub <;> rw [balanceDeltaCombineExpr, evalExpr_binary_nonshort (by decide) (by decide), h0, h1] <;> rfl

theorem balanceDeltaCombineBody {f : Frame} {evm : State} {a b : UInt256}
    (hf : f.contract = contract) (ha : f.locals.get? "a" = some (.int (EVM.signed a)))
    (hb : f.locals.get? "b" = some (.int (EVM.signed b))) (sub : Bool) :
    ExecFuncBody config f evm (balanceDeltaCombineFunction sub).body (balanceDeltaCombineResult f evm sub a b) := by
  rw [balanceDeltaCombine_body]
  have hfirst := signedToInt128Call hf (balanceDeltaCombine_eval (evm := evm) ha hb sub false) "amount0"
  by_cases h0 : signedFits ⟨128, by decide⟩ (balanceDeltaCombineAmount sub false a b)
  · rw [if_pos h0] at hfirst
    let f1 := {f with locals := f.locals.insert "amount0" (.int (balanceDeltaCombineAmount sub false a b))}
    have ha1 : f1.locals.get? "a" = some (.int (EVM.signed a)) := (store_get_ne _ _ (by decide : ("amount0" == "a") = false)).trans ha
    have hb1 : f1.locals.get? "b" = some (.int (EVM.signed b)) := (store_get_ne _ _ (by decide : ("amount0" == "b") = false)).trans hb
    have hsecond := signedToInt128Call (f := f1) hf (balanceDeltaCombine_eval (evm := evm) ha1 hb1 sub true) "amount1"
    by_cases h1 : signedFits ⟨128, by decide⟩ (balanceDeltaCombineAmount sub true a b)
    · rw [if_pos h1] at hsecond
      rw [balanceDeltaCombineResult, if_pos (show balanceDeltaCombineFits sub a b from ⟨h0, h1⟩)]
      let f2 := {f1 with locals := f1.locals.insert "amount1" (.int (balanceDeltaCombineAmount sub true a b))}
      have he0 : evalExpr? config f2 evm (.var "amount0") =
          .ok (.int (EVM.signed (EVM.wordOfInt (balanceDeltaCombineAmount sub false a b)))) := by
        rw [signed_wordOfInt (signedFits128_int256 h0)]
        exact evalLocalValue ((store_get_ne _ _ (by decide : ("amount1" == "amount0") = false)).trans (store_get_self _ _ _))
      have he1 : evalExpr? config f2 evm (.var "amount1") =
          .ok (.int (EVM.signed (EVM.wordOfInt (balanceDeltaCombineAmount sub true a b)))) := by
        rw [signed_wordOfInt (signedFits128_int256 h1)]
        exact evalLocalValue (store_get_self _ _ _)
      have hpack := balanceDeltaCall (f := f2) hf he0 he1 "result"
      exact .execBlockRet (ExecBlock.consNormal hfirst (ExecBlock.consNormal hsecond
        (ExecBlock.consNormal hpack (ABlock.start.returns (evalLocalValue (store_get_self _ _ _))))))
    · rw [balanceDeltaCombineResult, if_neg (show ¬balanceDeltaCombineFits sub a b from fun hh => h1 hh.2)]
      rw [if_neg h1] at hsecond
      exact .execBlockRevert (ExecBlock.consNormal hfirst (ExecBlock.consRevert hsecond))
  · rw [balanceDeltaCombineResult, if_neg (show ¬balanceDeltaCombineFits sub a b from fun hh => h0 hh.1)]
    rw [if_neg h0] at hfirst
    exact .execBlockRevert (ExecBlock.consRevert hfirst)

theorem balanceDeltaCombineCall {f : Frame} {evm : State} {ea eb : Expr} {a b : UInt256}
    (hf : f.contract = contract) (ha : evalExpr? config f evm ea = .ok (.int (EVM.signed a)))
    (hb : evalExpr? config f evm eb = .ok (.int (EVM.signed b))) (sub : Bool) (ret : Ident) :
    ExecStmt config f evm (.internalCall (balanceDeltaCombineName sub) [ea, eb] ret)
      (if balanceDeltaCombineFits sub a b then
        .ok {f with locals := f.locals.insert ret (.int (EVM.signed (balanceDeltaCombineWord sub a b)))} evm else .reverted) := by
  let fc := {f with locals := ((∅ : Store).insert "b" (.int (EVM.signed b))).insert "a" (.int (EVM.signed a))}
  have hr := balanceDeltaCombineBody (f := fc) (evm := evm) hf (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("a" == "b") = false)).trans (store_get_self _ _ _)) sub
  have hl : lookupCallable? f.contract (balanceDeltaCombineName sub) = some (balanceDeltaCombineFunction sub).toCallable := by
    rw [hf]; exact balanceDeltaCombine_lookup sub
  have he : evalExprs? config f evm [ea, eb] = .ok [.int (EVM.signed a), .int (EVM.signed b)] := by
    simp only [evalExprs?, ha, hb, bind, EvalResult.bind, pure]
  by_cases hfit : balanceDeltaCombineFits sub a b
  · rw [balanceDeltaCombineResult, if_pos hfit] at hr
    rw [if_pos hfit]
    exact internalCallFunctionReturn he hl (by cases sub <;> rfl) hr
  · rw [balanceDeltaCombineResult, if_neg hfit] at hr
    rw [if_neg hfit]
    exact internalCallFunctionRevert he hl (by cases sub <;> rfl) hr

end Benchmarks.UniswapV4PoolManager
