import Benchmarks.UniswapV4PoolManager.FullMathReduce
import Benchmarks.UniswapV4PoolManager.WordXorSource
import Benchmarks.UniswapV4PoolManager.CallComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem fullMathInverseStepSource {f : Frame} {evm : EVM.State} {d inv : UInt256}
    (hd : f.locals.get? "denominator" = some (.int (Int.ofNat d.toNat)))
    (hi : f.locals.get? "inv" = some (.int (Int.ofNat inv.toNat))) :
    ExecStmt config f evm fullMathFunction.body[17]!
      (.ok (wordLocal f "inv" (fullMathInverseStep d inv)) evm) := by
  have hd' := evalLocalValue (cfg := config) (f := f) (evm := evm) hd
  have hi' := evalLocalValue (cfg := config) (f := f) (evm := evm) hi
  have he := evalWordMul hi'
    (evalWordSub (x := ⟨2⟩)
      (show evalExpr? config f evm (.intLit 2) = .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) by
        simp only [evalExpr?, pure]; rfl)
      (evalWordMul hd' hi'))
  rw [u256_mul_comm inv] at he
  exact ExecStmt.assign he (assignLocalValue hi)

def fullMathInverseFrame (f : Frame) (d inv : UInt256) : Nat → Frame
  | 0 => f
  | n+1 => fullMathInverseFrame (wordLocal f "inv" (fullMathInverseStep d inv)) d
      (fullMathInverseStep d inv) n

theorem fullMathInverseFrame_get (f : Frame) (d inv : UInt256) (n : Nat) (name : Ident)
    (hn : ("inv" == name) = false) :
    (fullMathInverseFrame f d inv n).locals.get? name = f.locals.get? name := by
  induction n generalizing f inv with
  | zero => rfl
  | succ n ih =>
    rw [fullMathInverseFrame, ih, wordLocal_get, hn]
    rfl

theorem fullMathInverseFrame_inv {f : Frame} (d inv : UInt256) (n : Nat)
    (hi : f.locals.get? "inv" = some (.int (Int.ofNat inv.toNat))) :
    (fullMathInverseFrame f d inv n).locals.get? "inv" =
      some (.int (Int.ofNat (fullMathInverseIter d inv n).toNat)) := by
  induction n generalizing f inv with
  | zero => exact hi
  | succ n ih => exact ih _ (store_get_self _ _ _)

theorem fullMathInverseSteps {f : Frame} {evm : EVM.State} {d inv : UInt256}
    (hd : f.locals.get? "denominator" = some (.int (Int.ofNat d.toNat)))
    (hi : f.locals.get? "inv" = some (.int (Int.ofNat inv.toNat))) (n : Nat) :
    ExecBlock config f evm (List.replicate n fullMathFunction.body[17]!)
      (.ok (fullMathInverseFrame f d inv n) evm) := by
  induction n generalizing f inv with
  | zero => exact ExecBlock.nil
  | succ n ih =>
    exact ExecBlock.consNormal (fullMathInverseStepSource hd hi) (ih
      ((store_get_ne _ _ (by decide : ("inv" == "denominator") = false)).trans hd)
      (store_get_self _ _ _))

theorem fullMathInverseBody {f : Frame} {evm : EVM.State} {d w : UInt256} {old : Value}
    (hd : f.locals.get? "denominator" = some (.int (Int.ofNat d.toNat)))
    (hp : f.locals.get? "prod0" = some (.int (Int.ofNat w.toNat)))
    (hr : f.locals.get? "result" = some old) :
    ∃ f', ExecFuncBody config f evm (fullMathFunction.body.drop 16)
      (.returned f' evm (some [.int (Int.ofNat (UInt256.mul w (fullMathInverse d)).toNat)])) := by
  let inv := UInt256.xor (UInt256.mul ⟨3⟩ d) ⟨2⟩
  let f1 := wordLocal f "inv" inv
  let f7 := fullMathInverseFrame f1 d inv 6
  let result := UInt256.mul w (fullMathInverse d)
  have he := evalWordXor (evalWordMul (x := ⟨3⟩)
    (show evalExpr? config f evm (.intLit 3) = .ok (.int (Int.ofNat (⟨3⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)
    (evalLocalValue hd))
    (show evalExpr? config f evm (.intLit 2) = .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  have h16 : ExecStmt config f evm fullMathFunction.body[16]! (.ok f1 evm) := ExecStmt.letDecl he
  have hsteps := fullMathInverseSteps (f := f1) (evm := evm)
    ((store_get_ne _ _ (by decide : ("inv" == "denominator") = false)).trans hd)
    (store_get_self _ _ _) 6
  have hp7 : f7.locals.get? "prod0" = some (.int (Int.ofNat w.toNat)) :=
    (fullMathInverseFrame_get _ _ _ _ _ (by decide)).trans
      ((store_get_ne _ _ (by decide : ("inv" == "prod0") = false)).trans hp)
  have hr7 : f7.locals.get? "result" = some old :=
    (fullMathInverseFrame_get _ _ _ _ _ (by decide)).trans
      ((store_get_ne _ _ (by decide : ("inv" == "result") = false)).trans hr)
  have hi7 : f7.locals.get? "inv" = some (.int (Int.ofNat (fullMathInverse d).toNat)) :=
    fullMathInverseFrame_inv d inv 6 (store_get_self _ _ _)
  have h23 : ExecStmt config f7 evm fullMathFunction.body[23]! (.ok (wordLocal f7 "result" result) evm) :=
    ExecStmt.assign (evalWordMul (evalLocalValue hp7) (evalLocalValue hi7)) (assignLocalValue hr7)
  refine ⟨wordLocal f7 "result" result, ExecFuncBody.execBlockRet (ExecBlock.consNormal h16 ?_)⟩
  exact execBlock_append hsteps (ExecBlock.consNormal h23 (ABlock.start.returns wordLocal_eval))

end Benchmarks.UniswapV4PoolManager
