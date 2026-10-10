import Benchmarks.UniswapV4PoolManager.UnsignedRangeSource
import Benchmarks.UniswapV4PoolManager.CallComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev liquidityAddFunction : FunctionDecl := contract.functions[73]!
theorem liquidityAdd_lookup : lookupCallable? contract "LiquidityMath_addDelta" =
    some liquidityAddFunction.toCallable := rfl

abbrev liquidityAddFits (x : UInt256) (y : Int) : Prop :=
  unsignedFits ⟨128, by decide⟩ (Int.ofNat x.toNat+y)

theorem liquidityAddBody {f : Frame} {evm : EVM.State} {x : UInt256} {y : Int}
    (hx : f.locals.get? "x" = some (.int (Int.ofNat x.toNat)))
    (hy : f.locals.get? "y" = some (.int y)) :
    ∃ f', ExecFuncBody config f evm liquidityAddFunction.body
      (if liquidityAddFits x y then .returned f' evm (some [.int (Int.ofNat x.toNat+y)]) else .reverted) := by
  let f1 : Frame := {f with locals := f.locals.insert "z" (.int 0)}
  have hsum : evalExpr? config f1 evm (.binary .add (.var "x") (.var "y")) =
      .ok (.int (Int.ofNat x.toNat+y)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide),
      evalLocalValue ((store_get_ne _ _ (by decide : ("z" == "x") = false)).trans hx),
      evalLocalValue ((store_get_ne _ _ (by decide : ("z" == "y") = false)).trans hy)]
    rfl
  have hcheck := evalUnsignedRange ⟨128, by decide⟩ hsum
  have hz : ExecStmt config f evm liquidityAddFunction.body[0]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  by_cases hfit : liquidityAddFits x y
  · simp only [if_pos hfit] at hcheck ⊢
    exact ⟨_, .execBlockRet (ExecBlock.consNormal hz (ExecBlock.consNormal
      (ExecStmt.assign hcheck (assignLocalValue (store_get_self _ _ _)))
      (ABlock.start.returns (evalLocalValue (store_get_self _ _ _)))))⟩
  · simp only [if_neg hfit] at hcheck ⊢
    exact ⟨f1, .execBlockRevert (ExecBlock.consNormal hz (ExecBlock.consRevert
      (ExecStmt.assignExprRevert hcheck)))⟩

theorem liquidityAddCall {f : Frame} {evm : EVM.State} {ex ey : Expr} {x : UInt256} {y : Int}
    (hf : f.contract = contract) (hx : evalExpr? config f evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config f evm ey = .ok (.int y)) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "LiquidityMath_addDelta" [ex, ey] retVar)
      (if liquidityAddFits x y then
        .ok {f with locals := f.locals.insert retVar (.int (Int.ofNat x.toNat+y))} evm else .reverted) := by
  obtain ⟨f', hb⟩ := liquidityAddBody (f := {f with locals := (((∅ : Store).insert "y" (.int y)).insert
    "x" (.int (Int.ofNat x.toNat)))}) (evm := evm) (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("x" == "y") = false)).trans (store_get_self _ _ _))
  have hargs : evalExprs? config f evm [ex, ey] = .ok [.int (Int.ofNat x.toNat), .int y] := by
    simp only [evalExprs?, hx, hy, bind, EvalResult.bind, pure]
  have hlookup : lookupCallable? f.contract "LiquidityMath_addDelta" = some liquidityAddFunction.toCallable := by
    rw [hf]; exact liquidityAdd_lookup
  by_cases hfit : liquidityAddFits x y
  · rw [if_pos hfit] at hb ⊢
    exact internalCallFunctionReturn hargs hlookup rfl hb
  · rw [if_neg hfit] at hb ⊢
    exact internalCallFunctionRevert hargs hlookup rfl hb

end Benchmarks.UniswapV4PoolManager
