import Benchmarks.CompoundIII.Comet.ApprovePayload

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem approveCall_source {frame : Frame} {evm evm' : EVM.State}
    {asset manager : AccountAddress} {amount : UInt256} {out : ByteArray} {z : Bool}
    {assetExpr managerExpr amountExpr : Expr} {ret : Ident}
    (ha : evalExpr? config frame evm assetExpr = .ok (.address asset))
    (hm : evalExpr? config frame evm managerExpr = .ok (.address manager))
    (hn : evalExpr? config frame evm amountExpr = .ok (.int amount.toNat))
    (hc : callViaEVM fork evm asset 0 (approvePayload manager amount) (z, evm', out)) :
    ExecStmt fork config frame evm
      (.externalCall assetExpr "approve" (.intLit 0) [managerExpr, amountExpr] ret)
      (if z then .ok { frame with locals := frame.locals.insert ret .unit } evm'
        else .reverted) := by
  have ht : typedCallViaEVM fork config evm (EVM.address asset) "approve" 0
      [.address manager, .int amount.toNat] (z, evm', out) := by
    rw [addressOfAddress]
    exact ⟨_, approvePayload_encode manager amount, hc⟩
  have he : evalExprs? config frame evm [managerExpr, amountExpr] =
      .ok [.address manager, .int amount.toNat] := by
    simp only [evalExprs?, hm, hn, bind, EvalResult.bind, pure]
  cases z with
  | false => exact ExecStmt.externalCallFailure (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) ha (by simp only [evalExpr?, pure]) he ht
  | true => exact ExecStmt.externalCallSuccess (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) ha (by simp only [evalExpr?, pure]) he ht rfl

end Benchmarks.CompoundIII.Comet
