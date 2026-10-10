import Benchmarks.Morpho.MetaMorphoV1_1.MaxWithdrawConversionSource
import Benchmarks.Morpho.MetaMorphoV1_1.SimulateWithdrawFunction

/-! Calling the withdrawal simulation and returning the available assets and accrued totals. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

structure MaxWithdrawResultLocals (frame : Frame) (assets supply total ptr : UInt256) : Prop where
  assets : frame.locals.get? "assets" = some (uint256Value assets)
  supply : frame.locals.get? "newTotalSupply" = some (uint256Value supply)
  total : frame.locals.get? "newTotalAssets" = some (uint256Value total)
  cursor : frame.locals.get? cursorName = some (uint256Value ptr)

theorem MaxWithdrawResultLocals.reader {frame : Frame}
    {assets supply total ptr remaining cursor : UInt256}
    (h : MaxWithdrawResultLocals frame assets supply total ptr) :
    MaxWithdrawResultLocals (cursorResultFrame frame "__c4" (uint256Value remaining) cursor)
      assets supply total cursor := by
  refine ⟨?_, ?_, ?_, cursorResultFrame_cursor _ _ _ _⟩ <;>
    rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
  · exact h.assets
  · exact h.supply
  · exact h.total

theorem allocatedMaxWithdrawFunction_simulate :
    allocatedMaxWithdrawFunction.body.drop 14 =
      cursorCall allocatedSimulateWithdrawFunction.name [.var "assets"] "__c4" ++
        allocatedMaxWithdrawFunction.body.drop 17 := by decide +kernel

theorem allocatedMaxWithdrawFunction_return :
    allocatedMaxWithdrawFunction.body.drop 17 =
      [.assign .localVar ⟨"assets", []⟩ (.inRange (.uint ⟨256, by decide⟩)
        (.binary .sub (.var "assets") (.var "__c4"))),
        .return [.tupleLit [.var "assets", .var "newTotalSupply", .var "newTotalAssets"],
          .var cursorName]] := by decide +kernel

theorem maxWithdrawSimulateArgs {frame : Frame} {evm : State} {assets supply total ptr : UInt256}
    (h : MaxWithdrawResultLocals frame assets supply total ptr) :
    evalExprs? config frame evm [.var "assets", .var cursorName] =
      .ok [uint256Value assets, uint256Value ptr] := by
  simp only [evalExprs?, evalExpr?, h.assets, h.cursor,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem maxWithdrawSimulatePrefix (v : MetaMorphoV1_1Immutables)
    {locals : Store} {evm evm' : State} {final : Frame}
    {assets supply total ptr remaining cursor : UInt256} {outcome : ExecResult}
    (hl : MaxWithdrawResultLocals ⟨contract, locals, immStore v⟩ assets supply total ptr)
    (hbody : ExecFuncBody config (simulateWithdrawFrame (immStore v) assets ptr) evm
      allocatedSimulateWithdrawFunction.body
      (.returned final evm' [uint256Value remaining, uint256Value cursor]))
    (htail : ExecBlock config
      (cursorResultFrame ⟨contract, locals, immStore v⟩ "__c4" (uint256Value remaining) cursor)
      evm' (allocatedMaxWithdrawFunction.body.drop 17) outcome) :
    ExecBlock config ⟨contract, locals, immStore v⟩ evm
      (allocatedMaxWithdrawFunction.body.drop 14) outcome := by
  rw [allocatedMaxWithdrawFunction_simulate]
  exact cursorCallPrefix (by decide)
    (internalCallFunctionReturn (callee := allocatedSimulateWithdrawFunction)
      (maxWithdrawSimulateArgs hl) rfl rfl hbody) htail

theorem maxWithdrawSimulateReverts (v : MetaMorphoV1_1Immutables)
    {locals : Store} {evm : State} {assets supply total ptr : UInt256}
    (hl : MaxWithdrawResultLocals ⟨contract, locals, immStore v⟩ assets supply total ptr)
    (hbody : ExecFuncBody config (simulateWithdrawFrame (immStore v) assets ptr) evm
      allocatedSimulateWithdrawFunction.body .reverted) :
    ExecBlock config ⟨contract, locals, immStore v⟩ evm
      (allocatedMaxWithdrawFunction.body.drop 14) .reverted := by
  rw [allocatedMaxWithdrawFunction_simulate]
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (callee := allocatedSimulateWithdrawFunction) (maxWithdrawSimulateArgs hl) rfl rfl hbody)

theorem maxWithdrawReturnSource {frame : Frame} {evm : State}
    {assets supply total ptr remaining : UInt256}
    (hl : MaxWithdrawResultLocals frame assets supply total ptr)
    (hr : frame.locals.get? "__c4" = some (uint256Value remaining))
    (hfit : remaining.toNat ≤ assets.toNat) :
    ExecBlock config frame evm (allocatedMaxWithdrawFunction.body.drop 17)
      (.returned { frame with
        locals := frame.locals.insert "assets"
          (uint256Value (UInt256.sub assets remaining)) } evm
        [.tuple [uint256Value (UInt256.sub assets remaining), uint256Value supply,
          uint256Value total], uint256Value ptr]) := by
  rw [allocatedMaxWithdrawFunction_return]
  have hsub := evalExpr_uint256_sub
    (show evalExpr? config frame evm (.var "assets") = .ok (uint256Value assets) by
      simp only [evalExpr?, hl.assets, EvalResult.ofOption])
    (show evalExpr? config frame evm (.var "__c4") = .ok (uint256Value remaining) by
      simp only [evalExpr?, hr, EvalResult.ofOption]) hfit
  apply ExecBlock.consNormal (ExecStmt.assign hsub ?_)
  · apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, evalExpr?, evalExprList?, store_get_self,
      store_get_ne _ _ (by decide : ("assets" == "newTotalSupply") = false),
      store_get_ne _ _ (by decide : ("assets" == "newTotalAssets") = false),
      store_get_ne _ _ (by decide : ("assets" == cursorName) = false),
      hl.supply, hl.total, hl.cursor, EvalResult.ofOption, bind, EvalResult.bind, pure]
  · simp only [assignStorageRef?, hl.assets, updateLocalPath?, bind, EvalResult.bind, pure]

theorem maxWithdrawReturnReverts {frame : Frame} {evm : State}
    {assets supply total ptr remaining : UInt256}
    (hl : MaxWithdrawResultLocals frame assets supply total ptr)
    (hr : frame.locals.get? "__c4" = some (uint256Value remaining))
    (hbad : assets.toNat < remaining.toNat) :
    ExecBlock config frame evm (allocatedMaxWithdrawFunction.body.drop 17) .reverted := by
  rw [allocatedMaxWithdrawFunction_return]
  apply ExecBlock.consRevert (ExecStmt.assignExprRevert (checkedSubSourceUnderflow ?_ ?_ hbad))
  · simp only [evalExpr?, hl.assets, EvalResult.ofOption]
  · simp only [evalExpr?, hr, EvalResult.ofOption]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
