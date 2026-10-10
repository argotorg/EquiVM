import Benchmarks.CompoundIII.Comet.BuyCollateralModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

structure BuyCollateralArgs (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (asset recipient : AccountAddress) (minimum base : UInt256) : Prop where
  contract : frame.contract = Comet.contract
  immutables : frame.immutables = immStore v
  asset : frame.locals.get? "asset" = some (.address asset)
  recipient : frame.locals.get? "recipient" = some (.address recipient)
  minimum : frame.locals.get? "minAmount" = some (.int minimum.toNat)
  base : frame.locals.get? "baseAmount" = some (.int base.toNat)

theorem BuyCollateralArgs.insert {frame v asset recipient minimum base}
    (hf : BuyCollateralArgs frame v asset recipient minimum base) (name : Ident) (value : Value)
    (hn : name ∉ ["asset", "recipient", "minAmount", "baseAmount"]) :
    BuyCollateralArgs { frame with locals := frame.locals.insert name value }
      v asset recipient minimum base := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  refine ⟨hf.contract, hf.immutables, ?_, ?_, ?_, ?_⟩
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.1, Ne.symm hn.1]
      using hf.asset
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.1, Ne.symm hn.2.1]
      using hf.recipient
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.1, Ne.symm hn.2.2.1]
      using hf.minimum
  · simpa [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn.2.2.2, Ne.symm hn.2.2.2]
      using hf.base

theorem BuyCollateralArgs.setBase {frame v asset recipient minimum base}
    (hf : BuyCollateralArgs frame v asset recipient minimum base) (received : UInt256) :
    BuyCollateralArgs { frame with locals := frame.locals.insert "baseAmount" (.int received.toNat) }
      v asset recipient minimum received := by
  refine ⟨hf.contract, hf.immutables, ?_, ?_, ?_, ?_⟩
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hf.asset
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hf.recipient
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hf.minimum
  · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl

theorem BuyCollateralArgs.evalAsset {frame v asset recipient minimum base}
    (hf : BuyCollateralArgs frame v asset recipient minimum base) (evm : EVM.State) :
    evalExpr? config frame evm (.var "asset") = .ok (.address asset) := by
  simp only [evalExpr?, hf.asset, EvalResult.ofOption]

theorem BuyCollateralArgs.evalRecipient {frame v asset recipient minimum base}
    (hf : BuyCollateralArgs frame v asset recipient minimum base) (evm : EVM.State) :
    evalExpr? config frame evm (.var "recipient") = .ok (.address recipient) := by
  simp only [evalExpr?, hf.recipient, EvalResult.ofOption]

theorem BuyCollateralArgs.evalBase {frame v asset recipient minimum base}
    (hf : BuyCollateralArgs frame v asset recipient minimum base) (evm : EVM.State) :
    evalExpr? config frame evm (.var "baseAmount") = .ok (.int base.toNat) := by
  simp only [evalExpr?, hf.base, EvalResult.ofOption]

theorem buyCollateralForSale_eval {v : CometWithExtendedAssetListImmutables}
    {frame : Frame} {evm : EVM.State} {reserves : UInt256}
    (hi : frame.immutables = immStore v)
    (hr : frame.locals.get? "reserves" = some (.int (signedWord reserves))) :
    evalExpr? config frame evm buyCollateralForSaleExpr =
      .ok (.bool (decide (BuyCollateralForSale v reserves))) := by
  have he : evalExpr? config frame evm (.var "reserves") =
      .ok (.int (signedWord reserves)) := by simp only [evalExpr?, hr, EvalResult.ofOption]
  have hc : evalExpr? config frame evm
      (.cast (.var "reserves") (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int reserves.toNat) := by
    have hcast := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩) he
    change evalExpr? config frame evm _ = .ok (.int (signedWord reserves % (2^256 : Int)))
      at hcast
    rw [signedWord_mod] at hcast
    exact hcast
  have ht : evalExpr? config frame evm (.immutable "targetReserves") =
      .ok (.int v.targetReserves.toNat) := by
    cases frame
    subst_vars
    exact evalImmutable_targetReserves config _ _ evm v
  simp only [buyCollateralForSaleExpr, evalExpr?, he, hc, ht, pure, bind, EvalResult.bind,
    evalBinaryOp?, evalUnaryOp?, BuyCollateralForSale]
  by_cases hz : 0 ≤ signedWord reserves <;> simp [hz, EvalResult.ofOption]
  exact Bool.eq_iff_iff.mpr (by simp)

end Benchmarks.CompoundIII.Comet
