import Benchmarks.CompoundIII.Comet.CollateralCheckModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem pricePositive_bounds {price : UInt256} (hp : 0 < signedPrice price) :
    0 < price.toNat ∧ price.toNat < 2^255 := by
  have hw : price.toNat < 2^256 := price.val.isLt
  unfold signedPrice at hp
  split_ifs at hp with hs
  · simp only [Int.ofNat_eq_natCast] at hp
    exact ⟨by omega, hs⟩
  · simp only [Int.ofNat_eq_natCast] at hp
    norm_num at hp
    omega

def CollateralCheckSourceResult (frame : Frame) (evm : EVM.State) (body : List Stmt)
    (result : Option (EVM.State × Bool)) : Prop :=
  match result with
  | none => ExecBlock config frame evm body .reverted
  | some (evm', value) => ∃ final, ExecBlock config frame evm body
      (.returned final evm' (some [.bool value]))

theorem collateralBasePriceFeed_eval (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) (basic magnitude : UInt256) (evm : EVM.State) :
    evalExpr? config (collateralPresentFrame v account basic magnitude) evm
      (.immutable "baseTokenPriceFeed") = .ok (.address v.baseTokenPriceFeed) := by
  simp only [evalExpr?, collateralPresentFrame, collateralBitsFrame, collateralPrincipalFrame,
    collateralCheckEntry, immStore_get_baseTokenPriceFeed, EvalResult.ofOption]

theorem collateralDebtPrice_call (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) (basic magnitude price : UInt256) (evm : EVM.State)
    (hp : price.toNat < 2^255) :
    ExecStmt config (collateralBasePriceFrame v account basic magnitude price) evm
      (.internalCall "signedMulPrice" [.var "__c0", .var "__c1",
        .cast (.immutable "baseScale") (.elem (.int (.uint ⟨64, by decide⟩)))] "liquidity")
      (if signedDebtPriceValid magnitude price (collateralBaseScale v) then
        .ok (collateralLiquidityFrame v account basic magnitude price) evm else .reverted) := by
  apply signedMulPrice_call _ evm magnitude price (collateralBaseScale v) _ _ _ "liquidity"
    rfl hp (uintCastWord_lt _ _)
  · simp only [evalExpr?, collateralBasePriceFrame, collateralPresentFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  · simp only [evalExpr?, collateralBasePriceFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  · apply uintCastWord_source
    simp only [evalExpr?, collateralBasePriceFrame, collateralPresentFrame, collateralBitsFrame,
      collateralPrincipalFrame, collateralCheckEntry, immStore_get_baseScale, EvalResult.ofOption]

theorem collateralInitialFrame_spec (v : CometWithExtendedAssetListImmutables)
    (account : AccountAddress) (basic magnitude price : UInt256)
    (hm : signedDebtPriceValid magnitude price (collateralBaseScale v)) :
    CollateralLoopFrame v account (userBasicFieldWord basic 2) (userBasicFieldWord basic 3) 0
      (signedDebtPriceWord magnitude price (collateralBaseScale v))
      (collateralInitialFrame v account basic magnitude price) := by
  dsimp only [collateralInitialFrame, collateralLiquidityFrame, collateralBasePriceFrame,
    collateralPresentFrame, collateralBitsFrame, collateralPrincipalFrame, collateralCheckEntry]
  constructor
  · rfl
  · rfl
  · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  · rw [signedDebtPriceWord_int hm.1]
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  · simp

theorem collateralDebt_source {v : CometWithExtendedAssetListImmutables} {borrow : Bool}
    {account : AccountAddress} {basic magnitude : UInt256} {evm : EVM.State}
    {result : Option (EVM.State × Bool)}
    (ht : CollateralDebtTrace v borrow account basic magnitude evm result) :
    CollateralCheckSourceResult (collateralPresentFrame v account basic magnitude) evm
      (collateralDebtTail borrow) result := by
  have hf := collateralBasePriceFeed_eval v account basic magnitude evm
  cases ht with
  | @priceFailed evm' z out hc hh hv =>
      exact ExecBlock.consRevert (price_call_revert
        (collateralPresentFrame v account basic magnitude) evm evm' _ _ "__c1" out z
        rfl hf hc hh hv)
  | @mathFailed evm' out hc hh hv hm =>
      have hp := price_call_ok (collateralPresentFrame v account basic magnitude)
        evm evm' _ _ "__c1" out rfl hf hc hh hv
      have hmath := collateralDebtPrice_call v account basic magnitude (calldataWord out 32)
        evm' (pricePositive_bounds hv.2.2).2
      rw [if_neg hm] at hmath
      exact ExecBlock.consNormal hp (ExecBlock.consRevert hmath)
  | @loop evm' out result hc hh hv hm ht =>
      have hp := price_call_ok (collateralPresentFrame v account basic magnitude)
        evm evm' _ _ "__c1" out rfl hf hc hh hv
      have hmath := collateralDebtPrice_call v account basic magnitude (calldataWord out 32)
        evm' (pricePositive_bounds hv.2.2).2
      rw [if_pos hm] at hmath
      have hloop := collateralLoop_source ht (packedUint_lt basic _ (by decide))
        (packedUint_lt basic _ (by decide)) _
        (collateralInitialFrame_spec v account basic magnitude (calldataWord out 32) hm)
      have hinit : ExecStmt config (collateralLiquidityFrame v account basic magnitude
          (calldataWord out 32)) evm'
          (.letDecl "i" (some (.elem (.int (.uint ⟨8, by decide⟩)))) (.intLit 0))
          (.ok (collateralInitialFrame v account basic magnitude (calldataWord out 32)) evm') :=
        ExecStmt.letDecl (by simp only [evalExpr?, pure])
      cases result with
      | none =>
          exact ExecBlock.consNormal hp (ExecBlock.consNormal hmath
            (ExecBlock.consNormal hinit hloop))
      | some r =>
          obtain ⟨evm'', value⟩ := r
          obtain ⟨final, hloop⟩ := hloop
          exact ⟨final, ExecBlock.consNormal hp (ExecBlock.consNormal hmath
            (ExecBlock.consNormal hinit hloop))⟩

end Benchmarks.CompoundIII.Comet
