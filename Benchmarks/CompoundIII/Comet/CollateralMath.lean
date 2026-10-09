import Benchmarks.CompoundIII.Comet.AssetSource
import Benchmarks.CompoundIII.Comet.MulPrice
import Benchmarks.CompoundIII.Comet.Signed256

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def collateralFactorOffset (borrow : Bool) : Nat := if borrow then 128 else 160

def collateralFactorName (borrow : Bool) : Ident :=
  if borrow then "borrowCollateralFactor" else "liquidateCollateralFactor"

def collateralValueWord (borrow : Bool) (amount price : UInt256) (out : ByteArray) : UInt256 :=
  mulFactorWord (mulPriceWord amount price (calldataWord out 96))
    (calldataWord out (collateralFactorOffset borrow))

def CollateralMathValid (borrow : Bool) (amount price : UInt256) (out : ByteArray) : Prop :=
  MulPriceValid amount price (calldataWord out 96) ∧
    (mulPriceWord amount price (calldataWord out 96)).toNat *
      (calldataWord out (collateralFactorOffset borrow)).toNat < UInt256.size ∧
    (collateralValueWord borrow amount price out).toNat < 2^255

instance (borrow : Bool) (amount price : UInt256) (out : ByteArray) :
    Decidable (CollateralMathValid borrow amount price out) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def collateralMathBlock (borrow : Bool) : List Stmt :=
  [.internalCall "mulPrice"
      [.var "collateralBalance", .var "__c5", .field (.var "asset") "scale"] "newAmount",
    .internalCall "mulFactor"
      [.var "newAmount", .field (.var "asset") (collateralFactorName borrow)] "__c7",
    .internalCall "signed256" [.var "__c7"] "__c8"]

def collateralMathFinal (frame : Frame) (borrow : Bool) (amount price : UInt256)
    (out : ByteArray) : Frame :=
  { frame with
    locals := ((frame.locals.insert "newAmount"
      (.int (mulPriceWord amount price (calldataWord out 96)).toNat)).insert
      "__c7" (.int (collateralValueWord borrow amount price out).toNat)).insert
      "__c8" (.int (collateralValueWord borrow amount price out).toNat) }

theorem collateralFactor_source (frame : Frame) (evm : EVM.State) (borrow : Bool)
    (out : ByteArray) (ha : frame.locals.get? "asset" = some (assetValue out)) :
    evalExpr? config frame evm (.field (.var "asset") (collateralFactorName borrow)) =
      .ok (.int (calldataWord out (collateralFactorOffset borrow)).toNat) := by
  cases borrow <;>
    simp only [collateralFactorName, collateralFactorOffset, Bool.false_eq_true, if_false,
      if_true, evalExpr?, ha, EvalResult.ofOption, bind, EvalResult.bind] <;> rfl

theorem collateralMath_source (frame : Frame) (evm : EVM.State) (borrow : Bool)
    (amount price : UInt256) (out : ByteArray) (hc : frame.contract = contract)
    (ha : frame.locals.get? "asset" = some (assetValue out))
    (hn : evalExpr? config frame evm (.var "collateralBalance") = .ok (.int amount.toNat))
    (hp : evalExpr? config frame evm (.var "__c5") = .ok (.int price.toNat)) :
    ExecBlock config frame evm (collateralMathBlock borrow)
      (if CollateralMathValid borrow amount price out then
        .ok (collateralMathFinal frame borrow amount price out) evm else .reverted) := by
  let n := mulPriceWord amount price (calldataWord out 96)
  let factor := calldataWord out (collateralFactorOffset borrow)
  let val := collateralValueWord borrow amount price out
  let f1 : Frame := { frame with locals := frame.locals.insert "newAmount" (.int n.toNat) }
  let f2 : Frame := { f1 with locals := f1.locals.insert "__c7" (.int val.toNat) }
  have hs : evalExpr? config frame evm (.field (.var "asset") "scale") =
      .ok (.int (calldataWord out 96).toNat) := by
    simp only [evalExpr?, ha, EvalResult.ofOption, bind, EvalResult.bind]
    rfl
  have hc1 := mulPrice_call frame evm amount price (calldataWord out 96) _ _ _ "newAmount"
    hc hn hp hs
  by_cases hv1 : MulPriceValid amount price (calldataWord out 96)
  · rw [if_pos hv1] at hc1
    apply ExecBlock.consNormal hc1
    have hn1 : evalExpr? config f1 evm (.var "newAmount") = .ok (.int n.toNat) := by
      simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]
      rfl
    have ha1 : f1.locals.get? "asset" = some (assetValue out) := by
      simpa [f1, Std.HashMap.getElem?_insert] using ha
    have hf := collateralFactor_source f1 evm borrow out ha1
    by_cases hv2 : n.toNat * factor.toNat < UInt256.size
    · apply ExecBlock.consNormal (mulFactor_call_ok f1 evm n factor _ _ "__c7" hc hn1 hf hv2)
      have hv : evalExpr? config f2 evm (.var "__c7") = .ok (.int val.toNat) := by
        simp only [evalExpr?, f2, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          EvalResult.ofOption]
        rfl
      by_cases hv3 : val.toNat < 2^255
      · rw [if_pos (show CollateralMathValid borrow amount price out from ⟨hv1, hv2, hv3⟩)]
        exact ExecBlock.consNormal (signed256_call_ok f2 evm val _ "__c8" hc hv hv3) .nil
      · rw [if_neg (fun h : CollateralMathValid borrow amount price out ↦ hv3 h.2.2)]
        exact ExecBlock.consRevert (signed256_call_revert f2 evm val _ "__c8" hc hv hv3)
    · rw [if_neg (fun h : CollateralMathValid borrow amount price out ↦ hv2 h.2.1)]
      exact ExecBlock.consRevert (mulFactor_call_revert f1 evm n factor _ _ "__c7" hc hn1 hf hv2)
  · rw [if_neg hv1] at hc1
    rw [if_neg (fun h : CollateralMathValid borrow amount price out ↦ hv1 h.1)]
    exact ExecBlock.consRevert hc1

end Benchmarks.CompoundIII.Comet
