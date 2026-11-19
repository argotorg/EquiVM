import Benchmarks.Midnight.LiquidateAmountsGuard
import Benchmarks.Midnight.ToUint128Source
import Benchmarks.Midnight.CollateralSourceState
import Benchmarks.Midnight.NamedCollateralSource

/-! Source conversion, subtraction, and storage assignment for seized collateral. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def liquidateCollateralUpdateBody : List Stmt := (liquidateAmountsBody.drop 6).take 3

def liquidateCollateralUpdateFrame (frame : Frame) (seized value : UInt256) : Frame :=
  wordLocal (wordLocal frame "__c27" seized) "newCollateral" value

theorem liquidateCollateralUpdateSource {frame : Frame} {evm : State} {m : MarketData}
    {id index seized repaid borrower mode : UInt256} {receiver callback : AccountAddress}
    {data : ByteArray}
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (hcanon : borrower.toNat < EVM.addressModulus) :
    let old := collateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
      id borrower index
    let safe := index.toNat < 128 ∧ seized.toNat < 2^128 ∧ seized.toNat ≤ old.toNat
    (¬ safe ∧ ExecBlock config frame evm liquidateCollateralUpdateBody .reverted) ∨
    (safe ∧ evm.executionEnv.perm = false ∧
      ExecBlock config frame evm liquidateCollateralUpdateBody .staticViolation) ∨
    (safe ∧ evm.executionEnv.perm = true ∧
      ExecBlock config frame evm liquidateCollateralUpdateBody
        (.ok (liquidateCollateralUpdateFrame frame seized (UInt256.sub old seized))
          (collateralWriteState evm id borrower index (UInt256.sub old seized)))) := by
  dsimp only
  let old := collateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
    id borrower index
  let f1 := wordLocal frame "__c27" seized
  have hf1 : LiquidateSourceFrame f1 m id index seized repaid borrower mode receiver callback data :=
    hf.insert "__c27" (.int seized.toNat) (by decide)
  have hc1 : f1.locals.get? "__c27" = some (.int seized.toNat) := wordLocal_get _ _ _
  have ha0 : evalExprs? config frame evm [.var "seizedAssets"] = .ok [.int seized.toNat] := by
    simp only [evalExprs?, evalWordLocal hf.seized, bind, pure, EvalResult.bind]
  by_cases h128 : seized.toNat < 2^128
  · have hx0 := callToUint128 (name := "__c27") hf.contract ha0 h128
    by_cases hidx : index.toNat < 128
    · have hr : evalExpr? config f1 evm (positionCollateralExpr "collateralIndex") =
          .ok (.int old.toNat) :=
        evalPositionCollateral "collateralIndex" hf1.contract hcanon hf1.position hf1.index hidx
      by_cases hle : seized.toNat ≤ old.toNat
      · have hx1 : ExecStmt config f1 evm (liquidateAmountsBody[7]!)
            (.ok (wordLocal f1 "newCollateral" (UInt256.sub old seized)) evm) :=
          ExecStmt.letDecl (evalCheckedSub128 hr (evalWordLocal hc1) (low128_lt _) hle)
        let value := UInt256.sub old seized
        let f2 := liquidateCollateralUpdateFrame frame seized value
        have hf2 : LiquidateSourceFrame f2 m id index seized repaid borrower mode
            receiver callback data := hf1.insert "newCollateral" (.int value.toNat) (by decide)
        have hw : assignStorageRef? config f2 evm .storage
            { base := "_position", steps := [.field "collateral", .aindex (.var "collateralIndex")] }
            (.int value.toNat) = .ok (f2, collateralWriteState evm id borrower index value) :=
          assignPositionCollateral "collateralIndex" hf2.contract hcanon hf2.position hf2.index
            hidx (storageLocStore_collateral evm id borrower index value)
        by_cases hp : evm.executionEnv.perm = true
        · exact Or.inr (Or.inr ⟨⟨hidx, h128, hle⟩, hp, ExecBlock.consNormal hx0
            (ExecBlock.consNormal hx1 (ExecBlock.consNormal
              (ExecStmt.assign (Or.inr hp) (evalWordLocal (wordLocal_get ..)) hw) ExecBlock.nil))⟩)
        · exact Or.inr (Or.inl ⟨⟨hidx, h128, hle⟩, Bool.eq_false_iff.mpr hp,
            ExecBlock.consNormal hx0 (ExecBlock.consNormal hx1 (ExecBlock.consStatic
              (ExecStmt.assignStatic (evalWordLocal (wordLocal_get ..)) hw
                (Bool.eq_false_iff.mpr hp))))⟩)
      · exact Or.inl ⟨fun h ↦ hle h.2.2, ExecBlock.consNormal hx0
          (ExecBlock.consRevert (ExecStmt.letDeclRevert
            (evalCheckedSubUnderflow ⟨128, by decide⟩ hr (evalWordLocal hc1)
              (Nat.lt_of_not_ge hle))))⟩
    · refine Or.inl ⟨fun h ↦ hidx h.1, ExecBlock.consNormal hx0
        (ExecBlock.consRevert (ExecStmt.letDeclRevert ?_))⟩
      change evalExpr? config f1 evm (.inRange packedUInt128Int
        (.binary .sub (positionCollateralExpr "collateralIndex") (.var "__c27"))) = .revert
      rw [evalExpr?, evalExpr_binary_nonshort (by decide) (by decide),
        evalPositionCollateralRevert "collateralIndex" hf1.contract hf1.position hf1.index hidx]
      rfl
  · exact Or.inl ⟨fun h ↦ h128 h.2.1, ExecBlock.consRevert
      (callToUint128Revert hf.contract ha0 (Nat.le_of_not_gt h128))⟩

end Benchmarks.Midnight
