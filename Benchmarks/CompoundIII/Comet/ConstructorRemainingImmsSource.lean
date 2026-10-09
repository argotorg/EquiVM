import Benchmarks.CompoundIII.Comet.ConstructorScaleSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem constructorSourceDivNat {frame : Frame} {evm : EVM.State} {e : Expr} {n d : Nat}
    (he : evalExpr? config frame evm e = .ok (.int (Int.ofNat n))) (hd : d ≠ 0) :
    evalExpr? config frame evm (.binary .div e (.intLit (Int.ofNat d))) =
      .ok (.int (Int.ofNat (n / d))) := by
  simp [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?, hd]

theorem constructorSourceAssetCount {c : ConstructorConfig} {frame : Frame} {evm : EVM.State}
    (hl : frame.locals.get? "config" = some (constructorConfigValue c)) :
    evalExpr? config frame evm (.arrayLength .localVar ⟨"config", [.field "assetConfigs"]⟩) =
      .ok (.int (Int.ofNat c.assetConfigs.length)) := by
  have hfield : lookupField? (constructorConfigValue c) "assetConfigs" =
      some (.array (c.assetConfigs.map ConstructorAsset.value)) := rfl
  have hpath : readLocalPath? config frame evm (constructorConfigValue c) [.field "assetConfigs"] =
      .ok (.array (c.assetConfigs.map ConstructorAsset.value)) := by
    simp only [readLocalPath?, hfield, EvalResult.ofOption, bind, EvalResult.bind, pure]
  simp only [evalExpr?, hl, pure, bind, EvalResult.bind]
  change (show EvalResult Value from do
    let v ← readLocalPath? config frame evm (constructorConfigValue c) [.field "assetConfigs"]
    match v with
    | .array vs => pure (.int vs.length)
    | .bytes b => pure (.int (Int.ofNat b.size))
    | .fixedBytes n _ => pure (.int (fixedBytesSize n))
    | _ => .error .typeError) = _
  rw [hpath]
  simp only [bind, EvalResult.bind, pure, List.length_map, Int.ofNat_eq_natCast]

def constructorRemainingImms (c : ConstructorConfig) (w : UInt256) : Store :=
  let imms := (constructorScaleImms c w).insert "accrualDescaleFactor"
    (.int (Int.ofNat (10^w.toNat / 1000000)))
  let imms := imms.insert "baseMinForRewards" (.int (Int.ofNat c.baseMinForRewards.val))
  let imms := imms.insert "baseTrackingSupplySpeed" (.int (Int.ofNat c.baseTrackingSupplySpeed.val))
  let imms := imms.insert "baseTrackingBorrowSpeed" (.int (Int.ofNat c.baseTrackingBorrowSpeed.val))
  let imms := imms.insert "baseBorrowMin" (.int (Int.ofNat c.baseBorrowMin.val))
  let imms := imms.insert "targetReserves" (.int (Int.ofNat c.targetReserves.val))
  let imms := imms.insert "supplyKink" (.int (Int.ofNat c.supplyKink.val))
  let imms := imms.insert "supplyPerSecondInterestRateSlopeLow"
    (.int (Int.ofNat (c.supplyPerYearInterestRateSlopeLow.val / 31536000)))
  let imms := imms.insert "supplyPerSecondInterestRateSlopeHigh"
    (.int (Int.ofNat (c.supplyPerYearInterestRateSlopeHigh.val / 31536000)))
  let imms := imms.insert "supplyPerSecondInterestRateBase"
    (.int (Int.ofNat (c.supplyPerYearInterestRateBase.val / 31536000)))
  let imms := imms.insert "borrowKink" (.int (Int.ofNat c.borrowKink.val))
  let imms := imms.insert "borrowPerSecondInterestRateSlopeLow"
    (.int (Int.ofNat (c.borrowPerYearInterestRateSlopeLow.val / 31536000)))
  let imms := imms.insert "borrowPerSecondInterestRateSlopeHigh"
    (.int (Int.ofNat (c.borrowPerYearInterestRateSlopeHigh.val / 31536000)))
  let imms := imms.insert "borrowPerSecondInterestRateBase"
    (.int (Int.ofNat (c.borrowPerYearInterestRateBase.val / 31536000)))
  imms.insert "numAssets" (.int (Int.ofNat c.assetConfigs.length))

def constructorSourceRemainingImms (c : ConstructorConfig) (w feed : UInt256) : Frame :=
  { constructorSourceScale c w feed with immutables := constructorRemainingImms c w }

theorem constructorSourceRemainingImms_exec {c : ConstructorConfig} {w feed : UInt256}
    {evm evm' : EVM.State} (hw : w.toNat ≤ 18) (hn : c.assetConfigs.length ≤ 24)
    (hp : ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 19)
      (.ok (constructorSourceScale c w feed) evm')) :
    ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 34)
      (.ok (constructorSourceRemainingImms c w feed) evm') := by
  change ExecBlock config _ _ (contract.ctor.body.take 19 ++
    [.setImmutable "accrualDescaleFactor" (.binary .div (.immutable "baseScale") (.intLit 1000000)),
      .setImmutable "baseMinForRewards" (.field (.var "config") "baseMinForRewards"),
      .setImmutable "baseTrackingSupplySpeed" (.field (.var "config") "baseTrackingSupplySpeed"),
      .setImmutable "baseTrackingBorrowSpeed" (.field (.var "config") "baseTrackingBorrowSpeed"),
      .setImmutable "baseBorrowMin" (.field (.var "config") "baseBorrowMin"),
      .setImmutable "targetReserves" (.field (.var "config") "targetReserves"),
      .setImmutable "supplyKink" (.field (.var "config") "supplyKink"),
      .setImmutable "supplyPerSecondInterestRateSlopeLow" (.binary .div
        (.field (.var "config") "supplyPerYearInterestRateSlopeLow") (.intLit 31536000)),
      .setImmutable "supplyPerSecondInterestRateSlopeHigh" (.binary .div
        (.field (.var "config") "supplyPerYearInterestRateSlopeHigh") (.intLit 31536000)),
      .setImmutable "supplyPerSecondInterestRateBase" (.binary .div
        (.field (.var "config") "supplyPerYearInterestRateBase") (.intLit 31536000)),
      .setImmutable "borrowKink" (.field (.var "config") "borrowKink"),
      .setImmutable "borrowPerSecondInterestRateSlopeLow" (.binary .div
        (.field (.var "config") "borrowPerYearInterestRateSlopeLow") (.intLit 31536000)),
      .setImmutable "borrowPerSecondInterestRateSlopeHigh" (.binary .div
        (.field (.var "config") "borrowPerYearInterestRateSlopeHigh") (.intLit 31536000)),
      .setImmutable "borrowPerSecondInterestRateBase" (.binary .div
        (.field (.var "config") "borrowPerYearInterestRateBase") (.intLit 31536000)),
      .setImmutable "numAssets" (.cast
        (.arrayLength .localVar ⟨"config", [.field "assetConfigs"]⟩)
        (.elem (.int (.uint ⟨8, by decide⟩))))]) _
  apply execBlockAppendOk hp
  have hl : (constructorSourceScale c w feed).locals.get? "config" =
      some (constructorConfigValue c) := by
    simp only [constructorSourceScale, constructorSourceInitialImms, constructorSourcePriceFeed,
      constructorSourceDecimals, constructorSourceConfig, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
    rfl
  have fits {n : Nat} (hb : n < 2^256) :
      elemValueFits (.int (.uint ⟨256, by decide⟩)) (.int (Int.ofNat n)) = true := by
    simp only [elemValueFits, decide_eq_true_eq]
    exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hb⟩
  have fits64 (n : Fin (2^64)) := fits (lt_trans n.isLt (by decide : (2 : Nat)^64 < 2^256))
  have fits104 (n : Fin (2^104)) := fits (lt_trans n.isLt (by decide : (2 : Nat)^104 < 2^256))
  have fitsRate (n : Fin (2^64)) := fits (lt_of_le_of_lt (Nat.div_le_self n.val 31536000)
    (lt_trans n.isLt (by decide : (2 : Nat)^64 < 2^256)))
  refine ExecBlock.consNormal (ExecStmt.setImmutable
    (value := .int (Int.ofNat (10^w.toNat / 1000000)))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl (fits (lt_of_le_of_lt (Nat.div_le_self _ _)
      (lt_trans (constructorScale_bound hw) (by decide : (2 : Nat)^64 < 2^256))))) ?_
  · apply constructorSourceDivNat ?_ (by decide)
    simp only [evalExpr?, constructorSourceScale, constructorScaleImms,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  refine ExecBlock.consNormal (ExecStmt.setImmutable
    (value := .int (Int.ofNat c.baseMinForRewards.val))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl (fits104 c.baseMinForRewards)) ?_
  · exact constructorSourceField hl rfl
  dsimp only
  refine ExecBlock.consNormal (ExecStmt.setImmutable
    (value := .int (Int.ofNat c.baseTrackingSupplySpeed.val))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl (fits64 c.baseTrackingSupplySpeed)) ?_
  · exact constructorSourceField hl rfl
  dsimp only
  refine ExecBlock.consNormal (ExecStmt.setImmutable
    (value := .int (Int.ofNat c.baseTrackingBorrowSpeed.val))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl (fits64 c.baseTrackingBorrowSpeed)) ?_
  · exact constructorSourceField hl rfl
  dsimp only
  refine ExecBlock.consNormal (ExecStmt.setImmutable (value := .int (Int.ofNat c.baseBorrowMin.val))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl (fits104 c.baseBorrowMin)) ?_
  · exact constructorSourceField hl rfl
  dsimp only
  refine ExecBlock.consNormal (ExecStmt.setImmutable
    (value := .int (Int.ofNat c.targetReserves.val))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl (fits104 c.targetReserves)) ?_
  · exact constructorSourceField hl rfl
  dsimp only
  refine ExecBlock.consNormal (ExecStmt.setImmutable (value := .int (Int.ofNat c.supplyKink.val))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl (fits64 c.supplyKink)) ?_
  · exact constructorSourceField hl rfl
  dsimp only
  refine ExecBlock.consNormal (ExecStmt.setImmutable
    (value := .int (Int.ofNat (c.supplyPerYearInterestRateSlopeLow.val / 31536000)))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl (fitsRate c.supplyPerYearInterestRateSlopeLow)) ?_
  · exact constructorSourceDivNat (constructorSourceField hl rfl) (by decide)
  dsimp only
  refine ExecBlock.consNormal (ExecStmt.setImmutable
    (value := .int (Int.ofNat (c.supplyPerYearInterestRateSlopeHigh.val / 31536000)))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl (fitsRate c.supplyPerYearInterestRateSlopeHigh)) ?_
  · exact constructorSourceDivNat (constructorSourceField hl rfl) (by decide)
  dsimp only
  refine ExecBlock.consNormal (ExecStmt.setImmutable
    (value := .int (Int.ofNat (c.supplyPerYearInterestRateBase.val / 31536000)))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl (fitsRate c.supplyPerYearInterestRateBase)) ?_
  · exact constructorSourceDivNat (constructorSourceField hl rfl) (by decide)
  dsimp only
  refine ExecBlock.consNormal (ExecStmt.setImmutable (value := .int (Int.ofNat c.borrowKink.val))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl (fits64 c.borrowKink)) ?_
  · exact constructorSourceField hl rfl
  dsimp only
  refine ExecBlock.consNormal (ExecStmt.setImmutable
    (value := .int (Int.ofNat (c.borrowPerYearInterestRateSlopeLow.val / 31536000)))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl (fitsRate c.borrowPerYearInterestRateSlopeLow)) ?_
  · exact constructorSourceDivNat (constructorSourceField hl rfl) (by decide)
  dsimp only
  refine ExecBlock.consNormal (ExecStmt.setImmutable
    (value := .int (Int.ofNat (c.borrowPerYearInterestRateSlopeHigh.val / 31536000)))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl (fitsRate c.borrowPerYearInterestRateSlopeHigh)) ?_
  · exact constructorSourceDivNat (constructorSourceField hl rfl) (by decide)
  dsimp only
  refine ExecBlock.consNormal (ExecStmt.setImmutable
    (value := .int (Int.ofNat (c.borrowPerYearInterestRateBase.val / 31536000)))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ rfl (fitsRate c.borrowPerYearInterestRateBase)) ?_
  · exact constructorSourceDivNat (constructorSourceField hl rfl) (by decide)
  dsimp only
  refine ExecBlock.consNormal (ExecStmt.setImmutable
    (value := .int (Int.ofNat c.assetConfigs.length)) (ty := .int (.uint ⟨8, by decide⟩))
    ?_ rfl (by simp [elemValueFits]; omega)) .nil
  have hnorm : normalizeInt (.uint ⟨8, by decide⟩) (Int.ofNat c.assetConfigs.length) =
      Int.ofNat c.assetConfigs.length :=
    normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _) (by
      change Int.ofNat c.assetConfigs.length < Int.ofNat 256
      exact Int.ofNat_lt.mpr (by omega))
  rw [← hnorm]
  apply evalExpr_cast_int
  exact constructorSourceAssetCount hl

def constructorSourceDelegate (c : ConstructorConfig) (w feed : UInt256) : Frame :=
  let frame := constructorSourceRemainingImms c w feed
  { frame with locals := frame.locals.insert "delegate" (.address c.extensionDelegate) }

theorem constructorSourceDelegate_exec {c : ConstructorConfig} {w feed : UInt256}
    {evm evm' : EVM.State}
    (hp : ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 34)
      (.ok (constructorSourceRemainingImms c w feed) evm')) :
    ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 35)
      (.ok (constructorSourceDelegate c w feed) evm') := by
  change ExecBlock config _ _ (contract.ctor.body.take 34 ++
    [.letDecl "delegate" (some (.elem .address)) (.immutable "extensionDelegate")]) _
  apply execBlockAppendOk hp
  refine .consNormal (.letDecl ?_) .nil
  simp only [evalExpr?, constructorSourceRemainingImms, constructorRemainingImms,
    constructorScaleImms, constructorInitialImms, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, EvalResult.ofOption]
  rfl

end Benchmarks.CompoundIII.Comet
