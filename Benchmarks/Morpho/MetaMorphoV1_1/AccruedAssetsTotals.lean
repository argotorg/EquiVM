import Benchmarks.Morpho.MetaMorphoV1_1.AccruedAssetsPrefix

/-! Loss adjustment and checked total-assets and interest arithmetic. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def accruedNewLost (last lost real : UInt256) : UInt256 :=
  if real.toNat < (UInt256.sub last lost).toNat then UInt256.sub last real else lost

def accruedNewTotal (last lost real : UInt256) : UInt256 := real + accruedNewLost last lost real

def accruedInterest (last lost real : UInt256) : UInt256 :=
  UInt256.sub (accruedNewTotal last lost real) last

def accruedTotalsFit (last lost real : UInt256) : Prop :=
  lost.toNat ≤ last.toNat ∧ real.toNat + (accruedNewLost last lost real).toNat < UInt256.size

theorem accruedLossSubFits {last lost real : UInt256} (hl : lost.toNat ≤ last.toNat)
    (hr : real.toNat < (UInt256.sub last lost).toNat) : real.toNat ≤ last.toNat := by
  rw [usub_toNat hl] at hr
  omega

theorem accruedTotal_ge_last {last lost real : UInt256}
    (hfit : accruedTotalsFit last lost real) :
    last.toNat ≤ (accruedNewTotal last lost real).toNat := by
  unfold accruedNewTotal
  have hadd : (real + accruedNewLost last lost real).toNat =
      real.toNat + (accruedNewLost last lost real).toNat := addWord_toNat _ _ hfit.2
  rw [hadd]
  unfold accruedNewLost
  split_ifs with hr
  · rw [usub_toNat (accruedLossSubFits hfit.1 hr)]
    omega
  · rw [usub_toNat hfit.1] at hr
    omega

def accruedLossCondition : Expr :=
  .binary .lt (.var "realTotalAssets")
    (.inRange (.uint ⟨256, by decide⟩)
      (.binary .sub (.storage ⟨"lastTotalAssets", []⟩) (.storage ⟨"lostAssets", []⟩)))

def accruedLossStmt : Stmt :=
  .ite accruedLossCondition
    [.assign .localVar ⟨"newLostAssets", []⟩ (.inRange (.uint ⟨256, by decide⟩)
      (.binary .sub (.storage ⟨"lastTotalAssets", []⟩) (.var "realTotalAssets")))]
    [.assign .localVar ⟨"newLostAssets", []⟩ (.storage ⟨"lostAssets", []⟩)]

def accruedTotalStmt : Stmt :=
  .assign .localVar ⟨"newTotalAssets", []⟩ (.inRange (.uint ⟨256, by decide⟩)
    (.binary .add (.var "realTotalAssets") (.var "newLostAssets")))

def accruedInterestStmt : Stmt :=
  .letDecl "totalInterest" (some abiUInt256) (.inRange (.uint ⟨256, by decide⟩)
    (.binary .sub (.var "newTotalAssets") (.storage ⟨"lastTotalAssets", []⟩)))

theorem allocatedAccruedFeeAssetsFunction_totals :
    allocatedAccruedFeeAssetsFunction.body.drop 5 =
      [accruedLossStmt, accruedTotalStmt, accruedInterestStmt] ++
        allocatedAccruedFeeAssetsFunction.body.drop 8 := by decide +kernel

def accruedLossFrame (frame : Frame) (last lost real : UInt256) : Frame :=
  { frame with locals :=
    frame.locals.insert "newLostAssets" (uint256Value (accruedNewLost last lost real)) }

def accruedTotalFrame (frame : Frame) (last lost real : UInt256) : Frame :=
  { accruedLossFrame frame last lost real with
    locals := (accruedLossFrame frame last lost real).locals.insert "newTotalAssets"
      (uint256Value (accruedNewTotal last lost real)) }

def accruedInterestFrame (frame : Frame) (last lost real : UInt256) : Frame :=
  { accruedTotalFrame frame last lost real with
    locals := (accruedTotalFrame frame last lost real).locals.insert "totalInterest"
      (uint256Value (accruedInterest last lost real)) }

theorem accruedLossChoiceSource {frame : Frame} {evm : State} {last lost real : UInt256}
    {old : Value}
    (ha : evalExpr? config frame evm (.storage ⟨"lastTotalAssets", []⟩) =
      .ok (uint256Value last))
    (hb : evalExpr? config frame evm (.storage ⟨"lostAssets", []⟩) = .ok (uint256Value lost))
    (hr : frame.locals.get? "realTotalAssets" = some (uint256Value real))
    (hn : frame.locals.get? "newLostAssets" = some old)
    (hl : lost.toNat ≤ last.toNat) :
    ExecStmt config frame evm accruedLossStmt
      (.ok (accruedLossFrame frame last lost real) evm) := by
  have hreal : evalExpr? config frame evm (.var "realTotalAssets") =
      .ok (uint256Value real) := by simp only [evalExpr?, hr, EvalResult.ofOption]
  have hcond := naturalLtSource hreal (evalExpr_uint256_sub ha hb hl)
  by_cases hlt : real.toNat < (UInt256.sub last lost).toNat
  · simp only [hlt, decide_true] at hcond
    apply ExecStmt.iteTrue hcond
    apply ExecBlock.consNormal (ExecStmt.assign
      (evalExpr_uint256_sub ha hreal (accruedLossSubFits hl hlt)) ?_) ExecBlock.nil
    simp only [assignStorageRef?, hn, updateLocalPath?, EvalResult.ofOption,
      bind, EvalResult.bind, pure, accruedLossFrame, accruedNewLost, if_pos hlt]
  · simp only [hlt, decide_false] at hcond
    apply ExecStmt.iteFalse hcond
    apply ExecBlock.consNormal (ExecStmt.assign hb ?_) ExecBlock.nil
    simp only [assignStorageRef?, hn, updateLocalPath?, EvalResult.ofOption,
      bind, EvalResult.bind, pure, accruedLossFrame, accruedNewLost, if_neg hlt]

theorem accruedLossChoiceReverts {frame : Frame} {evm : State} {last lost real : UInt256}
    (ha : evalExpr? config frame evm (.storage ⟨"lastTotalAssets", []⟩) =
      .ok (uint256Value last))
    (hb : evalExpr? config frame evm (.storage ⟨"lostAssets", []⟩) = .ok (uint256Value lost))
    (hr : frame.locals.get? "realTotalAssets" = some (uint256Value real))
    (hl : last.toNat < lost.toNat) : ExecStmt config frame evm accruedLossStmt .reverted := by
  apply ExecStmt.iteCondRevert
  exact binarySourceRevertRight (value := uint256Value real) (by decide) (by decide)
    (by simp only [evalExpr?, hr, EvalResult.ofOption]) (checkedSubSourceUnderflow ha hb hl)

theorem accruedTotalSource {frame : Frame} {evm : State} {last lost real : UInt256} {old : Value}
    (hr : frame.locals.get? "realTotalAssets" = some (uint256Value real))
    (ht : frame.locals.get? "newTotalAssets" = some old)
    (hfit : real.toNat + (accruedNewLost last lost real).toNat < UInt256.size) :
    ExecStmt config (accruedLossFrame frame last lost real) evm accruedTotalStmt
      (.ok (accruedTotalFrame frame last lost real) evm) := by
  apply ExecStmt.assign (checkedAddSourceOk ?_ ?_ hfit)
  · simp only [assignStorageRef?, accruedLossFrame,
      store_get_ne _ _ (by decide : ("newLostAssets" == "newTotalAssets") = false),
      ht, updateLocalPath?, bind, EvalResult.bind, pure]
    rfl
  · simp only [evalExpr?, accruedLossFrame,
      store_get_ne _ _ (by decide : ("newLostAssets" == "realTotalAssets") = false),
      hr, EvalResult.ofOption]
  · simp only [evalExpr?, accruedLossFrame, store_get_self, EvalResult.ofOption]

theorem accruedTotalReverts {frame : Frame} {evm : State} {last lost real : UInt256}
    (hr : frame.locals.get? "realTotalAssets" = some (uint256Value real))
    (hbad : UInt256.size ≤ real.toNat + (accruedNewLost last lost real).toNat) :
    ExecStmt config (accruedLossFrame frame last lost real) evm accruedTotalStmt .reverted := by
  apply ExecStmt.assignExprRevert (checkedAddSourceOverflow ?_ ?_ hbad)
  · simp only [evalExpr?, accruedLossFrame,
      store_get_ne _ _ (by decide : ("newLostAssets" == "realTotalAssets") = false),
      hr, EvalResult.ofOption]
  · simp only [evalExpr?, accruedLossFrame, store_get_self, EvalResult.ofOption]

theorem accruedInterestSource {frame : Frame} {evm : State} {last lost real : UInt256}
    (ha : evalExpr? config (accruedTotalFrame frame last lost real) evm
      (.storage ⟨"lastTotalAssets", []⟩) = .ok (uint256Value last))
    (hfit : accruedTotalsFit last lost real) :
    ExecStmt config (accruedTotalFrame frame last lost real) evm accruedInterestStmt
      (.ok (accruedInterestFrame frame last lost real) evm) := by
  apply ExecStmt.letDecl (evalExpr_uint256_sub ?_ ha (accruedTotal_ge_last hfit))
  simp only [evalExpr?, accruedTotalFrame, store_get_self, EvalResult.ofOption]

theorem accruedTotalsSource {frame : Frame} {evm : State} {last lost real : UInt256}
    {oldLost oldTotal : Value}
    (ha : evalExpr? config frame evm (.storage ⟨"lastTotalAssets", []⟩) =
      .ok (uint256Value last))
    (hb : evalExpr? config frame evm (.storage ⟨"lostAssets", []⟩) = .ok (uint256Value lost))
    (ha' : evalExpr? config (accruedTotalFrame frame last lost real) evm
      (.storage ⟨"lastTotalAssets", []⟩) = .ok (uint256Value last))
    (hr : frame.locals.get? "realTotalAssets" = some (uint256Value real))
    (hn : frame.locals.get? "newLostAssets" = some oldLost)
    (ht : frame.locals.get? "newTotalAssets" = some oldTotal)
    (hfit : accruedTotalsFit last lost real) :
    ABlock config evm frame (allocatedAccruedFeeAssetsFunction.body.drop 5)
      (accruedInterestFrame frame last lost real)
      (allocatedAccruedFeeAssetsFunction.body.drop 8) := by
  refine ⟨fun h ↦ ?_⟩
  rw [allocatedAccruedFeeAssetsFunction_totals]
  exact ExecBlock.consNormal (accruedLossChoiceSource ha hb hr hn hfit.1)
    (ExecBlock.consNormal (accruedTotalSource hr ht hfit.2)
      (ExecBlock.consNormal (accruedInterestSource ha' hfit) h))

theorem accruedTotalsReverts {frame : Frame} {evm : State} {last lost real : UInt256}
    {oldLost : Value}
    (ha : evalExpr? config frame evm (.storage ⟨"lastTotalAssets", []⟩) =
      .ok (uint256Value last))
    (hb : evalExpr? config frame evm (.storage ⟨"lostAssets", []⟩) = .ok (uint256Value lost))
    (hr : frame.locals.get? "realTotalAssets" = some (uint256Value real))
    (hn : frame.locals.get? "newLostAssets" = some oldLost)
    (hbad : ¬ accruedTotalsFit last lost real) :
    ExecBlock config frame evm (allocatedAccruedFeeAssetsFunction.body.drop 5) .reverted := by
  rw [allocatedAccruedFeeAssetsFunction_totals]
  by_cases hl : lost.toNat ≤ last.toNat
  · exact ExecBlock.consNormal (accruedLossChoiceSource ha hb hr hn hl)
      (ExecBlock.consRevert (accruedTotalReverts hr
        (Nat.le_of_not_gt (fun h ↦ hbad ⟨hl, h⟩))))
  · exact ExecBlock.consRevert (accruedLossChoiceReverts ha hb hr (Nat.lt_of_not_ge hl))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
