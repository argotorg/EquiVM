import Benchmarks.Midnight.SettlementIntervals

variable {fork : Ethereum.Fork}

/-! Source control flow of the settlement-fee internal function. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def settlementFeeFunction : FunctionDecl := contract.functions[6]!

def settlementFeeArguments (id time : UInt256) : Store :=
  ((∅ : Store).insert "timeToMaturity" (.int time.toNat)).insert "id" (wordBytes32Value id)

def settlementFeeInterpolated (word time : UInt256) : UInt256 :=
  if time.toNat < 86400 then
    interpolatedFee (scaledSettlementFee word 0) (scaledSettlementFee word 1) time
      (UInt256.ofNat 0) (UInt256.ofNat 86400)
  else
  if time.toNat < 604800 then
    interpolatedFee (scaledSettlementFee word 1) (scaledSettlementFee word 2) time
      (UInt256.ofNat 86400) (UInt256.ofNat 604800)
  else
  if time.toNat < 2592000 then
    interpolatedFee (scaledSettlementFee word 2) (scaledSettlementFee word 3) time
      (UInt256.ofNat 604800) (UInt256.ofNat 2592000)
  else
  if time.toNat < 7776000 then
    interpolatedFee (scaledSettlementFee word 3) (scaledSettlementFee word 4) time
      (UInt256.ofNat 2592000) (UInt256.ofNat 7776000)
  else
  if time.toNat < 15552000 then
    interpolatedFee (scaledSettlementFee word 4) (scaledSettlementFee word 5) time
      (UInt256.ofNat 7776000) (UInt256.ofNat 15552000)
  else
    interpolatedFee (scaledSettlementFee word 5) (scaledSettlementFee word 6) time
      (UInt256.ofNat 15552000) (UInt256.ofNat 31104000)

def settlementFeeValue (word time : UInt256) : UInt256 :=
  if 31104000 ≤ time.toNat then scaledSettlementFee word 6
  else settlementFeeInterpolated word time

theorem settlementChooseInterval {frame : Frame} {evm : EVM.State} {id time : UInt256}
    (hget : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (ht : frame.locals.get? "timeToMaturity" = some (.int time.toNat))
    (hs : frame.locals.get? "start" = some (.int 15552000))
    (he : frame.locals.get? "end" = some (.int 31104000))
    (hl : frame.locals.get? "feeLower" = some (.int 0))
    (hu : frame.locals.get? "feeUpper" = some (.int 0))
    (hmax : time.toNat < 31104000) :
    ∃ frame', ExecStmt fork config frame evm (settlementFeeFunction.body[7]!) (.ok frame' evm) ∧
      evalExpr? config frame' evm interpolationExpr =
        .ok (.int (settlementFeeInterpolated (marketFeeWord evm id) time).toNat) := by
  by_cases h0 : time.toNat < 86400
  · obtain ⟨frame', hbody, hvalue⟩ := settlementFeeInterval ⟨0, by decide⟩
      0 86400 hget ht hs he hl hu (by decide) (by omega) (by omega) (by decide)
    refine ⟨frame', ?_, by simpa only [settlementFeeInterpolated, h0,
      if_true, if_false] using hvalue⟩
    exact ExecStmt.iteTrue
      ((evalLocalLtNat 86400 ht).trans (by rw [decide_eq_true h0])) hbody
  by_cases h1 : time.toNat < 604800
  · obtain ⟨frame', hbody, hvalue⟩ := settlementFeeInterval ⟨1, by decide⟩
      86400 604800 hget ht hs he hl hu (by decide) (by omega) (by omega) (by decide)
    refine ⟨frame', ?_, by simpa only [settlementFeeInterpolated, h0, h1,
      if_true, if_false] using hvalue⟩
    apply execElseIf ((evalLocalLtNat 86400 ht).trans (by rw [decide_eq_false h0]))
    exact ExecStmt.iteTrue
      ((evalLocalLtNat 604800 ht).trans (by rw [decide_eq_true h1])) hbody
  by_cases h2 : time.toNat < 2592000
  · obtain ⟨frame', hbody, hvalue⟩ := settlementFeeInterval ⟨2, by decide⟩
      604800 2592000 hget ht hs he hl hu (by decide) (by omega) (by omega) (by decide)
    refine ⟨frame', ?_, by simpa only [settlementFeeInterpolated, h0, h1, h2,
      if_true, if_false] using hvalue⟩
    apply execElseIf ((evalLocalLtNat 86400 ht).trans (by rw [decide_eq_false h0]))
    apply execElseIf ((evalLocalLtNat 604800 ht).trans (by rw [decide_eq_false h1]))
    exact ExecStmt.iteTrue
      ((evalLocalLtNat 2592000 ht).trans (by rw [decide_eq_true h2])) hbody
  by_cases h3 : time.toNat < 7776000
  · obtain ⟨frame', hbody, hvalue⟩ := settlementFeeInterval ⟨3, by decide⟩
      2592000 7776000 hget ht hs he hl hu (by decide) (by omega) (by omega) (by decide)
    refine ⟨frame', ?_, by simpa only [settlementFeeInterpolated, h0, h1, h2, h3,
      if_true, if_false] using hvalue⟩
    apply execElseIf ((evalLocalLtNat 86400 ht).trans (by rw [decide_eq_false h0]))
    apply execElseIf ((evalLocalLtNat 604800 ht).trans (by rw [decide_eq_false h1]))
    apply execElseIf ((evalLocalLtNat 2592000 ht).trans (by rw [decide_eq_false h2]))
    exact ExecStmt.iteTrue
      ((evalLocalLtNat 7776000 ht).trans (by rw [decide_eq_true h3])) hbody
  by_cases h4 : time.toNat < 15552000
  · obtain ⟨frame', hbody, hvalue⟩ := settlementFeeInterval ⟨4, by decide⟩
      7776000 15552000 hget ht hs he hl hu (by decide) (by omega) (by omega) (by decide)
    refine ⟨frame', ?_, by simpa only [settlementFeeInterpolated, h0, h1, h2, h3, h4,
      if_true, if_false] using hvalue⟩
    apply execElseIf ((evalLocalLtNat 86400 ht).trans (by rw [decide_eq_false h0]))
    apply execElseIf ((evalLocalLtNat 604800 ht).trans (by rw [decide_eq_false h1]))
    apply execElseIf ((evalLocalLtNat 2592000 ht).trans (by rw [decide_eq_false h2]))
    apply execElseIf ((evalLocalLtNat 7776000 ht).trans (by rw [decide_eq_false h3]))
    exact ExecStmt.iteTrue
      ((evalLocalLtNat 15552000 ht).trans (by rw [decide_eq_true h4])) hbody
  obtain ⟨frame', hbody, hvalue⟩ := settlementFeePair
    (start := UInt256.ofNat 15552000) (finish := UInt256.ofNat 31104000)
    ⟨5, by decide⟩ hget ht hs he hl hu (by decide) (by change 15552000 ≤ time.toNat; omega)
    (by change time.toNat ≤ 31104000; omega) (by decide)
  refine ⟨frame', ?_, by simpa only [settlementFeeInterpolated, h0, h1, h2, h3, h4,
    if_true, if_false] using hvalue⟩
  apply execElseIf ((evalLocalLtNat 86400 ht).trans (by rw [decide_eq_false h0]))
  apply execElseIf ((evalLocalLtNat 604800 ht).trans (by rw [decide_eq_false h1]))
  apply execElseIf ((evalLocalLtNat 2592000 ht).trans (by rw [decide_eq_false h2]))
  apply execElseIf ((evalLocalLtNat 7776000 ht).trans (by rw [decide_eq_false h3]))
  exact ExecStmt.iteFalse
    ((evalLocalLtNat 15552000 ht).trans (by rw [decide_eq_false h4])) hbody

def settlementCallFrame (imms : Store) (id time : UInt256) : Frame :=
  { contract := contract, locals := settlementFeeArguments id time, immutables := imms }

def settlementAliasFrame (imms : Store) (id time : UInt256) : Frame :=
  { (settlementCallFrame imms id time) with
    locals := (settlementFeeArguments id time).insert "_marketState"
      (.storageRef (marketStateRef id) marketStateType) }

def settlementInitialIntervals (imms : Store) (id time : UInt256) : Frame :=
  { (settlementAliasFrame imms id time) with
    locals := ((((settlementAliasFrame imms id time).locals.insert "start" (.int 15552000)).insert
      "end" (.int 31104000)).insert "feeLower" (.int 0)).insert "feeUpper" (.int 0) }

theorem settlementBindAlias (evm : EVM.State) (imms : Store) (id time : UInt256) :
    ABlock fork config evm (settlementCallFrame imms id time) settlementFeeFunction.body
      (settlementAliasFrame imms id time) (settlementFeeFunction.body.drop 1) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letStorage ?_) h⟩
  apply resolveBytes32Mapping
  · simp [settlementCallFrame, settlementFeeArguments]
  · exact store_get_self _ _ _
  · rfl

theorem evalSettlementRequire (evm : EVM.State) (imms : Store) (id time : UInt256) :
    evalExpr? config (settlementAliasFrame imms id time) evm
      (.binary .gt (.storage { base := "_marketState", steps := [.field "tickSpacing"] })
        (.intLit 0)) =
      .ok (.bool (decide (0 < (marketTickSpacing (marketFeeWord evm id)).toNat))) := by
  rw [evalExpr_binary_nonshort (by decide : BinaryOp.gt ≠ .and) (by decide : BinaryOp.gt ≠ .or)]
  rw [evalMarketAliasTickSpacing (id := id) (store_get_self _ _ _)]
  simp [evalExpr?, bind, pure, EvalResult.bind, evalBinaryOp?]

theorem settlementFeeInternalReverts (evm : EVM.State) (imms : Store) (id time : UInt256)
    (hspace : marketTickSpacing (marketFeeWord evm id) = ⟨0⟩) :
    ExecFuncBody fork config (settlementCallFrame imms id time) evm settlementFeeFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (settlementBindAlias evm imms id time).requireRevert
  rw [evalSettlementRequire, hspace]
  rfl

theorem settlementFeeInternalReturns (evm : EVM.State) (imms : Store) (id time : UInt256)
    (hspace : marketTickSpacing (marketFeeWord evm id) ≠ ⟨0⟩) :
    ∃ frame', ExecFuncBody fork config (settlementCallFrame imms id time) evm
      settlementFeeFunction.body (.returned frame' evm
        (some [.int (settlementFeeValue (marketFeeWord evm id) time).toNat])) := by
  have hpositive : 0 < (marketTickSpacing (marketFeeWord evm id)).toNat := by
    by_contra h
    exact hspace (uint256_toNat_eq_zero (by omega))
  have hprefix := (settlementBindAlias (fork := fork) evm imms id time).requireStep
    ((evalSettlementRequire evm imms id time).trans (by rw [decide_eq_true hpositive]))
  have ht : (settlementAliasFrame imms id time).locals.get? "timeToMaturity" =
      some (.int time.toNat) := by
    change (((∅ : Store).insert "timeToMaturity" (.int time.toNat)).insert "id"
      (wordBytes32Value id) |>.insert "_marketState" (.storageRef (marketStateRef id)
        marketStateType)).get? "timeToMaturity" = _
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  by_cases hlast : 31104000 ≤ time.toNat
  · refine ⟨settlementAliasFrame imms id time, ExecFuncBody.execBlockRet (hprefix.run ?_)⟩
    apply ExecBlock.consReturn
    apply ExecStmt.iteTrue ((evalLocalGeNat 31104000 ht).trans (by rw [decide_eq_true hlast]))
    apply ABlock.start.returns
    rw [settlementFeeValue, if_pos hlast]
    exact evalExpr_uint256_inRange
      (evalScaledSettlementFee ⟨6, by decide⟩ (store_get_self _ _ _))
  · have hget : (settlementInitialIntervals imms id time).locals.get? "_marketState" =
        some (.storageRef (marketStateRef id) marketStateType) := by
      dsimp only [settlementInitialIntervals]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
      exact store_get_self _ _ _
    have ht' : (settlementInitialIntervals imms id time).locals.get? "timeToMaturity" =
        some (.int time.toNat) := by
      dsimp only [settlementInitialIntervals]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
      exact ht
    obtain ⟨frame', hchoose, hvalue⟩ := settlementChooseInterval hget ht' (by
        dsimp only [settlementInitialIntervals]
        rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
          store_get_ne _ _ (by decide), store_get_self]) (by
        dsimp only [settlementInitialIntervals]
        rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self])
      ((store_get_ne _ _ (by decide : ("feeUpper" == "feeLower") = false)).trans
        (store_get_self _ _ _)) (store_get_self _ _ _) (by omega)
    refine ⟨frame', ExecFuncBody.execBlockRet (hprefix.run ?_)⟩
    apply ExecBlock.consNormal (ExecStmt.iteFalse
      ((evalLocalGeNat 31104000 ht).trans (by rw [decide_eq_false hlast])) ExecBlock.nil)
    apply (ABlock.start.letStep (value := .int 15552000) (by simp [evalExpr?, pure])
      |>.letStep (value := .int 31104000) (by simp [evalExpr?, pure])
      |>.letStep (value := .int 0) (by simp [evalExpr?, pure])
      |>.letStep (value := .int 0) (by simp [evalExpr?, pure])).run
    apply ExecBlock.consNormal hchoose
    apply ABlock.start.returns
    simpa only [settlementFeeValue, if_neg hlast] using hvalue

end Benchmarks.Midnight
