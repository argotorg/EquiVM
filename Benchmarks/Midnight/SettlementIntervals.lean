import Benchmarks.Midnight.Interpolation
import Benchmarks.Midnight.SourceControl

/-! Source assignments and interpolation for each settlement-fee interval. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def settlementFeePairBlock (i : Nat) : List Stmt :=
  [.assign .localVar { base := "feeLower" } (.binary .mul
    (.storage { base := "_marketState", steps := [.field ("settlementFeeCbp" ++ toString i)] })
    (.intLit 1000000000000)),
   .assign .localVar { base := "feeUpper" } (.binary .mul
    (.storage { base := "_marketState", steps := [.field ("settlementFeeCbp" ++ toString (i + 1))] })
    (.intLit 1000000000000))]

theorem settlementFeePair {frame : Frame} {evm : EVM.State} {id time start finish : UInt256}
    {oldLower oldUpper : Value} (i : Fin 6)
    (hget : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (ht : frame.locals.get? "timeToMaturity" = some (.int time.toNat))
    (hs : frame.locals.get? "start" = some (.int start.toNat))
    (he : frame.locals.get? "end" = some (.int finish.toNat))
    (hl : frame.locals.get? "feeLower" = some oldLower)
    (hu : frame.locals.get? "feeUpper" = some oldUpper)
    (hfinish : finish.toNat < 2 ^ 32)
    (hstart : start.toNat ≤ time.toNat) (htime : time.toNat ≤ finish.toNat)
    (hwidth : start.toNat < finish.toNat) :
    ∃ frame', ExecBlock config frame evm (settlementFeePairBlock i.val) (.ok frame' evm) ∧
      evalExpr? config frame' evm interpolationExpr = .ok (.int
        (interpolatedFee (scaledSettlementFee (marketFeeWord evm id) i.val)
          (scaledSettlementFee (marketFeeWord evm id) (i.val + 1)) time start finish).toNat) := by
  let lower := scaledSettlementFee (marketFeeWord evm id) i.val
  let upper := scaledSettlementFee (marketFeeWord evm id) (i.val + 1)
  let frame' := { frame with locals :=
    (frame.locals.insert "feeLower" (.int lower.toNat)).insert "feeUpper" (.int upper.toNat) }
  refine ⟨frame', ?_, ?_⟩
  · apply ExecBlock.consNormal (execLocalAssign hl (evalScaledSettlementFee ⟨i.val, by omega⟩ hget))
    apply ExecBlock.consNormal (execLocalAssign (old := oldUpper) ?_
      (evalScaledSettlementFee ⟨i.val + 1, by omega⟩ ?_)) ExecBlock.nil
    · exact (store_get_ne frame.locals (.int lower.toNat)
        (by decide : ("feeLower" == "feeUpper") = false)).trans hu
    · exact (store_get_ne frame.locals (.int lower.toNat)
        (by decide : ("feeLower" == "_marketState") = false)).trans hget
  · apply evalInterpolation (scaledSettlementFee_lt _ _) (scaledSettlementFee_lt _ _)
      hfinish hstart htime hwidth
    · exact (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)
    · exact store_get_self _ _ _
    · exact (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans ht)
    · exact (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hs)
    · exact (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans he)

def settlementFeeIntervalBlock (i start finish : Nat) : List Stmt :=
  [.assign .localVar { base := "start" } (.intLit start),
   .assign .localVar { base := "end" } (.intLit finish)] ++ settlementFeePairBlock i

theorem settlementFeeInterval {frame : Frame} {evm : EVM.State} {id time : UInt256}
    {oldStart oldEnd oldLower oldUpper : Value} (i : Fin 6) (start finish : Nat)
    (hget : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (ht : frame.locals.get? "timeToMaturity" = some (.int time.toNat))
    (hs : frame.locals.get? "start" = some oldStart)
    (he : frame.locals.get? "end" = some oldEnd)
    (hl : frame.locals.get? "feeLower" = some oldLower)
    (hu : frame.locals.get? "feeUpper" = some oldUpper)
    (hfinish : finish < 2 ^ 32)
    (hstart : start ≤ time.toNat) (htime : time.toNat ≤ finish) (hwidth : start < finish) :
    ∃ frame', ExecBlock config frame evm (settlementFeeIntervalBlock i.val start finish)
      (.ok frame' evm) ∧
      evalExpr? config frame' evm interpolationExpr = .ok (.int
        (interpolatedFee (scaledSettlementFee (marketFeeWord evm id) i.val)
          (scaledSettlementFee (marketFeeWord evm id) (i.val + 1)) time
          (UInt256.ofNat start) (UInt256.ofNat finish)).toNat) := by
  have hsword : (UInt256.ofNat start).toNat = start :=
    UInt256.toNat_ofNat_of_lt (by change start < 2 ^ 256; omega)
  have heword : (UInt256.ofNat finish).toNat = finish :=
    UInt256.toNat_ofNat_of_lt (by change finish < 2 ^ 256; omega)
  obtain ⟨frame', hpair, hvalue⟩ := settlementFeePair
    (frame := { frame with locals :=
      (frame.locals.insert "start" (.int start)).insert "end" (.int finish) })
    (evm := evm) (id := id) (time := time) (start := UInt256.ofNat start)
    (finish := UInt256.ofNat finish) i
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hget))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans ht))
    (by rw [hsword]; exact (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _))
    (by rw [heword]; exact store_get_self _ _ _)
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hl))
    ((store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans hu))
    (by rwa [heword]) (by rwa [hsword]) (by rwa [heword]) (by rwa [hsword, heword])
  refine ⟨frame', ?_, hvalue⟩
  apply ExecBlock.consNormal (execLocalAssign (value := .int start) hs (by simp [evalExpr?, pure]))
  exact ExecBlock.consNormal (execLocalAssign (value := .int finish)
    ((store_get_ne _ _ (by decide : ("start" == "end") = false)).trans he)
    (by simp [evalExpr?, pure])) hpair

end Benchmarks.Midnight
