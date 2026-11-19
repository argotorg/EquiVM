import Benchmarks.Midnight.PositionViewSourceBase

/-! Source execution of the credit-slashing branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def slashCreditFrame (frame : Frame) (credit lastLoss loss : UInt256) : Frame :=
  if lastLoss.toNat < 2 ^ 128 - 1 then
    let v := slashCredit credit lastLoss loss
    wordLocal (wordLocal frame "slashed" v) "postSlashCredit" v
  else frame

theorem slashCreditFrame_contract (frame : Frame) (credit lastLoss loss : UInt256) :
    (slashCreditFrame frame credit lastLoss loss).contract = frame.contract := by
  unfold slashCreditFrame
  split <;> rfl

theorem slashCreditFrame_get (frame : Frame) (credit lastLoss loss : UInt256) (name : Ident)
    (h₁ : "slashed" ≠ name) (h₂ : "postSlashCredit" ≠ name) :
    (slashCreditFrame frame credit lastLoss loss).locals.get? name = frame.locals.get? name := by
  unfold slashCreditFrame
  split
  · rw [wordLocal_get_ne _ _ _ _ h₂, wordLocal_get_ne _ _ _ _ h₁]
  · rfl

theorem slashCreditFrame_value {frame : Frame} (credit lastLoss loss : UInt256)
    (hzero : frame.locals.get? "postSlashCredit" = some (.int 0)) :
    (slashCreditFrame frame credit lastLoss loss).locals.get? "postSlashCredit" =
      some (.int (slashCredit credit lastLoss loss).toNat) := by
  unfold slashCreditFrame
  split
  · exact wordLocal_get _ _ _
  · rename_i h
    simpa only [slashCredit, h, if_false] using hzero

theorem slashCreditSource {frame : Frame} {evm : EVM.State} {id credit lastLoss : UInt256}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hcredit : frame.locals.get? "_credit" = some (.int credit.toNat))
    (hlast : frame.locals.get? "_lastLossFactor" = some (.int lastLoss.toNat))
    (hzero : frame.locals.get? "postSlashCredit" = some (.int 0))
    (hbound : credit.toNat < 2 ^ 128) :
    ExecStmt config frame evm (positionViewFunction.body[4]!)
      (.ok (slashCreditFrame frame credit lastLoss (marketLossWord evm id)) evm) := by
  by_cases hlt : lastLoss.toNat < 2 ^ 128 - 1
  · have hloss := evalComplement128 (evalMarketLoss (evm := evm) hc hbase hid) (shiftRight128_lt _)
    have hlastDiff := evalComplement128 (evalWordLocal (cfg := config) (evm := evm) hlast)
      (by omega)
    have hargs : evalExprs? config frame evm
        [.var "_credit", .inRange packedUInt128Int (.binary .sub (.intLit (2 ^ 128 - 1))
          (.storage { base := "marketState", steps := [.mindex (.var "id"), .field "lossFactor"] })),
         .inRange packedUInt128Int (.binary .sub (.intLit (2 ^ 128 - 1)) (.var "_lastLossFactor"))] =
        .ok [.int credit.toNat, .int (complement128 (marketLossWord evm id)).toNat,
          .int (complement128 lastLoss).toNat] := by
      simp only [evalExprs?, evalWordLocal hcredit, hloss, hlastDiff, bind, pure, EvalResult.bind]
    have hnz : complement128 lastLoss ≠ ⟨0⟩ := by
      intro hz
      have hp := complement128_pos hlt
      rw [hz] at hp
      contradiction
    rw [slashCreditFrame, if_pos hlt]
    simp only [slashCredit, hlt, if_true]
    apply ExecStmt.iteTrue
      ((evalLocalLtNat (2 ^ 128 - 1) hlast).trans (by rw [decide_eq_true hlt]))
    have hcall := callMulDivDown hc hargs
      (uint128_product_bound hbound (complement128_lt (shiftRight128_lt _))) hnz
      (name := "slashed")
    apply ExecBlock.consNormal hcall
    apply ExecBlock.consNormal (execLocalAssign (old := .int 0) ?_ ?_) ExecBlock.nil
    · change (wordLocal frame "slashed" _).locals.get? "postSlashCredit" = some (.int 0)
      rw [wordLocal_get_ne _ _ _ _ (by decide)]
      exact hzero
    · apply evalWordLocal
      change (wordLocal frame "slashed" _).locals.get? "slashed" = _
      simpa only [slashCredit, hlt, if_true] using (wordLocal_get frame "slashed"
        (mulDivDown credit (complement128 (marketLossWord evm id)) (complement128 lastLoss)))
  · rw [slashCreditFrame, if_neg hlt]
    exact ExecStmt.iteFalse
      ((evalLocalLtNat (2 ^ 128 - 1) hlast).trans (by rw [decide_eq_false hlt])) ExecBlock.nil

end Benchmarks.Midnight
