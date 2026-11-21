import Benchmarks.Midnight.SettlementFields

/-! Checked word arithmetic for linear interpolation of bounded fees. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def interpolatedFee (lower upper time start finish : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul lower (UInt256.sub finish time) +
    UInt256.mul upper (UInt256.sub time start)) (UInt256.sub finish start)

-- LIBRARY CANDIDATE: bounded interpolation cannot overflow a 256-bit word.
theorem interpolationBounds {lower upper time start finish : UInt256}
    (hlower : lower.toNat < 2 ^ 64) (hupper : upper.toNat < 2 ^ 64)
    (hfinish : finish.toNat < 2 ^ 32)
    (hstart : start.toNat ≤ time.toNat) (htime : time.toNat ≤ finish.toNat) :
    lower.toNat * (UInt256.sub finish time).toNat < UInt256.size ∧
    upper.toNat * (UInt256.sub time start).toNat < UInt256.size ∧
    (UInt256.mul lower (UInt256.sub finish time)).toNat +
      (UInt256.mul upper (UInt256.sub time start)).toNat < UInt256.size := by
  have hleft : lower.toNat * (finish.toNat - time.toNat) ≤ 2 ^ 64 * 2 ^ 32 :=
    Nat.mul_le_mul hlower.le (by omega)
  have hright : upper.toNat * (time.toNat - start.toNat) ≤ 2 ^ 64 * 2 ^ 32 :=
    Nat.mul_le_mul hupper.le (by omega)
  rw [usub_toNat htime, usub_toNat hstart]
  have hleft' : lower.toNat * (finish.toNat - time.toNat) < UInt256.size := by
    change _ < 2 ^ 256; omega
  have hright' : upper.toNat * (time.toNat - start.toNat) < UInt256.size := by
    change _ < 2 ^ 256; omega
  refine ⟨hleft', hright', ?_⟩
  rw [u256_mul_toNat, u256_mul_toNat, usub_toNat htime, usub_toNat hstart,
    Nat.mod_eq_of_lt hleft', Nat.mod_eq_of_lt hright']
  change _ < 2 ^ 256
  omega

def interpolationExpr : Expr :=
  .binary .div
    (.inRange (.uint ⟨256, by decide⟩) (.binary .add
      (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "feeLower")
        (.inRange (.uint ⟨256, by decide⟩)
          (.binary .sub (.var "end") (.var "timeToMaturity")))))
      (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "feeUpper")
        (.inRange (.uint ⟨256, by decide⟩)
          (.binary .sub (.var "timeToMaturity") (.var "start")))))))
    (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.var "end") (.var "start")))

theorem evalInterpolation {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lower upper time start finish : UInt256}
    (hlower : lower.toNat < 2 ^ 64) (hupper : upper.toNat < 2 ^ 64)
    (hfinish : finish.toNat < 2 ^ 32)
    (hstart : start.toNat ≤ time.toNat) (htime : time.toNat ≤ finish.toNat)
    (hwidth : start.toNat < finish.toNat)
    (hl : frame.locals.get? "feeLower" = some (.int lower.toNat))
    (hu : frame.locals.get? "feeUpper" = some (.int upper.toNat))
    (ht : frame.locals.get? "timeToMaturity" = some (.int time.toNat))
    (hs : frame.locals.get? "start" = some (.int start.toNat))
    (he : frame.locals.get? "end" = some (.int finish.toNat)) :
    evalExpr? cfg frame evm interpolationExpr =
      .ok (.int (interpolatedFee lower upper time start finish).toNat) := by
  have varEval {name : Ident} {word : UInt256}
      (hget : frame.locals.get? name = some (.int word.toNat)) :
      evalExpr? cfg frame evm (.var name) = .ok (.int word.toNat) := by
    simp only [evalExpr?, hget, EvalResult.ofOption]
  obtain ⟨hleft, hright, hsum⟩ := interpolationBounds hlower hupper hfinish hstart htime
  apply divSourceOk
    (checkedAddSourceOk
      (checkedMulSourceOk (varEval hl)
        (evalExpr_uint256_sub (varEval he) (varEval ht) htime) hleft)
      (checkedMulSourceOk (varEval hu)
        (evalExpr_uint256_sub (varEval ht) (varEval hs) hstart) hright) hsum)
    (evalExpr_uint256_sub (varEval he) (varEval hs) hwidth.le)
  intro hz
  have hn := congrArg UInt256.toNat hz
  rw [usub_toNat hwidth.le] at hn
  change finish.toNat - start.toNat = 0 at hn
  omega

def scaledSettlementFee (word : UInt256) (i : Nat) : UInt256 :=
  UInt256.mul (settlementFeeWord word i) (UInt256.ofNat 1000000000000)

theorem scaledSettlementFee_noOverflow (word : UInt256) (i : Nat) :
    (settlementFeeWord word i).toNat * (UInt256.ofNat 1000000000000).toNat < UInt256.size := by
  have h := settlementFeeWord_lt word i
  change _ < 2 ^ 16 at h
  change _ * 1000000000000 < 2 ^ 256
  omega

theorem scaledSettlementFee_lt (word : UInt256) (i : Nat) :
    (scaledSettlementFee word i).toNat < 2 ^ 64 := by
  have h := settlementFeeWord_lt word i
  change _ < 2 ^ 16 at h
  rw [scaledSettlementFee, u256_mul_toNat,
    Nat.mod_eq_of_lt (scaledSettlementFee_noOverflow word i)]
  change _ * 1000000000000 < 2 ^ 64
  omega

theorem evalScaledSettlementFee {frame : Frame} {evm : EVM.State} {id : UInt256}
    (i : Fin 7)
    (hget : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType)) :
    evalExpr? config frame evm (.binary .mul
      (.storage { base := "_marketState", steps :=
        [.field ("settlementFeeCbp" ++ toString i.val)] }) (.intLit 1000000000000)) =
      .ok (.int (scaledSettlementFee (marketFeeWord evm id) i.val).toNat) := by
  simp only [evalExpr_binary_nonshort (by decide : BinaryOp.mul ≠ .and)
      (by decide : BinaryOp.mul ≠ .or), evalMarketAliasFee i hget, evalExpr?,
    EvalResult.bind, bind, pure, evalBinaryOp?, scaledSettlementFee, u256_mul_toNat,
    Nat.mod_eq_of_lt (scaledSettlementFee_noOverflow (marketFeeWord evm id) i.val)]
  rfl

end Benchmarks.Midnight
