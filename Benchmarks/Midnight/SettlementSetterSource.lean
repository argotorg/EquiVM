import Benchmarks.Midnight.RoleSource
import Benchmarks.Midnight.MaxSettlementFee
import Benchmarks.Midnight.PackedUint16
import Benchmarks.Midnight.ModArithmetic

/-! Common guards and the basis-point conversion for settlement-fee setters. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def settlementFeeQuotient (value : UInt256) : UInt256 :=
  UInt256.div value (UInt256.ofNat 1000000000000)

theorem settlementFeeQuotient_nat (value : UInt256) :
    (settlementFeeQuotient value).toNat = value.toNat / 1000000000000 := by
  exact udiv_toNat _ _

theorem settlementFeeQuotient_lt (value : UInt256) (i : Fin 7)
    (hbound : value.toNat ≤ maxSettlementFeeValue i) :
    (settlementFeeQuotient value).toNat < 2 ^ 16 := by
  rw [settlementFeeQuotient_nat]
  have := maxFeeValue_bound i
  omega

theorem evalSettlementIndexBound {cfg : Config} {frame : Frame} {evm : EVM.State} {index : Nat}
    (hget : frame.locals.get? "index" = some (.int index)) :
    evalExpr? cfg frame evm (.binary .le (.var "index") (.intLit 6)) =
      .ok (.bool (decide (index ≤ 6))) := by
  simp only [evalExpr?, hget, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?]
  norm_cast

theorem evalSettlementBound {cfg : Config} {frame : Frame} {evm : EVM.State}
    {value : UInt256} {i : Fin 7}
    (hget : frame.locals.get? "newSettlementFee" = some (.int value.toNat))
    (hcap : frame.locals.get? "__c0" = some (.int (maxSettlementFeeValue i))) :
    evalExpr? cfg frame evm (.binary .le (.var "newSettlementFee") (.var "__c0")) =
      .ok (.bool (decide (value.toNat ≤ maxSettlementFeeValue i))) := by
  simp only [evalExpr?, hget, hcap, EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp?]
  norm_cast

theorem evalSettlementMultiple {cfg : Config} {frame : Frame} {evm : EVM.State} {value : UInt256}
    (hget : frame.locals.get? "newSettlementFee" = some (.int value.toNat)) :
    evalExpr? cfg frame evm
      (.binary .eq (.binary .mod (.var "newSettlementFee") (.intLit 1000000000000)) (.intLit 0)) =
      .ok (.bool (decide (value.toNat % 1000000000000 = 0))) := by
  simp only [evalExpr?, hget, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?,
    show (1000000000000 : Int) ≠ 0 from by decide, if_false,
    Reasoning.VyperDispatch.value_int_beq]
  norm_cast

theorem evalSettlementCast {cfg : Config} {frame : Frame} {evm : EVM.State}
    {value : UInt256} (i : Fin 7)
    (hget : frame.locals.get? "newSettlementFee" = some (.int value.toNat))
    (hbound : value.toNat ≤ maxSettlementFeeValue i) :
    evalExpr? cfg frame evm
      (.cast (.binary .div (.var "newSettlementFee") (.intLit 1000000000000))
        (.elem (.int packedUInt16Int))) =
      .ok (.int (Int.ofNat (settlementFeeQuotient value).toNat)) := by
  have hdiv : evalExpr? cfg frame evm
      (.binary .div (.var "newSettlementFee") (.intLit 1000000000000)) =
      .ok (.int (Int.ofNat (settlementFeeQuotient value).toNat)) := by
    simp only [evalExpr?, hget, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?,
      show (1000000000000 : Int) ≠ 0 from by decide, if_false, settlementFeeQuotient_nat]
    norm_cast
  have hc := evalExpr_cast_int (intType := packedUInt16Int) hdiv
  have hq := settlementFeeQuotient_lt value i hbound
  change _ = EvalResult.ok (Value.int (Int.ofNat (settlementFeeQuotient value).toNat % 65536)) at hc
  have hn : 0 ≤ Int.ofNat (settlementFeeQuotient value).toNat := Int.natCast_nonneg _
  have hlt : Int.ofNat (settlementFeeQuotient value).toNat < 65536 := Int.ofNat_lt.mpr hq
  rw [Int.emod_eq_of_lt hn hlt] at hc
  exact hc

end Benchmarks.Midnight
