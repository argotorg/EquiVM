import Benchmarks.CompoundIII.Comet.WithdrawBaseMathModel
import Benchmarks.CompoundIII.Comet.SupplyBaseMathModel
import Benchmarks.CompoundIII.Comet.SignedPresentValueSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

-- Shared source composition for a signed balance and an unsigned delta.
def baseBalanceInt (subtract : Bool) (evm : EVM.State) (principal amount : UInt256) : Int :=
  if subtract then withdrawBaseBalanceInt evm principal amount
  else supplyBaseBalanceInt evm principal amount

def BaseBalanceFits (subtract : Bool) (evm : EVM.State) (principal amount : UInt256) : Prop :=
  -(2^103 : Int) < signed104 principal ∧ amount.toNat < 2^255 ∧
    -(2^255 : Int) ≤ baseBalanceInt subtract evm principal amount ∧
    baseBalanceInt subtract evm principal amount < (2^255 : Int)

instance (subtract : Bool) (evm : EVM.State) (principal amount : UInt256) :
    Decidable (BaseBalanceFits subtract evm principal amount) := by
  unfold BaseBalanceFits; infer_instance

theorem baseBalanceFits_sub (evm : EVM.State) (principal amount : UInt256) :
    BaseBalanceFits true evm principal amount ↔ WithdrawBaseBalanceFits evm principal amount := by
  simp only [BaseBalanceFits, baseBalanceInt, if_true, WithdrawBaseBalanceFits]
  constructor
  · intro h; exact ⟨h.1, h.2.1, h.2.2.1⟩
  · intro h
    refine ⟨h.1, h.2.1, h.2.2, ?_⟩
    have hh := (signedWord_bounds (signedPresentValueWord evm principal)).2
    rw [signedPresentValueWord_int evm principal h.1] at hh
    change signedPresentValueInt evm principal - Int.ofNat amount.toNat < _
    simp only [Int.ofNat_eq_natCast]
    omega

theorem baseBalanceFits_add (evm : EVM.State) (principal amount : UInt256) :
    BaseBalanceFits false evm principal amount ↔ SupplyBaseBalanceFits evm principal amount := by
  simp only [BaseBalanceFits, baseBalanceInt, Bool.false_eq_true, if_false, SupplyBaseBalanceFits]
  constructor
  · intro h; exact ⟨h.1, h.2.1, h.2.2.2⟩
  · intro h
    refine ⟨h.1, h.2.1, ?_, h.2.2⟩
    have hh := (signedWord_bounds (signedPresentValueWord evm principal)).1
    rw [signedPresentValueWord_int evm principal h.1] at hh
    change _ ≤ signedPresentValueInt evm principal + Int.ofNat amount.toNat
    simp only [Int.ofNat_eq_natCast]
    omega

def baseBalanceBlock (subtract : Bool) (principalName presentName castName balanceName : Ident) :
    List Stmt :=
  [.internalCall "presentValue" [.var principalName] presentName,
    .internalCall "signed256" [.var "amount"] castName,
    .letDecl balanceName (some (.elem (.int (.sint ⟨256, by decide⟩))))
      (.inRange (.sint ⟨256, by decide⟩)
        (.binary (if subtract then .sub else .add) (.var presentName) (.var castName)))]

def baseBalanceFrame (frame : Frame) (subtract : Bool) (evm : EVM.State)
    (principal amount : UInt256) (presentName castName balanceName : Ident) : Frame :=
  { frame with
    locals := ((frame.locals.insert presentName (.int (signedPresentValueInt evm principal))).insert
      castName (.int amount.toNat)).insert balanceName
        (.int (baseBalanceInt subtract evm principal amount)) }

theorem baseBalance_source (frame : Frame) (evm : EVM.State) (principal amount : UInt256)
    (subtract : Bool) (principalName presentName castName balanceName : Ident)
    (hpa : "amount" ≠ presentName) (hpc : presentName ≠ castName)
    (hc : frame.contract = contract)
    (hp : frame.locals.get? principalName = some (.int (signed104 principal)))
    (ha : frame.locals.get? "amount" = some (.int amount.toNat)) :
    ExecBlock config frame evm (baseBalanceBlock subtract principalName presentName castName balanceName)
      (if BaseBalanceFits subtract evm principal amount then
        .ok (baseBalanceFrame frame subtract evm principal amount presentName castName balanceName) evm
      else .reverted) := by
  simp only [baseBalanceFrame]
  have hpe : evalExpr? config frame evm (.var principalName) =
      .ok (.int (signed104 principal)) := by simp only [evalExpr?, hp, EvalResult.ofOption]
  have hcall := signedPresent_call frame evm principal _ presentName hc hpe
  let f1 : Frame := { frame with
    locals := frame.locals.insert presentName (.int (signedPresentValueInt evm principal)) }
  have hae : evalExpr? config f1 evm (.var "amount") = .ok (.int amount.toNat) := by
    simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, Ne.symm hpa, if_false]
    change EvalResult.ofOption .unboundVariable (frame.locals.get? "amount") = _
    rw [ha]; rfl
  by_cases hm : -(2^103 : Int) < signed104 principal
  · rw [if_pos hm] at hcall
    by_cases hcast : amount.toNat < 2^255
    · have hsign := signed256_call_ok f1 evm amount _ castName hc hae hcast
      let f2 : Frame := { f1 with locals := f1.locals.insert castName (.int amount.toNat) }
      have he : evalExpr? config f2 evm
          (.binary (if subtract then .sub else .add) (.var presentName) (.var castName)) =
          .ok (.int (baseBalanceInt subtract evm principal amount)) := by
        cases subtract <;>
          simp only [Bool.false_eq_true, if_false, if_true, evalExpr?, f2, f1,
            Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_iff_eq,
            Ne.symm hpc, if_false, if_true, EvalResult.ofOption, bind, EvalResult.bind,
            evalBinaryOp?, baseBalanceInt, withdrawBaseBalanceInt, supplyBaseBalanceInt,
            Int.ofNat_eq_natCast]
      by_cases hlo : -(2^255 : Int) ≤ baseBalanceInt subtract evm principal amount
      · by_cases hhi : baseBalanceInt subtract evm principal amount < (2^255 : Int)
        · rw [if_pos ⟨hm, hcast, hlo, hhi⟩]
          exact ExecBlock.consNormal hcall (ExecBlock.consNormal hsign
            (ExecBlock.consNormal (ExecStmt.letDecl (signedRangeSourceOk he hlo hhi)) ExecBlock.nil))
        · rw [if_neg (fun hf ↦ hhi hf.2.2.2)]
          exact ExecBlock.consNormal hcall (ExecBlock.consNormal hsign
            (ExecBlock.consRevert (ExecStmt.letDeclRevert
              (signedNarrowRangeSourceOverflow ⟨256, by decide⟩ he (by simpa using (not_lt.mp hhi))))))
      · rw [if_neg (fun hf ↦ hlo hf.2.2.1)]
        exact ExecBlock.consNormal hcall (ExecBlock.consNormal hsign
          (ExecBlock.consRevert (ExecStmt.letDeclRevert
            (signedNarrowRangeSourceUnderflow ⟨256, by decide⟩ he (by simpa using (not_le.mp hlo))))))
    · rw [if_neg (fun hf ↦ hcast hf.2.1)]
      exact ExecBlock.consNormal hcall
        (ExecBlock.consRevert (signed256_call_revert f1 evm amount _ castName hc hae hcast))
  · rw [if_neg hm] at hcall
    rw [if_neg (fun hf ↦ hm hf.1)]
    exact ExecBlock.consRevert hcall

end Benchmarks.CompoundIII.Comet
