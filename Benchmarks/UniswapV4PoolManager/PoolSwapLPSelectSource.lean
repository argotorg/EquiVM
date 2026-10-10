import Benchmarks.UniswapV4PoolManager.LPFeeOverrideSource
import Benchmarks.UniswapV4PoolManager.Slot0FeeSource
import Benchmarks.UniswapV4PoolManager.PoolSwapValues
import Benchmarks.UniswapV4PoolManager.PoolSwapSyntax

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapLPFeeWord (packed override : UInt256) : UInt256 :=
  if lpFeeIsOverride override then lpFeeRemoveOverride override else slot0FeeField packed 208

def poolSwapLPFeeValid (override : UInt256) : Prop :=
  lpFeeIsOverride override = true → (lpFeeRemoveOverride override).toNat ≤ 1000000
instance (override : UInt256) : Decidable (poolSwapLPFeeValid override) :=
  inferInstanceAs (Decidable (_ → _))

theorem poolSwapLPFeeWord_bound (packed override : UInt256) : (poolSwapLPFeeWord packed override).toNat < 2^24 := by
  unfold poolSwapLPFeeWord
  split
  · exact lpFeeRemoveOverride_bound override
  · exact slot0FeeField_bound packed 208

def poolSwapLPSelectFrame (f : Frame) (packed override : UInt256) : Frame :=
  if lpFeeIsOverride override then
    wordLocal (wordLocal f "overrideFee" (lpFeeRemoveOverride override)) "lpFee" (lpFeeRemoveOverride override)
  else wordLocal (wordLocal f "storedFee" (slot0FeeField packed 208)) "lpFee" (slot0FeeField packed 208)

theorem poolSwapLPSelectFrame_get (f : Frame) (packed override : UInt256) (key : Ident)
    (ho : ("overrideFee" == key) = false) (hs : ("storedFee" == key) = false) (hl : ("lpFee" == key) = false) :
    (poolSwapLPSelectFrame f packed override).locals.get? key = f.locals.get? key := by
  unfold poolSwapLPSelectFrame
  split <;> simp only [wordLocal_get, ho, hs, hl, Bool.false_eq_true, if_false]

theorem poolSwapLPSelectFrame_fee (f : Frame) (packed override : UInt256) :
    (poolSwapLPSelectFrame f packed override).locals.get? "lpFee" =
      some (.int (Int.ofNat (poolSwapLPFeeWord packed override).toNat)) := by
  unfold poolSwapLPSelectFrame poolSwapLPFeeWord
  split <;> exact store_get_self _ _ _

theorem poolSwapLPSelectFrame_contract (f : Frame) (packed override : UInt256) :
    (poolSwapLPSelectFrame f packed override).contract = f.contract := by
  unfold poolSwapLPSelectFrame
  split <;> rfl

theorem poolSwapLPSelectSource {f : Frame} {evm : State} {packed : UInt256} {p : PoolSwapParamsWords} {old : Value}
    (hf : f.contract = contract) (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hs : f.locals.get? "slot0Start" = some (wordBytes32Value packed))
    (hflag : f.locals.get? "__c6" = some (.bool (lpFeeIsOverride p.lpFeeOverride)))
    (hlp : f.locals.get? "lpFee" = some old) (hc : p.lpFeeOverride.toNat < 2^24) :
    ExecStmt config f evm poolSwapFunction.body[20]!
      (if poolSwapLPFeeValid p.lpFeeOverride then .ok (poolSwapLPSelectFrame f packed p.lpFeeOverride) evm else .reverted) := by
  have hg := evalLocalValue (cfg := config) (evm := evm) hflag
  cases he : lpFeeIsOverride p.lpFeeOverride
  · have hv : poolSwapLPFeeValid p.lpFeeOverride := by simp only [poolSwapLPFeeValid, he, Bool.false_eq_true, false_implies]
    rw [if_pos hv, poolSwapLPSelectFrame, he]
    apply ExecStmt.iteFalse (by simpa only [he] using hg)
    have hcall := slot0GetLPFeeCall hf (evalLocalValue (evm := evm) hs) "storedFee"
    exact ExecBlock.consNormal hcall (execBlock_singleton (ExecStmt.assign (evalLocalValue (store_get_self _ _ _))
      (assignLocalValue ((store_get_ne _ _ (by decide : ("storedFee" == "lpFee") = false)).trans hlp))))
  · have hcall := lpFeeOverrideValidateCall hf hc
      (evalStructField (evm := evm) (field := "lpFeeOverride") (evalLocalValue hp) rfl) "overrideFee"
    by_cases hv : (lpFeeRemoveOverride p.lpFeeOverride).toNat ≤ 1000000
    · rw [if_pos hv] at hcall
      rw [if_pos (show poolSwapLPFeeValid p.lpFeeOverride from fun _ => hv), poolSwapLPSelectFrame, he]
      apply ExecStmt.iteTrue (by simpa only [he] using hg)
      exact ExecBlock.consNormal hcall (execBlock_singleton (ExecStmt.assign (evalLocalValue (store_get_self _ _ _))
        (assignLocalValue ((store_get_ne _ _ (by decide : ("overrideFee" == "lpFee") = false)).trans hlp))))
    · rw [if_neg hv] at hcall
      rw [if_neg (show ¬poolSwapLPFeeValid p.lpFeeOverride from fun hh => hv (hh he))]
      exact ExecStmt.iteTrue (by simpa only [he] using hg) (ExecBlock.consRevert hcall)

end Benchmarks.UniswapV4PoolManager
