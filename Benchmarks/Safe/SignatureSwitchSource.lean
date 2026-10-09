import Benchmarks.Safe.SignatureContext
import Benchmarks.Safe.SignatureApprovalSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: equality of two evaluated natural-number expressions.
theorem naturalEqSource {cfg frame evm lhs rhs} {a b : Nat}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg frame evm (.binary .eq lhs rhs) = .ok (.bool (decide (a = b))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  simp [EvalResult.bind, bind, evalBinaryOp?, Int.ofNat_eq_natCast, pure]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, Int.natCast_inj, decide_eq_true_eq]

-- LIBRARY CANDIDATE: strict comparison of two evaluated natural-number expressions.
theorem naturalGtSource {cfg frame evm lhs rhs} {a b : Nat}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg frame evm (.binary .gt lhs rhs) = .ok (.bool (decide (b < a))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  simp [EvalResult.bind, bind, evalBinaryOp?, Int.ofNat_eq_natCast, pure]

def signatureSelectedBody (v : UInt256) : List Stmt :=
  if v.toNat = 0 then signatureContractBody
  else if v.toNat = 1 then signatureApprovalBody
  else if v.toNat = 2 then signatureP256Body
  else if 30 < v.toNat then signatureEthBody
  else signatureRecoverBody (.var "dataHash") (.var "v")

theorem signatureSwitchSource {f : Frame} {evm : EVM.State} {v : UInt256} {result : ExecResult}
    (hv : f.locals["v"]? = some (uint256Value v))
    (hbody : ExecBlock config f evm (signatureSelectedBody v) result) :
    ExecStmt config f evm signatureLoopBody[4]! result := by
  have heq (n : Nat) : evalExpr? config f evm (eqE (.var "v") (.intLit (Int.ofNat n))) =
      .ok (.bool (decide (v.toNat = n))) :=
    naturalEqSource (evalLocalValue hv) (by simp [evalExpr?, pure])
  have hgt : evalExpr? config f evm (gtE (.var "v") (.intLit 30)) =
      .ok (.bool (decide (30 < v.toNat))) :=
    naturalGtSource (evalLocalValue hv) (by simp [evalExpr?, pure])
  by_cases h₀ : v.toNat = 0
  · exact .iteTrue (by simpa only [h₀, decide_true] using heq 0)
      (by simpa only [signatureSelectedBody, h₀, if_true] using hbody)
  apply ExecStmt.iteFalse (by simpa only [h₀, decide_false] using heq 0)
  apply execBlock_singleton
  by_cases h₁ : v.toNat = 1
  · exact .iteTrue (by simpa only [h₁, decide_true] using heq 1)
      (by simpa only [signatureSelectedBody, h₀, h₁, if_false, if_true] using hbody)
  apply ExecStmt.iteFalse (by simpa only [h₁, decide_false] using heq 1)
  apply execBlock_singleton
  by_cases h₂ : v.toNat = 2
  · exact .iteTrue (by simpa only [h₂, decide_true] using heq 2)
      (by simpa only [signatureSelectedBody, h₀, h₁, h₂, if_false, if_true] using hbody)
  apply ExecStmt.iteFalse (by simpa only [h₂, decide_false] using heq 2)
  apply execBlock_singleton
  by_cases hh : 30 < v.toNat
  · exact .iteTrue (by simpa only [hh, decide_true] using hgt)
      (by simpa only [signatureSelectedBody, h₀, h₁, h₂, hh, if_false, if_true] using hbody)
  · exact .iteFalse (by simpa only [hh, decide_false] using hgt)
      (by simpa only [signatureSelectedBody, h₀, h₁, h₂, hh, if_false] using hbody)

end Benchmarks.Safe
