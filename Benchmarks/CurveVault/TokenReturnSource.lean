import Benchmarks.CurveVault.BoolCalls

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

abbrev vaultTokenReturnSizeExpr : Expr :=
  .binary .eq (.arrayLength .localVar {base := "returned", steps := []}) (.intLit 0)

abbrev vaultTokenReturnStmt : Stmt :=
  .ite vaultTokenReturnSizeExpr
    [.require (.binary .gt (.extCodeSize (.var "token")) (.intLit 0))]
    [.letDecl "transferred" (some (.elem .bool)) (.abiDecode (.elem .bool) (.var "returned")),
      .require (.var "transferred")]

def vaultTokenReturnAccepted (σ : AccountMap) (token : UInt256) (out : ByteArray) : Prop :=
  (out.size = 0 ∧ extCodeSizeWord σ token ≠ ⟨0⟩) ∨ (32 ≤ out.size ∧ retWord out = ⟨1⟩)

theorem vaultTokenReturnSizeEval (evm : State) (locals : Store) (out : ByteArray)
    (hret : locals.get? "returned" = some (.bytes out)) :
    evalExpr? config {contract := contract, locals := locals} evm vaultTokenReturnSizeExpr =
      .ok (.bool (decide (out.size = 0))) := by
  simp only [vaultTokenReturnSizeExpr, evalExpr?, readLocalPath?, hret, evalBinaryOp?,
    EvalResult.bind, pure, bind, value_int_beq]
  have heq : (Int.ofNat out.size = 0) ↔ out.size = 0 := Int.ofNat_inj
  simp only [heq]

theorem vaultTokenReturnDecode (evm : State) (locals : Store) (out : ByteArray) (value : Bool)
    (hret : locals.get? "returned" = some (.bytes out))
    (hdecode : ABI.decodeReturnValueWithMode? .vyper (.elem .bool) out = some (.bool value)) :
    evalExpr? config {contract := contract, locals := locals} evm (.abiDecode (.elem .bool) (.var "returned")) =
      .ok (.bool value) := by
  rw [evalExpr?, evalExpr?]
  simp only [hret, EvalResult.ofOption, EvalResult.bind, bind, pure]
  change (match ABI.decodeReturnValueWithMode? .vyper (.elem .bool) out with
    | some decoded => EvalResult.ok decoded | none => EvalResult.revert) = _
  rw [hdecode]

theorem vaultTokenReturnDecodeRevert (evm : State) (locals : Store) (out : ByteArray)
    (hret : locals.get? "returned" = some (.bytes out))
    (hdecode : ABI.decodeReturnValueWithMode? .vyper (.elem .bool) out = none) :
    evalExpr? config {contract := contract, locals := locals} evm (.abiDecode (.elem .bool) (.var "returned")) =
      .revert := by
  rw [evalExpr?, evalExpr?]
  simp only [hret, EvalResult.ofOption, EvalResult.bind, bind, pure]
  change (match ABI.decodeReturnValueWithMode? .vyper (.elem .bool) out with
    | some decoded => EvalResult.ok decoded | none => EvalResult.revert) = _
  rw [hdecode]

theorem vaultTokenReturnSourceSuccess {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (locals : Store) (token : UInt256) (out : ByteArray)
    (ht : locals.get? "token" = some (.address (AccountAddress.ofUInt256 token)))
    (hret : locals.get? "returned" = some (.bytes out)) (haccept : vaultTokenReturnAccepted σ token out) :
    ∃ locals', ExecStmt fork config {contract := contract, locals := locals} evm vaultTokenReturnStmt
      (.ok {contract := contract, locals := locals'} evm) := by
  have hsize := vaultTokenReturnSizeEval evm locals out hret
  rcases haccept with ⟨hempty, hcode⟩ | ⟨h32, hword⟩
  · refine ⟨locals, ExecStmt.iteTrue (by simpa only [hempty, decide_true] using hsize) ?_⟩
    apply ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil
    have hguard := evalExpr_codeGuard_of_accounts_eq (cfg := config)
      (frame := {contract := contract, locals := locals}) hs.accounts rfl
      (show evalExpr? config {contract := contract, locals := locals} evm (.var "token") =
        .ok (.address (AccountAddress.ofUInt256 token)) from by rw [evalExpr?]; simp only [ht, EvalResult.ofOption])
    have hpos : 0 < (extCodeSizeWord σ token).toNat := by
      by_contra hn
      exact hcode (uint256_toNat_eq_zero (by omega))
    simpa only [hpos, decide_true] using hguard
  · refine ⟨locals.insert "transferred" (.bool true), ExecStmt.iteFalse
      (by simpa only [show ¬ out.size = 0 by omega, decide_false] using hsize) ?_⟩
    apply ExecBlock.consNormal (ExecStmt.letDecl
      (vaultTokenReturnDecode evm locals out true hret (decodeReturn_vyper_bool_ok out h32 true hword)))
    exact ExecBlock.consNormal (ExecStmt.requireTrue (by simp [evalExpr?, EvalResult.ofOption])) ExecBlock.nil

theorem vaultTokenReturnSourceRevert {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (locals : Store) (token : UInt256) (out : ByteArray)
    (ht : locals.get? "token" = some (.address (AccountAddress.ofUInt256 token)))
    (hret : locals.get? "returned" = some (.bytes out)) (hreject : ¬ vaultTokenReturnAccepted σ token out) :
    ExecStmt fork config {contract := contract, locals := locals} evm vaultTokenReturnStmt .reverted := by
  have hsize := vaultTokenReturnSizeEval evm locals out hret
  by_cases hempty : out.size = 0
  · have hcode : extCodeSizeWord σ token = ⟨0⟩ := by
      by_contra hn
      exact hreject (Or.inl ⟨hempty, hn⟩)
    apply ExecStmt.iteTrue (by simpa only [hempty, decide_true] using hsize)
    apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
    have hguard := evalExpr_codeGuard_of_accounts_eq (cfg := config)
      (frame := {contract := contract, locals := locals}) hs.accounts rfl
      (show evalExpr? config {contract := contract, locals := locals} evm (.var "token") =
        .ok (.address (AccountAddress.ofUInt256 token)) from by rw [evalExpr?]; simp only [ht, EvalResult.ofOption])
    rw [hcode] at hguard
    exact hguard
  · apply ExecStmt.iteFalse (by simpa only [hempty, decide_false] using hsize)
    by_cases h32 : 32 ≤ out.size
    · have hone : retWord out ≠ ⟨1⟩ := fun hw => hreject (Or.inr ⟨h32, hw⟩)
      by_cases hzero : retWord out = ⟨0⟩
      · apply ExecBlock.consNormal (ExecStmt.letDecl
          (vaultTokenReturnDecode evm locals out false hret (decodeReturn_vyper_bool_ok out h32 false hzero)))
        exact ExecBlock.consRevert (ExecStmt.requireFalse (by simp [evalExpr?, EvalResult.ofOption]))
      · exact ExecBlock.consRevert (ExecStmt.letDeclRevert
          (vaultTokenReturnDecodeRevert evm locals out hret (decodeReturn_vyper_bool_noncanon out h32 hzero hone)))
    · exact ExecBlock.consRevert (ExecStmt.letDeclRevert
        (vaultTokenReturnDecodeRevert evm locals out hret (decodeReturn_vyper_bool_short out (by omega))))

end Benchmarks.CurveVault
