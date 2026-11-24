import Benchmarks.EAS.EAS.WhileInvariant

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES execWhile_invariant to a decreasing rank and a successful break exit.
theorem execWhile_true_rank {cfg : Config} {contract : ContractDecl} {imms : Store} {body : Body}
    (Inv : Nat → Store → EVM.State → Prop) (Post : Store → EVM.State → Prop) (Rev Static : Prop)
    (hstep : ∀ n L e, Inv n L e →
      (∃ L' e', ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} e body
        (.break {contract := contract,locals := L',immutables := imms} e') ∧ Post L' e') ∨
      (∃ n' L' e', n' < n ∧ ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} e body
        (.ok {contract := contract,locals := L',immutables := imms} e') ∧ Inv n' L' e') ∨
      (ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} e body .reverted ∧ Rev) ∨
      (ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} e body .staticViolation ∧ Static)) :
    ∀ n L e, Inv n L e →
      (∃ L' e', ExecStmt fork cfg {contract := contract,locals := L,immutables := imms} e (.while (.boolLit true) body)
        (.ok {contract := contract,locals := L',immutables := imms} e') ∧ Post L' e') ∨
      (ExecStmt fork cfg {contract := contract,locals := L,immutables := imms} e (.while (.boolLit true) body) .reverted ∧ Rev) ∨
      (ExecStmt fork cfg {contract := contract,locals := L,immutables := imms} e (.while (.boolLit true) body) .staticViolation ∧ Static) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro L e hv
    have hc : evalExpr? cfg {contract := contract,locals := L,immutables := imms} e (.boolLit true) = .ok (.bool true) := by simp only [evalExpr?,pure]
    rcases hstep n L e hv with ⟨L',e',hb,hpost⟩ | ⟨n',L',e',hlt,hb,hv'⟩ | ⟨hb,hr⟩ | ⟨hb,hr⟩
    · exact Or.inl ⟨L',e',ExecStmt.whileBreak hc hb,hpost⟩
    · rcases ih n' hlt L' e' hv' with ⟨L'',e'',hw,hpost⟩ | ⟨hw,hr⟩ | ⟨hw,hr⟩
      · exact Or.inl ⟨L'',e'',ExecStmt.whileTrue hc hb hw,hpost⟩
      · exact Or.inr (Or.inl ⟨ExecStmt.whileTrue hc hb hw,hr⟩)
      · exact Or.inr (Or.inr ⟨ExecStmt.whileTrue hc hb hw,hr⟩)
    · exact Or.inr (Or.inl ⟨ExecStmt.whileRevert hc hb,hr⟩)
    · exact Or.inr (Or.inr ⟨ExecStmt.whileStatic hc hb,hr⟩)

end Benchmarks.EAS.EAS
