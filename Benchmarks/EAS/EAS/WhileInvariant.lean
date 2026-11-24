import Benchmarks.EAS.EAS.Common

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES Reasoning.SteleBody.execWhile_var to state changes, relational invariants, and exceptional exits.
theorem execWhile_invariant {cfg : Config} {contract : ContractDecl} {imms : Store}
    {cond : Expr} {body : Body} {bound : Nat}
    (Inv : Nat → Store → EVM.State → Prop) (Post : Store → EVM.State → Prop) (Rev Static : Prop)
    (hguard : ∀ i locals evm, i ≤ bound → Inv i locals evm →
      evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm cond =
        .ok (.bool (decide (i < bound))))
    (hend : ∀ locals evm, Inv bound locals evm → Post locals evm)
    (hstep : ∀ i locals evm, i < bound → Inv i locals evm →
      (∃ locals' evm',
        ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm body
          (.ok {contract := contract, locals := locals', immutables := imms} evm') ∧ Inv (i + 1) locals' evm') ∨
      (ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm body .reverted ∧ Rev) ∨
      (ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm body .staticViolation ∧ Static)) :
    ∀ n i locals evm, i + n = bound → Inv i locals evm →
      (∃ locals' evm',
        ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm (.while cond body)
          (.ok {contract := contract, locals := locals', immutables := imms} evm') ∧ Post locals' evm') ∨
      (ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm (.while cond body) .reverted ∧ Rev) ∨
      (ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm (.while cond body) .staticViolation ∧ Static) := by
  intro n
  induction n with
  | zero =>
    intro i locals evm hn h
    have hi : i = bound := by omega
    subst i
    refine Or.inl ⟨locals, evm, ExecStmt.whileFalse ?_, hend locals evm h⟩
    simpa only [decide_eq_false (Nat.lt_irrefl bound)] using hguard bound locals evm (by omega) h
  | succ n ih =>
    intro i locals evm hn h
    have hi : i < bound := by omega
    have hc : evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm cond = .ok (.bool true) := by
      simpa only [decide_eq_true hi] using hguard i locals evm (by omega) h
    obtain (⟨locals', evm', hs, h'⟩ | ⟨hs, hr⟩ | ⟨hs, hr⟩) := hstep i locals evm hi h
    · obtain (⟨locals'', evm'', hs', hf⟩ | ⟨hs', hr⟩ | ⟨hs', hr⟩) := ih (i + 1) locals' evm' (by omega) h'
      · exact Or.inl ⟨locals'', evm'', ExecStmt.whileTrue hc hs hs', hf⟩
      · exact Or.inr (Or.inl ⟨ExecStmt.whileTrue hc hs hs', hr⟩)
      · exact Or.inr (Or.inr ⟨ExecStmt.whileTrue hc hs hs', hr⟩)
    · exact Or.inr (Or.inl ⟨ExecStmt.whileRevert hc hs, hr⟩)
    · exact Or.inr (Or.inr ⟨ExecStmt.whileStatic hc hs, hr⟩)

end Benchmarks.EAS.EAS
