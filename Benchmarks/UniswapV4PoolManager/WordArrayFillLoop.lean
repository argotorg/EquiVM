import Benchmarks.UniswapV4PoolManager.WordArrayABI
import Benchmarks.UniswapV4PoolManager.LocalArray

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: fill a local array using a state-preserving, invariant-preserving body.
theorem wordArrayFillLoop {cfg : Config} {CDecl : ContractDecl} {evm : EVM.State} {imms : Store}
    {cond : Expr} {body : List Stmt} {values : Nat → UInt256} {n : Nat}
    {Inv : List Value → Nat → Store → Prop}
    (condEval : ∀ locals res i, Inv res i locals →
      evalExpr? cfg {contract := CDecl, locals := locals, immutables := imms} evm cond =
        .ok (.bool (decide (i < n))))
    (resultGet : ∀ locals res i, Inv res i locals → locals.get? "result" = some (.array res))
    (bodyStep : ∀ locals res i, Inv res i locals → i < n → res.length = n →
      ∃ locals', ExecBlock cfg {contract := CDecl, locals := locals, immutables := imms} evm body
        (.ok {contract := CDecl, locals := locals', immutables := imms} evm) ∧
        Inv (res.set i (wordBytes32Value (values i))) (i+1) locals')
    (remaining : Nat) :
    ∀ locals res i, Inv res i locals → i + remaining = n → res.length = n →
      (∀ j, j < i → res[j]? = some (wordBytes32Value (values j))) →
      ∃ locals', ExecStmt cfg {contract := CDecl, locals := locals, immutables := imms}
        evm (.while cond body) (.ok {contract := CDecl, locals := locals', immutables := imms} evm) ∧
        locals'.get? "result" = some (.array (wordArrayValues values 0 n)) := by
  induction remaining with
  | zero =>
      intro locals res i hl hi hr hp
      have hin : i = n := by omega
      have he : res = wordArrayValues (values) 0 n := by
        apply List.ext_getElem?
        intro j
        by_cases hj : j < n
        · rw [hp j (by omega), wordArrayValues_getElem _ _ _ _ hj, Nat.zero_add]
        · rw [List.getElem?_eq_none (by omega),
            List.getElem?_eq_none (by rw [wordArrayValues_length]; omega)]
      refine ⟨locals, .whileFalse ?_, ?_⟩
      · simpa only [hin, lt_self_iff_false, decide_false] using condEval locals res i hl
      · simpa only [he] using resultGet locals res i hl
  | succ remaining ih =>
      intro locals res i hl hi hr hp
      obtain ⟨next, hs, hl'⟩ := bodyStep locals res i hl (by omega) hr
      have hp' : ∀ j, j < i+1 →
          (res.set i (wordBytes32Value (values i)))[j]? =
            some (wordBytes32Value (values j)) := by
        intro j hj
        by_cases he : i = j
        · subst j; exact List.getElem?_set_self (by omega)
        · rw [List.getElem?_set_ne he]
          exact hp j (by omega)
      obtain ⟨last, hw, hlast⟩ := ih next _ (i+1) hl' (by omega)
        (by simpa only [List.length_set] using hr) hp'
      refine ⟨last, .whileTrue ?_ hs hw, hlast⟩
      simpa only [show i < n by omega, decide_true] using condEval locals res i hl

end Benchmarks.UniswapV4PoolManager
