import Reasoning.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: Reasoning.Dispatch — successful named dispatch also applies
-- to contracts that provide a receive function or a fallback.
theorem dispatchMsg_of_selectorDispatch {C : ContractDecl} {cd : ByteArray}
    {t : TransitionDecl} (h : selectorDispatchMsg C cd = some t) :
    dispatchMsg C cd = some t := by
  simp only [dispatchMsg, h]

-- LIBRARY CANDIDATE: Reasoning.Dispatch — a unique matching member dispatches
-- without requiring the caller to enumerate all earlier nonmatching selectors.
theorem dispatchList_eq_some_of_unique {ts : List TransitionDecl} {cd : ByteArray}
    {t : TransitionDecl} (hmem : t ∈ ts) (hhit : (selectorOf t == cd.extract 0 4) = true)
    (hunique : ∀ t' ∈ ts, (selectorOf t' == cd.extract 0 4) = true → t' = t) :
    dispatchList ts cd = some t := by
  induction ts with
  | nil => cases hmem
  | cons head tail ih =>
    rw [dispatchList_cons]
    by_cases hhead : (selectorOf head == cd.extract 0 4) = true
    · rw [if_pos hhead, hunique head (by simp only [List.mem_cons, true_or]) hhead]
    · rw [if_neg hhead]
      apply ih
      · rcases List.mem_cons.mp hmem with heq | htail
        · subst head
          exact False.elim (hhead hhit)
        · exact htail
      · intro t' ht'
        exact hunique t' (List.mem_cons_of_mem _ ht')

end Benchmarks.CompoundIII.Comet
