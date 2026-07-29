import Benchmarks.Xxx.Constructor
import Benchmarks.Xxx.Function   -- one import per transition's proof file
import Solm.Equiv

/-!
# Xxx correctness capstone (TEMPLATE)

Thin top-level: the dispatcher driver routes each selector to its per-function `…Body` lemma,
adds the shared revert paths (non-payable guard, no-dispatch), and packages the constructor with
the runtime target into the whole-contract equivalence.  Mirrors
`Benchmarks/Dss/Pot/Correct.lean` — copy that file's `NonPayable`/`NoDispatch`/
`NoSelectorMatches` scaffolding and rename.

After it compiles, verify axiom hygiene on the capstone: only the `Trusted.lean` selector
axioms and the standard Lean axioms may appear.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Xxx

-- theorem xxxNonPayable … (hwv : I.weiValue ≠ ⟨0⟩) :
--     runtimeEquivalenceFor config contract … := …   (Pot: potNonPayable)

-- theorem xxxNoDispatch … (hnm : ∀ i, i < nArms → (xxxSelBytes i == …) = false) :
--     runtimeEquivalenceFor config contract … := …   (Pot: potNoDispatch)

-- theorem xxxNoSelectorMatches … : ∀ i, i < nArms → … := by interval_cases i <;> simpa [selIs] …

-- theorem xxxCorrect : runtimeEquivalence config xxxBytecode contract := by
--   refine runtimeEquivalence.intro ?_
--   intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
--   by_cases hwv : I.weiValue = ⟨0⟩
--   · by_cases h0 : selIs I (xxxSelBytes 0)
--     · exact xxxSetValueBody hcode hsize hperm hwv h0 hAccounts
--     · by_cases h1 : selIs I (xxxSelBytes 1)
--       · exact xxxValueBody hcode hsize hperm hwv h1 hAccounts
--       · exact xxxNoDispatch hcode hsize hperm hwv (xxxNoSelectorMatches h0 h1) hAccounts
--   · exact xxxNonPayable hcode hwv

-- theorem xxxContractCorrect :
--     contractEquivalence config xxxCreationBytecode xxxBytecode contract :=
--   contractEquivalence.intro xxxConstructorCorrect xxxCorrect

end Benchmarks.Xxx
