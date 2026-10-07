import Benchmarks.Xxx.Constructor
import Benchmarks.Xxx.Function   -- one import per transition's proof file
import Solm.Refine

/-!
# Xxx correctness capstone (TEMPLATE)

Thin top-level: the dispatcher driver routes each selector to its per-function `…Body` lemma,
adds the shared revert paths (non-payable guard, no-dispatch), and packages the constructor with
the runtime target into the whole-contract equivalence.  Mirrors
`Benchmarks/Dss/Pot/Correct.lean` — copy that file's `NonPayable`/`NoDispatch`/
`NoSelectorMatches` scaffolding and rename.

After it compiles, verify axiom hygiene on the capstone. The expected footprint consists of standard
Lean axioms and documented `native_decide` evaluation facts.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Xxx

-- theorem xxxNonPayable … (hwv : I.weiValue ≠ ⟨0⟩) :
--     runtimeRefinementFor config contract … := …   (Pot: potNonPayable)

-- theorem xxxNoDispatch … (hnm : ∀ i, i < nArms → (xxxSelBytes i == …) = false) :
--     runtimeRefinementFor config contract … := …   (Pot: potNoDispatch)

-- theorem xxxNoSelectorMatches … : ∀ i, i < nArms → … := by interval_cases i <;> simpa [selIs] …

-- theorem xxxCorrect : runtimeRefinement config xxxBytecode contract := by
--   refine runtimeRefinement.intro ?_
--   intro σ σ₀ g A I hcode hsize
--   by_cases hwv : I.weiValue = ⟨0⟩
--   · by_cases h0 : selIs I (xxxSelBytes 0)
--     · exact xxxSetValueBody hcode hsize hwv h0
--     · by_cases h1 : selIs I (xxxSelBytes 1)
--       · exact xxxValueBody hcode hsize hwv h1
--       · exact xxxNoDispatch hcode hsize hwv (xxxNoSelectorMatches h0 h1)
--   · exact xxxNonPayable hcode hwv

-- theorem xxxContractCorrect :
--     contractRefinement config xxxCreationBytecode contract :=
--   contractRefinement.of_constant xxxConstructorCorrect xxxCorrect

end Benchmarks.Xxx
