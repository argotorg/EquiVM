import Benchmarks.Xxx.Trusted

/-!
# Xxx dispatcher walk (TEMPLATE)

Reach lemmas from the runtime entry to each selector arm, mirroring the compiled dispatcher's
binary-search/comparison tree.  This file is bytecode-driven: read the tree shape off the
disassembly (root `GT` split, per-group `EQ` chains), define per-group "reach arm j" lemmas, and
close each with symbolic stepping.

See `Benchmarks/Dss/Pot/Dispatch.lean` (`potReachG54Body` etc.) and
`Benchmarks/Dss/Jug/Dispatch.lean` for the full pattern, including:

- `xxxSelWord_eq_of_beq` — from `selIs I (xxxSelBytes k)` to the concrete selector word;
- `armSelNat`/`nthArmPc` bookkeeping over the arm list;
- `native_decide` for the concrete word comparisons;
- `xxxDispatch_none_nomatch` / `xxxDispatch_none_short` — Solm-side `dispatchMsg … = none`
  facts used by the no-dispatch branch of `Correct.lean`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Xxx

-- TODO: reach lemmas per dispatcher group, e.g.
-- theorem xxxReachArm (j : ℕ) (hj : j < nArms) (pc : UInt256) (hcode : I.code = xxxBytecode)
--     (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size) … : ∃ k C, RD xxxBytecode I g … := …

-- TODO: theorem xxxDispatch_none_short (h : I.calldata.size < 4) :
--     dispatchMsg contract I.calldata = none := …
-- TODO: theorem xxxDispatch_none_nomatch
--     (hnm : ∀ i, i < nArms → (xxxSelBytes i == I.calldata.extract 0 4) = false) :
--     dispatchMsg contract I.calldata = none := …

end Benchmarks.Xxx
