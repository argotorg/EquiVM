import Benchmarks.Xxx.Dispatch

/-!
# Xxx `setValue(uint256)` (TEMPLATE — one file per transition, named after it)

Per-function pipeline: calldata-decode facts, the reach lemma into this selector's arm, the EVM
trace through the body, the Solm-side body evaluation, and the `…Body` theorem consumed by
`Correct.lean`.  Big functions split the middle parts across `<Fn>Trace*`/`<Fn>Source*`/
`<Fn>EVM*` files (see `Benchmarks/Dss/Pot/Drip*` or `Benchmarks/Dss/Cat/Bite*`).

Name every helper with the function prefix (`xxxSetValueKey`, not `key`): generic names collide
at the `Correct.lean` import join when several functions are proved in parallel sessions.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Xxx

/-! ## Calldata decoding -/

-- theorem xxxDecode_setValue_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
--     decodeCalldataWithMode config.abiDecodeMode (setValueTransition.params.map Param.name)
--       (transitionSignature setValueTransition).paramTypes I.calldata =
--         some ((∅ : Store).insert "data" (.int … (calldataWord I.calldata 4) …)) := …

-- theorem xxxDecode_setValue_none_short {I : ExecutionEnv}
--     (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) : … = none := …

/-! ## Runtime trace + body theorem -/

-- theorem xxxReachSetValueBody … :
--     ∃ k C, RD xxxBytecode I g (initState …) ⟨armPc⟩ [xxxSelWord I] solcFreePtrMem … := …

-- The theorem `Correct.lean` consumes (fixed signature shape):
-- theorem xxxSetValueBody {σ σ₀ A I} {g : UInt256}
--     (hcode : I.code = xxxBytecode) (hsize : I.calldata.size < UInt256.size)
--     (hwv : I.weiValue = ⟨0⟩)
--     (hsel : selIs I (xxxSelBytes 0)) :
--     runtimeEquivalenceFor config contract σ σ₀ g A I := …
--
-- There is no `I.perm = true` hypothesis: the body may run in static mode (STATICCALL).
-- The trace segment holding a path's first SSTORE / LOG / value-CALL concludes
--   (I.perm = true ∧ <usual RD>) ∨ (I.perm = false ∧ RDstatic code g s0)
-- by `by_cases hperm` and `RD.sstoreStatic` / `RD.log*Static` / `RD.callValueStatic` on the false
-- side; callers project with `permSplit_true` / `permSplit_false`.  The false side's Solm body is
-- the success derivation cut at that statement with its `*Static` rule (e.g.
-- `ExecBlock.consStatic (ExecStmt.assignStatic …)`), closed by `RDstatic.reEquivStaticHalt`.

end Benchmarks.Xxx
