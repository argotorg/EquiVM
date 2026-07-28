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
-- theorem xxxSetValueBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
--     (hcode : I.code = xxxBytecode) (hsize : I.calldata.size < UInt256.size)
--     (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
--     (hsel : selIs I (xxxSelBytes 0)) (hAccounts : accountMapEquiv σ_evm σ_solm) :
--     runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := …

end Benchmarks.Xxx
