# Repository layout

Two spec languages share only what the compiler and the EVM fix: how data is encoded (the ABI)
and where data lives (storage slots). Everything a language names, types or evaluates belongs to
that language.

```
EVM/            EVMLean glue (state, semantics, lemmas).
ABI/            ABI types, signatures, static words, encoder and decoder.
Storage/        Storage locations and typed slot access (`Basic.lean`); solc's `bytes`/`string`
                representation and the layout record it plugs into (`SolcLayout.lean`).
Refinement/     Account-map equivalence (`AccountEquiv.lean`); return conventions, the Ξ result
                type and storage well-formedness (`Result.lean`).
EVMReasoning/   Lemmas about compiled bytecode, stated on bytes, words and the shared vocabulary
                above: traces, memory, stack, solc code shapes, ABI decoding, storage.
Solm/           Sol⁻: syntax, semantics, refinement relation, `Reasoning/` (its coupling lemmas),
                `Examples/`, `Benchmarks/`, `Proofs/`, `Template/`.
Solidity/       Solidity: syntax, elaboration, semantics, interpreter, theory, `Examples/`,
                `Test/` (the differential harness `solidity-diff`).
```

Dependency rules: `EVM` imports nothing of ours; `ABI` imports `EVM`; `Storage` and `Refinement`
import `EVM` and `ABI`; `EVMReasoning` imports those four; `Solm` and `Solidity` import everything
below them and never each other. Proofs of a language live under that language.

Lake: `Solm` and `Solidity` are declared by root module only, so `lake build Solm` builds the
language, not its proofs; proofs are explicit targets (see `.github/workflows/ci.yml`).

## Known violations, to be removed in the next pass

- `Storage/`, `ABI/Encode`, `ABI/Decode` and `EVMReasoning/{ABI,Storage}.lean` are typed on
  `Solm.Value`, and the layout record is keyed on Sol⁻'s `EvaledStorageRef`/`StorageType`. The
  next pass introduces `ABI.Value` (the ABI-encodable values) as the shared boundary type, makes
  the layout record generic in the path type, and states the `bytes`/`string` representation on
  locations; Sol⁻ then converts at its boundaries like Solidity already does.
- `Solidity/Examples/ERC20` imports `Solm.Examples.ERC20.Correct` for the bytecode traces, and the
  harness imports pinned bytecode from `Solm/Examples/*/Bytecode.lean`. Pinned bytecode belongs in
  a shared `Contracts/` tree; that move waits on restating the per-contract selector axioms on
  literal signature strings, since today they are phrased with Sol⁻'s `transitionSigStr`.
- The moved definitions keep aliases under their old `Solm.*` names (`export` in the stub modules
  `Solm/Storage.lean`, `Solm/SolidityLayout.lean`, `Solm/Equiv.lean`, `Solm/Semantics/Dispatch.lean`,
  `Solm/Behaviors.lean`), so Sol⁻ proofs did not change; new code uses `Storage.*`/`Refinement.*`.
