# Repository layout

```
EVM/            EVMLean glue (state, semantics, lemmas).
ABI/            ABI types, signatures, static words, encoder and decoder (on `Solm.Value`).
Solm/           Sol⁻: syntax, semantics, storage backends, refinement relation (`Refine.lean`),
                interpreter and differential tests (`Solm/STRUCTURE.md`).
Reasoning/      Lemmas about compiled bytecode: traces (`Reach`, `Trace`), memory, solc code
                shapes, ABI decoding, storage, the Sol⁻ coupling (`Reasoning/STRUCTURE.md`).
Examples/       Sol⁻ example proofs.          Benchmarks/   Sol⁻ benchmark proofs and scaffolds.
Proofs/         Properties of Sol⁻ specs.     Tests/        Sol⁻ differential tests and the pipeline test.
Solidity/       Solidity: syntax, elaboration, semantics, interpreter, theory, `Examples/`,
                `Test/` (the differential harness `solidity-diff`).
scripts/        Scaffolding and bytecode tooling.   Misc/   Prompts and the proof template.
```

Both spec languages share the EVM, the ABI and the storage backends of `Solm/Storage.lean`:
`Solidity/` imports `Solm` for those (values at the ABI/storage boundary are `Solm.Value`,
storage paths are `Solm.EvaledStorageRef`), never the other way round.

Lake: `Solm` and `Solidity` are declared by root module only, so `lake build Solidity` builds the
language, not its proofs; proofs are explicit targets (see `.github/workflows/ci.yml`).
