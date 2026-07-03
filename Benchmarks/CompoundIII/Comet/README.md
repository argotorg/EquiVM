# Compound III Comet Benchmark

Source:
[`Benchmarks/CompoundIII/contracts/CometWithExtendedAssetList.sol`](../contracts/CometWithExtendedAssetList.sol)
from `compound-finance/comet` main branch commit
`f766f51583c23acc33b2a7824654ef2029a96804`.

Compiled with solc `0.8.15`, optimizer enabled, optimizer runs `1`, `via-ir`, and metadata hash
disabled. See [`Benchmarks/CompoundIII/README.md`](../README.md) for the full source and compiler
provenance.

Artifacts:

- `creation.hex`: optimized creation bytecode, 21528 bytes, sha256
  `3ccb8ad86cc5df26f3883ac1d48efb6579d474a1bce1524488fca81c48d90856`
- `runtime.hex`: optimized deployed runtime bytecode, 18655 bytes, sha256
  `3847d85dd1276299a127c14489368e18cce2eca4b5196ff9e4fae9bd661ac38d`
- `CometWithExtendedAssetList.abi.json`: ABI emitted by solc, sha256
  `4a24ffd74dcebbc275639465660d52d242da6e4511de7c13f1802c54d136f801`
- `CometWithExtendedAssetList.storage.json`: storage layout emitted by solc, sha256
  `a956223d75ab0e3be98445030d78ca8bf8c45bb7634fe1de9952448a504b9b25`
- `CometWithExtendedAssetList.sol.ast.json`: AST JSON emitted by solc, sha256
  `a31fef5398a6bd719cb87df6ffcdb2a36fffc94ffe506b6f9842bac3996174bd`
- `Bytecode.lean`: optimized creation/runtime bytecode as Lean `ByteArray`s plus `valid_jumps`
  facts.
- `Immutables.lean`: explicit immutable values for the stored solc runtime template.
- `Spec.lean`: Solm AST scaffold with ABI surface, solc storage layout, explicit runtime-template
  immutables, and the payable delegate-call fallback.
- `SpecSyntax.lean`: syntax-side wrapper checked definitionally against the AST scaffold.
- `Constructor.lean`: constructor status note. It deliberately does not state a
  `constructorEquivalence` theorem for the unpatched runtime template.
- `Correct.lean`: runtime-template equivalence target, currently `sorry`.

Main source sha256:
`c9099e56eda092fd0150005706edf086723899afb102f164b60ad1f36a426961`.

Status:

- The stored `runtime.hex`/`cometBytecode` is solc's unpatched `--bin-runtime` template. Its
  immutable references are represented explicitly in `Immutables.lean` as zero-valued template
  slots.
- The payable fallback path is represented by a raw-bytes Solm fallback that delegates to
  `extensionDelegate`.
- There is no honest whole-contract constructor wrapper for this artifact yet. Comet's constructor
  returns runtime bytecode whose immutable slots depend on constructor calldata and external
  constructor calls, while the current `constructorEquivalence` statement compares against one fixed
  runtime byte array.
- Several protocol bodies are still source-level scaffolds, not final proof-ready specs. In
  particular, the lending/transfer/liquidation paths and asset-list external calls still need full
  Solm bodies before this benchmark is ready for an agent to prove end-to-end.
