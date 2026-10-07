# Compound III Benchmarks

This directory holds the shared source closure for [Comet](../Comet/README.md) and
[CometRewards](../CometRewards/README.md), copied unchanged from
[`compound-finance/comet`](https://github.com/compound-finance/comet/tree/f766f51583c23acc33b2a7824654ef2029a96804)
commit `f766f51583c23acc33b2a7824654ef2029a96804`.

The artifacts now match the repository's recommended `yarn build` (`hardhat compile`) output
byte-for-byte, including metadata. The upstream
[`hardhat.config.ts`](https://github.com/compound-finance/comet/blob/f766f51583c23acc33b2a7824654ef2029a96804/hardhat.config.ts)
uses solc `0.8.15+commit.e14f2714`, optimizer enabled with 1 run, via-IR, and this custom sequence:

```text
dhfoDgvulfnTUtnIf [xa[r]scLM cCTUtTOntnfDIul Lcul Vcul [j] Tpeul xa[rul] xa[r]cL gvif CTUca[r]LsTOtfDnca[r]Iulc] jmul[jul] VcTOcul jmul
```

The EVM target is London (the solc 0.8.15 default), and metadata uses the default IPFS hash.
No `OPTIMIZER_DISABLED` override is set. The build requires nonempty explorer/RPC environment
variables to load its configuration; local dummy values suffice for compilation.

Each benchmark's `build.json` records exact compiler settings, source names/checksums, build tool
versions, and upstream configuration/lockfile checksums. Its README gives the replay command.
`sources.sha256` contains paths relative to this shared directory.

Scaffold notes:

- The Lean files are benchmark scaffolds with constructor and runtime correctness targets left as
  `sorry`.
- `Spec.lean` files expose ABI-shaped transition declarations and solc storage layouts.
- `SpecSyntax.lean` files expose syntax-facing contract values checked by `rfl` against the AST
  specs.
- Selector bytes, if needed in downstream proofs, can be proved by kernel reduction of pure `KEC`
  expressions, as in `Examples/*/Selectors.lean`; dispatch facts then use those theorems.
- `CometRewards` has been handed off for proof and semantically audited for the current equivalence
  relation. Its 0.8.15 via-IR artifacts match the Lean byte arrays, its packed storage layout
  matches the spec, and its no-return `accrueAccount` calls include the solc `EXTCODESIZE` guards
  in the spec.
- The Comet runtime artifact is solc's unpatched `--bin-runtime` template. Its immutable template
  values are explicit in `Comet/Immutables.lean`, and its payable fallback is modeled in
  `Comet/Spec.lean`.
- Comet exposes a parameterized immutable-aware whole-contract wrapper using
  `constructorEquivalenceWith`, but it is still not ready for proof: the constructor spec contains
  placeholders for `numAssets`, asset-list creation, constructor validation, and external-call
  wiring, and several runtime protocol bodies remain source-level scaffolds.
