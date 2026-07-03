# Compound III CometRewards Benchmark

Source: [`Benchmarks/CompoundIII/contracts/CometRewards.sol`](../contracts/CometRewards.sol) from
`compound-finance/comet` main branch commit `f766f51583c23acc33b2a7824654ef2029a96804`.

Compiled with solc `0.8.15`, optimizer enabled, optimizer runs `1`, `via-ir`, and metadata hash
disabled. See [`Benchmarks/CompoundIII/README.md`](../README.md) for the full source and compiler
provenance.

Artifacts:

- `creation.hex`: optimized creation bytecode, 4207 bytes, sha256
  `8776a8d2bfc30e32c4e762f3f4bc34f654ed6e75baa6fb36ea3cf412a9cc5206`
- `runtime.hex`: optimized deployed runtime bytecode, 4063 bytes, sha256
  `a96c066be24c8e2de04537bb682583475d70cfe35d8aa34a857165df7c9dfe86`
- `CometRewards.abi.json`: ABI emitted by solc, sha256
  `f980ef704b65f32cfea0d4568178408a3455921aad2fa07b521827e2b813eabe`
- `CometRewards.storage.json`: storage layout emitted by solc, sha256
  `4e8e887cde6b3244eedf3514a79d33e6d754acbf60975f3bddeff165e561112d`
- `CometRewards.sol.ast.json`: AST JSON emitted by solc, sha256
  `cd4926631a632aee6f5f514f4aad6631f2e9ae79f7304c31e1cc3d094df503a8`
- `Bytecode.lean`: optimized creation/runtime bytecode as Lean `ByteArray`s plus `valid_jumps`
  facts.
- `Spec.lean`: Solm AST scaffold with ABI surface and solc storage layout.
- `SpecSyntax.lean`: syntax-side wrapper checked definitionally against the AST scaffold.
- `Constructor.lean`: constructor-equivalence target, currently `sorry`.
- `Correct.lean`: runtime and top-level contract-equivalence targets, currently `sorry`.

Main source sha256:
`ba7a859d2936926943613a2add8e651da02b9a38535ac3c3440f6484cf6e9e3c`.

Status:

- Ready for proof as of 2026-07-03. Target theorem:
  `Benchmarks.CompoundIII.CometRewards.cometRewardsContractCorrect`.
- Fresh solc `0.8.15` via-IR output matches the checked-in Lean creation/runtime byte arrays and
  ABI exactly. The storage payload matches modulo regenerated source-path strings.
- The runtime has six `STATICCALL` sites, three `CALL` sites, and two `EXTCODESIZE` guards. The
  spec models the view calls with `perm := false`; the two no-return `accrueAccount` calls are
  guarded with explicit `EXTCODESIZE > 0` checks.
- The three source events and custom-error revert payloads are intentionally not represented under
  the current equivalence relation, which ignores substate/logs and revert data.
