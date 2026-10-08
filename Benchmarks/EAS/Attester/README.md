# EAS Attester benchmark

This is the official EAS **example wrapper** `Attester`, which calls an immutable EAS address.
It is not the production `EAS.sol` implementation. Its two batch functions have nested loops.

The upstream default branch is `master`. Its head was checked on 2026-10-07 and remains
[`d2864b166a08f9b3f9314f8b302316d67f227462`](https://github.com/ethereum-attestation-service/eas-contracts-example/commit/d2864b166a08f9b3f9314f8b302316d67f227462),
dated 2024-10-12. The vendored
[`contracts/Attester.sol`](https://github.com/ethereum-attestation-service/eas-contracts-example/blob/d2864b166a08f9b3f9314f8b302316d67f227462/contracts/Attester.sol)
matches that source byte for byte. Its imported interface closure matches npm
`@ethereum-attestation-service/eas-contracts@1.7.1`, the upstream lockfile version.

## Compiler and artifacts

The artifacts use the effective settings of upstream's
[`hardhat.config.ts`](https://github.com/ethereum-attestation-service/eas-contracts-example/blob/d2864b166a08f9b3f9314f8b302316d67f227462/hardhat.config.ts):

| Setting | Value |
|---|---|
| Compiler | `0.8.26+commit.8a97fa7a` |
| Optimizer | enabled, **1,000,000 runs** |
| EVM target | **Paris** |
| Pipeline | legacy (`viaIR: false`) |
| Metadata hash | `none` (the compiler-version CBOR trailer remains) |
| Upstream Hardhat | `2.22.13` |
| Creation bytecode | **4,057 bytes**, before constructor arguments |
| Runtime template | **3,865 bytes** |
| Immutable `_eas` payload offsets | **824, 1719, 1888, 2289**, 32 bytes each |

Paris is supplied by
[Hardhat 2.22.13's configuration resolver](https://github.com/NomicFoundation/hardhat/blob/hardhat%402.22.13/packages/hardhat-core/src/internal/core/config/config-resolution.ts#L401-L409).
Upstream does not explicitly set `evmVersion`; solc 0.8.26 directly without that option defaults
to Cancun. The previous benchmark used 200 optimizer runs and that native compiler default,
so it did not reproduce upstream's effective build settings.

`Attester.compiler.json` records settings, source and bytecode hashes, method IDs, immutable
references, and compiler function PCs. `sources.sha256` covers the vendored sources and
compiler JSON/hex artifacts. `Bytecode.lean` embeds the exact bytes and checks jump destinations.
A separate compile using all 27 sources in the upstream project's dependency closure,
including its other examples and OpenZeppelin 5.0.2, produced identical Attester bytes.

Reproduce and compare artifacts using the official solc 0.8.26 executable:

```sh
python3 Benchmarks/EAS/Attester/rebuild.py --solc /path/to/solc-0.8.26
```

Use `--write` to regenerate them. The Linux compiler used for this refresh has SHA-256
`d5f23436f443edb85d8e76906d12f0a86ce0490e7663a9e608efeb7a93f149ef`.

## Specification and proof targets

`SpecSyntax.lean` is the authoritative current-Solm surface specification. `Spec.lean` derives
the contract and transition handles and supplies the empty storage backend, ABI codecs,
modern decoder mode, and constructor deployment codec. There is one contract body.

`AUDIT.md` records the semantic review, mismatches fixed, and refinement scope. `Audit.lean`
contains executable differential checks against the real EVM bytecode. It does not import
the correctness targets; its finite checks are separate from the quantified proofs.

`Common.lean`, `Dispatch.lean`, the four function files, `Constructor.lean`, and `Correct.lean`
prove the full contract refinement, with supporting modules for ABI correspondence, memory,
loop invariants, external calls, and immutable patching. Every proof body is complete.

## Completed refinement proof

The final target is `Benchmarks.EAS.Attester.attesterContractCorrect` in `Correct.lean`.
It combines constructor refinement with runtime refinement for every well-typed immutable
assignment through the existing `contractRefinement.of_runtime` interface.

The proof covers dispatch and guard failures, all four entry points, both nested-loop request
builders, the four external CALL boundaries, arbitrary return-data decoding, and the constructor's
four immutable patches. It preserves the original statements and their arbitrary calldata,
callee, immutable, and static-execution scope. Wrapped nested offsets and the return-array
allocation guard are deliberate audited behavior.

Out-of-gas paths use the refinement's dedicated constructor. Input, allocation, and return-data
bounds are proved directly, including the gas-derived bound on callee return data. The unbounded
`readWithPadding` fix allows outgoing ABI encodings of at least 2^64 bytes to be related exactly.
No additional well-formedness condition or contract-specific axiom is needed.

The proof runs Paris-compiled bytecode under the repository's Cancun semantics. Selector
identities use `decide +kernel`; concrete bytecode and decode checks use the permitted
`native_decide` evaluation axioms. See `AUDIT.md` for the refinement boundary and validation.

## Block summaries and validation

`Blocks.lean` imports the generated shards. `Blocks/Runtime.index` and `Blocks/Creation.index`
map theorem names to instruction PCs and source locations. Runtime summaries quantify the
immutable patch values; constructor summaries quantify an arbitrary appended argument tail.
The constructor's executable prefix is `[0, 192)`; the rest is runtime data.

There are 486 runtime summary theorems (including packed variants) and 28 constructor summary
theorems. Every constructor-prefix instruction is covered. Runtime coverage includes 2,261
of 2,265 instructions; the four `CALL` instructions at 906, 1786, 2127, and 2381 are explicit
boundaries. Use the shared `RD.call` / `callViaEVM` machinery to compose those calls. CBOR metadata
is excluded from executable block discovery.

From the project root:

```sh
lake build Benchmarks.EAS.Attester.Correct
lake build Benchmarks.EAS.Attester.ReadLimitAudit
printf '%s\n' 'import Benchmarks.EAS.Attester.Correct' \
  '#print axioms Benchmarks.EAS.Attester.attesterContractCorrect' | lake env lean --stdin
```

`lake build Benchmarks.EAS.Attester.Audit` runs the separate differential audit when desired.
Use `python3 Benchmarks/EAS/Attester/generate_blocks.py --check` to check summary reproducibility
without rewriting them. The artifact refresh also passed `ABI.SignatureTests`,
`Reasoning.ABIComposite`, and `Reasoning.ABIViews`.

The checked semantics are Cancun, as fixed by the current EVMLean dependency. This is
Paris-compiled bytecode executed under that model, rather than a historical Paris fork
equivalence target. Attester itself uses no post-Paris opcode, `CREATE`, or `SELFDESTRUCT`.
