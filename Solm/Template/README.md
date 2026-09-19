# Refinement proof template

Skeletons for adding a new contract and proving the deployed runtime bytecode
equivalent to its Solm spec. `Misc/` is not a lake target: these files do not
build; they are reference scaffolds for the layout and shapes described below.

The division of labor is deliberate: **the user provides the compiled artifacts
and the surface specification (`SpecSyntax.lean`) — the boilerplate and the
proof are the job of the LLM agent**, driven by the prompt in `Misc/prompt.md`.

Proven end-to-end examples: `Benchmarks/Dss/Pot` (this template's source),
`Benchmarks/Dss/Jug`, `Benchmarks/Dss/Cat`, `Benchmarks/WETH9`, `Examples/Ballot`.

## Directory layout

Every contract directory follows this structure (`Examples/<C>/` or
`Benchmarks/[<Family>/]<C>/`):

| file | role | author |
|---|---|---|
| `contracts/` or `<C>.sol` | pinned source (vendored imports under `contracts/`) | user |
| `sources.sha256` | `shasum -a 256` of the pinned sources | user |
| `creation.hex`, `runtime.hex` | compiler output, hex-encoded | user |
| `<C>.abi.json`, `<C>.storage.json`, `<C>.sol.ast.json` | solc artifacts used for audits | user |
| `SpecSyntax.lean` | **the specification**: the contract in `solidity%` surface syntax | user |
| `Immutables.lean` | contracts with immutables only: the valuation structure + read exprs | user |
| `Spec.lean` | derived assembly: `def contract := Syntax.contractSyntax`, named transition handles, storage layout, `Config` | agent |
| `Bytecode.lean` | runtime/creation bytes as chunked `ByteArray`s + jump-dest facts, transcribed from the `.hex` files | agent |
| `Common.lean` | selector table, `selIs`/`selWord`, shared proof helpers | agent |
| `Storage.lean` | contract-wide storage load/store facts (contracts with storage) | agent |
| `Trusted.lean` | the accepted trusted base: per-function selector-bytes axioms | agent |
| `Dispatch.lean` | dispatcher walk: reach lemmas from entry to each selector arm | agent |
| `<Function>.lean` (×N) | per-function proof: decode lemmas, EVM trace, source body, `…Body` refinement | agent |
| `Constructor.lean` (+ `ConstructorTrace*`) | creation-code equivalence | agent |
| `Correct.lean` | thin capstone: dispatch routing, revert paths, `<name>Correct` / `<name>ContractCorrect` | agent |

The existing contracts predate this flow and carry both a hand-written AST in
`Spec.lean` and the surface syntax in `SpecSyntax.lean`, related by a proved
`contractSyntax_eq … := by rfl`. There is no reason for a new contract to
provide both: exactly one of the two files carries the spec, and for new work
that is `SpecSyntax.lean` — `Spec.lean` only references it.

## Workflow

1. **Compile & pin** (user). Build with the contract's original compiler
   settings, save `creation.hex`/`runtime.hex`/ABI/storage/AST JSON, write
   `sources.sha256`, and record the exact command and compiler version (it ends
   up in `Bytecode.lean`'s header). Bytecode provenance is arbitrary — the
   proof targets whatever was actually deployed, optimizer included.
2. **Specification** (user). Author the contract in `solidity%` surface syntax
   (see `Solm/Notation.lean` header for the language). For the most part it
   mirrors the Solidity source, when one is available. Events, error payloads,
   and exact gas tracking are not modeled currently. Contracts with immutables
   also get an `Immutables.lean` valuation.
3. **Everything else** (agent). Hand the directory to the agent with
   `Misc/prompt.md`. It audits the spec against the bytecode, assembles the
   derived `Spec.lean` (contract reference, per-transition handles, storage
   layout, external-call ABI, `Config`), transcribes `Bytecode.lean`,
   scaffolds `Correct.lean`'s dispatch skeleton, proves each function body and
   the constructor in their own files, and closes the top-level theorems —
   `sorry`-free and axiom-clean up to the accepted trusted base (selector and
   jump-dest facts, plus the tolerated `Reasoning/` axioms).
4. **Acceptance**. `lake build <Module>.Correct` succeeds, no `sorry`/`admit` in
   the directory, and `#print axioms` on the capstone shows only the accepted
   set (see the finish checklist in `Misc/prompt.md`).
