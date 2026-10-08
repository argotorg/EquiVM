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
| `Selectors.lean` | selector table, `selIs`/`selWord`, and ABI selector theorems | agent |
| `Common.lean` | single proof import point; re-exports contract modules and shared reasoning, and holds cross-file helpers | agent |
| `Storage.lean` | contract-wide storage load/store facts (contracts with storage) | agent |
| `Trusted.lean` (when required) | explicitly authorized contract-specific assumptions | agent |
| `Dispatch.lean` | dispatcher walk: reach lemmas from entry to each selector arm | agent |
| `<Function>.lean` (×N) | per-function proof: decode lemmas, EVM trace, source body, `…Body` refinement | agent |
| `Constructor.lean` (+ `ConstructorTrace*`) | creation-code equivalence | agent |
| `Correct.lean` | thin capstone: dispatch routing, revert paths, `<name>Correct` / `<name>ContractCorrect` | agent |

The existing contracts predate this flow and carry both a hand-written AST in
`Spec.lean` and the surface syntax in `SpecSyntax.lean`, related by a proved
`contractSyntax_eq … := by rfl`. There is no reason for a new contract to
provide both: exactly one of the two files carries the spec, and for new work
that is `SpecSyntax.lean` — `Spec.lean` only references it.

`Selectors.lean` owns the complete selector interface: `xxxSelBytes`, `xxxSelWord`, `selIs`, and
the proofs connecting the table to the ABI signatures. `Common.lean` is the stable import
point used by the proof modules and may also contain contract-specific helpers shared across those
modules. If the user explicitly authorizes a contract-specific assumption that cannot be derived
from the model or artifact, create `Trusted.lean` as its isolation boundary. That file records the
assumption and its justification, and is imported only by modules that use it.

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
3. **Generated scaffold** (scripts, see `scripts/README.md`; an agent runs steps 3 and 4 from
   `Misc/scaffold-prompt.md`). `scripts/scaffold.py`
   compiles and pins the artifacts, writes `Bytecode.lean`, `Selectors.lean` and the
   immutables modules, and generates the block summaries; `scripts/bytecode_report.py`
   writes the bytecode report the audit works from; `scripts/sol2solm.py` drafts
   `SpecSyntax.lean` from the solc AST (with holes); `scripts/proof_skeleton.py` writes
   the derived `Spec.lean`, `Common.lean`, the proved `Dispatch.lean`, one `sorry` stub per
   function, `Constructor.lean` and `Correct.lean`; `scripts/scaffold.py difftest` writes
   `DiffTarget.lean` and registers the contract in the differential suite.
4. **Differential test, then audit** (agent, before any proof). The agent runs
   `lake exe solm-difftest --only <Name> --count 50` (`Tests/DiffTest/README.md`) and fixes
   every disagreement in the spec, then audits the spec against the bytecode report block by
   block (step 8 of `Misc/scaffold-prompt.md`). The `successful/cases` line shows which
   transitions the cases reach; raise the count or add words to `DiffTarget.lean` for the ones at
   zero. The suite samples paths; it does not replace the audit.
5. **Everything else** (agent). Hand the directory to the agent with
   `Misc/prompt.md`. It closes the spec holes and audits the spec against the
   bytecode report, proves each function body and the constructor in their own
   files, and closes the top-level theorems — `sorry`-free and axiom-clean
   (concrete obligations may still use documented `native_decide` evaluation
   axioms).
6. **Acceptance** (`scripts/finish_check.py`). `lake build <Module>.Correct` succeeds, the
   differential suite passes on the contract, no `sorry`/`admit` in the directory, and
   `#print axioms` on the capstone matches the accepted footprint (see the finish checklist in
   `Misc/prompt.md`).
