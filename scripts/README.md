# scripts/ — scaffold and proof-skeleton automation

Everything a proof needs that is a pure function of the compiler artifacts is generated here.
The agent's work starts after these scripts: closing the spec holes, auditing the spec against
the bytecode report, and proving the function bodies.

All scripts are plain Python 3 with no third-party dependencies (keccak is included), run from
the repository root. `solc` binaries are taken from `--solc`; the standard-JSON interface is used,
so any solc ≥ 0.5 works.

## Pipeline for a new contract

```bash
D=Benchmarks/Scaffolds/Foo        # contract directory; sources under $D/contracts/
M=Benchmarks.Scaffolds.Foo        # its Lean module path

# 1. compile and pin the artifacts (runtime/creation hex, ABI, storage layout, AST, build json)
scripts/scaffold.py compile --dir $D --solc /path/to/solc-0.8.20 --main contracts/Foo.sol \
    --contract Foo --runs 200 --evm-version shanghai --metadata-hash none

# 2. Bytecode.lean (chunked bytes + JUMPDEST theorems), Selectors.lean (table + keccak facts),
#    Immutables.lean / ImmutableCode.lean for contracts with immutables
scripts/scaffold.py lean --dir $D --module $M

# 3. proved block summaries for the runtime and the creation code
scripts/scaffold.py blocks --dir $D --module $M

# 4. the bytecode report: census, dispatcher, source functions, routines, annotated blocks
scripts/bytecode_report.py $D -o $D/REPORT.md

# 5. the spec draft (holes fail to elaborate until closed; --comment-holes to check the rest)
scripts/sol2solm.py $D --namespace $M -o $D/SpecSyntax.lean --spec-json $D/Foo.spec.json

# 6. the proof skeleton: Spec, Common, Dispatch (proved), <Fn>.lean stubs, Constructor, Correct
scripts/proof_skeleton.py --dir $D --module $M

# 7. consistency checks, and the finish checklist once the proof is done
scripts/scaffold.py check --dir $D
scripts/finish_check.py --dir $D --module $M --theorem $M.fooContractCorrect
```

`scaffold.py all` runs steps 1–3 and the check in one go. Steps 2, 3 and 6 never overwrite existing
files unless `--force` is given.

## What each script produces

| Script | Output | Notes |
|---|---|---|
| `scaffold.py compile` | `runtime.hex`, `creation.hex`, `<Name>.abi.json`, `<Name>.storage.json`, `<Name>.sol.ast.json`, `<Name>.metadata.json`, `<Name>.build.json`, `sources.sha256` | `build.json` holds the compiler version and settings, method identifiers, immutable references (named, in constructor write order), source maps, generated sources, and every source unit's AST. Only the import closure of `--main` is compiled. |
| `scaffold.py lean` | `Bytecode.lean`, `Selectors.lean`, `Immutables.lean`, `ImmutableCode.lean` | Selector table in `SpecSyntax.lean` order when that file exists, else by selector value. Selector facts are spec-independent keccak facts; the bridge to each transition is in the skeleton's `Common.lean`. |
| `scaffold.py blocks` | `RuntimeBlocks_NNN.lean`, `CreationBlocks_NNN.lean`, `.index` files | `generate_rd_blocks.py` driven with the right code terms, immutable-aware when needed. |
| `scaffold.py check` | report | Lean bytes vs hex, jump tables vs the EVM scan, selector table vs ABI and spec order, immutable offsets, source hashes. |
| `scaffold.py difftest` | `DiffTarget.lean`, `Tests/DiffTest/Generated.lean` | The contract's `Target` for the differential suite (spec, config, runtime, creation code, immutable plumbing when the contract has immutables) and the registry of every `DiffTarget.lean` in the repository, which `lake exe solm-difftest` runs. Delete a `DiffTarget.lean` and rerun to unregister. |
| `bytecode_report.py` | Markdown | Opcode census, dispatcher (guard, size check, pivots, arms, fallthroughs), JUMPDEST set, per-function pc ranges and internal routines from the source map, every runtime block with its source statement, creation summary. |
| `sol2solm.py` | `SpecSyntax.lean` draft, optional `.spec.json` | From the solc AST: storage (persistent and `transient`)/structs/events/immutables, constructor with base constructors and initialisers inlined, external functions (modifiers inlined, getters generated), reachable internal and library functions, checked arithmetic from static types, external calls bound with view flags and EXTCODESIZE guards, via-IR calldata guard. Holes for what it cannot translate. |
| `proof_skeleton.py` | `Spec.lean`, `Common.lean`, `Dispatch.lean`, `<Fn>.lean`, `Constructor.lean`, `Correct.lean` | `Spec.lean` configures the transient backend when the spec declares transient state. `Dispatch.lean` contains proved reach lemmas composed from the block summaries (linear and binary-search dispatchers, with and without a global callvalue guard). Function bodies and the constructor are `sorry` stubs with the fixed signatures `Correct.lean` consumes. |
| `check_sol2solm.py` | report | Translates every given directory and elaborates the drafts (holes as comments). |
| `finish_check.py` | report | Build, differential suite on the contract (`--difftest-count`, `--skip-difftest`), `sorry`/`admit`/`axiom` grep, `#print axioms` against the accepted trusted base. |
| `check_all_benchmark_blocks.py` | report | CI check that every benchmark's block summaries compile. |

## Conventions the generators follow

- Transition order is the `SpecSyntax.lean` function order; the translator writes them in selector
  order, which is the compiled dispatcher order.
- Declarations are prefixed with the lowerCamel contract name (`fooBytecode`, `fooSelBytes`,
  `fooReachTransferBody`, `fooTransferBody`); overloaded functions get their parameter types
  appended (`file_bytes32_uint256`).
- Constants are inlined at their uses (solc does the same; the surface grammar has no constant
  item). Enums are `uint8`. Interface casts are dropped (receivers are addresses).
- A public function that is also called internally is split into `<f>_body` (internal) plus the
  external wrapper, so the internal call does not pass through the entry guards.
- Contracts with a `fallback`/`receive` get `sorry` stubs for the Solm dispatch facts: the
  unmatched-selector path then runs the fallback instead of reverting.

## Tests

```bash
python3 scripts/test_generate_rd_blocks.py
python3 scripts/test_scaffold_tools.py
```

`Misc/scaffold-prompt.md` is the agent brief that runs these scripts from a contract to a
ready-to-prove scaffold.

The differential suite (`lake exe solm-difftest`, `Tests/DiffTest/README.md`) runs every
specification against its bytecode.  `scaffold.py difftest` registers a contract; once its
specification compiles, `lake exe solm-difftest --only <Name> --count 50` tests it before any
proof is attempted, and `finish_check.py` runs it again at acceptance.
