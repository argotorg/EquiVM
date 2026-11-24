# scripts/ — scaffold and proof-skeleton automation

Everything a proof needs that is a pure function of the compiler artifacts is generated here.
The agent's work starts after these scripts: closing the spec holes, auditing the spec against
the bytecode report, and proving the function bodies.

All scripts are plain Python 3 with no third-party Python dependencies (keccak is included), run
from the repository root. `solc` binaries are taken from `--solc`; the standard-JSON interface is
used, so any solc ≥ 0.5 works. Vyper compilation uses a Vyper 0.4.3 executable passed to
`--vyper` and a pinned local import tree.

## Pipeline for a new contract

```bash
D=Benchmarks/Scaffolds/Foo        # contract directory; sources under $D/contracts/
M=Benchmarks.Scaffolds.Foo        # its Lean module path

# 1. compile and pin the artifacts (runtime/creation hex, ABI, storage layout, AST, build json)
scripts/scaffold.py compile --dir $D --solc /path/to/solc-0.8.20 --main contracts/Foo.sol \
    --contract Foo --runs 200 --evm-version shanghai --metadata-hash none

# 2. Bytecode.lean / CreationBytecode.lean: the runtime / creation bytecode as listings (a
#    `listing_from_hex` command over runtime.hex / creation.hex, pinned by SHA-256, that decodes
#    them into tables of instructions checked against the bytes in the kernel; they define
#    fooBytecode and fooCreationBytecode), Selectors.lean (table + keccak facts),
#    Immutables.lean / ImmutableCode.lean for contracts with immutables
scripts/scaffold.py lean --dir $D --module $M

# 3. proved block summaries for the runtime and the creation code, by runs over the listings
#    (without native_decide)
scripts/scaffold.py blocks --dir $D --module $M

# 4. the bytecode report: census, dispatcher, source functions, routines, annotated blocks
scripts/bytecode_report.py $D -o $D/REPORT.md

# 5. the spec draft (holes fail to elaborate until closed; --comment-holes to check the rest)
scripts/sol2stele.py $D --namespace $M -o $D/SpecSyntax.lean --spec-json $D/Foo.spec.json
#    (Vyper: scripts/vy2stele.py, same arguments, from the pinned annotated AST)

# 6. the proof skeleton: Spec, Common, Dispatch (proved), <Fn>.lean stubs, Constructor, Correct
scripts/proof_skeleton.py --dir $D --module $M

# 7. consistency checks, and the finish checklist once the proof is done
scripts/scaffold.py check --dir $D
scripts/finish_check.py --dir $D --module $M --theorem $M.fooContractCorrect
```

`scaffold.py all` runs steps 1–3 and the check in one go. Steps 2, 3 and 6 never overwrite existing
files unless `--force` is given.

## Vyper path

Put the exact main `.vy`, imported `.vy`/`.vyi` files, and any imported package modules under
`<Dir>/contracts/`, preserving their import paths. Pin the compiler and EVM fork:

```bash
scripts/scaffold.py all --dir <Dir> --vyper /path/to/vyper-0.4.3 \
    --main path/to/Main.vy --contract Main --evm-version prague --module <Module>
scripts/bytecode_report.py <Dir> -o <Dir>/REPORT.md
```

`all` generates artifacts, Lean bytecode, selectors, block summaries, and a differential target.
The build JSON records the source `# pragma optimize` mode, including `codesize`. The report uses
Vyper's `pc_pos_map` for block-to-source line annotations; solc AST function ranges are unavailable.
Check the source and `<Name>.storage.json` together before writing `SpecSyntax.lean`.

`compile` also pins the annotated AST (`<Name>.vy.ast.json`, and the `ast` entry of the build
JSON), from which `vy2stele.py` drafts the specification:

```bash
scripts/vy2stele.py <Dir> --namespace <Module> -o <Dir>/SpecSyntax.lean --spec-json <Dir>/<Name>.spec.json
```

The draft has one transition per selector, including the variants Vyper generates for default
arguments (same surface name, bodies with the defaults bound first), the public getters, and the
functions a module exports; module state and functions carry the module alias as a prefix
(`ownable_owner`, `ownable__check_owner`), and the storage declarations follow
`<Name>.storage.json`. Arithmetic is checked (`as T`), `unsafe_*` wraps, `convert` becomes a
range assertion or a cast, `@nonreentrant` becomes the compiler's lock protocol around an
internal `<f>_body` (transient slot from Cancun, a storage word before), `extcall`/`staticcall`
are bound external calls with the EXTCODESIZE guard Vyper emits for calls without return data,
`send`/`raw_call` are low-level calls, `range` loops carry their bound checks and `for … in list`
becomes an index loop. What it cannot translate is a hole (`abi_encode`, `create_*`, decimals,
bytes literals, …). The spec JSON lists every selector with its parameters, the ones with a
Vyper capacity (for `externalABI.withVyperABI`), the external calls, and the lock protocol.
`check_sol2stele.py` elaborates Vyper drafts too; it picks the translator from the build JSON.
Use `Examples/VyperERC20/SpecSyntax.lean` as a reference when closing holes. Once the spec
builds, generate the Config shell:

```bash
scripts/proof_skeleton.py --dir <Dir> --module <Module> --only Spec
lake build <Module>.Spec
```

This selects the static Vyper storage backend and Vyper calldata mode. For bounded dynamic state,
replace `vyperStorage!` with source-checked `vyperBoundedStorage!` declarations. For bounded
entry arguments, replace `.withMode DecodeMode.vyper` with `.withVyperABI` and list the
capacity-bearing selector variants from the source; ABI JSON does not retain their bounds.
Review explicit `abi_decode`, constructor inputs, and return decoding separately. If a contract
uses Vyper transient state, write its backend explicitly; `proof_skeleton.py` will stop instead
of generating a Solidity transient layout.

`proof_skeleton.py` then writes the Vyper skeleton: `Common.lean` (selector bridges; with
immutables the `deployed_of_fit` stub, the Vyper analogue of `restrictImmutables_of_fit`), the
proved `Dispatch.lean` (the jump-table lookup of every bucket from the generated `block_0`
summary and `Reasoning/VyperDispatch.lean`, the selector-compare chain down to each function's
guard block, the short-calldata and no-match revert paths by a case split on the bucket), one
`…Body` stub per selector (the function's own `calldatasize`/`callvalue` guard is part of the
body: Vyper has no global guard), `Constructor.lean` and `Correct.lean`. With `--wf <name>` the
runtime theorems are stated under a storage precondition: `Common.lean` declares the placeholder
`def <name> : StorageWF := fun _ _ => True` (to be strengthened to the typed view the proofs need:
Vyper returns and compares raw `bool`/`address` storage words; array lengths need no clause, the
backend reads them raw), the `…Body` stubs take `(hwf : <name> σ I)`, and
`Correct.lean` proves `runtimeRefinementWithWF <name> noGasBound …` and
`contractRefinementWF <name> noGasBound …`. Use `Examples/VyperERC20`
for a complete Vyper proof and `Examples/VyperImmutable` for the immutable suffix artifacts;
`Tests/Pipeline/Vyper*` are complete runs of the pipeline.

## What each script produces

| Script | Output | Notes |
|---|---|---|
| `scaffold.py compile` | `runtime.hex`, `creation.hex`, `<Name>.abi.json`, `<Name>.storage.json`, `<Name>.build.json`, `sources.sha256`; solc also emits `<Name>.sol.ast.json` and `<Name>.metadata.json` | `build.json` holds compiler settings and selectors. Solc includes AST and immutable patch sites; Vyper includes its source maps and code-layout immutables. |
| `scaffold.py lean` | `Bytecode.lean`, `CreationBytecode.lean`, `Selectors.lean`, `Immutables.lean`, `ImmutableCode.lean` | The two listings are written by `gen_listing.py`'s code (below). Selector table in `SpecSyntax.lean` order when that file exists, else by selector value. Selector facts are spec-independent keccak facts; the bridge to each transition is in the skeleton's `Common.lean`. |
| `gen_listing.py` | `Bytecode.lean`, with `--creation` `CreationBytecode.lean` | What `scaffold.py lean` writes, as a command of its own (to regenerate a listing alone, or with `--layout`). The file is one `listing_from_hex` command (`Reasoning/Listing/FromHex.lean`) naming `runtime.hex` (`creation.hex`) and its SHA-256; when the module is built the command reads the file, checks the hash, and adds the listing: the bytes (solc immutable sites zeroed), the table of `(offset, section)` pairs of decoded instructions (sections cut at every `JUMPDEST`, immutable pushes as `.immutable i`), the kernel check of the table against the bytes, the proof that the code the summaries name is the listing's filled code, and `decodes_code` / `jumpdest_code`. `#print_listing <Module>.Listing.table` (after `import <Module>.Bytecode`) prints the instructions with their offsets. Runtime code with 32-byte solc immutables (`layout <term> … blocks <namespace>`: the sites are the layout's, the layout facts go in the blocks namespace; `names [...]` is written when the build JSON numbers the immutables otherwise than by first appearance) or none; a Vyper runtime (`template ++ suffix`) and, with `--creation`, creation code (`creationBytecode ++ tail`) are listed as fixed code followed by arbitrary data (`followed_by`). Without a build JSON, `--layout <term> --layout-import <module>` name the immutable layout (EAS Attester). The file defines the bytecode constant (`<prefix>Bytecode`, `<prefix>CreationBytecode`); its declarations are in the namespace `<Module>.Listing` (`<Module>.CreationListing`); `--constant-namespace` puts the constant elsewhere (`''`: the root). `--valid-jumps <name>` also states membership in the `JUMPDEST` set as a lookup in the listing's tree, the `@[valid_jumps]` theorem `<name>` (`(D_J <code> 0).contains t = …`, `Reasoning/Listing/JumpTable.lean`), which the `jump_dest` tactic rewrites with before `decide +kernel`; `--provenance <file>` adds prose (how the bytes were produced) to the module doc. Lake does not track the hex file: after changing it, regenerate the listing (new hash). |
| `scaffold.py blocks` | `RuntimeBlocks_NNN.lean`, `CreationBlocks_NNN.lean`, `.index` files | `generate_rd_blocks.py` driven with the right code terms, immutable-aware when needed. When `Bytecode.lean` / `CreationBytecode.lean` are listings (by content; and `--no-listing` is not given) each runtime / creation summary is proved by `Reasoning.Listing.RDL.run` over the listing; a block with an instruction the run does not cover keeps its `RD.<opcode>` chain. Statements are unchanged except that a runtime block jumping to a literal target has no `hvalid` hypothesis: the run looks the target up in the listing (`jumpdest_code`). A jump through a stack word keeps it. |
| `scaffold.py check` | report | Each listing's namespace, constant, hex file (`runtime.hex` / `creation.hex`) and its SHA-256 against the one in the listing, its mode (`followed_by`), and for solc immutables its layout's sites (evaluated in Lean when the layout module is built) against the build JSON; the table is checked by the kernel when the listing is built. `--constant-namespace` as for `lean`. Selector table vs ABI and spec order, immutable offsets, source hashes. |
| `scaffold.py difftest` | `DiffTarget.lean`, `Tests/DiffTest/Generated.lean` | The contract's `Target` for the differential suite (spec, config, runtime, creation code, immutable plumbing when the contract has immutables) and the registry of every `DiffTarget.lean` in the repository, which `lake exe stele-difftest` runs. Delete a `DiffTarget.lean` and rerun to unregister. |
| `bytecode_report.py` | Markdown | Opcode census, dispatcher, JUMPDEST set and annotated blocks. Solc reports AST function ranges and internal routines; Vyper reports source lines from `pc_pos_map`. |
| `sol2stele.py` | `SpecSyntax.lean` draft, optional `.spec.json` | From the solc AST: storage (persistent and `transient`)/structs/events/immutables, constructor with base constructors and initialisers inlined, external functions (modifiers inlined, getters generated), reachable internal and library functions, checked arithmetic from static types, external calls bound with view flags and EXTCODESIZE guards, via-IR calldata guard. Holes for what it cannot translate. |
| `vy2stele.py` | `SpecSyntax.lean` draft, optional `.spec.json` | From the Vyper annotated AST: storage in layout order (modules prefixed), structs/events/immutables, constructor, one transition per selector (default-argument variants, getters, module exports), reachable internal functions, checked arithmetic and `convert` from static types, the `@nonreentrant` lock protocol, external calls bound with view flags and Vyper's EXTCODESIZE guard, `send`/`raw_call` as low-level calls. Holes for what it cannot translate. |
| `proof_skeleton.py` | `Spec.lean`, `Common.lean`, `Dispatch.lean`, `<Fn>.lean`, `Constructor.lean`, `Correct.lean` | solc: the compare-chain or binary-search dispatcher; Vyper: the jump-table dispatcher (`Reasoning/VyperDispatch.lean`), Vyper storage and ABI defaults in `Spec.lean` that need capacity review, the `deployed_of_fit` stub for immutables, and with `--wf <name>` the storage-precondition form of the runtime theorems. Jump validity goes through `<prefix>Jumpdest` in `Common.lean` (the listing's `jumpdest_code`, `rfl rfl` for a literal target); the dispatcher chains pass no `hvalid` to a block whose generated statement has none. |
| `check_sol2stele.py` | report | Translates every given directory (solc or Vyper, by the build JSON) and elaborates the drafts (holes as comments). |
| `finish_check.py` | report | Build, differential suite on the contract (`--difftest-count`, `--skip-difftest`), `sorry`/`admit`/`axiom` grep, `#print axioms` against the accepted trusted base. |
| `check_all_benchmark_blocks.py` | report | Check that benchmark block summaries compile, excluding temporary contracts under `Benchmarks/Scaffolds/`. Finds a contract by its `Bytecode.lean` listing and generates with it (its constant, blocks namespace and immutable layout). CI selects `UniswapV3/Pool`. |
| `check_listing_hashes.py` | report | Every `listing_from_hex` in the repository names an existing hex file whose SHA-256 is the one written in the listing (no Lean needed; CI runs it). Lake does not track hex files, so an edited hex file with stale `.olean`s would otherwise go unnoticed until a clean build. |

## Conventions the generators follow

- Transition order is the `SpecSyntax.lean` function order; the translator writes them in selector
  order, which is the compiled dispatcher order. `vy2stele.py` keeps the selector variants of one
  source function (default arguments) adjacent, the grouping `scaffold.py` applies when it
  derives the selector table from an existing `SpecSyntax.lean`.
- Declarations are prefixed with the lowerCamel contract name (`fooBytecode`, `fooSelBytes`,
  `fooReachTransferBody`, `fooTransferBody`); overloaded functions get their parameter types
  appended (`file_bytes32_uint256`).
- `generate_rd_blocks.py --namespace <Module>.RuntimeBlocks` gives compiler variants distinct
  namespaces while preserving their summary names. `audit_safe.py` uses each Safe variant's
  module path for its runtime and creation namespaces so the proofs can be imported together.
- Constants are inlined at their uses (solc does the same; the surface grammar has no constant
  item). Enums are `uint8`. Interface casts are dropped (receivers are addresses).
- A public function that is also called internally is split into `<f>_body` (internal) plus the
  external wrapper, so the internal call does not pass through the entry guards.
- Internal `storage` parameters and returns keep their source types, including mappings and
  library structs. Named storage returns and local pointer assignments bind aliases. Library
  extension calls include their receiver; colliding struct names are qualified by their owner.
- Memory structs, arrays, `bytes` and `string` are passed to internal functions by reference in
  Solidity but by value in Stele. A callee that may modify one (directly, or through a callee)
  returns its final value after the declared results, and the caller assigns it back to the
  argument's path. Overlapping arguments, a parameter that is reassigned and modified, and a
  modification through a local alias of a parameter are holes.
- Contracts with a `fallback`/`receive` get `sorry` stubs for the Stele dispatch facts: the
  unmatched-selector path then runs the fallback instead of reverting.

## Tests

```bash
python3 scripts/test_generate_rd_blocks.py
python3 scripts/test_scaffold_tools.py
python3 scripts/check_listing_hashes.py
VYPER=/path/to/vyper-0.4.3 python3 -B -m unittest discover -s scripts -p test_vy2stele.py
```

`Misc/scaffold-prompt.md` is the agent brief that runs these scripts from a contract to a
ready-to-prove scaffold.

The differential suite (`lake exe stele-difftest`, `Tests/DiffTest/README.md`) runs every
specification against its bytecode.  `scaffold.py difftest` registers a contract; once its
specification compiles, `lake exe stele-difftest --only <Name> --count 50` tests it before any
proof is attempted, and `finish_check.py` runs it again at acceptance.
