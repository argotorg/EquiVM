# Agent prompt — from a contract to a ready-to-prove scaffold

In one session you turn one Solidity or Vyper contract into a proof scaffold: pinned artifacts, generated
Lean that builds, a Stele specification you have audited against the bytecode and that the
differential suite cannot tell apart from it, and the proof skeleton the proving session
(`Misc/prompt.md`) starts from. You write no proofs.

## Inputs

- The contract: its sources (the main unit and its import closure), the compiler version and
  settings (solc optimizer/runs/via-IR or Vyper optimization pragma, EVM version), or the deployed bytecode with its verified
  sources. The proof targets the bytecode as deployed, so the settings must reproduce it.
- Its place: a directory `<Dir>` and module path `<Module>`, for example
  `Benchmarks/Scaffolds/<Name>` and `Benchmarks.Scaffolds.<Name>`.

## Rules

- No guessing. Every statement of the specification follows from the source or the bytecode
  report. When the two differ, the bytecode wins and the difference is recorded.
- Generated files are not edited by hand except for the ABI and Vyper storage configuration in `Spec.lean` when
  the generated decoder does not match the bytecode. Rerun the generator with `--force` before
  making that edit, and reapply it if regeneration is later necessary. The main file you write is
  `SpecSyntax.lean`; its surface syntax is documented in the header of `Stele/Notation.lean`.
- Nothing outside `<Dir>` changes: not `Stele/`, not `Reasoning/`, not `scripts/`.
- Inline assembly, library calls and everything else the translator leaves as a hole are
  modelled by their effect: the Stele statements that perform the same storage reads and writes,
  calls and results, justified by the bytecode report. Compiler-inserted checks are written as
  `require` statements. A blocker is only a behaviour the Stele semantics cannot express; name the
  function and the bytecode location, do not work around it silently.
- The differential suite is evidence, not the audit. It runs first and samples the paths its
  generator reaches; the audit of step 8 covers every block of the bytecode, is yours to do, and
  ends either with a faithful spec or with an immediate report of what cannot be made faithful.
- **No memory implementation details in the spec.** The finished spec works on values: it
  never models the free memory pointer, allocation, memory layout or copying (encoding buffers,
  scratch space, `mload`/`mstore`), including where a translated hole or inline assembly touches
  them. A compiler guard on an allocation (a size check that reverts) stays as a `require`, since
  its revert is observable; the pointer arithmetic behind it does not. Where that arithmetic is
  safe only because of gas, the gas bound below covers it, not the spec.
- **The gas bound is yours to find.** The runtime refinement may be stated only for calls whose
  starting gas satisfies a bound (`runtimeRefinementWithWF <wf> <gasBound> …`, `noGasBound` when
  there is none). The proving session takes the bound from your hand-off. Propose one only when
  it lets the proof abstract a low-level implementation detail, and then choose the loosest bound
  that does. It must sit above `2^24`: every starting gas up to `2^24` (the per-transaction gas
  cap of EIP-7825) satisfies it, so no real call is excluded. A bound is an obligation, not an
  assumption: within the bound, every path on which the abstracted detail does not hold must be
  shown to end in the `outOfGas` refinement case. If such a path can complete within the bound,
  the bound is wrong.

## Steps

1. **Scaffold.**
   ```
   scripts/scaffold.py all --dir <Dir> --solc <solc> --main <Main.sol> --contract <Name> \
       --runs <n> [--via-ir] [--evm-version <v>] --module <Module>
   ```
   Compiles and pins the artifacts, writes the bytecode files `Bytecode.lean` and
   `CreationBytecode.lean` (the runtime and creation bytecode with kernel-checked disassembly),
   `Selectors.lean`, the immutable modules, `DiffTarget.lean` (registered in `Tests/DiffTest/Generated.lean`), the block
   summaries, and checks them. Every check line must read `ok`. A contract with transient
   storage needs `--evm-version cancun` (or later) and solc 0.8.28 or later.
   For Vyper 0.4.3, pin the entire local import tree (`.vy` and `.vyi`) under `<Dir>/contracts`
   and run:
   ```
   scripts/scaffold.py all --dir <Dir> --vyper /path/to/vyper --main <Main.vy> \
       --contract <Name> --evm-version <v> --module <Module>
   ```
   Record the source's `# pragma optimize` and `# pragma nonreentrancy` settings. Vyper's
   `layout` output and source map have different shapes from solc's. `all` creates artifacts,
   selectors, block summaries and a differential target; it does not create a Stele spec.
2. **Report.** `scripts/bytecode_report.py <Dir> --output <Dir>/<Name>.report.md`: the
   dispatcher, every runtime block with its source statement, the per-function pc ranges, the
   internal routines. For Vyper, the report annotates blocks from `pc_pos_map`; it does not
   infer solc AST function ranges or jump tags. This is the ground truth for steps 4 and 8.
3. **Draft.**
   ```
   scripts/sol2stele.py <Dir> --contract <Name> --namespace <Module> \
       --output <Dir>/SpecSyntax.lean --spec-json <Dir>/<Name>.spec.json
   ```
   The draft encodes checked arithmetic, the compiler's guards, hoisted calls and the getters;
   what it cannot translate is a `${hole …}`, listed in the file header.
   **Vyper:**
   ```
   scripts/vy2stele.py <Dir> --contract <Name> --namespace <Module> \
       --output <Dir>/SpecSyntax.lean --spec-json <Dir>/<Name>.spec.json
   ```
   drafts from the pinned annotated AST: one transition per selector (default-argument variants
   share the source name and bind the defaults first), public getters, module exports with the
   module alias as a prefix on module state and functions, checked arithmetic and `convert`, the
   `@nonreentrant` lock protocol, external calls with Vyper's EXTCODESIZE guard, `send` and
   `raw_call` as low-level calls. The spec JSON lists the selectors whose parameters carry a
   capacity (`bounded`), the external calls, and the lock slot. Check the storage declarations
   against `<Name>.storage.json` and treat external calls and imported modules according to the
   compiled bytecode, not their names; `Examples/VyperERC20/SpecSyntax.lean` shows the syntax.
4. **Close the holes.** Replace each hole with the Stele statements the source and the report
   justify (Vyper drafts: `abi_encode`, `create_*`, bytes literals, decimals, `extract32`, …).
   `lake build <Module>.SpecSyntax` must succeed before you continue.
5. **Skeleton.** `scripts/proof_skeleton.py --dir <Dir> --module <Module>` writes `Spec.lean`,
   `Common.lean`, the proved `Dispatch.lean`, one stub per function, `Constructor.lean` and
   `Correct.lean`. Check the external-call ABI table in `Spec.lean` against the callees' ABIs; a
   `TODO` there is a hole you close in `SpecSyntax.lean` or report. Configure `config.externalABI`
   to match the pinned bytecode's calldata and explicit `abi.decode` behavior, including how it
   handles malformed inputs. The default decoders are modern; use `externalABI.withMode` only
   when a built-in variant matches. Otherwise define a custom decoder in `Spec.lean` and assign
   it to `decodeCalldata?` and/or `decodeValue?` there. Calldata decoding receives the full
   calldata, including the four-byte selector; dispatch checks the selector separately. Keep
   named external-call return decoding in `decode?`, matched to the callee's ABI. Build the
   resulting `Spec.lean` before accepting the scaffold.
   **Vyper:** `scripts/proof_skeleton.py --dir <Dir> --module <Module>` writes the same files; its
   `Spec.lean` selects `vyperStorage!` for static state and Vyper calldata mode.
   Compare the state layout with `<Name>.storage.json`. If state contains `DynArray`, `Bytes`, or
   `String`, replace the static backend with `vyperBoundedStorage!` and explicit
   `VyperStorageDecl` capacities. If an entry parameter is bounded, declare a
   `List ABI.VyperABIFunction` from the source (the `bounded` entries of `<Name>.spec.json` list
   them) and use `externalABI.withVyperABI` so oversized values fail; plain `.withMode .vyper` does
   not check capacities. Include every default-argument selector variant in the list. Explicit `abi_decode`, constructor inputs, and callee return
   bounds need separate review: the entry-calldata adapter does not check those sites.
   `Dispatch.lean` proves the jump-table dispatcher from the generated block summaries; the
   stubs are the `…Body` theorems, `Constructor.lean`, and `deployed_of_fit` in `Common.lean`
   when the contract has immutables. Vyper returns and compares raw storage words, so a spec
   with typed storage (`bool`, `address`, bounded arrays) refines the bytecode only on
   well-formed storage: pass `--wf storageWF` to state the runtime theorems under a storage
   precondition (`runtimeRefinementWithWF storageWF noGasBound …`; the stubs take
   `(hwf : storageWF σ I)`), strengthen the placeholder in `Common.lean` to the typed view the
   proofs need (canonical address words, `bool` words in `{0, 1}`, and whatever a re-read of
   such a word after an external call needs), and record it in the hand-off; every writer must
   store validated words so the precondition is preserved.  Bounded arrays and byte strings
   need no clause: the backend reads length words raw, as the bytecode does, and the spec's
   `for` loop carries the compiler's bound as a `require`.
6. **Build.** `lake build <Module>.Correct` succeeds. The only `sorry`s are the generated stubs:
   the function files, `Constructor.lean`, `restrictImmutables_of_fit` (solc) or
   `deployed_of_fit` (Vyper) in `Common.lean` when the contract has immutables, and the dispatch
   facts when it has a `fallback`, `receive` or `__default__`.
   Do not report a finished ready-to-prove skeleton before `Correct` builds.
7. **Differential test**, before the audit, so the gross errors are gone when you read.
   `lake exe stele-difftest --only <Name> --count 50` (`Tests/DiffTest/README.md`). Every
   `DISAGREE` and every `spec stuck` case is understood: a specification error is fixed in
   `SpecSyntax.lean` (then steps 5 to 7 again), anything else is a blocker. Inconclusive cases
   (out of gas, out of fuel, allocation cap) impose nothing. Every transition's `successful/cases`
   entry is nonzero, or you say why; raise `--count` or add the words and callees its guards need
   to `DiffTarget.lean`.
8. **Semantic audit.** Its purpose: be certain that the spec is a faithful, authoritative model of
   the bytecode and that nothing in it will block the proof. Record findings in the hand-off. For every
   function (each selector arm, the constructor, `receive` and `fallback` when present), take its
   pc range and blocks from the report and walk the blocks in order against the spec:
   for Vyper computed dispatch, reconstruct selector-to-entry and block ownership directly from
   the generated selector table and bytecode, then record the mapping in `HANDOFF.md`;
   - every block implements a spec statement and every statement has its blocks; a block without
     a statement, or a statement without blocks, is a finding;
   - memory: a block that only manages memory (free-pointer bumps, allocation, encoding buffers)
     is accounted for by the statement it serves, never by a statement of its own; a spec
     statement that models the free memory pointer, an allocation or a memory layout is a finding;
   - storage: each `SLOAD` and `SSTORE` has its read or write in the spec, in the same order,
     with the same slot derivation (mapping keys, array elements and lengths, packed fields);
     the same for `TLOAD` and `TSTORE` against the `transient` declarations, whose slots start
     at zero in their own space;
     for Vyper, check full-word state slots, Vyper's mapping-key/slot hash order, and inline
     bounded dynamic storage against the compiler layout; verify any compiler-generated
     nonreentrancy lock, including view checks and reentrant exceptions;
   - arithmetic: checked operations revert on overflow and wrapping ones do not; division and
     modulo by zero; shifts, masks and sign extension at the declared widths;
   - guards, in the order the bytecode evaluates them: the compiler's (payability, `EXTCODESIZE`,
     calldata size and validation, allocation size before `new`) and the source's (`require`,
     `revert`, modifiers), including the short-circuit of `&&` and `||`;
   - calls: target, value, selector and argument encoding, static versus regular call, the success
     check, the decoding of the return and what a codeless callee produces; contract creation;
   - results: return encoding, every revert path (the revert itself is modelled, its payload is
     not), events and their arguments; `delete`, `push`, `pop`;
   - the environment: every use of `msg.sender`, `msg.value`, `address(this)`, `block.*`;
   - gas (see the gas-bound rule): every low-level detail whose correctness depends on the
     starting gas, such as pointer or size arithmetic that cannot overflow only because memory
     expansion would exhaust the gas first, or behaviour that reads `GAS` or forwards gas to a
     call. For each one, find the largest starting gas under which every path that breaks it runs
     out of gas first (e.g. expanding memory to an overflowing offset costs more than that gas).
     The bound you propose is the loosest one that covers all of them, and it sits above `2^24`.
     A detail that needs a bound at or below `2^24`, or a path that breaks it and still completes
     within the bound, is a finding;
   - proof blockers: storage reads and writes of mappings, arrays, strings and bytes in the
     bytecode's order (otherwise the proof needs a slot-noncollision axiom, which is not allowed);
     the same logic in one helper function rather than repeated; nothing the Stele semantics cannot
     express.
   A function is done when every block of its range is accounted for; nothing is skipped because
   the suite agreed. Every finding makes the spec faithful (then steps 5 to 7 again). A finding
   that cannot be fixed in the spec is reported immediately, with the function and the pc, and
   the session stops there.
9. **Hand-off.** `<Dir>/HANDOFF.md`: compiler settings and provenance; the differential run
   (command, seed, summary line, coverage line); the places where the spec follows the bytecode
   rather than the source, if any; what the proving session should know (immutables and their
   valuation, external-call ABI entries, the selected or custom calldata and value decoders and
   the bytecode behavior that justifies them, the functions you expect to be hard and why); the gas
   bound: `noGasBound`, or the bound with the details it abstracts, why it is the loosest, why it
   sits above `2^24`, and why every path that breaks an abstracted detail within it runs out of gas.
   For Vyper, also list selector variants from default arguments, bound-bearing entry and
   explicit decode sites, source/layout-derived storage capacities, the EVM fork used for locks,
   and the bucket of each selector in the jump-table dispatcher.

## Done when

- `scripts/scaffold.py check --dir <Dir>` prints only `ok` lines.
- `lake build <Module>.Correct` succeeds with no `sorry` outside the generated stubs.
- `config.externalABI` uses decoders that match the pinned bytecode, including malformed inputs.
- `lake exe stele-difftest --only <Name> --count 50` reports no disagreement and no stuck case.
- The audit of step 8 is complete for every function and the constructor, with no finding left.
- `HANDOFF.md` has the five sections of step 9.

If a step cannot be completed, state the narrower result and list what is missing.
