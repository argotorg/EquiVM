# Agent prompt — proving EVM↔Solm correctness for a contract

You are proving that a concrete EVM bytecode artifact refines its Solm
specification. You goal is to complete the proof of the top-level theorem 
in `Correct.lean` with no `sorry` and no added axioms, except for the 
accepted trusted base below.

```lean

You are given a working directory, which is named after the contract
(`<Name>/`) and includes:

- The EVM bytecode (file `Bytecode.lean`).

- The source it was compiled from (e.g., `<Name>.sol`), plus the exact
  compiler and options used to produce it. The bytecode can be of
  arbitrary provenance — do not assume a specific compiler or
  version. Always check.

- The Solm specification of the contract, including its storage
  layout. (file `Spec.lean`)

- A correctness file stating the top-level theorem with a `sorry`
  placeholder. (file `Correct.lean`)

The top-level theorem bundles the correctness of the constructor:

```lean
constructorEquivalence <config> <initcode> <contract> <runtimeBytecode>
```

and the correctness of the runtime code:

```lean
runtimeEquivalence!?! <config> <runtimeBytecode> <contract>
```

Your goal is to complete the proof. The proof must be correct,
modular, fast enough to work on, and axiom-clean except for the
accepted trusted base below.

Be forthcoming with blocking issues. Never bypass a problem to move on
to the next proof, and never circumvent it. If you suspect something
is unprovable, investigate thoroughly, report it immediately to the
user, and do not continue until it is resolved.

You should only work in the `<Name>/` directory. Do not make changes
outside of it.

## 1. Overall Workflow

### Phase 0: Evaluate the spec and bytecode

Do a thorough read of the Solm spec and the bytecode. Check that the
Solm spec matches the bytecode's storage reads/writes, arithmetic, and
control flow. If you find a mismatch, report it immediately. After
this pass, you should be confident that the Solm spec is a faithful
model of the bytecode, and that it is possible to prove the
refinement.

Things to watch for:

- The Solm spec, in general, must model storage reads/writes in the
  order the bytecode performs them. This is not a hard rule, for all
  data types. But for mapping, array, string and byte types this is
  important as otherwise you will have to introduce a slot noncollision
  axiom to prove the refinement, which is not allowed.

  If you find that you need such an axiom, evaluate whether the Solm can 
  be written 
  differently to exactly model the bytecode's storage reads/writes. 
  If it can, rewrite the Solm spec to do so.
  
  Only add such axiom if the compiler has done an optimization that cannot 
  be reflected in the Solm spec and the proof cannot be completed without it.

- The Solm spec must use helper functions where possible and not
  inline the same logic in multiple places. This is important for
  modularity and reusability of proofs.

- The storage layout in the Solm spec must match the storage layout in
  the bytecode. If there is a mismatch, report it immediately.

### Phase 1: Scaffold the proof

Create the top-level scaffold of the proof in `Correct.lean`. This
includes the dispatch skeleton, the per-function `…BodyCore` lemmas,
and the revert paths. The top-level theorem should type-check and
route correctly before the leaves are done. Reuse the available
machinery drivers for dispatching (e.g., `solcDispatchReachBody`).

1. Add the dispatch handler to the main theorem first. Wire the full
   dispatcher (`by_cases` on `callvalue`/`size`/each selector, routing
   each selector to its per-function `…BodyCore`, plus the shared
   revert paths). This skeleton should type-check and route correctly
   before the leaves are done. Add the necessary ABI selector axiom 
   as needed.

2. For each ABI function `<Fn>`, route to a `…BodyCore` whose proof is
   a `sorry`. That `…BodyCore` should be defined in that function's
   own file `<Fn>.lean`.

3. Create a `…BodyCore` lemma for the constructor in
   `Constructor.lean` file.

4. The skeleton of the proof should now route every function and the
   constructor correctly through the main top-level dispatch.

*Hard rule*: You should set up the dispatch skeleton and the per ABI 
function theorems (initially with `sorry`) in their own files before 
proving any of the functions. 

It is likely that some of the `Examples/` proof templates will be useful 
for this phase. You can use them as a reference for the ABI dispatch skeleton.

### Phase 2: Prove each function

Finish each function's `…BodyCore` lemma in its own `<Fn>.lean`
file. If the proof gets difficult, do not try to bypass the problem
and move to another function. Investigate thoroughly and report
immediately any blocking issues you may find.

You should tackle proofs in order of dependency: if function `f` calls
function `g`, prove `g` first, then `f`. This is true for both
internal and external calls.

The proof of each function follows, roughly, four phases:


1. ABI decode. Prove decode succeeds for valid calldata and fails on
   each malformed branch (short / huge / non-canonical address
   lemmas). Use the `decodeCalldata_*` library lemmas
   (`decodeCalldata_address_ok`, `decodeCalldata_uint256_ok`,
   `…_none_short`, `…_none_huge`, `…_none_noncanon`). One `simpa …
   using <lib lemma>` per branch (see `BalanceOf.lean`).

2. Add trusted selector facts for the public selectors in `Trusted.lean`.

3. Solm source body. Prove the `ExecTransitionBody` result (return
   value / storage update / revert) using `Reasoning.SolmBody`
   (`ExecStmt`/`ExecBlock` combinators, `evalExpr_*`, `requireStep`,
   `returns`). For mutating functions, split success and revert
   branches early.

4. EVM reachability. Thread the bytecode trace from the body entry PC
   to `RDret` (success) or `RDrev` (revert) using `evm_run … with [ …
   ]` cooked-step chains and factored `RD.*` routine lemmas. Never
   write one giant `evm_run`; split into named `have`s, one per
   phase/routine.

5. Connect. `reEquivExecution` / `reEquivDecodingFailed` /
   `reEquivNoDispatch` / `reEquivElim` glue the source result, the
   decode fact, and the EVM `RDret`/`RDrev` into
   `runtimeEquivalenceFor`.

---

### Phase 3: Prove the constructor

In a similar manner, prove correct the constructor body.

---

### Phase 4: Finish the proof

After you have proved all the functions and the constructor, verify
that the top-level theorem complies with no added axioms and no
`sorry`/`admit`. Report the axiom footprint.

---

## 2. Accepted axioms

The only acceptable trusted facts are:

- The selector / jump-dest facts in `Bytecode.lean` (the selector
  bytes of each function).

- Axioms that already exist in `Reasoning/`, including the
  external-call axioms described in §6.

Do not introduce new axioms about EVM semantics, Solm semantics, or
mapping-slot noncollision. If you think you need one, stop, report the
situation, and ask for guidance.

---

## 3. File layout

You should work exclusively in a directory `<Name>/` for the contract
you are proving.  The file structure is the following:

The proof of a contract `<Name>` goes in a directory `<Name>/`:

| File | Role |
|---|---|
| `<Name>.sol` | the Solidity source + the exact compiler invocation used. |
| `Spec.lean` | the Solm `ContractDecl`, storage layout, `Config`. |
| `Bytecode.lean` | runtime bytecode + selector/jump-dest trusted facts. |
| `Common.lean` | contract-wide ABI / memory / selector / return / other helpers shared by ≥2 functions. |
| `Storage.lean` | contract-wide storage load/store + RBMap preservation + bool-return facts (only if it has storage). |
| `<Fn>.lean` | one file per interface (public/external) function — its decode, source body, EVM trace, and `…BodyCore` refinement. |
| `Constructor.lean` | the equivalence proof of the contract's constructor. |
| `Correct.lean` | thin top-level: dispatcher driver + per-function routing + revert paths + constructor packaging + the final `theorem <name>Correct`. |


- At least one file per external ABI function. Never put two ABI
  functions' proofs in one file, never fold a function's body proof
  into `Correct.lean` or `Common.lean`, and never let `Correct.lean`
  carry body-specific complexity.

- Shared machinery used by several functions goes in
  `Common.lean`/`Storage.lean`/`Routines.lean`, not in any one
  function's file. Internal/private functions are not ABI
  entries. Their proofs can go into common files or their own
  standalone files.

- You can add further helper files in `<Name>/` for common lemmas and
  helpers.

- **Hard rule:** do not let files grow past 2000 lines. If this
  happens you should split them into smaller files by concern.

---

## 4. Reasoning library and reuse

`Reasoning/` is a library of abstractions, lemmas, and tactics for
proving EVM bytecode correct against its Solm spec. Useful reads:

- `Reasoning/GUIDE.md` — the library map: where every kind of fact
  lives, import layering, and the gotchas (native_decide for decode,
  `RD.foo rd` not `rd.foo`, heartbeat budgets, etc.).

- Each `Reasoning/*.lean` file's `/-! # … -/` header — per-module
  detail.

How to use the library:

- Respect and extend the library's abstractions. Almost every line should apply a library lemma.
  A reusable, contract-independent fact the library lacks is a missing library lemma. Add it
  (proved) to the current working directory's `Common.lean` (or another local common file), 
  tagged `-- LIBRARY CANDIDATE: <generalizes…>`
  (or `-- GENERALIZES Reasoning.<Module>.<lemma> …` for a near-variant). 

- Never edit `Reasoning/` yourself

- Do not reinvent. The library already discharges the solc prologue,
  non-payable guard, calldata-size guard, selector load,
  `RD.dispatchTo` selector routing, ABI decode/encode, memory/storage
  round-trips, and the `RD`/`RDret`/`RDrev` stepping
  discipline. Almost every line you write should be applying a library
  lemma, not proving EVM semantics from scratch. Before writing any
  arithmetic / calldata / memory / dispatch proof by hand, search for
  an existing lemma.

- Never duplicate lemmas and proof work. Always search `Reasoning/`
  for existing lemmas before proving a new one.  If you find yourself
  proving the same fact in two places, refactor it into a single lemma
  in a common file.

- You should strive to build generic, modular, and reusable
  infrastructure in your proofs and follow the library abstractions.
  This will make your proofs more maintainable and easier to
  understand.

- After you are done with your proof, someone will evaluate it for
  generality and reusability.  If your lemmas are deemed general
  enough, they will promote your lemmas to the `Reasoning/` library.
  If they find that your lemmas are too specific, they will ask you to
  refactor them into more generic lemmas that can be reused in other
  proofs.

- Lemma hygiene:

  1. Make lemmas useful and general. The new lemmas that you add
     should be as generic as possible, avoiding hard-coded PCs,
     widths, types, and stack tails when possible.

  2. Do not prove anticipated lemmas, unless you are 100% sure they
     will be used in the final proof.

  3. Before introducing a lemma, search `Reasoning/` and the existing
     examples for one that already exists — do not re-prove it.

  4. Never duplicate a lemma. If you find yourself writing the same
     lemma in two places, refactor it into a single lemma in a common
     file. If you find yourself proving similar lemmas in two places,
     consider generalizing the lemma to make it reusable.

  5. Add lemmas in the working directory (shared ones in common
     files), then flag the contract-independent ones for promotion to
     `Reasoning/` (below). Do not add lemmas directly to `Reasoning/`.

- The library is not yet exercised by every Solidity construct. As you
  prove new patterns you will find segments that are
  contract-independent and reusable and can be promoted to the
  library.  When you do:

  1. Make sure the theorem is not already proved in `Reasoning/`. Search first.

  2. If your lemma is a near-miss of an existing one (same shape,
    different PC/width/type/stack tail), that is a generalization
    opportunity: write your version in the common file and mark it `--
    GENERALIZES Reasoning.<Module>.<lemma> — lift by parameterizing
    over <what differs>`, so the library lemma can later be widened to
    subsume both instead of accreting near-duplicates.

  3. If it's genuinely new but contract-independent, mark it a fresh
     `LIBRARY CANDIDATE`.  The goal: every reusable fact ends up in
     one place, tagged with where it belongs in `Reasoning/`, so
     lifting it later is a mechanical move, not a hunt across function
     files.

  4. Collect all candidates in common files per example so the lift is
     mechanical, not a scavenger hunt.

  5. A lemma is library-ready only if it references no example-local
     defs. Watch for per-example abbreviations (`addr`, `uint256`,
     `uint256Int` are redefined in each `Spec.lean`); inline the raw
     type or it won't compile in the library.


---

## 5. Examples

The `Examples/` directory contains a set of template proofs. You can
use them as a reference for your own proof.

Look at the examples to find known patterns and proof templates for 
your proof.

Note that not all examples are derived with the same compiler,
version, and optimization settings. Always check the source and
bytecode for your contract.

The examples may lag behind recent Solm changes (they are migrated in
batches). If an example does not compile, use it as a *reading*
reference for trace/dispatch/proof patterns only — do not build it and
do not copy its conventions blindly. In particular, examples written
before the multi-value-return change show the old return conventions
(`returnType := some T` / `.return e`); the current convention is
lists (`returnType := [T]` / `.return [e]`, multi-value
`.return [a, b]`).

- For an example of binary search dispatch, see `Examples/Ballot`. 
- For an example of linear dispatch, see `Examples/ERC20`.


*Hard rule:* do not import code directly from `Examples/` into your proof. 
If you find yourself needed the same lemma, prove it in your own working 
directory and flag it for promotion to the library if it is general enough.

---

## 6. Function Calls and loops

Function calls should be proven modularly. In particular:

- External calls (calls to other contracts):

  All external calls are proved correct by showing the bytecode and
  the source semantics make to the same opaque Ethereum.EVM.Θ
  invocation. Runtime RD lemmas produce the Θ witness; calldata/target
  lemmas prove the bytecode memory slice matches the source ABI call;
  then callCoincides or direct callViaEVM.callMade turns that into the
  source-side call relation, with account-map transport handled by
  typedCallViaEVM_accountMapEquiv or callViaEVM_accountMapEquiv.

  For static external calls, you may also use the proved fact that the
  accounts storage is preserved by the call.

- Internal calls:

  For internal calls, never inline the caller proof manually. Prove
  the callee body once as an ExecFuncBody, then use
  internalCallFunctionReturn or internalCallFunctionRevert to
  discharge the caller’s .internalCall statement by supplying argument
  evaluation, function lookup, parameter binding, and the callee body
  proof.

  This is also true when a public function is also called internally
  by another function of the contract. The callee body is proved once,
  and the caller uses the callee’s lemma to discharge its internal
  call.

  Reference: `Examples/Reuse`; larger patterns occur in Ballot and
  BlindAuction.

  If a function `f` is called internally by another function `g`,
  prove `f` before tackling the proof of `g`.


- Loops: 

  The `Examples/BlindAuction` example has a big complicated loop in the 
  `Reveal` function and shows how to prove loops by induction: state
  the invariant over the loop counter, prove a single reusable
  body-step lemma, and close the loop by induction on the remaining
  iterations, on both the Solm side and the bytecode trace.
---

## 7. Build discipline, tactics, proof engineering, efficiency

- Every file should compile and should be validated by the build
  system.

- Builds are slow. Only recompile when necessary. Do not make
  pointless recompilation attempts.

- Quick elaboration is important. Prefer `simp only` over `simp`, and
  `native_decide` over `decide`. Avoid tactics that blow up build
  time.

- Don't rebuild the world to check a leaf lemma.

- If your proof is taking too long to compile, you should evaluate
  your tactics and see if you can optimize them.  You may also
  consider splitting the proof into smaller lemmas to improve
  compilation time.

- Develop new lemmas in a small scratch file, not by editing the large
  file in place. Heavy files take minutes to rebuild and every edit
  re-elaborates the whole file. Create a throwaway
  `<Name>/Scratch.lean` in your working directory that imports the real file (so its
  defs/lemmas are in scope, compiled once and cached) and develop the
  new lemma there with fast cycles. Once it compiles clean, move it
  into its proper file and delete the scratch.

- Decode obligations use `native_decide`, not `decide` (~20× faster on
  big bytecode). `evm_run` cooked steps auto-supply it; raw steps
  write `(by native_decide)` for decode, `(by decide)` for small side
  conditions, `(by jump_dest)` for jump-dest membership, `(by evm_ov)`
  for stack-overflow bounds. Keep these — the resulting `ofReduceBool`
  axiom dependency is expected and fine.

- Raise `maxHeartbeats` only on the file/lemma that needs it, with
  `set_option … in` on that one theorem, not globally.

---

## 8. Routine-lemma discipline

Every repeated bytecode segment becomes one `RD`-combinator lemma,
proved once, applied many times:

- A straight-line bytecode segment `pc_in → pc_out` over a stack tail
  `R` becomes a theorem of the form `RD code … pc_in (args ++ R) … → ∃
  k' C', RD code … pc_out (results ++ R) …` (or `→ RDret` / `→ RDrev`
  for terminal segments). See `RD.routine9c`, `RD.routinebb`,
  `RD.routinecf`, `RD.erc20DecodeAddrMask`,
  `RD.erc20MappingHashSuffix`, `RD.erc20RoutineEncodeUint256`.

- These chain directly: `rd |>.routineA … |>.routineB …` (call as
  `RD.foo rd …`, not `rd.foo` — the `RD` type whnf's to an
  `Or`). Factor over a generic tail `R` so the lemma is reused at
  every call site regardless of what else is on the stack.

- Before writing a trace, scan the bytecode for segments solc shares
  (decoders, the address mask/cleanup, the mapping-hash `keccak`
  suffix, the uint256 ABI encoder, identity `cleanup_t_*`
  routines). solc emits these once; prove them once. If you find
  yourself writing the same `evm_run [...]` block in two functions,
  stop and extract a lemma.

- Generalize hard-coded constants (PCs, widths, types, stack tails)
  into lemma parameters wherever possible, so the lemma is reusable
  across functions. If a lemma is truly contract-independent, flag it
  for promotion to `Reasoning/`.

- Split traces into `have`s, one per sub-trace / routine. A single
  giant `evm_run` over a compound tail blows the heartbeat/`whnf`
  budget. Factoring a routine over a generic tail `R` needs
  `set_option maxHeartbeats 1000000 in` and intermediate `have`s — see
  the note in `Reasoning/GUIDE.md` and `RD.erc20DecodeAddrMask`.

Disassemble — never guess PCs, opcodes, or jump-dests. The biggest
failure mode in these proofs is guessing contract-specific constants:
the exact `evm_run … with [push2 ⟨71⟩, dup1, …]` opcode sequence for a
basic block, the entry/exit PCs, the jump-dest set, the selector
bytes, the stack shapes. These are a pure function of the bytecode —
one wrong token fails late and opaquely and wastes a whole cycle. Read
them off the actual bytecode: disassemble `Bytecode.lean` (a short
script, `evmasm`/`solc --asm`, or by decoding the byte array) to get
each block's exact cooked-step list, its PCs, and the jump-dest array
before writing the trace. Treat the trace as "fill in the
side-conditions of a known opcode list," not "invent the opcode list."
When a step fails, re-check it against the disassembly first.

---

## 9. Hard rules

- Do not make changes outside of your working directory.

- Do not build examples and benchmarks that are not your own. This is extremely
  important as builds are extremely expensive and time-consuming.

- If you find misspecifications, mismatches, or unprovable
  obligations, stop and report them immediately. Do not continue until
  they are resolved.

- Edit `Spec.lean` only if you are certain it is wrong, and report the
  change immediately. Do not change the given bytecode or Solidity
  source.

- Never edit `Bytecode.lean`. If you suspect it is wrong, report it
  immediately.

- No `sorry` in the finished proof.

- Do not introduce new `axiom`, unless explicitly told to do so. If
  you think you need one, stop, report the situation, and ask for
  guidance.

---

## 10. Finish checklist

Run, and report results verbatim:

```
lake build <Module>.Correct
rg -n '\b(sorry|admit)\b' <WorkDir>
printf '%s\n' 'import <Module>.Correct' '#print axioms <Namespace>.<name>Correct' | lake env lean --stdin
```

where `<WorkDir>` is your working directory, `<Module>` its Lean module
path, and `<Namespace>` the contract's namespace — e.g. for
`Examples/ERC20/`: `Examples.ERC20`; for `Benchmarks/Dss/Dai/`:
`Benchmarks.Dss.Dai`.

The build must succeed with no `sorry`.

The axiom footprint should contain only
`propext`/`Classical.choice`/`Quot.sound`, the expected `ofReduceBool`
(from `native_decide`), the pre-existing library axiom
`ByteArray_zeroes_size`, your contract's selector/jump-dest facts, and
— for any contract with an external call — the tolerated external-call
axiom `Reasoning.Reach.Theta_returnData_size_lt_2pow138` (a known
trusted base being removed separately; do not block on it).
(`typedCallViaEVM_accountMapEquiv` is a proved theorem in
`Reasoning/ExternalCall.lean`, not an axiom — it does not appear in the
footprint.) Flag only anything beyond this set — a new axiom your work
introduced.
