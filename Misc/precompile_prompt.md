# Agent prompt — proving precompile-style bytecode correctness

You are proving a Solm-independent correctness theorem for a concrete EVM
bytecode artifact that implements a precompile-like pure computation. The goal
is not to prove refinement against Solm. The goal is to prove a caller-observable
bytecode specification against a trusted pure Lean model, including exact gas
consumption on valid inputs.

Your target theorem should have the shape provided by `Reasoning/Bytecode.lean`,
usually:

```lean
theorem bytecodeSpec : PrecompileSpec code accepts valid output gasCost
```

or, when every accepted input is valid:

```lean
theorem bytecodeSpec : ExactGasSpec code accepts output gasCost
```

Here `output` is the trusted pure model of the return bytearray, and `gasCost` is
the bytecode-specific exact gas cost. The gas theorem is about this bytecode
implementation, not necessarily the native Ethereum precompile gas formula,
unless the bytecode is itself the native implementation being specified.

Be direct about blocking issues. If the bytecode, copied model, or intended
validity predicate do not line up, report the mismatch rather than changing a
trusted model just to make the proof easier.

## 1. Scope

This workflow applies to precompile-style code:

- pure computation over calldata and execution context;
- no persistent storage effects;
- no external calls;
- success returns a bytearray;
- invalid inputs or exceptional execution are specified at the caller-observable
  `Θ` boundary;
- exact success gas is part of the theorem.

Do not introduce Solm refinement unless explicitly requested. A Solm file may
exist as a source artifact or comparison point, but it should not be on the proof
path for this task.

## 2. Trusted target and references

Use the pure Lean model as the semantic target.

If the model or validity predicate is copied from another repository, add a
source comment next to the copied definitions giving:

- the source repository/path;
- the commit, tag, or version if available;
- any local changes made after copying.

If the external model is known to pass conformance tests or EEST, treat it as
trusted. Do not silently modify it. If a modification appears necessary, first
show that the bytecode and trusted model disagree, or that the copied file has a
versioning/import issue unrelated to the model's intended semantics.

## 3. Caller-observable specification boundary

State the final theorem using `Reasoning/Bytecode.lean`.

Important interface definitions:

```lean
BytecodeContext
BytecodeResult
BytecodeSpec
ExactGasSpec
PrecompileSpec
ExactGasSpec.ofRDxRet
PrecompileSpec.ofRDxRetOrErr
PrecompileSpec.runValid
PrecompileSpec.runInvalid
```

The public result is `BytecodeContext.result`, which is `Ξ` projected through
`observeXi`. This intentionally matches what the `.Code` branch of `Θ` exposes:
returned gas, success flag, and return data.

Consequences:

- Out-of-gas and `INVALID` are not distinguished by the public bytecode spec.
  Both become `BytecodeResult.failure`.
- `REVERT` is different: it can return unused gas and revert data. Do not map a
  revert path to ordinary precompile failure unless the intended public behavior
  really matches.
- Invalid native-precompile inputs are normally specified as caller-visible
  failure, not as a particular internal exception constructor.

## 4. File layout

Put the proof under:

```text
Examples/Precompiles/<Name>/
```

Recommended layout:

| File or directory | Role |
|---|---|
| `README.md` | Current proof status, final theorem, trusted sources, and caveats. |
| `Model.lean` | Pure Lean model and validity/output definitions, or imports of them. |
| `Bytecode.lean` | Concrete bytecode, jump-destination facts, bytecode-local constants. |
| `Spec.lean` | Thin bytecode-spec target: `accepts`, `valid`, `output`, `gasCost`, target theorem type. |
| `Fallback/` | Low-level bytecode trace fragments and routine reachability lemmas. |
| `Correct/Interface.lean` | Shared bridge lemmas between local traces and the bytecode spec. |
| `Correct/Valid.lean` | Successful valid-input trace theorem. |
| `Correct/Invalid.lean` | Invalid-input exceptional trace theorem, if applicable. |
| `Correct/Final.lean` | Final `bytecodeSpec` theorem. |
| `Correct.lean` | Aggregate import for the complete proof. |

When the proof has semantically different cases, split them explicitly. Examples:

- `Correct/ZeroCase/`
- `Correct/PositiveCase/`
- `Correct/ShortInput/`
- `Correct/InvalidFlag/`
- `Correct/Loop/`

Keep files small enough to build and edit. As a practical limit, split files
before they become multi-thousand-line monoliths. Do not change shared
`Reasoning/` files merely to improve build times.

## 5. Overall workflow

### Phase 0: Inspect bytecode and model

Read the bytecode, trusted model, and any README/source comments.

Check:

- calldata layout;
- validity predicate;
- output encoding;
- all constants embedded in bytecode;
- jump destinations;
- loop structure;
- explicit failure paths;
- whether the implementation ever uses `REVERT`;
- whether the proof should expose invalid-input behavior or only valid-input
  exact gas behavior.

Never guess program counters, opcodes, or constants. Inspect the actual bytecode
and add trusted jump-destination facts only when needed.

### Phase 1: State the spec

In `Spec.lean`, define the intended bytecode-facing interface.

For a precompile with invalid inputs:

```lean
def accepts (ctx : BytecodeContext) : Prop := ...
def valid (ctx : BytecodeContext) : Prop := ...
def output (ctx : BytecodeContext) : ByteArray := ...
def gasCost (ctx : BytecodeContext) : Nat := ...

abbrev bytecodeSpecTarget : Prop :=
  PrecompileSpec code accepts valid output gasCost
```

For always-valid accepted inputs:

```lean
abbrev bytecodeSpecTarget : Prop :=
  ExactGasSpec code accepts output gasCost
```

Keep `gasCost` executable whenever possible. If a gas expression becomes
`noncomputable`, identify why. Do not hide proof-framework limitations inside
the spec unless there is no better option.

### Phase 2: Prove success traces with exact gas

For valid inputs, prove an `RDxRet` theorem:

```lean
theorem validTrace :
  ∀ ctx : BytecodeContext,
    ctx.executionEnv.code = code →
    accepts ctx →
    valid ctx →
    RDxRet code ctx.gas ctx.initialState (ctx.createdAccounts, ctx.accountMap)
      (output ctx) (gasCost ctx)
```

This theorem is the core functional and gas proof. It must establish both:

- the returned bytearray is the pure model output;
- the exact gas consumed is `gasCost ctx`, including the out-of-gas threshold.

Use `Reasoning/ReachExact.lean` machinery for gas-sensitive traces. Prefer
factored routine lemmas over one giant proof.

### Phase 3: Prove invalid traces, if required

For invalid inputs, prove an exceptional trace:

```lean
theorem invalidTrace :
  ∀ ctx : BytecodeContext,
    ctx.executionEnv.code = code →
    accepts ctx →
    ¬ valid ctx →
    ∃ exception errorThreshold,
      RDxErr code ctx.gas ctx.initialState exception errorThreshold
```

The exception constructor and threshold are proof details. They do not appear in
the final `PrecompileSpec` because `Θ` erases ordinary exceptional halts to
`BytecodeResult.failure`.

If the bytecode uses `REVERT`, stop and verify the intended public behavior
before using this invalid-trace shape.

### Phase 4: Close the bytecode spec

Use the interface theorem:

```lean
exact PrecompileSpec.ofRDxRetOrErr validTrace invalidTrace
```

or, for always-valid exact-gas specs:

```lean
exact ExactGasSpec.ofRDxRet validTrace
```

The final file should stay thin. It should assemble previously proved traces,
not contain low-level bytecode execution.

## 6. Loop and case discipline

Do fixed unrolling only when the computation has a genuinely fixed bound and the
resulting proof remains manageable.

For arbitrary rounds, arbitrary limb counts, or input-size-dependent loops, use
loop invariants. After enough exploration to understand the bytecode shape,
switch to parametric loop rules rather than continuing to unroll.

For `RDx` loops, track:

- the semantic accumulator;
- memory regions used by the output;
- stack shape;
- program counter;
- exact gas consumed so far;
- the condition under which the loop exits;
- the out-of-gas threshold for the loop body and exit step.

Split proof files by loop phase or semantic phase, not by incidental bytecode
chunks.

## 7. Reusable lemmas

Reusable proof facts belong in the narrowest shared file that makes sense.

Use comments to mark candidates that could later move to `Reasoning/`:

```lean
/- LIBRARY CANDIDATE:
   This lemma only depends on generic memory/word/RDx facts and should be moved
   to Reasoning if another precompile needs it.
-/
```

Do not edit `Reasoning/` unless explicitly requested or unless the existing
interface is genuinely insufficient for the theorem.

Avoid creating ad-hoc axioms. If a fact is routine but tedious, prove it locally
or isolate it as a named lemma with a clear dependency footprint.

## 8. Gas discipline

Gas in the final theorem is exact and bytecode-specific.

Do not conflate:

- native Ethereum precompile gas schedule;
- gas consumed by the bytecode implementation;
- gas remaining after `Θ` finalization;
- internal thresholds for exceptional paths.

For valid inputs, `ExactGasPost` states:

```lean
ctx.gas.toNat < gasCost ctx →
  result = BytecodeResult.failure

gasCost ctx ≤ ctx.gas.toNat →
  result =
    BytecodeResult.returned ctx.accountMap
      (ctx.gas.subNat (gasCost ctx)).toUInt256
      (output ctx)
```

This is the final public property to preserve.

## 9. Build discipline

Build targeted modules only. Do not build all of `Examples` unless explicitly
asked.

Useful checks:

```bash
lake build Examples.Precompiles.<Name>.Correct.Final
lake build Examples.Precompiles.<Name>.Correct
rg -n '\b(sorry|admit)\b' Examples/Precompiles/<Name>
printf '%s\n' \
  'import Examples.Precompiles.<Name>.Correct' \
  '#print axioms <Namespace>.bytecodeSpec' \
  | lake env lean --stdin
```

Expected trusted footprint should be limited to:

- normal Lean axioms already present in the project;
- native evaluation axioms already used by the project, if any;
- trusted bytecode/jump-destination facts in the example's `Bytecode.lean`;
- explicitly documented copied-model assumptions, if the example intentionally
  imports or axiomatizes them.

No new axioms about EVM semantics, gas accounting, or the pure model should be
introduced without explicit approval.

## 10. Completion checklist

The proof is complete when:

- the final theorem has the intended `PrecompileSpec` or `ExactGasSpec` type;
- valid inputs are connected to the pure Lean output model;
- valid inputs have an exact proven bytecode gas expression;
- invalid inputs, if any, are connected to caller-visible failure;
- the relevant target modules build;
- no `sorry` or `admit` remains in the example;
- the axiom footprint has been checked and reported;
- `README.md` describes the final theorem and no longer reads like a frontier
  debugging log.

