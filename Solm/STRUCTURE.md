# Solm/ structure

Sol⁻ is a source-agnostic specification language of EquiVM. Its structure
mirrors a subset of Solidity. Solidity's structs like inheritance,
modifiers are assumed to be desugared away.

Note that there are semantics differences between Solidity and Sol⁻,
for example in Sol⁻, in-memory integers have unbounded range.
This facilitates reasoning using unbounded mathematical integers, and only
converts to bounded integers at the storage boundary.

Currently, Sol⁻ does not currently model events, error payloads, or gas.
```
Solm/
├── Syntax.lean            umbrella: Syntax/Basic + Syntax/DecEq
├── Syntax/
│   ├── Basic.lean         the AST: KeyValue, EvaledStorageRef, StorageType, Expr, StorageRef,
│   │                      Stmt, contract declarations
│   └── DecEq.lean         DecidableEq instances (hand-written where `deriving` fails
│                          on nested List payloads)
├── Notation.lean          surface syntax macros
├── Value.lean             umbrella + the ABI boundary (Value.ofABI, Value.toABI?) and
│                          keyValueToWord
├── Value/
│   ├── Basic.lean         the runtime Value type (unbounded ints, structs, storage pointers, unit)
│   └── DecEq.lean         DecidableEq Value (hand-written, same reason as Syntax)
├── Storage.lean           re-exports the shared storage layer (`Storage/Basic.lean`) under
│                          the Sol⁻ names
├── SolidityLayout.lean    solc's slot assignment (slots, packing, keccak-derived
│                          mapping/array locations); the bytes/string representation is
│                          shared and re-exported from `Storage/SolcLayout.lean`
├── VyperLayout.lean       Vyper's storage layout
├── Immutables.lean        splice immutable values / library addresses into the
│                          runtime-code template (patchRuntime)
├── Semantics.lean         umbrella for Semantics/
├── Semantics/
│   ├── Types.lean         shared context: Config, ExternalCallABI, Frame
│   ├── Dispatch.lean      selector/receive/fallback dispatch, calldata bound to parameter names
│   │                      (decodeCalldata); return conventions are shared
│   │                      (`Refinement/Result.lean`, re-exported here)
│   ├── ValueOps.lean      EvalResult monad; operations on values (operators, casts,
│   │                      indexing, packed encoding)
│   ├── StorageOps.lean    operations on storage: typed read/write/clear/default
│   │                      through the layout
│   ├── Eval.lean          the expression evaluator (evalExpr?, functional)
│   ├── Calls.lean         external call and contract creation, bridged to the
│   │                      EVM's Θ/Λ (relational)
│   └── Exec.lean          statement and transaction execution relations
│                          (ExecStmt … solmExec, solmCtorExec)
├── Equiv.lean             the top-level refinement statement (contractEquivalence);
│                          account-map equivalence is shared (`Refinement/AccountEquiv.lean`)
├── Behaviors.lean         behavioural corollaries of the relation
├── Reasoning.lean         umbrella for Reasoning/
├── Reasoning/             the Sol⁻ halves of the proof library (everything that mentions
│   │                      Sol⁻ semantics or its relation), on top of `EVMReasoning/`
│   ├── SolmBody.lean      ExecTransitionBody/ExecStmt/ExecBlock lemmas, call wrappers, loops
│   ├── Reach.lean         the coupled loop rule and the `reEquiv*` case builders/eliminators
│   ├── Storage.lean       `readStorage?`/`writeStorage?`/`clearStorage?` on solc string layouts
│   ├── ABI.lean           decode facts phrased with `lookupNth?`, the Sol⁻ list bridge
│   │                      (lookupNth?_ofABIList), and the store-shaped `decodeCalldata_*`
│   │                      corollaries of the positional facts
│   ├── Dispatch.lean      dispatcher facts (`dispatchList`, single-selector bundle) and the
│   │                      `RDret`/`RDrev.reEquiv*` bridges
│   ├── ExternalCall.lean  the CALL ↔ `externalCall` boundary (`callCoincides`)
│   └── Constructor.lean   constructor (creation-code) equivalence skeletons
├── Examples.lean, Examples/     the proved examples (sources and pinned bytecode included)
├── Benchmarks.lean, Benchmarks/ the benchmark proofs and scaffolds
├── Proofs.lean, Proofs/         properties of Sol⁻ specs (invariants)
└── Template/                    per-contract refinement-proof template
```

Dependency order (each layer imports the previous):

```
Syntax → Notation
Syntax → Value → Storage(shared) → {SolidityLayout, VyperLayout}
         Value → Immutables
Semantics: Types → ValueOps → StorageOps → Eval → Exec   (Calls, Dispatch join at Exec)
Equiv: on top of Semantics and Refinement/
Reasoning/: on top of Equiv and EVMReasoning/
```

Everything is in `namespace Solm`, except `Reasoning/` (`Reasoning.Theory` / `Reasoning.Reach`,
like `EVMReasoning/`).
