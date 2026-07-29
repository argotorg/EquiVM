# Solm/ structure

Sol⁻ is the high-level specification language of EquiVM. Its structure
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
│   ├── Basic.lean         the AST: StorageType, Expr, StorageRef, Stmt, contract declarations
│   └── DecEq.lean         DecidableEq instances (hand-written where `deriving` fails
│                          on nested List payloads)
├── Notation.lean          surface syntax macros
├── Value.lean             umbrella + Value↔word conversions (valueToWord, wordToElem,
│                          keyValueToWord)
├── Value/
│   ├── Basic.lean         the runtime Value type
│   └── DecEq.lean         DecidableEq Value (hand-written, same reason as Syntax)
├── Storage.lean           StorageLoc (slot/offset/size of a primitive), packed load/store
│                          within a slot, and the StorageLayout interface a compiler
│                          layout implements
├── SolidityLayout.lean    solc's storage layout (slots, packing, keccak-derived
│                          mapping/array locations, bytes/string representation)
├── VyperLayout.lean       Vyper's storage layout
├── Immutables.lean        splice immutable values / library addresses into the
│                          runtime-code template (patchRuntime)
├── Semantics.lean         umbrella for Semantics/
├── Semantics/
│   ├── Types.lean         shared context: Config, ExternalCallABI, Frame
│   ├── Dispatch.lean      selector/receive/fallback dispatch, return conventions
│   ├── ValueOps.lean      EvalResult monad; operations on values (operators, casts,
│   │                      indexing, packed encoding)
│   ├── StorageOps.lean    operations on storage: typed read/write/clear/default
│   │                      through the layout
│   ├── Eval.lean          the expression evaluator (evalExpr?, functional)
│   ├── Calls.lean         external call and contract creation, bridged to the
│   │                      EVM's Θ/Λ (relational)
│   └── Exec.lean          statement and transaction execution relations
│                          (ExecStmt … solmExec, solmCtorExec)
└── Equiv.lean             the top-level refinement statement (contractEquivalence)
                           and supporting definitions.
```

Dependency order (each layer imports the previous):

```
Syntax → Notation
Syntax → Value → Storage → {SolidityLayout, VyperLayout}
         Value → Immutables
Semantics: Types → ValueOps → StorageOps → Eval → Exec   (Calls, Dispatch join at Exec)
Equiv: on top of Semantics
```

Everything is in `namespace Solm`.
