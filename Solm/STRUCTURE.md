# Solm/ structure

Sol⁻ is the high-level specification language of EquiVM. Its structure
mirrors a subset of Solidity. Solidity's structs like inheritance, 
modifiers are assumed to be desugared away.

Sol⁻ uses unbounded mathematical integers for in-memory values and arithmetic,
including negation. Overflow handling is explicit: `uintN(e)` and `intN(e)`
normalize to the target width, while `e as uintN` and `e as intN` assert that
the value is in range and revert otherwise. For example, adding 250 and 10
produces 260; `uint8(250 + 10)` produces 4; `(250 + 10) as uint8` reverts.
Storage conversion also applies the field's width. ABI encoding and modern
ABI decoding validate values instead of silently truncating them.

`/` and `%` retain mathematical (Euclidean) division and modulo. The explicit
operations `sdiv(x, y)` and `srem(x, y)` instead truncate the quotient toward
zero and give a nonzero remainder the dividend's sign: `sdiv(-5, 3)` is `-1`,
`srem(-5, 3)` is `-2`, and `-5 % 3` is `1`. Their results remain unbounded;
division, remainder, and modulo by zero revert.

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
