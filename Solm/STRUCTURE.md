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

Integer bit operations use an explicit width and signed interpretation:
`x &[uint8] y`, `x |[uint8] y`, `x ^[uint8] y`, `~[uint8] x`,
`x <<[uint8] n`, and `x >>[int8] n`. Operands are interpreted as bit patterns
at that width; signed right shift extends the sign. Negative shift counts are
type errors. Counts at least as large as the width yield zero, or negative one
for a signed right shift of a negative value. Unqualified bit operators act on
fixed bytes, with the width carried by the values.

Contracts declare `constant`s and `immutable`s. A constant's value is a compile-time
constant expression (`evalConstExprWith`). Immutables live in the frame
(`Frame.immutables`): the constructor starts from their zero values and assigns them
with `setImmutable`, and a runtime call reads the values the constructor left. How a
compiler embeds those values in the deployed code is not part of the semantics; the
refinement relation (`Refine.lean`) quantifies over the map from immutable values to
deployed code.

Transient state is declared with `uint256 transient flag;` and stored separately in
`ContractDecl.transient`. Configure it with
`solidityTransientStorage! [contract.structs] [contract.transient]` in
`Config.transientBackend`; persistent state still uses `Config.storageBackend`.
The two layouts each start at slot zero and use the current Solidity packing rules.
The transient backend implements the same encoding and aggregate operations directly
against the executing account's `tstorage` map.

Reads and assignments resolve the declared storage kind. `delete`, `push`, and `pop`
also select the appropriate backend; local persistent-storage aliases take precedence.
Transient writes halt in static mode, while reads remain available. External calls use
the existing EVM call semantics, including account ownership and rollback; transient
state is cleared by the EVM transaction boundary, not between message calls. Solm also
supports transient aggregates as a specification extension. This does not imply Solidity
compiler support for transient arrays, mappings, or structs, or for local transient aliases.

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
├── SolidityStorage.lean   operations on Solidity storage through StorageBackend
├── TransientStorage.lean  Solidity encoding over the executing account's transient map
├── MetaSolidityLayout.lean generated layouts and persistent/transient backend macros
├── TransientTests.lean    transient packing, isolation, aggregate, and resolution regressions
├── VyperLayout.lean       Vyper's storage layout
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
└── Refine.lean            the refinement relation: result equivalences, runtime
                           refinement (runtimeRefinement), and the top-level
                           contractRefinement linking constructor and runtime
                           through the deployed immutables
```

Dependency order (each layer imports the previous):

```
Syntax → Notation
Syntax → Value → Storage → {SolidityLayout, VyperLayout}
Semantics: Types → ValueOps → StorageOps → Eval → Exec   (Calls, Dispatch join at Exec)
Equiv: on top of Semantics
```

Everything is in `namespace Solm`.
