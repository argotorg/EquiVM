# Reasoning/ — library guide (for agents)

Orientation only. **Per-module detail lives in each file's `/-! # … -/` header — that is the source
of truth.** This file covers the cross-cutting things no single header tells you: where a new lemma
goes, the import layering, and the conventions/gotchas that are easy to get wrong.

Everything here is under namespace `Reasoning.Theory`, except the `RD`/`evm_run` straight-line
execution combinators, which are `Reasoning.Reach` (`RD.*`).

## Where does X go? (routing)

| You're proving / stating … | Module |
|---|---|
| Symbolic EVM runs: `evm_run`, `RD`/`RDret`/`RDrev` combinators, `RD.whileLoop`, factored routine lemmas | **Reach** |
| Per-opcode step wrappers (`*_xstep`) | **Stepping** |
| `UInt256` arithmetic / comparisons / `compare` instances / `EQ` + low-bit mask facts | **EVMWord** |
| EVM memory & `ByteArray` byte facts (`MSTORE`/`MLOAD`/`RETURN` round-trips, `toByteArray`↔`toBytesBE`, selector-byte extraction) | **Memory** |
| ABI calldata **decode** *and* return-value **encode** facts | **ABI** |
| RBMap / EVM storage-map preservation (`storage_findD_*`, `rbmap_find?_erase_ne`) | **Storage** |
| solc boilerplate every compiled contract shares: prologue/callvalue/size guards, dispatch driver, selector load, **address-mask cleanup** (`solcAddrMask`, `solcAddrCanon_eq`, `solcAddrMask_clean`) | **Solc** |
| Generic `dispatchMsg` / selector-routing facts | **Dispatch** |
| `JUMPDEST`-membership (the `jump_dest` tactic) | **JumpDest** |
| `CALL` ↔ Solm `externalCall` opaque coupling | **ExternalCall** |
| Decode facts for creation `initcode ++ args` (per-PC decode proved on the prefix, reused for any appended ABI tail) | **Initcode** |
| Source-level Solm body execution (`ExecStmt`/`ExecBlock`) compositional lemmas | **SolmBody** |
| Proof-side bridges to the equivalence statements (`reEquiv*`, `runtimeEquivalenceFor`) | **Refinement** |
| Core runtime-equivalence theory | **Theory** |

`SolcDecode` is experimental and **unused** (intentionally not imported) — don't build on it.

## Import layering (low → high; a module may import anything strictly below it)

```
Theory,  JumpDest,  Initcode                        (base, no Reasoning deps)
  Stepping,  EVMWord,  SolmBody                     ⟵ Theory
    Memory, Storage ⟵ EVMWord+Stepping      ExternalCall ⟵ SolmBody
      ABI ⟵ Memory            Reach ⟵ Stepping+Memory
        Dispatch ⟵ Reach           Solc ⟵ Memory+Stepping+Reach
          Refinement ⟵ Dispatch         (SolcDecode ⟵ Solc, unused)
```

(`Initcode` depends only on `Ethereum.Semantics`, like `Theory`/`JumpDest`; its lemmas live under
namespace `Reasoning.Theory`.)

Place a lemma in the **lowest** module whose imports already give it everything it needs. Don't add
an *upward* import to force a placement — that's the sign it belongs in a lower module (or that you
need a small new one, as `Storage` was split out of `Memory`).

## Conventions & gotchas (these bite)

- **Target optimizer-ON solc bytecode.** Optimizer-ON is the target. The newer examples (`Ballot`,
  `ERC721`, `Ownable2Step`, `Reuse`, `SimpleAuction`, `BlindAuction`) are optimizer-**ON**; the older
  ones (`ERC20`, `Pow`, `Truth`) are optimizer-off — an artifact of how their bytecode was generated,
  not a requirement. Don't assume an optimizer-off example's PCs/shapes/lemma constants carry over to
  optimized output — disassemble and validate before reusing a concrete lemma.
- **Decode is discharged by `native_decide`, not `decide`.** `evm_run`'s cooked steps auto-supply
  `(by native_decide)` for the `decode code pc = …` obligation (≈20× faster on big bytecode); keep
  it. `raw` steps still write `(by native_decide)` for decode and `(by decide)` for small side
  conditions. `jump_dest` is also `native_decide`. So proofs depend on `ofReduceBool` axioms — that
  is expected and pervasive, not a problem.
- **Factoring a routine over a generic stack tail `R`** (or any compound, non-reducing term): needs
  `set_option maxHeartbeats 1000000 in`, and the proof split into intermediate `have`s (one per
  sub-trace) — a single giant `evm_run` blows the budget at `isDefEq`/`whnf`.
- **`rd.myLemma` dot-notation fails** (the `RD` type whnf's to an `Or`) — call `RD.myLemma rd …`.
- **Before moving an example lemma here, validate it references only library symbols.** Watch for
  example-local defs: `addr`, `uint256`, `uint256Int` are defined per-example in each `Spec.lean`
  (small abbreviations, deliberately not shared), so a "general-looking" lemma may resolve them only
  transitively. Inline the raw type or it won't compile in the library.
- **Migrating a lemma out of an example**: leave a thin re-export shim under the old name
  (`theorem erc20Foo … := libFoo …`) so the example's call sites stay unchanged.

## Building / verifying

A bare `lake build` does **not** compile `Reasoning.ExternalCall` or `Examples/*/Correct`. After
touching a shared module, build the affected `Examples.<X>.Correct` targets explicitly and scan for
`sorry`/`admit`. Editing a low module rebuilds everything above it — expect long rebuilds.
