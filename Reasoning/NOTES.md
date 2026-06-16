# Reasoning — library index

`Reasoning/` is the contract-agnostic library for proving EVM↔Solm runtime equivalence.
Two worked examples live in `Examples/` (`Pow`, `Truth`); both are **fully proved — no
`sorry`**. `lake build` is green.

Each `*Correct` rests only on: Lean's `propext`/`Classical.choice`/`Quot.sound`, the evmlean
base axiom `ByteArray_zeroes_size`, its extern-spec companion `byteArray_zeroes_toList`, and the
contract's **two** trusted axioms (`{pow,truth}SelectorBytes`, `{pow,truth}ValidJumps` — see
`MISSPEC.md`). No `sorryAx`, no `native_decide`.

## Library files

- **`Theory.lean`** — the `Ξ`→`X` reduction. `initState` (the state `Ξ` builds, shared with
  `actExec`); `Xi_{error,revert,success}_of_X`; the low-level stepping drivers
  (`stepContinue`/`stepOOG`/`stepHalt{Success,Revert}`, `X_peel`); gas/`UInt256` arithmetic
  (`toNat_sub_ofNat`); and the `reEquiv_{outOfGas,noDispatch,decodingFailed,execution}` builders
  for `runtimeEquivalenceFor`.
- **`Stepping.lean`** — per-opcode `Xstep` wrappers: a successor `def` (`stPush1`, `stMStore`, …)
  and an `<op>_xstep` lemma per opcode (`Xstep s = if gas < cost then OutOfGass else .ok (st_op …)`).
- **`Memory.lean`** — byte/memory/ABI lemmas: the big-endian round-trips (`MLOAD` decode), the
  `MSTORE` write characterization (`toByteArray_write_eq`), `readWithPadding`-as-slice, and
  `selector_toNat` (the `CALLDATALOAD`+`SHR 224` selector decode). Built on `byteArray_zeroes_toList`.
- **`Solc.lean`** — facts shared by every solc-compiled contract: the non-payable guard prologue as
  an `RD` producer (`solcGuardPrologueRD`) and the generic selector-decode `evmSelectorDecode`.
- **`Reach.lean`** — the `RD` ("Reached Disjunction") combinator algebra (see below).

## Reach: the compositional core (`Reach.lean`)

`RD code ee g s0 pc stk mem aw acc k C : Prop` is the straight-line segment invariant: either the
run is out of gas, or a cursor reached `pc` after `k` steps / gas `C` with the given stack/memory.
The proof of a bytecode segment is a **fold over per-opcode combinators** (`.push1`, `.jumpdest`,
`.mstore`, `.jumpiT`, …), each a forward `RD → RD` implication that handles the OOG case and the
bookkeeping internally.

- **`evm_run base with [op, op, …]`** — a macro that threads `base` through the listed combinators,
  auto-supplying each opcode's `decode` (`by decide`) and stack-depth (`by evm_ov`) proofs. Control
  flow carries its value proofs inline (`jump hjd`, `jumpiT hb hjd`, `jumpiNT hb`); non-uniform ops
  (`mstore`/`mload`/`ret`/`rev`/`routine*`) are written verbatim after `raw`.
- **Terminals** — `RDret`/`RDrev` record that the whole run halts (success / revert); `RD.ret` and
  `RD.rev` step the final `RETURN`/`REVERT` off an `RD` cursor.
- **`RD → Solm` eliminators** — `RDret.reEquivElim` / `RDrev.{reEquivElim,reEquivNoDispatch,
  reEquivDecodingFailed}` carry a halting `X`-fact across the `X→Ξ` bridge into a
  `runtimeEquivalenceFor` case, folding the out-of-gas alternative automatically.

So a whole proof flows `evm_run` (segments) → `RDret`/`RDrev` (terminals) → `reEquivElim` (Solm),
with no hand-written stepping. All of the above is generic over `code` — a new contract reuses it
by supplying its bytecode's `decode` facts.

## To verify a new contract

Write `Spec.lean` (Solm spec), `Bytecode.lean` (bytecode + the two trusted axioms), and
`Correct.lean` (the proof: `evm_run` chains over the bytecode, terminals, then `reEquivElim`).
`Examples/Pow` (loop + ABI decode/encode) and `Examples/Truth` (constant return) are the templates.
