# Cat proof — status & remaining-work plan

## Done (15/16 interface fns + constructor), sorry-free, axiom-clean, integrated
`Correct.lean` builds; `catContractCorrect = contractEquivalence.intro catConstructorCorrect catCorrect`.
Proved: getters `live box litter vat vow wards ilks`; auth setters `rely deny cage claw`;
file setters `file(bytes32,uint256) file(bytes32,address) file(bytes32,bytes32,uint256)`; the constructor.
Axiom footprint of each = `propext`/`Classical.choice`/`Quot.sound` + trusted `*SelectorBytes` + `decide +native`
(`ofReduceBool`); no `sorryAx`, no custom axioms. `ByteArray_zeroes_size` not even needed by the ctor.

Shared infra (frozen, reusable): `Common` (binary-dispatch reach lemmas `catReach{LowLow,LowHigh,HighLow,HighHigh}Body`,
`catUint256/AddressGetterBodyCore`, `catSelWord_eq_of_beq`, noMatch reverts), `Storage` (`catAuthGuardEval_*`,
`RD.catAuthCheckOk/Revert`, mapping/scalar store routines), `Arithmetic` (`execMin*`, `execSub*`,
`evalExpr_{mul,add,sub}256_ok/_revert`, comparisons), `Trusted` (16 selector axioms).

## Remaining: `bite` and `fileIlkFlip` — both blocked on the SAME final step (the Θ-transport connect)

### bite — foundation PARTIAL (all files build green, but content is incomplete — verified by disassembly)
- `BiteEVM.lean` — DONE: `catDispatch_bite`, `catReachBiteEntry` (→ pc 375, LOW-LOW arm 3), `catDecode_bite`, `biteLocals`.
- `BiteTrace.lean` — DONE: `catReachBiteRoutine` (pc 375→1163 reach; output stack
  `[land mask (calldataWord 36), calldataWord 4, ⟨419⟩, catSelWord I]`, mem solcFreePtrMem, aw ⟨3⟩).
- `BiteSource.lean` — **only `catBiteSourceLiveRevert`** (the live≠1 branch) + storage-read/`biteTupleLet`/checkpoint-Store
  scaffolding. **NO `catBiteSourceSuccess`, NO other revert branches.** The full Solm body must still be built (~500-700
  lines, but FAST builds, uses `Arithmetic.execMin*`/`evalExpr_{mul,add,sub}256_*` + `internalCallFunction*`).
- `BiteCall{Urns,Grab,Fess,Kick}.lean` — substantive (5-7 `RD.catBite*` lemmas each: encoding + guard + CALL/STATICCALL
  + return-decode). `BiteCallUrns` names its ilk abbrevs `biteUrnsIlk*` (collision-avoid).
- `BiteCallIlks.lean` — **only the guard reach (1 RD lemma)** — NO STATICCALL/5-word-decode helper, because the ilks
  return-decode is optimizer-INTERLEAVED with the urns calldata build (urns selector MSTORE'd at 1311 mid-ilks-decode),
  so it cannot be cleanly factored — must be hand-traced inline in the success trace.
- **NO reusable RD helpers exist (anywhere in Reasoning/ or Benchmarks/) for the arithmetic glue**: DSMath checked-`mul`
  (×5), the 4 `div`s, the 2 `min` JUMP routines. These are NEW infrastructure to build from bytecode (only
  `solcCheckedSub/AddSuccess` exist).

  REMAINING for `catBiteBody` (in `Bite.lean`, currently `sorry`):
  1. `catReachBiteRoutine` (pc 375→1163): 2-arg decode preamble; unsigned LT len-check
     `solcDecodeLenCheckOkUnsigned head=⟨4⟩ need=⟨64⟩`; final stack
     `[land((1<<160)-1)(calldataWord 36), calldataWord 4, ⟨419⟩, catSelWord I]`.
  2. The full EVM SUCCESS trace 1163→RETURN: apply the 5 `RD.catBite*` call lemmas at pc
     1233/1248, 1383/1398, 2177/2192, 2284/2299, 2516/2531, threading the arithmetic RD segments between
     (checkedMul DSMath routine, the 4 divisions with div-by-0 guard NOT taken on success, 2 `min` JUMPs,
     checkedSub/Add, litter SSTORE@6, id return via encoder 419). Many `have`s, one per routine.
  3. Revert branches: each require-fail / mul-overflow / `milkChop==0` INVALID (→ `execResultsEquiv.invalidHalt`)
     / call-failure needs its own partial trace to the revert.
  4. Connect tree: `by_cases` over the branches, each bridging the EVM trace to the `BiteSource` body via
     `reEquivExecutionGenAccountMapEquiv` (success) / `reEquivExecutionRevert`, using `callCoincides` +
     `typedCallViaEVM_(static_)accountMapEquiv` at each call. TEMPLATE: `Vow/KissSuccess.lean vowKissBody`
     (2-call version; bite is 5-call).

### fileIlkFlip — FRONT HALF COMPLETE (`FileIlkFlipCalls.lean`, builds green, 0 sorry/axiom)
Has: `(bytes32,bytes32,address)` legacy decode lemmas, dispatch/decode/locals, `catReachFileIlkFlipBody`
(HIGH-HIGH arm 3, entry 733), `RD.catFileIlkFlipDecodeToRoutine` (755→3366), auth reach + `catFileIlkFlipAuthRevert`,
the `what=="flip"` switch, and the hardest piece **`RD.catFileIlkFlipNopeEncode`** (3471→3546, the ~40-step
`vat.nope(ilks[ilk].flip)` calldata encoder). Full exact trace derived:
733→3366→3455→nope-enc→3546 guard→3561 CALL→3582 store(`setAddressOffset0Word` @ keccak(ilk,1)+0)→hope-enc→3679
guard→3694 CALL→3711→1030→302 STOP.

  REMAINING for `catFileIlkFlipBody` (in `FileIlkFlip.lean`, currently `sorry`):
  1. nope call coupling: use the `fifNopeSelMem_gapeq` decomposition (NOT `write32_eq`, which needs dest≤base.size
     but here it extends the 96-byte buffer) for the selector write at offset 128; then guard+CALL helpers
     (copy `BiteCallFess` shape).
  2. RMW store 3582→3626 (`FileAddress`'s `setAddressOffset0Word` machinery at slot keccak(ilk,1)).
  3. hope encoder+coupling+call 3626→3711 (near-copy of nope; selector 0xa3b22fc4, arg = flip from stack).
  4. epilogue → `RDret`; Solm source body via `checkedExternalCall*`/assign helpers.
  5. the 2-Θ connect (same untemplated step as bite #4, but 2 calls) — TEMPLATE `KissSuccess`.

## Practical constraints for a resume session
- Fresh compiles of the heavy `decide +native`-dense EVM-trace files are **~40 s each** (measured:
  BiteCallKick 442L = 42 s fresh, under concurrent load). NOT slow — an earlier note claiming ~30 min was
  wrong (a subagent misattributed its proof-DEVELOPMENT time to compile time). The real cost is the
  DIFFICULTY of getting the intricate trace/connect proofs right, not compile time — iterate freely.
- Do NOT hand-edit generated files to resolve name collisions — the LSP linter reformats concurrently and
  substring renames break delicate simp/elaboration. Regenerate the offending file or fix atomically in-context.
- `.lake` cache setup (if `.lake` empty): `.lake/packages` → symlink `EquiVM-proofs1/.lake/packages`;
  `.lake/build` → `cp -a EquiVM/.lake/build`. (claude2 Reasoning/Solm == proofs1's, verified.)
- `lake build` returns exit 0 WITH `sorry` (warning). Check `rg -c '\bsorry\b'` AND actual build errors —
  `sorry=0` does NOT imply the file compiles (BiteSource had 5 real errors at `sorry=0`).
