# Ballot — proof handoff

Read **`prompt.md`** (repo root) and **`Examples/ERC20/PROOF_GUIDE.md`** first; they are the source of
truth for the proof architecture and override anything here. This file only records the
**Ballot-specific** facts a new agent needs — above all the **binary-search dispatcher**, which is
the one piece of genuinely new machinery.

---

## 0. Status (what's done / what's left)

| File | State |
|---|---|
| `Ballot.sol` | input; solc invocation in header (optimizer ON, Shanghai, solc 0.8.35) |
| `Spec.lean` | ✅ **trusted, complete, builds.** Full ABI: 5 explicit fns + 3 auto-getters. Hand-written storage layout matching the bytecode. Do **not** edit to make a proof pass. |
| `Bytecode.lean` | ✅ **trusted, complete, builds.** Runtime bytecode, 8 selector axioms (each verified against `solc --hashes`), 64-entry `D_J` jump set (`native_decide`). |
| `Correct.lean` | ⚠️ **scaffold, compiles with 11 `sorry`s.** Top-level `ballotCorrect` routing tree is *proven* (closes); the 8 body obligations + 3 revert obligations are `sorry`. |
| `Common.lean` / `Storage.lean` / `<Fn>.lean` | ❌ not created yet |
| `Examples.lean` | ❌ Ballot intentionally **not** added (it has `sorry`s). Add `import Examples.Ballot.Correct` once proven. |

`ballotCorrect` currently depends on `sorryAx`. The 11 leaves in `Correct.lean` are the entire
work-list. Build with:
```
lake build Examples.Ballot.Correct
```
Already-true language extension done during scaffolding: **`Expr.tupleLit`** (→ `Value.tuple`) was
added to `Solm/Syntax.lean` + `Solm/Semantics.lean` so the struct getters' tuple returns encode
(`encodeABIValue?` only accepts `Value.tuple` for `.tuple` types, and `arrayLit` makes `Value.array`).

---

## 1. Contract-specific constants (read off the bytecode — do not re-guess)

### Storage layout (hand-written in `Spec.lean`, confirmed against the bytecode)
- `chairperson` : slot **0**, offset 0, 20 bytes (address)
- `voters[a]` is a `Voter` struct at base `B = keccak256(a ‖ 1)` (mapping at decl slot 1):
  - `weight`  → `B+0` (uint256)
  - `voted`   → `B+1` offset 0, **1 byte** (bool, packed)
  - `delegate`→ `B+1` offset 1, **20 bytes** (address, packed in the same slot as `voted`)
  - `vote`    → `B+2` (uint256)
- `proposals` is a dynamic `Proposal[]`: length at slot **2**; element `i` base `= keccak256(2) + 2·i`
  - `proposals[i].name`      → base+0 (bytes32)
  - `proposals[i].voteCount` → base+1 (uint256)

### Selectors → body entry PC (dispatch targets)
| selector | function | body PC | group |
|---|---|---|---|
| `0x0121b93f` | `vote(uint256)`            | `137` (0x89)  | low |
| `0x013cf08b` | `proposals(uint256)`       | `158` (0x9e)  | low |
| `0x2e4176cf` | `chairperson()`            | `203` (0xcb)  | low |
| `0x5c19a95c` | `delegate(address)`        | `245` (0xf5)  | low |
| `0x609ff1bd` | `winningProposal()`        | `264` (0x108) | high |
| `0x9e7b8d61` | `giveRightToVote(address)` | `286` (0x11e) | high |
| `0xa3ec138d` | `voters(address)`          | `305` (0x131) | high |
| `0xe2ba53f0` | `winnerName()`             | `417` (0x1a1) | high |

---

## 2. THE DISPATCHER — binary-search (the new machinery)

Unlike every existing example (Pow/Truth/Caller/ERC20/Reuse are all **linear**), Ballot has 8
selectors so solc emits a **one-level binary-search dispatcher**: a single `GT` pivot that splits the
selectors into a low half and a high half, each then a normal linear `EQ`-arm chain.

### Exact shape (decoded)
Standard solc prologue/guards/selector-load are unchanged from ERC20, and land at **pc 30** with the
selector word on the stack (same offset as ERC20's `firstArmPc`). At pc 30:

```
pc 30: DUP1                 ; [selWord, selWord]
pc 31: PUSH4 0x609ff1bd     ; pivot
pc 36: GT                   ; EVM GT = (pivot > selWord)  ⟺  selWord < pivot
pc 37: PUSH2 0x0058         ; = 88
pc 40: JUMPI                ; taken ⟺ selWord < pivot  → low group at 88
pc 41: (fall-through)       ; high group, linear EQ arms
```

- **JUMPI taken** (`selWord < 0x609ff1bd`, i.e. `UInt256.gt 0x609ff1bd selWord ≠ ⟨0⟩`): jump to
  **88 (`0x58`, a JUMPDEST)**, step the JUMPDEST, then the **low group** linear arms begin at **pc 89**.
- **JUMPI not taken** (`selWord ≥ 0x609ff1bd`): fall through to the **high group** linear arms at **pc 41**.

Note `0x609ff1bd` (`winningProposal`) is both the pivot *and* the first arm of the high group (it
matches via fall-through + `EQ`).

Linear arms within each group (standard `DUP1; PUSH4 selᵢ; EQ; PUSH2 tgtᵢ; JUMPI`), in order — these
are the `(i, firstArmPc)` arguments for `RD.dispatchTo`:

| group | firstArmPc | arm 0 | arm 1 | arm 2 | arm 3 | no-match falls to |
|---|---|---|---|---|---|---|
| high | **41** | `609ff1bd`→264 | `9e7b8d61`→286 | `a3ec138d`→305 | `e2ba53f0`→417 | local `5f 5f fd` revert stub |
| low  | **89** | `0121b93f`→137 | `013cf08b`→158 | `2e4176cf`→203 | `5c19a95c`→245 | pc **133** (`0x85`) revert |

### Build plan for the dispatcher
The pieces already exist; assemble them:

1. **Lift the GT combinator into `Reasoning`** (it's currently duplicated example-local):
   - `gt_xstep` — see `Examples/ERC20/Transfer.lean:950` (mirror of `lt_xstep` in
     `Reasoning/Stepping.lean:383`). Put next to `lt_xstep`/`eq_xstep`.
   - `RD.gt` — see `Examples/ERC20/Transfer.lean:977` (mirror of `RD.lt` in `Reasoning/Reach.lean:774`).
   Core `UInt256.gt` / `step_gt` / `.GT` decode already exist (these locals compile). This is a
   **LIBRARY CANDIDATE** (`Reasoning/Stepping.lean` + `Reasoning/Reach.lean`) — and lifting it also
   de-duplicates Transfer.lean/Reuse.lean's checked-add copies.

2. **Add a selector-split combinator** — `RD.selectorSplitTaken` / `RD.selectorSplitNotTaken`,
   *structurally identical* to `RD.selectorArmTaken`/`NotTaken` (`Reasoning/Reach.lean:1426`/`1447`)
   but with `EQ` → `GT` and the boolean being `UInt256.gt pivot selWord`:
   - taken (`UInt256.gt pivot selWord ≠ ⟨0⟩`): `jumpiT` to the low-group JUMPDEST (then `jumpdest` step);
   - not taken (`= ⟨0⟩`): fall through to the high-group first arm.
   The chain is `h.dup1 |>.push4 |>.gt |>.pushConst |>.jumpiT/jumpiNT` (copy the arm proof, swap
   `.eq` for the new `.gt`). This is a **LIBRARY CANDIDATE** (generalizes `selectorArm*`; could later
   unify EQ/GT/LT split arms under one width/op-generic lemma).

3. **Write `ballotReachBody`** (mirror `erc20ReachBody` in `Examples/ERC20/Correct.lean:92`):
   prologue → guards → selector-load (reuse `solcGuardPrologueRD` → `solcGuardCallvalueZero` →
   `solcCalldataOk` → `solcSelectorLoad`, exactly as ERC20; revert target / body pc read from the
   bytecode = **133**) to reach pc 30, then:
   - **high group**: `selectorSplitNotTaken` → `RD.dispatchTo bodyPC i (start := 41)` for `i ∈ {0,1,2,3}`;
   - **low group**: `selectorSplitTaken` → `jumpdest` → `RD.dispatchTo bodyPC i (start := 89)`.
   The selector-coupling facts (`armSelNat … = if selector matches …`) reuse `evmSelectorDecode`
   exactly like `erc20ArmEq`/`erc20Matches`; you'll need a `ballotPivotGt` fact coupling
   `UInt256.gt 0x609ff1bd selWord` to "selWord's group" (an instance of an ordering lemma on the
   decoded selector word — there is no library helper yet; prove it from `evmSelectorDecode`/word
   arithmetic, or add a small `evmSelectorGt` companion as a candidate).

4. **`ballotNoDispatch`** must cover **both** revert tails (it's harder than ERC20's single path):
   `selWord < pivot` → all 4 low arms miss → fall to pc 133 revert; `selWord ≥ pivot` → all 4 high
   arms miss → local `5f 5f fd` stub. Split on the pivot first, then mirror `erc20X_noMatch`'s
   `selectorArmNotTakenAuto` fold per half. Also prove `dispatchMsg ballotContract cd = none` for the
   no-match case (mirror `erc20Dispatch_none_nomatch`).

Once `ballotReachBody` exists, refactor each `ballot<Fn>Body` in `Correct.lean` to take the
dispatcher-reached cursor (`hreach : ∃ k C, RD … bodyPC [selWord] …`) like `erc20<Fn>Body`, and have
the top-level pass it in — instead of the current self-contained `sorry` bodies.

---

## 3. Per-function notes / gotchas

Each interface function gets its own `Examples/Ballot/<Fn>.lean` proving a `…BodyCore`
(`runtimeEquivalenceFor`) in the four phases of `prompt.md §2` (decode → Solm body → EVM trace →
connect). Shared helpers go in `Common.lean` (ABI/memory/return) and `Storage.lean` (RBMap/storage
load-store + struct-field/packed-slot facts). Suggested order, easiest first:

1. **`chairperson()`** — warm-up. Plain scalar storage read of slot 0 (address). Closest to ERC20
   `totalSupply`/`balanceOf`. Establishes the dispatcher + return-encode plumbing end to end.
2. **`proposals(uint256)`** and **`voters(address)`** — the **tuple getters**. Returns are
   `Value.tuple` (via `tupleLit`); the EVM packs the members into the ABI return (head-only, both
   tuples are static). `voters` reads a **packed slot** (`voted` at offset 0 / `delegate` at offset 1
   of `B+1`) — the bytecode does one `SLOAD` + masks; your `Storage.lean` needs the offset/size
   `storageLocLoad` facts for that slot. `proposals(i)` and every `proposals[i]`/array access does an
   **array bounds check** against length@slot 2 (`Panic(0x32)` on OOB) — model the revert branch.
3. **`giveRightToVote(address)`** — three `require`s (string-revert messages) then one packed-slot
   write (`weight` at `B+0`). Mutating + multiple revert branches; split success/revert early.
4. **`vote(uint256)`** — `letStorage` alias `sender = voters[msg.sender]`; reads via the alias; a
   compound `proposals[proposal].voteCount += sender.weight` (checked add ⇒ `inRange`, reads the
   target slot **fresh** at the assignment site — see the TransferFrom pitfall in `PROOF_GUIDE.md`).
5. **`winningProposal()` + `winnerName()`** — the **reuse pair** (`prompt.md §3`). `winningProposal`
   is `public` and called internally by `winnerName`; solc emits its body once. Factor
   `winningProposal`'s body as a reusable `RD.<…>Routine` + a standalone Solm body lemma, then apply
   *both* at `winnerName`'s internal `JUMP` and Solm `.internalCall`. `winningProposal` has a **`for`
   loop** (argmax over `proposals`) — use the `for`-loop `RD`/Solm combinators (see `Pow`'s `while`
   and `Reasoning`'s for-loop lemmas, commits "Reasoning: lemmas for for loop"). Note the loop
   increment is solc-**unchecked** `p++` (modelled as plain `.add`, no `inRange`), matching the
   bytecode (`PUSH1 1 ADD`, no overflow guard).
6. **`delegate(address)`** — hardest, do last. `while` delegation-chain walk reassigning the param
   `to`; two storage aliases (`sender`, `delegate_`); a branch (`if delegate_.voted`) with a compound
   `+=` into either `proposals[delegate_.vote].voteCount` or `delegate_.weight`. Needs the `while`
   combinator + alias reasoning + packed-slot writes (`sender.voted`/`sender.delegate` touch the
   packed `B+1` slot).

### Spec-fidelity reminders (from `prompt.md §5`)
- Model storage reads/writes **in bytecode order**; compound assignments re-read the target slot at
  the assignment site (keeps the proof free of keccak-noncollision axioms — `ffi.KEC` is opaque).
- No new `axiom` beyond the selector/jump facts already in `Bytecode.lean`; no `sorry`/`admit` in the
  finished proof. Prove RBMap/storage-map facts in `Storage.lean`, never axiomatize.

---

## 4. Library candidates to surface in the final report
- `gt_xstep`, `RD.gt` → `Reasoning/Stepping.lean` / `Reasoning/Reach.lean` (de-dups Transfer/Reuse).
- `RD.selectorSplitTaken` / `selectorSplitNotTaken` (+ an `evmSelectorGt` ordering companion) →
  `Reasoning/Reach.lean` / `Reasoning/Solc.lean`; the binary-search dispatch driver generalizes the
  linear `dispatchTo`. First contract to need it; likely reusable for any solc contract with >~4
  external functions.

---

## 5. Finish checklist (`prompt.md §6`)
```
lake build Examples.Ballot.Correct
rg -n '\b(sorry|admit)\b' Examples/Ballot
printf '%s\n' 'import Examples.Ballot.Correct' '#print axioms Ballot.ballotCorrect' | lake env lean --stdin
```
- Build clean, no `sorry`/`admit`.
- Axioms only `propext`/`Classical.choice`/`Quot.sound` + expected `ofReduceBool` (from
  `native_decide`); flag anything else (no `sorryAx`).
- Then add `import Examples.Ballot.Correct` to `Examples.lean`.
