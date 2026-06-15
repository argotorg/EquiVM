# Reach — design notes

`Reach.lean` factors out the straight-line stepping boilerplate that dominates EVM-equivalence
proofs (per opcode: a `set sN := st<op> …`, the `have hcN/hpN/hgN/hXN …` bookkeeping, and the
`by_cases` out-of-gas split — ~8–10 near-identical lines, repeated ~150× across a contract).

**Scope:** straight-line segments. Control flow stays ordinary Lean and composes by `RD`
transitivity — branches by `by_cases` + value lemmas, loops by induction (`RD.loop` is the
template), solc subroutines as `RD → RD` combinators. `CALL`/`CREATE` are out of scope (a single
`Xstep` there hides a recursive sub-execution).

## The shape

`RD … : Prop := OOG ∨ ∃ s, X(g+1) s0 = X(g+1-k) s ∧ s.pc=pc ∧ s.stk=stk ∧ s.gas=g-C ∧ … ∧ k≤C≤g`.
Each combinator is a forward implication `RD pc (a::b::t) … → decode → RD (pc+1) (b::a::t) …`;
chaining is function application; the OOG case threads inside the `Prop`. This Prop-predicate shape
(rather than an indexed `Type`) is what makes the conclusion close cleanly — a fixed-`pc`/fixed-stack
goal *is* the `RD` itself, with no post-`cases` opacity.

## Key decisions

- **Counters, not gas-pinning.** Track steps `k` and gas burned `C` with `k ≤ C ≤ g`. The
  `X(g+1-k) = X(g+1-(k+1))` step lemmas hold unconditionally on termination; the gas-pinned
  alternative would need fuel monotonicity at every step.
- **Carry everything the conclusion asserts.** `pc`, `stk`, `C`, and any preserved value (`mem`,
  `aw`, accounts) are pinned fields on *every* combinator — across the OOG boundary the final state
  is opaque, so preservation cannot be recovered at the end; it must ride along. `mem`/`aw` are
  initialized at `start` to the input's, so relative clauses (`s'.mem = s.mem`) fall out for free.
- **Symbolic arithmetic.** A binop yields the symbolic result (`UInt256.lt a b`); resolving it to
  `⟨0⟩`/`⟨1⟩` for a branch is a manual value-lemma at the call site. The library shortens
  stack/gas/pc mechanics, not branch reasoning.

## Delivered surface

The per-opcode combinators, the `evm_run` macro (auto-fills decode/overflow proofs), the
`RDret`/`RDrev` halting terminals, and the `RD → Act` `reEquivElim` eliminators — see `NOTES.md`.
All generic over `code`; `Examples/Pow` and `Examples/Truth` are both expressed through them.

## External calls (in progress) — `RD.call` recipe

State of play (all green): `RD` carries read-only world fields (`RDWorld s0 s` = `σ₀/gh/blocks`);
`externalCallViaEVM` abstracts the **full** input substate (`∃ A_in callGas`); trusted axiom
`Theta_returnedGas_le` (`Θ` returns `g' ≤` forwarded gas); `RD.sstore` done.

`RD.call` is **opaque** — it never inspects the callee. Develop it from this verified `step_call`
reduction (value `= ⟨0⟩`, `depth.val < 1024`, `t.length + 1 ≤ 1024`):

```
have st := step_call s hd; rw [hstk] at st
have hovF    : (t.length+1+1+1+1+1+1+1-7+1 > 1024) = False := eq_false (by omega)
have hstaticF: (¬ s.executionEnv.perm = true ∧ ({val:=0}:UInt256) ≠ {val:=0}) = False :=
                 eq_false (by rintro ⟨_,h2⟩; exact h2 rfl)
have hdepthLt: s.executionEnv.depth < 1024 := by rw [Fin.lt_def]; exact hdepth
have hbal : ∀ y:UInt256, (({val:=0}:UInt256) ≤ y) = True := fun y => eq_true (Fin.zero_le _)
have hgtF : ∀ y:UInt256, (({val:=0}:UInt256) > y) = False := fun y => eq_false (Fin.not_lt_zero _)
have hdeqF: (s.executionEnv.depth == 1024) = false := by
              rw [beq_eq_false_iff_ne]; intro hh; rw [hh] at hdepth; exact absurd hdepth (by decide)
simp only [List.length_cons, hovF, hstaticF, if_false, hdepthLt, hbal, hgtF, hdeqF,
  and_true, if_true, true_and, Bool.or_false, Bool.false_or] at st
-- st : Xstep s = if gas<memCost then OOG else if gasAvail'<gasCost then OOG
--                else .ok (SUCC, none),  SUCC = step_call successor with the Θ-branch taken,
--   stack := (if !(θ).z then ⟨0⟩ else ⟨1⟩) :: t,  memory := o.write 0 mem outOffset (min outSize ‖o‖),
--   accountMap/createdAccounts/substate := (θ).proj,  gas := gasAvail' - ofNat gasCost + g',  pc+1.
```

Then: combine the two OOG guards into threshold `memCost + gasCost`; `by_cases`; OOG ⇒ `stepOOG`,
else `stepContinue`. Conclusion (existential, no callee identity, world fields via `hworld`,
`A_in := (s.addAccessedAccount tAddr).substate`, `callGas := Ccallgas …` as witnesses):

```
∃ cA' σ' z o A_in callGas k' C',
  (∃ g'' A', (cA',σ',g'',A',z,o) = Θ ee.blobVersionedHashes cA s0.genesisBlockHeader s0.blocks σ s0.σ₀
       A_in (AccountAddress.ofUInt256 (.ofNat ee.codeOwner)) ee.sender (AccountAddress.ofUInt256 target)
       (toExecute σ (AccountAddress.ofUInt256 target)) callGas (.ofNat ee.gasPrice) ⟨0⟩ ⟨0⟩
       (mem.readWithPadding inOffset.toNat inSize.toNat) (ee.depth+1) ee.header ee.perm)
  ∧ RD code ee g s0 (pc+1) ((if z then ⟨1⟩ else ⟨0⟩) :: t)
       (o.write 0 mem outOffset.toNat (min outSize (.ofNat o.size)).toNat)
       (.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat) outOffset.toNat outSize.toNat))
       (cA', σ') k' C'
```

Gas arithmetic (`C' = C + memCost + gasCost - g'.toNat`):
* value 0 ⇒ `Cextra = Caccess ≥ Gwarmaccess = 100 ≥ 1`, `Ccall = Cgascap + Cextra`, `Ccallgas = Cgascap`,
  and `Cgascap` depends on `μ` only via `μ.gasAvailable` (so the `gasState` vs `callMachineState`
  `execLength` difference is irrelevant) ⇒ `callgas ≤ gasCost` and `1 ≤ gasCost - callgas`.
* `Theta_returnedGas_le` ⇒ `g'.toNat ≤ callgas` (using `callgas < UInt256.size` from `Cgascap ≤ gasArg.toNat`).
* hence `g'.toNat < gasCost`, so net CALL cost `≥ 1`, `k+1 ≤ C'`, `C' ≤ g`, no `UInt256` wrap.

After `RD.call`: trace continues RETURNDATACOPY/decoder/`RD.sstore`/STOP; the caller proof instantiates
the Act `externalCall`'s `A_in`/`callGas` to these witnesses ⇒ `Θ_Act = Θ_EVM` ⇒ same opaque `(z,σ',o)`.

### WIP file: `RDCall.lean` (repo root, not in any build glob)

`RD.call` is under construction in `RDCall.lean`. Done & compiling: full statement, the `step_call`
reduction (above), `X_peel`+`split` cursor stepping, and the **OOG branch fully proven**. The single
`sorry` is the success branch — emit `Or.inr ⟨SUCC, …⟩` (SUCC is concrete in `hXP`) with the field
projections, the gas arithmetic (`C' = C + memCost + gasCost − g'.toNat`, facts above), and the
`Θ`-link by tuple-eta. Move into `Reasoning/Reach.lean` once the `sorry` is closed.

---

## External calls — STATUS (2026-06-15, updated)

**DONE & green (whole project builds; one `sorry` left, in the Caller success path):**
- **`RD.call`** — fully proved, moved into `Reasoning/Reach.lean` (after `RD.sstore`). Only the
  `Theta_returnedGas_le` axiom + Lean/evmlean base. The `RDCall.lean` WIP file is deleted.
- **`RD.and` / `RD.shl`** combinators + `and_xstep`/`shl_xstep` (Stepping.lean) — Caller's body/decoder
  use AND/SHL which Pow didn't.
- **`Examples/Caller/Correct.lean`**:
  - dispatch facts, `callerBodyReverts`, `callerEvmSelector`, `callerContains{15,41,45,348}`.
  - revert traces: `callerX_callvalue_ne`, `callerX_cvz_prefix` (→pc24, k14 C53),
    `callerX_cvz_short`, `callerX_cvz_revertB` — all proved.
  - `callerX_disp` (→pc45, k24 C96), `callerX_toDecoder` (→pc348, k38 C140) — proved.
  - **Coincidence crux PROVED**: `accountAddress_roundtrip` (160-bit `ofUInt256∘ofNat = id`),
    `wordOfInt_zero`, and **`callerCallCoincides`** — given the EVM `Θ`-link (from `RD.call`, in
    `evm.*` form) + couplings (`tgt = ofUInt256 targetWord`, `encode? "pow2" [n] = mem.read…`,
    `perm = true`, `depth ≠ 1024`), the Act `externalCallViaEVM` holds for the *same* opaque
    `(z,σ',o)`. Built via `@externalCallViaEVM.callMade (x := fun _ _ => g'') …` (the discarded-gas
    implicit `x` must be pinned, else higher-order unification fails on the `⟨callGas,A_in,h⟩` tuple).

**REMAINING = the one `sorry`** (`callerReEquiv_callvalueZero`, matching-selector branch). Plan:
1. **Decoder** `abi_decode_(address,uint256)`: pc 348 → returns to 66 with `[t, n, …]`. Execution
   order (success, `size ≥ 68`): 348 bounds-check (`SLT(E-4,64)=0`, needs a `slt64_zero` helper like
   Pow's `slt32_zero`) → 370 → arg0 path 277→255→238→207(AND mask)→…→264 with a **clean-address**
   check at 266 `EQ(tw, land tw mask)` then JUMPI 274 (success needs the address canonical, i.e. high
   96 bits zero ⇒ `decodingFailed` otherwise) → arg1 path 328→306→297 (uint256) → back to 66.
   Build as one `evm_run` chain (inline subroutines in execution order) or as `RD.routine*` combinators;
   trace stacks with compiler assistance (extend, read actual stack from type-mismatch, fix).
   Also a `size < 68` (or dirty-address) **decode-revert** trace ⇒ `RDrev` + Act `decodingFailed`.
2. **Body** pc 73→143: clean target (AND pc96), build `pow2` calldata in memory via encoder 425
   (PUSH4 0x442b7ffb selector, SHL, MSTORE), reach the CALL cursor at pc 143 with stack
   `[gas, target, 0, inOff, inSize, outOff, outSize, …]` — then **`RD.call`**.
3. **z-split** post-CALL (pc 144): `z=true` → 158→ return-decoder 470 → `RD.sstore` slot 0 → 73's
   caller → 71 STOP ⇒ `RDret (cA, σ[slot0 := decode o])`; `z=false` → 151 RETURNDATACOPY → REVERT ⇒ `RDrev`.
4. **Act body**: `require(callvalue=0)` (passes) → `externalCall` via `callerCallCoincides`
   (instantiate `A_in`/`callGas` to the `RD.call` witnesses) → on `z` split: `assign stored` (full-slot
   SSTORE coupling, `decode o`) or revert.
5. **Assemble**: a success-execution eliminator that does the `z`/size case-split and feeds
   `RDret.reEquivExecution` / `RDrev.reEquiv*` ⇒ discharge the `sorry` ⇒ `callerCorrect`.

---

## External calls — STATUS (2026-06-15, session 2: decoder + body trace)

**Whole project builds green; one `sorry` (Caller success path). New infrastructure all verified:**
- `RD.and`, `RD.shl`, `RD.push20`, `RD.dup7`, `RD.dup8`, `RD.gas` (+ `and/shl/push20/dup7/dup8/gas_xstep`,
  `stPush20`/`stGas`). `RD.gas` returns `∃ gv, …` (GAS pushes the cursor's remaining gas).
- `Examples/Caller/Correct.lean` now proves the **entire ABI decoder** `abi_decode_(address,uint256)`
  pc 348→66 through 7 nested sub-routines, as a chain of existential-counter lemmas:
  `callerX_dec277` → `callerX_dec264` (arg0 load+cleanup) → `callerX_dec291` (clean-address check,
  needs `hclean : eq (callerArg0 I) (land (callerArg0 I) addrMask) = ⟨1⟩`) → `callerX_decoded`
  (arg1 uint256 decode, reaches pc 66 with `[callerArg1 I, callerArg0 I, ⟨71⟩, sel]`).
  Helpers: `add4_sub4`, `slt64_zero`, `ueq_self`, `addrMask`, `callerArg0/1`, `caller_jd` macro.
- Body: `callerX_body117` (clean target, MLOAD free-ptr, build selector → reach selector MSTORE),
  `callerX_body425` (selector MSTORE → encoder entry pc 425, mem = `callerSelMem`, aw 5).

**REMAINING (the `sorry`) — each a real sub-step, NOT trivial:**
1. **Encoder MSTORE + CALL setup → CALL cursor (pc 143).** Trace 425→142 (encoder writes `n` at
   mem[132] via the 410/297 sub-routines; `mem = callerCalldataMem := (callerArg1 I).toByteArray.write
   0 callerSelMem 132 32`, aw 6), MLOAD the free-ptr at 64 (carry `loadval` SYMBOLICALLY via
   `RD.mload`'s `hval` — RD.call's offsets are free vars, so no need to prove it's 128 yet), DUP8/GAS,
   then **`RD.call`** (value 0). Stack at 143: `[gv, tgt, ⟨0⟩, inOff, inSize, outOff, ⟨32⟩, …]`.
2. **Memory–encoding coupling (HARD, byte-level).** For the Act coincidence: prove
   `callerCalldataMem.readWithPadding 128 36 = pow2Selector ++ UInt256.toByteArray (callerArg1 I)`
   AND `loadval = ⟨128⟩`, `inSize = ⟨36⟩`. Needs NEW lemmas: the 2nd MSTORE is a *partial overwrite*
   (off 132 < callerSelMem.size 160), which `toByteArray_write_eq` (write-past-end only) does NOT
   cover. Also relate `callerArg1 I` (the EVM word) to the Act decoded `n : ℤ` so `encode? "pow2"
   [.int n] = some (…)`.
3. **Post-CALL z-split (more bytecode).** pc 144: `z=true` → POP×4 → return-decoder 470 (uint256) →
   `RD.sstore` slot 0 (store `decode o`) → JUMP back → 71 STOP ⇒ `RDret (cA, σ[slot0])`;
   `z=false` → 151 RETURNDATACOPY → REVERT ⇒ `RDrev`.
4. **Act body** `ExecContractBody callerConfig callerContract … runTransition.body`: `require(cv=0)`
   passes → `externalCall` via `callerCallCoincides` (instantiate Act `A_in`/`callGas` to the
   `RD.call` witnesses; uses coupling #2) → on `z`: `assign stored` (decode coupling) or revert.
5. **Assembly.** New success eliminator doing the `z`/size/clean-address case-split, feeding
   `RDret.reEquivExecution` / `RDrev.reEquiv*` ⇒ discharge the `sorry` (the matching-selector branch
   of `callerReEquiv_callvalueZero`) ⇒ `callerCorrect`.

### MILESTONE (session 2 cont.): the opaque CALL executes in the trace
`callerX_afterCall` (Examples/Caller/Correct.lean) — PROVED & green: the full EVM trace
`initState → dispatcher → decoder → body → encoder → GAS → RD.call` reaches the post-CALL cursor at
pc 144 with `(if z then ⟨1⟩ else ⟨0⟩) :: REST` on the stack and accounts `(cA', σ')` — the opaque
`Θ` output. Memory/activeWords carried symbolically (`callerCalldataMem I`, `callerOutPtr I`). The
entire EVM side up to and including the opaque CALL is done. Remaining: post-call z-split tails
(success/​fail), memory–encoding coupling, Act body, assembly.

---

## BLOCKER (session 3): Act `decode?` is total, EVM return-ABI-decoder is partial

**Status: the theorem `callerCorrect` is FALSE as currently stated. Root cause is in the trusted
Act spec, not the proof.** Found while building the post-call z=true tail.

### The discrepancy
Post-CALL, on success (`z=true`), solc ABI-decodes the return data as `(uint256)` via the decoder
at pc 470 (`abi_decode_tuple_t_uint256_fromMemory`):
```
470 PUSH0; PUSH1 32; DUP3(dataEnd); DUP5(headStart); SUB; SLT; ISZERO; PUSH2 491; JUMPI
483 PUSH2 490; PUSH2 203; JUMP        ; 203: PUSH0;PUSH0;REVERT
```
i.e. `if slt(returndatasize, 32) { revert }`. So **`z=true ∧ returndata.size < 32 ⇒ EVM REVERTS**
(reachable: an opaque callee can `STOP` → 0 bytes, or `RETURN` <32 bytes, with success=1).

Act `defaultDecodeReturn?` (Act/Semantics.lean:517) is TOTAL:
```
if bytes.isEmpty then some .unit else some (.int (fromByteArrayBigEndian (bytes.extract 0 32)))
```
So `decode? "pow2" out = some value` ALWAYS holds ⇒ `externalCallSuccess` (Semantics.lean:722)
fires ⇒ `assign stored := tmp` ⇒ result `.ok`/`.returned` (a committed store), NEVER `.reverted`.

### Why it's a real refinement violation (not a proof gap)
For an opaque sub-call that succeeds returning `0 < out.size < 32` bytes: EVM = `.ok (.revert …)`,
Act = `.returned …` (stored). `execResultsEquiv` cannot relate a revert to a returned result, and
no other `runtimeEquivalenceFor` constructor applies (dispatch+decode of the *top-level* calldata
both succeed; not OOG). Hence the `execution` case is unprovable for this witness. Everything ELSE
is done/mechanical — this single case breaks it.

### Fix (REQUIRES changing the trusted Act semantics — user decision)
BOTH pieces are needed:
1. Make the return decoder **partial**: `decode? "pow2" out = none` when `out.size < 32` (for an
   int/uint return). (Narrow option: do it only in `callerExternalABI.decode?`.)
2. Add an `ExecStmt` rule `externalCallReturnDecodeRevert`:
   `… externalCallViaEVM … (true, evm', out) → cfg.externalABI.decode? name out = none → .reverted`.
   (Piece 1 alone leaves `z=true ∧ decode=none` with no applicable rule ⇒ `ExecContractBody`
   uninhabited ⇒ still cannot build the witness.)
Then all cases couple: `out.size ≥ 32` → success/store (matches EVM store); `out.size < 32` →
revert (matches EVM revert); `z=false` → `externalCallFailure` revert (matches EVM revert).

---

## PROGRESS (session 3): spec fix + returndata infra + z=false revert tail

**All green; the single `sorry` (matching-selector success branch) remains.**

1. **Spec blocker FIXED** (per user "apply the full fix"): `defaultDecodeReturn?` is now partial
   (`none` when `bytes.size < 32`); added `ExecStmt.externalCallReturnDecodeRevert`
   (`z=true ∧ decode?=none → .reverted`). Act/Semantics.lean. Builds clean, no other dependents.
2. **Returndata stepping lemmas** (Stepping.lean): `returndatasize_xstep` (Gbase=2),
   `returndatacopy_xstep` (two-stage gas + `b+c ≤ |rd|` guard). `memExpRevertZeroOff` (Solc.lean):
   REVERT/RETURN memory cost for offset-0, arbitrary length.
3. **RD combinators** (Reach.lean): `RD.returndatasize` (existential pushed value, like `RD.gas`);
   `RD.returndatacopyFull` (the 4-op `RETURNDATASIZE;PUSH0;PUSH0;RETURNDATACOPY` idiom copying the
   whole return buffer to `mem[0]`, discharging the InvalidMemoryAccess guard internally via
   `|rd| % 2²⁵⁶ ≤ |rd|`; memory/aw/counters existential).
4. **z=false revert tail DONE**: `callerX_postRevert` (Correct.lean) — from the post-call cursor with
   `⟨0⟩` (failure flag) on the stack, traces `144 ISZERO…JUMPI(not taken) → 151 RETURNDATACOPY…REVERT`
   ⇒ `RDrev`. Verified green.

### Remaining (unchanged shape) — z=TRUE success tail needs `returnData` tracking
The success path (144 → JUMPI taken → 158 → return-decoder 470 → SSTORE slot 0 → 71 STOP) runs the
solc ABI return-decoder, which **reads `returnData`** (RETURNDATASIZE for the `≥32` check + allocation,
RETURNDATACOPY to copy `o` into fresh memory, then MLOAD the first word → SSTORE). `RD` does **not**
track `returnData` (it hides the cursor state and pins only pc/stack/mem/aw/accounts/world). So the
stored value cannot currently be tied to the opaque `o`.

**Architectural fork to resolve before the z=true tail:**
  (a) add a `returnData` field to `RD` (≈preserved by all opcodes, set by `RD.call` to `o`, read by
      RETURNDATASIZE/COPY) — clean + reusable, but churns the whole `RD` core (~40 combinators +
      ~10 lemma signatures); OR
  (b) a parallel `RDr` predicate (RD + `returnData = rdata`) with combinators only for the ~25 tail
      opcodes; OR
  (c) one monolithic `callerX_postSuccess` lemma that rcases the post-call RD once (exposing
      `returnData = o`) and steps the whole decoder by hand.
Then: memory–encoding coupling (#2, HARD byte-level), Act body, assembly.

---

## PROGRESS (session 3 cont.): returnData added to RD (option a) — DONE, green

`RD` now carries a `rdata : ByteArray` field (sibling of `mem`/`aw`), threaded through every
combinator: `RD.start`/`startWith`/`conclude`, all ~27 per-opcode combinators, `RD.call` (sets
`rdata := o`, the opaque output), `RD.mstore`/`mload`/`sstore`/`ret`/`rev`, `RD.returndatasize`/
`returndatacopyFull` (preserve it). `solcGuardPrologueRD`/`revertStub` (Solc.lean) and all ~13
`callerX_*` RD annotations (Correct.lean) updated — pre-call `rdata = ByteArray.empty`, post-call
`rdata = o`. `callerX_afterCall` now existentially exposes `rdata'` (= the opaque `o`). Whole project
builds green; single `sorry` unchanged.

### Next: z=true success tail (now unblocked)
From `callerX_afterCall` (z=true): `144 ISZERO…JUMPI(taken) → 158 POP×4 → PUSH1 64;MLOAD → return
decoder (RETURNDATASIZE, round-up, RETURNDATACOPY copies `o` into fresh mem, subroutine 470 checks
`|o| ≥ 32`, MLOAD the word) → SSTORE slot 0 → JUMP 71 → STOP ⇒ RDret`. The stored word is
`fromByteArrayBigEndian (o[0:32])` = Act's `decode? "pow2" o`. Needs: an `RD.not` combinator (opcode
0x19 at pc 169), the decoder trace (incl. subroutine 470/450/306), and the memory↔encoding coupling
(#2). Then Act body + assembly.
