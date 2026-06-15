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
