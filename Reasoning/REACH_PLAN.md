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
