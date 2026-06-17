import Reasoning.Dispatch

/-!
# Refinement — proof-side bridges: straight-line EVM runs ⟹ the equivalence statements

The statements live in `Solm.Equiv` (`runtimeEquivalenceFor`, `equivTransition`).  This file proves
the bridges between them and the Reasoning-layer EVM discipline (`RD` / `RDret` / `RDrev` from
`Reach`):

* `equivTransition.toRuntime` — **the dispatch glue**: a per-function equivalence
  (`equivTransition`) plus "the selector dispatches to `t`, its args decode, and the EVM whole-tx
  result is the body result" ⟹ the whole-contract `runtimeEquivalenceFor`.

The statement-level `equivStmts` (and its `RDret`/`RDrev`-driven proofs) belong here too, once a
body is cracked open statement by statement.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

/-- **The dispatch glue.**  Per-function equivalence (`equivTransition`, over the body-entry state
    `initState`) + the selector dispatches to `t` + its args decode + the EVM whole-transaction
    result `Ξ` is the body result `evmRes` ⟹ the whole-contract `runtimeEquivalenceFor`.  This is the
    only place dispatch enters; it is a direct repackaging of `runtimeEquivalenceFor.execution`. -/
theorem equivTransition.toRuntime
    {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {createdAccounts gh bl σ σ₀ A I} {g : UInt256} {callargs : Store} {evmRes}
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldata (t.params.map Param.name) (transitionSignature t).paramTypes
              I.calldata = some callargs)
    (hΞ : Ethereum.EVM.Ξ createdAccounts gh bl σ σ₀ g A I = evmRes)
    (h : equivTransition cfg contract t
          (initState createdAccounts gh bl σ σ₀ (Sat256.ofUInt256 g) A I) callargs evmRes) :
    runtimeEquivalenceFor cfg contract createdAccounts gh bl σ σ₀ g A I := by
  cases h with
  | exec hbody hequiv =>
    exact .execution hΞ (.intro hd rfl hdec rfl hbody) hequiv

/-! ## A relational Hoare logic for compiled Solm

`equivStmts code … Rpre stmts out` is the judgment  `{Rpre} stmts ~ bytecode {out}`:  from any EVM
cursor where the bytecode sits (`RD …`) and the Solm frame/state are related to it by `Rpre`, the
bytecode fragment and the Solm statement block step *together* to a matching outcome `out`.  The
structural rules (`skip`, `seq`, `consequence`) are proved once, generically; concrete per-statement
rules (`single`) are where the actual opcode↔statement work happens. -/

namespace Reasoning.Refinement

/-- A relation between an EVM reach-`Cursor` and the Solm execution state (frame + the EVM state Solm
    threads).  Concrete couplings — locals ↔ stack/memory, storage agreement — are particular
    `StateRel`s; the structural rules are agnostic to what a `StateRel` actually says. -/
abbrev StateRel := Cursor → Frame → State → Prop

/-- The three ways a compiled statement block can exit, used as the postcondition.
    `cont Rpost` — fell through to the next fragment, end states related by `Rpost`;
    `ret rv` — returned the value `rv`;  `rev` — reverted. -/
inductive StmtOutcome where
  | cont (Rpost : StateRel)
  | ret  (rv : Option Value)
  | rev

/-- **Relational Hoare judgment for compiled Solm:** `{Rpre} stmts ~ bytecode {out}`.  For every EVM
    `Cursor` at which the bytecode sits (`RDc …`) with the Solm frame/state related by `Rpre`, the
    bytecode fragment and the Solm block `stmts` step together to the outcome `out`. -/
def equivStmts (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (cfg : Config) (returnType : Option ABIType)
    (Rpre : StateRel) (stmts : List Stmt) (out : StmtOutcome) : Prop :=
  ∀ cur k C frame evm,
    RDc code ee g s0 cur k C →
    Rpre cur frame evm →
    (match out with
     | .cont Rpost =>
         ∃ cur' k' C' frame' evm',
           RDc code ee g s0 cur' k' C'
           ∧ ExecBlock cfg frame evm stmts (.ok frame' evm')
           ∧ Rpost cur' frame' evm'
     | .ret rv =>
         ∃ world' o frame' evm',
           RDret code g s0 world' o
           ∧ ExecBlock cfg frame evm stmts (.returned frame' evm' rv)
           ∧ world' = (evm'.createdAccounts, evm'.accountMap)
           ∧ returnEquiv o rv returnType
     | .rev =>
         RDrev code g s0
         ∧ ExecBlock cfg frame evm stmts .reverted)

/-- Append two Solm statement blocks: if the first runs to a fall-through (`.ok`) and the second runs
    from there, the concatenation runs to the second's result.  (Helper for `seq`.) -/
theorem execBlock_append {cfg : Config} {s1 : List Stmt} {f f1 : Frame} {e e1 : State}
    {s2 : List Stmt} {r : ExecResult}
    (h1 : ExecBlock cfg f e s1 (.ok f1 e1)) (h2 : ExecBlock cfg f1 e1 s2 r) :
    ExecBlock cfg f e (s1 ++ s2) r := by
  induction s1 generalizing f e with
  | nil => cases h1; simpa using h2
  | cons stmt rest ih =>
      cases h1 with
      | consNormal hstmt hrest => exact ExecBlock.consNormal hstmt (ih hrest)

/-! ### Structural rules -/

/-- **skip** — the empty block keeps the cursor and the relation unchanged. -/
theorem equivStmts.skip {code ee g s0 cfg returnType} (R : StateRel) :
    equivStmts code ee g s0 cfg returnType R [] (.cont R) := by
  intro cur k C frame evm hRD hpre
  exact ⟨cur, k, C, frame, evm, hRD, ExecBlock.nil, hpre⟩

/-- **consequence (strengthen the precondition).** -/
theorem equivStmts.consequencePre {code ee g s0 cfg returnType} {R R' : StateRel} {stmts out}
    (himp : ∀ cur frame evm, R' cur frame evm → R cur frame evm)
    (h : equivStmts code ee g s0 cfg returnType R stmts out) :
    equivStmts code ee g s0 cfg returnType R' stmts out := by
  intro cur k C frame evm hRD hpre
  exact h cur k C frame evm hRD (himp cur frame evm hpre)

/-- **consequence (weaken the postcondition)** — for the fall-through (`cont`) outcome. -/
theorem equivStmts.consequencePost {code ee g s0 cfg returnType} {R Q Q' : StateRel} {stmts}
    (himp : ∀ cur frame evm, Q cur frame evm → Q' cur frame evm)
    (h : equivStmts code ee g s0 cfg returnType R stmts (.cont Q)) :
    equivStmts code ee g s0 cfg returnType R stmts (.cont Q') := by
  intro cur k C frame evm hRD hpre
  obtain ⟨cur', k', C', frame', evm', hRD', hblock, hQ⟩ := h cur k C frame evm hRD hpre
  exact ⟨cur', k', C', frame', evm', hRD', hblock, himp cur' frame' evm' hQ⟩

/-- **seq / composition** — run `s1` to a fall-through, then `s2` to any outcome. -/
theorem equivStmts.seq {code ee g s0 cfg returnType} {P Q : StateRel} {s1 s2 : List Stmt}
    {out : StmtOutcome}
    (h1 : equivStmts code ee g s0 cfg returnType P s1 (.cont Q))
    (h2 : equivStmts code ee g s0 cfg returnType Q s2 out) :
    equivStmts code ee g s0 cfg returnType P (s1 ++ s2) out := by
  intro cur k C frame evm hRD hpre
  obtain ⟨cur1, k1, C1, frame1, evm1, hRD1, hblock1, hQ⟩ := h1 cur k C frame evm hRD hpre
  cases out with
  | cont Rpost =>
      obtain ⟨cur2, k2, C2, frame2, evm2, hRD2, hblock2, hR2⟩ := h2 cur1 k1 C1 frame1 evm1 hRD1 hQ
      exact ⟨cur2, k2, C2, frame2, evm2, hRD2, execBlock_append hblock1 hblock2, hR2⟩
  | ret rv =>
      obtain ⟨world2, o, frame2, evm2, hRDret, hblock2, hAcc, henc⟩ :=
        h2 cur1 k1 C1 frame1 evm1 hRD1 hQ
      exact ⟨world2, o, frame2, evm2, hRDret, execBlock_append hblock1 hblock2, hAcc, henc⟩
  | rev =>
      obtain ⟨hRDrev, hblock2⟩ := h2 cur1 k1 C1 frame1 evm1 hRD1 hQ
      exact ⟨hRDrev, execBlock_append hblock1 hblock2⟩

/-! ### A single-statement rule -/

/-- **single** — lift one statement that *falls through* (`.ok`) into a one-element block, given its
    per-statement simulation: from `Rpre` the compiled fragment `RDc`-advances to a cursor satisfying
    `Rpost` while the Solm `ExecStmt` steps `.ok`.  Concrete statement axioms (e.g. `require true`)
    are instances of this, discharged by tracing that statement's compiled opcodes. -/
theorem equivStmts.single {code ee g s0 cfg returnType} {Rpre Rpost : StateRel} {stmt : Stmt}
    (hstep : ∀ cur k C frame evm,
      RDc code ee g s0 cur k C →
      Rpre cur frame evm →
      ∃ cur' k' C' frame' evm',
        RDc code ee g s0 cur' k' C'
        ∧ ExecStmt cfg frame evm stmt (.ok frame' evm')
        ∧ Rpost cur' frame' evm') :
    equivStmts code ee g s0 cfg returnType Rpre [stmt] (.cont Rpost) := by
  intro cur k C frame evm hRD hpre
  obtain ⟨cur', k', C', frame', evm', hRD', hstmt, hpost⟩ := hstep cur k C frame evm hRD hpre
  exact ⟨cur', k', C', frame', evm', hRD', ExecBlock.consNormal hstmt ExecBlock.nil, hpost⟩

end Reasoning.Refinement
