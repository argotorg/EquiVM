import Reasoning.Dispatch

/-!
# Refinement — proof-side bridges: straight-line EVM runs ⟹ the equivalence statements

Only `runtimeEquivalenceFor` lives in `Solm.Equiv`.  The *relational* per-block and per-function
judgments — generic `equivStmts` (statement-list logic parameterized by an `ExecResult`
postcondition), `equivTransitionStmts` (the externally-dispatched body interpretation), and
`equivTransition` (one function's EVM body ≈ its Solm body) — mention the EVM `RD`/`RDret`/`RDrev`
discipline, so they live here, together with the bridges up the ladder:

* segment rules (`nil`/`consNormal`/`consReturn`/`consRevert`/`consBreak`/`consContinue`/
  `consequence`) — discharge a straight-line statement segment by symbolic execution on both sides
  (`RD` + `ExecStmt`), leaving the result meaning to the chosen postcondition.
* `equivStmts.toTransition` — externally-dispatched body logic ⟹ `equivTransition`.
* `equivTransition.toRuntime` — `equivTransition` + dispatch/decoding ⟹ `runtimeEquivalenceFor`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Refinement

/-- The persistent **world** carried by an EVM state: its created accounts and storage map.  This is
    the only part of the state the two executions are required to agree on (between external calls). -/
def worldOf (s : State) : Batteries.RBSet AccountAddress compare × AccountMap :=
  (s.createdAccounts, s.accountMap)

/-- A relation coupling an EVM reach-`Cursor` to the Solm execution state (frame + threaded EVM
    state).  It carries the *non-`pc`, non-world* part of the coupling — e.g. which stack/memory
    slots hold which locals — and is only constrained where it matters (call arguments, return
    value).  The structural rules are agnostic to what a `StateRel` actually says. -/
abbrev StateRel := Cursor → Frame → State → Prop

namespace StateRel

/-- Mechanically transform a relation across one concrete proof step.  The new relation pins the
    new cursor/frame/EVM state exactly and retains the old relation fact at the old state. -/
def stepFrom (R : StateRel) (cur0 : Cursor) (frame0 : Frame) (evm0 : State)
    (cur1 : Cursor) (frame1 : Frame) (evm1 : State) : StateRel :=
  fun cur frame evm => cur = cur1 ∧ frame = frame1 ∧ evm = evm1 ∧ R cur0 frame0 evm0

theorem stepFrom_here {R : StateRel} {cur0 cur1 : Cursor} {frame0 frame1 : Frame}
    {evm0 evm1 : State} (hrel : R cur0 frame0 evm0) :
    StateRel.stepFrom R cur0 frame0 evm0 cur1 frame1 evm1 cur1 frame1 evm1 := by
  exact ⟨rfl, rfl, rfl, hrel⟩

end StateRel

/-- A locals-only variant of `StateRel`.  This is useful for internal/callable bodies: their entry
    and exit frames may differ in the surrounding contract context, but most coupling facts only
    mention the local store. -/
abbrev StoreRel := Cursor → Store → State → Prop

namespace StoreRel

/-- Lift a locals-only relation to the frame-shaped relation expected by top-level statement rules. -/
def toStateRel (R : StoreRel) : StateRel :=
  fun cur frame evm => R cur frame.locals evm

end StoreRel

/-- A postcondition over a Solm block result.  The postcondition is where each client decides what
    `.ok`, `.returned`, `.break`, `.continue`, and `.reverted` mean on the EVM side. -/
abbrev StmtPost := ExecResult → Prop

/-- A concrete coupled proof state.

    This is the proof-mode counterpart of `RD`: it keeps the original EVM initial state `s0`, the
    current reachable EVM cursor with its `RDc` evidence, and the current Solm frame/threaded EVM
    state with the active coupling relation.  Unlike `equivStmts`, this does not quantify over all
    possible entries; it represents the single state currently being symbolically advanced. -/
structure CoupledState (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (R : StateRel) (pc : UInt256) where
  cur : Cursor
  k : ℕ
  C : ℕ
  frame : Frame
  evm : State
  hpc : cur.pc = pc
  hRD : RDc code ee g s0 cur k C
  hworld : cur.world = worldOf evm
  hrel : R cur frame evm

/-- Cursor packaging for positional `RD` facts. -/
def cursorOfRD (pc : UInt256) (stack : List UInt256) (mem : ByteArray)
    (aw : UInt256) (rdata : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := pc, stack := stack, mem := mem, aw := aw, rdata := rdata, world := world }

/-- Package a reached cursor and coupled Solm state as a concrete proof state. -/
def CoupledState.reached {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : StateRel} {pc : UInt256}
    (cur : Cursor) (k C : ℕ) (frame : Frame) (evm : State)
    (hpc : cur.pc = pc) (hRD : RDc code ee g s0 cur k C)
    (hworld : cur.world = worldOf evm) (hrel : R cur frame evm) :
    CoupledState code ee g s0 R pc :=
  { cur := cur, k := k, C := C, frame := frame, evm := evm,
    hpc := hpc, hRD := hRD, hworld := hworld, hrel := hrel }

/-- Package a positional `RD` fact directly as a concrete coupled proof state.  This hides the
    routine `RD → RDc` conversion at handoff points where bytecode helpers still expose positional
    reachability. -/
def CoupledState.ofRD {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : StateRel} {pc : UInt256}
    {stack : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (frame : Frame) (evm : State)
    (hRD : RD code ee g s0 pc stack mem aw rdata world k C)
    (hworld : world = worldOf evm)
    (hrel : R (cursorOfRD pc stack mem aw rdata world) frame evm) :
    CoupledState code ee g s0 R pc := by
  let cur := cursorOfRD pc stack mem aw rdata world
  have hRDc : RDc code ee g s0 cur k C := by
    change RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C
    simpa [cur, cursorOfRD] using hRD
  have hworld' : cur.world = worldOf evm := by
    simpa [cur, cursorOfRD] using hworld
  exact CoupledState.reached cur k C frame evm rfl hRDc hworld' hrel

/-- Advance a coupled state using a positional `RD` fact and a mechanical relation transform. -/
def CoupledState.stepRD {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : StateRel} {pc pc' : UInt256}
    {stack' : List UInt256} {mem' : ByteArray} {aw' : UInt256} {rdata' : ByteArray}
    {world' : Batteries.RBSet AccountAddress compare × AccountMap} {k' C' : ℕ}
    (st : CoupledState code ee g s0 R pc)
    (frame' : Frame) (evm' : State)
    (hRD : RD code ee g s0 pc' stack' mem' aw' rdata' world' k' C')
    (hworld : world' = worldOf evm') :
    CoupledState code ee g s0
      (StateRel.stepFrom R st.cur st.frame st.evm
        (cursorOfRD pc' stack' mem' aw' rdata' world') frame' evm') pc' :=
  CoupledState.ofRD frame' evm' hRD hworld (StateRel.stepFrom_here st.hrel)

/-- Compatibility wrapper for older proof scripts; prefer `CoupledState.reached` at the new state. -/
def CoupledState.next {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R R' : StateRel} {pc pc' : UInt256} (_st : CoupledState code ee g s0 R pc)
    (cur' : Cursor) (k' C' : ℕ) (frame' : Frame) (evm' : State)
    (hpc' : cur'.pc = pc') (hRD' : RDc code ee g s0 cur' k' C')
    (hworld' : cur'.world = worldOf evm') (hrel' : R' cur' frame' evm') :
    CoupledState code ee g s0 R' pc' :=
  CoupledState.reached cur' k' C' frame' evm' hpc' hRD' hworld' hrel'

/-- Convert the cursor-indexed reachability proof stored in a coupled state into the positional
    `RD` form expected by `evm_run`, after exposing the cursor fields used by the local relation. -/
theorem CoupledState.toRD {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : StateRel} {pc : UInt256} (st : CoupledState code ee g s0 R pc)
    {stack : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (hstack : st.cur.stack = stack) (hmem : st.cur.mem = mem)
    (haw : st.cur.aw = aw) (hrdata : st.cur.rdata = rdata) :
    RD code ee g s0 pc stack mem aw rdata st.cur.world st.k st.C := by
  have hRD := st.hRD
  unfold RDc at hRD
  rw [st.hpc, hstack, hmem, haw, hrdata] at hRD
  exact hRD

/-- Concrete statement-list equivalence from one coupled proof state. -/
def CoupledState.refines {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : StateRel} {pc : UInt256}
    (st : CoupledState code ee g s0 R pc) (cfg : Config)
    (stmts : List Stmt) (Post : StmtPost) : Prop :=
  ∃ result, ExecBlock cfg st.frame st.evm stmts result ∧ Post result

/-- **Generic statement-list equivalence** `{R} stmts ~ bytecode@pc {Post}`.

    From an entry cursor the run has reached (`cur.pc = pc`, `RDc`), with the world coupled
    (`cur.world = worldOf evm`) and the rest coupled by `R`, the Solm block *runs* to some
    `ExecResult`, and the caller-supplied `Post` explains the matching EVM-side fact for that result.

    This deliberately does not assign a fixed meaning to `.returned`, `.break`, or `.continue`.
    Externally-dispatched transition bodies, internal callables, and loop bodies instantiate `Post`
    differently. -/
def equivStmts (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (cfg : Config) (pc : UInt256) (R : StateRel) (stmts : List Stmt)
    (Post : StmtPost) : Prop :=
  ∀ cur k C frame evm,
    cur.pc = pc →
    RDc code ee g s0 cur k C →
    cur.world = worldOf evm →
    R cur frame evm →
    ∃ result, ExecBlock cfg frame evm stmts result ∧ Post result

/-- A quantified `equivStmts` theorem can be used at any concrete coupled proof state. -/
theorem equivStmts.toAt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {pc : UInt256} {R : StateRel} {stmts : List Stmt} {Post : StmtPost}
    (h : equivStmts code ee g s0 cfg pc R stmts Post)
    (st : CoupledState code ee g s0 R pc) :
    CoupledState.refines st cfg stmts Post :=
  h st.cur st.k st.C st.frame st.evm st.hpc st.hRD st.hworld st.hrel

/-- Build a quantified `equivStmts` theorem from a proof that works for every concrete coupled
    proof state. -/
theorem equivStmts.ofAt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {pc : UInt256} {R : StateRel} {stmts : List Stmt} {Post : StmtPost}
    (h : ∀ st : CoupledState code ee g s0 R pc, CoupledState.refines st cfg stmts Post) :
    equivStmts code ee g s0 cfg pc R stmts Post := by
  intro cur k C frame evm hpc hRD hw hR
  exact h (CoupledState.mk cur k C frame evm hpc hRD hw hR)

/-- A normal fall-through postcondition: the block must finish with `.ok` at a reached cursor. -/
def normalPost (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (Q : StateRel) : StmtPost
  | .ok frame' evm' =>
      ∃ cur' k' C', RDc code ee g s0 cur' k' C' ∧ cur'.world = worldOf evm'
        ∧ Q cur' frame' evm'
  | .returned _ _ _ | .reverted | .break _ _ | .continue _ _ =>
      False

/-- Concrete **nil** rule. -/
theorem CoupledState.refines.nil {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {pc : UInt256} {R : StateRel}
    (st : CoupledState code ee g s0 R pc) :
    CoupledState.refines st cfg [] (normalPost code ee g s0 R) := by
  exact ⟨.ok st.frame st.evm, ExecBlock.nil, st.cur, st.k, st.C, st.hRD, st.hworld, st.hrel⟩

/-- Concrete postcondition weakening. -/
theorem CoupledState.refines.consequencePost {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cfg : Config} {pc : UInt256} {R : StateRel} {stmts : List Stmt}
    {Post Post' : StmtPost} {st : CoupledState code ee g s0 R pc}
    (himp : ∀ result, Post result → Post' result)
    (h : CoupledState.refines st cfg stmts Post) :
    CoupledState.refines st cfg stmts Post' := by
  obtain ⟨result, hblock, hpost⟩ := h
  exact ⟨result, hblock, himp result hpost⟩

/-- Concrete **consNormal** rule.  The head statement advances the concrete coupled state to a new
    concrete coupled state for the tail. -/
theorem CoupledState.refines.consNormal {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cfg : Config} {pc pc' : UInt256} {R R' : StateRel}
    {Post : StmtPost} {s : Stmt} {rest : List Stmt}
    (st : CoupledState code ee g s0 R pc)
    (hhead :
      ∃ frame' evm' cur' k' C',
        cur'.pc = pc' ∧
        ExecStmt cfg st.frame st.evm s (.ok frame' evm') ∧
        RDc code ee g s0 cur' k' C' ∧
        cur'.world = worldOf evm' ∧
        R' cur' frame' evm')
    (hrest : ∀ cur' k' C' frame' evm',
      ∀ (hpc' : cur'.pc = pc') (hRD' : RDc code ee g s0 cur' k' C')
        (hworld' : cur'.world = worldOf evm') (hrel' : R' cur' frame' evm'),
        CoupledState.refines (CoupledState.mk cur' k' C' frame' evm' hpc' hRD' hworld' hrel')
          cfg rest Post) :
    CoupledState.refines st cfg (s :: rest) Post := by
  obtain ⟨frame', evm', cur', k', C', hpc', hstmt, hRD', hw', hR'⟩ := hhead
  obtain ⟨result, hblock, hpost⟩ := hrest cur' k' C' frame' evm' hpc' hRD' hw' hR'
  exact ⟨result, ExecBlock.consNormal hstmt hblock, hpost⟩

/-- Concrete **consNormal** rule when the advanced coupled state has already been packaged. -/
theorem CoupledState.refines.consNormalAt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cfg : Config} {pc pc' : UInt256} {R R' : StateRel}
    {Post : StmtPost} {s : Stmt} {rest : List Stmt}
    (st : CoupledState code ee g s0 R pc)
    (st' : CoupledState code ee g s0 R' pc')
    (hstmt : ExecStmt cfg st.frame st.evm s (.ok st'.frame st'.evm))
    (hrest : CoupledState.refines st' cfg rest Post) :
    CoupledState.refines st cfg (s :: rest) Post := by
  obtain ⟨result, hblock, hpost⟩ := hrest
  exact ⟨result, ExecBlock.consNormal hstmt hblock, hpost⟩

/-- Progress a source-only `require` known to evaluate to true.  The EVM cursor/relation are
    unchanged; this is useful when the corresponding bytecode check has already happened before the
    current coupled point. -/
theorem CoupledState.refines.requireTrue {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cfg : Config} {pc : UInt256} {R : StateRel}
    {Post : StmtPost} {cond : Expr} {rest : List Stmt}
    (st : CoupledState code ee g s0 R pc)
    (heval : evalExpr? cfg st.frame st.evm cond = .ok (.bool true))
    (hrest : CoupledState.refines st cfg rest Post) :
    CoupledState.refines st cfg (.require cond :: rest) Post :=
  CoupledState.refines.consNormalAt st st (ExecStmt.requireTrue heval) hrest

/-- Progress a `letDecl` while advancing to a caller-supplied coupled state.  The bytecode-side
    progress is intentionally abstracted into `st'`: callers prove whatever cursor/RD/relation facts
    their compiled pattern establishes, while this rule handles the generic source-frame update. -/
theorem CoupledState.refines.letDeclAt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cfg : Config} {pc pc' : UInt256} {R R' : StateRel}
    {Post : StmtPost} {name : Ident} {ty : Option ABIType} {expr : Expr} {rest : List Stmt}
    (st : CoupledState code ee g s0 R pc)
    (st' : CoupledState code ee g s0 R' pc')
    {value : Value}
    (heval : evalExpr? cfg st.frame st.evm expr = .ok value)
    (hframe : st'.frame = { st.frame with locals := st.frame.locals.insert name value })
    (hevm : st'.evm = st.evm)
    (hrest : CoupledState.refines st' cfg rest Post) :
    CoupledState.refines st cfg (.letDecl name ty expr :: rest) Post := by
  refine CoupledState.refines.consNormalAt st st' ?_ hrest
  rw [hframe, hevm]
  exact ExecStmt.letDecl heval

/-- Progress an `assign` while advancing to a caller-supplied coupled state.  As with
    `letDeclAt`, the EVM reachability and relation update live in `st'`; this rule packages the
    generic Solm assignment semantics. -/
theorem CoupledState.refines.assignAt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cfg : Config} {pc pc' : UInt256} {R R' : StateRel}
    {Post : StmtPost} {origin : VarOrigin} {slot : StorageRef} {expr : Expr} {rest : List Stmt}
    (st : CoupledState code ee g s0 R pc)
    (st' : CoupledState code ee g s0 R' pc')
    {value : Value}
    (heval : evalExpr? cfg st.frame st.evm expr = .ok value)
    (hassign : assignStorageRef? cfg st.frame st.evm origin slot value = .ok (st'.frame, st'.evm))
    (hrest : CoupledState.refines st' cfg rest Post) :
    CoupledState.refines st cfg (.assign origin slot expr :: rest) Post := by
  refine CoupledState.refines.consNormalAt st st' ?_ hrest
  exact ExecStmt.assign heval hassign

/-- Concrete **consReturn** rule.  The caller-supplied postcondition decides what a Solm `return`
    means for this proof context. -/
theorem CoupledState.refines.consReturn {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cfg : Config} {pc : UInt256} {R : StateRel}
    {Post : StmtPost} {s : Stmt} {rest : List Stmt}
    (st : CoupledState code ee g s0 R pc)
    (hhead :
      ∃ frame' evm' rv,
        ExecStmt cfg st.frame st.evm s (.returned frame' evm' rv) ∧
        Post (.returned frame' evm' rv)) :
    CoupledState.refines st cfg (s :: rest) Post := by
  obtain ⟨frame', evm', rv, hstmt, hpost⟩ := hhead
  exact ⟨.returned frame' evm' rv, ExecBlock.consReturn hstmt, hpost⟩

/-- Concrete **consRevert** rule.  The tail is never reached. -/
theorem CoupledState.refines.consRevert {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cfg : Config} {pc : UInt256} {R : StateRel}
    {Post : StmtPost} {s : Stmt} {rest : List Stmt}
    (st : CoupledState code ee g s0 R pc)
    (hhead : ExecStmt cfg st.frame st.evm s .reverted ∧ Post .reverted) :
    CoupledState.refines st cfg (s :: rest) Post := by
  obtain ⟨hstmt, hpost⟩ := hhead
  exact ⟨.reverted, ExecBlock.consRevert hstmt, hpost⟩

/-- Concrete **consBreak** rule.  The tail is never reached. -/
theorem CoupledState.refines.consBreak {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cfg : Config} {pc : UInt256} {R : StateRel}
    {Post : StmtPost} {s : Stmt} {rest : List Stmt}
    (st : CoupledState code ee g s0 R pc)
    (hhead :
      ∃ frame' evm',
        ExecStmt cfg st.frame st.evm s (.break frame' evm') ∧
        Post (.break frame' evm')) :
    CoupledState.refines st cfg (s :: rest) Post := by
  obtain ⟨frame', evm', hstmt, hpost⟩ := hhead
  exact ⟨.break frame' evm', ExecBlock.consBreak hstmt, hpost⟩

/-- Concrete **consContinue** rule.  The tail is never reached. -/
theorem CoupledState.refines.consContinue {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cfg : Config} {pc : UInt256} {R : StateRel}
    {Post : StmtPost} {s : Stmt} {rest : List Stmt}
    (st : CoupledState code ee g s0 R pc)
    (hhead :
      ∃ frame' evm',
        ExecStmt cfg st.frame st.evm s (.continue frame' evm') ∧
        Post (.continue frame' evm')) :
    CoupledState.refines st cfg (s :: rest) Post := by
  obtain ⟨frame', evm', hstmt, hpost⟩ := hhead
  exact ⟨.continue frame' evm', ExecBlock.consContinue hstmt, hpost⟩

/-- Postcondition for one loop-body iteration.  Normal fall-through and `continue` return to the
    loop head with the decreased invariant; `break` exits the loop; `return`/`revert` are terminal
    for the surrounding block. -/
def loopBodyPost (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (loopPc exitPc : UInt256) (Rloop : ℕ → StateRel) (Rexit : StateRel)
    (v : ℕ) (Post : StmtPost) : StmtPost
  | .ok frame' evm' =>
      ∃ cur' k' C', cur'.pc = loopPc ∧ RDc code ee g s0 cur' k' C'
        ∧ cur'.world = worldOf evm' ∧ Rloop v cur' frame' evm'
  | .continue frame' evm' =>
      ∃ cur' k' C', cur'.pc = loopPc ∧ RDc code ee g s0 cur' k' C'
        ∧ cur'.world = worldOf evm' ∧ Rloop v cur' frame' evm'
  | .break frame' evm' =>
      ∃ cur' k' C', cur'.pc = exitPc ∧ RDc code ee g s0 cur' k' C'
        ∧ cur'.world = worldOf evm' ∧ Rexit cur' frame' evm'
  | .returned frame' evm' rv =>
      Post (.returned frame' evm' rv)
  | .reverted =>
      Post .reverted

/-- Prefix a recursive `while :: rest` block with an iteration whose body fell through normally. -/
theorem execBlock_prependWhileTrue {cfg : Config} {cond : Expr} {body rest : List Stmt}
    {frame evm frame' evm'} {result : ExecResult}
    (hcond : evalExpr? cfg frame evm cond = .ok (.bool true))
    (hbody : ExecBlock cfg frame evm body (.ok frame' evm'))
    (hrec : ExecBlock cfg frame' evm' (.while cond body :: rest) result) :
    ExecBlock cfg frame evm (.while cond body :: rest) result := by
  cases hrec with
  | consNormal hwhile hrest =>
      exact ExecBlock.consNormal (ExecStmt.whileTrue hcond hbody hwhile) hrest
  | consReturn hwhile =>
      exact ExecBlock.consReturn (ExecStmt.whileTrue hcond hbody hwhile)
  | consRevert hwhile =>
      exact ExecBlock.consRevert (ExecStmt.whileTrue hcond hbody hwhile)
  | consBreak hwhile =>
      exact ExecBlock.consBreak (ExecStmt.whileTrue hcond hbody hwhile)
  | consContinue hwhile =>
      exact ExecBlock.consContinue (ExecStmt.whileTrue hcond hbody hwhile)

/-- Prefix a recursive `while :: rest` block with an iteration whose body hit `continue`. -/
theorem execBlock_prependWhileContinue {cfg : Config} {cond : Expr} {body rest : List Stmt}
    {frame evm frame' evm'} {result : ExecResult}
    (hcond : evalExpr? cfg frame evm cond = .ok (.bool true))
    (hbody : ExecBlock cfg frame evm body (.continue frame' evm'))
    (hrec : ExecBlock cfg frame' evm' (.while cond body :: rest) result) :
    ExecBlock cfg frame evm (.while cond body :: rest) result := by
  cases hrec with
  | consNormal hwhile hrest =>
      exact ExecBlock.consNormal (ExecStmt.whileContinue hcond hbody hwhile) hrest
  | consReturn hwhile =>
      exact ExecBlock.consReturn (ExecStmt.whileContinue hcond hbody hwhile)
  | consRevert hwhile =>
      exact ExecBlock.consRevert (ExecStmt.whileContinue hcond hbody hwhile)
  | consBreak hwhile =>
      exact ExecBlock.consBreak (ExecStmt.whileContinue hcond hbody hwhile)
  | consContinue hwhile =>
      exact ExecBlock.consContinue (ExecStmt.whileContinue hcond hbody hwhile)

/-- Concrete **while-loop** rule with a natural variant.

    `Rloop v` is the coupled invariant at the loop head with `v` iterations remaining.  At `0`, the
    condition is false and the EVM reaches the loop exit.  At `v+1`, the condition is true and the
    EVM reaches the body entry; the body proof must either return to `Rloop v`, exit by `break`, or
    satisfy the surrounding terminal postcondition. -/
theorem CoupledState.refines.whileLoop {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cfg : Config} {loopPc bodyPc exitPc : UInt256}
    {Rbody Rexit : StateRel} {Rloop : ℕ → StateRel} {Post : StmtPost}
    {cond : Expr} {body rest : List Stmt}
    (hfalse : ∀ st : CoupledState code ee g s0 (Rloop 0) loopPc,
      ∃ curExit kExit CExit,
        evalExpr? cfg st.frame st.evm cond = .ok (.bool false) ∧
        curExit.pc = exitPc ∧
        RDc code ee g s0 curExit kExit CExit ∧
        curExit.world = worldOf st.evm ∧
        Rexit curExit st.frame st.evm)
    (htrue : ∀ v (st : CoupledState code ee g s0 (Rloop (v + 1)) loopPc),
      ∃ curBody kBody CBody,
        evalExpr? cfg st.frame st.evm cond = .ok (.bool true) ∧
        curBody.pc = bodyPc ∧
        RDc code ee g s0 curBody kBody CBody ∧
        curBody.world = worldOf st.evm ∧
        Rbody curBody st.frame st.evm)
    (hbody : ∀ v (stBody : CoupledState code ee g s0 Rbody bodyPc),
      CoupledState.refines stBody cfg body
        (loopBodyPost code ee g s0 loopPc exitPc Rloop Rexit v Post))
    (hrest : ∀ stExit : CoupledState code ee g s0 Rexit exitPc,
      CoupledState.refines stExit cfg rest Post) :
    ∀ v (st : CoupledState code ee g s0 (Rloop v) loopPc),
      CoupledState.refines st cfg (.while cond body :: rest) Post := by
  intro v
  induction v with
  | zero =>
      intro st
      obtain ⟨curExit, kExit, CExit, hcond, hpcExit, hRDExit, hwExit, hRExit⟩ := hfalse st
      obtain ⟨result, hrestBlock, hpost⟩ :=
        hrest (CoupledState.mk curExit kExit CExit st.frame st.evm hpcExit hRDExit hwExit hRExit)
      exact ⟨result, ExecBlock.consNormal (ExecStmt.whileFalse hcond) hrestBlock, hpost⟩
  | succ v ih =>
      intro st
      obtain ⟨curBody, kBody, CBody, hcond, hpcBody, hRDBody, hwBody, hRBody⟩ := htrue v st
      obtain ⟨bodyResult, hbodyBlock, hbodyPost⟩ :=
        hbody v (CoupledState.mk curBody kBody CBody st.frame st.evm hpcBody hRDBody hwBody hRBody)
      cases bodyResult with
      | ok frame' evm' =>
          obtain ⟨curLoop, kLoop, CLoop, hpcLoop, hRDLoop, hwLoop, hRLoop⟩ := hbodyPost
          obtain ⟨result, hrecBlock, hpost⟩ :=
            ih (CoupledState.mk curLoop kLoop CLoop frame' evm' hpcLoop hRDLoop hwLoop hRLoop)
          exact ⟨result,
            execBlock_prependWhileTrue hcond hbodyBlock hrecBlock,
            hpost⟩
      | returned frame' evm' rv =>
          exact ⟨.returned frame' evm' rv, ExecBlock.consReturn (ExecStmt.whileReturn hcond hbodyBlock),
            hbodyPost⟩
      | reverted =>
          exact ⟨.reverted, ExecBlock.consRevert (ExecStmt.whileRevert hcond hbodyBlock), hbodyPost⟩
      | «break» frame' evm' =>
          obtain ⟨curExit, kExit, CExit, hpcExit, hRDExit, hwExit, hRExit⟩ := hbodyPost
          obtain ⟨result, hrestBlock, hpost⟩ :=
            hrest (CoupledState.mk curExit kExit CExit frame' evm' hpcExit hRDExit hwExit hRExit)
          exact ⟨result, ExecBlock.consNormal (ExecStmt.whileBreak hcond hbodyBlock) hrestBlock, hpost⟩
      | «continue» frame' evm' =>
          obtain ⟨curLoop, kLoop, CLoop, hpcLoop, hRDLoop, hwLoop, hRLoop⟩ := hbodyPost
          obtain ⟨result, hrecBlock, hpost⟩ :=
            ih (CoupledState.mk curLoop kLoop CLoop frame' evm' hpcLoop hRDLoop hwLoop hRLoop)
          exact ⟨result,
            execBlock_prependWhileContinue hcond hbodyBlock hrecBlock,
            hpost⟩

/-- Concrete **while-loop** rule with a natural variant and variant-indexed body-entry relation.

    This is the scoped-body version of `CoupledState.refines.whileLoop`: when the guard is true at
    variant `v + 1`, the body-entry relation is `Rbody v`, so the body proof retains the exact
    target variant it must re-establish. -/
theorem CoupledState.refines.whileLoopIndexedBody {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {cfg : Config} {loopPc bodyPc exitPc : UInt256}
    {Rexit : StateRel} {Rloop Rbody : ℕ → StateRel} {Post : StmtPost}
    {cond : Expr} {body rest : List Stmt}
    (hfalse : ∀ st : CoupledState code ee g s0 (Rloop 0) loopPc,
      ∃ curExit kExit CExit,
        evalExpr? cfg st.frame st.evm cond = .ok (.bool false) ∧
        curExit.pc = exitPc ∧
        RDc code ee g s0 curExit kExit CExit ∧
        curExit.world = worldOf st.evm ∧
        Rexit curExit st.frame st.evm)
    (htrue : ∀ v (st : CoupledState code ee g s0 (Rloop (v + 1)) loopPc),
      ∃ curBody kBody CBody,
        evalExpr? cfg st.frame st.evm cond = .ok (.bool true) ∧
        curBody.pc = bodyPc ∧
        RDc code ee g s0 curBody kBody CBody ∧
        curBody.world = worldOf st.evm ∧
        Rbody v curBody st.frame st.evm)
    (hbody : ∀ v (stBody : CoupledState code ee g s0 (Rbody v) bodyPc),
      CoupledState.refines stBody cfg body
        (loopBodyPost code ee g s0 loopPc exitPc Rloop Rexit v Post))
    (hrest : ∀ stExit : CoupledState code ee g s0 Rexit exitPc,
      CoupledState.refines stExit cfg rest Post) :
    ∀ v (st : CoupledState code ee g s0 (Rloop v) loopPc),
      CoupledState.refines st cfg (.while cond body :: rest) Post := by
  intro v
  induction v with
  | zero =>
      intro st
      obtain ⟨curExit, kExit, CExit, hcond, hpcExit, hRDExit, hwExit, hRExit⟩ := hfalse st
      obtain ⟨result, hrestBlock, hpost⟩ :=
        hrest (CoupledState.mk curExit kExit CExit st.frame st.evm hpcExit hRDExit hwExit hRExit)
      exact ⟨result, ExecBlock.consNormal (ExecStmt.whileFalse hcond) hrestBlock, hpost⟩
  | succ v ih =>
      intro st
      obtain ⟨curBody, kBody, CBody, hcond, hpcBody, hRDBody, hwBody, hRBody⟩ := htrue v st
      obtain ⟨bodyResult, hbodyBlock, hbodyPost⟩ :=
        hbody v (CoupledState.mk curBody kBody CBody st.frame st.evm hpcBody hRDBody hwBody hRBody)
      cases bodyResult with
      | ok frame' evm' =>
          obtain ⟨curLoop, kLoop, CLoop, hpcLoop, hRDLoop, hwLoop, hRLoop⟩ := hbodyPost
          obtain ⟨result, hrecBlock, hpost⟩ :=
            ih (CoupledState.mk curLoop kLoop CLoop frame' evm' hpcLoop hRDLoop hwLoop hRLoop)
          exact ⟨result,
            execBlock_prependWhileTrue hcond hbodyBlock hrecBlock,
            hpost⟩
      | returned frame' evm' rv =>
          exact ⟨.returned frame' evm' rv, ExecBlock.consReturn (ExecStmt.whileReturn hcond hbodyBlock),
            hbodyPost⟩
      | reverted =>
          exact ⟨.reverted, ExecBlock.consRevert (ExecStmt.whileRevert hcond hbodyBlock), hbodyPost⟩
      | «break» frame' evm' =>
          obtain ⟨curExit, kExit, CExit, hpcExit, hRDExit, hwExit, hRExit⟩ := hbodyPost
          obtain ⟨result, hrestBlock, hpost⟩ :=
            hrest (CoupledState.mk curExit kExit CExit frame' evm' hpcExit hRDExit hwExit hRExit)
          exact ⟨result, ExecBlock.consNormal (ExecStmt.whileBreak hcond hbodyBlock) hrestBlock, hpost⟩
      | «continue» frame' evm' =>
          obtain ⟨curLoop, kLoop, CLoop, hpcLoop, hRDLoop, hwLoop, hRLoop⟩ := hbodyPost
          obtain ⟨result, hrecBlock, hpost⟩ :=
            ih (CoupledState.mk curLoop kLoop CLoop frame' evm' hpcLoop hRDLoop hwLoop hRLoop)
          exact ⟨result,
            execBlock_prependWhileContinue hcond hbodyBlock hrecBlock,
            hpost⟩

/-- Postcondition used by externally-dispatched transition bodies.  Here a Solm `return` really is
    an EVM `RETURN`; fall-through is left as a cursor for the ABI-encoding epilogue. -/
def transitionPost (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (returnType : Option ABIType) (Q : StateRel) : StmtPost
  | .ok frame' evm' =>
      ∃ cur' k' C', RDc code ee g s0 cur' k' C' ∧ cur'.world = worldOf evm'
        ∧ Q cur' frame' evm'
  | .returned _ evm' rv =>
      ∃ o, RDret code g s0 (worldOf evm') o ∧ returnEquiv o rv returnType
  | .reverted =>
      RDrev code g s0
  | .break _ _ | .continue _ _ =>
      False

/-- Close an external-transition proof when the next statement is a Solm `return` and the bytecode
    side has reached an EVM `RETURN` with ABI-equivalent bytes. -/
theorem CoupledState.refines.returnTransition {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {cfg : Config} {pc : UInt256} {R Q : StateRel}
    {returnType : Option ABIType} {expr : Expr} {rest : List Stmt}
    (st : CoupledState code ee g s0 R pc)
    {frame' : Frame} {evm' : State} {rv : Option Value} {o : ByteArray}
    (hstmt : ExecStmt cfg st.frame st.evm (.return expr) (.returned frame' evm' rv))
    (hret : RDret code g s0 (worldOf evm') o)
    (hequiv : returnEquiv o rv returnType) :
    CoupledState.refines st cfg (.return expr :: rest) (transitionPost code ee g s0 returnType Q) := by
  refine CoupledState.refines.consReturn st ?_
  exact ⟨frame', evm', rv, hstmt, o, hret, hequiv⟩

/-- Compatibility name for the external-transition interpretation of `equivStmts`. -/
def equivTransitionStmts (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (cfg : Config) (returnType : Option ABIType)
    (pc : UInt256) (R : StateRel) (stmts : List Stmt) (Q : StateRel) : Prop :=
  equivStmts code ee g s0 cfg pc R stmts (transitionPost code ee g s0 returnType Q)

/-! ### Structural rules — symbolic execution on both sides, statement by statement -/

/-- **nil** — the empty block keeps the cursor and the relation unchanged. -/
theorem equivStmts.nil {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {pc : UInt256} (R : StateRel) :
    equivStmts code ee g s0 cfg pc R [] (normalPost code ee g s0 R) := by
  intro cur k C frame evm _hpc hRD hw hR
  exact ⟨.ok frame evm, ExecBlock.nil, cur, k, C, hRD, hw, hR⟩

/-- **nil**, fully generic form. -/
theorem equivStmts.nilPost {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {pc : UInt256} {R : StateRel} {Post : StmtPost}
    (hpost : ∀ cur k C frame evm, cur.pc = pc → RDc code ee g s0 cur k C →
      cur.world = worldOf evm → R cur frame evm → Post (.ok frame evm)) :
    equivStmts code ee g s0 cfg pc R [] Post := by
  intro cur k C frame evm hpc hRD hw hR
  exact ⟨.ok frame evm, ExecBlock.nil, hpost cur k C frame evm hpc hRD hw hR⟩

/-- **consNormal** — peel a fall-through head statement.  `hhead` runs the head in Solm
    (`ExecStmt … .ok`) and walks its bytecode (`RDc … cur'`, exit pc `pc'`), re-establishing the
    coupling `R'`; `hrest` is the advanced judgment for the tail.  This is "run some bytecode with
    `RD`, run a Solm statement, move to an advanced `equivStmts`." -/
theorem equivStmts.consNormal {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {pc pc' : UInt256} {R R' : StateRel} {Post : StmtPost}
    {s : Stmt} {rest : List Stmt}
    (hhead : ∀ cur k C frame evm, cur.pc = pc → RDc code ee g s0 cur k C → cur.world = worldOf evm →
        R cur frame evm →
        ∃ frame' evm' cur' k' C',
          cur'.pc = pc' ∧
          ExecStmt cfg frame evm s (.ok frame' evm') ∧
          RDc code ee g s0 cur' k' C' ∧
          cur'.world = worldOf evm' ∧
          R' cur' frame' evm')
    (hrest : equivStmts code ee g s0 cfg pc' R' rest Post) :
    equivStmts code ee g s0 cfg pc R (s :: rest) Post := by
  intro cur k C frame evm hpc hRD hw hR
  obtain ⟨frame', evm', cur', k', C', hpc', hstmt, hRD', hw', hR'⟩ := hhead cur k C frame evm hpc hRD hw hR
  obtain ⟨result, hblock, hmatch⟩ := hrest cur' k' C' frame' evm' hpc' hRD' hw' hR'
  exact ⟨result, ExecBlock.consNormal hstmt hblock, hmatch⟩

/-- **consReturn** — the head statement `return`s.  The caller-supplied postcondition decides
    whether that is an EVM `RETURN` (external transition) or a reached continuation (internal
    callable).  The tail is never reached. -/
theorem equivStmts.consReturn {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {pc : UInt256} {R : StateRel} {Post : StmtPost}
    {s : Stmt} {rest : List Stmt}
    (hhead : ∀ cur k C frame evm, cur.pc = pc → RDc code ee g s0 cur k C → cur.world = worldOf evm →
        R cur frame evm →
        ∃ frame' evm' rv,
          ExecStmt cfg frame evm s (.returned frame' evm' rv) ∧
          Post (.returned frame' evm' rv)) :
    equivStmts code ee g s0 cfg pc R (s :: rest) Post := by
  intro cur k C frame evm hpc hRD hw hR
  obtain ⟨frame', evm', rv, hstmt, hpost⟩ := hhead cur k C frame evm hpc hRD hw hR
  exact ⟨.returned frame' evm' rv, ExecBlock.consReturn hstmt, hpost⟩

/-- **consRevert** — the head statement `revert`s.  The tail is never reached. -/
theorem equivStmts.consRevert {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {pc : UInt256} {R : StateRel} {Post : StmtPost}
    {s : Stmt} {rest : List Stmt}
    (hhead : ∀ cur k C frame evm, cur.pc = pc → RDc code ee g s0 cur k C → cur.world = worldOf evm →
        R cur frame evm →
        ExecStmt cfg frame evm s .reverted ∧ Post .reverted) :
    equivStmts code ee g s0 cfg pc R (s :: rest) Post := by
  intro cur k C frame evm hpc hRD hw hR
  obtain ⟨hstmt, hpost⟩ := hhead cur k C frame evm hpc hRD hw hR
  exact ⟨.reverted, ExecBlock.consRevert hstmt, hpost⟩

/-- **consBreak** — the head statement `break`s.  The tail is never reached. -/
theorem equivStmts.consBreak {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {pc : UInt256} {R : StateRel} {Post : StmtPost}
    {s : Stmt} {rest : List Stmt}
    (hhead : ∀ cur k C frame evm, cur.pc = pc → RDc code ee g s0 cur k C → cur.world = worldOf evm →
        R cur frame evm →
        ∃ frame' evm', ExecStmt cfg frame evm s (.break frame' evm') ∧
          Post (.break frame' evm')) :
    equivStmts code ee g s0 cfg pc R (s :: rest) Post := by
  intro cur k C frame evm hpc hRD hw hR
  obtain ⟨frame', evm', hstmt, hpost⟩ := hhead cur k C frame evm hpc hRD hw hR
  exact ⟨.break frame' evm', ExecBlock.consBreak hstmt, hpost⟩

/-- **consContinue** — the head statement `continue`s.  The tail is never reached. -/
theorem equivStmts.consContinue {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {pc : UInt256} {R : StateRel} {Post : StmtPost}
    {s : Stmt} {rest : List Stmt}
    (hhead : ∀ cur k C frame evm, cur.pc = pc → RDc code ee g s0 cur k C → cur.world = worldOf evm →
        R cur frame evm →
        ∃ frame' evm', ExecStmt cfg frame evm s (.continue frame' evm') ∧
          Post (.continue frame' evm')) :
    equivStmts code ee g s0 cfg pc R (s :: rest) Post := by
  intro cur k C frame evm hpc hRD hw hR
  obtain ⟨frame', evm', hstmt, hpost⟩ := hhead cur k C frame evm hpc hRD hw hR
  exact ⟨.continue frame' evm', ExecBlock.consContinue hstmt, hpost⟩

/-- **external call (success / continue)** — peel a *successful* external call.  The bytecode's
    `CALL` (`RD.call`) and Solm's `externalCall` (`typedCallViaEVM`) invoke the **same** `Θ`, so
    the opaque result `(z, evm', out)` coincides on both sides by construction; `hcall` packages that
    bridged fact (obtained from `RD.call`) together with the post-`CALL` cursor.  On `z = true` with a
    decoding return, `retVar` binds the decoded `value` and execution continues at `pc'`.

    A call that **reverts** — `z = false`, or a return that does not decode — is *not* a new rule:
    it is `consRevert` with `ExecStmt.externalCallFailure` / `externalCallReturnDecodeRevert`.  Which
    branch fires is dictated by the (opaque, but deterministic) `Θ` result, exactly as the contract's
    post-`CALL` bytecode (`ISZERO …` / the return-size check) branches on it. -/
theorem CoupledState.refines.externalCall {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cfg : Config} {pc pc' : UInt256} {R R' : StateRel} {Post : StmtPost}
    {receiver eth : Expr} {name : Ident} {args : List Expr} {retVar : Ident}
    {rest : List Stmt} {perm : Bool}
    (st : CoupledState code ee g s0 R pc)
    (hcall :
      ∃ (target : EVM.Address) (sendVal : ℤ) (argVals : List Value) (evm' : State)
        (out : ByteArray) (value : Value) (cur' : Cursor) (k' C' : ℕ),
        evalExpr? cfg st.frame st.evm receiver = .ok (.address target) ∧
        evalExpr? cfg st.frame st.evm eth = .ok (.int sendVal) ∧
        evalExprs? cfg st.frame st.evm args = .ok argVals ∧
        typedCallViaEVM cfg st.evm (EVM.address target) name sendVal argVals
          (true, evm', out) perm ∧
        cfg.externalABI.decode? name out = some value ∧
        cur'.pc = pc' ∧
        RDc code ee g s0 cur' k' C' ∧
        cur'.world = worldOf evm' ∧
        R' cur' { st.frame with locals := st.frame.locals.insert retVar value } evm')
    (hrest : ∀ cur' k' C' frame' evm',
      ∀ (hpc' : cur'.pc = pc') (hRD' : RDc code ee g s0 cur' k' C')
        (hworld' : cur'.world = worldOf evm') (hrel' : R' cur' frame' evm'),
        CoupledState.refines (CoupledState.mk cur' k' C' frame' evm' hpc' hRD' hworld' hrel')
          cfg rest Post) :
    CoupledState.refines st cfg (.externalCall receiver name eth args retVar perm :: rest) Post := by
  obtain ⟨target, sendVal, argVals, evm', out, value, cur', k', C',
    hrec, heth, hargs, hcallEVM, hdec, hpc', hRD', hw', hR'⟩ := hcall
  obtain ⟨result, hblock, hpost⟩ :=
    hrest cur' k' C' { st.frame with locals := st.frame.locals.insert retVar value } evm'
      hpc' hRD' hw' hR'
  exact ⟨result,
    ExecBlock.consNormal (ExecStmt.externalCallSuccess hrec heth hargs hcallEVM hdec) hblock,
    hpost⟩

/-- Concrete external-call rule for the `z = false` branch.  The statement reverts immediately, so
    the tail is unreachable and the caller-supplied postcondition must already accept `.reverted`. -/
theorem CoupledState.refines.externalCallFailure {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {cfg : Config} {pc : UInt256} {R : StateRel}
    {Post : StmtPost} {receiver eth : Expr} {name : Ident} {args : List Expr}
    {retVar : Ident} {rest : List Stmt} {perm : Bool}
    (st : CoupledState code ee g s0 R pc)
    (hcall :
      ∃ (target : EVM.Address) (sendVal : ℤ) (argVals : List Value) (evm' : State)
        (out : ByteArray),
        evalExpr? cfg st.frame st.evm receiver = .ok (.address target) ∧
        evalExpr? cfg st.frame st.evm eth = .ok (.int sendVal) ∧
        evalExprs? cfg st.frame st.evm args = .ok argVals ∧
        typedCallViaEVM cfg st.evm (EVM.address target) name sendVal argVals
          (false, evm', out) perm)
    (hpost : Post .reverted) :
    CoupledState.refines st cfg (.externalCall receiver name eth args retVar perm :: rest) Post := by
  obtain ⟨target, sendVal, argVals, evm', out, hrec, heth, hargs, hcallEVM⟩ := hcall
  exact ⟨.reverted,
    ExecBlock.consRevert (ExecStmt.externalCallFailure hrec heth hargs hcallEVM),
    hpost⟩

/-- Concrete external-call rule for the successful-call / ABI-decode-failure branch.  The statement
    reverts immediately, so the tail is unreachable. -/
theorem CoupledState.refines.externalCallDecodeRevert {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {cfg : Config} {pc : UInt256} {R : StateRel}
    {Post : StmtPost} {receiver eth : Expr} {name : Ident} {args : List Expr}
    {retVar : Ident} {rest : List Stmt} {perm : Bool}
    (st : CoupledState code ee g s0 R pc)
    (hcall :
      ∃ (target : EVM.Address) (sendVal : ℤ) (argVals : List Value) (evm' : State)
        (out : ByteArray),
        evalExpr? cfg st.frame st.evm receiver = .ok (.address target) ∧
        evalExpr? cfg st.frame st.evm eth = .ok (.int sendVal) ∧
        evalExprs? cfg st.frame st.evm args = .ok argVals ∧
        typedCallViaEVM cfg st.evm (EVM.address target) name sendVal argVals
          (true, evm', out) perm ∧
        cfg.externalABI.decode? name out = none)
    (hpost : Post .reverted) :
    CoupledState.refines st cfg (.externalCall receiver name eth args retVar perm :: rest) Post := by
  obtain ⟨target, sendVal, argVals, evm', out, hrec, heth, hargs, hcallEVM, hdec⟩ := hcall
  exact ⟨.reverted,
    ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert hrec heth hargs hcallEVM hdec),
    hpost⟩

theorem equivStmts.externalCall {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {pc pc' : UInt256} {R R' : StateRel} {Post : StmtPost}
    {receiver eth : Expr} {name : Ident} {args : List Expr} {retVar : Ident} {rest : List Stmt}
    {perm : Bool}
    (hcall : ∀ cur k C frame evm, cur.pc = pc → RDc code ee g s0 cur k C → cur.world = worldOf evm →
        R cur frame evm →
        ∃ (target : EVM.Address) (sendVal : ℤ) (argVals : List Value) (evm' : State)
          (out : ByteArray) (value : Value) (cur' : Cursor) (k' C' : ℕ),
          evalExpr? cfg frame evm receiver = .ok (.address target) ∧
          evalExpr? cfg frame evm eth = .ok (.int sendVal) ∧
          evalExprs? cfg frame evm args = .ok argVals ∧
          typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
            (true, evm', out) perm ∧
          cfg.externalABI.decode? name out = some value ∧
          cur'.pc = pc' ∧
          RDc code ee g s0 cur' k' C' ∧
          cur'.world = worldOf evm' ∧
          R' cur' { frame with locals := frame.locals.insert retVar value } evm')
    (hrest : equivStmts code ee g s0 cfg pc' R' rest Post) :
    equivStmts code ee g s0 cfg pc R
      (.externalCall receiver name eth args retVar perm :: rest) Post := by
  intro cur k C frame evm hpc hRD hw hR
  obtain ⟨target, sendVal, argVals, evm', out, value, cur', k', C',
    hrec, heth, hargs, hcallEVM, hdec, hpc', hRD', hw', hR'⟩ := hcall cur k C frame evm hpc hRD hw hR
  obtain ⟨result, hblock, hmatch⟩ :=
    hrest cur' k' C' { frame with locals := frame.locals.insert retVar value } evm' hpc' hRD' hw' hR'
  exact ⟨result,
    ExecBlock.consNormal (ExecStmt.externalCallSuccess hrec heth hargs hcallEVM hdec) hblock, hmatch⟩

/-- **consequence (strengthen the precondition).** -/
theorem equivStmts.consequencePre {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {pc : UInt256} {R R' : StateRel} {Post : StmtPost} {stmts}
    (himp : ∀ cur frame evm, R' cur frame evm → R cur frame evm)
    (h : equivStmts code ee g s0 cfg pc R stmts Post) :
    equivStmts code ee g s0 cfg pc R' stmts Post := by
  intro cur k C frame evm hpc hRD hw hR'
  exact h cur k C frame evm hpc hRD hw (himp cur frame evm hR')

/-- **consequence (weaken the postcondition).** -/
theorem equivStmts.consequencePost {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {pc : UInt256} {R : StateRel} {Post Post' : StmtPost} {stmts}
    (himp : ∀ result, Post result → Post' result)
    (h : equivStmts code ee g s0 cfg pc R stmts Post) :
    equivStmts code ee g s0 cfg pc R stmts Post' := by
  intro cur k C frame evm hpc hRD hw hR
  obtain ⟨result, hblock, hmatch⟩ := h cur k C frame evm hpc hRD hw hR
  exact ⟨result, hblock, himp result hmatch⟩

/-! ### Sequencing (chunk composition) -/

/-- Append helper: if `s1` falls through to `(f1, e1)`, running `s2` from there is running `s1 ++ s2`. -/
theorem execBlock_append {cfg : Config} {s2 : List Stmt} :
    ∀ {s1 : List Stmt} {f e f1 e1 r}, ExecBlock cfg f e s1 (.ok f1 e1) → ExecBlock cfg f1 e1 s2 r →
      ExecBlock cfg f e (s1 ++ s2) r := by
  intro s1
  induction s1 with
  | nil => intro f e f1 e1 r h1 h2; cases h1; exact h2
  | cons stmt rest ih =>
      intro f e f1 e1 r h1 h2
      cases h1 with
      | consNormal hstmt hrest => exact ExecBlock.consNormal hstmt (ih hrest h2)

/-- Append helper: if `s1` *terminates* (any non-`.ok` result), `s1 ++ s2` terminates the same way —
    `s2` never runs. -/
theorem execBlock_append_term {cfg : Config} {s2 : List Stmt} :
    ∀ {s1 : List Stmt} {f e r}, ExecBlock cfg f e s1 r → (∀ f' e', r ≠ .ok f' e') →
      ExecBlock cfg f e (s1 ++ s2) r := by
  intro s1
  induction s1 with
  | nil => intro f e r h1 hterm; cases h1; exact absurd rfl (hterm _ _)
  | cons stmt rest ih =>
      intro f e r h1 hterm
      cases h1 with
      | consNormal hstmt hrest => exact ExecBlock.consNormal hstmt (ih hrest hterm)
      | consReturn hstmt => exact ExecBlock.consReturn hstmt
      | consRevert hstmt => exact ExecBlock.consRevert hstmt
      | consBreak hstmt => exact ExecBlock.consBreak hstmt
      | consContinue hstmt => exact ExecBlock.consContinue hstmt

/-- Postcondition for the left side of a sequence.  A fall-through result must reach the seam
    relation `S` at `pcmid`; any non-fall-through result is already checked by the final `Post`. -/
def seqPost (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (pcmid : UInt256) (S : StateRel) (Post : StmtPost) : StmtPost
  | .ok frame' evm' =>
      ∃ cur' k' C', cur'.pc = pcmid ∧ RDc code ee g s0 cur' k' C'
        ∧ cur'.world = worldOf evm' ∧ S cur' frame' evm'
  | .returned frame' evm' rv =>
      Post (.returned frame' evm' rv)
  | .reverted =>
      Post .reverted
  | .break frame' evm' =>
      Post (.break frame' evm')
  | .continue frame' evm' =>
      Post (.continue frame' evm')

/-- Concrete **seq (chunk composition)** for coupled proof states.  The first chunk is proved from
    the current state using `seqPost`; on fall-through, the midpoint facts are repackaged as the
    coupled state consumed by the second chunk. -/
theorem CoupledState.refines.seq {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cfg : Config} {pc pcmid : UInt256} {R S : StateRel} {Post : StmtPost}
    {s1 s2 : List Stmt}
    (st : CoupledState code ee g s0 R pc)
    (h1 : CoupledState.refines st cfg s1 (seqPost code ee g s0 pcmid S Post))
    (h2 : ∀ st' : CoupledState code ee g s0 S pcmid,
      CoupledState.refines st' cfg s2 Post) :
    CoupledState.refines st cfg (s1 ++ s2) Post := by
  obtain ⟨result1, hblock1, hmatch1⟩ := h1
  cases result1 with
  | ok frame1 evm1 =>
      obtain ⟨cur1, k1, C1, hpc1, hRD1, hw1, hS⟩ := hmatch1
      let st1 : CoupledState code ee g s0 S pcmid :=
        { cur := cur1, k := k1, C := C1, frame := frame1, evm := evm1,
          hpc := hpc1, hRD := hRD1, hworld := hw1, hrel := hS }
      obtain ⟨result2, hblock2, hmatch2⟩ := h2 st1
      exact ⟨result2, execBlock_append hblock1 hblock2, hmatch2⟩
  | returned frame1 evm1 rv =>
      exact ⟨_, execBlock_append_term hblock1 (by intro f' e' h; simp at h), hmatch1⟩
  | reverted =>
      exact ⟨_, execBlock_append_term hblock1 (by intro f' e' h; simp at h), hmatch1⟩
  | «break» frame1 evm1 =>
      exact ⟨_, execBlock_append_term hblock1 (by intro f' e' h; simp at h), hmatch1⟩
  | «continue» frame1 evm1 =>
      exact ⟨_, execBlock_append_term hblock1 (by intro f' e' h; simp at h), hmatch1⟩

/-- **seq (chunk composition).**  Glue two chunks at a chosen boundary `pcmid`.  If `s1` falls
    through, its `seqPost` supplies the `RDc` cursor and relation for `s2`; if `s1` returns,
    reverts, breaks, or continues, that result is already the whole appended block's result.

    Composition needs no transitivity — the EVM facts (`RDc`/terminal facts embedded in `Post`) are
    absolute from `s0`, so they carry through verbatim. -/
theorem equivStmts.seq {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {pc pcmid : UInt256} {R S : StateRel} {Post : StmtPost}
    {s1 s2 : List Stmt}
    (h1 : equivStmts code ee g s0 cfg pc R s1 (seqPost code ee g s0 pcmid S Post))
    (h2 : equivStmts code ee g s0 cfg pcmid S s2 Post) :
    equivStmts code ee g s0 cfg pc R (s1 ++ s2) Post := by
  intro cur k C frame evm hpc hRD hw hR
  obtain ⟨result1, hblock1, hmatch1⟩ := h1 cur k C frame evm hpc hRD hw hR
  cases result1 with
  | ok f1 e1 =>
      obtain ⟨cur1, k1, C1, hpc1, hRD1, hw1, hS⟩ := hmatch1
      obtain ⟨result2, hblock2, hmatch2⟩ :=
        h2 cur1 k1 C1 f1 e1 hpc1 hRD1 hw1 hS
      exact ⟨result2, execBlock_append hblock1 hblock2, hmatch2⟩
  | returned f1 e1 rv =>
      exact ⟨_, execBlock_append_term hblock1 (by intro f' e' h; simp at h), hmatch1⟩
  | reverted =>
      exact ⟨_, execBlock_append_term hblock1 (by intro f' e' h; simp at h), hmatch1⟩
  | «break» f1 e1 =>
      exact ⟨_, execBlock_append_term hblock1 (by intro f' e' h; simp at h), hmatch1⟩
  | «continue» f1 e1 =>
      exact ⟨_, execBlock_append_term hblock1 (by intro f' e' h; simp at h), hmatch1⟩

/-! ### Up to the function and the contract -/

/-- Per-function equivalence: from possibly representation-different initial maps, the EVM body and
    the Solm body `t.body` (run with `callargs`) reach a matching terminal result — both return
    ABI-coupled values with equivalent final worlds, or both revert. -/
inductive equivTransition (cfg : Config) (contract : ContractDecl) (t : TransitionDecl)
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (bl : ProcessedBlocks)
    (σ_evm σ_solm σ₀ : AccountMap) (A : Substate) (I : ExecutionEnv)
    (g : Sat256)
    (code : ByteArray) (callargs : Store) : Prop where
  | returns {o : ByteArray} {cs : Frame} {retVal} {evm'' : State}
      {world : Batteries.RBSet AccountAddress compare × AccountMap} :
      RDret code g (initState cA gh bl σ_evm σ₀ g A I) world o →
      ExecTransitionBody cfg contract (initState cA gh bl σ_solm σ₀ g A I) callargs t.body
        (.returned cs evm'' retVal) →
      world.1 = evm''.createdAccounts →
      accountMapEquiv world.2 evm''.accountMap →
      returnEquiv o retVal t.returnType →
      equivTransition cfg contract t cA gh bl σ_evm σ_solm σ₀ A I g code
        callargs
  | reverts :
      RDrev code g (initState cA gh bl σ_evm σ₀ g A I) →
      ExecTransitionBody cfg contract (initState cA gh bl σ_solm σ₀ g A I)
        callargs t.body .reverted →
      equivTransition cfg contract t cA gh bl σ_evm σ_solm σ₀ A I g code
        callargs

/-- `equivTransition` + the selector dispatches to `t` + its args decode ⟹ `runtimeEquivalenceFor`. -/
theorem equivTransition.toRuntime {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256} {code : ByteArray}
    {callargs : Store}
    (hcode : I.code = code)
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldata (t.params.map Param.name) (transitionSignature t).paramTypes
              I.calldata = some callargs)
    (h : equivTransition cfg contract t cA gh bl σ_evm σ_solm σ₀ A I g code
      callargs) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I := by
  cases h with
  | returns hret hbody hCreated hAccounts henc =>
      exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody hCreated hAccounts henc
  | reverts hrev hbody => exact hrev.reEquivExecutionRevert hcode hd hdec hbody

/-- **Bridge** — the body-level `equivStmts` ⟹ `equivTransition`.  The dispatcher reached the body
    entry (`hRD` at `pcEntry`) under the entry coupling (`hR`, `hworld`); `h` runs the body and reads
    off the matching EVM behaviour.  `.returned`/`.reverted` close directly; the `.ok` fall-through
    (body runs off the end → `ExecFuncBody.execBlockOK` gives an implicit `return none`) hands the
    post-body cursor to `hfall`, the epilogue's trailing `RETURN`.

    This bridge is for externally-dispatched transition bodies.  Internal callable bodies use
    `equivCallable` below, where Solm `.returned` means "return to caller" rather than EVM `RETURN`. -/
theorem equivStmts.toTransition {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray} {callargs : Store} {R Q : StateRel}
    {pcEntry : UInt256} {entry : Cursor} {kE CE : ℕ}
    (hpc : entry.pc = pcEntry)
    (hRD : RDc code I g (initState cA gh bl σ σ₀ g A I) entry kE CE)
    (hworld : entry.world = worldOf (initState cA gh bl σ σ₀ g A I))
    (hR : R entry { contract := contract, locals := callargs } (initState cA gh bl σ σ₀ g A I))
    (h : equivTransitionStmts code I g (initState cA gh bl σ σ₀ g A I)
      cfg t.returnType pcEntry R t.body Q)
    (hfall : ∀ cur' k' C' frame' evm',
        RDc code I g (initState cA gh bl σ σ₀ g A I) cur' k' C' → cur'.world = worldOf evm' →
        Q cur' frame' evm' →
        ∃ o, RDret code g (initState cA gh bl σ σ₀ g A I) (worldOf evm') o
          ∧ returnEquiv o none t.returnType) :
    equivTransition cfg contract t cA gh bl σ σ σ₀ A I g code callargs := by
  obtain ⟨result, hbody, hmatch⟩ :=
    h entry kE CE { contract := contract, locals := callargs } (initState cA gh bl σ σ₀ g A I)
      hpc hRD hworld hR
  cases result with
  | ok frame' evm' =>
      obtain ⟨cur', k', C', hRD', hw', hQ⟩ := hmatch
      obtain ⟨o, hRDret, henc⟩ := hfall cur' k' C' frame' evm' hRD' hw' hQ
      exact .returns hRDret (ExecFuncBody.execBlockOK hbody) rfl
        (accountMapEquiv.refl evm'.accountMap) henc
  | returned cs evm' rv =>
      obtain ⟨o, hRDret, henc⟩ := hmatch
      exact .returns hRDret (ExecFuncBody.execBlockRet hbody) rfl
        (accountMapEquiv.refl evm'.accountMap) henc
  | reverted => exact .reverts hmatch (ExecFuncBody.execBlockRevert hbody)
  | «break» _ _ => exact hmatch.elim
  | «continue» _ _ => exact hmatch.elim

/-! ### Callable/internal bodies -/

/-- Postcondition used by internal/local callables.  A Solm return reaches a caller continuation
    instead of halting the EVM; ordinary fall-through is treated as `return none`, matching
    `ExecFuncBody.execBlockOK`. -/
def callablePost (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (entry : Cursor) (returnTo : UInt256 → Prop)
    (Return : Cursor → Option Value → StoreRel) : StmtPost
  | .ok frame' evm' =>
      ∃ cur' k' C', RDc code ee g s0 cur' k' C' ∧ cur'.world = worldOf evm'
        ∧ Return entry none cur' frame'.locals evm'
        ∧ returnTo cur'.pc
  | .returned frame' evm' rv =>
      ∃ cur' k' C', RDc code ee g s0 cur' k' C' ∧ cur'.world = worldOf evm'
        ∧ Return entry rv cur' frame'.locals evm'
        ∧ returnTo cur'.pc
  | .reverted =>
      RDrev code g s0
  | .break _ _ | .continue _ _ =>
      False

/-- **Callable-body equivalence** for internal/local functions.

    Unlike `equivStmts`, a Solm `.returned rv` here is not an EVM halt.  It means the callable has
    returned to its caller, so the bytecode must reach a continuation cursor still inside the same
    contract execution.  The return postcondition is parameterized by the entry cursor and returned
    value, allowing it to express calling conventions such as "jump to the return address from the
    entry stack" and "place the return value in this stack slot".

    The precondition `R` is frame-shaped, so callers may either constrain `frame.contract` or leave
    the callable generic over contracts.  The return postcondition is locals-only (`StoreRel`) so the
    caller-resume relation can focus on the returned store. -/
def equivCallable (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (cfg : Config) (pc : UInt256) (R : StateRel) (callable : CallableDecl)
    (ReturnTo : Cursor → UInt256 → Prop)
    (Return : Cursor → Option Value → StoreRel) : Prop :=
  ∀ entry k C args (frame : Frame) evm,
    (hpc : entry.pc = pc) →
    (hRD : RDc code ee g s0 entry k C) →
    (hworld : entry.world = worldOf evm) →
    bindParams? callable.params args = .some (frame.locals) →
    (hR : R entry frame evm) →
    CoupledState.refines (CoupledState.mk entry k C frame evm hpc hRD hworld hR)
      cfg callable.body (callablePost code ee g s0 entry (ReturnTo entry) Return)

/-- Concrete proof-state version of `equivStmts.internalCall`.

    This is the intended proof-mode rule: it consumes one coupled state `st`, so the setup and
    continuation obligations are scoped to the actual call currently being peeled. -/
theorem CoupledState.refines.internalCall {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cfg : Config} {funcPc : UInt256} {R Rcall R' : StateRel}
    {Post : StmtPost} {callable : CallableDecl} {name : Ident} {args : List Expr}
    {retVar : Ident} {rest : List Stmt} {ReturnTo : Cursor → UInt256 → Prop}
    {Return : Cursor → Option Value → StoreRel}
    (st : CoupledState code ee g s0 R funcPc)
    (hequiv : equivCallable code ee g s0 cfg funcPc Rcall callable ReturnTo Return)
    (hsetup :
      ∃ argVals locals,
        evalExprs? cfg st.frame st.evm args = .ok argVals ∧
        lookupCallable? st.frame.contract name = some callable ∧
        bindParams? callable.params argVals = some locals ∧
        Rcall st.cur { st.frame with locals := locals } st.evm ∧
        (∀ rv curRet localsRet evmRet,
          Return st.cur rv curRet localsRet evmRet →
          ReturnTo st.cur curRet.pc →
          R' curRet (resumeAfterInternalCall st.frame retVar rv) evmRet))
    (hrest : ∀ rv curRet kRet CRet localsRet evmRet,
        ∀ (hRDRet : RDc code ee g s0 curRet kRet CRet)
          (hworldRet : curRet.world = worldOf evmRet)
          (_hReturn : Return st.cur rv curRet localsRet evmRet)
          (_hReturnTo : ReturnTo st.cur curRet.pc)
          (hRRet : R' curRet (resumeAfterInternalCall st.frame retVar rv) evmRet),
          CoupledState.refines
            (CoupledState.mk curRet kRet CRet (resumeAfterInternalCall st.frame retVar rv) evmRet
              rfl hRDRet hworldRet hRRet)
            cfg rest Post)
    (hrevert : RDrev code g s0 → Post .reverted) :
    CoupledState.refines st cfg (.internalCall name args retVar :: rest) Post := by
  obtain ⟨argVals, locals, hargs, hlookup, hbind, hRcall, hresume⟩ := hsetup
  obtain ⟨calleeResult, hcalleeBlock, hcalleePost⟩ :=
    hequiv st.cur st.k st.C argVals { st.frame with locals := locals } st.evm
      st.hpc st.hRD st.hworld hbind hRcall
  cases calleeResult with
  | ok calleeFrame calleeEvm =>
      obtain ⟨curRet, kRet, CRet, hRDRet, hwRet, hReturn, hReturnTo⟩ := hcalleePost
      have hstmt : ExecStmt cfg st.frame st.evm (.internalCall name args retVar)
          (.ok (resumeAfterInternalCall st.frame retVar none) calleeEvm) :=
        ExecStmt.internalCallReturn hargs hlookup hbind (ExecFuncBody.execBlockOK hcalleeBlock)
      obtain ⟨result, hrestBlock, hpost⟩ :=
        hrest none curRet kRet CRet calleeFrame.locals calleeEvm hRDRet hwRet hReturn hReturnTo
          (hresume none curRet calleeFrame.locals calleeEvm hReturn hReturnTo)
      exact ⟨result, ExecBlock.consNormal hstmt hrestBlock, hpost⟩
  | returned calleeFrame calleeEvm rv =>
      obtain ⟨curRet, kRet, CRet, hRDRet, hwRet, hReturn, hReturnTo⟩ := hcalleePost
      have hstmt : ExecStmt cfg st.frame st.evm (.internalCall name args retVar)
          (.ok (resumeAfterInternalCall st.frame retVar rv) calleeEvm) :=
        ExecStmt.internalCallReturn hargs hlookup hbind (ExecFuncBody.execBlockRet hcalleeBlock)
      obtain ⟨result, hrestBlock, hpost⟩ :=
        hrest rv curRet kRet CRet calleeFrame.locals calleeEvm hRDRet hwRet hReturn hReturnTo
          (hresume rv curRet calleeFrame.locals calleeEvm hReturn hReturnTo)
      exact ⟨result, ExecBlock.consNormal hstmt hrestBlock, hpost⟩
  | reverted =>
      have hstmt : ExecStmt cfg st.frame st.evm (.internalCall name args retVar) .reverted :=
        ExecStmt.internalCallRevert hargs hlookup hbind (ExecFuncBody.execBlockRevert hcalleeBlock)
      exact ⟨.reverted, ExecBlock.consRevert hstmt, hrevert hcalleePost⟩
  | «break» _ _ =>
      exact hcalleePost.elim
  | «continue» _ _ =>
      exact hcalleePost.elim

/-- **internal call (success / revert)** — peel an internal Solm call when the EVM cursor is already
    at the callee body entry `funcPc`.

    `hsetup` is the caller-to-callee Solm bridge: it evaluates the caller arguments, checks the
    callable lookup, binds callee locals, establishes the callable precondition `Rcall`, and explains
    how a callable return relation resumes the caller frame.  No extra EVM setup cursor is produced
    here; if bytecode must jump from a call-site to `funcPc`, prove that as a preceding segment.

    `hrest` is indexed by the return PC relation supplied by the callable proof, but only for entries
    satisfying this rule's own call-site precondition.  That keeps the continuation obligation local
    to the call being peeled instead of requiring it for every possible callable entry. -/
theorem equivStmts.internalCall {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cfg : Config} {funcPc : UInt256} {R Rcall R' : StateRel} {Post : StmtPost}
    {callable : CallableDecl} {name : Ident} {args : List Expr} {retVar : Ident}
    {rest : List Stmt} {ReturnTo : Cursor → UInt256 → Prop}
    {Return : Cursor → Option Value → StoreRel}
    (hequiv : equivCallable code ee g s0 cfg funcPc Rcall callable ReturnTo Return)
    (hsetup : ∀ cur k C frame evm,
        cur.pc = funcPc →
        RDc code ee g s0 cur k C →
        cur.world = worldOf evm →
        R cur frame evm →
        ∃ argVals locals,
          evalExprs? cfg frame evm args = .ok argVals ∧
          lookupCallable? frame.contract name = some callable ∧
          bindParams? callable.params argVals = some locals ∧
          Rcall cur { frame with locals := locals } evm ∧
          (∀ rv curRet localsRet evmRet,
            Return cur rv curRet localsRet evmRet →
            ReturnTo cur curRet.pc →
            R' curRet (resumeAfterInternalCall frame retVar rv) evmRet))
    (hrest : ∀ entry k C frame evm retPc,
        entry.pc = funcPc →
        RDc code ee g s0 entry k C →
        entry.world = worldOf evm →
        R entry frame evm →
        ReturnTo entry retPc →
        equivStmts code ee g s0 cfg retPc R' rest Post)
    (hrevert : RDrev code g s0 → Post .reverted) :
    equivStmts code ee g s0 cfg funcPc R (.internalCall name args retVar :: rest) Post := by
  intro cur k C frame evm hpc hRD hw hR
  obtain ⟨argVals, locals, hargs, hlookup, hbind, hRcall, hresume⟩ :=
    hsetup cur k C frame evm hpc hRD hw hR
  obtain ⟨calleeResult, hcalleeBlock, hcalleePost⟩ :=
    hequiv cur k C argVals { frame with locals := locals } evm hpc hRD hw hbind hRcall
  cases calleeResult with
  | ok calleeFrame calleeEvm =>
      obtain ⟨curRet, kRet, CRet, hRDRet, hwRet, hReturn, hReturnTo⟩ := hcalleePost
      have hstmt : ExecStmt cfg frame evm (.internalCall name args retVar)
          (.ok (resumeAfterInternalCall frame retVar none) calleeEvm) :=
        ExecStmt.internalCallReturn hargs hlookup hbind (ExecFuncBody.execBlockOK hcalleeBlock)
      obtain ⟨result, hrestBlock, hpost⟩ :=
        hrest cur k C frame evm curRet.pc hpc hRD hw hR hReturnTo curRet kRet CRet
          (resumeAfterInternalCall frame retVar none) calleeEvm rfl hRDRet hwRet
          (hresume none curRet calleeFrame.locals calleeEvm hReturn hReturnTo)
      exact ⟨result, ExecBlock.consNormal hstmt hrestBlock, hpost⟩
  | returned calleeFrame calleeEvm rv =>
      obtain ⟨curRet, kRet, CRet, hRDRet, hwRet, hReturn, hReturnTo⟩ := hcalleePost
      have hstmt : ExecStmt cfg frame evm (.internalCall name args retVar)
          (.ok (resumeAfterInternalCall frame retVar rv) calleeEvm) :=
        ExecStmt.internalCallReturn hargs hlookup hbind (ExecFuncBody.execBlockRet hcalleeBlock)
      obtain ⟨result, hrestBlock, hpost⟩ :=
        hrest cur k C frame evm curRet.pc hpc hRD hw hR hReturnTo curRet kRet CRet
          (resumeAfterInternalCall frame retVar rv) calleeEvm rfl hRDRet hwRet
          (hresume rv curRet calleeFrame.locals calleeEvm hReturn hReturnTo)
      exact ⟨result, ExecBlock.consNormal hstmt hrestBlock, hpost⟩
  | reverted =>
      have hstmt : ExecStmt cfg frame evm (.internalCall name args retVar) .reverted :=
        ExecStmt.internalCallRevert hargs hlookup hbind (ExecFuncBody.execBlockRevert hcalleeBlock)
      exact ⟨.reverted, ExecBlock.consRevert hstmt, hrevert hcalleePost⟩
  | «break» _ _ =>
      exact hcalleePost.elim
  | «continue» _ _ =>
      exact hcalleePost.elim

end Reasoning.Refinement
