import EVMReasoning.Reach

/-!
# Trace — the EVM straight-line execution tracker

`Run code s0 cur k C` is the segment invariant a bytecode proof carries while it walks the
run of `code` from the initial state `s0`:

> either the whole run `X (budget + 1) … s0` has already run out of gas, **or** there is a
> state reached after `k` steps and `C` gas whose cursor is `cur`, with `k ≤ C ≤ budget`.

The cursor packs everything an instruction can change: the machine state (`pc`, stack, memory,
active words, return-data buffer) and the persistent world (created accounts, account map,
event log).  The run's constants are never duplicated as arguments: the execution environment,
the gas budget and the read-only world fields are read from `s0`.  `code` stays a separate
argument because it is the bytecode *literal* every `decode` obligation is discharged on.

Each opcode is a forward combinator `Run … cur k C → decode … → Run … cur' (k+1) (C+cost)`;
chains are ordinary function application (`h.jumpdest … |>.push1 …`, or `evm_run`), and the
out-of-gas case threads itself inside the `Prop`.  The terminals `Returned` (world and output)
and `Reverted` (revert data) record how the whole run halted; `Returned.xi`/`Reverted.xi` turn
them into `Ξ` results.

This library succeeds `Reasoning.Reach.RD`, which tracked no event log and forgot revert data.
It reuses Reach's `evm_run`/`evm_ov`/`mem_cost` macros and its bytecode-shape definitions
(`pushAt`, `armWellFormed`, …); none of the `RD` lemmas are used.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Trace

open Reasoning.Theory
open Reasoning.Reach (pushAt armSelNat armTgt armTgtOp armTgtWidth armWellFormed selArmPush4Pc
  selArmEqPc selArmPushTgtPc selArmJumpiPc selArmNextPc selArmPushSelPcW selArmEqPcW
  selArmPushTgtPcW selArmJumpiPcW selArmNextPcW armSelNatW armSelOpW armTgtOpW armTgtW armTgtWidthW
  armWellFormedW selectorSplitWellFormed nthArmPc Theta_returnedGas_le Theta_returnData_size_lt)

set_option maxRecDepth 10000

/-! ## Cursor, world and the invariant -/

/-- The persistent world of a run: what survives the call and what a refinement relation
    observes on success. -/
structure World where
  created  : Batteries.RBSet AccountAddress compare
  accounts : AccountMap
  logs     : LogSeries

/-- Everything an instruction can change. -/
structure Cursor where
  pc    : UInt256
  stack : List UInt256
  mem   : ByteArray
  aw    : UInt256
  rdata : ByteArray
  world : World

@[simp] theorem World.eta (w : World) : (⟨w.created, w.accounts, w.logs⟩ : World) = w := rfl

/-- The cursor of a state. -/
def cursorOf (s : State) : Cursor :=
  ⟨s.machineState.pc, s.machineState.stack, s.machineState.memory, s.machineState.activeWords,
    s.machineState.returnData, ⟨s.createdAccounts, s.accountMap, s.substate.logSeries⟩⟩

theorem cursorOf_eq {s : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {w : World} :
    cursorOf s = ⟨pc, stk, mem, aw, rdata, w⟩ ↔
      s.machineState.pc = pc ∧ s.machineState.stack = stk ∧ s.machineState.memory = mem
      ∧ s.machineState.activeWords = aw ∧ s.machineState.returnData = rdata
      ∧ s.createdAccounts = w.created ∧ s.accountMap = w.accounts
      ∧ s.substate.logSeries = w.logs := by
  cases w; simp [cursorOf]

/-- The run's gas budget: the initial state's gas. -/
abbrev budget (s0 : State) : Sat256 := s0.machineState.gasAvailable

/-- The fields no instruction changes: the execution environment and the read-only world. -/
def Static (s0 s : State) : Prop :=
  s.executionEnv = s0.executionEnv ∧ s.σ₀ = s0.σ₀ ∧ s.genesisBlockHeader = s0.genesisBlockHeader
    ∧ s.blocks = s0.blocks

theorem Static.refl (s : State) : Static s s := ⟨rfl, rfl, rfl, rfl⟩

theorem Static.trans {s0 s s' : State} (h : Static s0 s) (h' : Static s s') : Static s0 s' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.trans h.2.2.2⟩

/-- Reached-or-out-of-gas: after `k` steps and `C` gas, the run of `code` from `s0` is at `cur`. -/
def Run (code : ByteArray) (s0 : State) (cur : Cursor) (k C : ℕ) : Prop :=
  X ((budget s0).toNat + 1) (D_J code 0) s0 = .error .OutOfGass
  ∨ ∃ s : State,
      X ((budget s0).toNat + 1) (D_J code 0) s0 = X ((budget s0).toNat + 1 - k) (D_J code 0) s
    ∧ s.executionEnv.code = code
    ∧ cursorOf s = cur
    ∧ s.machineState.gasAvailable = (budget s0).subNat C
    ∧ k ≤ C ∧ C ≤ (budget s0).toNat
    ∧ Static s0 s

/-- The run halted successfully, returning `o` and leaving the world `w`. -/
def Returned (code : ByteArray) (s0 : State) (w : World) (o : ByteArray) : Prop :=
  X ((budget s0).toNat + 1) (D_J code 0) s0 = .error .OutOfGass
  ∨ ∃ s', X ((budget s0).toNat + 1) (D_J code 0) s0 = .ok (.success s' o)
        ∧ s'.createdAccounts = w.created ∧ s'.accountMap = w.accounts
        ∧ s'.substate.logSeries = w.logs

/-- The run reverted with data `o`. -/
def Reverted (code : ByteArray) (s0 : State) (o : ByteArray) : Prop :=
  X ((budget s0).toNat + 1) (D_J code 0) s0 = .error .OutOfGass
  ∨ ∃ g', X ((budget s0).toNat + 1) (D_J code 0) s0 = .ok (.revert g' o)

variable {code : ByteArray} {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray}
  {aw : UInt256} {rdata : ByteArray} {w : World} {k C : ℕ} {a b c d e f : UInt256}
  {t : List UInt256}

/-! ## Entering and leaving the invariant -/

/-- Open the invariant at a state `s` whose cursor is `cur`. -/
theorem Run.start {s : State} {cur : Cursor}
    (hX : X ((budget s0).toNat + 1) (D_J code 0) s0 = X ((budget s0).toNat + 1 - k) (D_J code 0) s)
    (hcode : s.executionEnv.code = code) (hcur : cursorOf s = cur)
    (hgas : s.machineState.gasAvailable = (budget s0).subNat C) (hk : k ≤ C)
    (hC : C ≤ (budget s0).toNat) (hst : Static s0 s) :
    Run code s0 cur k C :=
  Or.inr ⟨s, hX, hcode, hcur, hgas, hk, hC, hst⟩

/-- The entry cursor of a message call: pc `0`, empty stack/memory/return data, the genesis
    accounts and the incoming log series, nothing consumed yet. -/
theorem Run.initState {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {g : Sat256} {A : Substate} {I : ExecutionEnv}
    (hcode : I.code = code) :
    Run code (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      ⟨⟨0⟩, [], ByteArray.empty, UInt256.ofNat 0, ByteArray.empty, ⟨cA, σ, A.logSeries⟩⟩ 0 0 :=
  Run.start (s := Reasoning.Theory.initState cA gh bl σ σ₀ g A I) rfl hcode
    (by simp [cursorOf, Reasoning.Theory.initState]; repeat' constructor) (Sat256.subNat_zero _).symm
    (le_refl 0) (Nat.zero_le _) (Static.refl _)

/-- Expose the invariant's witnesses (the counters become existential). -/
theorem Run.conclude {cur : Cursor} (h : Run code s0 cur k C) :
    X ((budget s0).toNat + 1) (D_J code 0) s0 = .error .OutOfGass
    ∨ ∃ (k' C' : ℕ) (s' : State),
        X ((budget s0).toNat + 1) (D_J code 0) s0 = X ((budget s0).toNat + 1 - k') (D_J code 0) s'
      ∧ s'.executionEnv.code = code ∧ cursorOf s' = cur
      ∧ s'.machineState.gasAvailable = (budget s0).subNat C' ∧ k' ≤ C' ∧ C' ≤ (budget s0).toNat
      ∧ Static s0 s' := by
  rcases h with hoog | ⟨s', hX, hcode, hcur, hgas, hk, hC, hst⟩
  · exact Or.inl hoog
  · exact Or.inr ⟨k, C, s', hX, hcode, hcur, hgas, hk, hC, hst⟩

/-- A cursor claimed beyond the gas budget can only be the out-of-gas branch. -/
theorem Run.oog_of_cost_gt {cur : Cursor} (h : Run code s0 cur k C)
    (hgt : (budget s0).toNat < C) :
    X ((budget s0).toNat + 1) (D_J code 0) s0 = .error .OutOfGass := by
  rcases h with hoog | ⟨_, _, _, _, _, _, hC, _⟩
  · exact hoog
  · omega

/-! ## The generic step

Every continue-instruction is an instance of `Run.step` (fixed cost) or `Run.stepVar` (cost
read from the reached state): the caller supplies the instruction's `Xstep` fact and the successor's
cursor.  `trace_succ` discharges the successor obligation for a `Stepping` state-update. -/

/-- One continue-step of cost `cost`: from any state at `cur`, the instruction yields `f s` at
    `cur'`. -/
theorem Run.step {cur cur' : Cursor} {cost : ℕ} {f : State → State}
    (h : Run code s0 cur k C)
    (hstep : ∀ s : State, s.executionEnv.code = code → Static s0 s → cursorOf s = cur →
        Xstep (D_J code 0) s =
          if s.machineState.gasAvailable.toNat < cost then .error .OutOfGass
          else .ok (f s, .none))
    (hsucc : ∀ s : State, s.executionEnv.code = code → Static s0 s → cursorOf s = cur →
        cursorOf (f s) = cur'
        ∧ (f s).machineState.gasAvailable = s.machineState.gasAvailable.subNat cost
        ∧ Static s (f s))
    (hpos : 0 < cost := by decide) :
    Run code s0 cur' (k + 1) (C + cost) := by
  rcases h with hoog | ⟨s, hX, hcode, hcur, hgas, hk, hC, hst⟩
  · exact Or.inl hoog
  have st := hstep s hcode hst hcur
  obtain ⟨hcur', hgas', hst'⟩ := hsucc s hcode hst hcur
  by_cases gg : (budget s0).toNat < C + cost
  · exact Or.inl (hX.trans (stepOOG hgas st hk hC gg))
  · refine Or.inr ⟨f s, hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, hcur', ?_,
      by omega, by omega, hst.trans hst'⟩
    · rw [hst'.1]; exact hcode
    · rw [hgas', hgas, Sat256.subNat_subNat]

/-- One continue-step whose gas guard and charge are read from the reached state (`SLOAD`,
    `SSTORE`, `EXTCODESIZE`, …): the counters become existential. -/
theorem Run.stepVar {cur cur' : Cursor} {guard cost : State → ℕ} {f : State → State}
    (h : Run code s0 cur k C)
    (hstep : ∀ s : State, s.executionEnv.code = code → Static s0 s → cursorOf s = cur →
        Xstep (D_J code 0) s =
          if s.machineState.gasAvailable.toNat < guard s then .error .OutOfGass
          else .ok (f s, .none))
    (hsucc : ∀ s : State, s.executionEnv.code = code → Static s0 s → cursorOf s = cur →
        cursorOf (f s) = cur'
        ∧ (f s).machineState.gasAvailable = s.machineState.gasAvailable.subNat (cost s)
        ∧ 1 ≤ cost s ∧ cost s ≤ guard s
        ∧ Static s (f s)) :
    ∃ k' C', Run code s0 cur' k' C' := by
  rcases h with hoog | ⟨s, hX, hcode, hcur, hgas, hk, hC, hst⟩
  · exact ⟨k, C, Or.inl hoog⟩
  have st := hstep s hcode hst hcur
  obtain ⟨hcur', hgas', hpos, hle, hst'⟩ := hsucc s hcode hst hcur
  by_cases gg : (budget s0).toNat < C + guard s
  · exact ⟨k, C, Or.inl (hX.trans (stepOOG hgas st hk hC gg))⟩
  · refine ⟨k + 1, C + cost s,
      Or.inr ⟨f s, hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, hcur', ?_,
        by omega, by omega, hst.trans hst'⟩⟩
    · rw [hst'.1]; exact hcode
    · rw [hgas', hgas, Sat256.subNat_subNat]

/-- Discharge the successor obligation of `Run.step`/`Run.stepVar` for a successor built by the
    `Stepping` state-update `succ`: unfold it and rewrite the input cursor's fields (named `hpc hstk
    hmem haw hrdata hcA hσ hlogs`, with `hst : Static s0 s` and `hcode`), plus the optional extra
    rewrite terms.  Expects the section variables `code`/`s0` in scope. -/
syntax "trace_succ " ident " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
syntax "trace_succ " ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| trace_succ $succ:ident [ $extra,* ]) =>
    `(tactic| (intro s hcode hst hcur
               have hcode0 : s0.executionEnv.code = code := hst.1 ▸ hcode
               obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
               refine ⟨?_, ?_, ⟨rfl, rfl, rfl, rfl⟩⟩
               · simp only [cursorOf, $succ:ident, Cursor.mk.injEq, World.mk.injEq, World.eta,
                   hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs, hst.1, hcode, hcode0, and_self,
                   and_true, true_and, eq_self_iff_true, $extra,*]
               · first | (simp only [$succ:ident, Sat256.subNat_subNat, $extra,*]; done) | rfl))
macro_rules
  | `(tactic| trace_succ $succ:ident) => `(tactic| trace_succ $succ:ident [])

/-! ## Stack and environment instructions (fixed cost) -/

theorem Run.jumpdest (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.JUMPDEST, .none)) (hov : stk.length ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, stk, mem, aw, rdata, w⟩ (k + 1) (C + 1) :=
  h.step (fun s hc _ hcur =>
      jumpdest_xstep hc (cursorOf_eq.mp hcur).1 hdec (by rw [(cursorOf_eq.mp hcur).2.1]; exact hov))
    (by trace_succ stJumpdest)

theorem Run.push0 (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.PUSH0, .none)) (hov : stk.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, ⟨0⟩ :: stk, mem, aw, rdata, w⟩ (k + 1) (C + 2) :=
  h.step (fun s hc _ hcur =>
      push0_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stPush0)

theorem Run.push1 (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH1, some (argv, 1))) (hov : stk.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + UInt256.ofNat 2, argv :: stk, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur =>
      push1_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stPush1)

theorem Run.push2 (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH2, some (argv, 2))) (hov : stk.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + UInt256.ofNat 3, argv :: stk, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur =>
      push2_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stPush2)

theorem Run.push4 (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH4, some (argv, 4))) (hov : stk.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + UInt256.ofNat 5, argv :: stk, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur =>
      push4_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stPush4)

theorem Run.push20 (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH20, some (argv, 20))) (hov : stk.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + UInt256.ofNat 21, argv :: stk, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur =>
      push20_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stPush20)

/-- Width-generic `PUSHk` (`k ≥ 1`): pushes `argv`, advancing `pc` by `width + 1` (read from the
    decode fact).  `push1`/`push2`/… are its fixed-width specializations. -/
theorem Run.pushConst (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C) (argv : UInt256)
    {width : ℕ} {op : Operation.POp} (hop : op ≠ .PUSH0)
    (hdec : decode code pc = some (.Push op, some (argv, width))) (hov : stk.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + UInt256.ofNat width.succ, argv :: stk, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur =>
      pushConst_xstep hc (cursorOf_eq.mp hcur).1 hop hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stPushConst)

theorem Run.dup1 (h : Run code s0 ⟨pc, a :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.DUP1, .none)) (hov : t.length + 2 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, a :: a :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur =>
      dup1_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1
        (by simp only [List.length_cons]; omega))
    (by trace_succ stDup1)

theorem Run.pop (h : Run code s0 ⟨pc, a :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.POP, .none)) (hov : t.length ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, t, mem, aw, rdata, w⟩ (k + 1) (C + 2) :=
  h.step (fun s hc _ hcur => pop_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stPop)

theorem Run.iszero (h : Run code s0 ⟨pc, a :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.ISZERO, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.isZero a :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur =>
      iszero_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1
        (by simp only [List.length_cons]; omega))
    (by trace_succ stIsZero)

theorem Run.not (h : Run code s0 ⟨pc, a :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.NOT, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.lnot a :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => not_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stNot)

/-- Internal `JUMP` to the statically-valid destination `a`. -/
theorem Run.jump (h : Run code s0 ⟨pc, a :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.JUMP, .none)) (hjd : (D_J code 0).contains a = true)
    (hov : t.length ≤ 1024) :
    Run code s0 ⟨a, t, mem, aw, rdata, w⟩ (k + 1) (C + 8) :=
  h.step (fun s hc _ hcur =>
      jump_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hjd hov)
    (by trace_succ stJump)

/-- `JUMPI` **taken** (condition `b ≠ 0`) to the statically-valid destination `a`. -/
theorem Run.jumpiT (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.JUMPI, .none)) (hb : b ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains a = true) (hov : t.length ≤ 1024) :
    Run code s0 ⟨a, t, mem, aw, rdata, w⟩ (k + 1) (C + 10) :=
  h.step (fun s hc _ hcur =>
      jumpi_t_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hb hjd hov)
    (by trace_succ stJumpiT)

/-- `JUMPI` **not taken** (condition `b = 0`): falls through to `pc + 1`. -/
theorem Run.jumpiNT (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.JUMPI, .none)) (hb : b = ⟨0⟩) (hov : t.length ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, t, mem, aw, rdata, w⟩ (k + 1) (C + 10) := by
  subst hb
  exact h.step (fun s hc _ hcur =>
      jumpi_nt_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stJumpiNT)

/-! ### Binary operators (cost 3 or 5) and swaps/dups (cost 3) -/

theorem Run.eq (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.EQ, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.eq a b :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => eq_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stBinop)

theorem Run.lt (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.LT, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.lt a b :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => lt_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stBinop)

theorem Run.gt (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.GT, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.gt a b :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => gt_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stBinop)

theorem Run.slt (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SLT, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.slt a b :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => slt_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stBinop)

theorem Run.sgt (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SGT, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.sgt a b :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => sgt_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stBinop)

theorem Run.shr (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SHR, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.shiftRight b a :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => shr_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stBinop)

theorem Run.shl (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SHL, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.shiftLeft b a :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => shl_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stBinop)

theorem Run.sub (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SUB, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.sub a b :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => sub_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stBinop)

theorem Run.add (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.ADD, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, (a + b) :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => add_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stBinop)

theorem Run.and (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.AND, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.land a b :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => and_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stBinop)

theorem Run.or (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.OR, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.lor a b :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => or_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stBinop)

theorem Run.xor (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.XOR, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.xor a b :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => xor_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stBinop)

theorem Run.mod (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.MOD, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.mod a b :: t, mem, aw, rdata, w⟩ (k + 1) (C + 5) :=
  h.step (fun s hc _ hcur => mod_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stBinop5)

theorem Run.mul (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.MUL, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.mul a b :: t, mem, aw, rdata, w⟩ (k + 1) (C + 5) :=
  h.step (fun s hc _ hcur => mul_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stBinop5)

theorem Run.div (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.DIV, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.div a b :: t, mem, aw, rdata, w⟩ (k + 1) (C + 5) :=
  h.step (fun s hc _ hcur => div_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stBinop5)

theorem Run.exp (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.EXP, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.exp a b :: t, mem, aw, rdata, w⟩ (k + 1) (C + expGasCost b) :=
  h.step (fun s hc _ hcur => exp_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stExp) (expGasCost_pos b)

theorem Run.swap1 (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SWAP1, .none)) (hov : t.length + 2 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, b :: a :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => swap1_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.swap2 (h : Run code s0 ⟨pc, a :: b :: c :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SWAP2, .none)) (hov : t.length + 3 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, c :: b :: a :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => swap2_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.swap3 (h : Run code s0 ⟨pc, a :: b :: c :: d :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SWAP3, .none)) (hov : t.length + 4 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, d :: b :: c :: a :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => swap3_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.swap4 (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SWAP4, .none)) (hov : t.length + 5 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, e :: b :: c :: d :: a :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => swap4_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.swap5 (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: f :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SWAP5, .none)) (hov : t.length + 6 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, f :: b :: c :: d :: e :: a :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => swap5_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.swap6 {x7 : UInt256}
    (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: f :: x7 :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SWAP6, .none)) (hov : t.length + 7 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, x7 :: b :: c :: d :: e :: f :: a :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => swap6_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.swap7 {x7 x8 : UInt256}
    (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: f :: x7 :: x8 :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SWAP7, .none)) (hov : t.length + 8 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, x8 :: b :: c :: d :: e :: f :: x7 :: a :: t, mem, aw, rdata, w⟩
      (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => swap7_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.swap8 {x7 x8 x9 : UInt256}
    (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SWAP8, .none)) (hov : t.length + 9 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, x9 :: b :: c :: d :: e :: f :: x7 :: x8 :: a :: t, mem, aw, rdata, w⟩
      (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => swap8_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.swap10 {x7 x8 x9 x10 x11 : UInt256}
    (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: x10 :: x11 :: t,
      mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SWAP10, .none)) (hov : t.length + 11 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, x11 :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: x10 :: a :: t,
      mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => swap10_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.swap11 {x7 x8 x9 x10 x11 x12 : UInt256}
    (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: t,
      mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SWAP11, .none)) (hov : t.length + 12 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, x12 :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: x10 :: x11 :: a :: t,
      mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => swap11_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.dup2 (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.DUP2, .none)) (hov : t.length + 3 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, b :: a :: b :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => dup2_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.dup3 (h : Run code s0 ⟨pc, a :: b :: c :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.DUP3, .none)) (hov : t.length + 4 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, c :: a :: b :: c :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => dup3_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.dup4 (h : Run code s0 ⟨pc, a :: b :: c :: d :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.DUP4, .none)) (hov : t.length + 5 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, d :: a :: b :: c :: d :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => dup4_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.dup5 (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.DUP5, .none)) (hov : t.length + 6 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, e :: a :: b :: c :: d :: e :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => dup5_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.dup6 (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: f :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.DUP6, .none)) (hov : t.length + 7 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, f :: a :: b :: c :: d :: e :: f :: t, mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => dup6_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.dup7 {x7 : UInt256}
    (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: f :: x7 :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.DUP7, .none)) (hov : t.length + 8 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, x7 :: a :: b :: c :: d :: e :: f :: x7 :: t, mem, aw, rdata, w⟩
      (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => dup7_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.dup8 {x7 x8 : UInt256}
    (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: f :: x7 :: x8 :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.DUP8, .none)) (hov : t.length + 9 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, x8 :: a :: b :: c :: d :: e :: f :: x7 :: x8 :: t, mem, aw, rdata, w⟩
      (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => dup8_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.dup9 {x7 x8 x9 : UInt256}
    (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.DUP9, .none)) (hov : t.length + 10 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, x9 :: a :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: t, mem, aw, rdata, w⟩
      (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => dup9_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.dup10 {x7 x8 x9 x10 : UInt256}
    (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: x10 :: t,
      mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.DUP10, .none)) (hov : t.length + 11 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, x10 :: a :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: x10 :: t,
      mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => dup10_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.dup11 {x7 x8 x9 x10 x11 : UInt256}
    (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: x10 :: x11 :: t,
      mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.DUP11, .none)) (hov : t.length + 12 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, x11 :: a :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: x10 :: x11 :: t,
      mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => dup11_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.dup13 {x7 x8 x9 x10 x11 x12 x13 : UInt256}
    (h : Run code s0
      ⟨pc, a :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: t,
        mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.DUP13, .none)) (hov : t.length + 14 ≤ 1024) :
    Run code s0
      ⟨pc + ⟨1⟩, x13 :: a :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: t,
        mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => dup13_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.dup14 {x7 x8 x9 x10 x11 x12 x13 x14 : UInt256}
    (h : Run code s0
      ⟨pc, a :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: t,
        mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.DUP14, .none)) (hov : t.length + 15 ≤ 1024) :
    Run code s0
      ⟨pc + ⟨1⟩,
        x14 :: a :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: t,
        mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => dup14_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

theorem Run.dup15 {x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256}
    (h : Run code s0
      ⟨pc, a :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: t,
        mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.DUP15, .none)) (hov : t.length + 16 ≤ 1024) :
    Run code s0
      ⟨pc + ⟨1⟩,
        x15 :: a :: b :: c :: d :: e :: f :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15
          :: t,
        mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur => dup15_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stSwap)

/-! ### Environment reads (cost 2, `CALLDATALOAD` 3) -/

theorem Run.callvalue (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.CALLVALUE, .none)) (hov : stk.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, s0.executionEnv.weiValue :: stk, mem, aw, rdata, w⟩ (k + 1) (C + 2) :=
  h.step (fun s hc _ hcur =>
      callvalue_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stCallvalue)

theorem Run.timestamp (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.TIMESTAMP, .none)) (hov : stk.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.ofNat s0.executionEnv.header.timestamp :: stk, mem, aw, rdata, w⟩
      (k + 1) (C + 2) :=
  h.step (fun s hc _ hcur =>
      timestamp_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stTimestamp)

theorem Run.chainid (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.CHAINID, .none)) (hov : stk.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.ofNat Ethereum.chainId :: stk, mem, aw, rdata, w⟩ (k + 1) (C + 2) :=
  h.step (fun s hc _ hcur =>
      chainid_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stChainid)

theorem Run.calldatasize (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.CALLDATASIZE, .none)) (hov : stk.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.ofNat s0.executionEnv.calldata.size :: stk, mem, aw, rdata, w⟩
      (k + 1) (C + 2) :=
  h.step (fun s hc _ hcur =>
      calldatasize_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stCalldatasize)

theorem Run.calldataload (h : Run code s0 ⟨pc, a :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.CALLDATALOAD, .none)) (hov : t.length + 1 ≤ 1024) :
    Run code s0
      ⟨pc + ⟨1⟩, uInt256OfByteArray (s0.executionEnv.calldata.readBytes a.toNat 32) :: t,
        mem, aw, rdata, w⟩ (k + 1) (C + 3) :=
  h.step (fun s hc _ hcur =>
      calldataload_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stCalldataload)

theorem Run.caller (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.CALLER, .none)) (hov : stk.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.ofNat s0.executionEnv.source.val :: stk, mem, aw, rdata, w⟩
      (k + 1) (C + 2) :=
  h.step (fun s hc _ hcur => caller_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stCaller)

theorem Run.address (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.ADDRESS, .none)) (hov : stk.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.ofNat s0.executionEnv.codeOwner.val :: stk, mem, aw, rdata, w⟩
      (k + 1) (C + 2) :=
  h.step (fun s hc _ hcur => address_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stAddress)

theorem Run.codesize (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.CODESIZE, .none)) (hov : stk.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.ofNat code.size :: stk, mem, aw, rdata, w⟩ (k + 1) (C + 2) :=
  h.step (fun s hc _ hcur => codesize_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stCodesize)

/-- `RETURNDATASIZE` pushes the size of the carried return-data buffer. -/
theorem Run.returndatasize (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.RETURNDATASIZE, .none)) (hov : stk.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, UInt256.ofNat rdata.size :: stk, mem, aw, rdata, w⟩ (k + 1) (C + 2) :=
  h.step (fun s hc _ hcur =>
      returndatasize_xstep hc (cursorOf_eq.mp hcur).1 hdec (cursorOf_eq.mp hcur).2.1 hov)
    (by trace_succ stReturndatasize)

/-- `GAS` pushes the remaining gas, which depends on the reached state: the pushed value is
    existential. -/
theorem Run.gas (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.GAS, .none)) (hov : stk.length + 1 ≤ 1024) :
    ∃ gv, Run code s0 ⟨pc + ⟨1⟩, gv :: stk, mem, aw, rdata, w⟩ (k + 1) (C + 2) := by
  rcases h with hoog | ⟨s, hX, hcode, hcur, hgas, hk, hC, hst⟩
  · exact ⟨⟨0⟩, Or.inl hoog⟩
  obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
  have st := gas_xstep hcode hpc hdec hstk hov
  refine ⟨(s.machineState.gasAvailable.subNat 2).toUInt256, ?_⟩
  by_cases gg : (budget s0).toNat < C + 2
  · exact Or.inl (hX.trans (stepOOG hgas st hk hC gg))
  · refine Or.inr ⟨stGas s, hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), hcode, ?_, ?_,
      by omega, by omega, hst⟩
    · simp [cursorOf, stGas, hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs]
    · simp only [stGas]; rw [hgas, Sat256.subNat_subNat]


/-! ## Memory instructions

The cost of a memory instruction is `memoryExpansionCost s op + base`, where the expansion part
depends only on the carried active words and the offsets on the stack.  Each combinator takes the
concrete `mcost` with a proof `hmc` (at a concrete call site the `mem_cost` macro) and the resulting
memory / active words as equations, so the successor cursor stays literal. -/

/-- `MSTORE`: pops offset `a` and value `b`, writes `b` at `mem[a]`. -/
theorem Run.mstore (mcost : ℕ) (memout : ByteArray) (awout : UInt256)
    (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.MSTORE, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: t →
        memoryExpansionCost s .MSTORE = mcost)
    (hmemout : b.toByteArray.write 0 mem a.toNat 32 = memout)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat 32) = awout)
    (hov : t.length ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, t, memout, awout, rdata, w⟩ (k + 1) (C + (mcost + 3)) :=
  h.step (fun s hc _ hcur => by
      obtain ⟨hpc, hstk, -, haw, -, -, -, -⟩ := cursorOf_eq.mp hcur
      have st := mstore_xstep hc hpc hdec hstk hov
      rw [hmc s haw hstk] at st; exact st)
    (by trace_succ stMStore [hmemout, hawout, hmc s haw hstk]) (by omega)

/-- `MLOAD`: pops offset `a`, pushes the word at `mem[a]` (resolved to `loadval`). -/
theorem Run.mload (mcost : ℕ) (loadval awout : UInt256)
    (h : Run code s0 ⟨pc, a :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.MLOAD, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: t →
        memoryExpansionCost s .MLOAD = mcost)
    (hval : (if a.toNat ≥ mem.size ∨ a ≥ aw * ⟨32⟩ then ⟨0⟩
             else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding a.toNat 32))) = loadval)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat 32) = awout)
    (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, loadval :: t, mem, awout, rdata, w⟩ (k + 1) (C + (mcost + 3)) :=
  h.step (fun s hc _ hcur => by
      obtain ⟨hpc, hstk, -, haw, -, -, -, -⟩ := cursorOf_eq.mp hcur
      have st := mload_xstep hc hpc hdec hstk hov
      rw [hmc s haw hstk] at st; exact st)
    (by intro s hcode hst hcur
        obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
        refine ⟨?_, ?_, ⟨rfl, rfl, rfl, rfl⟩⟩
        · refine cursorOf_eq.mpr ⟨?_, ?_, ?_, ?_, ?_, hcA, hσ, hlogs⟩
          · simp only [stMLoad]; rw [hpc]
          · simp only [stMLoad]; rw [hmem, haw, hval]
          · simp only [stMLoad]; exact hmem
          · simp only [stMLoad]; rw [haw, hawout]
          · exact hrdata
        · simp only [stMLoad, hmc s haw hstk, Sat256.subNat_subNat])
    (by omega)

/-- `KECCAK256`: pops offset `a` and size `b`, pushes `KEC(mem[a .. a+b])` (resolved to `kecval`). -/
theorem Run.keccak256 (mcost : ℕ) (kecval awout : UInt256)
    (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.KECCAK256, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: t →
        memoryExpansionCost s .KECCAK256 = mcost)
    (hval : UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (mem.readWithPadding a.toNat b.toNat)))
        = kecval)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length + 1 ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, kecval :: t, mem, awout, rdata, w⟩ (k + 1)
      (C + (mcost + (GasConstants.Gkeccak256 + GasConstants.Gkeccak256word * ((b.toNat + 31) / 32)))) :=
  h.step (fun s hc _ hcur => by
      obtain ⟨hpc, hstk, -, haw, -, -, -, -⟩ := cursorOf_eq.mp hcur
      have st := keccak_xstep hc hpc hdec hstk hov
      rw [hmc s haw hstk] at st; exact st)
    (by trace_succ stKeccak [hval, hawout, hmc s haw hstk])
    (by have : 1 ≤ GasConstants.Gkeccak256 := by decide
        omega)

/-- `CALLDATACOPY`: pops destination `a`, calldata offset `b` and length `c`. -/
theorem Run.calldatacopy (mcost : ℕ) (memout : ByteArray) (awout : UInt256)
    (h : Run code s0 ⟨pc, a :: b :: c :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.CALLDATACOPY, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: c :: t →
        memoryExpansionCost s .CALLDATACOPY = mcost)
    (hmemout : s0.executionEnv.calldata.write b.toNat mem a.toNat c.toNat = memout)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat c.toNat) = awout)
    (hov : t.length ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, t, memout, awout, rdata, w⟩ (k + 1)
      (C + (mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))) :=
  h.step (fun s hc _ hcur => by
      obtain ⟨hpc, hstk, -, haw, -, -, -, -⟩ := cursorOf_eq.mp hcur
      have st := calldatacopy_xstep hc hpc hdec hstk hov
      rw [hmc s haw hstk, collapse_two_stage] at st; exact st)
    (by trace_succ stCalldatacopy [hmemout, hawout, hmc s haw hstk])
    (by have : 1 ≤ GasConstants.Gverylow := by decide
        omega)

/-- `CODECOPY`: pops destination `a`, code offset `b` and length `c`. -/
theorem Run.codecopy (mcost : ℕ) (memout : ByteArray) (awout : UInt256)
    (h : Run code s0 ⟨pc, a :: b :: c :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.CODECOPY, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: c :: t →
        memoryExpansionCost s .CODECOPY = mcost)
    (hmemout : code.write b.toNat mem a.toNat c.toNat = memout)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat c.toNat) = awout)
    (hov : t.length ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, t, memout, awout, rdata, w⟩ (k + 1)
      (C + (mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))) :=
  h.step (fun s hc _ hcur => by
      obtain ⟨hpc, hstk, -, haw, -, -, -, -⟩ := cursorOf_eq.mp hcur
      have st := codecopy_xstep hc hpc hdec hstk hov
      rw [hmc s haw hstk, collapse_two_stage] at st; exact st)
    (by trace_succ stCodecopy [hmemout, hawout, hmc s haw hstk])
    (by have : 1 ≤ GasConstants.Gverylow := by decide
        omega)

/-- `RETURNDATACOPY`: pops destination `a`, return-data offset `b` and length `c`; the copied range
    must lie inside the carried return data. -/
theorem Run.returndatacopy (mcost : ℕ) (memout : ByteArray) (awout : UInt256)
    (h : Run code s0 ⟨pc, a :: b :: c :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.RETURNDATACOPY, .none))
    (hguard : b.toNat + c.toNat ≤ rdata.size)
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: c :: t →
        memoryExpansionCost s .RETURNDATACOPY = mcost)
    (hmemout : rdata.write b.toNat mem a.toNat c.toNat = memout)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat c.toNat) = awout)
    (hov : t.length ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, t, memout, awout, rdata, w⟩ (k + 1)
      (C + (mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))) :=
  h.step (fun s hc _ hcur => by
      obtain ⟨hpc, hstk, -, haw, hrdata, -, -, -⟩ := cursorOf_eq.mp hcur
      have st := returndatacopy_xstep hc hpc hdec hstk (by rw [hrdata]; omega) hov
      rw [hmc s haw hstk, collapse_two_stage] at st; exact st)
    (by trace_succ stReturndatacopy [hmemout, hawout, hmc s haw hstk])
    (by have : 1 ≤ GasConstants.Gverylow := by decide
        omega)

/-- `RETURNDATACOPY` with its cost read from the reached state (no `mem_cost` witness), for
    symbolic offsets: the counters become existential. -/
theorem Run.returndatacopyVar (h : Run code s0 ⟨pc, a :: b :: c :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.RETURNDATACOPY, .none))
    (hguard : b.toNat + c.toNat ≤ rdata.size) (hov : t.length ≤ 1024) :
    ∃ k' C', Run code s0 ⟨pc + ⟨1⟩, t, rdata.write b.toNat mem a.toNat c.toNat,
      UInt256.ofNat (MachineState.M aw.toNat a.toNat c.toNat), rdata, w⟩ k' C' :=
  h.stepVar (guard := fun s => memoryExpansionCost s .RETURNDATACOPY
      + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))
    (cost := fun s => memoryExpansionCost s .RETURNDATACOPY
      + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))
    (fun s hc _ hcur => by
      obtain ⟨hpc, hstk, -, -, hrdata, -, -, -⟩ := cursorOf_eq.mp hcur
      have st := returndatacopy_xstep hc hpc hdec hstk (by rw [hrdata]; omega) hov
      rw [collapse_two_stage] at st; exact st)
    (by intro s hcode hst hcur
        obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
        refine ⟨?_, ?_, ?_, le_refl _, ⟨rfl, rfl, rfl, rfl⟩⟩
        · simp [cursorOf, stReturndatacopy, hpc, hmem, haw, hrdata, hcA, hσ, hlogs]
        · simp only [stReturndatacopy, Sat256.subNat_subNat]
        · dsimp only
          have : 1 ≤ GasConstants.Gverylow := by decide
          omega)

/-- The idiom `RETURNDATASIZE; PUSH0; PUSH0; RETURNDATACOPY`: copy the entire return data to
    `mem[0]`. -/
theorem Run.returndatacopyFull (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hd0 : decode code pc = some (.RETURNDATASIZE, .none))
    (hd1 : decode code (pc + ⟨1⟩) = some (.PUSH0, .none))
    (hd2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.PUSH0, .none))
    (hd3 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.RETURNDATACOPY, .none))
    (hov : stk.length + 3 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩, stk,
      rdata.write 0 mem 0 (UInt256.ofNat rdata.size).toNat,
      UInt256.ofNat (MachineState.M aw.toNat 0 (UInt256.ofNat rdata.size).toNat), rdata, w⟩ k' C' :=
  h.returndatasize hd0 (by omega)
    |>.push0 hd1 (by simp only [List.length_cons]; omega)
    |>.push0 hd2 (by simp only [List.length_cons]; omega)
    |>.returndatacopyVar hd3 (by show 0 + (UInt256.ofNat rdata.size).toNat ≤ rdata.size
                                 simp only [Nat.zero_add]; exact Nat.mod_le _ _)
      (by omega)

/-- `RETURNDATACOPY` whose memory-expansion cost alone exceeds the budget: the run is out of gas. -/
theorem Run.returndatacopyOOG_error (mcost : ℕ)
    (h : Run code s0 ⟨pc, a :: b :: c :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.RETURNDATACOPY, .none))
    (hguard : b.toNat + c.toNat ≤ rdata.size)
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: c :: t →
        memoryExpansionCost s .RETURNDATACOPY = mcost)
    (hOOG : (budget s0).toNat < mcost) (hov : t.length ≤ 1024) :
    X ((budget s0).toNat + 1) (D_J code 0) s0 = .error .OutOfGass := by
  rcases h with hoog | ⟨s, hX, hcode, hcur, hgas, hk, hC, _⟩
  · exact hoog
  obtain ⟨hpc, hstk, -, haw, hrdata, -, -, -⟩ := cursorOf_eq.mp hcur
  have st := returndatacopy_xstep hcode hpc hdec hstk (by rw [hrdata]; omega) hov
  rw [hmc s haw hstk, collapse_two_stage] at st
  exact hX.trans (stepOOG hgas st hk hC (by omega))

/-- `Run.returndatacopyOOG_error` packaged as a (vacuous) `Reverted`. -/
theorem Run.returndatacopyOOG (mcost : ℕ) {o : ByteArray}
    (h : Run code s0 ⟨pc, a :: b :: c :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.RETURNDATACOPY, .none))
    (hguard : b.toNat + c.toNat ≤ rdata.size)
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: c :: t →
        memoryExpansionCost s .RETURNDATACOPY = mcost)
    (hOOG : (budget s0).toNat < mcost) (hov : t.length ≤ 1024) :
    Reverted code s0 o :=
  Or.inl (Run.returndatacopyOOG_error mcost h hdec hguard hmc hOOG hov)

/-! ### Memory instructions with the expansion cost read from the reached state

For symbolic offsets or active words, where no `mem_cost` witness can be computed: the counters
become existential (as for `SLOAD`), the cursor stays literal. -/

theorem Run.mstoreVar (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.MSTORE, .none)) (hov : t.length ≤ 1024) :
    ∃ k' C', Run code s0 ⟨pc + ⟨1⟩, t, b.toByteArray.write 0 mem a.toNat 32,
      UInt256.ofNat (MachineState.M aw.toNat a.toNat 32), rdata, w⟩ k' C' :=
  h.stepVar (guard := fun s => memoryExpansionCost s .MSTORE + 3)
    (cost := fun s => memoryExpansionCost s .MSTORE + 3)
    (fun s hc _ hcur => by
      obtain ⟨hpc, hstk, -, -, -, -, -, -⟩ := cursorOf_eq.mp hcur
      exact mstore_xstep hc hpc hdec hstk hov)
    (by intro s _ hst hcur
        obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
        refine ⟨?_, ?_, ?_, le_refl _, ⟨rfl, rfl, rfl, rfl⟩⟩
        · simp [cursorOf, stMStore, hpc, hmem, haw, hrdata, hcA, hσ, hlogs]
        · simp only [stMStore, Sat256.subNat_subNat]
        · dsimp only; omega)

theorem Run.mloadVar (h : Run code s0 ⟨pc, a :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.MLOAD, .none)) (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨pc + ⟨1⟩,
      (if a.toNat ≥ mem.size ∨ a ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding a.toNat 32))) :: t,
      mem, UInt256.ofNat (MachineState.M aw.toNat a.toNat 32), rdata, w⟩ k' C' :=
  h.stepVar (guard := fun s => memoryExpansionCost s .MLOAD + 3)
    (cost := fun s => memoryExpansionCost s .MLOAD + 3)
    (fun s hc _ hcur => by
      obtain ⟨hpc, hstk, -, -, -, -, -, -⟩ := cursorOf_eq.mp hcur
      exact mload_xstep hc hpc hdec hstk hov)
    (by intro s _ hst hcur
        obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
        refine ⟨?_, ?_, ?_, le_refl _, ⟨rfl, rfl, rfl, rfl⟩⟩
        · refine cursorOf_eq.mpr ⟨?_, ?_, ?_, ?_, hrdata, hcA, hσ, hlogs⟩
          · simp only [stMLoad]; rw [hpc]
          · simp only [stMLoad]; rw [hmem, haw]
          · simp only [stMLoad]; exact hmem
          · simp only [stMLoad]; rw [haw]
        · simp only [stMLoad, Sat256.subNat_subNat]
        · dsimp only; omega)

theorem Run.keccak256Var (h : Run code s0 ⟨pc, a :: b :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.KECCAK256, .none)) (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨pc + ⟨1⟩,
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (mem.readWithPadding a.toNat b.toNat))) :: t,
      mem, UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat), rdata, w⟩ k' C' :=
  h.stepVar (guard := fun s => memoryExpansionCost s .KECCAK256
      + (GasConstants.Gkeccak256 + GasConstants.Gkeccak256word * ((b.toNat + 31) / 32)))
    (cost := fun s => memoryExpansionCost s .KECCAK256
      + (GasConstants.Gkeccak256 + GasConstants.Gkeccak256word * ((b.toNat + 31) / 32)))
    (fun s hc _ hcur => by
      obtain ⟨hpc, hstk, -, -, -, -, -, -⟩ := cursorOf_eq.mp hcur
      exact keccak_xstep hc hpc hdec hstk hov)
    (by intro s _ hst hcur
        obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
        refine ⟨?_, ?_, ?_, le_refl _, ⟨rfl, rfl, rfl, rfl⟩⟩
        · simp [cursorOf, stKeccak, hpc, hmem, haw, hrdata, hcA, hσ, hlogs]
        · simp only [stKeccak, Sat256.subNat_subNat]
        · dsimp only
          have : 1 ≤ GasConstants.Gkeccak256 := by decide
          omega)

/-! ## Logs

`LOGn` appends `⟨codeOwner, topics, mem[offset .. offset+size]⟩` to the world's log series.
Requires `perm` (aborts in static mode). -/

theorem Run.log1 (mcost : ℕ) (awout : UInt256)
    (h : Run code s0 ⟨pc, a :: b :: c :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.LOG1, .none)) (hperm : s0.executionEnv.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: c :: t →
        memoryExpansionCost s .LOG1 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, t, mem, awout, rdata,
        { w with logs := w.logs.push ⟨s0.executionEnv.codeOwner, #[c],
                                        mem.readWithPadding a.toNat b.toNat⟩ }⟩
      (k + 1) (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + GasConstants.Glogtopic))) :=
  h.step (fun s hc hst hcur => by
      obtain ⟨hpc, hstk, -, haw, -, -, -, -⟩ := cursorOf_eq.mp hcur
      have st := log1_xstep hc hpc hdec (by rw [hst.1]; exact hperm) hstk hov
      rw [hmc s haw hstk] at st; exact st)
    (by trace_succ stLog1 [hawout, hmc s haw hstk])
    (by have : 1 ≤ GasConstants.Glog := by decide
        omega)

theorem Run.log3 (mcost : ℕ) (awout : UInt256)
    (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.LOG3, .none)) (hperm : s0.executionEnv.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: e :: t → memoryExpansionCost s .LOG3 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, t, mem, awout, rdata,
        { w with logs := w.logs.push ⟨s0.executionEnv.codeOwner, #[c, d, e],
                                        mem.readWithPadding a.toNat b.toNat⟩ }⟩
      (k + 1) (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 3 * GasConstants.Glogtopic))) :=
  h.step (fun s hc hst hcur => by
      obtain ⟨hpc, hstk, -, haw, -, -, -, -⟩ := cursorOf_eq.mp hcur
      have st := log3_xstep hc hpc hdec (by rw [hst.1]; exact hperm) hstk hov
      rw [hmc s haw hstk] at st; exact st)
    (by trace_succ stLog3 [hawout, hmc s haw hstk])
    (by have : 1 ≤ GasConstants.Glog := by decide
        omega)

theorem Run.log4 (mcost : ℕ) (awout : UInt256)
    (h : Run code s0 ⟨pc, a :: b :: c :: d :: e :: f :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.LOG4, .none)) (hperm : s0.executionEnv.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: e :: f :: t → memoryExpansionCost s .LOG4 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    Run code s0 ⟨pc + ⟨1⟩, t, mem, awout, rdata,
        { w with logs := w.logs.push ⟨s0.executionEnv.codeOwner, #[c, d, e, f],
                                        mem.readWithPadding a.toNat b.toNat⟩ }⟩
      (k + 1) (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 4 * GasConstants.Glogtopic))) :=
  h.step (fun s hc hst hcur => by
      obtain ⟨hpc, hstk, -, haw, -, -, -, -⟩ := cursorOf_eq.mp hcur
      have st := log4_xstep hc hpc hdec (by rw [hst.1]; exact hperm) hstk hov
      rw [hmc s haw hstk] at st; exact st)
    (by trace_succ stLog4 [hawout, hmc s haw hstk])
    (by have : 1 ≤ GasConstants.Glog := by decide
        omega)

/-! ## Storage and account reads (cost read from the reached state) -/

private theorem stSStore_logSeries (s : State) (slot val : UInt256) (t : List UInt256) :
    (stSStore s slot val t).substate.logSeries = s.substate.logSeries := by
  simp only [stSStore]
  cases s.accountMap.find? s.executionEnv.codeOwner <;> rfl

/-- `SSTORE`: writes `val` to `slot` of the executing account.  Requires `perm`. -/
theorem Run.sstore {slot val : UInt256}
    (h : Run code s0 ⟨pc, slot :: val :: t, mem, aw, rdata, w⟩ k C)
    (hperm : s0.executionEnv.perm = true) (hdec : decode code pc = some (.SSTORE, .none))
    (hov : t.length ≤ 1024) :
    ∃ k' C', Run code s0 ⟨pc + ⟨1⟩, t, mem, aw, rdata,
      { w with accounts := sstoreAccountMap s0.executionEnv.codeOwner w.accounts slot val }⟩ k' C' :=
  h.stepVar (guard := fun s => max (Csstore s) (GasConstants.Gcallstipend + 1)) (cost := Csstore)
    (fun s hc hst hcur => by
      obtain ⟨hpc, hstk, -, -, -, -, -, -⟩ := cursorOf_eq.mp hcur
      exact sstore_xstep hc hpc hdec (by rw [hst.1]; exact hperm) hstk hov)
    (by intro s _ hst hcur
        obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
        refine ⟨cursorOf_eq.mpr ⟨?_, ?_, ?_, ?_, hrdata, ?_, ?_, ?_⟩, stSStore_gas s slot val t,
          Theory.Csstore_pos s, le_max_left _ _, stSStore_executionEnv s slot val t, rfl, rfl, rfl⟩
        · rw [stSStore_pc, hpc]
        · exact stSStore_stack s slot val t
        · rw [stSStore_memory]; exact hmem
        · rw [stSStore_activeWords]; exact haw
        · rw [stSStore_createdAccounts]; exact hcA
        · rw [stSStore_accountMap, hσ, hst.1]
        · rw [stSStore_logSeries]; exact hlogs)

/-- `SLOAD`: pops `a`, pushes `storage[codeOwner][a]` read from the carried accounts. -/
theorem Run.sload (h : Run code s0 ⟨pc, a :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.SLOAD, .none)) (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨pc + ⟨1⟩,
      (w.accounts.find? s0.executionEnv.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD a ⟨0⟩))
        :: t, mem, aw, rdata, w⟩ k' C' :=
  h.stepVar (guard := fun s => Csload (a :: t) s.substate s.executionEnv)
    (cost := fun s => Csload (a :: t) s.substate s.executionEnv)
    (fun s hc _ hcur => by
      obtain ⟨hpc, hstk, -, -, -, -, -, -⟩ := cursorOf_eq.mp hcur
      exact sload_xstep hc hpc hdec hstk hov)
    (by intro s _ hst hcur
        obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
        refine ⟨?_, rfl, ?_, le_refl _, ⟨rfl, rfl, rfl, rfl⟩⟩
        · simp [cursorOf, stSload, hpc, hmem, haw, hrdata, hcA, hσ, hlogs, hst.1]
        · dsimp only; unfold Csload; split <;> decide)

/-- `EXTCODESIZE`: pops `target`, pushes its code size read from the carried accounts. -/
theorem Run.extcodesize {target : UInt256}
    (h : Run code s0 ⟨pc, target :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.EXTCODESIZE, .none)) (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨pc + ⟨1⟩, extCodeSizeWord w.accounts target :: t, mem, aw, rdata, w⟩ k' C' :=
  h.stepVar (guard := fun s => Caccess (AccountAddress.ofUInt256 target) s.substate)
    (cost := fun s => Caccess (AccountAddress.ofUInt256 target) s.substate)
    (fun s hc _ hcur => by
      obtain ⟨hpc, hstk, -, -, -, -, -, -⟩ := cursorOf_eq.mp hcur
      exact extcodesize_xstep hc hpc hdec hstk hov)
    (by intro s _ hst hcur
        obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
        refine ⟨?_, rfl, ?_, le_refl _, ⟨rfl, rfl, rfl, rfl⟩⟩
        · simp [cursorOf, stExtcodesize, hpc, hmem, haw, hrdata, hcA, hσ, hlogs]
        · dsimp only; unfold Caccess; split <;> decide)

/-! ## Selector dispatch

A solc dispatcher is a chain of arms `DUP1; PUSH4 selᵢ; EQ; PUSHk tgtᵢ; JUMPI` (or, for large
contracts, binary-search splits with `GT`).  The pc arithmetic and the bytecode-shape predicates
(`armWellFormed`, `selectorSplitWellFormed`, `nthArmPc`, …) are shared with `Reasoning.Reach`. -/

/-- Arm **taken** (`EQ ≠ 0`): jump to the matched body entry `tgt`, selector word kept. -/
theorem Run.selectorArmTaken {armPc selWord selNat tgt : UInt256} {width : ℕ}
    {op : Operation.POp} {rest : List UInt256}
    (h : Run code s0 ⟨armPc, selWord :: rest, mem, aw, rdata, w⟩ k C)
    (hdup : decode code armPc = some (.DUP1, .none))
    (hpush4 : decode code (selArmPush4Pc armPc) = some (.Push .PUSH4, some (selNat, 4)))
    (heq : decode code (selArmEqPc armPc) = some (.EQ, .none))
    (hop : op ≠ .PUSH0)
    (hpushT : decode code (selArmPushTgtPc armPc) = some (.Push op, some (tgt, width)))
    (hjumpi : decode code (selArmJumpiPc armPc width) = some (.JUMPI, .none))
    (hb : UInt256.eq selNat selWord ≠ ⟨0⟩) (hjd : (D_J code 0).contains tgt = true)
    (hov : rest.length + 3 ≤ 1024) :
    Run code s0 ⟨tgt, selWord :: rest, mem, aw, rdata, w⟩ (k + 5) (C + 22) :=
  h.dup1 hdup (by omega)
   |>.push4 selNat hpush4 (by simp only [List.length_cons]; omega)
   |>.eq heq (by simp only [List.length_cons]; omega)
   |>.pushConst tgt hop hpushT (by simp only [List.length_cons]; omega)
   |>.jumpiT hjumpi hb hjd (by simp only [List.length_cons]; omega)

/-- Arm **not taken** (`EQ = 0`): fall through to the next arm. -/
theorem Run.selectorArmNotTaken {armPc selWord selNat tgt : UInt256} {width : ℕ}
    {op : Operation.POp} {rest : List UInt256}
    (h : Run code s0 ⟨armPc, selWord :: rest, mem, aw, rdata, w⟩ k C)
    (hdup : decode code armPc = some (.DUP1, .none))
    (hpush4 : decode code (selArmPush4Pc armPc) = some (.Push .PUSH4, some (selNat, 4)))
    (heq : decode code (selArmEqPc armPc) = some (.EQ, .none))
    (hop : op ≠ .PUSH0)
    (hpushT : decode code (selArmPushTgtPc armPc) = some (.Push op, some (tgt, width)))
    (hjumpi : decode code (selArmJumpiPc armPc width) = some (.JUMPI, .none))
    (hb : UInt256.eq selNat selWord = ⟨0⟩) (hov : rest.length + 3 ≤ 1024) :
    Run code s0 ⟨selArmNextPc armPc width, selWord :: rest, mem, aw, rdata, w⟩ (k + 5) (C + 22) :=
  h.dup1 hdup (by omega)
   |>.push4 selNat hpush4 (by simp only [List.length_cons]; omega)
   |>.eq heq (by simp only [List.length_cons]; omega)
   |>.pushConst tgt hop hpushT (by simp only [List.length_cons]; omega)
   |>.jumpiNT hjumpi hb (by simp only [List.length_cons]; omega)

/-- Arm **taken**, opcode facts bundled as `armWellFormed` (selector and target read from the
    bytecode). -/
theorem Run.selectorArmTakenAuto {armPc selWord : UInt256} {rest : List UInt256}
    (h : Run code s0 ⟨armPc, selWord :: rest, mem, aw, rdata, w⟩ k C)
    (hwf : armWellFormed code armPc)
    (hb : UInt256.eq (armSelNat code armPc) selWord ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains (armTgt code armPc) = true) (hov : rest.length + 3 ≤ 1024) :
    Run code s0 ⟨armTgt code armPc, selWord :: rest, mem, aw, rdata, w⟩ (k + 5) (C + 22) := by
  obtain ⟨hdup, hpush4, heq, hopT, hpushT, hjumpi⟩ := hwf
  exact h.selectorArmTaken hdup hpush4 heq hopT hpushT hjumpi hb hjd hov

/-- Arm **not taken**, opcode facts bundled as `armWellFormed`. -/
theorem Run.selectorArmNotTakenAuto {armPc selWord : UInt256} {rest : List UInt256}
    (h : Run code s0 ⟨armPc, selWord :: rest, mem, aw, rdata, w⟩ k C)
    (hwf : armWellFormed code armPc)
    (hb : UInt256.eq (armSelNat code armPc) selWord = ⟨0⟩) (hov : rest.length + 3 ≤ 1024) :
    Run code s0 ⟨selArmNextPc armPc (armTgtWidth code armPc), selWord :: rest, mem, aw, rdata, w⟩
      (k + 5) (C + 22) := by
  obtain ⟨hdup, hpush4, heq, hopT, hpushT, hjumpi⟩ := hwf
  exact h.selectorArmNotTaken hdup hpush4 heq hopT hpushT hjumpi hb hov

/-- Width-generic arm (selector pushed with fewer than four bytes) **taken**. -/
theorem Run.selectorArmWidthTakenAuto {armPc selWord : UInt256} {rest : List UInt256}
    (selWidth : ℕ) (h : Run code s0 ⟨armPc, selWord :: rest, mem, aw, rdata, w⟩ k C)
    (hwf : armWellFormedW code armPc selWidth)
    (hb : UInt256.eq (armSelNatW code armPc) selWord ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains (armTgtW code armPc selWidth) = true)
    (hov : rest.length + 3 ≤ 1024) :
    Run code s0 ⟨armTgtW code armPc selWidth, selWord :: rest, mem, aw, rdata, w⟩ (k + 5) (C + 22) := by
  obtain ⟨hdup, hopSel, hpushSel, heq, hopT, hpushT, hjumpi⟩ := hwf
  exact h.dup1 hdup (by omega)
    |>.pushConst (armSelNatW code armPc) hopSel hpushSel (by simp only [List.length_cons]; omega)
    |>.eq heq (by simp only [List.length_cons]; omega)
    |>.pushConst (armTgtW code armPc selWidth) hopT hpushT (by simp only [List.length_cons]; omega)
    |>.jumpiT hjumpi hb hjd (by simp only [List.length_cons]; omega)

/-- Width-generic arm **not taken**. -/
theorem Run.selectorArmWidthNotTakenAuto {armPc selWord : UInt256} {rest : List UInt256}
    (selWidth : ℕ) (h : Run code s0 ⟨armPc, selWord :: rest, mem, aw, rdata, w⟩ k C)
    (hwf : armWellFormedW code armPc selWidth)
    (hb : UInt256.eq (armSelNatW code armPc) selWord = ⟨0⟩) (hov : rest.length + 3 ≤ 1024) :
    Run code s0 ⟨selArmNextPcW armPc selWidth (armTgtWidthW code armPc selWidth), selWord :: rest,
      mem, aw, rdata, w⟩ (k + 5) (C + 22) := by
  obtain ⟨hdup, hopSel, hpushSel, heq, hopT, hpushT, hjumpi⟩ := hwf
  exact h.dup1 hdup (by omega)
    |>.pushConst (armSelNatW code armPc) hopSel hpushSel (by simp only [List.length_cons]; omega)
    |>.eq heq (by simp only [List.length_cons]; omega)
    |>.pushConst (armTgtW code armPc selWidth) hopT hpushT (by simp only [List.length_cons]; omega)
    |>.jumpiNT hjumpi hb (by simp only [List.length_cons]; omega)

/-- Binary-search split **taken** (`pivot > selWord`): jump to the low-half target. -/
theorem Run.selectorSplitTaken {splitPc selWord pivot tgt : UInt256} {width : ℕ}
    {op : Operation.POp} {rest : List UInt256}
    (h : Run code s0 ⟨splitPc, selWord :: rest, mem, aw, rdata, w⟩ k C)
    (hdup : decode code splitPc = some (.DUP1, .none))
    (hpush4 : decode code (selArmPush4Pc splitPc) = some (.Push .PUSH4, some (pivot, 4)))
    (hgt : decode code (selArmEqPc splitPc) = some (.GT, .none))
    (hop : op ≠ .PUSH0)
    (hpushT : decode code (selArmPushTgtPc splitPc) = some (.Push op, some (tgt, width)))
    (hjumpi : decode code (selArmJumpiPc splitPc width) = some (.JUMPI, .none))
    (hb : UInt256.gt pivot selWord ≠ ⟨0⟩) (hjd : (D_J code 0).contains tgt = true)
    (hov : rest.length + 3 ≤ 1024) :
    Run code s0 ⟨tgt, selWord :: rest, mem, aw, rdata, w⟩ (k + 5) (C + 22) :=
  h.dup1 hdup (by omega)
   |>.push4 pivot hpush4 (by simp only [List.length_cons]; omega)
   |>.gt hgt (by simp only [List.length_cons]; omega)
   |>.pushConst tgt hop hpushT (by simp only [List.length_cons]; omega)
   |>.jumpiT hjumpi hb hjd (by simp only [List.length_cons]; omega)

/-- Binary-search split **not taken**: fall through to the high half. -/
theorem Run.selectorSplitNotTaken {splitPc selWord pivot tgt : UInt256} {width : ℕ}
    {op : Operation.POp} {rest : List UInt256}
    (h : Run code s0 ⟨splitPc, selWord :: rest, mem, aw, rdata, w⟩ k C)
    (hdup : decode code splitPc = some (.DUP1, .none))
    (hpush4 : decode code (selArmPush4Pc splitPc) = some (.Push .PUSH4, some (pivot, 4)))
    (hgt : decode code (selArmEqPc splitPc) = some (.GT, .none))
    (hop : op ≠ .PUSH0)
    (hpushT : decode code (selArmPushTgtPc splitPc) = some (.Push op, some (tgt, width)))
    (hjumpi : decode code (selArmJumpiPc splitPc width) = some (.JUMPI, .none))
    (hb : UInt256.gt pivot selWord = ⟨0⟩) (hov : rest.length + 3 ≤ 1024) :
    Run code s0 ⟨selArmNextPc splitPc width, selWord :: rest, mem, aw, rdata, w⟩ (k + 5) (C + 22) :=
  h.dup1 hdup (by omega)
   |>.push4 pivot hpush4 (by simp only [List.length_cons]; omega)
   |>.gt hgt (by simp only [List.length_cons]; omega)
   |>.pushConst tgt hop hpushT (by simp only [List.length_cons]; omega)
   |>.jumpiNT hjumpi hb (by simp only [List.length_cons]; omega)

/-- Split **taken**, opcode facts bundled as `selectorSplitWellFormed`. -/
theorem Run.selectorSplitTakenAuto {splitPc selWord : UInt256} {rest : List UInt256}
    (h : Run code s0 ⟨splitPc, selWord :: rest, mem, aw, rdata, w⟩ k C)
    (hwf : selectorSplitWellFormed code splitPc)
    (hb : UInt256.gt (armSelNat code splitPc) selWord ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains (armTgt code splitPc) = true) (hov : rest.length + 3 ≤ 1024) :
    Run code s0 ⟨armTgt code splitPc, selWord :: rest, mem, aw, rdata, w⟩ (k + 5) (C + 22) := by
  obtain ⟨hdup, hpush4, hgt, hopT, hpushT, hjumpi⟩ := hwf
  exact h.selectorSplitTaken hdup hpush4 hgt hopT hpushT hjumpi hb hjd hov

/-- Split **not taken**, opcode facts bundled as `selectorSplitWellFormed`. -/
theorem Run.selectorSplitNotTakenAuto {splitPc selWord : UInt256} {rest : List UInt256}
    (h : Run code s0 ⟨splitPc, selWord :: rest, mem, aw, rdata, w⟩ k C)
    (hwf : selectorSplitWellFormed code splitPc)
    (hb : UInt256.gt (armSelNat code splitPc) selWord = ⟨0⟩) (hov : rest.length + 3 ≤ 1024) :
    Run code s0 ⟨selArmNextPc splitPc (armTgtWidth code splitPc), selWord :: rest, mem, aw, rdata, w⟩
      (k + 5) (C + 22) := by
  obtain ⟨hdup, hpush4, hgt, hopT, hpushT, hjumpi⟩ := hwf
  exact h.selectorSplitNotTaken hdup hpush4 hgt hopT hpushT hjumpi hb hov

/-- Split **taken** with the bytecode-derived target, opcode and width resolved to literals, so the
    result carries no reducible `armTgt` projection into later `simp` steps. -/
theorem Run.selectorSplitTakenResolved {splitPc selWord tgt : UInt256} {width : ℕ}
    {op : Operation.POp} {rest : List UInt256}
    (h : Run code s0 ⟨splitPc, selWord :: rest, mem, aw, rdata, w⟩ k C)
    (hwf : selectorSplitWellFormed code splitPc)
    (hopEq : armTgtOp code splitPc = op) (htgtEq : armTgt code splitPc = tgt)
    (hwidthEq : armTgtWidth code splitPc = width)
    (hb : UInt256.gt (armSelNat code splitPc) selWord ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains tgt = true) (hov : rest.length + 3 ≤ 1024) :
    Run code s0 ⟨tgt, selWord :: rest, mem, aw, rdata, w⟩ (k + 5) (C + 22) := by
  obtain ⟨hdup, hpush4, hgt, hopT, hpushT, hjumpi⟩ := hwf
  exact h.selectorSplitTaken (pivot := armSelNat code splitPc) (tgt := tgt) (width := width)
    (op := op) hdup hpush4 hgt (by simpa [hopEq] using hopT)
    (by simpa [hopEq, htgtEq, hwidthEq] using hpushT) (by simpa [hwidthEq] using hjumpi) hb hjd hov

/-- Split **not taken** with the bytecode-derived target, opcode, width and next pc resolved. -/
theorem Run.selectorSplitNotTakenResolved {splitPc selWord tgt nextPc : UInt256} {width : ℕ}
    {op : Operation.POp} {rest : List UInt256}
    (h : Run code s0 ⟨splitPc, selWord :: rest, mem, aw, rdata, w⟩ k C)
    (hwf : selectorSplitWellFormed code splitPc)
    (hopEq : armTgtOp code splitPc = op) (htgtEq : armTgt code splitPc = tgt)
    (hwidthEq : armTgtWidth code splitPc = width) (hnextEq : selArmNextPc splitPc width = nextPc)
    (hb : UInt256.gt (armSelNat code splitPc) selWord = ⟨0⟩) (hov : rest.length + 3 ≤ 1024) :
    Run code s0 ⟨nextPc, selWord :: rest, mem, aw, rdata, w⟩ (k + 5) (C + 22) := by
  rw [← hnextEq]
  obtain ⟨hdup, hpush4, hgt, hopT, hpushT, hjumpi⟩ := hwf
  exact h.selectorSplitNotTaken (pivot := armSelNat code splitPc) (tgt := tgt) (width := width)
    (op := op) hdup hpush4 hgt (by simpa [hopEq] using hopT)
    (by simpa [hopEq, htgtEq, hwidthEq] using hpushT) (by simpa [hwidthEq] using hjumpi) hb hov

/-- **Dispatcher fold.**  From the first arm with the selector word on top, skip arms `0 … i-1`
    (none match) and take arm `i`, reaching its body entry `bodyPC`. -/
theorem Run.dispatchTo {selWord : UInt256} {rest : List UInt256} (bodyPC : UInt256) :
    ∀ (i : ℕ) {start : UInt256} {k C : ℕ}
      (_ : Run code s0 ⟨start, selWord :: rest, mem, aw, rdata, w⟩ k C)
      (_ : ∀ j, j ≤ i → armWellFormed code (nthArmPc code start j))
      (_ : ∀ j, j < i → UInt256.eq (armSelNat code (nthArmPc code start j)) selWord = ⟨0⟩)
      (_ : UInt256.eq (armSelNat code (nthArmPc code start i)) selWord ≠ ⟨0⟩)
      (_ : (D_J code 0).contains (armTgt code (nthArmPc code start i)) = true)
      (_ : armTgt code (nthArmPc code start i) = bodyPC)
      (_ : rest.length + 3 ≤ 1024),
      ∃ k' C', Run code s0 ⟨bodyPC, selWord :: rest, mem, aw, rdata, w⟩ k' C' := by
  intro i
  induction i with
  | zero =>
    intro start k C h hwf _ htake hjd hbody hov
    have hbody' : armTgt code start = bodyPC := hbody
    rw [← hbody']
    exact ⟨_, _, h.selectorArmTakenAuto (hwf 0 (le_refl 0)) htake hjd hov⟩
  | succ n ih =>
    intro start k C h hwf heq0 htake hjd hbody hov
    exact ih (h.selectorArmNotTakenAuto (hwf 0 (Nat.zero_le _)) (heq0 0 (Nat.succ_pos n)) hov)
      (fun j hj => hwf (j + 1) (by omega)) (fun j hj => heq0 (j + 1) (by omega))
      htake hjd hbody hov


/-! ## External calls

`CALL` performs the opaque message call `Θ` on the carried world and advances the cursor: the callee's
result `(cA', σ', g'', A', z, o)` is abstract (nothing is assumed about its code), the returned bytes
are written to memory and become the return-data buffer, the status flag is pushed, and the world
advances to the callee's accounts and log series.  The substate handed to `Θ` carries the cursor's
log series, so the successor's logs are exactly `A'.logSeries`.  The gas forwarded and the counters
are existential. -/

/-- The `Θ` invocation of a `CALL` from the cursor world `w`, as the EVM performs it. -/
abbrev callTheta (s0 : State) (w : World) (A_in : Substate) (target callGas value : UInt256)
    (input : ByteArray) :=
  Ethereum.EVM.Θ s0.executionEnv.blobVersionedHashes w.created s0.genesisBlockHeader s0.blocks
    w.accounts s0.σ₀ A_in (AccountAddress.ofUInt256 (UInt256.ofNat s0.executionEnv.codeOwner))
    s0.executionEnv.sender (AccountAddress.ofUInt256 target)
    (toExecute w.accounts (AccountAddress.ofUInt256 target)) callGas
    (UInt256.ofNat s0.executionEnv.gasPrice) value value input (s0.executionEnv.depth + 1)
    s0.executionEnv.header s0.executionEnv.perm

/-- The cursor after a `CALL` step: status pushed, output written at `outOffset`, return data set,
    memory grown for both the input and the output ranges, world advanced. -/
abbrev callCursor (pc : UInt256) (t : List UInt256) (mem : ByteArray) (aw : UInt256)
    (inOffset inSize outOffset outSize : UInt256) (z : Bool) (o : ByteArray) (w' : World) : Cursor :=
  ⟨pc + ⟨1⟩, (if z then ⟨1⟩ else ⟨0⟩) :: t,
    o.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat o.size)).toNat,
    UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
      outOffset.toNat outSize.toNat),
    o, w'⟩

set_option maxHeartbeats 1000000 in
/-- **`CALL`** with value `0` (the EVM invokes `Θ`; needs depth below the limit). -/
theorem Run.call {gasArg target inOffset inSize outOffset outSize : UInt256}
    (h : Run code s0 ⟨pc, gasArg :: target :: ⟨0⟩ :: inOffset :: inSize :: outOffset :: outSize :: t,
      mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.CALL, .none))
    (hdepth : s0.executionEnv.depth.val < 1024) (hov : t.length + 1 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (g'' : UInt256)
      (A_in A' : Substate) (z : Bool) (o : ByteArray) (callGas : UInt256) (k' C' : ℕ),
      A_in.logSeries = w.logs
      ∧ (cA', σ', g'', A', z, o) = callTheta s0 w A_in target callGas ⟨0⟩
          (mem.readWithPadding inOffset.toNat inSize.toNat)
      ∧ Run code s0 (callCursor pc t mem aw inOffset inSize outOffset outSize z o
          ⟨cA', σ', A'.logSeries⟩) k' C'
      ∧ o.size < UInt256.size := by
  rcases h with hoog | ⟨s, hX, hcode, hcur, hgas, hk, hC, hst⟩
  · exact ⟨_, _, _, { (default : Substate) with logSeries := w.logs }, _, _, _, ⟨0⟩, k, C, rfl, rfl,
      Or.inl hoog,
      Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)⟩
  obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
  have hee := hst.1
  have hd : decode s.executionEnv.code s.machineState.pc = some (.CALL, .none) := by
    rw [hcode, hpc]; exact hdec
  have hdepth' : s.executionEnv.depth.val < 1024 := by rw [hee]; exact hdepth
  have st := step_call s hd
  rw [hstk] at st
  have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 + 1 > 1024) = False := eq_false (by omega)
  have hstaticF : (¬ s.executionEnv.perm = true ∧ ({val := 0} : UInt256) ≠ {val := 0}) = False :=
    eq_false (by rintro ⟨_, h2⟩; exact h2 rfl)
  have hdepthLt : s.executionEnv.depth < 1024 := by rw [Fin.lt_def]; exact hdepth'
  have hbal : ∀ y : UInt256, (({val := 0} : UInt256) ≤ y) = True := fun y => eq_true (Fin.zero_le _)
  have hgtF : ∀ y : UInt256, (({val := 0} : UInt256) > y) = False :=
    fun y => eq_false (Fin.not_lt_zero _)
  have hdeqF : (s.executionEnv.depth == 1024) = false := by
    rw [beq_eq_false_iff_ne]; intro hh; rw [hh] at hdepth'; exact absurd hdepth' (by decide)
  simp only [List.length_cons, hovF, hstaticF, if_false, hdepthLt, hbal, hgtF, hdeqF,
    and_true, if_true, Bool.or_false] at st
  rw [collapse_two_stage, hcode] at st
  have hfuel : (budget s0).toNat + 1 - k = ((budget s0).toNat - k) + 1 := by omega
  have hXP := hX.trans (hfuel.symm ▸ X_peel (f := (budget s0).toNat - k) st)
  split at hXP
  · exact ⟨_, _, _, { (default : Substate) with logSeries := w.logs }, _, _, _, ⟨0⟩, k, C, rfl, rfl,
      Or.inl hXP,
      Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)⟩
  · rename_i hP
    set mc := memoryExpansionCost s Operation.CALL with hmc
    set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) { val := 0 }
      gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate
      with hgc
    set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) { val := 0 }
      gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack,
        execLength := s.machineState.execLength + 1,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate
      with hG
    set cg := UInt256.ofNat G with hcg
    set θs := Θ s.executionEnv.blobVersionedHashes s.createdAccounts s.genesisBlockHeader s.blocks
      s.accountMap s.σ₀ (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
      (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner)) s.executionEnv.sender
      (AccountAddress.ofUInt256 target) (toExecute s.accountMap (AccountAddress.ofUInt256 target))
      cg (UInt256.ofNat s.executionEnv.gasPrice) { val := 0 } { val := 0 }
      (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat) (s.executionEnv.depth + 1)
      s.executionEnv.header s.executionEnv.perm with hθs
    set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - θs.2.2.1.toNat) with hgv
    have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
    have hmcle : mc ≤ s.machineState.gasAvailable.toNat := by omega
    have hretle : θs.2.2.1.toNat ≤ cg.toNat := by
      rw [hθs]
      exact Theta_returnedGas_le s.executionEnv.blobVersionedHashes s.createdAccounts
        s.genesisBlockHeader s.blocks s.accountMap s.σ₀
        (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
        (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner)) s.executionEnv.sender
        (AccountAddress.ofUInt256 target) (toExecute s.accountMap (AccountAddress.ofUInt256 target))
        cg (UInt256.ofNat s.executionEnv.gasPrice) { val := 0 } { val := 0 }
        (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (s.executionEnv.depth + 1) s.executionEnv.header s.executionEnv.perm
    have hcgle : cg.toNat ≤ G := by
      have h : cg.toNat = G % UInt256.size := by rw [hcg]; rfl
      rw [h]; exact Nat.mod_le _ _
    have hgcG : gc = G + Cextra (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        { val := 0 } s.accountMap s.substate := by rw [hgc, hG]; rfl
    have hce1 : 1 ≤ Cextra (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        { val := 0 } s.accountMap s.substate := by
      have hcacc : 1 ≤ Caccess (AccountAddress.ofUInt256 target) s.substate := by
        unfold Caccess; split <;> decide
      unfold Cextra; omega
    have hgasN : s.machineState.gasAvailable.toNat = (budget s0).toNat - C := by
      rw [hgas, Sat256.subNat_toNat]
    set callCharge := mc + (gc - θs.2.2.1.toNat) with hcallCharge
    have hcallChargePos : 1 ≤ callCharge := by rw [hcallCharge]; omega
    have hcallChargeLeGas : callCharge ≤ s.machineState.gasAvailable.toNat := by
      rw [hcallCharge]
      have hdeltaLe : gc - θs.2.2.1.toNat ≤ gc := Nat.sub_le _ _
      omega
    have hCcallCharge : C + callCharge ≤ (budget s0).toNat := by
      rw [hgasN] at hcallChargeLeGas; omega
    have hgvGas : gv = (budget s0).subNat (C + callCharge) := by
      rw [hgv, hgas, hcallCharge, Sat256.subNat_subNat, Sat256.subNat_subNat]
    rw [show (budget s0).toNat - k = (budget s0).toNat + 1 - (k + 1) from by omega] at hXP
    refine ⟨θs.1, θs.2.1, θs.2.2.1, (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate,
      θs.2.2.2.1, θs.2.2.2.2.1, θs.2.2.2.2.2, cg, k + 1, C + callCharge, hlogs, ?_, ?_, ?_⟩
    · -- Θ-link: rewrite the world/env fields to the reached state's, then tuple-eta
      show _ = Θ s0.executionEnv.blobVersionedHashes w.created s0.genesisBlockHeader s0.blocks
        w.accounts s0.σ₀ _ _ _ _ _ _ _ _ _ _ _ _ _
      rw [← hee, ← hcA, ← hσ, ← hmem, ← hst.2.1, ← hst.2.2.1, ← hst.2.2.2, ← hθs]
    · refine Or.inr ⟨_, hXP, hcode, cursorOf_eq.mpr ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩, ?_, ?_,
        hCcallCharge, hst⟩
      · rw [hpc]
      · cases θs.2.2.2.2.1 <;> rfl
      · rw [hmem]
      · rw [haw]
      · exact hgvGas
      · omega
    · rw [hθs]
      exact Ethereum.EVM.theta_projection_output_size_lt_uint256
        s.executionEnv.blobVersionedHashes s.createdAccounts s.genesisBlockHeader s.blocks
        s.accountMap s.σ₀ (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
        (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner))
        s.executionEnv.sender (AccountAddress.ofUInt256 target)
        (toExecute s.accountMap (AccountAddress.ofUInt256 target))
        (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        cg (UInt256.ofNat s.executionEnv.gasPrice) { val := 0 } { val := 0 }
        (s.executionEnv.depth + 1) s.executionEnv.header s.executionEnv.perm
        (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)

set_option maxHeartbeats 1000000 in
/-- **`CALL`** with an arbitrary value, call-made branch: not static, enough balance, depth below
    the limit. -/
theorem Run.callValueMade {gasArg target valueWord inOffset inSize outOffset outSize : UInt256}
    (h : Run code s0
      ⟨pc, gasArg :: target :: valueWord :: inOffset :: inSize :: outOffset :: outSize :: t,
        mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.CALL, .none)) (hperm : s0.executionEnv.perm = true)
    (hbalance : valueWord ≤ (w.accounts.find? s0.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : s0.executionEnv.depth.val < 1024) (hov : t.length + 1 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (g'' : UInt256)
      (A_in A' : Substate) (z : Bool) (o : ByteArray) (callGas : UInt256) (k' C' : ℕ),
      A_in.logSeries = w.logs
      ∧ (cA', σ', g'', A', z, o) = callTheta s0 w A_in target callGas valueWord
          (mem.readWithPadding inOffset.toNat inSize.toNat)
      ∧ Run code s0 (callCursor pc t mem aw inOffset inSize outOffset outSize z o
          ⟨cA', σ', A'.logSeries⟩) k' C'
      ∧ o.size < UInt256.size := by
  rcases h with hoog | ⟨s, hX, hcode, hcur, hgas, hk, hC, hst⟩
  · exact ⟨_, _, _, { (default : Substate) with logSeries := w.logs }, _, _, _, ⟨0⟩, k, C, rfl, rfl,
      Or.inl hoog,
      Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)⟩
  obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
  have hee := hst.1
  have hd : decode s.executionEnv.code s.machineState.pc = some (.CALL, .none) := by
    rw [hcode, hpc]; exact hdec
  have hperm' : s.executionEnv.perm = true := by rw [hee]; exact hperm
  have hdepth' : s.executionEnv.depth.val < 1024 := by rw [hee]; exact hdepth
  have st := step_call s hd
  rw [hstk] at st
  have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 + 1 > 1024) = False := eq_false (by omega)
  have hstaticF : (¬ s.executionEnv.perm = true ∧ valueWord ≠ { val := 0 }) = False := by
    rw [hperm']; exact eq_false (by simp)
  have hdepthLt : s.executionEnv.depth < 1024 := by rw [Fin.lt_def]; exact hdepth'
  have hbalT :
      (valueWord ≤ (s.accountMap.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))) = True := by
    rw [hee, hσ]; exact eq_true hbalance
  have hbalOpt :
      (valueWord ≤ Option.option ⟨0⟩ (fun x => x.balance)
          (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner)) = True := by
    rw [show Option.option ⟨0⟩ (fun x => x.balance)
        (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner) =
        (s.accountMap.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) by
      cases Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner <;> rfl]
    exact hbalT
  have hgtF :
      (valueWord > (s.accountMap.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))) = False := by
    rw [hee, hσ]
    exact eq_false (by
      intro hlt
      have hLeNat : valueWord.val.val ≤
          ((w.accounts.find? s0.executionEnv.codeOwner).elim ⟨0⟩ fun x => x.balance).val.val :=
        hbalance
      have hGtNat : ((w.accounts.find? s0.executionEnv.codeOwner).elim ⟨0⟩ fun x => x.balance).val.val
          < valueWord.val.val := hlt
      exact Nat.not_lt_of_ge hLeNat hGtNat)
  have hdeqF : (s.executionEnv.depth == 1024) = false := by
    rw [beq_eq_false_iff_ne]; intro hh; rw [hh] at hdepth'; exact absurd hdepth' (by decide)
  simp only [List.length_cons, hovF, hstaticF, if_false, hdepthLt, hbalOpt, hgtF, hdeqF,
    and_true, if_true, Bool.or_false] at st
  rw [collapse_two_stage, hcode] at st
  have hfuel : (budget s0).toNat + 1 - k = ((budget s0).toNat - k) + 1 := by omega
  have hXP := hX.trans (hfuel.symm ▸ X_peel (f := (budget s0).toNat - k) st)
  split at hXP
  · exact ⟨_, _, _, { (default : Substate) with logSeries := w.logs }, _, _, _, ⟨0⟩, k, C, rfl, rfl,
      Or.inl hXP,
      Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)⟩
  · rename_i hP
    set mc := memoryExpansionCost s Operation.CALL with hmc
    set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) valueWord
      gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate
      with hgc
    set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) valueWord
      gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack,
        execLength := s.machineState.execLength + 1,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate
      with hG
    set cg := UInt256.ofNat G with hcg
    set θs := Θ s.executionEnv.blobVersionedHashes s.createdAccounts s.genesisBlockHeader s.blocks
      s.accountMap s.σ₀ (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
      (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner)) s.executionEnv.sender
      (AccountAddress.ofUInt256 target) (toExecute s.accountMap (AccountAddress.ofUInt256 target))
      cg (UInt256.ofNat s.executionEnv.gasPrice) valueWord valueWord
      (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat) (s.executionEnv.depth + 1)
      s.executionEnv.header s.executionEnv.perm with hθs
    set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - θs.2.2.1.toNat) with hgv
    have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
    have hmcle : mc ≤ s.machineState.gasAvailable.toNat := by omega
    have hretle : θs.2.2.1.toNat ≤ cg.toNat := by
      rw [hθs]
      exact Theta_returnedGas_le s.executionEnv.blobVersionedHashes s.createdAccounts
        s.genesisBlockHeader s.blocks s.accountMap s.σ₀
        (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
        (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner)) s.executionEnv.sender
        (AccountAddress.ofUInt256 target) (toExecute s.accountMap (AccountAddress.ofUInt256 target))
        cg (UInt256.ofNat s.executionEnv.gasPrice) valueWord valueWord
        (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (s.executionEnv.depth + 1) s.executionEnv.header s.executionEnv.perm
    have hcgle : cg.toNat ≤ G := by
      have h : cg.toNat = G % UInt256.size := by rw [hcg]; rfl
      rw [h]; exact Nat.mod_le _ _
    have hGltgc : G < gc := by
      rw [hG, hgc]
      exact Ccallgas_lt_Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        valueWord gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack,
          execLength := s.machineState.execLength + 1,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return }
        s.substate
    have hgasN : s.machineState.gasAvailable.toNat = (budget s0).toNat - C := by
      rw [hgas, Sat256.subNat_toNat]
    set callCharge := mc + (gc - θs.2.2.1.toNat) with hcallCharge
    have hcallChargePos : 1 ≤ callCharge := by rw [hcallCharge]; omega
    have hcallChargeLeGas : callCharge ≤ s.machineState.gasAvailable.toNat := by
      rw [hcallCharge]
      have hdeltaLe : gc - θs.2.2.1.toNat ≤ gc := Nat.sub_le _ _
      omega
    have hCcallCharge : C + callCharge ≤ (budget s0).toNat := by
      rw [hgasN] at hcallChargeLeGas; omega
    have hgvGas : gv = (budget s0).subNat (C + callCharge) := by
      rw [hgv, hgas, hcallCharge, Sat256.subNat_subNat, Sat256.subNat_subNat]
    rw [show (budget s0).toNat - k = (budget s0).toNat + 1 - (k + 1) from by omega] at hXP
    refine ⟨θs.1, θs.2.1, θs.2.2.1, (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate,
      θs.2.2.2.1, θs.2.2.2.2.1, θs.2.2.2.2.2, cg, k + 1, C + callCharge, hlogs, ?_, ?_, ?_⟩
    · show _ = Θ s0.executionEnv.blobVersionedHashes w.created s0.genesisBlockHeader s0.blocks
        w.accounts s0.σ₀ _ _ _ _ _ _ _ _ _ _ _ _ _
      rw [← hee, ← hcA, ← hσ, ← hmem, ← hst.2.1, ← hst.2.2.1, ← hst.2.2.2, ← hθs]
    · refine Or.inr ⟨_, hXP, hcode, cursorOf_eq.mpr ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩, ?_, ?_,
        hCcallCharge, hst⟩
      · rw [hpc]
      · cases θs.2.2.2.2.1 <;> rfl
      · rw [hmem]
      · rw [haw]
      · exact hgvGas
      · omega
    · rw [hθs]
      exact Ethereum.EVM.theta_projection_output_size_lt_uint256
        s.executionEnv.blobVersionedHashes s.createdAccounts s.genesisBlockHeader s.blocks
        s.accountMap s.σ₀ (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
        (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner))
        s.executionEnv.sender (AccountAddress.ofUInt256 target)
        (toExecute s.accountMap (AccountAddress.ofUInt256 target))
        (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        cg (UInt256.ofNat s.executionEnv.gasPrice) valueWord valueWord
        (s.executionEnv.depth + 1) s.executionEnv.header s.executionEnv.perm
        (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)

/-- The cursor after a `CALL` the EVM does **not** make (insufficient balance / depth limit):
    status `0`, empty return data, memory grown as for a made call, world unchanged. -/
abbrev noCallCursor (pc : UInt256) (t : List UInt256) (mem : ByteArray) (aw : UInt256)
    (inOffset inSize outOffset outSize : UInt256) (w : World) : Cursor :=
  ⟨pc + ⟨1⟩, ⟨0⟩ :: t,
    ByteArray.empty.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat ByteArray.empty.size)).toNat,
    UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
      outOffset.toNat outSize.toNat),
    ByteArray.empty, w⟩

/-- Shared tail of the no-call-made branches: charge `mc + (gc - callgas)` and repackage. -/
theorem Run.callNoCallMade {inOffset inSize outOffset outSize : UInt256} {s s' : State}
    {mc gc G : ℕ}
    (hXP : X ((budget s0).toNat + 1) (D_J code 0) s0 = X ((budget s0).toNat - k) (D_J code 0) s')
    (hgas : s.machineState.gasAvailable = (budget s0).subNat C) (hk : k ≤ C)
    (hC : C ≤ (budget s0).toNat) (hPle : mc + gc ≤ s.machineState.gasAvailable.toNat)
    (hGltgc : G < gc) (hcode' : s'.executionEnv.code = code)
    (hcur' : cursorOf s' = noCallCursor pc t mem aw inOffset inSize outOffset outSize w)
    (hgv' : s'.machineState.gasAvailable
        = (s.machineState.gasAvailable.subNat mc).subNat (gc - (UInt256.ofNat G).toNat))
    (hst' : Static s0 s') :
    ∃ k' C', Run code s0 (noCallCursor pc t mem aw inOffset inSize outOffset outSize w) k' C' := by
  have hcgle : (UInt256.ofNat G).toNat ≤ G := by
    show G % UInt256.size ≤ G
    exact Nat.mod_le _ _
  have hgasN : s.machineState.gasAvailable.toNat = (budget s0).toNat - C := by
    rw [hgas, Sat256.subNat_toNat]
  set callCharge := mc + (gc - (UInt256.ofNat G).toNat) with hcallCharge
  have hcallChargeLeGas : callCharge ≤ s.machineState.gasAvailable.toNat := by
    rw [hcallCharge]
    have hdeltaLe : gc - (UInt256.ofNat G).toNat ≤ gc := Nat.sub_le _ _
    omega
  have hCcallCharge : C + callCharge ≤ (budget s0).toNat := by
    rw [hgasN] at hcallChargeLeGas; omega
  have hgvGas : s'.machineState.gasAvailable = (budget s0).subNat (C + callCharge) := by
    rw [hgv', hgas, hcallCharge, Sat256.subNat_subNat, Sat256.subNat_subNat]
  rw [show (budget s0).toNat - k = (budget s0).toNat + 1 - (k + 1) from by omega] at hXP
  refine ⟨k + 1, C + callCharge, Or.inr ⟨s', hXP, hcode', hcur', hgvGas, ?_, hCcallCharge, hst'⟩⟩
  show k + 1 ≤ C + callCharge
  rw [hcallCharge]; omega

set_option maxHeartbeats 1000000 in
/-- **`CALL` insufficient-balance branch** (arbitrary value): `Θ` is not invoked, status `0`. -/
theorem Run.callValueInsufficientBalance
    {gasArg target value inOffset inSize outOffset outSize : UInt256}
    (h : Run code s0 ⟨pc, gasArg :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: t,
      mem, aw, rdata, w⟩ k C)
    (hperm : s0.executionEnv.perm = true) (hdec : decode code pc = some (.CALL, .none))
    (hbalance : ¬ value ≤ (w.accounts.find? s0.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : s0.executionEnv.depth.val < 1024) (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', Run code s0 (noCallCursor pc t mem aw inOffset inSize outOffset outSize w) k' C' := by
  rcases h with hoog | ⟨s, hX, hcode, hcur, hgas, hk, hC, hst⟩
  · exact ⟨k, C, Or.inl hoog⟩
  obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
  have hee := hst.1
  have hd : decode s.executionEnv.code s.machineState.pc = some (.CALL, .none) := by
    rw [hcode, hpc]; exact hdec
  have hperm' : s.executionEnv.perm = true := by rw [hee]; exact hperm
  have hdepth' : s.executionEnv.depth.val < 1024 := by rw [hee]; exact hdepth
  have st := step_call s hd
  rw [hstk] at st
  have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 + 1 > 1024) = False := eq_false (by omega)
  have hstaticF : (¬ s.executionEnv.perm = true ∧ value ≠ ({ val := 0 } : UInt256)) = False :=
    eq_false (by rintro ⟨hp, _⟩; exact hp hperm')
  have hdepthLt : s.executionEnv.depth < 1024 := by rw [Fin.lt_def]; exact hdepth'
  have hbalOpt :
      (value ≤ Option.option ⟨0⟩ (fun x => x.balance)
          (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner)) = False := by
    rw [hee, hσ]
    rw [show Option.option ⟨0⟩ (fun x => x.balance)
        (Batteries.RBMap.find? w.accounts s0.executionEnv.codeOwner) =
        (w.accounts.find? s0.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) by
      cases Batteries.RBMap.find? w.accounts s0.executionEnv.codeOwner <;> rfl]
    exact eq_false hbalance
  have hgtT :
      (value > (s.accountMap.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))) = True := by
    rw [hee, hσ]
    exact eq_true (by
      show ((w.accounts.find? s0.executionEnv.codeOwner).elim ⟨0⟩ fun x => x.balance).val.val
        < value.val.val
      exact Nat.lt_of_not_ge hbalance)
  have hdeqF : (s.executionEnv.depth == 1024) = false := by
    rw [beq_eq_false_iff_ne]; intro hh; rw [hh] at hdepth'; exact absurd hdepth' (by decide)
  simp only [List.length_cons, hovF, hstaticF, if_false, hdepthLt, hbalOpt, hgtT, hdeqF] at st
  rw [collapse_two_stage, hcode] at st
  have hfuel : (budget s0).toNat + 1 - k = ((budget s0).toNat - k) + 1 := by omega
  have hXP := hX.trans (hfuel.symm ▸ X_peel (f := (budget s0).toNat - k) st)
  set mc := memoryExpansionCost s Operation.CALL with hmc
  set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value
    gasArg s.accountMap
    { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength,
      gasAvailable := s.machineState.gasAvailable.subNat mc,
      activeWords := s.machineState.activeWords, memory := s.machineState.memory,
      returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate
    with hgc
  set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value
    gasArg s.accountMap
    { pc := s.machineState.pc, stack := s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat mc,
      activeWords := s.machineState.activeWords, memory := s.machineState.memory,
      returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate
    with hG
  set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - (UInt256.ofNat G).toNat) with hgv
  split at hXP
  · exact ⟨k, C, Or.inl hXP⟩
  · rename_i hP
    have hGltgc : G < gc := by
      rw [hG, hgc]
      exact Ccallgas_lt_Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        value gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack,
          execLength := s.machineState.execLength + 1,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return }
        s.substate
    exact Run.callNoCallMade hXP hgas hk hC (Nat.le_of_not_lt hP) hGltgc hcode
      (cursorOf_eq.mpr ⟨by rw [hpc], rfl, by simp [hmem], by rw [haw], rfl, hcA, hσ, hlogs⟩)
      hgv hst

set_option maxHeartbeats 1000000 in
/-- **`CALL` at the call-depth limit** (arbitrary value): `Θ` is not invoked, status `0`. -/
theorem Run.callValueDepthLimit {gasArg target value inOffset inSize outOffset outSize : UInt256}
    (h : Run code s0 ⟨pc, gasArg :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: t,
      mem, aw, rdata, w⟩ k C)
    (hperm : s0.executionEnv.perm = true) (hdec : decode code pc = some (.CALL, .none))
    (hdepth : s0.executionEnv.depth = 1024) (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', Run code s0 (noCallCursor pc t mem aw inOffset inSize outOffset outSize w) k' C' := by
  rcases h with hoog | ⟨s, hX, hcode, hcur, hgas, hk, hC, hst⟩
  · exact ⟨k, C, Or.inl hoog⟩
  obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
  have hee := hst.1
  have hd : decode s.executionEnv.code s.machineState.pc = some (.CALL, .none) := by
    rw [hcode, hpc]; exact hdec
  have hperm' : s.executionEnv.perm = true := by rw [hee]; exact hperm
  have hdepth1024 : s.executionEnv.depth = 1024 := by rw [hee]; exact hdepth
  have st := step_call s hd
  rw [hstk] at st
  have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 + 1 > 1024) = False := eq_false (by omega)
  have hstaticF : (¬ s.executionEnv.perm = true ∧ value ≠ ({ val := 0 } : UInt256)) = False :=
    eq_false (by rintro ⟨hp, _⟩; exact hp hperm')
  have hdepthF : (s.executionEnv.depth < 1024) = False :=
    eq_false (by rw [hdepth1024]; exact lt_irrefl _)
  have hdeqT : (s.executionEnv.depth == 1024) = true := by rw [beq_iff_eq]; exact hdepth1024
  simp only [List.length_cons, hovF, hstaticF, if_false, hdepthF, hdeqT, and_false,
    Bool.or_true, if_true] at st
  rw [collapse_two_stage, hcode] at st
  have hfuel : (budget s0).toNat + 1 - k = ((budget s0).toNat - k) + 1 := by omega
  have hXP := hX.trans (hfuel.symm ▸ X_peel (f := (budget s0).toNat - k) st)
  set mc := memoryExpansionCost s Operation.CALL with hmc
  set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value gasArg
    s.accountMap
    { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength,
      gasAvailable := s.machineState.gasAvailable.subNat mc,
      activeWords := s.machineState.activeWords, memory := s.machineState.memory,
      returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate
    with hgc
  set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value gasArg
    s.accountMap
    { pc := s.machineState.pc, stack := s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat mc,
      activeWords := s.machineState.activeWords, memory := s.machineState.memory,
      returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate
    with hG
  set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - (UInt256.ofNat G).toNat) with hgv
  split at hXP
  · exact ⟨k, C, Or.inl hXP⟩
  · rename_i hP
    have hGltgc : G < gc := by
      rw [hG, hgc]
      exact Ccallgas_lt_Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        value gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack,
          execLength := s.machineState.execLength + 1,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return }
        s.substate
    exact Run.callNoCallMade hXP hgas hk hC (Nat.le_of_not_lt hP) hGltgc hcode
      (cursorOf_eq.mpr ⟨by rw [hpc], rfl, by rw [hmem], by rw [haw], rfl, hcA, hσ, hlogs⟩)
      hgv hst

set_option maxHeartbeats 1000000 in
/-- **`CALL` at the call-depth limit** with value `0`. -/
theorem Run.callDepthLimit {gasArg target inOffset inSize outOffset outSize : UInt256}
    (h : Run code s0 ⟨pc, gasArg :: target :: ⟨0⟩ :: inOffset :: inSize :: outOffset :: outSize :: t,
      mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.CALL, .none)) (hdepth : s0.executionEnv.depth = 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', Run code s0 (noCallCursor pc t mem aw inOffset inSize outOffset outSize w) k' C' := by
  rcases h with hoog | ⟨s, hX, hcode, hcur, hgas, hk, hC, hst⟩
  · exact ⟨k, C, Or.inl hoog⟩
  obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
  have hee := hst.1
  have hd : decode s.executionEnv.code s.machineState.pc = some (.CALL, .none) := by
    rw [hcode, hpc]; exact hdec
  have hdepth1024 : s.executionEnv.depth = 1024 := by rw [hee]; exact hdepth
  have st := step_call s hd
  rw [hstk] at st
  have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 + 1 > 1024) = False := eq_false (by omega)
  have hstaticF : (¬ s.executionEnv.perm = true ∧ ({val := 0} : UInt256) ≠ {val := 0}) = False :=
    eq_false (by rintro ⟨_, h2⟩; exact h2 rfl)
  have hdepthF : (s.executionEnv.depth < 1024) = False :=
    eq_false (by rw [hdepth1024]; exact lt_irrefl _)
  have hbal : ∀ y : UInt256, (({val := 0} : UInt256) ≤ y) = True := fun y => eq_true (Fin.zero_le _)
  have hgtF : ∀ y : UInt256, (({val := 0} : UInt256) > y) = False :=
    fun y => eq_false (Fin.not_lt_zero _)
  have hdeqT : (s.executionEnv.depth == 1024) = true := by rw [beq_iff_eq]; exact hdepth1024
  simp only [List.length_cons, hovF, hstaticF, if_false, hdepthF, hbal, hgtF, hdeqT,
    and_false, Bool.or_true, if_true] at st
  rw [collapse_two_stage, hcode] at st
  have hfuel : (budget s0).toNat + 1 - k = ((budget s0).toNat - k) + 1 := by omega
  have hXP := hX.trans (hfuel.symm ▸ X_peel (f := (budget s0).toNat - k) st)
  set mc := memoryExpansionCost s Operation.CALL with hmc
  set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) { val := 0 }
    gasArg s.accountMap
    { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength,
      gasAvailable := s.machineState.gasAvailable.subNat mc,
      activeWords := s.machineState.activeWords, memory := s.machineState.memory,
      returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate
    with hgc
  set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) { val := 0 }
    gasArg s.accountMap
    { pc := s.machineState.pc, stack := s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat mc,
      activeWords := s.machineState.activeWords, memory := s.machineState.memory,
      returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate
    with hG
  set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - (UInt256.ofNat G).toNat) with hgv
  split at hXP
  · exact ⟨k, C, Or.inl hXP⟩
  · rename_i hP
    have hGltgc : G < gc := by
      rw [hG, hgc]
      exact Ccallgas_lt_Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        { val := 0 } gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack,
          execLength := s.machineState.execLength + 1,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return }
        s.substate
    exact Run.callNoCallMade hXP hgas hk hC (Nat.le_of_not_lt hP) hGltgc hcode
      (cursorOf_eq.mpr ⟨by rw [hpc], rfl, by rw [hmem], by rw [haw], rfl, hcA, hσ, hlogs⟩)
      hgv hst

/-! ### Solidity's empty-input / no-output-copy call shape -/

/-- Rewrites a `CALL` result to Solidity's `inSize = outSize = 0` shape: empty input, memory unchanged. -/
private theorem callCursor_empty {z : Bool} {o : ByteArray} {w' : World}
    {inOffset outOffset : UInt256} :
    callCursor pc t mem aw inOffset ⟨0⟩ outOffset ⟨0⟩ z o w'
      = ⟨pc + ⟨1⟩, (if z then ⟨1⟩ else ⟨0⟩) :: t, mem,
          UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat
            (⟨0⟩ : UInt256).toNat) outOffset.toNat (⟨0⟩ : UInt256).toNat), o, w'⟩ := by
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  simp only [callCursor, hmin, byteArray_write_len_zero]

private theorem noCallCursor_empty {inOffset outOffset : UInt256} :
    noCallCursor pc t mem aw inOffset ⟨0⟩ outOffset ⟨0⟩ w
      = ⟨pc + ⟨1⟩, ⟨0⟩ :: t, mem,
          UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat
            (⟨0⟩ : UInt256).toNat) outOffset.toNat (⟨0⟩ : UInt256).toNat), ByteArray.empty, w⟩ := by
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by decide
  simp only [noCallCursor, hmin, byteArray_write_len_zero]

/-- `Run.call` for `inSize = outSize = 0`: empty input to `Θ`, memory unchanged. -/
theorem Run.callEmptyInOut {gasArg target inOffset outOffset : UInt256}
    (h : Run code s0 ⟨pc, gasArg :: target :: ⟨0⟩ :: inOffset :: ⟨0⟩ :: outOffset :: ⟨0⟩ :: t,
      mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.CALL, .none))
    (hdepth : s0.executionEnv.depth.val < 1024) (hov : t.length + 1 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (g'' : UInt256)
      (A_in A' : Substate) (z : Bool) (o : ByteArray) (callGas : UInt256) (k' C' : ℕ),
      A_in.logSeries = w.logs
      ∧ (cA', σ', g'', A', z, o) = callTheta s0 w A_in target callGas ⟨0⟩ ByteArray.empty
      ∧ Run code s0 ⟨pc + ⟨1⟩, (if z then ⟨1⟩ else ⟨0⟩) :: t, mem,
          UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat
            (⟨0⟩ : UInt256).toNat) outOffset.toNat (⟨0⟩ : UInt256).toNat), o,
          ⟨cA', σ', A'.logSeries⟩⟩ k' C'
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', g'', A_in, A', z, o, callGas, k', C', hlogs, hΘ, rd, hoSize⟩ :=
    Run.call h hdec hdepth hov
  have hcd : mem.readWithPadding inOffset.toNat (⟨0⟩ : UInt256).toNat = ByteArray.empty :=
    byteArray_readWithPadding_zero _ _
  rw [hcd] at hΘ
  rw [callCursor_empty] at rd
  exact ⟨cA', σ', g'', A_in, A', z, o, callGas, k', C', hlogs, hΘ, rd, hoSize⟩

/-- `Run.callValueMade` for `inSize = outSize = 0`. -/
theorem Run.callValueMadeEmptyInOut {gasArg target valueWord inOffset outOffset : UInt256}
    (h : Run code s0 ⟨pc, gasArg :: target :: valueWord :: inOffset :: ⟨0⟩ :: outOffset :: ⟨0⟩ :: t,
      mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.CALL, .none)) (hperm : s0.executionEnv.perm = true)
    (hbalance : valueWord ≤ (w.accounts.find? s0.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : s0.executionEnv.depth.val < 1024) (hov : t.length + 1 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (g'' : UInt256)
      (A_in A' : Substate) (z : Bool) (o : ByteArray) (callGas : UInt256) (k' C' : ℕ),
      A_in.logSeries = w.logs
      ∧ (cA', σ', g'', A', z, o) = callTheta s0 w A_in target callGas valueWord ByteArray.empty
      ∧ Run code s0 ⟨pc + ⟨1⟩, (if z then ⟨1⟩ else ⟨0⟩) :: t, mem,
          UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat
            (⟨0⟩ : UInt256).toNat) outOffset.toNat (⟨0⟩ : UInt256).toNat), o,
          ⟨cA', σ', A'.logSeries⟩⟩ k' C'
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', g'', A_in, A', z, o, callGas, k', C', hlogs, hΘ, rd, hoSize⟩ :=
    Run.callValueMade h hdec hperm hbalance hdepth hov
  have hcd : mem.readWithPadding inOffset.toNat (⟨0⟩ : UInt256).toNat = ByteArray.empty :=
    byteArray_readWithPadding_zero _ _
  rw [hcd] at hΘ
  rw [callCursor_empty] at rd
  exact ⟨cA', σ', g'', A_in, A', z, o, callGas, k', C', hlogs, hΘ, rd, hoSize⟩

/-- `Run.callValueInsufficientBalance` for `inSize = outSize = 0`. -/
theorem Run.callValueInsufficientBalanceEmptyInOut
    {gasArg target value inOffset outOffset : UInt256}
    (h : Run code s0 ⟨pc, gasArg :: target :: value :: inOffset :: ⟨0⟩ :: outOffset :: ⟨0⟩ :: t,
      mem, aw, rdata, w⟩ k C)
    (hperm : s0.executionEnv.perm = true) (hdec : decode code pc = some (.CALL, .none))
    (hbalance : ¬ value ≤ (w.accounts.find? s0.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : s0.executionEnv.depth.val < 1024) (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨pc + ⟨1⟩, ⟨0⟩ :: t, mem,
      UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat
        (⟨0⟩ : UInt256).toNat) outOffset.toNat (⟨0⟩ : UInt256).toNat), ByteArray.empty, w⟩ k' C' := by
  obtain ⟨k', C', rd⟩ := Run.callValueInsufficientBalance h hperm hdec hbalance hdepth hov
  rw [noCallCursor_empty] at rd
  exact ⟨k', C', rd⟩

/-- `Run.callValueDepthLimit` for `inSize = outSize = 0`. -/
theorem Run.callValueDepthLimitEmptyInOut {gasArg target value inOffset outOffset : UInt256}
    (h : Run code s0 ⟨pc, gasArg :: target :: value :: inOffset :: ⟨0⟩ :: outOffset :: ⟨0⟩ :: t,
      mem, aw, rdata, w⟩ k C)
    (hperm : s0.executionEnv.perm = true) (hdec : decode code pc = some (.CALL, .none))
    (hdepth : s0.executionEnv.depth = 1024) (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨pc + ⟨1⟩, ⟨0⟩ :: t, mem,
      UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat
        (⟨0⟩ : UInt256).toNat) outOffset.toNat (⟨0⟩ : UInt256).toNat), ByteArray.empty, w⟩ k' C' := by
  obtain ⟨k', C', rd⟩ := Run.callValueDepthLimit h hperm hdec hdepth hov
  rw [noCallCursor_empty] at rd
  exact ⟨k', C', rd⟩

/-- `Run.callDepthLimit` for `inSize = outSize = 0`. -/
theorem Run.callDepthLimitEmptyInOut {gasArg target inOffset outOffset : UInt256}
    (h : Run code s0 ⟨pc, gasArg :: target :: ⟨0⟩ :: inOffset :: ⟨0⟩ :: outOffset :: ⟨0⟩ :: t,
      mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.CALL, .none)) (hdepth : s0.executionEnv.depth = 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨pc + ⟨1⟩, ⟨0⟩ :: t, mem,
      UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat
        (⟨0⟩ : UInt256).toNat) outOffset.toNat (⟨0⟩ : UInt256).toNat), ByteArray.empty, w⟩ k' C' := by
  obtain ⟨k', C', rd⟩ := Run.callDepthLimit h hdec hdepth hov
  rw [noCallCursor_empty] at rd
  exact ⟨k', C', rd⟩

/-! ## Loops -/

/-- **Variant-indexed while-rule.**  A loop is described by an invariant `Inv : ℕ → α → Prop` over
    the loop-carried state `α`, the header cursor `cur a` of a state and its exit cursor `exitCur a`:
    * `hexit` — at variant `0` the guard leaves the loop, reaching `exitCur a`;
    * `hbody` — at variant `v + 1` the guard, the body and the back-jump return to the header with
      the carried state at variant `v`.
    Then the loop runs from any variant to the exit cursor of the final carried state (with
    existential counters).  Since the cursor is a function of the carried state, stack, memory,
    accounts and logs may all change per iteration. -/
theorem Run.whileLoop {α : Type} (Inv : ℕ → α → Prop) (cur exitCur : α → Cursor)
    (hexit : ∀ a, Inv 0 a → ∀ k C, Run code s0 (cur a) k C → ∃ k' C', Run code s0 (exitCur a) k' C')
    (hbody : ∀ v a, Inv (v + 1) a → ∀ k C, Run code s0 (cur a) k C →
        ∃ a' k' C', Inv v a' ∧ Run code s0 (cur a') k' C') :
    ∀ v a, Inv v a → ∀ k C, Run code s0 (cur a) k C →
      ∃ a' k' C', Inv 0 a' ∧ Run code s0 (exitCur a') k' C' := by
  intro v
  induction v with
  | zero =>
    intro a hInv k C h
    obtain ⟨k', C', h'⟩ := hexit a hInv k C h
    exact ⟨a, k', C', hInv, h'⟩
  | succ v ih =>
    intro a hInv k C h
    obtain ⟨a', k', C', hInv', h'⟩ := hbody v a hInv k C h
    exact ih a' hInv' k' C' h'

/-- **Counting loop.**  A loop whose carried state has a counter `idx` running up to `len`: the
    body advances the counter by one while `idx < len`, the exit fires once `len ≤ idx`.  An
    instance of `Run.whileLoop` with variant `len - idx`. -/
theorem Run.countingLoop {α : Type} (Inv : α → Prop) (idx : α → UInt256) (len : ℕ)
    (cur exitCur : α → Cursor)
    (hexit : ∀ a, Inv a → len ≤ (idx a).toNat → ∀ k C, Run code s0 (cur a) k C →
        ∃ k' C', Run code s0 (exitCur a) k' C')
    (hbody : ∀ a, Inv a → (idx a).toNat < len → ∀ k C, Run code s0 (cur a) k C →
        ∃ a' k' C', Inv a' ∧ (idx a').toNat = (idx a).toNat + 1 ∧ Run code s0 (cur a') k' C') :
    ∀ a, Inv a → ∀ k C, Run code s0 (cur a) k C →
      ∃ a' k' C', Inv a' ∧ len ≤ (idx a').toNat ∧ Run code s0 (exitCur a') k' C' := by
  intro a hInv k C h
  obtain ⟨a', k', C', ⟨hInv', hv⟩, h'⟩ := Run.whileLoop (fun v a => Inv a ∧ len - (idx a).toNat = v)
    cur exitCur
    (fun a ⟨hInv, hv⟩ k C h => hexit a hInv (by omega) k C h)
    (fun v a ⟨hInv, hv⟩ k C h => by
      obtain ⟨a', k', C', hInv', hidx, h'⟩ := hbody a hInv (by omega) k C h
      exact ⟨a', k', C', ⟨hInv', by omega⟩, h'⟩)
    (len - (idx a).toNat) a ⟨hInv, rfl⟩ k C h
  exact ⟨a', k', C', hInv', by omega, h'⟩

/-! ## Halting terminals

`RETURN`/`STOP` turn a cursor into `Returned` (output and final world), `REVERT` into `Reverted`
(the revert data, read from the carried memory). -/

/-- A terminal instruction whose gas check fails leaves the whole run out of gas. -/
private theorem terminalOOG {s : State} {cost : ℕ}
    {res : Except ExecutionException (State × Option (HaltCause × ByteArray))}
    (hgas : s.machineState.gasAvailable = (budget s0).subNat C)
    (hstep : Xstep (D_J code 0) s
              = if s.machineState.gasAvailable.toNat < cost then .error .OutOfGass else res)
    (hk : k ≤ C) (hC : C ≤ (budget s0).toNat) (hOOG : (budget s0).toNat < C + cost)
    (hX : X ((budget s0).toNat + 1) (D_J code 0) s0 = X ((budget s0).toNat + 1 - k) (D_J code 0) s) :
    X ((budget s0).toNat + 1) (D_J code 0) s0 = .error .OutOfGass := by
  rw [hX]
  have hgg : s.machineState.gasAvailable.toNat < cost := by
    rw [hgas, Sat256.subNat_toNat]; omega
  have hstepE : Xstep (D_J code 0) s = .error .OutOfGass := by rw [hstep, if_pos hgg]
  have hfuel : (budget s0).toNat + 1 - k = ((budget s0).toNat + 1 - (k + 1)) + 1 := by omega
  rw [hfuel]; exact Ethereum.EVM.Xstep_X_X_except _ s _ _ hstepE

/-- `RETURN`: the run returns `mem[off .. off+len]` (resolved to `oval`) with the cursor's world. -/
theorem Run.ret {off len : UInt256} (mcost : ℕ) (oval : ByteArray)
    (h : Run code s0 ⟨pc, off :: len :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.RETURN, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: len :: t →
        memoryExpansionCost s .RETURN = mcost)
    (hoval : mem.readWithPadding off.toNat len.toNat = oval) (hov : t.length ≤ 1024) :
    Returned code s0 w oval := by
  rcases h with hoog | ⟨s, hX, hcode, hcur, hgas, hk, hC, _⟩
  · exact Or.inl hoog
  obtain ⟨hpc, hstk, hmem, haw, _, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
  have st := return_xstep hcode hpc hdec hstk hov
  rw [hmc s haw hstk, show s.machineState.memory.readWithPadding off.toNat len.toNat = oval from by
    rw [hmem, hoval]] at st
  by_cases gg : (budget s0).toNat < C + mcost
  · exact Or.inl (terminalOOG hgas st hk hC gg hX)
  · exact Or.inr ⟨stReturn s off len t, hX.trans (stepHaltSuccess hgas st hk (by omega)),
      hcA, hσ, hlogs⟩

/-- `STOP`: the run returns empty output with the cursor's world. -/
theorem Run.stop (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.STOP, .none)) (hov : stk.length ≤ 1024) :
    Returned code s0 w ByteArray.empty := by
  rcases h with hoog | ⟨s, hX, hcode, hcur, hgas, hk, hC, _⟩
  · exact Or.inl hoog
  obtain ⟨hpc, hstk, _, _, _, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
  have st := stop_xstep hcode hpc hdec hstk hov
  refine Or.inr ⟨stStop s, hX.trans (stepHaltSuccess (cost := 0) hgas ?_ hk (by omega)),
    hcA, hσ, hlogs⟩
  rw [if_neg (Nat.not_lt_zero _)]; exact st

/-- `REVERT`: the run reverts with `mem[off .. off+len]` (resolved to `oval`). -/
theorem Run.rev {off len : UInt256} (mcost : ℕ) (oval : ByteArray)
    (h : Run code s0 ⟨pc, off :: len :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.REVERT, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: len :: t →
        memoryExpansionCost s .REVERT = mcost)
    (hoval : mem.readWithPadding off.toNat len.toNat = oval) (hov : t.length ≤ 1024) :
    Reverted code s0 oval := by
  rcases h with hoog | ⟨s, hX, hcode, hcur, hgas, hk, hC, _⟩
  · exact Or.inl hoog
  obtain ⟨hpc, hstk, hmem, haw, _, _, _, _⟩ := cursorOf_eq.mp hcur
  have st := revert_xstep hcode hpc hdec hstk hov
  rw [hmc s haw hstk, show s.machineState.memory.readWithPadding off.toNat len.toNat = oval from by
    rw [hmem, hoval]] at st
  by_cases gg : (budget s0).toNat < C + mcost
  · exact Or.inl (terminalOOG hgas st hk hC gg hX)
  · exact Or.inr ⟨_, hX.trans (stepHaltRevert hgas st hk (by omega))⟩

/-- `RETURN` with its expansion cost read from the reached state (symbolic offsets). -/
theorem Run.retVar {off len : UInt256}
    (h : Run code s0 ⟨pc, off :: len :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.RETURN, .none)) (hov : t.length ≤ 1024) :
    Returned code s0 w (mem.readWithPadding off.toNat len.toNat) := by
  rcases h with hoog | ⟨s, hX, hcode, hcur, hgas, hk, hC, _⟩
  · exact Or.inl hoog
  obtain ⟨hpc, hstk, hmem, _, _, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
  have st := return_xstep hcode hpc hdec hstk hov
  rw [hmem] at st
  by_cases gg : (budget s0).toNat < C + memoryExpansionCost s .RETURN
  · exact Or.inl (terminalOOG hgas st hk hC gg hX)
  · exact Or.inr ⟨stReturn s off len t, hX.trans (stepHaltSuccess hgas st hk (by omega)),
      hcA, hσ, hlogs⟩

/-- `REVERT` with its expansion cost read from the reached state (symbolic offsets). -/
theorem Run.revVar {off len : UInt256}
    (h : Run code s0 ⟨pc, off :: len :: t, mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.REVERT, .none)) (hov : t.length ≤ 1024) :
    Reverted code s0 (mem.readWithPadding off.toNat len.toNat) := by
  rcases h with hoog | ⟨s, hX, hcode, hcur, hgas, hk, hC, _⟩
  · exact Or.inl hoog
  obtain ⟨hpc, hstk, hmem, _, _, _, _, _⟩ := cursorOf_eq.mp hcur
  have st := revert_xstep hcode hpc hdec hstk hov
  rw [hmem] at st
  by_cases gg : (budget s0).toNat < C + memoryExpansionCost s .REVERT
  · exact Or.inl (terminalOOG hgas st hk hC gg hX)
  · exact Or.inr ⟨_, hX.trans (stepHaltRevert hgas st hk (by omega))⟩

/-! ## From a halted run to its `Ξ` result -/

section Xi

variable {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
  {σ σ₀ : AccountMap} {g : Sat256} {A : Substate} {I : ExecutionEnv}

private theorem Xi_error_of_X_sat {e}
    (h : X (g.toNat + 1) (D_J I.code 0) (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) = .error e) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error e :=
  Xi_error_of_X (g := g.toUInt256) (by
    simpa [Reasoning.Theory.initState, Sat256.ofUInt256, Sat256.toUInt256] using h)

private theorem Xi_revert_of_X_sat {g' o}
    (h : X (g.toNat + 1) (D_J I.code 0) (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
          = .ok (.revert g' o)) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.revert g' o) :=
  Xi_revert_of_X (g := g.toUInt256) (by
    simpa [Reasoning.Theory.initState, Sat256.ofUInt256, Sat256.toUInt256] using h)

private theorem Xi_success_of_X_sat {s' o}
    (h : X (g.toNat + 1) (D_J I.code 0) (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
          = .ok (.success s' o)) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I
      = .ok (.success (s'.createdAccounts, s'.accountMap, s'.machineState.gasAvailable.toUInt256,
                       s'.substate) o) :=
  Xi_success_of_X (g := g.toUInt256) (by
    simpa [Reasoning.Theory.initState, Sat256.ofUInt256, Sat256.toUInt256] using h)

/-- A returned run's `Ξ` result: out of gas, or success with the world's accounts and logs. -/
theorem Returned.xi {o : ByteArray} (hcode : I.code = code)
    (h : Returned code (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) w o) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass
    ∨ ∃ (g' : UInt256) (A' : Substate),
        Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (w.created, w.accounts, g', A') o)
        ∧ A'.logSeries = w.logs := by
  rcases h with hoog | ⟨s', hX, hcA, hσ, hlogs⟩
  · exact Or.inl (Xi_error_of_X_sat (by rw [← hcode] at hoog; exact hoog))
  · have hxi := Xi_success_of_X_sat (by rw [← hcode] at hX; exact hX)
    rw [hcA, hσ] at hxi
    exact Or.inr ⟨_, _, hxi, hlogs⟩

/-- A reverted run's `Ξ` result: out of gas, or a revert with exactly the data `o`. -/
theorem Reverted.xi {o : ByteArray} (hcode : I.code = code)
    (h : Reverted code (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) o) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass
    ∨ ∃ g' : UInt256, Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.revert g' o) := by
  rcases h with hoog | ⟨g', hX⟩
  · exact Or.inl (Xi_error_of_X_sat (by rw [← hcode] at hoog; exact hoog))
  · exact Or.inr ⟨g', Xi_revert_of_X_sat (by rw [← hcode] at hX; exact hX)⟩

end Xi

end Reasoning.Trace
