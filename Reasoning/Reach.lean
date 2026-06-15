import Reasoning.Stepping

/-!
# Reach — a reusable symbolic straight-line execution abstraction

`RD code ee g s0 pc stk mem aw acc k C` ("**R**eached **D**isjunction") is the
**segment invariant** the straight-line proofs carry, packaged as a single `Prop`:

> either the whole run `X (g+1) … s0` already ran out of gas, **or** there is a
> cursor state `s` reached after `k` steps / `C` gas, sitting at `pc` with stack
> `stk`, memory `mem`, active words `aw`, accounts `acc`, with `k ≤ C ≤ g`.

This is *exactly* the conclusion shape of the hand-written segment lemmas it replaced, with the
existential step/gas counters `k' C'` pulled out as explicit indices.  Each opcode becomes a
forward **implication** combinator
`RD … pc stkᵢₙ … k C → decode … → RD … (pc+1) stkₒᵤₜ … (k+1) (C+cost)`; chaining is
ordinary function application (`r.jumpdest …  |>.swap1 …`), the out-of-gas case
threads itself inside the `Prop`, and `RD.conclude` repackages the indices back into
the `∃ k' C'` form the segment lemmas state.

Design notes live in `Reasoning/REACH_PLAN.md`.  Built on `Reasoning.Theory`
(`stepContinue`/`stepOOG`, `toNat_sub_ofNat`) and `Reasoning.Stepping` (the
`st_op` successors + `<op>_xstep` lemmas).  Straight-line only; control flow stays
ordinary Lean and composes by `RD` transitivity at the call site.
-/

open Act ABI Ethereum Ethereum.EVM

namespace Reasoning.Reach

open Reasoning.Theory

set_option maxRecDepth 10000

/-- The reached-or-out-of-gas segment invariant.  `mem`/`aw`/`acc` are carried as
    absolute values (initialised at `start` to the input state's), so a relative
    preservation clause like `s'.memory = s.memory` falls out at `conclude`. -/
def RD (code : ByteArray) (ee : ExecutionEnv) (g : UInt256) (s0 : State)
    (pc : UInt256) (stk : List UInt256) (mem : ByteArray) (aw : UInt256)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  X (g.toNat + 1) (D_J code ⟨0⟩) s0 = .error .OutOfGass
  ∨ ∃ s : State,
      X (g.toNat + 1) (D_J code ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J code ⟨0⟩) s
    ∧ s.executionEnv.code = code
    ∧ s.machineState.pc = pc
    ∧ s.machineState.stack = stk
    ∧ s.machineState.gasAvailable.toNat = g.toNat - C
    ∧ k ≤ C ∧ C ≤ g.toNat
    ∧ s.machineState.memory = mem
    ∧ s.machineState.activeWords = aw
    ∧ (s.createdAccounts, s.accountMap) = acc
    ∧ s.executionEnv = ee

/-- Inject the current cursor state into the invariant.  `mem`/`aw`/`acc` are
    pinned to the input state's values; the trace's preservation clauses are then
    `= s.machineState.memory` etc. for free. -/
theorem RD.start {code : ByteArray} {g : UInt256} {s0 s : State} {k C : ℕ}
    {pc : UInt256} {stk : List UInt256}
    (hcode : s.executionEnv.code = code)
    (hpc : s.machineState.pc = pc) (hstk : s.machineState.stack = stk)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J code ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J code ⟨0⟩) s) :
    RD code s.executionEnv g s0 pc stk s.machineState.memory s.machineState.activeWords
       (s.createdAccounts, s.accountMap) k C := by
  unfold RD
  exact Or.inr ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, rfl, rfl, rfl, rfl⟩

/-- Like `start`, but the carried `mem`/`aw`/`acc` are *given* values related to the
    cursor by equations (rather than pinned to the cursor's own fields).  This is what
    re-enters the fold after an internal sub-routine call: pass the sub-call's exit
    state together with its preservation facts composed back to the original input
    (`hsub.trans horig`), so the suffix keeps carrying the original `s.memory` etc. -/
theorem RD.startWith {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 s : State} {k C : ℕ}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hcode : s.executionEnv.code = code)
    (hpc : s.machineState.pc = pc) (hstk : s.machineState.stack = stk)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J code ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J code ⟨0⟩) s)
    (hmem : s.machineState.memory = mem)
    (haw : s.machineState.activeWords = aw)
    (hacc : (s.createdAccounts, s.accountMap) = acc)
    (hee : s.executionEnv = ee) :
    RD code ee g s0 pc stk mem aw acc k C := by
  unfold RD
  exact Or.inr ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩

/-- Repackage the invariant into the `∃ k' C' s'` conclusion the segment lemmas
    state (the explicit step/gas indices become the existential witnesses). -/
theorem RD.conclude {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw acc k C) :
    X (g.toNat + 1) (D_J code ⟨0⟩) s0 = .error .OutOfGass
    ∨ ∃ (k' C' : ℕ) (s' : State),
        X (g.toNat + 1) (D_J code ⟨0⟩) s0 = X (g.toNat + 1 - k') (D_J code ⟨0⟩) s'
      ∧ s'.executionEnv.code = code ∧ s'.machineState.pc = pc
      ∧ s'.machineState.stack = stk
      ∧ s'.machineState.gasAvailable.toNat = g.toNat - C' ∧ k' ≤ C' ∧ C' ≤ g.toNat
      ∧ s'.machineState.memory = mem
      ∧ s'.machineState.activeWords = aw
      ∧ (s'.createdAccounts, s'.accountMap) = acc := by
  unfold RD at h
  rcases h with hoog | ⟨s', hX, hc, hp, hstk, hg, hkC, hCg, hm, ha, hacc, _hee⟩
  · exact Or.inl hoog
  · exact Or.inr ⟨k, C, s', hX, hc, hp, hstk, hg, hkC, hCg, hm, ha, hacc⟩

/-! ## Per-opcode combinators (continue steps)

Each rcases the incoming invariant; if it is already out-of-gas, propagate; else
re-derive the `<op>_xstep` fact about the exposed cursor `s`, split on whether the
gas suffices, and either return out-of-gas (`stepOOG`) or advance (`stepContinue`)
with a freshly-built successor.  `mem`/`aw`/`acc` ride along untouched (none of
these opcodes touch memory or accounts).

The `stSwap`-family (`SWAP*`/`DUP2-6`) and the `stBinop`-family (`EQ/LT/SLT/SHR/SUB/ADD`)
share their entire post-`rcases` body, so each is factored through one helper
(`RD.stepSwap`/`RD.stepBinop`) that takes the opcode's `Xstep` fact as a `∀`-closure
fired on the exposed cursor. -/

/-- Common tail for a cost-3, pc+1 `stSwap`-family step (`SWAP*`, `DUP2-6`). -/
theorem RD.stepSwap {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {stkIn stkOut : List UInt256}
    (h : RD code ee g s0 pc stkIn mem aw acc k C)
    (hstep : ∀ s : State, s.executionEnv.code = code → s.machineState.pc = pc →
        s.machineState.stack = stkIn →
        Xstep (D_J code ⟨0⟩) s =
          if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
          else .ok (stSwap s stkOut, .none)) :
    RD code ee g s0 (pc + ⟨1⟩) stkOut mem aw acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := hstep s hcode hpc hstk
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stSwap s stkOut,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stSwap]; exact hcode
      · simp only [stSwap]; rw [hpc]
      · rfl
      · simp only [stSwap]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stSwap]; exact hmem
      · simp only [stSwap]; exact haw
      · simp only [stSwap]; exact hacc
      · exact hee

/-- Common tail for a cost-3, pc+1 `stBinop`-family step (`EQ/LT/SLT/SHR/SUB/ADD`):
    pops two, pushes the result `res`. -/
theorem RD.stepBinop {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b res : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw acc k C)
    (hstep : ∀ s : State, s.executionEnv.code = code → s.machineState.pc = pc →
        s.machineState.stack = a :: b :: t →
        Xstep (D_J code ⟨0⟩) s =
          if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
          else .ok (stBinop s res t, .none)) :
    RD code ee g s0 (pc + ⟨1⟩) (res :: t) mem aw acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := hstep s hcode hpc hstk
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stBinop s res t,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stBinop]; exact hcode
      · simp only [stBinop]; rw [hpc]
      · rfl
      · simp only [stBinop]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stBinop]; exact hmem
      · simp only [stBinop]; exact haw
      · simp only [stBinop]; exact hacc
      · exact hee

theorem RD.jumpdest {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw acc k C)
    (hdec : decode code pc = some (.JUMPDEST, .none))
    (hov : stk.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) stk mem aw acc (k + 1) (C + 1) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := jumpdest_xstep hcode hpc hdec (by rw [hstk]; exact hov)
    by_cases gg : g.toNat < C + 1
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stJumpdest s,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stJumpdest]; exact hcode
      · simp only [stJumpdest]; rw [hpc]
      · simp only [stJumpdest]; exact hstk
      · simp only [stJumpdest]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stJumpdest]; exact hmem
      · simp only [stJumpdest]; exact haw
      · simp only [stJumpdest]; exact hacc
      · exact hee

theorem RD.push0 {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw acc k C)
    (hdec : decode code pc = some (.PUSH0, .none))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (⟨0⟩ :: stk) mem aw acc (k + 1) (C + 2) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := push0_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stPush0 s,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stPush0]; exact hcode
      · simp only [stPush0]; rw [hpc]
      · simp only [stPush0]; rw [hstk]
      · simp only [stPush0]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stPush0]; exact hmem
      · simp only [stPush0]; exact haw
      · simp only [stPush0]; exact hacc
      · exact hee

theorem RD.push1 {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw acc k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH1, some (argv, 1)))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + UInt256.ofNat 2) (argv :: stk) mem aw acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := push1_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stPush1 s argv,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stPush1]; exact hcode
      · simp only [stPush1]; rw [hpc]
      · simp only [stPush1]; rw [hstk]
      · simp only [stPush1]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stPush1]; exact hmem
      · simp only [stPush1]; exact haw
      · simp only [stPush1]; exact hacc
      · exact hee

theorem RD.push4 {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw acc k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH4, some (argv, 4)))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + UInt256.ofNat 5) (argv :: stk) mem aw acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := push4_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stPush4 s argv,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stPush4]; exact hcode
      · simp only [stPush4]; rw [hpc]
      · simp only [stPush4]; rw [hstk]
      · simp only [stPush4]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stPush4]; exact hmem
      · simp only [stPush4]; exact haw
      · simp only [stPush4]; exact hacc
      · exact hee

theorem RD.swap1 {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw acc k C)
    (hdec : decode code pc = some (.SWAP1, .none)) (hov : t.length + 2 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (b :: a :: t) mem aw acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap1_xstep hc hp hdec hs hov)

theorem RD.swap2 {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw acc k C)
    (hdec : decode code pc = some (.SWAP2, .none)) (hov : t.length + 3 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (c :: b :: a :: t) mem aw acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap2_xstep hc hp hdec hs hov)

theorem RD.swap3 {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw acc k C)
    (hdec : decode code pc = some (.SWAP3, .none)) (hov : t.length + 4 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (d :: b :: c :: a :: t) mem aw acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap3_xstep hc hp hdec hs hov)

theorem RD.dup2 {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw acc k C)
    (hdec : decode code pc = some (.DUP2, .none)) (hov : t.length + 3 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (b :: a :: b :: t) mem aw acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup2_xstep hc hp hdec hs hov)

theorem RD.dup3 {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw acc k C)
    (hdec : decode code pc = some (.DUP3, .none)) (hov : t.length + 4 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (c :: a :: b :: c :: t) mem aw acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup3_xstep hc hp hdec hs hov)

theorem RD.dup4 {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw acc k C)
    (hdec : decode code pc = some (.DUP4, .none)) (hov : t.length + 5 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (d :: a :: b :: c :: d :: t) mem aw acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup4_xstep hc hp hdec hs hov)

theorem RD.dup5 {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: t) mem aw acc k C)
    (hdec : decode code pc = some (.DUP5, .none)) (hov : t.length + 6 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (e :: a :: b :: c :: d :: e :: t) mem aw acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup5_xstep hc hp hdec hs hov)

theorem RD.dup6 {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw acc k C)
    (hdec : decode code pc = some (.DUP6, .none)) (hov : t.length + 7 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (f :: a :: b :: c :: d :: e :: f :: t) mem aw acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup6_xstep hc hp hdec hs hov)

/-- `DUP1` goes through `stDup1`, not `stSwap`, so it is its own combinator. -/
theorem RD.dup1 {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: t) mem aw acc k C)
    (hdec : decode code pc = some (.DUP1, .none)) (hov : t.length + 2 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (a :: a :: t) mem aw acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := dup1_xstep hcode hpc hdec hstk (by simp only [List.length_cons]; omega)
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stDup1 s a t,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stDup1]; exact hcode
      · simp only [stDup1]; rw [hpc]
      · rfl
      · simp only [stDup1]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stDup1]; exact hmem
      · simp only [stDup1]; exact haw
      · simp only [stDup1]; exact hacc
      · exact hee

theorem RD.pop {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: t) mem aw acc k C)
    (hdec : decode code pc = some (.POP, .none))
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem aw acc (k + 1) (C + 2) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := pop_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stPop s t,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stPop]; exact hcode
      · simp only [stPop]; rw [hpc]
      · rfl
      · simp only [stPop]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stPop]; exact hmem
      · simp only [stPop]; exact haw
      · simp only [stPop]; exact hacc
      · exact hee

/-- Internal `JUMP` to a statically-valid destination `a` (needs the
    `(D_J code 0).contains a` fact).  Sets `pc := a`, pops the target. -/
theorem RD.jump {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: t) mem aw acc k C)
    (hdec : decode code pc = some (.JUMP, .none))
    (hjd : (D_J code ⟨0⟩).contains a = true)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 a t mem aw acc (k + 1) (C + 8) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := jump_xstep hcode hpc hdec hstk hjd hov
    by_cases gg : g.toNat < C + 8
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stJump s a t,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stJump]; exact hcode
      · rfl
      · rfl
      · simp only [stJump]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stJump]; exact hmem
      · simp only [stJump]; exact haw
      · simp only [stJump]; exact hacc
      · exact hee

theorem RD.push2 {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw acc k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH2, some (argv, 2)))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + UInt256.ofNat 3) (argv :: stk) mem aw acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := push2_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stPush2 s argv,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stPush2]; exact hcode
      · simp only [stPush2]; rw [hpc]
      · simp only [stPush2]; rw [hstk]
      · simp only [stPush2]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stPush2]; exact hmem
      · simp only [stPush2]; exact haw
      · simp only [stPush2]; exact hacc
      · exact hee

theorem RD.eq {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw acc k C)
    (hdec : decode code pc = some (.EQ, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.eq a b :: t) mem aw acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => eq_xstep hc hp hdec hs hov)

theorem RD.lt {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw acc k C)
    (hdec : decode code pc = some (.LT, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.lt a b :: t) mem aw acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => lt_xstep hc hp hdec hs hov)

theorem RD.slt {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw acc k C)
    (hdec : decode code pc = some (.SLT, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.slt a b :: t) mem aw acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => slt_xstep hc hp hdec hs hov)

theorem RD.shr {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw acc k C)
    (hdec : decode code pc = some (.SHR, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.shiftRight b a :: t) mem aw acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => shr_xstep hc hp hdec hs hov)

theorem RD.sub {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw acc k C)
    (hdec : decode code pc = some (.SUB, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.sub a b :: t) mem aw acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => sub_xstep hc hp hdec hs hov)

theorem RD.add {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw acc k C)
    (hdec : decode code pc = some (.ADD, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) ((a + b) :: t) mem aw acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => add_xstep hc hp hdec hs hov)

/-- `MUL` is cost 5 (`stMul`), so it does not share the `stBinop` helper. -/
theorem RD.mul {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw acc k C)
    (hdec : decode code pc = some (.MUL, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.mul a b :: t) mem aw acc (k + 1) (C + 5) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := mul_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 5
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stMul s (UInt256.mul a b) t,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stMul]; exact hcode
      · simp only [stMul]; rw [hpc]
      · rfl
      · simp only [stMul]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stMul]; exact hmem
      · simp only [stMul]; exact haw
      · simp only [stMul]; exact hacc
      · exact hee

theorem RD.iszero {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: t) mem aw acc k C)
    (hdec : decode code pc = some (.ISZERO, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.isZero a :: t) mem aw acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := iszero_xstep hcode hpc hdec hstk (by simp only [List.length_cons]; omega)
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stIsZero s a t,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stIsZero]; exact hcode
      · simp only [stIsZero]; rw [hpc]
      · rfl
      · simp only [stIsZero]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stIsZero]; exact hmem
      · simp only [stIsZero]; exact haw
      · simp only [stIsZero]; exact hacc
      · exact hee

/-! ### Environment-reading ops (read the carried `ee`) -/

theorem RD.callvalue {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw acc k C)
    (hdec : decode code pc = some (.CALLVALUE, .none))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (ee.weiValue :: stk) mem aw acc (k + 1) (C + 2) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := callvalue_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stCallvalue s,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stCallvalue]; exact hcode
      · simp only [stCallvalue]; rw [hpc]
      · simp only [stCallvalue]; rw [hee, hstk]
      · simp only [stCallvalue]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stCallvalue]; exact hmem
      · simp only [stCallvalue]; exact haw
      · simp only [stCallvalue]; exact hacc
      · exact hee

theorem RD.calldatasize {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw acc k C)
    (hdec : decode code pc = some (.CALLDATASIZE, .none))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.ofNat ee.calldata.size :: stk) mem aw acc (k + 1) (C + 2) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := calldatasize_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stCalldatasize s,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stCalldatasize]; exact hcode
      · simp only [stCalldatasize]; rw [hpc]
      · simp only [stCalldatasize]; rw [hee, hstk]
      · simp only [stCalldatasize]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stCalldatasize]; exact hmem
      · simp only [stCalldatasize]; exact haw
      · simp only [stCalldatasize]; exact hacc
      · exact hee

theorem RD.calldataload {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: t) mem aw acc k C)
    (hdec : decode code pc = some (.CALLDATALOAD, .none))
    (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
        (uInt256OfByteArray (ee.calldata.readBytes a.toNat 32) :: t) mem aw acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := calldataload_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stCalldataload s a t,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stCalldataload]; exact hcode
      · simp only [stCalldataload]; rw [hpc]
      · simp only [stCalldataload]; rw [hee]
      · simp only [stCalldataload]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stCalldataload]; exact hmem
      · simp only [stCalldataload]; exact haw
      · simp only [stCalldataload]; exact hacc
      · exact hee

/-! ### Memory ops (dynamic cost)

`MLOAD`/`MSTORE` cost is `memoryExpansionCost s op + 3`, which depends only on the
carried `activeWords` and the offset (stack top).  The combinator takes the concrete
`mcost` plus a proof `hmc` (computed at the call site from the carried `aw` and the
literal offset) and updates `mem`/`aw` accordingly. -/

/-- `MSTORE`: pops `a` (offset), `b` (value); writes `b` at `mem[a]`, grows active words. -/
theorem RD.mstore {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256} (mcost : ℕ) (memout : ByteArray) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: t) mem aw acc k C)
    (hdec : decode code pc = some (.MSTORE, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: t →
        memoryExpansionCost s .MSTORE = mcost)
    (hmemout : b.toByteArray.write 0 mem a.toNat 32 = memout)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat 32) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t memout awout acc (k + 1) (C + (mcost + 3)) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .MSTORE = mcost := hmc s haw hstk
    have st := mstore_xstep hcode hpc hdec hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost + 3)
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stMStore s a b t,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stMStore]; exact hcode
      · simp only [stMStore]; rw [hpc]
      · rfl
      · simp only [stMStore, hmcS]
        rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega),
          toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stMStore]; rw [hmem, hmemout]
      · simp only [stMStore]; rw [haw, hawout]
      · simp only [stMStore]; exact hacc
      · exact hee

/-- `MLOAD`: pops `a` (offset), pushes the 32-byte word at `mem[a]`, grows active words. -/
theorem RD.mload {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256} (mcost : ℕ) (loadval awout : UInt256)
    (h : RD code ee g s0 pc (a :: t) mem aw acc k C)
    (hdec : decode code pc = some (.MLOAD, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: t →
        memoryExpansionCost s .MLOAD = mcost)
    (hval : (if a.toNat ≥ mem.size ∨ a ≥ aw * ⟨32⟩ then ⟨0⟩
             else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding a.toNat 32))) = loadval)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat 32) = awout)
    (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (loadval :: t) mem awout acc (k + 1) (C + (mcost + 3)) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .MLOAD = mcost := hmc s haw hstk
    have st := mload_xstep hcode hpc hdec hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost + 3)
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stMLoad s a t,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stMLoad]; exact hcode
      · simp only [stMLoad]; rw [hpc]
      · simp only [stMLoad]; rw [hmem, haw, hval]
      · simp only [stMLoad, hmcS]
        rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega),
          toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stMLoad]; rw [hmem]
      · simp only [stMLoad]; rw [haw, hawout]
      · simp only [stMLoad]; exact hacc
      · exact hee

/-- `JUMPI` **taken** (condition `b ≠ 0`) to a statically-valid destination `a`. -/
theorem RD.jumpiT {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw acc k C)
    (hdec : decode code pc = some (.JUMPI, .none))
    (hb : b ≠ ⟨0⟩)
    (hjd : (D_J code ⟨0⟩).contains a = true)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 a t mem aw acc (k + 1) (C + 10) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · have st := jumpi_t_xstep hcode hpc hdec hstk hb hjd hov
    by_cases gg : g.toNat < C + 10
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stJumpiT s a t,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stJumpiT]; exact hcode
      · rfl
      · rfl
      · simp only [stJumpiT]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stJumpiT]; exact hmem
      · simp only [stJumpiT]; exact haw
      · simp only [stJumpiT]; exact hacc
      · exact hee

/-- `JUMPI` **not taken** (condition `b = 0`): falls through to `pc+1`.  Takes the
    condition value + a proof it is `⟨0⟩` (so a symbolic condition can be resolved at
    the call site), symmetric with `jumpiT`. -/
theorem RD.jumpiNT {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw acc k C)
    (hdec : decode code pc = some (.JUMPI, .none))
    (hb : b = ⟨0⟩)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem aw acc (k + 1) (C + 10) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · rw [hb] at hstk
    have st := jumpi_nt_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 10
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stJumpiNT s t,
        hX.trans (stepContinue hgas st hk (by omega)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [stJumpiNT]; exact hcode
      · simp only [stJumpiNT]; rw [hpc]
      · rfl
      · simp only [stJumpiNT]; rw [toNat_sub_ofNat (by rw [hgas]; omega), hgas]; omega
      · simp only [stJumpiNT]; exact hmem
      · simp only [stJumpiNT]; exact haw
      · simp only [stJumpiNT]; exact hacc
      · exact hee

/-! ## Halting terminals (`RETURN` ⇒ success, `REVERT` ⇒ revert)

`RDret`/`RDrev` are the **terminal** analogues of `RD`: instead of a reached cursor, they record
that the whole run `X (g+1) … s0` has *halted* — with a success (returning bytes `o`, accounts
`acc` preserved) or a revert.  The combinators `RD.ret`/`RD.rev` step the final `RETURN`/`REVERT`
off an `RD` cursor, so a terminating segment composes in the `|>.` chain (`… |>.push0 |>.push0
|>.rev …`) instead of breaking out via `.out` + a manual halt step. -/

/-- Halting-success terminal: `X (g+1) … s0` returns the bytes `o`, preserving accounts `acc`. -/
def RDret (code : ByteArray) (g : UInt256) (s0 : State)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (o : ByteArray) : Prop :=
  X (g.toNat + 1) (D_J code ⟨0⟩) s0 = .error .OutOfGass
  ∨ ∃ s', X (g.toNat + 1) (D_J code ⟨0⟩) s0 = .ok (.success s' o)
        ∧ (s'.createdAccounts, s'.accountMap) = acc

/-- Halting-revert terminal: `X (g+1) … s0` reverts. -/
def RDrev (code : ByteArray) (g : UInt256) (s0 : State) : Prop :=
  X (g.toNat + 1) (D_J code ⟨0⟩) s0 = .error .OutOfGass
  ∨ ∃ g' o, X (g.toNat + 1) (D_J code ⟨0⟩) s0 = .ok (.revert g' o)

/-- A terminal opcode whose gas check fails leaves the whole run out of gas (shared by
    `RD.ret`/`RD.rev`).  `stepOOG` does not apply — it wants the *continue* control `.none`,
    whereas a halt step carries `.some (_, o)` — so we peel the erroring `Xstep` directly. -/
private theorem RD.terminalOOG {code : ByteArray} {g : UInt256} {s0 s : State} {k C cost : ℕ}
    {res : Except _ (State × Option (Bool × ByteArray))}
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C)
    (hstep : Xstep (D_J code ⟨0⟩) s
              = if s.machineState.gasAvailable.toNat < cost then .error .OutOfGass else res)
    (hk : k ≤ C) (hC : C ≤ g.toNat) (hOOG : g.toNat < C + cost)
    (hX : X (g.toNat + 1) (D_J code ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J code ⟨0⟩) s) :
    X (g.toNat + 1) (D_J code ⟨0⟩) s0 = .error .OutOfGass := by
  rw [hX]
  have hgg : s.machineState.gasAvailable.toNat < cost := by rw [hgas]; omega
  have hstepE : Xstep (D_J code ⟨0⟩) s = .error .OutOfGass := by rw [hstep, if_pos hgg]
  have hfuel : g.toNat + 1 - k = (g.toNat + 1 - (k + 1)) + 1 := by omega
  rw [hfuel]; exact Ethereum.EVM.Xstep_X_X_except _ s _ _ hstepE

/-- `RETURN`: terminate, returning `mem[off .. off+len]` (resolved to the literal `oval`).  Turns an
    `RD` cursor into the halting-success terminal `RDret`. -/
theorem RD.ret {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {off len : UInt256} {t : List UInt256} (mcost : ℕ) (oval : ByteArray)
    (h : RD code ee g s0 pc (off :: len :: t) mem aw acc k C)
    (hdec : decode code pc = some (.RETURN, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: len :: t →
        memoryExpansionCost s .RETURN = mcost)
    (hoval : mem.readWithPadding off.toNat len.toNat = oval)
    (hov : t.length ≤ 1024) :
    RDret code g s0 acc oval := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hacc, _hee⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .RETURN = mcost := hmc s haw hstk
    have st := return_xstep hcode hpc hdec hstk hov
    rw [hmcS, show s.machineState.memory.readWithPadding off.toNat len.toNat = oval from by
      rw [hmem, hoval]] at st
    by_cases gg : g.toNat < C + mcost
    · exact Or.inl (RD.terminalOOG hgas st hk hC gg hX)
    · exact Or.inr ⟨stReturn s off len t, hX.trans (stepHaltSuccess hgas st hk (by omega)),
        by simp only [stReturn]; exact hacc⟩

/-- `REVERT`: terminate with a revert returning `mem[off .. off+len]`.  Turns an `RD` cursor into the
    halting-revert terminal `RDrev`. -/
theorem RD.rev {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {off len : UInt256} {t : List UInt256} (mcost : ℕ)
    (h : RD code ee g s0 pc (off :: len :: t) mem aw acc k C)
    (hdec : decode code pc = some (.REVERT, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: len :: t →
        memoryExpansionCost s .REVERT = mcost)
    (hov : t.length ≤ 1024) :
    RDrev code g s0 := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, _hmem, haw, _hacc, _hee⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .REVERT = mcost := hmc s haw hstk
    have st := revert_xstep hcode hpc hdec hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + mcost
    · exact Or.inl (RD.terminalOOG hgas st hk hC gg hX)
    · exact Or.inr ⟨_, _, hX.trans (stepHaltRevert hgas st hk (by omega))⟩

/-! ## From RD terminals to Act runtime-equivalence

`RDret`/`RDrev` record that the *whole* run `X (g+1) … (initState …)` halts.  These
eliminators carry that halting fact across the `X → Ξ` bridge (`Xi_*_of_X`) and into a
`runtimeEquivalenceFor` case, folding the out-of-gas alternative into `reEquiv_outOfGas`
*once*.  A revert/success segment therefore reaches the Act layer compositionally — e.g.
`(powX_short …).reEquivNoDispatch hcode (powDispatch_none_short …)` — with no per-site
`rcases` / `Xi_*_of_X` / `reEquiv_*` plumbing.  All four are contract- and bytecode-generic
(`hcode : I.code = code` bridges the concrete bytecode back to `I.code`). -/

/-- Eliminate an `RDrev` into a `runtimeEquivalenceFor`: the OOG alternative becomes the
    `outOfGas` case automatically, and the continuation `k` receives the `Ξ`-level revert. -/
theorem RDrev.reEquivElim {cfg contract cA gh bl σ σ₀ A I} {g : UInt256} {code : ByteArray}
    (hcode : I.code = code)
    (h : RDrev code g (initState cA gh bl σ σ₀ g A I))
    (k : ∀ g' o, Ξ cA gh bl σ σ₀ g A I = .ok (.revert g' o) →
          runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g A I) :
    runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g A I := by
  rcases h with hoog | ⟨g', o, hX⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
  · exact k g' o (Xi_revert_of_X (by rw [← hcode] at hX; exact hX))

/-- `RDrev ⇒ noDispatch`: the revert with Act failing to dispatch. -/
theorem RDrev.reEquivNoDispatch {cfg contract cA gh bl σ σ₀ A I} {g : UInt256} {code : ByteArray}
    (hcode : I.code = code) (h : RDrev code g (initState cA gh bl σ σ₀ g A I))
    (hd : dispatchMsg contract I.calldata = none) :
    runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g A I :=
  h.reEquivElim hcode fun _ _ hrev => reEquiv_noDispatch hd hrev

/-- `RDrev ⇒ decodingFailed`: Act dispatches to `t` but calldata-decoding fails. -/
theorem RDrev.reEquivDecodingFailed {cfg contract cA gh bl σ σ₀ A I} {g : UInt256}
    {code : ByteArray} {t}
    (hcode : I.code = code) (h : RDrev code g (initState cA gh bl σ σ₀ g A I))
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldata (t.params.map Param.name) (transitionSignature t).paramTypes
              I.calldata = none) :
    runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g A I :=
  h.reEquivElim hcode fun _ _ hrev => reEquiv_decodingFailed hd hdec hrev

/-- Eliminate an `RDret` into a `runtimeEquivalenceFor`: the OOG alternative becomes the
    `outOfGas` case automatically; the continuation `k` receives the `Ξ`-level success, with
    accounts already projected back to the carried `(cA, σ)`. -/
theorem RDret.reEquivElim {cfg contract cA gh bl σ σ₀ A I} {g : UInt256} {code o : ByteArray}
    (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ) o)
    (k : ∀ (g' : UInt256) (A' : Substate),
          Ξ cA gh bl σ σ₀ g A I = .ok (.success (cA, σ, g', A') o) →
          runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g A I) :
    runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g A I := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
  · have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    have hxi := Xi_success_of_X (by rw [← hcode] at hX; exact hX)
    rw [hcA, hσ] at hxi
    exact k _ _ hxi

/-! ## Spike acceptance: a 2-step fold closes a fixed-pc / fixed-stack conclusion -/

/-- JUMPDEST then SWAP1, fully abstract over the bytecode (decode facts supplied as
    hypotheses).  Confirms `conclude` produces the fixed `pc`/`stack` and the carried
    `memory`/`activeWords`/accounts preservation with no leftover goals. -/
example {code : ByteArray} {g : UInt256} {s0 s : State} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = ⟨10⟩)
    (hstk : s.machineState.stack = a :: b :: t)
    (hd0 : decode code ⟨10⟩ = some (.JUMPDEST, .none))
    (hd1 : decode code (⟨10⟩ + ⟨1⟩) = some (.SWAP1, .none))
    (hov : t.length + 2 ≤ 1024)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J code ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J code ⟨0⟩) s) :
    X (g.toNat + 1) (D_J code ⟨0⟩) s0 = .error .OutOfGass
    ∨ ∃ (k' C' : ℕ) (s' : State),
        X (g.toNat + 1) (D_J code ⟨0⟩) s0 = X (g.toNat + 1 - k') (D_J code ⟨0⟩) s'
      ∧ s'.executionEnv.code = code ∧ s'.machineState.pc = ⟨10⟩ + ⟨1⟩ + ⟨1⟩
      ∧ s'.machineState.stack = b :: a :: t
      ∧ s'.machineState.gasAvailable.toNat = g.toNat - C' ∧ k' ≤ C' ∧ C' ≤ g.toNat
      ∧ s'.machineState.memory = s.machineState.memory
      ∧ s'.machineState.activeWords = s.machineState.activeWords
      ∧ (s'.createdAccounts, s'.accountMap) = (s.createdAccounts, s.accountMap) :=
  (RD.start hcode hpc hstk hgas hk hC hX
    |>.jumpdest hd0 (by simp only [List.length_cons]; omega)
    |>.swap1 hd1 (by omega)).conclude

/-! ## `evm_run` — a boilerplate-eliding chain builder

Every straight-line combinator above ends in the *same* two trailing proofs: a decode
fact (`by decide`, since on the concrete contracts the bytecode is a literal) and a
stack-depth bound (`by evm_ov`).  Writing them out on each of ~50 ops per segment is
pure noise.  `evm_run base with [op, op, …]` threads `base` through the listed
combinators left-to-right, auto-supplying both proofs:

```
exact evm_run h with [
  jumpdest, push0, dup2, swap1, pop,          -- uniform ops: ` (by decide) (by evm_ov)`
  push2 ⟨174⟩,                                -- a push carries its value, proofs still auto
  jumpiT hb hjd, jump hjd, jumpiNT hb,        -- control flow: value proofs inline, decode/ov auto
  raw routine9c hret (by evm_ov),             -- anything else: written verbatim after `raw`
  raw ret 0 oval (by decide) hmc hoval (by evm_ov) ]
```

Only `decode`/overflow are inferred; every *value* proof (`hjd`, `hb`, `hret`, memory
costs, …) is still supplied explicitly, so nothing about the proof is hidden.  Use
`raw` for any op whose argument shape is not `… (by decide) (by evm_ov)`
(`mstore`/`mload`/`ret`/`rev`/`routine*`). -/

/-- Universal stack-depth discharger: reduce concrete `length`s then `omega` (which also
    picks up a variable tail's bound from context); fall back to bare `omega`. -/
macro "evm_ov" : tactic =>
  `(tactic| first | (simp only [List.length_cons, List.length_nil]; omega) | omega)

/-- One step of an `evm_run` chain. -/
declare_syntax_cat evmStep
/-- Verbatim step: the combinator and all its arguments are written out unchanged. -/
syntax "raw " ident (term:max)* : evmStep
/-- Cooked step: combinator + value args; decode/overflow proofs are auto-supplied. -/
syntax ident (term:max)* : evmStep

syntax "evm_run " term:max " with " "[" evmStep,* "]" : term

open Lean in
macro_rules
  | `(evm_run $base:term with [ $steps,* ]) => do
      let mut acc := base
      for s in steps.getElems do
        match s with
        | `(evmStep| raw $op:ident $args*) =>
            acc ← `($(acc).$op $args*)
        | `(evmStep| $op:ident $args*) =>
            match op.getId with
            | `jump    => acc ← `($(acc).jump (by decide) $(args[0]!) (by evm_ov))
            | `jumpiT  => acc ← `($(acc).jumpiT (by decide) $(args[0]!) $(args[1]!) (by evm_ov))
            | `jumpiNT => acc ← `($(acc).jumpiNT (by decide) $(args[0]!) (by evm_ov))
            | _        => acc ← `($(acc).$op $args* (by decide) (by evm_ov))
        | _ => Macro.throwUnsupported
      return acc

end Reasoning.Reach
