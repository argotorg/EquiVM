import Reasoning.Stepping
import Reasoning.Memory

/-!
# Reach — a reusable symbolic straight-line execution abstraction

`RD code ee g s0 pc stk mem aw rdata acc k C` ("**R**eached **D**isjunction") is the
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

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Reach

open Reasoning.Theory

set_option maxRecDepth 10000

/-- The **read-only world fields** a cursor shares with the initial state `s0`: `σ₀`, the genesis
    header, and the processed blocks.  No opcode ever changes these, so every `RD` combinator
    preserves them by `rfl`.  They are not tracked for their own sake — `Θ` (the external-call
    bridge) reads them, so `RD.call` needs to recover them from the (otherwise hidden) cursor. -/
def RDWorld (s0 s : State) : Prop :=
  s.σ₀ = s0.σ₀ ∧ s.genesisBlockHeader = s0.genesisBlockHeader ∧ s.blocks = s0.blocks

/-- The reached-or-out-of-gas segment invariant.  `mem`/`aw`/`acc` are carried as
    absolute values (initialised at `start` to the input state's), so a relative
    preservation clause like `s'.memory = s.memory` falls out at `conclude`. -/
def RD (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (pc : UInt256) (stk : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass
  ∨ ∃ s : State,
      X (g.toNat + 1) (D_J code 0) s0 = X (g.toNat + 1 - k) (D_J code 0) s
    ∧ s.executionEnv.code = code
    ∧ s.machineState.pc = pc
    ∧ s.machineState.stack = stk
    ∧ s.machineState.gasAvailable = g.subNat C
    ∧ k ≤ C ∧ C ≤ g.toNat
    ∧ s.machineState.memory = mem ∧ s.machineState.activeWords = aw ∧ s.machineState.returnData = rdata
    ∧ (s.createdAccounts, s.accountMap) = acc
    ∧ s.executionEnv = ee
    ∧ RDWorld s0 s

/-- Inject the current cursor state into the invariant.  `mem`/`aw`/`acc` are
    pinned to the input state's values; the trace's preservation clauses are then
    `= s.machineState.memory` etc. for free. -/
theorem RD.start {code : ByteArray} {g : Sat256} {s0 s : State} {k C : ℕ}
    {pc : UInt256} {stk : List UInt256}
    (hcode : s.executionEnv.code = code)
    (hpc : s.machineState.pc = pc) (hstk : s.machineState.stack = stk)
    (hgas : s.machineState.gasAvailable = g.subNat C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J code 0) s0 = X (g.toNat + 1 - k) (D_J code 0) s)
    (hworld : RDWorld s0 s) :
    RD code s.executionEnv g s0 pc stk s.machineState.memory s.machineState.activeWords
       s.machineState.returnData (s.createdAccounts, s.accountMap) k C := by
  unfold RD
  exact Or.inr ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, rfl, rfl, rfl, rfl, rfl, hworld⟩

/-- Like `start`, but the carried `mem`/`aw`/`acc` are *given* values related to the
    cursor by equations (rather than pinned to the cursor's own fields).  This is what
    re-enters the fold after an internal sub-routine call: pass the sub-call's exit
    state together with its preservation facts composed back to the original input
    (`hsub.trans horig`), so the suffix keeps carrying the original `s.memory` etc. -/
theorem RD.startWith {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 s : State} {k C : ℕ}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hcode : s.executionEnv.code = code)
    (hpc : s.machineState.pc = pc) (hstk : s.machineState.stack = stk)
    (hgas : s.machineState.gasAvailable = g.subNat  C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J code 0) s0 = X (g.toNat + 1 - k) (D_J code 0) s)
    (hmem : s.machineState.memory = mem)
    (haw : s.machineState.activeWords = aw)
    (hrdata : s.machineState.returnData = rdata)
    (hacc : (s.createdAccounts, s.accountMap) = acc)
    (hee : s.executionEnv = ee) (hworld : RDWorld s0 s) :
    RD code ee g s0 pc stk mem aw rdata acc k C := by
  unfold RD
  exact Or.inr ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩

/-- Repackage the invariant into the `∃ k' C' s'` conclusion the segment lemmas
    state (the explicit step/gas indices become the existential witnesses). -/
theorem RD.conclude {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass
    ∨ ∃ (k' C' : ℕ) (s' : State),
        X (g.toNat + 1) (D_J code 0) s0 = X (g.toNat + 1 - k') (D_J code 0) s'
      ∧ s'.executionEnv.code = code ∧ s'.machineState.pc = pc
      ∧ s'.machineState.stack = stk
      ∧ s'.machineState.gasAvailable = g.subNat  C' ∧ k' ≤ C' ∧ C' ≤ g.toNat
      ∧ s'.machineState.memory = mem
      ∧ s'.machineState.activeWords = aw
      ∧ s'.machineState.returnData = rdata
      ∧ (s'.createdAccounts, s'.accountMap) = acc := by
  unfold RD at h
  rcases h with hoog | ⟨s', hX, hc, hp, hstk, hg, hkC, hCg, hm, ha, hrd, hacc, _hee, _hworld⟩
  · exact Or.inl hoog
  · exact Or.inr ⟨k, C, s', hX, hc, hp, hstk, hg, hkC, hCg, hm, ha, hrd, hacc⟩

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
theorem RD.stepSwap {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {stkIn stkOut : List UInt256}
    (h : RD code ee g s0 pc stkIn mem aw rdata acc k C)
    (hstep : ∀ s : State, s.executionEnv.code = code → s.machineState.pc = pc →
        s.machineState.stack = stkIn →
        Xstep (D_J code 0) s =
          if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
          else .ok (stSwap s stkOut, .none)) :
    RD code ee g s0 (pc + ⟨1⟩) stkOut mem aw rdata acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := hstep s hcode hpc hstk
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stSwap s stkOut,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stSwap]; exact hcode
      · simp only [stSwap]; rw [hpc]
      · rfl
      · simp only [stSwap]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stSwap]; exact hmem
      · simp only [stSwap]; exact haw
      · simp only [stSwap]; exact hrdata
      · simp only [stSwap]; exact hacc
      · exact hee
      · exact hworld

/-- Common tail for a cost-3, pc+1 `stBinop`-family step (`EQ/LT/SLT/SHR/SUB/ADD`):
    pops two, pushes the result `res`. -/
theorem RD.stepBinop {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b res : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hstep : ∀ s : State, s.executionEnv.code = code → s.machineState.pc = pc →
        s.machineState.stack = a :: b :: t →
        Xstep (D_J code 0) s =
          if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
          else .ok (stBinop s res t, .none)) :
    RD code ee g s0 (pc + ⟨1⟩) (res :: t) mem aw rdata acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := hstep s hcode hpc hstk
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stBinop s res t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stBinop]; exact hcode
      · simp only [stBinop]; rw [hpc]
      · rfl
      · simp only [stBinop]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stBinop]; exact hmem
      · simp only [stBinop]; exact haw
      · simp only [stBinop]; exact hrdata
      · simp only [stBinop]; exact hacc
      · exact hee
      · exact hworld

theorem RD.jumpdest {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.JUMPDEST, .none))
    (hov : stk.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) stk mem aw rdata acc (k + 1) (C + 1) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := jumpdest_xstep hcode hpc hdec (by rw [hstk]; exact hov)
    by_cases gg : g.toNat < C + 1
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stJumpdest s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stJumpdest]; exact hcode
      · simp only [stJumpdest]; rw [hpc]
      · simp only [stJumpdest]; exact hstk
      · simp only [stJumpdest]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stJumpdest]; exact hmem
      · simp only [stJumpdest]; exact haw
      · simp only [stJumpdest]; exact hrdata
      · simp only [stJumpdest]; exact hacc
      · exact hee
      · exact hworld

theorem RD.push0 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.PUSH0, .none))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (⟨0⟩ :: stk) mem aw rdata acc (k + 1) (C + 2) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := push0_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stPush0 s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stPush0]; exact hcode
      · simp only [stPush0]; rw [hpc]
      · simp only [stPush0]; rw [hstk]
      · simp only [stPush0]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stPush0]; exact hmem
      · simp only [stPush0]; exact haw
      · simp only [stPush0]; exact hrdata
      · simp only [stPush0]; exact hacc
      · exact hee
      · exact hworld

theorem RD.push1 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH1, some (argv, 1)))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + UInt256.ofNat 2) (argv :: stk) mem aw rdata acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := push1_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stPush1 s argv,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stPush1]; exact hcode
      · simp only [stPush1]; rw [hpc]
      · simp only [stPush1]; rw [hstk]
      · simp only [stPush1]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stPush1]; exact hmem
      · simp only [stPush1]; exact haw
      · simp only [stPush1]; exact hrdata
      · simp only [stPush1]; exact hacc
      · exact hee
      · exact hworld

theorem RD.push4 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH4, some (argv, 4)))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + UInt256.ofNat 5) (argv :: stk) mem aw rdata acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := push4_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stPush4 s argv,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stPush4]; exact hcode
      · simp only [stPush4]; rw [hpc]
      · simp only [stPush4]; rw [hstk]
      · simp only [stPush4]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stPush4]; exact hmem
      · simp only [stPush4]; exact haw
      · simp only [stPush4]; exact hrdata
      · simp only [stPush4]; exact hacc
      · exact hee
      · exact hworld

theorem RD.push20 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH20, some (argv, 20)))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + UInt256.ofNat 21) (argv :: stk) mem aw rdata acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := push20_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stPush20 s argv,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stPush20]; exact hcode
      · simp only [stPush20]; rw [hpc]
      · simp only [stPush20]; rw [hstk]
      · simp only [stPush20]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stPush20]; exact hmem
      · simp only [stPush20]; exact haw
      · simp only [stPush20]; exact hrdata
      · simp only [stPush20]; exact hacc
      · exact hee
      · exact hworld

theorem RD.swap1 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP1, .none)) (hov : t.length + 2 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (b :: a :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap1_xstep hc hp hdec hs hov)

theorem RD.swap2 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP2, .none)) (hov : t.length + 3 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (c :: b :: a :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap2_xstep hc hp hdec hs hov)

theorem RD.swap3 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP3, .none)) (hov : t.length + 4 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (d :: b :: c :: a :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap3_xstep hc hp hdec hs hov)

theorem RD.dup2 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP2, .none)) (hov : t.length + 3 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (b :: a :: b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup2_xstep hc hp hdec hs hov)

theorem RD.dup3 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP3, .none)) (hov : t.length + 4 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (c :: a :: b :: c :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup3_xstep hc hp hdec hs hov)

theorem RD.dup4 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP4, .none)) (hov : t.length + 5 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (d :: a :: b :: c :: d :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup4_xstep hc hp hdec hs hov)

theorem RD.dup5 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP5, .none)) (hov : t.length + 6 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (e :: a :: b :: c :: d :: e :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup5_xstep hc hp hdec hs hov)

theorem RD.dup6 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP6, .none)) (hov : t.length + 7 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (f :: a :: b :: c :: d :: e :: f :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup6_xstep hc hp hdec hs hov)

theorem RD.dup7 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP7, .none)) (hov : t.length + 8 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (gg :: a :: b :: c :: d :: e :: f :: gg :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup7_xstep hc hp hdec hs hov)

theorem RD.dup8 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP8, .none)) (hov : t.length + 9 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (hh :: a :: b :: c :: d :: e :: f :: gg :: hh :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup8_xstep hc hp hdec hs hov)

/-- `GAS` pushes the (cursor-dependent) remaining gas, so its pushed value is existential. -/
theorem RD.gas {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.GAS, .none)) (hov : stk.length + 1 ≤ 1024) :
    ∃ gv, RD code ee g s0 (pc + ⟨1⟩) (gv :: stk) mem aw rdata acc (k + 1) (C + 2) := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact ⟨⟨0⟩, by unfold RD; exact Or.inl hoog⟩
  · have st := gas_xstep hcode hpc hdec hstk hov
    refine ⟨(s.machineState.gasAvailable.subNat 2).toUInt256, ?_⟩
    unfold RD
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stGas s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stGas]; exact hcode
      · simp only [stGas]; rw [hpc]
      · simp only [stGas]; rw [hstk]
      · simp only [stGas]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stGas]; exact hmem
      · simp only [stGas]; exact haw
      · simp only [stGas]; exact hrdata
      · simp only [stGas]; exact hacc
      · exact hee
      · exact hworld

/-- `RETURNDATASIZE` as an `RD → RD` combinator: pushes `|returnData| = |rdata|`.  Now that `RD`
    pins `rdata`, the pushed size is the *concrete* `ofNat rdata.size` (the post-call decoder needs
    it for the `≥ 32` length check). -/
theorem RD.returndatasize {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.RETURNDATASIZE, .none)) (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.ofNat rdata.size :: stk) mem aw rdata acc (k + 1) (C + 2) := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact (by unfold RD; exact Or.inl hoog)
  · have st := returndatasize_xstep hcode hpc hdec hstk hov
    rw [show UInt256.ofNat rdata.size = UInt256.ofNat s.machineState.returnData.size from by rw [hrdata]]
    unfold RD
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stReturndatasize s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stReturndatasize]; exact hcode
      · simp only [stReturndatasize]; rw [hpc]
      · simp only [stReturndatasize]; rw [hstk]
      · simp only [stReturndatasize]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stReturndatasize]; exact hmem
      · simp only [stReturndatasize]; exact haw
      · simp only [stReturndatasize]; exact hrdata
      · simp only [stReturndatasize]; exact hacc
      · exact hee
      · exact hworld

/-- The four-opcode idiom `RETURNDATASIZE; PUSH0; PUSH0; RETURNDATACOPY` — copy the *entire* return
    data to `mem[0]`.  Done as one combinator so the `RETURNDATACOPY` length argument stays tied to
    `|returnData|` (the size just pushed), discharging its `b + c ≤ |returnData|` guard internally
    (`0 + |rd| % 2²⁵⁶ ≤ |rd|`).  Resulting memory / active-words / counters are existential — the
    revert tail that follows ignores them. -/
theorem RD.returndatacopyFull {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hd0 : decode code pc = some (.RETURNDATASIZE, .none))
    (hd1 : decode code (pc + ⟨1⟩) = some (.PUSH0, .none))
    (hd2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.PUSH0, .none))
    (hd3 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.RETURNDATACOPY, .none))
    (hov : stk.length + 3 ≤ 1024) :
    ∃ mem' aw' k' C', RD code ee g s0 (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) stk mem' aw' rdata acc k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact ⟨mem, aw, k, C, by unfold RD; exact Or.inl hoog⟩
  · -- s1 = RETURNDATASIZE s
    set c := UInt256.ofNat s.machineState.returnData.size with hc
    have st1 := returndatasize_xstep hcode hpc hd0 hstk (by omega)
    by_cases g1 : g.toNat < C + 2
    · exact ⟨mem, aw, k, C, by unfold RD; exact Or.inl (hX.trans (stepOOG hgas st1 hk hC (by omega)))⟩
    set s1 := stReturndatasize s with hs1
    have hX1 := hX.trans (stepContinue hgas st1 hk (by omega))
    have hc1 : s1.executionEnv.code = code := hcode
    have hp1 : s1.machineState.pc = pc + ⟨1⟩ := by simp only [hs1, stReturndatasize]; rw [hpc]
    have hk1 : s1.machineState.stack = c :: stk := by simp only [hs1, stReturndatasize, ← hc]; rw [hstk]
    have hgas1 : s1.machineState.gasAvailable = g.subNat (C + 2) := by
      simp only [hs1, stReturndatasize]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
    -- s2 = PUSH0 s1
    have st2 := push0_xstep hc1 hp1 hd1 hk1 (by simp only [List.length_cons]; omega)
    by_cases g2 : g.toNat < (C + 2) + 2
    · exact ⟨mem, aw, k + 1, C + 2, by unfold RD; exact Or.inl (hX1.trans (stepOOG hgas1 st2 (by omega) (by omega) (by omega)))⟩
    set s2 := stPush0 s1 with hs2
    have hX2 := hX1.trans (stepContinue hgas1 st2 (by omega) (by omega))
    have hc2 : s2.executionEnv.code = code := hc1
    have hp2 : s2.machineState.pc = pc + ⟨1⟩ + ⟨1⟩ := by simp only [hs2, stPush0]; rw [hp1]
    have hk2 : s2.machineState.stack = ⟨0⟩ :: c :: stk := by simp only [hs2, stPush0]; rw [hk1]
    have hgas2 : s2.machineState.gasAvailable = g.subNat ((C + 2) + 2) := by
      simp only [hs2, stPush0]; rw [hgas1, Sat256.subNat_sub_add_of_sub_sub]
    -- s3 = PUSH0 s2
    have st3 := push0_xstep hc2 hp2 hd2 hk2 (by simp only [List.length_cons]; omega)
    by_cases g3 : g.toNat < ((C + 2) + 2) + 2
    · exact ⟨mem, aw, k + 2, (C + 2) + 2, by unfold RD; exact Or.inl (hX2.trans (stepOOG hgas2 st3 (by omega) (by omega) (by omega)))⟩
    set s3 := stPush0 s2 with hs3
    have hX3 := hX2.trans (stepContinue hgas2 st3 (by omega) (by omega))
    have hc3 : s3.executionEnv.code = code := hc2
    have hp3 : s3.machineState.pc = pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ := by simp only [hs3, stPush0]; rw [hp2]
    have hk3 : s3.machineState.stack = ⟨0⟩ :: ⟨0⟩ :: c :: stk := by simp only [hs3, stPush0]; rw [hk2]
    have hgas3 : s3.machineState.gasAvailable = g.subNat (((C + 2) + 2) + 2) := by
      simp only [hs3, stPush0]; rw [hgas2, Sat256.subNat_sub_add_of_sub_sub]
    have hrd3 : s3.machineState.returnData = s.machineState.returnData := by
      simp only [hs3, hs2, hs1, stPush0, stReturndatasize]
    -- s4 = RETURNDATACOPY s3, copying all of returnData to mem[0]
    have hcle : c.toNat ≤ s.machineState.returnData.size := by
      rw [hc]; exact Nat.mod_le _ _
    have hguard : ¬ (⟨0⟩ : UInt256).toNat + c.toNat > s3.machineState.returnData.size := by
      rw [hrd3, show (⟨0⟩ : UInt256).toNat = 0 from rfl]; omega
    have st4 := returndatacopy_xstep hc3 hp3 hd3 hk3 hguard (by omega)
    rw [collapse_two_stage] at st4
    -- generalise the two symbolic gas components so the arithmetic is purely linear
    set memc := memoryExpansionCost s3 .RETURNDATACOPY with hmemc
    set cpc := GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32) with hcpc
    by_cases g4 : g.toNat < (((C + 2) + 2) + 2) + (memc + cpc)
    · exact ⟨mem, aw, k + 3, ((C + 2) + 2) + 2, by unfold RD; exact Or.inl (hX3.trans (stepOOG hgas3 st4 (by omega) (by omega) (by omega)))⟩
    set s4 := stReturndatacopy s3 ⟨0⟩ ⟨0⟩ c stk with hs4
    refine ⟨s4.machineState.memory, s4.machineState.activeWords, k + 4,
      (((C + 2) + 2) + 2) + (memc + cpc), ?_⟩
    unfold RD
    refine Or.inr ⟨s4, hX3.trans (stepContinue hgas3 st4 (by omega) (by omega)),
      ?_, ?_, ?_, ?_, by omega, by omega, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [hs4, stReturndatacopy]; exact hc3
    · simp only [hs4, stReturndatacopy]; rw [hp3]
    · simp only [hs4, stReturndatacopy]
    · simp only [hs4, stReturndatacopy, ← hmemc, ← hcpc]
      rw [hgas3, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
    · simp only [hs4, stReturndatacopy]; rw [hrd3]; exact hrdata
    · simp only [hs4, stReturndatacopy]; exact hacc
    · simp only [hs4, stReturndatacopy]; exact hee
    · refine ⟨?_, ?_, ?_⟩
      · simp only [hs4, stReturndatacopy, hs3, hs2, hs1, stPush0, stReturndatasize]; exact hworld.1
      · simp only [hs4, stReturndatacopy, hs3, hs2, hs1, stPush0, stReturndatasize]; exact hworld.2.1
      · simp only [hs4, stReturndatacopy, hs3, hs2, hs1, stPush0, stReturndatasize]; exact hworld.2.2

/-- `DUP1` goes through `stDup1`, not `stSwap`, so it is its own combinator. -/
theorem RD.dup1 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP1, .none)) (hov : t.length + 2 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (a :: a :: t) mem aw rdata acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := dup1_xstep hcode hpc hdec hstk (by simp only [List.length_cons]; omega)
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stDup1 s a t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stDup1]; exact hcode
      · simp only [stDup1]; rw [hpc]
      · rfl
      · simp only [stDup1]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stDup1]; exact hmem
      · simp only [stDup1]; exact haw
      · simp only [stDup1]; exact hrdata
      · simp only [stDup1]; exact hacc
      · exact hee
      · exact hworld

theorem RD.pop {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.POP, .none))
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem aw rdata acc (k + 1) (C + 2) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := pop_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stPop s t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stPop]; exact hcode
      · simp only [stPop]; rw [hpc]
      · rfl
      · simp only [stPop]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stPop]; exact hmem
      · simp only [stPop]; exact haw
      · simp only [stPop]; exact hrdata
      · simp only [stPop]; exact hacc
      · exact hee
      · exact hworld

/-- Internal `JUMP` to a statically-valid destination `a` (needs the
    `(D_J code 0).contains a` fact).  Sets `pc := a`, pops the target. -/
theorem RD.jump {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.JUMP, .none))
    (hjd : (D_J code 0).contains a = true)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 a t mem aw rdata acc (k + 1) (C + 8) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := jump_xstep hcode hpc hdec hstk hjd hov
    by_cases gg : g.toNat < C + 8
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stJump s a t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stJump]; exact hcode
      · rfl
      · rfl
      · simp only [stJump]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stJump]; exact hmem
      · simp only [stJump]; exact haw
      · simp only [stJump]; exact hrdata
      · simp only [stJump]; exact hacc
      · exact hee
      · exact hworld

theorem RD.push2 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH2, some (argv, 2)))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + UInt256.ofNat 3) (argv :: stk) mem aw rdata acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := push2_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stPush2 s argv,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stPush2]; exact hcode
      · simp only [stPush2]; rw [hpc]
      · simp only [stPush2]; rw [hstk]
      · simp only [stPush2]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stPush2]; exact hmem
      · simp only [stPush2]; exact haw
      · simp only [stPush2]; exact hrdata
      · simp only [stPush2]; exact hacc
      · exact hee
      · exact hworld

theorem RD.eq {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.EQ, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.eq a b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => eq_xstep hc hp hdec hs hov)

theorem RD.lt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LT, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.lt a b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => lt_xstep hc hp hdec hs hov)

theorem RD.slt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SLT, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.slt a b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => slt_xstep hc hp hdec hs hov)

theorem RD.shr {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SHR, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.shiftRight b a :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => shr_xstep hc hp hdec hs hov)

theorem RD.sub {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SUB, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.sub a b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => sub_xstep hc hp hdec hs hov)

theorem RD.and {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.AND, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.land a b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => and_xstep hc hp hdec hs hov)

theorem RD.shl {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SHL, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.shiftLeft b a :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => shl_xstep hc hp hdec hs hov)

theorem RD.add {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.ADD, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) ((a + b) :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => add_xstep hc hp hdec hs hov)

/-- `MUL` is cost 5 (`stMul`), so it does not share the `stBinop` helper. -/
theorem RD.mul {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MUL, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.mul a b :: t) mem aw rdata acc (k + 1) (C + 5) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := mul_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 5
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stMul s (UInt256.mul a b) t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stMul]; exact hcode
      · simp only [stMul]; rw [hpc]
      · rfl
      · simp only [stMul]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stMul]; exact hmem
      · simp only [stMul]; exact haw
      · simp only [stMul]; exact hrdata
      · simp only [stMul]; exact hacc
      · exact hee
      · exact hworld

theorem RD.iszero {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.ISZERO, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.isZero a :: t) mem aw rdata acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := iszero_xstep hcode hpc hdec hstk (by simp only [List.length_cons]; omega)
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stIsZero s a t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stIsZero]; exact hcode
      · simp only [stIsZero]; rw [hpc]
      · rfl
      · simp only [stIsZero]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stIsZero]; exact hmem
      · simp only [stIsZero]; exact haw
      · simp only [stIsZero]; exact hrdata
      · simp only [stIsZero]; exact hacc
      · exact hee
      · exact hworld

theorem RD.not {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.NOT, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.lnot a :: t) mem aw rdata acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := not_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stNot s a t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stNot]; exact hcode
      · simp only [stNot]; rw [hpc]
      · rfl
      · simp only [stNot]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stNot]; exact hmem
      · simp only [stNot]; exact haw
      · simp only [stNot]; exact hrdata
      · simp only [stNot]; exact hacc
      · exact hee
      · exact hworld

/-! ### Environment-reading ops (read the carried `ee`) -/

theorem RD.callvalue {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.CALLVALUE, .none))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (ee.weiValue :: stk) mem aw rdata acc (k + 1) (C + 2) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := callvalue_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stCallvalue s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stCallvalue]; exact hcode
      · simp only [stCallvalue]; rw [hpc]
      · simp only [stCallvalue]; rw [hee, hstk]
      · simp only [stCallvalue]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stCallvalue]; exact hmem
      · simp only [stCallvalue]; exact haw
      · simp only [stCallvalue]; exact hrdata
      · simp only [stCallvalue]; exact hacc
      · exact hee
      · exact hworld

theorem RD.calldatasize {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.CALLDATASIZE, .none))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.ofNat ee.calldata.size :: stk) mem aw rdata acc (k + 1) (C + 2) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := calldatasize_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stCalldatasize s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stCalldatasize]; exact hcode
      · simp only [stCalldatasize]; rw [hpc]
      · simp only [stCalldatasize]; rw [hee, hstk]
      · simp only [stCalldatasize]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stCalldatasize]; exact hmem
      · simp only [stCalldatasize]; exact haw
      · simp only [stCalldatasize]; exact hrdata
      · simp only [stCalldatasize]; exact hacc
      · exact hee
      · exact hworld

theorem RD.calldataload {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.CALLDATALOAD, .none))
    (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
        (uInt256OfByteArray (ee.calldata.readBytes a.toNat 32) :: t) mem aw rdata acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := calldataload_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stCalldataload s a t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stCalldataload]; exact hcode
      · simp only [stCalldataload]; rw [hpc]
      · simp only [stCalldataload]; rw [hee]
      · simp only [stCalldataload]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stCalldataload]; exact hmem
      · simp only [stCalldataload]; exact haw
      · simp only [stCalldataload]; exact hrdata
      · simp only [stCalldataload]; exact hacc
      · exact hee
      · exact hworld

/-! ### Memory ops (dynamic cost)

`MLOAD`/`MSTORE` cost is `memoryExpansionCost s op + 3`, which depends only on the
carried `activeWords` and the offset (stack top).  The combinator takes the concrete
`mcost` plus a proof `hmc` (computed at the call site from the carried `aw` and the
literal offset) and updates `mem`/`aw` accordingly. -/

/-- `MSTORE`: pops `a` (offset), `b` (value); writes `b` at `mem[a]`, grows active words. -/
theorem RD.mstore {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256} (mcost : ℕ) (memout : ByteArray) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MSTORE, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: t →
        memoryExpansionCost s .MSTORE = mcost)
    (hmemout : b.toByteArray.write 0 mem a.toNat 32 = memout)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat 32) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t memout awout rdata acc (k + 1) (C + (mcost + 3)) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .MSTORE = mcost := hmc s haw hstk
    have st := mstore_xstep hcode hpc hdec hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost + 3)
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stMStore s a b t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stMStore]; exact hcode
      · simp only [stMStore]; rw [hpc]
      · rfl
      · simp only [stMStore, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stMStore]; rw [hmem, hmemout]
      · simp only [stMStore]; rw [haw, hawout]
      · simp only [stMStore]; exact hrdata
      · simp only [stMStore]; exact hacc
      · exact hee
      · exact hworld

/-- `MLOAD`: pops `a` (offset), pushes the 32-byte word at `mem[a]`, grows active words. -/
theorem RD.mload {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256} (mcost : ℕ) (loadval awout : UInt256)
    (h : RD code ee g s0 pc (a :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MLOAD, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: t →
        memoryExpansionCost s .MLOAD = mcost)
    (hval : (if a.toNat ≥ mem.size ∨ a ≥ aw * ⟨32⟩ then ⟨0⟩
             else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding a.toNat 32))) = loadval)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat 32) = awout)
    (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (loadval :: t) mem awout rdata acc (k + 1) (C + (mcost + 3)) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .MLOAD = mcost := hmc s haw hstk
    have st := mload_xstep hcode hpc hdec hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost + 3)
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stMLoad s a t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stMLoad]; exact hcode
      · simp only [stMLoad]; rw [hpc]
      · simp only [stMLoad]; rw [hmem, haw, hval]
      · simp only [stMLoad, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stMLoad]; rw [hmem]
      · simp only [stMLoad]; rw [haw, hawout]
      · simp only [stMLoad]; exact hrdata
      · simp only [stMLoad]; exact hacc
      · exact hee
      · exact hworld

/-- `JUMPI` **taken** (condition `b ≠ 0`) to a statically-valid destination `a`. -/
theorem RD.jumpiT {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.JUMPI, .none))
    (hb : b ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains a = true)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 a t mem aw rdata acc (k + 1) (C + 10) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := jumpi_t_xstep hcode hpc hdec hstk hb hjd hov
    by_cases gg : g.toNat < C + 10
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stJumpiT s a t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stJumpiT]; exact hcode
      · rfl
      · rfl
      · simp only [stJumpiT]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stJumpiT]; exact hmem
      · simp only [stJumpiT]; exact haw
      · simp only [stJumpiT]; exact hrdata
      · simp only [stJumpiT]; exact hacc
      · exact hee
      · exact hworld

/-- `JUMPI` **not taken** (condition `b = 0`): falls through to `pc+1`.  Takes the
    condition value + a proof it is `⟨0⟩` (so a symbolic condition can be resolved at
    the call site), symmetric with `jumpiT`. -/
theorem RD.jumpiNT {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.JUMPI, .none))
    (hb : b = ⟨0⟩)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem aw rdata acc (k + 1) (C + 10) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · rw [hb] at hstk
    have st := jumpi_nt_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 10
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stJumpiNT s t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stJumpiNT]; exact hcode
      · simp only [stJumpiNT]; rw [hpc]
      · rfl
      · simp only [stJumpiNT]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stJumpiNT]; exact hmem
      · simp only [stJumpiNT]; exact haw
      · simp only [stJumpiNT]; exact hrdata
      · simp only [stJumpiNT]; exact hacc
      · exact hee
      · exact hworld


/-- A message call cannot create gas: the gas `Θ` returns (the callee's leftover) never exceeds the
gas it was forwarded.  The old CALL proof needed this to bound a `gasAvailable - cost + refund`
successor.  The current opcode semantics instead charges `cost - refund`, so the `RD` gas invariant
does not fundamentally depend on this bound anymore; the proof below still uses it as a convenient
local fact while establishing that the CALL step advances the symbolic counters. -/
theorem Theta_returnedGas_le
    (blob : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (c : ToExecute) (g p v v' : UInt256) (d : ByteArray)
    (e : Fin 1025) (H : BlockHeader) (w : Bool) :
    (Ethereum.EVM.Θ blob cA gh blocks σ σ₀ A s o r c g p v v' d e H w).2.2.1.toNat ≤ g.toNat := by
  exact Ethereum.EVM.Theta_gas_le

/-- **Trusted base — `Θ` return-data is address-bounded.**  A message call's return data is a slice
    `memory[off .. off+len]` with `off, len : UInt256`, so its size is below `2²⁵⁶`; the tighter
    `< 2²⁵⁵` bound (still astronomically large — a return buffer can never approach `2²⁵⁵` bytes)
    is what the solc return-decoder's `ADD`/signed-`SLT` length check needs to behave as plain
    unsigned arithmetic.  Physically always true; analogue of the per-call `calldata.size < 2²⁵⁵`. -/
axiom Theta_returnData_size_lt
    (blob : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (c : ToExecute) (g p v v' : UInt256) (d : ByteArray)
    (e : Fin 1025) (H : BlockHeader) (w : Bool) :
    (Ethereum.EVM.Θ blob cA gh blocks σ σ₀ A s o r c g p v v' d e H w).2.2.2.2.2.size < 2 ^ 255

/-- **SSTORE** as an `RD → RD` combinator (existential step/gas counters, like `RD.loop`): from a
    cursor at the `SSTORE` pc with `[slot, val, …t]` and carried accounts `(cA, σ)`, write `val` to
    `slot` of the caller account (`ee.codeOwner`), advancing the carried `accountMap` to
    `sstoreAccountMap ee.codeOwner σ slot val` (`createdAccounts` and memory untouched).  The cost
    `Csstore s` is symbolic (it depends on the unknown prior slot value), so the counters are
    existential.  Requires `ee.perm = true` — `SSTORE` aborts in static mode. -/
theorem RD.sstore {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {slot val : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (slot :: val :: t) mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hdec : decode code pc = some (.SSTORE, .none))
    (hov : t.length ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) t mem aw rdata
      (cA, sstoreAccountMap ee.codeOwner σ slot val) k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact ⟨k, C, Or.inl hoog⟩
  · have hperms : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have st := sstore_xstep hcode hpc hdec hperms hstk hov
    have hmax : Csstore s ≤ max (Csstore s) (GasConstants.Gcallstipend + 1) := le_max_left _ _
    have hpos := Theory.Csstore_pos s
    by_cases gg : g.toNat < C + max (Csstore s) (GasConstants.Gcallstipend + 1)
    · exact ⟨k, C, Or.inl (hX.trans (stepOOG hgas st hk hC gg))⟩
    · have hcss : Csstore s ≤ s.machineState.gasAvailable.toNat := by simp [hgas, Sat256.subNat, Sat256.toNat]; rw [← Sat256.toNat]; omega
      refine ⟨k + 1, C + Csstore s, Or.inr ⟨stSStore s slot val t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)),
        ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [stSStore_executionEnv]; exact hcode
      · rw [stSStore_pc, hpc]
      · exact stSStore_stack s slot val t
      · rw [stSStore_gas s slot val t, ← Sat256.subNat_sub_add_of_sub_sub, hgas]
      · rw [stSStore_memory]; exact hmem
      · rw [stSStore_activeWords]; exact haw
      · exact hrdata
      · have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
        have hσ : s.accountMap = σ := congrArg Prod.snd hacc
        have hco : s.executionEnv.codeOwner = ee.codeOwner := by rw [hee]
        rw [stSStore_createdAccounts, stSStore_accountMap, hcA, hσ, hco]
      · rw [stSStore_executionEnv]; exact hee
      · exact hworld

/-- **CALLER**: push `msg.sender` (`ee.source`) onto the stack (cost `Gbase = 2`, pc += 1). -/
theorem RD.caller {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.CALLER, .none)) (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.ofNat ee.source.val :: stk) mem aw rdata acc
      (k + 1) (C + 2) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := caller_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stCaller s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stCaller]; exact hcode
      · simp only [stCaller]; rw [hpc]
      · simp only [stCaller]; rw [hstk, hee]
      · simp only [stCaller]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stCaller]; exact hmem
      · simp only [stCaller]; exact haw
      · simp only [stCaller]; exact hrdata
      · simp only [stCaller]; exact hacc
      · exact hee
      · exact hworld

/-- **SWAP4**: exchange the stack top with the 5th element (cost `Gverylow = 3`, pc += 1). -/
theorem RD.swap4 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP4, .none)) (hov : t.length + 5 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (e :: b :: c :: d :: a :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap4_xstep hc hp hdec hs hov)

/-- **KECCAK256**: pop offset `a` and size `b`, push `KEC(mem[a..a+b])` (two-stage cost
    `memExp + hashCost`, pc += 1).  `mcost` is the memory-expansion cost (computed from the carried
    `aw` and offsets via `hmc`); the hash cost is `Gkeccak256 + Gkeccak256word·⌈b/32⌉`. -/
theorem RD.keccak256 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256} (mcost : ℕ) (kecval awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.KECCAK256, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: t →
        memoryExpansionCost s .KECCAK256 = mcost)
    (hval : UInt256.ofNat (fromByteArrayBigEndian
              (ffi.KEC (mem.readWithPadding a.toNat b.toNat))) = kecval)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (kecval :: t) mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Gkeccak256
        + GasConstants.Gkeccak256word * ((b.toNat + 31) / 32)))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .KECCAK256 = mcost := hmc s haw hstk
    have st := keccak_xstep hcode hpc hdec hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Gkeccak256 + GasConstants.Gkeccak256word * ((b.toNat + 31) / 32)))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stKeccak s a b t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, (by have : 1 ≤ GasConstants.Gkeccak256 := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stKeccak]; exact hcode
      · simp only [stKeccak]; rw [hpc]
      · simp only [stKeccak]; rw [hmem, hval]
      · simp only [stKeccak, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stKeccak]; exact hmem
      · simp only [stKeccak]; rw [haw, hawout]
      · simp only [stKeccak]; exact hrdata
      · simp only [stKeccak]; exact hacc
      · exact hee
      · exact hworld

/-- **SLOAD**: pop slot `a`, push `storage[ee.codeOwner][a]` from the carried `accountMap` `σ`
    (cost `Csload` is symbolic — warm/cold — so the counters are existential, pc += 1).  The
    `substate` access-set update is invisible to `RD`; `createdAccounts`/`accountMap` are untouched. -/
theorem RD.sload {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: t) mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.SLOAD, .none)) (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩)
      ((σ.find? ee.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD a ⟨0⟩)) :: t)
      mem aw rdata (cA, σ) k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact ⟨k, C, Or.inl hoog⟩
  · have st := sload_xstep hcode hpc hdec hstk hov
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hco : s.executionEnv.codeOwner = ee.codeOwner := by rw [hee]
    by_cases gg : g.toNat < C + Csload (a :: t) s.substate s.executionEnv
    · exact ⟨k, C, Or.inl (hX.trans (stepOOG hgas st hk hC gg))⟩
    · refine ⟨k + 1, C + Csload (a :: t) s.substate s.executionEnv, Or.inr ⟨stSload s a t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, (by have : 1 ≤ Csload (a :: t) s.substate s.executionEnv := (by unfold Csload; split <;> decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · simp only [stSload]; exact hcode
      · simp only [stSload]; rw [hpc]
      · simp only [stSload]; rw [hσ, hco]
      · simp only [stSload]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stSload]; exact hmem
      · simp only [stSload]; exact haw
      · simp only [stSload]; exact hrdata
      · simp only [stSload]; rw [hcA, hσ]
      · simp only [stSload]; exact hee
      · simp only [stSload]; exact hworld

/-- **LOG3**: pop `[offset, size, t1, t2, t3]`, append a log over `mem[offset..offset+size]` with the
    three topics (cost `memExp + Glog + Glogdata·size + 3·Glogtopic`, pc += 1).  Requires `ee.perm`
    (aborts in static mode).  The `substate.logSeries` append is invisible to `RD`. -/
theorem RD.log3 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG3, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: e :: t →
        memoryExpansionCost s .LOG3 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 3 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG3 = mcost := hmc s haw hstk
    have hperms : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have st := log3_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 3 * GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stLog3 s a b c d e t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stLog3]; exact hcode
      · simp only [stLog3]; rw [hpc]
      · simp only [stLog3]
      · simp only [stLog3, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stLog3]; exact hmem
      · simp only [stLog3]; rw [haw, hawout]
      · simp only [stLog3]; exact hrdata
      · simp only [stLog3]; exact hacc
      · simp only [stLog3]; exact hee
      · simp only [stLog3]; exact hworld


set_option maxHeartbeats 1000000 in
/-- **CALL** (value 0) as an `RD → RD` combinator.  From a cursor at the `CALL` pc with the
    7 stack args `[gas, target, 0, inOff, inSize, outOff, outSize, …t]`, perform the *opaque*
    external message call `Θ` and advance to the successor: the result `(cA', σ', z, o)` is
    abstracted (no assumption on the callee's code), the return bytes `o` are written to memory,
    the status flag `z` is pushed, and accounts advance to `(cA', σ')`.  The same `Θ` is what the
    Solm-side `externalCall` invokes, so the two coincide by construction.  Gas is existential:
    the successor gas is expressed through the charged delta `gc - returnedGas`. -/
theorem RD.call {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {gasArg target inOffset inSize outOffset outSize : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: ⟨0⟩ :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.CALL, .none))
    (hdepth : ee.depth.val < 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ ee.blobVersionedHashes cA
          s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat ee.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOffset.toNat inSize.toNat) (ee.depth + 1) ee.header ee.perm)
      ∧ RD code ee g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: t)
          (o.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat o.size)).toNat)
          (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
            outOffset.toNat outSize.toNat))
          o (cA', σ') k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · -- OOG: default witnesses; the Θ-link is tuple-eta (rfl), the RD part is OOG.
    exact ⟨_, _, _, _, default, ⟨0⟩, k, C, ⟨_, _, rfl⟩, (by unfold RD; exact Or.inl hoog)⟩
  · -- reach the CALL cursor `s`; reduce `step_call` (value 0, depth < 1024)
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
    have hgtF : ∀ y : UInt256, (({val := 0} : UInt256) > y) = False := fun y => eq_false (Fin.not_lt_zero _)
    have hdeqF : (s.executionEnv.depth == 1024) = false := by
      rw [beq_eq_false_iff_ne]; intro hh; rw [hh] at hdepth'; exact absurd hdepth' (by decide)
    simp only [List.length_cons, hovF, hstaticF, if_false, hdepthLt, hbal, hgtF, hdeqF,
      and_true, if_true, Bool.or_false] at st
    rw [collapse_two_stage, hcode] at st
    -- st : Xstep (D_J code 0) s = if (gas < memCost+gasCost) then OOG else .ok (SUCC, none)
    -- Step the cursor with `X_peel`, then `split` on the (unnamed) gas guard so SUCC stays concrete.
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    -- hXP : X (g+1) s0 = if (gas < memCost+gasCost) then OOG else X (g-k) SUCC
    split at hXP
    · -- OOG: the whole run is out of gas (RD absorbs it); Θ-link via default witnesses.
      exact ⟨_, _, _, _, default, ⟨0⟩, k, C, ⟨_, _, rfl⟩, by unfold RD; exact Or.inl hXP⟩
    · -- success: SUCC is concrete in hXP.  Emit `Or.inr ⟨SUCC, …⟩` with field projections,
      -- the gas-refund arithmetic (`C' = g - SUCC.gas`), and the Θ-link by tuple-eta.
      rename_i hP
      set mc := memoryExpansionCost s Operation.CALL with hmc
      set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) { val := 0 } gasArg
        s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hgc
      set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) { val := 0 } gasArg
        s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength + 1,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hG
      set cg := UInt256.ofNat G with hcg
      set ce := Cextra (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) { val := 0 }
        s.accountMap s.substate with hce
      set θs := Θ s.executionEnv.blobVersionedHashes s.createdAccounts s.genesisBlockHeader s.blocks
        s.accountMap s.σ₀ (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
        (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner)) s.executionEnv.sender
        (AccountAddress.ofUInt256 target) (toExecute s.accountMap (AccountAddress.ofUInt256 target))
        cg (UInt256.ofNat s.executionEnv.gasPrice) { val := 0 } { val := 0 }
        (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat) (s.executionEnv.depth + 1)
        s.executionEnv.header s.executionEnv.perm with hθs
      set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - θs.2.2.1.toNat) with hgv
      have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
      have hσ : s.accountMap = σ := congrArg Prod.snd hacc
      have hw1 : s.σ₀ = s0.σ₀ := hworld.1
      have hw2 : s.genesisBlockHeader = s0.genesisBlockHeader := hworld.2.1
      have hw3 : s.blocks = s0.blocks := hworld.2.2
      -- gas arithmetic
      have haN : s.machineState.gasAvailable.toNat < UInt256.size := s.machineState.gasAvailable.isLt
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hmcle : mc ≤ s.machineState.gasAvailable.toNat := by omega
      have hretle : θs.2.2.1.toNat ≤ cg.toNat := by
        rw [hθs]
        exact Theta_returnedGas_le s.executionEnv.blobVersionedHashes s.createdAccounts s.genesisBlockHeader
          s.blocks s.accountMap s.σ₀ (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
          (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner)) s.executionEnv.sender
          (AccountAddress.ofUInt256 target) (toExecute s.accountMap (AccountAddress.ofUInt256 target))
          cg (UInt256.ofNat s.executionEnv.gasPrice) { val := 0 } { val := 0 }
          (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat) (s.executionEnv.depth + 1)
          s.executionEnv.header s.executionEnv.perm
      have hcgle : cg.toNat ≤ G := by
        have h : cg.toNat = G % UInt256.size := by rw [hcg]; rfl
        rw [h]; exact Nat.mod_le _ _
      have hgcG : gc = G + ce := by rw [hgc, hG, hce]; rfl
      have hce1 : 1 ≤ ce := by
        rw [hce]
        have hcacc : 1 ≤ Caccess (AccountAddress.ofUInt256 target) s.substate := by
          unfold Caccess; split <;> decide
        unfold Cextra; omega
      have hg''le : θs.2.2.1.toNat + 1 ≤ gc := by omega
      have hgcle' : gc ≤ (s.machineState.gasAvailable.subNat mc).toNat := by
        rw [toNat_sub_ofNat hmcle]; omega
      have hgvN : gv = (s.machineState.gasAvailable.subNat mc).subNat (gc - θs.2.2.1.toNat) := by
        rw [hgv]
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      have hrefundCostPos : 1 ≤ gc - θs.2.2.1.toNat := by omega
      set callCharge := mc + (gc - θs.2.2.1.toNat) with hcallCharge
      have hcallChargePos : 1 ≤ callCharge := by
        rw [hcallCharge]
        omega
      have hcallChargeLeGas : callCharge ≤ s.machineState.gasAvailable.toNat := by
        rw [hcallCharge]
        have hdeltaLe : gc - θs.2.2.1.toNat ≤ gc := Nat.sub_le _ _
        omega
      have hCcallCharge : C + callCharge ≤ g.toNat := by
        rw [hgasN] at hcallChargeLeGas
        omega
      have hgvGas : gv = g.subNat (C + callCharge) := by
        rw [hgv, hgas, hcallCharge]
        rw [Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      have hgkey : gv.toNat + k + 1 ≤ g.toNat := by
        rw [hgvGas, Sat256.subNat_toNat]
        omega
      rw [show g.toNat - k = g.toNat + 1 - (k + 1) from by omega] at hXP
      -- assemble the conclusion
      refine ⟨θs.1, θs.2.1, θs.2.2.2.2.1, θs.2.2.2.2.2,
        (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate, cg, k + 1,
        C + callCharge, ⟨θs.2.2.1, θs.2.2.2.1, ?_⟩, ?_⟩
      · -- Θ-link: rewrite cursor fields to the world/ee/acc form, then tuple-eta
        rw [← hee, ← hcA, ← hσ, ← hmem, ← hw1, ← hw2, ← hw3, ← hθs]
      · -- RD on the successor `SUCC` (inferred from `hXP`'s `X` equation)
        unfold RD
        refine Or.inr ⟨_, hXP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hcode
        · rw [hpc]
        · cases θs.2.2.2.2.1 <;> rfl
        · show gv = g.subNat (C + callCharge)
          exact hgvGas
        · show k + 1 ≤ C + callCharge
          rw [hcallCharge]
          omega
        · exact hCcallCharge
        · rw [hmem]
        · rw [haw]
        · rfl
        · rfl
        · exact hee
        · exact hworld


/-- **`CALL` at the call-depth limit** (`ee.depth = 1024`, value `0`).  The EVM never invokes `Θ`:
    it takes the *no-call-made* branch, returning `0` (`z = false`) with accounts, memory and
    return data untouched — the cursor advances with `⟨0⟩` pushed.  Mirrors `RD.call`'s gas
    arithmetic but with the concrete else-tuple in place of `Θ`. -/
theorem RD.callDepthLimit {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {gasArg target inOffset inSize outOffset outSize : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: ⟨0⟩ :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.CALL, .none))
    (hdepth : ee.depth = 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) (⟨0⟩ :: t)
        (ByteArray.empty.write 0 mem outOffset.toNat
          (min outSize (UInt256.ofNat ByteArray.empty.size)).toNat)
        (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat))
        ByteArray.empty (cA, σ) k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact ⟨k, C, by unfold RD; exact Or.inl hoog⟩
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.CALL, .none) := by
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
    have hgtF : ∀ y : UInt256, (({val := 0} : UInt256) > y) = False := fun y => eq_false (Fin.not_lt_zero _)
    have hdeqT : (s.executionEnv.depth == 1024) = true := by rw [beq_iff_eq]; exact hdepth1024
    simp only [List.length_cons, hovF, hstaticF, if_false, hdepthF, hbal, hgtF, hdeqT,
      and_false, Bool.or_true, if_true] at st
    rw [collapse_two_stage, hcode] at st
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    set mc := memoryExpansionCost s Operation.CALL with hmc
    set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) { val := 0 } gasArg
      s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hgc
    set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) { val := 0 } gasArg
      s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength + 1,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hG
    set ce := Cextra (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) { val := 0 }
      s.accountMap s.substate with hce
    set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - (UInt256.ofNat G).toNat) with hgv
    have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    split at hXP
    · exact ⟨k, C, by unfold RD; exact Or.inl hXP⟩
    · rename_i hP
      have haN : s.machineState.gasAvailable.toNat < UInt256.size := s.machineState.gasAvailable.isLt
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hmcle : mc ≤ s.machineState.gasAvailable.toNat := by omega
      have hcgle : (UInt256.ofNat G).toNat ≤ G := by
        show G % UInt256.size ≤ G; exact Nat.mod_le _ _
      have hgcG : gc = G + ce := by rw [hgc, hG, hce]; rfl
      have hce1 : 1 ≤ ce := by
        rw [hce]
        have hcacc : 1 ≤ Caccess (AccountAddress.ofUInt256 target) s.substate := by
          unfold Caccess; split <;> decide
        unfold Cextra; omega
      have hgcle' : gc ≤ (s.machineState.gasAvailable.subNat mc).toNat := by
        rw [toNat_sub_ofNat hmcle]; omega
      have hgvN : gv = (s.machineState.gasAvailable.subNat mc).subNat (gc - (UInt256.ofNat G).toNat) := by
        rw [hgv]
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      set callCharge := mc + (gc - (UInt256.ofNat G).toNat) with hcallCharge
      have hrefundCostPos : 1 ≤ gc - (UInt256.ofNat G).toNat := by omega
      have hcallChargePos : 1 ≤ callCharge := by
        rw [hcallCharge]
        omega
      have hcallChargeLeGas : callCharge ≤ s.machineState.gasAvailable.toNat := by
        rw [hcallCharge]
        have hdeltaLe : gc - (UInt256.ofNat G).toNat ≤ gc := Nat.sub_le _ _
        omega
      have hCcallCharge : C + callCharge ≤ g.toNat := by
        rw [hgasN] at hcallChargeLeGas
        omega
      have hgvGas : gv = g.subNat (C + callCharge) := by
        rw [hgv, hgas, hcallCharge]
        rw [Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      have hgkey : gv.toNat + k + 1 ≤ g.toNat := by
        rw [hgvGas, Sat256.subNat_toNat]
        omega
      rw [show g.toNat - k = g.toNat + 1 - (k + 1) from by omega] at hXP
      refine ⟨k + 1, C + callCharge, ?_⟩
      unfold RD
      refine Or.inr ⟨_, hXP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hcode
      · rw [hpc]
      · rfl
      · show gv = g.subNat (C + callCharge)
        exact hgvGas
      · show k + 1 ≤ C + callCharge
        omega
      · exact hCcallCharge
      · rw [hmem]
      · rw [haw]
      · rfl
      · rw [hcA, hσ]
      · exact hee
      · exact hworld

/-- **Hoare while-rule for an `RD` loop** — the EVM analogue of `execWhile_var` (the Solm-side
    while-rule).  A variant-indexed invariant `Inv : ℕ → α → Prop` over the loop-carried state `α`
    (whose stack image is `stk a`), together with:
    * **`hexit`** — at variant `0` the guard's `JUMPI` falls through to `exit` with `exitStk`;
    * **`hbody`** — at variant `v+1` the guard (not taken) + body + back-jump returns to `header`
      with the state at variant `v`;

    drives the loop from any starting variant to the exit.  Memory / active-words / return-data /
    accounts / env are loop-invariant (carried as fixed parameters); only the stack changes.  The
    step/gas counters are existential (they grow per iteration), exactly as in the per-contract
    hand-written version.  Proof: induction on the variant. -/
theorem RD.whileLoop {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {α : Type}
    (header exit : UInt256) (Inv : ℕ → α → Prop) (stk : α → List UInt256) (exitStk : List UInt256)
    (hexit : ∀ a, Inv 0 a → ∀ k C,
        RD code ee g s0 header (stk a) mem aw rdata acc k C →
        ∃ k' C', RD code ee g s0 exit exitStk mem aw rdata acc k' C')
    (hbody : ∀ v a, Inv (v + 1) a → ∀ k C,
        RD code ee g s0 header (stk a) mem aw rdata acc k C →
        ∃ a' k' C', Inv v a' ∧ RD code ee g s0 header (stk a') mem aw rdata acc k' C') :
    ∀ v a, Inv v a → ∀ k C,
      RD code ee g s0 header (stk a) mem aw rdata acc k C →
      ∃ k' C', RD code ee g s0 exit exitStk mem aw rdata acc k' C' := by
  intro v
  induction v with
  | zero => intro a hInv k C h; exact hexit a hInv k C h
  | succ v ih =>
    intro a hInv k C h
    obtain ⟨a', k', C', hInv', h'⟩ := hbody v a hInv k C h
    exact ih a' hInv' k' C' h'

/-! ## Halting terminals (`RETURN` ⇒ success, `REVERT` ⇒ revert)

`RDret`/`RDrev` are the **terminal** analogues of `RD`: instead of a reached cursor, they record
that the whole run `X (g+1) … s0` has *halted* — with a success (returning bytes `o`, accounts
`acc` preserved) or a revert.  The combinators `RD.ret`/`RD.rev` step the final `RETURN`/`REVERT`
off an `RD` cursor, so a terminating segment composes in the `|>.` chain (`… |>.push0 |>.push0
|>.rev …`) instead of breaking out via `.out` + a manual halt step. -/

/-- Halting-success terminal: `X (g+1) … s0` returns the bytes `o`, preserving accounts `acc`. -/
def RDret (code : ByteArray) (g : Sat256) (s0 : State)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (o : ByteArray) : Prop :=
  X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass
  ∨ ∃ s', X (g.toNat + 1) (D_J code 0) s0 = .ok (.success s' o)
        ∧ (s'.createdAccounts, s'.accountMap) = acc

/-- Halting-revert terminal: `X (g+1) … s0` reverts. -/
def RDrev (code : ByteArray) (g : Sat256) (s0 : State) : Prop :=
  X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass
  ∨ ∃ g' o, X (g.toNat + 1) (D_J code 0) s0 = .ok (.revert g' o)

/-- A terminal opcode whose gas check fails leaves the whole run out of gas (shared by
    `RD.ret`/`RD.rev`).  `stepOOG` does not apply — it wants the *continue* control `.none`,
    whereas a halt step carries `.some (_, o)` — so we peel the erroring `Xstep` directly. -/
private theorem RD.terminalOOG {code : ByteArray} {g : Sat256} {s0 s : State} {k C cost : ℕ}
    {res : Except ExecutionException (State × Option (HaltCause × ByteArray))}
    (hgas : s.machineState.gasAvailable = g.subNat  C)
    (hstep : Xstep (D_J code 0) s
              = if s.machineState.gasAvailable.toNat < cost then .error .OutOfGass else res)
    (hk : k ≤ C) (hC : C ≤ g.toNat) (hOOG : g.toNat < C + cost)
    (hX : X (g.toNat + 1) (D_J code 0) s0 = X (g.toNat + 1 - k) (D_J code 0) s) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass := by
  rw [hX]
  have hgg : s.machineState.gasAvailable.toNat < cost := by
    rw [hgas, Sat256.subNat_toNat]
    omega
  have hstepE : Xstep (D_J code 0) s = .error .OutOfGass := by rw [hstep, if_pos hgg]
  have hfuel : g.toNat + 1 - k = (g.toNat + 1 - (k + 1)) + 1 := by omega
  rw [hfuel]; exact Ethereum.EVM.Xstep_X_X_except _ s _ _ hstepE

private theorem Xi_error_of_X_sat
    {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {e} {g : Sat256}
    (h : X (g.toNat + 1) (D_J I.code 0)
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) = .error e) :
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g.toUInt256 A I = .error e :=
  Xi_error_of_X (g := g.toUInt256) (by
    simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using h)

private theorem Xi_revert_of_X_sat
    {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {g' o} {g : Sat256}
    (h : X (g.toNat + 1) (D_J I.code 0)
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
          = .ok (.revert g' o)) :
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g.toUInt256 A I = .ok (.revert g' o) :=
  Xi_revert_of_X (g := g.toUInt256) (by
    simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using h)

private theorem Xi_success_of_X_sat
    {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {s' o} {g : Sat256}
    (h : X (g.toNat + 1) (D_J I.code 0)
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
          = .ok (.success s' o)) :
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g.toUInt256 A I
      = .ok (.success (s'.createdAccounts, s'.accountMap, s'.machineState.gasAvailable.toUInt256,
                       s'.substate) o) :=
  Xi_success_of_X (g := g.toUInt256) (by
    simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using h)

/-- `RETURN`: terminate, returning `mem[off .. off+len]` (resolved to the literal `oval`).  Turns an
    `RD` cursor into the halting-success terminal `RDret`. -/
theorem RD.ret {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {off len : UInt256} {t : List UInt256} (mcost : ℕ) (oval : ByteArray)
    (h : RD code ee g s0 pc (off :: len :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.RETURN, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: len :: t →
        memoryExpansionCost s .RETURN = mcost)
    (hoval : mem.readWithPadding off.toNat len.toNat = oval)
    (hov : t.length ≤ 1024) :
    RDret code g s0 acc oval := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, _hrdata, hacc, _hee⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .RETURN = mcost := hmc s haw hstk
    have st := return_xstep hcode hpc hdec hstk hov
    rw [hmcS, show s.machineState.memory.readWithPadding off.toNat len.toNat = oval from by
      rw [hmem, hoval]] at st
    by_cases gg : g.toNat < C + mcost
    · exact Or.inl (RD.terminalOOG hgas st hk hC gg hX)
    · exact Or.inr ⟨stReturn s off len t, hX.trans (stepHaltSuccess hgas st hk (by omega)),
        by simp only [stReturn]; exact hacc⟩

/-- `STOP`: terminate with **empty** output (cost `Gzero = 0`).  Turns an `RD` cursor into the
    halting-success terminal `RDret … ByteArray.empty`. -/
theorem RD.stop {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.STOP, .none))
    (hov : stk.length ≤ 1024) :
    RDret code g s0 acc ByteArray.empty := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, _hmem, _haw, _hrdata, hacc, _hee⟩
  · exact Or.inl hoog
  · have st := stop_xstep hcode hpc hdec hstk hov
    refine Or.inr ⟨stStop s, hX.trans (stepHaltSuccess (cost := 0) hgas ?_ hk (by omega)),
      by simp only [stStop]; exact hacc⟩
    rw [if_neg (Nat.not_lt_zero _)]; exact st

/-- `REVERT`: terminate with a revert returning `mem[off .. off+len]`.  Turns an `RD` cursor into the
    halting-revert terminal `RDrev`. -/
theorem RD.rev {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {off len : UInt256} {t : List UInt256} (mcost : ℕ)
    (h : RD code ee g s0 pc (off :: len :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.REVERT, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = off :: len :: t →
        memoryExpansionCost s .REVERT = mcost)
    (hov : t.length ≤ 1024) :
    RDrev code g s0 := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, _hmem, haw, _hrdata, _hacc, _hee⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .REVERT = mcost := hmc s haw hstk
    have st := revert_xstep hcode hpc hdec hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + mcost
    · exact Or.inl (RD.terminalOOG hgas st hk hC gg hX)
    · exact Or.inr ⟨_, _, hX.trans (stepHaltRevert hgas st hk (by omega))⟩

/-! ## From RD terminals to Solm runtime-equivalence

`RDret`/`RDrev` record that the *whole* run `X (g+1) … (initState …)` halts.  These
eliminators carry that halting fact across the `X → Ξ` bridge (`Xi_*_of_X`) and into a
`runtimeEquivalenceFor` case, folding the out-of-gas alternative into `reEquiv_outOfGas`
*once*.  A revert/success segment therefore reaches the Solm layer compositionally — e.g.
`(powX_short …).reEquivNoDispatch hcode (powDispatch_none_short …)` — with no per-site
`rcases` / `Xi_*_of_X` / `reEquiv_*` plumbing.  All four are contract- and bytecode-generic
(`hcode : I.code = code` bridges the concrete bytecode back to `I.code`). -/

/-- Eliminate an `RDrev` into a `runtimeEquivalenceFor`: the OOG alternative becomes the
    `outOfGas` case automatically, and the continuation `k` receives the `Ξ`-level revert. -/
theorem RDrev.reEquivElim {cfg contract cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code)
    (h : RDrev code g (initState cA gh bl σ σ₀ g A I))
    (k : ∀ g' o, Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.revert g' o) →
          runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g.toUInt256 A I) :
    runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g.toUInt256 A I := by
  rcases h with hoog | ⟨g', o, hX⟩
  · exact reEquiv_outOfGas (Xi_error_of_X_sat (by rw [← hcode] at hoog; exact hoog))
  · exact k g' o (Xi_revert_of_X_sat (by rw [← hcode] at hX; exact hX))

/-- `RDrev ⇒ noDispatch`: the revert with Act failing to dispatch. -/
theorem RDrev.reEquivNoDispatch {cfg contract cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code) (h : RDrev code g (initState cA gh bl σ σ₀ g A I))
    (hd : dispatchMsg contract I.calldata = none) :
    runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g.toUInt256 A I :=
  h.reEquivElim hcode fun _ _ hrev => reEquiv_noDispatch hd hrev

/-- `RDrev ⇒ decodingFailed`: Act dispatches to `t` but calldata-decoding fails. -/
theorem RDrev.reEquivDecodingFailed {cfg contract cA gh bl σ σ₀ A I} {g : Sat256}
    {code : ByteArray} {t}
    (hcode : I.code = code) (h : RDrev code g (initState cA gh bl σ σ₀ g A I))
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldata (t.params.map Param.name) (transitionSignature t).paramTypes
              I.calldata = none) :
    runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g.toUInt256 A I :=
  h.reEquivElim hcode fun _ _ hrev => reEquiv_decodingFailed hd hdec hrev

/-- Eliminate an `RDret` into a `runtimeEquivalenceFor`: the OOG alternative becomes the
    `outOfGas` case automatically; the continuation `k` receives the `Ξ`-level success, with
    accounts already projected back to the carried `(cA, σ)`. -/
theorem RDret.reEquivElim {cfg contract cA gh bl σ σ₀ A I} {g : Sat256} {code o : ByteArray}
    (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ) o)
    (k : ∀ (g' : UInt256) (A' : Substate),
          Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA, σ, g', A') o) →
          runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g.toUInt256 A I) :
    runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g.toUInt256 A I := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact reEquiv_outOfGas (Xi_error_of_X_sat (by rw [← hcode] at hoog; exact hoog))
  · have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    have hxi := Xi_success_of_X_sat (by rw [← hcode] at hX; exact hX)
    rw [hcA, hσ] at hxi
    exact k _ _ hxi

/-! ## Callable interface — exposing a segment's raw `Ξ` result

`xiResult` turns an `RDret`/`RDrev` over `initState` into the `Ξ`-level disjunction (out-of-gas or
the concrete halt).  (Originally built for callee-correctness reuse; the external-call proof instead
treats the sub-call result as opaque, so this is currently unused — kept pending cleanup.) -/

/-- A success segment's **raw `Ξ` result**: either the run OOGs, or `Ξ` halts with success returning
    `o`, the accounts projected back to the carried `(cA, σ)`. -/
theorem RDret.xiResult {cA gh bl σ σ₀ A I} {g : Sat256} {code o : ByteArray}
    (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ) o) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass
    ∨ ∃ (g' : UInt256) (A' : Substate),
        Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA, σ, g', A') o) := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X_sat (by rw [← hcode] at hoog; exact hoog))
  · have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    have hxi := Xi_success_of_X_sat (by rw [← hcode] at hX; exact hX)
    rw [hcA, hσ] at hxi
    exact Or.inr ⟨_, _, hxi⟩

/-- A revert segment's **raw `Ξ` result**: either the run OOGs, or `Ξ` halts with a revert. -/
theorem RDrev.xiResult {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code)
    (h : RDrev code g (initState cA gh bl σ σ₀ g A I)) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass
    ∨ ∃ (g' : UInt256) (o : ByteArray), Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.revert g' o) := by
  rcases h with hoog | ⟨g', o, hX⟩
  · exact Or.inl (Xi_error_of_X_sat (by rw [← hcode] at hoog; exact hoog))
  · exact Or.inr ⟨g', o, Xi_revert_of_X_sat (by rw [← hcode] at hX; exact hX)⟩

/-! ## Spike acceptance: a 2-step fold closes a fixed-pc / fixed-stack conclusion -/

/-- JUMPDEST then SWAP1, fully abstract over the bytecode (decode facts supplied as
    hypotheses).  Confirms `conclude` produces the fixed `pc`/`stack` and the carried
    `memory`/`activeWords`/accounts preservation with no leftover goals. -/
example {code : ByteArray} {g : Sat256} {s0 s : State} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = ⟨10⟩)
    (hstk : s.machineState.stack = a :: b :: t)
    (hd0 : decode code ⟨10⟩ = some (.JUMPDEST, .none))
    (hd1 : decode code (⟨10⟩ + ⟨1⟩) = some (.SWAP1, .none))
    (hov : t.length + 2 ≤ 1024)
    (hgas : s.machineState.gasAvailable = g.subNat  C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J code 0) s0 = X (g.toNat + 1 - k) (D_J code 0) s)
    (hworld : RDWorld s0 s) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass
    ∨ ∃ (k' C' : ℕ) (s' : State),
        X (g.toNat + 1) (D_J code 0) s0 = X (g.toNat + 1 - k') (D_J code 0) s'
      ∧ s'.executionEnv.code = code ∧ s'.machineState.pc = ⟨10⟩ + ⟨1⟩ + ⟨1⟩
      ∧ s'.machineState.stack = b :: a :: t
      ∧ s'.machineState.gasAvailable = g.subNat  C' ∧ k' ≤ C' ∧ C' ≤ g.toNat
      ∧ s'.machineState.memory = s.machineState.memory
      ∧ s'.machineState.activeWords = s.machineState.activeWords
      ∧ s'.machineState.returnData = s.machineState.returnData
      ∧ (s'.createdAccounts, s'.accountMap) = (s.createdAccounts, s.accountMap) :=
  (RD.start hcode hpc hstk hgas hk hC hX hworld
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

/-- The recurring **memory-cost witness** every `mload`/`mstore`/`ret`/`rev` carries:
    `fun s haws hstks => …` proving `memoryExpansionCost s op = mcost` for the carried active-words
    `haws` and literal stack offset(s) in `hstks`.  Rewriting by `haws`/`hstks` reduces the cost to a
    closed term on literals, which `decide` evaluates — independent of the op, offset, and `mcost`. -/
macro "mem_cost" : term =>
  `(fun s haws hstks => by
      set_option linter.unusedSimpArgs false in
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
      decide)

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
