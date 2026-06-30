import Reasoning.Stepping
import Reasoning.Memory
import Ethereum.Theory.ReturnDataBound

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

/-- The EVM **reach-cursor**: the six fields `RD` pins on the underlying `State` at a program point —
    the transient machine state `pc`/`stack`/`mem`/`aw`/`rdata`, plus the persistent `world`
    (`createdAccounts × accountMap`, where contract storage lives).  `RDc` below is `RD` indexed by a
    `Cursor` instead of six loose arguments; eventually `RD` itself should take one. -/
structure Cursor where
  pc    : UInt256
  stack : List UInt256
  mem   : ByteArray
  aw    : UInt256
  rdata : ByteArray
  world : Batteries.RBSet AccountAddress compare × AccountMap

/-- `RD` indexed by a `Cursor` rather than six positional fields. -/
def RDc (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (cur : Cursor) (k C : ℕ) : Prop :=
  RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C

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

/-- Open the `RD` fold at a transaction's `initState`: the entry cursor at pc 0 with an empty stack,
    empty memory / return-data, zero active words, gas fully available (`C = 0`), and the genesis
    accounts `(cA, σ)`.  Every contract (runtime or constructor) begins its `evm_run` chain here;
    supersedes the hand-written `RD.start (s := initState …)` setup. -/
theorem RD.initState {code : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = code) :
    RD code I g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) ⟨0⟩ []
      ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 := by
  apply RD.start (s0 := Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
    (s := Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (code := code) (g := g)
  · simp [Reasoning.Theory.initState, hcode]
  · simp [Reasoning.Theory.initState]; rfl
  · simp [Reasoning.Theory.initState]; rfl
  · simp [Reasoning.Theory.initState]
  · omega
  · omega
  · simp
  · simp [RDWorld]

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

theorem RD.dup9 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP9, .none)) (hov : t.length + 10 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (ii :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup9_xstep hc hp hdec hs hov)

theorem RD.dup10 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP10, .none)) (hov : t.length + 11 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (jj :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup10_xstep hc hp hdec hs hov)

theorem RD.dup11 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP11, .none)) (hov : t.length + 12 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (kk :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup11_xstep hc hp hdec hs hov)

theorem RD.dup13 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP13, .none)) (hov : t.length + 14 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (mm :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup13_xstep hc hp hdec hs hov)

theorem RD.dup14 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP14, .none)) (hov : t.length + 15 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (nn :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup14_xstep hc hp hdec hs hov)

theorem RD.dup15 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn oo : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP15, .none)) (hov : t.length + 16 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (oo :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup15_xstep hc hp hdec hs hov)

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

/-- `CODESIZE` pushes the size of the current code bytearray. -/
theorem RD.codesize {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.CODESIZE, .none)) (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.ofNat code.size :: stk) mem aw rdata acc
      (k + 1) (C + 2) := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact (by unfold RD; exact Or.inl hoog)
  · have st := codesize_xstep hcode hpc hdec hstk hov
    rw [show UInt256.ofNat code.size = UInt256.ofNat s.executionEnv.code.size from by rw [hcode]]
    unfold RD
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stCodesize s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stCodesize]; exact hcode
      · simp only [stCodesize]; rw [hpc]
      · simp only [stCodesize]; rw [hcode, hstk]
      · simp only [stCodesize]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stCodesize]; exact hmem
      · simp only [stCodesize]; exact haw
      · simp only [stCodesize]; exact hrdata
      · simp only [stCodesize]; exact hacc
      · exact hee
      · exact hworld

set_option maxHeartbeats 1000000 in
theorem RD.returndatacopy {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256} (mcost : ℕ)
    (memout : ByteArray) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.RETURNDATACOPY, .none))
    (hguard : b.toNat + c.toNat ≤ rdata.size)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: t →
        memoryExpansionCost s .RETURNDATACOPY = mcost)
    (hmemout : rdata.write b.toNat mem a.toNat c.toNat = memout)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat c.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t memout awout rdata acc
      (k + 1)
      (C + (mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee,
    hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .RETURNDATACOPY = mcost := hmc s haw hstk
    have hmemok : ¬ b.toNat + c.toNat > s.machineState.returnData.size := by
      rw [hrdata]
      omega
    have st := returndatacopy_xstep hcode hpc hdec hstk hmemok hov
    rw [hmcS] at st
    rw [collapse_two_stage] at st
    by_cases gg :
        g.toNat < C + (mcost +
          (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · have hcost_pos :
          0 < mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)) := by
        simp [GasConstants.Gverylow]
      refine Or.inr ⟨stReturndatacopy s a b c t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stReturndatacopy]; exact hcode
      · simp only [stReturndatacopy]; rw [hpc]
      · rfl
      · simp only [stReturndatacopy, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stReturndatacopy]; rw [hmem, hrdata, hmemout]
      · simp only [stReturndatacopy]; rw [haw, hawout]
      · simp only [stReturndatacopy]; exact hrdata
      · simp only [stReturndatacopy]; exact hacc
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

/-- Width-generic `PUSHk` (`k ≥ 1`): pushes `argv`, advancing `pc` by `width + 1` (read from the
    decode fact), cost `3`.  Lets a generic dispatcher fold push a jump target without forking on
    `PUSH1`/`PUSH2` — `RD.push1`/`RD.push2` are the fixed-width specializations. -/
theorem RD.pushConst {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C) (argv : UInt256) {width : ℕ}
    {op : Operation.POp} (hop : op ≠ .PUSH0)
    (hdec : decode code pc = some (.Push op, some (argv, width)))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + UInt256.ofNat width.succ) (argv :: stk) mem aw rdata acc (k + 1) (C + 3) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := pushConst_xstep hcode hpc hop hdec hstk hov
    by_cases gg : g.toNat < C + 3
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stPushConst s argv width,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stPushConst]; exact hcode
      · simp only [stPushConst]; rw [hpc]
      · simp only [stPushConst]; rw [hstk]
      · simp only [stPushConst]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stPushConst]; exact hmem
      · simp only [stPushConst]; exact haw
      · simp only [stPushConst]; exact hrdata
      · simp only [stPushConst]; exact hacc
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

theorem RD.gt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.GT, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.gt a b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => gt_xstep hc hp hdec hs hov)

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

theorem RD.sgt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SGT, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.sgt a b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => sgt_xstep hc hp hdec hs hov)

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

theorem RD.lor {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.OR, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.lor a b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => or_xstep hc hp hdec hs hov)

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

/-- `DIV` is cost 5 (`stMul`), so it does not share the `stBinop` helper. -/
theorem RD.div {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DIV, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.div a b :: t) mem aw rdata acc (k + 1) (C + 5) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := div_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 5
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stMul s (UInt256.div a b) t,
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

theorem RD.timestamp {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.TIMESTAMP, .none))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.ofNat ee.header.timestamp :: stk) mem aw rdata acc
      (k + 1) (C + 2) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := timestamp_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stTimestamp s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stTimestamp]; exact hcode
      · simp only [stTimestamp]; rw [hpc]
      · simp only [stTimestamp]; rw [hee, hstk]
      · simp only [stTimestamp]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stTimestamp]; exact hmem
      · simp only [stTimestamp]; exact haw
      · simp only [stTimestamp]; exact hrdata
      · simp only [stTimestamp]; exact hacc
      · exact hee
      · exact hworld

theorem RD.chainid {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.CHAINID, .none))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.ofNat Ethereum.chainId :: stk) mem aw rdata acc
      (k + 1) (C + 2) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := chainid_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stChainid s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stChainid]; exact hcode
      · simp only [stChainid]; rw [hpc]
      · simp only [stChainid]; rw [hstk]
      · simp only [stChainid]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stChainid]; exact hmem
      · simp only [stChainid]; exact haw
      · simp only [stChainid]; exact hrdata
      · simp only [stChainid]; exact hacc
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

/-- `CALLDATACOPY`: pops destination, calldata offset, and length; copies calldata bytes into memory. -/
theorem RD.calldatacopy {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256} (mcost : ℕ)
    (memout : ByteArray) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.CALLDATACOPY, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: c :: t →
        memoryExpansionCost s .CALLDATACOPY = mcost)
    (hmemout : ee.calldata.write b.toNat mem a.toNat c.toNat = memout)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat c.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t memout awout rdata acc
      (k + 1) (C + (mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .CALLDATACOPY = mcost := hmc s haw hstk
    have st := calldatacopy_xstep hcode hpc hdec hstk hov
    rw [hmcS] at st
    rw [collapse_two_stage] at st
    by_cases gg : g.toNat < C + (mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · have hcost_pos :
          0 < mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)) := by
        simp [GasConstants.Gverylow]
      refine Or.inr ⟨stCalldatacopy s a b c t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stCalldatacopy]; exact hcode
      · simp only [stCalldatacopy]; rw [hpc]
      · rfl
      · simp only [stCalldatacopy, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stCalldatacopy]; rw [hee, hmem, hmemout]
      · simp only [stCalldatacopy]; rw [haw, hawout]
      · simp only [stCalldatacopy]; exact hrdata
      · simp only [stCalldatacopy]; exact hacc
      · exact hee
      · exact hworld

/-- `CODECOPY`: pops destination, code offset, and length; copies code bytes into memory. -/
theorem RD.codecopy {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256} (mcost : ℕ)
    (memout : ByteArray) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.CODECOPY, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: c :: t →
        memoryExpansionCost s .CODECOPY = mcost)
    (hmemout : code.write b.toNat mem a.toNat c.toNat = memout)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat c.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t memout awout rdata acc
      (k + 1) (C + (mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .CODECOPY = mcost := hmc s haw hstk
    have st := codecopy_xstep hcode hpc hdec hstk hov
    rw [hmcS] at st
    rw [collapse_two_stage] at st
    by_cases gg : g.toNat < C + (mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · have hcost_pos :
          0 < mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)) := by
        simp [GasConstants.Gverylow]
      refine Or.inr ⟨stCodecopy s a b c t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stCodecopy]; exact hcode
      · simp only [stCodecopy]; rw [hpc]
      · rfl
      · simp only [stCodecopy, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stCodecopy]; rw [hcode, hmem, hmemout]
      · simp only [stCodecopy]; rw [haw, hawout]
      · simp only [stCodecopy]; exact hrdata
      · simp only [stCodecopy]; exact hacc
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

/-- `Θ` return data is word-size-bounded when the calldata supplied to `Θ` is word-size-bounded.
    The only remaining trusted base is evmlean's opaque-precompile case; interpreted bytecode is
    proved in `Ethereum.Theory.ReturnDataBound`. -/
theorem Theta_returnData_size_lt
    (blob : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (c : ToExecute) (g p v v' : UInt256) (d : ByteArray)
    (e : Fin 1025) (H : BlockHeader) (w : Bool) (hd : d.size < UInt256.size) :
    (Ethereum.EVM.Θ blob cA gh blocks σ σ₀ A s o r c g p v v' d e H w).2.2.2.2.2.size <
      UInt256.size :=
  Ethereum.EVM.theta_projection_output_size_lt_uint256 blob cA gh blocks σ σ₀ A s o r c d
    g p v v' e H w hd

/-- Tight `Θ` return-data bound, pending the generic gas-derived EVM proof. -/
axiom Theta_returnData_size_lt_2pow138
    (blob : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (c : ToExecute) (g p v v' : UInt256) (d : ByteArray)
    (e : Fin 1025) (H : BlockHeader) (w : Bool) (hd : d.size < UInt256.size) :
    (Ethereum.EVM.Θ blob cA gh blocks σ σ₀ A s o r c g p v v' d e H w).2.2.2.2.2.size <
      2 ^ 138

theorem Theta_returnData_size_lt_2pow138_of_eq
    (blob : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (c : ToExecute) (g p v v' : UInt256) (d : ByteArray)
    (e : Fin 1025) (H : BlockHeader) (w : Bool)
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {g' : UInt256} {A' : Substate} {z : Bool} {out : ByteArray}
    (hΘ : (cA', σ', g', A', z, out) =
      Ethereum.EVM.Θ blob cA gh blocks σ σ₀ A s o r c g p v v' d e H w)
    (hd : d.size < UInt256.size) :
    out.size < 2 ^ 138 := by
  have htheta :=
    Theta_returnData_size_lt_2pow138 blob cA gh blocks σ σ₀ A s o r c g p v v' d e H w hd
  rw [← hΘ] at htheta
  simpa using htheta

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

/-- **SWAP5**: exchange the stack top with the 6th element (cost `Gverylow = 3`, pc += 1). -/
theorem RD.swap5 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP5, .none)) (hov : t.length + 6 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (f :: b :: c :: d :: e :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap5_xstep hc hp hdec hs hov)

/-- **SWAP6**: exchange the stack top with the 7th element (cost `Gverylow = 3`, pc += 1). -/
theorem RD.swap6 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP6, .none)) (hov : t.length + 7 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (gg :: b :: c :: d :: e :: f :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap6_xstep hc hp hdec hs hov)

/-- **SWAP7**: exchange the stack top with the 8th element (cost `Gverylow = 3`, pc += 1). -/
theorem RD.swap7 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: h :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP7, .none)) (hov : t.length + 8 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (h :: b :: c :: d :: e :: f :: gg :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap7_xstep hc hp hdec hs hov)

theorem RD.swap8 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP8, .none)) (hov : t.length + 9 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (ii :: b :: c :: d :: e :: f :: gg :: hh :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap8_xstep hc hp hdec hs hov)

theorem RD.swap10 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP10, .none)) (hov : t.length + 11 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (kk :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap10_xstep hc hp hdec hs hov)

theorem RD.swap11 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP11, .none)) (hov : t.length + 12 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (ll :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap11_xstep hc hp hdec hs hov)

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

/-- **LOG1**: pop `[offset, size, t1]`, append a log over `mem[offset..offset+size]` with one topic
    (cost `memExp + Glog + Glogdata·size + Glogtopic`, pc += 1).  Requires `ee.perm` (aborts in
    static mode).  The `substate.logSeries` append is invisible to `RD`. -/
theorem RD.log1 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG1, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: t →
        memoryExpansionCost s .LOG1 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG1 = mcost := hmc s haw hstk
    have hperms : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have st := log1_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stLog1 s a b c t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stLog1]; exact hcode
      · simp only [stLog1]; rw [hpc]
      · simp only [stLog1]
      · simp only [stLog1, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stLog1]; exact hmem
      · simp only [stLog1]; rw [haw, hawout]
      · simp only [stLog1]; exact hrdata
      · simp only [stLog1]; exact hacc
      · simp only [stLog1]; exact hee
      · simp only [stLog1]; exact hworld

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

/-- **LOG4**: pop `[offset, size, t1, t2, t3, t4]`, append a log over
    `mem[offset..offset+size]` with the four topics
    (cost `memExp + Glog + Glogdata·size + 4·Glogtopic`, pc += 1).  Requires `ee.perm`
    (aborts in static mode).  The `substate.logSeries` append is invisible to `RD`. -/
theorem RD.log4 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG4, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: e :: f :: t →
        memoryExpansionCost s .LOG4 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 4 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata,
      hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG4 = mcost := hmc s haw hstk
    have hperms : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have st := log4_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 4 * GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stLog4 s a b c d e f t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stLog4]; exact hcode
      · simp only [stLog4]; rw [hpc]
      · simp only [stLog4]
      · simp only [stLog4, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stLog4]; exact hmem
      · simp only [stLog4]; rw [haw, hawout]
      · simp only [stLog4]; exact hrdata
      · simp only [stLog4]; exact hacc
      · simp only [stLog4]; exact hee
      · simp only [stLog4]; exact hworld

/-! ## Selector-dispatch arm — one `DUP1; PUSH4 selᵢ; EQ; PUSHk tgtᵢ; JUMPI`

A solc dispatcher is a chain of these arms.  Each consumes the 5 opcodes width-generically (the
target push via `pushConst`); the EQ outcome (`UInt256.eq selᵢ selWord`) decides taken vs. fall-
through, supplied as a hypothesis so the arm stays a pure opcode lemma — `evmSelectorDecode` couples
that outcome to `selᵢBytes == calldata[0:4]` at the call site.  Decode facts are stated at the
*threaded* pcs the chain produces (so the proof unifies with no normalization); a concrete caller
discharges each with `by decide`. -/

/-- The pcs within one selector arm starting at `armPc` with a width-`w` target push: the `PUSH4`,
    `EQ`, target-`PUSH`, and `JUMPI` positions, and `selArmNext` the fall-through (next arm) pc.
    Reducible, so the decode hypotheses read cleanly while the chain still unifies definitionally. -/
@[reducible] def selArmPush4Pc (armPc : UInt256) : UInt256 := armPc + ⟨1⟩
@[reducible] def selArmEqPc (armPc : UInt256) : UInt256 := armPc + ⟨1⟩ + UInt256.ofNat 5
@[reducible] def selArmPushTgtPc (armPc : UInt256) : UInt256 := armPc + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩
@[reducible] def selArmJumpiPc (armPc : UInt256) (w : ℕ) : UInt256 :=
  armPc + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat w.succ
@[reducible] def selArmNextPc (armPc : UInt256) (w : ℕ) : UInt256 :=
  armPc + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat w.succ + ⟨1⟩

/-- Arm **taken** (`EQ ≠ 0`): jump to the matched body entry `tgt`, decoded selector word preserved. -/
theorem RD.selectorArmTaken {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {armPc selWord selNat tgt : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {width : ℕ} {op : Operation.POp} {rest : List UInt256}
    (h : RD code ee g s0 armPc (selWord :: rest) mem aw rdata acc k C)
    (hdup : decode code armPc = some (.DUP1, .none))
    (hpush4 : decode code (selArmPush4Pc armPc) = some (.Push .PUSH4, some (selNat, 4)))
    (heq : decode code (selArmEqPc armPc) = some (.EQ, .none))
    (hop : op ≠ .PUSH0)
    (hpushT : decode code (selArmPushTgtPc armPc) = some (.Push op, some (tgt, width)))
    (hjumpi : decode code (selArmJumpiPc armPc width) = some (.JUMPI, .none))
    (hb : UInt256.eq selNat selWord ≠ ⟨0⟩) (hjd : (D_J code 0).contains tgt = true)
    (hov : rest.length + 3 ≤ 1024) :
    RD code ee g s0 tgt (selWord :: rest) mem aw rdata acc (k + 5) (C + 22) :=
  h.dup1 hdup (by omega)
   |>.push4 selNat hpush4 (by simp only [List.length_cons]; omega)
   |>.eq heq (by simp only [List.length_cons]; omega)
   |>.pushConst tgt hop hpushT (by simp only [List.length_cons]; omega)
   |>.jumpiT hjumpi hb hjd (by simp only [List.length_cons]; omega)

/-- Arm **not taken** (`EQ = 0`): fall through to the next arm (`selArmNextPc`), selector word kept. -/
theorem RD.selectorArmNotTaken {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {armPc selWord selNat tgt : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {width : ℕ} {op : Operation.POp} {rest : List UInt256}
    (h : RD code ee g s0 armPc (selWord :: rest) mem aw rdata acc k C)
    (hdup : decode code armPc = some (.DUP1, .none))
    (hpush4 : decode code (selArmPush4Pc armPc) = some (.Push .PUSH4, some (selNat, 4)))
    (heq : decode code (selArmEqPc armPc) = some (.EQ, .none))
    (hop : op ≠ .PUSH0)
    (hpushT : decode code (selArmPushTgtPc armPc) = some (.Push op, some (tgt, width)))
    (hjumpi : decode code (selArmJumpiPc armPc width) = some (.JUMPI, .none))
    (hb : UInt256.eq selNat selWord = ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD code ee g s0 (selArmNextPc armPc width) (selWord :: rest) mem aw rdata acc (k + 5) (C + 22) :=
  h.dup1 hdup (by omega)
   |>.push4 selNat hpush4 (by simp only [List.length_cons]; omega)
   |>.eq heq (by simp only [List.length_cons]; omega)
   |>.pushConst tgt hop hpushT (by simp only [List.length_cons]; omega)
   |>.jumpiNT hjumpi hb (by simp only [List.length_cons]; omega)

/-! ### Auto arms — selector/target read from the bytecode (width-generic)

The `selectorArm*` lemmas take `selNat`/`tgt`/`op`/`width` explicitly because `by decide` can't
infer them inside a decode metavariable.  These wrappers **extract** them from the bytecode
(`pushAt` reads a `PUSH`'s op/value/width), so a caller supplies only the running cursor and `by
decide` for each decode fact — no per-arm `(selNat := …) (tgt := …) (op := …) (width := …)`.  The
target push width stays generic (`PUSH1` for `Truth`, `PUSH2` for the rest), read from the bytecode. -/

/-- The `(op, value, width)` of a `PUSH` decoded at `pc` (junk fallback for a non-push). -/
def pushAt (code : ByteArray) (pc : UInt256) : Operation.POp × UInt256 × ℕ :=
  match decode code pc with
  | some (.Push op, some (v, w)) => (op, v, w)
  | _ => (.PUSH1, ⟨0⟩, 1)

/-- The arm's `PUSH4` selector value, read from the bytecode. -/
@[reducible] def armSelNat (code : ByteArray) (armPc : UInt256) : UInt256 :=
  (pushAt code (selArmPush4Pc armPc)).2.1
/-- The arm's target-push opcode (`PUSH1`/`PUSH2`/…), read from the bytecode. -/
@[reducible] def armTgtOp (code : ByteArray) (armPc : UInt256) : Operation.POp :=
  (pushAt code (selArmPushTgtPc armPc)).1
/-- The arm's jump target (the function body entry), read from the bytecode. -/
@[reducible] def armTgt (code : ByteArray) (armPc : UInt256) : UInt256 :=
  (pushAt code (selArmPushTgtPc armPc)).2.1
/-- The arm's target-push width (`1`/`2`), read from the bytecode. -/
@[reducible] def armTgtWidth (code : ByteArray) (armPc : UInt256) : ℕ :=
  (pushAt code (selArmPushTgtPc armPc)).2.2

/-- An arm at `armPc` is **well-formed**: decodes as `DUP1; PUSH4 selᵢ; EQ; PUSHk tgtᵢ; JUMPI`
    (selector/target/op/width read from the bytecode).  Bundling the six decode facts lets a caller
    discharge them with a single `by decide` and a dispatcher fold carry `∀ arm, armWellFormed`. -/
@[reducible] def armWellFormed (code : ByteArray) (armPc : UInt256) : Prop :=
  decode code armPc = some (.DUP1, .none)
  ∧ decode code (selArmPush4Pc armPc) = some (.Push .PUSH4, some (armSelNat code armPc, 4))
  ∧ decode code (selArmEqPc armPc) = some (.EQ, .none)
  ∧ armTgtOp code armPc ≠ .PUSH0
  ∧ decode code (selArmPushTgtPc armPc)
      = some (.Push (armTgtOp code armPc), some (armTgt code armPc, armTgtWidth code armPc))
  ∧ decode code (selArmJumpiPc armPc (armTgtWidth code armPc)) = some (.JUMPI, .none)

/-- Arm **taken**, opcode facts bundled as `armWellFormed` (one `by decide`). -/
theorem RD.selectorArmTakenAuto {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {armPc selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ} {rest : List UInt256}
    (h : RD code ee g s0 armPc (selWord :: rest) mem aw rdata acc k C)
    (hwf : armWellFormed code armPc)
    (hb : UInt256.eq (armSelNat code armPc) selWord ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains (armTgt code armPc) = true)
    (hov : rest.length + 3 ≤ 1024) :
    RD code ee g s0 (armTgt code armPc) (selWord :: rest) mem aw rdata acc (k + 5) (C + 22) := by
  obtain ⟨hdup, hpush4, heq, hopT, hpushT, hjumpi⟩ := hwf
  exact h.selectorArmTaken hdup hpush4 heq hopT hpushT hjumpi hb hjd hov

/-- Arm **not taken**, opcode facts bundled as `armWellFormed` (fall through to the next arm). -/
theorem RD.selectorArmNotTakenAuto {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {armPc selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ} {rest : List UInt256}
    (h : RD code ee g s0 armPc (selWord :: rest) mem aw rdata acc k C)
    (hwf : armWellFormed code armPc)
    (hb : UInt256.eq (armSelNat code armPc) selWord = ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD code ee g s0 (selArmNextPc armPc (armTgtWidth code armPc)) (selWord :: rest)
      mem aw rdata acc (k + 5) (C + 22) := by
  obtain ⟨hdup, hpush4, heq, hopT, hpushT, hjumpi⟩ := hwf
  exact h.selectorArmNotTaken hdup hpush4 heq hopT hpushT hjumpi hb hov

/-! ### Width-generic selector arms

Solc can encode a selector with fewer than four pushed bytes when the high selector byte is zero.
The arm shape is still `DUP1; PUSHw selᵢ; EQ; PUSHk tgtᵢ; JUMPI`; only the selector push width
changes. -/

@[reducible] def selArmPushSelPcW (armPc : UInt256) : UInt256 := armPc + ⟨1⟩
@[reducible] def selArmEqPcW (armPc : UInt256) (selWidth : ℕ) : UInt256 :=
  selArmPushSelPcW armPc + UInt256.ofNat selWidth.succ
@[reducible] def selArmPushTgtPcW (armPc : UInt256) (selWidth : ℕ) : UInt256 :=
  selArmEqPcW armPc selWidth + ⟨1⟩
@[reducible] def selArmJumpiPcW (armPc : UInt256) (selWidth tgtWidth : ℕ) : UInt256 :=
  selArmPushTgtPcW armPc selWidth + UInt256.ofNat tgtWidth.succ
@[reducible] def selArmNextPcW (armPc : UInt256) (selWidth tgtWidth : ℕ) : UInt256 :=
  selArmJumpiPcW armPc selWidth tgtWidth + ⟨1⟩

@[reducible] def armSelNatW (code : ByteArray) (armPc : UInt256) : UInt256 :=
  (pushAt code (selArmPushSelPcW armPc)).2.1
@[reducible] def armSelOpW (code : ByteArray) (armPc : UInt256) : Operation.POp :=
  (pushAt code (selArmPushSelPcW armPc)).1
@[reducible] def armTgtOpW (code : ByteArray) (armPc : UInt256) (selWidth : ℕ) :
    Operation.POp :=
  (pushAt code (selArmPushTgtPcW armPc selWidth)).1
@[reducible] def armTgtW (code : ByteArray) (armPc : UInt256) (selWidth : ℕ) : UInt256 :=
  (pushAt code (selArmPushTgtPcW armPc selWidth)).2.1
@[reducible] def armTgtWidthW (code : ByteArray) (armPc : UInt256) (selWidth : ℕ) : ℕ :=
  (pushAt code (selArmPushTgtPcW armPc selWidth)).2.2

@[reducible] def armWellFormedW (code : ByteArray) (armPc : UInt256) (selWidth : ℕ) : Prop :=
  decode code armPc = some (.DUP1, .none)
  ∧ armSelOpW code armPc ≠ .PUSH0
  ∧ decode code (selArmPushSelPcW armPc)
      = some (.Push (armSelOpW code armPc), some (armSelNatW code armPc, selWidth))
  ∧ decode code (selArmEqPcW armPc selWidth) = some (.EQ, .none)
  ∧ armTgtOpW code armPc selWidth ≠ .PUSH0
  ∧ decode code (selArmPushTgtPcW armPc selWidth)
      = some (.Push (armTgtOpW code armPc selWidth),
          some (armTgtW code armPc selWidth, armTgtWidthW code armPc selWidth))
  ∧ decode code (selArmJumpiPcW armPc selWidth (armTgtWidthW code armPc selWidth))
      = some (.JUMPI, .none)

theorem RD.selectorArmWidthTakenAuto {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {armPc selWord : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {rest : List UInt256} (selWidth : ℕ)
    (h : RD code ee g s0 armPc (selWord :: rest) mem aw rdata acc k C)
    (hwf : armWellFormedW code armPc selWidth)
    (hb : UInt256.eq (armSelNatW code armPc) selWord ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains (armTgtW code armPc selWidth) = true)
    (hov : rest.length + 3 ≤ 1024) :
    RD code ee g s0 (armTgtW code armPc selWidth) (selWord :: rest)
      mem aw rdata acc (k + 5) (C + 22) := by
  obtain ⟨hdup, hopSel, hpushSel, heq, hopT, hpushT, hjumpi⟩ := hwf
  exact h.dup1 hdup (by omega)
    |>.pushConst (armSelNatW code armPc) hopSel hpushSel
        (by simp only [List.length_cons]; omega)
    |>.eq heq (by simp only [List.length_cons]; omega)
    |>.pushConst (armTgtW code armPc selWidth) hopT hpushT
        (by simp only [List.length_cons]; omega)
    |>.jumpiT hjumpi hb hjd (by simp only [List.length_cons]; omega)

theorem RD.selectorArmWidthNotTakenAuto {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {armPc selWord : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {rest : List UInt256} (selWidth : ℕ)
    (h : RD code ee g s0 armPc (selWord :: rest) mem aw rdata acc k C)
    (hwf : armWellFormedW code armPc selWidth)
    (hb : UInt256.eq (armSelNatW code armPc) selWord = ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD code ee g s0
      (selArmNextPcW armPc selWidth (armTgtWidthW code armPc selWidth))
      (selWord :: rest) mem aw rdata acc (k + 5) (C + 22) := by
  obtain ⟨hdup, hopSel, hpushSel, heq, hopT, hpushT, hjumpi⟩ := hwf
  exact h.dup1 hdup (by omega)
    |>.pushConst (armSelNatW code armPc) hopSel hpushSel
        (by simp only [List.length_cons]; omega)
    |>.eq heq (by simp only [List.length_cons]; omega)
    |>.pushConst (armTgtW code armPc selWidth) hopT hpushT
        (by simp only [List.length_cons]; omega)
    |>.jumpiNT hjumpi hb (by simp only [List.length_cons]; omega)

/-! ### Selector split — one `DUP1; PUSH4 pivot; GT; PUSHk tgt; JUMPI`

Solc switches from a linear selector chain to a binary-search split for larger contracts.  The
shape is identical to a selector arm except the comparison is `GT` rather than `EQ`; the boolean is
therefore `UInt256.gt pivot selWord`. -/

/-- A binary-search selector split at `splitPc` is well-formed:
    `DUP1; PUSH4 pivot; GT; PUSHk tgt; JUMPI`. -/
@[reducible] def selectorSplitWellFormed (code : ByteArray) (splitPc : UInt256) : Prop :=
  decode code splitPc = some (.DUP1, .none)
  ∧ decode code (selArmPush4Pc splitPc)
      = some (.Push .PUSH4, some (armSelNat code splitPc, 4))
  ∧ decode code (selArmEqPc splitPc) = some (.GT, .none)
  ∧ armTgtOp code splitPc ≠ .PUSH0
  ∧ decode code (selArmPushTgtPc splitPc)
      = some (.Push (armTgtOp code splitPc), some (armTgt code splitPc, armTgtWidth code splitPc))
  ∧ decode code (selArmJumpiPc splitPc (armTgtWidth code splitPc)) = some (.JUMPI, .none)

/-- Selector split **taken** (`pivot > selWord`): jump to the low-half target. -/
theorem RD.selectorSplitTaken {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {splitPc selWord pivot tgt : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {width : ℕ} {op : Operation.POp} {rest : List UInt256}
    (h : RD code ee g s0 splitPc (selWord :: rest) mem aw rdata acc k C)
    (hdup : decode code splitPc = some (.DUP1, .none))
    (hpush4 : decode code (selArmPush4Pc splitPc) = some (.Push .PUSH4, some (pivot, 4)))
    (hgt : decode code (selArmEqPc splitPc) = some (.GT, .none))
    (hop : op ≠ .PUSH0)
    (hpushT : decode code (selArmPushTgtPc splitPc) = some (.Push op, some (tgt, width)))
    (hjumpi : decode code (selArmJumpiPc splitPc width) = some (.JUMPI, .none))
    (hb : UInt256.gt pivot selWord ≠ ⟨0⟩) (hjd : (D_J code 0).contains tgt = true)
    (hov : rest.length + 3 ≤ 1024) :
    RD code ee g s0 tgt (selWord :: rest) mem aw rdata acc (k + 5) (C + 22) :=
  h.dup1 hdup (by omega)
   |>.push4 pivot hpush4 (by simp only [List.length_cons]; omega)
   |>.gt hgt (by simp only [List.length_cons]; omega)
   |>.pushConst tgt hop hpushT (by simp only [List.length_cons]; omega)
   |>.jumpiT hjumpi hb hjd (by simp only [List.length_cons]; omega)

/-- Selector split **not taken** (`pivot > selWord = 0`): fall through to the high half. -/
theorem RD.selectorSplitNotTaken {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {splitPc selWord pivot tgt : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {width : ℕ} {op : Operation.POp} {rest : List UInt256}
    (h : RD code ee g s0 splitPc (selWord :: rest) mem aw rdata acc k C)
    (hdup : decode code splitPc = some (.DUP1, .none))
    (hpush4 : decode code (selArmPush4Pc splitPc) = some (.Push .PUSH4, some (pivot, 4)))
    (hgt : decode code (selArmEqPc splitPc) = some (.GT, .none))
    (hop : op ≠ .PUSH0)
    (hpushT : decode code (selArmPushTgtPc splitPc) = some (.Push op, some (tgt, width)))
    (hjumpi : decode code (selArmJumpiPc splitPc width) = some (.JUMPI, .none))
    (hb : UInt256.gt pivot selWord = ⟨0⟩) (hov : rest.length + 3 ≤ 1024) :
    RD code ee g s0 (selArmNextPc splitPc width) (selWord :: rest)
      mem aw rdata acc (k + 5) (C + 22) :=
  h.dup1 hdup (by omega)
   |>.push4 pivot hpush4 (by simp only [List.length_cons]; omega)
   |>.gt hgt (by simp only [List.length_cons]; omega)
   |>.pushConst tgt hop hpushT (by simp only [List.length_cons]; omega)
   |>.jumpiNT hjumpi hb (by simp only [List.length_cons]; omega)

/-- Selector split **taken**, with opcode facts bundled as `selectorSplitWellFormed`. -/
theorem RD.selectorSplitTakenAuto {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {splitPc selWord : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {rest : List UInt256}
    (h : RD code ee g s0 splitPc (selWord :: rest) mem aw rdata acc k C)
    (hwf : selectorSplitWellFormed code splitPc)
    (hb : UInt256.gt (armSelNat code splitPc) selWord ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains (armTgt code splitPc) = true)
    (hov : rest.length + 3 ≤ 1024) :
    RD code ee g s0 (armTgt code splitPc) (selWord :: rest)
      mem aw rdata acc (k + 5) (C + 22) := by
  obtain ⟨hdup, hpush4, hgt, hopT, hpushT, hjumpi⟩ := hwf
  exact h.selectorSplitTaken hdup hpush4 hgt hopT hpushT hjumpi hb hjd hov

/-- Selector split **not taken**, with opcode facts bundled as `selectorSplitWellFormed`. -/
theorem RD.selectorSplitNotTakenAuto {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {splitPc selWord : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {rest : List UInt256}
    (h : RD code ee g s0 splitPc (selWord :: rest) mem aw rdata acc k C)
    (hwf : selectorSplitWellFormed code splitPc)
    (hb : UInt256.gt (armSelNat code splitPc) selWord = ⟨0⟩)
    (hov : rest.length + 3 ≤ 1024) :
    RD code ee g s0 (selArmNextPc splitPc (armTgtWidth code splitPc)) (selWord :: rest)
      mem aw rdata acc (k + 5) (C + 22) := by
  obtain ⟨hdup, hpush4, hgt, hopT, hpushT, hjumpi⟩ := hwf
  exact h.selectorSplitNotTaken hdup hpush4 hgt hopT hpushT hjumpi hb hov

/-- The pc of the `n`-th arm from `start`, each arm's width read from the bytecode (so it threads
    `PUSH1` and `PUSH2` target arms alike). -/
def nthArmPc (code : ByteArray) (start : UInt256) : ℕ → UInt256
  | 0 => start
  | n + 1 => nthArmPc code (selArmNextPc start (armTgtWidth code start)) n

/-- **Dispatcher fold.**  From the first arm with the selector word on top, skip arms `0 … i-1`
    (`heq0`: none match) and take arm `i` (`htake`: it matches), reaching its body entry `bodyPC`.
    The per-arm opcode facts are the single `∀`-hypothesis `hwf` — at a concrete call discharged by
    one `intro/interval_cases/decide`, replacing six `by decide`s per arm. -/
theorem RD.dispatchTo {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {selWord : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {rest : List UInt256}
    (bodyPC : UInt256) :
    ∀ (i : ℕ) {start : UInt256} {k C : ℕ}
      (_ : RD code ee g s0 start (selWord :: rest) mem aw rdata acc k C)
      (_ : ∀ j, j ≤ i → armWellFormed code (nthArmPc code start j))
      (_ : ∀ j, j < i → UInt256.eq (armSelNat code (nthArmPc code start j)) selWord = ⟨0⟩)
      (_ : UInt256.eq (armSelNat code (nthArmPc code start i)) selWord ≠ ⟨0⟩)
      (_ : (D_J code 0).contains (armTgt code (nthArmPc code start i)) = true)
      (_ : armTgt code (nthArmPc code start i) = bodyPC)
      (_ : rest.length + 3 ≤ 1024),
      ∃ k' C', RD code ee g s0 bodyPC (selWord :: rest) mem aw rdata acc k' C' := by
  intro i
  induction i with
  | zero =>
    intro start k C h hwf _ htake hjd hbody hov
    have key : RD code ee g s0 bodyPC (selWord :: rest) mem aw rdata acc (k + 5) (C + 22) := by
      have hbody' : armTgt code start = bodyPC := hbody
      rw [← hbody']
      exact h.selectorArmTakenAuto (hwf 0 (le_refl 0)) htake hjd hov
    exact ⟨_, _, key⟩
  | succ n ih =>
    intro start k C h hwf heq0 htake hjd hbody hov
    exact ih (h.selectorArmNotTakenAuto (hwf 0 (Nat.zero_le _)) (heq0 0 (Nat.succ_pos n)) hov)
      (fun j hj => hwf (j + 1) (by omega)) (fun j hj => heq0 (j + 1) (by omega))
      htake hjd hbody hov


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
          o (cA', σ') k' C'
      ∧ o.size < UInt256.size := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · -- OOG: default witnesses; the Θ-link is tuple-eta (rfl), the RD part is OOG.
    exact ⟨_, _, _, _, default, ⟨0⟩, k, C, ⟨_, _, rfl⟩,
      (by unfold RD; exact Or.inl hoog),
      (by
        exact Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _))⟩
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
      exact ⟨_, _, _, _, default, ⟨0⟩, k, C, ⟨_, _, rfl⟩,
        (by unfold RD; exact Or.inl hXP),
        (by
          exact Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _))⟩
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
        C + callCharge, ⟨θs.2.2.1, θs.2.2.2.1, ?_⟩, ?_, ?_⟩
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

/-- `RD.call` specialized to Solidity's empty-call-data / no-return-copy pattern.

When both `inSize` and `outSize` are zero, the input to `Θ` is `ByteArray.empty` and copying the
callee return bytes leaves memory unchanged.  The active-word expression is kept explicit so callers
can rewrite it with their own local active-word facts. -/
theorem RD.callEmptyInOut {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {gasArg target inOffset outOffset : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: ⟨0⟩ :: inOffset :: ⟨0⟩ :: outOffset :: ⟨0⟩ :: t)
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
          ByteArray.empty (ee.depth + 1) ee.header ee.perm)
      ∧ RD code ee g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: t)
          mem
          (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat
            (⟨0⟩ : UInt256).toNat) outOffset.toNat (⟨0⟩ : UInt256).toNat))
          o (cA', σ') k' C'
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd, hoSize⟩ :=
    RD.call h hdec hdepth hov
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  have hcd : mem.readWithPadding inOffset.toNat (⟨0⟩ : UInt256).toNat = ByteArray.empty := by
    exact byteArray_readWithPadding_zero _ _
  have hΘ' : ∃ (g'' : UInt256) (A' : Substate),
      (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ ee.blobVersionedHashes cA
        s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
        (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
        callGas (UInt256.ofNat ee.gasPrice) ⟨0⟩ ⟨0⟩
        ByteArray.empty (ee.depth + 1) ee.header ee.perm := by
    rcases hΘ with ⟨g'', A', hΘeq⟩
    refine ⟨g'', A', ?_⟩
    rw [hcd] at hΘeq
    exact hΘeq
  rw [hmin, byteArray_write_len_zero] at rd
  exact ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ', rd, hoSize⟩

set_option maxHeartbeats 1000000 in
/-- **CALL** (arbitrary value, call-made branch) as an `RD → RD` combinator.

This is the value-parametric analogue of `RD.call`.  The EVM invokes `Θ` only when the call is not
static, the caller has enough balance for the transferred value, and the depth is below 1024; those
facts are hypotheses here.  The zero-value `RD.call` keeps the smaller statement used by existing
proofs. -/
theorem RD.callValueMade {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {gasArg target valueWord inOffset inSize outOffset outSize : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: valueWord :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.CALL, .none))
    (hperm : ee.perm = true)
    (hbalance : valueWord ≤ (σ.find? ee.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : ee.depth.val < 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ ee.blobVersionedHashes cA
          s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat ee.gasPrice) valueWord valueWord
          (mem.readWithPadding inOffset.toNat inSize.toNat) (ee.depth + 1) ee.header ee.perm)
      ∧ RD code ee g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: t)
          (o.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat o.size)).toNat)
          (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
            outOffset.toNat outSize.toNat))
          o (cA', σ') k' C'
      ∧ o.size < UInt256.size := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact ⟨_, _, _, _, default, ⟨0⟩, k, C, ⟨_, _, rfl⟩,
      (by unfold RD; exact Or.inl hoog),
      (by
        exact Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _))⟩
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.CALL, .none) := by
      rw [hcode, hpc]; exact hdec
    have hperm' : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have hdepth' : s.executionEnv.depth.val < 1024 := by rw [hee]; exact hdepth
    have st := step_call s hd
    rw [hstk] at st
    have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 + 1 > 1024) = False := eq_false (by omega)
    have hstaticF : (¬ s.executionEnv.perm = true ∧ valueWord ≠ { val := 0 }) = False := by
      rw [hperm']; exact eq_false (by simp)
    have hdepthLt : s.executionEnv.depth < 1024 := by rw [Fin.lt_def]; exact hdepth'
    have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    have hbalT :
        (valueWord ≤ (s.accountMap.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))) =
          True := by
      rw [hee, hσ]
      exact eq_true hbalance
    have hbalOpt :
        (valueWord ≤ Option.option ⟨0⟩ (fun x => x.balance)
            (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner)) = True := by
      rw [show Option.option ⟨0⟩ (fun x => x.balance)
          (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner) =
          (s.accountMap.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) by
        cases Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner <;> rfl]
      exact hbalT
    have hgtF :
        (valueWord > (s.accountMap.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))) =
          False := by
      rw [hee, hσ]
      exact eq_false (by
        intro hlt
        have hLeNat :
            valueWord.val.val ≤
              ((σ.find? ee.codeOwner).elim ⟨0⟩ fun x => x.balance).val.val := hbalance
        have hGtNat :
            ((σ.find? ee.codeOwner).elim ⟨0⟩ fun x => x.balance).val.val <
              valueWord.val.val := hlt
        exact Nat.not_lt_of_ge hLeNat hGtNat)
    have hdeqF : (s.executionEnv.depth == 1024) = false := by
      rw [beq_eq_false_iff_ne]; intro hh; rw [hh] at hdepth'; exact absurd hdepth' (by decide)
    simp only [List.length_cons, hovF, hstaticF, if_false, hdepthLt, hbalOpt, hgtF, hdeqF,
      and_true, if_true, Bool.or_false] at st
    rw [collapse_two_stage, hcode] at st
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    split at hXP
    · exact ⟨_, _, _, _, default, ⟨0⟩, k, C, ⟨_, _, rfl⟩,
        (by unfold RD; exact Or.inl hXP),
        (by
          exact Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _))⟩
    · rename_i hP
      set mc := memoryExpansionCost s Operation.CALL with hmc
      set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) valueWord
        gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hgc
      set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) valueWord
        gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength + 1,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hG
      set cg := UInt256.ofNat G with hcg
      set θs := Θ s.executionEnv.blobVersionedHashes s.createdAccounts s.genesisBlockHeader s.blocks
        s.accountMap s.σ₀ (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
        (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner)) s.executionEnv.sender
        (AccountAddress.ofUInt256 target) (toExecute s.accountMap (AccountAddress.ofUInt256 target))
        cg (UInt256.ofNat s.executionEnv.gasPrice) valueWord valueWord
        (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat) (s.executionEnv.depth + 1)
        s.executionEnv.header s.executionEnv.perm with hθs
      set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - θs.2.2.1.toNat) with hgv
      have hw1 : s.σ₀ = s0.σ₀ := hworld.1
      have hw2 : s.genesisBlockHeader = s0.genesisBlockHeader := hworld.2.1
      have hw3 : s.blocks = s0.blocks := hworld.2.2
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hmcle : mc ≤ s.machineState.gasAvailable.toNat := by omega
      have hretle : θs.2.2.1.toNat ≤ cg.toNat := by
        rw [hθs]
        exact Theta_returnedGas_le s.executionEnv.blobVersionedHashes s.createdAccounts s.genesisBlockHeader
          s.blocks s.accountMap s.σ₀ (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
          (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner)) s.executionEnv.sender
          (AccountAddress.ofUInt256 target) (toExecute s.accountMap (AccountAddress.ofUInt256 target))
          cg (UInt256.ofNat s.executionEnv.gasPrice) valueWord valueWord
          (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat) (s.executionEnv.depth + 1)
          s.executionEnv.header s.executionEnv.perm
      have hcgle : cg.toNat ≤ G := by
        have h : cg.toNat = G % UInt256.size := by rw [hcg]; rfl
        rw [h]; exact Nat.mod_le _ _
      have hGltgc : G < gc := by
        rw [hG, hgc]
        exact Ccallgas_lt_Ccall (AccountAddress.ofUInt256 target)
          (AccountAddress.ofUInt256 target) valueWord gasArg s.accountMap
          { pc := s.machineState.pc, stack := s.machineState.stack,
            execLength := s.machineState.execLength + 1,
            gasAvailable := s.machineState.gasAvailable.subNat mc,
            activeWords := s.machineState.activeWords, memory := s.machineState.memory,
            returnData := s.machineState.returnData, H_return := s.machineState.H_return }
          s.substate
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
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
      rw [show g.toNat - k = g.toNat + 1 - (k + 1) from by omega] at hXP
      refine ⟨θs.1, θs.2.1, θs.2.2.2.2.1, θs.2.2.2.2.2,
        (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate, cg, k + 1,
        C + callCharge, ⟨θs.2.2.1, θs.2.2.2.1, ?_⟩, ?_, ?_⟩
      · rw [← hee, ← hcA, ← hσ, ← hmem, ← hw1, ← hw2, ← hw3, ← hθs]
      · unfold RD
        refine Or.inr ⟨_, hXP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hcode
        · rw [hpc]
        · cases θs.2.2.2.2.1 <;> rfl
        · show gv = g.subNat (C + callCharge)
          exact hgvGas
        · show k + 1 ≤ C + callCharge
          omega
        · exact hCcallCharge
        · rw [hmem]
        · rw [haw]
        · rfl
        · rfl
        · exact hee
        · exact hworld
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

/-- `RD.callValueMade` specialized to Solidity's empty-call-data / no-return-copy pattern. -/
theorem RD.callValueMadeEmptyInOut {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {gasArg target valueWord inOffset outOffset : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: valueWord :: inOffset :: ⟨0⟩ :: outOffset :: ⟨0⟩ :: t)
          mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.CALL, .none))
    (hperm : ee.perm = true)
    (hbalance : valueWord ≤ (σ.find? ee.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : ee.depth.val < 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ ee.blobVersionedHashes cA
          s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat ee.gasPrice) valueWord valueWord
          ByteArray.empty (ee.depth + 1) ee.header ee.perm)
      ∧ RD code ee g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: t)
          mem
          (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat
            (⟨0⟩ : UInt256).toNat) outOffset.toNat (⟨0⟩ : UInt256).toNat))
          o (cA', σ') k' C'
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd, hoSize⟩ :=
    RD.callValueMade h hdec hperm hbalance hdepth hov
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  have hcd : mem.readWithPadding inOffset.toNat (⟨0⟩ : UInt256).toNat = ByteArray.empty := by
    exact byteArray_readWithPadding_zero _ _
  have hΘ' : ∃ (g'' : UInt256) (A' : Substate),
      (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ ee.blobVersionedHashes cA
        s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
        (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
        callGas (UInt256.ofNat ee.gasPrice) valueWord valueWord
        ByteArray.empty (ee.depth + 1) ee.header ee.perm := by
    rcases hΘ with ⟨g'', A', hΘeq⟩
    refine ⟨g'', A', ?_⟩
    rw [hcd] at hΘeq
    exact hΘeq
  rw [hmin, byteArray_write_len_zero] at rd
  exact ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ', rd, hoSize⟩

set_option maxHeartbeats 1000000 in
/-- **`CALL` insufficient-balance branch**, with an arbitrary transferred `value`.
    The EVM does not invoke `Θ`: it returns status `0`, leaves the account map carried by `RD`
    unchanged, and only updates memory/return-data as the concrete no-call-made branch dictates.
    `hperm` rules out the earlier static-mode violation when `value ≠ 0`. -/
theorem RD.callValueInsufficientBalance {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {gasArg target value inOffset inSize outOffset outSize : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hdec : decode code pc = some (.CALL, .none))
    (hbalance : ¬ value ≤ (σ.find? ee.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : ee.depth.val < 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) (⟨0⟩ :: t)
        (ByteArray.empty.write 0 mem outOffset.toNat
          (min outSize (UInt256.ofNat ByteArray.empty.size)).toNat)
        (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat))
        ByteArray.empty (cA, σ) k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee,
    hworld⟩
  · exact ⟨k, C, by unfold RD; exact Or.inl hoog⟩
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.CALL, .none) := by
      rw [hcode, hpc]; exact hdec
    have hperm' : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have hdepth' : s.executionEnv.depth.val < 1024 := by rw [hee]; exact hdepth
    have st := step_call s hd
    rw [hstk] at st
    have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 + 1 > 1024) = False :=
      eq_false (by omega)
    have hstaticF : (¬ s.executionEnv.perm = true ∧ value ≠ ({ val := 0 } : UInt256)) = False :=
      eq_false (by rintro ⟨hp, _⟩; exact hp hperm')
    have hdepthLt : s.executionEnv.depth < 1024 := by
      rw [Fin.lt_def]; exact hdepth'
    have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    have hbalOpt :
        (value ≤ Option.option ⟨0⟩ (fun x => x.balance)
            (Batteries.RBMap.find? s.accountMap s.executionEnv.codeOwner)) = False := by
      rw [hee, hσ]
      rw [show Option.option ⟨0⟩ (fun x => x.balance)
          (Batteries.RBMap.find? σ ee.codeOwner) =
          (σ.find? ee.codeOwner |>.elim ⟨0⟩ (·.balance)) by
        cases Batteries.RBMap.find? σ ee.codeOwner <;> rfl]
      exact eq_false hbalance
    have hgtT :
        (value > (s.accountMap.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))) =
          True := by
      rw [hee, hσ]
      exact eq_true (by
        show ((σ.find? ee.codeOwner).elim ⟨0⟩ fun x => x.balance).val.val < value.val.val
        exact Nat.lt_of_not_ge hbalance)
    have hdeqF : (s.executionEnv.depth == 1024) = false := by
      rw [beq_eq_false_iff_ne]
      intro hh
      rw [hh] at hdepth'
      exact absurd hdepth' (by decide)
    simp only [List.length_cons, hovF, hstaticF, if_false, hdepthLt, hbalOpt, hgtT,
      hdeqF] at st
    rw [collapse_two_stage, hcode] at st
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    set mc := memoryExpansionCost s Operation.CALL with hmc
    set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value
      gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack,
        execLength := s.machineState.execLength,
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
    set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - (UInt256.ofNat G).toNat)
      with hgv
    split at hXP
    · exact ⟨k, C, by unfold RD; exact Or.inl hXP⟩
    · rename_i hP
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hcgle : (UInt256.ofNat G).toNat ≤ G := by
        show G % UInt256.size ≤ G
        exact Nat.mod_le _ _
      have hGltgc : G < gc := by
        rw [hG, hgc]
        exact Ccallgas_lt_Ccall (AccountAddress.ofUInt256 target)
          (AccountAddress.ofUInt256 target) value gasArg s.accountMap
          { pc := s.machineState.pc, stack := s.machineState.stack,
            execLength := s.machineState.execLength + 1,
            gasAvailable := s.machineState.gasAvailable.subNat mc,
            activeWords := s.machineState.activeWords, memory := s.machineState.memory,
            returnData := s.machineState.returnData, H_return := s.machineState.H_return }
          s.substate
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      set callCharge := mc + (gc - (UInt256.ofNat G).toNat) with hcallCharge
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
        rw [hcallCharge]
        omega
      · exact hCcallCharge
      · simp [hmem]
      · rw [haw]
      · rfl
      · simp [hcA, hσ]
      · exact hee
      · exact hworld

set_option maxHeartbeats 1000000 in
/-- **`CALL` at the call-depth limit**, with an arbitrary transferred `value`.
    The EVM does not invoke `Θ`: it returns status `0`, leaves the account map carried by `RD`
    unchanged, and only updates memory/return-data as the concrete no-call-made branch dictates.
    `hperm` rules out the earlier static-mode violation when `value ≠ 0`. -/
theorem RD.callValueDepthLimit {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {gasArg target value inOffset inSize outOffset outSize : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
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
    have hperm' : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have hdepth1024 : s.executionEnv.depth = 1024 := by rw [hee]; exact hdepth
    have st := step_call s hd
    rw [hstk] at st
    have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 + 1 > 1024) = False := eq_false (by omega)
    have hstaticF : (¬ s.executionEnv.perm = true ∧ value ≠ ({ val := 0 } : UInt256)) = False :=
      eq_false (by rintro ⟨hp, _⟩; exact hp hperm')
    have hdepthF : (s.executionEnv.depth < 1024) = False :=
      eq_false (by rw [hdepth1024]; exact lt_irrefl _)
    have hdeqT : (s.executionEnv.depth == 1024) = true := by
      rw [beq_iff_eq]; exact hdepth1024
    simp only [List.length_cons, hovF, hstaticF, if_false, hdepthF, hdeqT, and_false,
      Bool.or_true, if_true] at st
    rw [collapse_two_stage, hcode] at st
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    set mc := memoryExpansionCost s Operation.CALL with hmc
    set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value gasArg
      s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hgc
    set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) value gasArg
      s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength + 1,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hG
    set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - (UInt256.ofNat G).toNat) with hgv
    have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    split at hXP
    · exact ⟨k, C, by unfold RD; exact Or.inl hXP⟩
    · rename_i hP
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hcgle : (UInt256.ofNat G).toNat ≤ G := by
        show G % UInt256.size ≤ G
        exact Nat.mod_le _ _
      have hGltgc : G < gc := by
        rw [hG, hgc]
        exact Ccallgas_lt_Ccall (AccountAddress.ofUInt256 target)
          (AccountAddress.ofUInt256 target) value gasArg s.accountMap
          { pc := s.machineState.pc, stack := s.machineState.stack,
            execLength := s.machineState.execLength + 1,
            gasAvailable := s.machineState.gasAvailable.subNat mc,
            activeWords := s.machineState.activeWords, memory := s.machineState.memory,
            returnData := s.machineState.returnData, H_return := s.machineState.H_return }
          s.substate
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      set callCharge := mc + (gc - (UInt256.ofNat G).toNat) with hcallCharge
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
        rw [hcallCharge]
        omega
      · exact hCcallCharge
      · rw [hmem]
      · rw [haw]
      · rfl
      · rw [hcA, hσ]
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

/-- `RD.callValueInsufficientBalance` specialized to empty input and no return-data copy. -/
theorem RD.callValueInsufficientBalanceEmptyInOut {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {gasArg target value inOffset outOffset : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: value :: inOffset :: ⟨0⟩ :: outOffset :: ⟨0⟩ :: t)
          mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hdec : decode code pc = some (.CALL, .none))
    (hbalance : ¬ value ≤ (σ.find? ee.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : ee.depth.val < 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) (⟨0⟩ :: t)
      mem
      (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat
        (⟨0⟩ : UInt256).toNat) outOffset.toNat (⟨0⟩ : UInt256).toNat))
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd⟩ :=
    RD.callValueInsufficientBalance h hperm hdec hbalance hdepth hov
  have hmin :
      (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  rw [hmin, byteArray_write_len_zero] at rd
  exact ⟨k', C', rd⟩

/-- `RD.callValueDepthLimit` specialized to empty input and no return-data copy. -/
theorem RD.callValueDepthLimitEmptyInOut {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {gasArg target value inOffset outOffset : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: value :: inOffset :: ⟨0⟩ :: outOffset :: ⟨0⟩ :: t)
          mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hdec : decode code pc = some (.CALL, .none))
    (hdepth : ee.depth = 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) (⟨0⟩ :: t)
      mem
      (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat
        (⟨0⟩ : UInt256).toNat) outOffset.toNat (⟨0⟩ : UInt256).toNat))
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd⟩ := RD.callValueDepthLimit h hperm hdec hdepth hov
  have hmin :
      (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  rw [hmin, byteArray_write_len_zero] at rd
  exact ⟨k', C', rd⟩

/-- `RD.callDepthLimit` specialized to empty input and no return-data copy. -/
theorem RD.callDepthLimitEmptyInOut {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {gasArg target inOffset outOffset : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: ⟨0⟩ :: inOffset :: ⟨0⟩ :: outOffset :: ⟨0⟩ :: t)
          mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.CALL, .none))
    (hdepth : ee.depth = 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) (⟨0⟩ :: t)
      mem
      (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat
        (⟨0⟩ : UInt256).toNat) outOffset.toNat (⟨0⟩ : UInt256).toNat))
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd⟩ := RD.callDepthLimit h hdec hdepth hov
  have hmin :
      (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  rw [hmin, byteArray_write_len_zero] at rd
  exact ⟨k', C', rd⟩

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

/-- Variant-indexed `RD` while-rule for loops whose carried state changes the stack and scratch
    memory.  This is the same induction principle as `RD.whileLoop`, but `mem` and `aw` are read
    from the loop-carried state `α`; the exit cursor is returned with the final state. -/
theorem RD.whileLoopCarry {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {α : Type}
    (header exit : UInt256) (Inv : ℕ → α → Prop) (stk : α → List UInt256)
    (mem : α → ByteArray) (aw : α → UInt256) (exitStk : α → List UInt256)
    (hexit : ∀ a, Inv 0 a → ∀ k C,
        RD code ee g s0 header (stk a) (mem a) (aw a) rdata acc k C →
        ∃ k' C', RD code ee g s0 exit (exitStk a) (mem a) (aw a) rdata acc k' C')
    (hbody : ∀ v a, Inv (v + 1) a → ∀ k C,
        RD code ee g s0 header (stk a) (mem a) (aw a) rdata acc k C →
        ∃ a' k' C',
          Inv v a' ∧ RD code ee g s0 header (stk a') (mem a') (aw a') rdata acc k' C') :
    ∀ v a, Inv v a → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata acc k C →
      ∃ a' k' C',
        Inv 0 a' ∧ RD code ee g s0 exit (exitStk a') (mem a') (aw a') rdata acc k' C' := by
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

/-- Variant-indexed `RD` while-rule for loops whose carried state changes the stack, scratch memory,
    **and persistent storage** (`acc`).  Same induction principle as `RD.whileLoopCarry`, but the
    accounts/account-map are read from the loop-carried state `α` rather than being fixed.  Drives a
    storage-mutating loop (e.g. a dynamic-array `push`) from any variant to the exit cursor. -/
theorem RD.whileLoopCarryFull {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {α : Type}
    (header exit : UInt256) (Inv : ℕ → α → Prop) (stk : α → List UInt256)
    (mem : α → ByteArray) (aw : α → UInt256)
    (acc : α → Batteries.RBSet AccountAddress compare × AccountMap)
    (exitStk : α → List UInt256)
    (hexit : ∀ a, Inv 0 a → ∀ k C,
        RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
        ∃ k' C', RD code ee g s0 exit (exitStk a) (mem a) (aw a) rdata (acc a) k' C')
    (hbody : ∀ v a, Inv (v + 1) a → ∀ k C,
        RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
        ∃ a' k' C',
          Inv v a' ∧ RD code ee g s0 header (stk a') (mem a') (aw a') rdata (acc a') k' C') :
    ∀ v a, Inv v a → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
      ∃ a' k' C',
        Inv 0 a' ∧ RD code ee g s0 exit (exitStk a') (mem a') (aw a') rdata (acc a') k' C' := by
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

-- LIBRARY CANDIDATE: `Reasoning.Reach`.
/-- If an `RD` cursor is claimed with consumed gas above the initial gas budget, the only possible
    branch of `RD` is the out-of-gas branch. -/
theorem RD.oog_of_cost_gt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C) (hgt : g.toNat < C) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata,
      hacc, hee, hworld⟩
  · exact hoog
  · omega

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

/-- Coupled variant-indexed loop rule for a solc bytecode loop and a Solm `for` loop.

This is the `RD.whileLoopCarryFull` analogue used when the source loop body may revert before the
variant reaches zero.  The caller supplies the bytecode transitions for the false-condition exit
and the true-condition body entry, plus a body step that either reverts both sides or produces the
next carried state. -/
theorem RD.execForLoopOrRevertCarryFull {cfg : Config} {contract : ContractDecl}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {α : Type}
    (header bodyHeader exit : UInt256) (condExpr : Expr) (post body : List Stmt)
    (Inv : ℕ → α → Store → EVM.State → Prop) (stk : α → List UInt256)
    (mem : α → ByteArray) (aw : α → UInt256)
    (acc : α → Batteries.RBSet AccountAddress compare × AccountMap)
    (exitStk : α → List UInt256)
    (hfalse : ∀ a L evm, Inv 0 a L evm →
      evalExpr? cfg { contract := contract, locals := L } evm condExpr = .ok (.bool false))
    (hexit : ∀ a L evm, Inv 0 a L evm → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
      ∃ k' C', RD code ee g s0 exit (exitStk a) (mem a) (aw a) rdata (acc a) k' C')
    (htrue : ∀ v a L evm, Inv (v + 1) a L evm →
      evalExpr? cfg { contract := contract, locals := L } evm condExpr = .ok (.bool true))
    (henter : ∀ v a L evm, Inv (v + 1) a L evm → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
      ∃ k' C', RD code ee g s0 bodyHeader (stk a) (mem a) (aw a) rdata (acc a) k' C')
    (hbody : ∀ v a L evm, Inv (v + 1) a L evm → ∀ k C,
      RD code ee g s0 bodyHeader (stk a) (mem a) (aw a) rdata (acc a) k C →
      (ExecBlock cfg { contract := contract, locals := L } evm body .reverted ∧
        RDrev code g s0) ∨
      ∃ a' L1 evm1 L2 evm2 k' C',
        (ExecBlock cfg { contract := contract, locals := L } evm body
            (.ok { contract := contract, locals := L1 } evm1) ∨
          ExecBlock cfg { contract := contract, locals := L } evm body
            (.continue { contract := contract, locals := L1 } evm1)) ∧
        ExecBlock cfg { contract := contract, locals := L1 } evm1 post
          (.ok { contract := contract, locals := L2 } evm2) ∧
        Inv v a' L2 evm2 ∧
        RD code ee g s0 header (stk a') (mem a') (aw a') rdata (acc a') k' C') :
    ∀ v a L evm, Inv v a L evm → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
      (∃ a' L' evm' k' C',
        ExecForLoop cfg { contract := contract, locals := L } evm condExpr post body
          (.ok { contract := contract, locals := L' } evm') ∧
        Inv 0 a' L' evm' ∧
        RD code ee g s0 exit (exitStk a') (mem a') (aw a') rdata (acc a') k' C') ∨
      (ExecForLoop cfg { contract := contract, locals := L } evm condExpr post body .reverted ∧
        RDrev code g s0) := by
  intro v
  induction v with
  | zero =>
      intro a L evm hInv k C rd
      obtain ⟨k', C', rdExit⟩ := hexit a L evm hInv k C rd
      exact Or.inl ⟨a, L, evm, k', C', ExecForLoop.falseDone (hfalse a L evm hInv),
        hInv, rdExit⟩
  | succ v ih =>
      intro a L evm hInv k C rd
      obtain ⟨k1, C1, rdBody⟩ := henter v a L evm hInv k C rd
      rcases hbody v a L evm hInv k1 C1 rdBody with hrev | hstep
      · exact Or.inr ⟨ExecForLoop.bodyRevert (htrue v a L evm hInv) hrev.1, hrev.2⟩
      · rcases hstep with
          ⟨a', L1, evm1, L2, evm2, k2, C2, hbodyStep, hpost, hInv', rdNext⟩
        rcases ih a' L2 evm2 hInv' k2 C2 rdNext with hdone | hloopRev
        · rcases hdone with ⟨a'', L', evm', k', C', hloop, hInv0, rdExit⟩
          rcases hbodyStep with hbodyOk | hbodyCont
          · exact Or.inl ⟨a'', L', evm', k', C',
              ExecForLoop.iterate (htrue v a L evm hInv) hbodyOk hpost hloop,
              hInv0, rdExit⟩
          · exact Or.inl ⟨a'', L', evm', k', C',
              ExecForLoop.continueIter (htrue v a L evm hInv) hbodyCont hpost hloop,
              hInv0, rdExit⟩
        · rcases hloopRev with ⟨hloop, hrdRev⟩
          rcases hbodyStep with hbodyOk | hbodyCont
          · exact Or.inr
              ⟨ExecForLoop.iterate (htrue v a L evm hInv) hbodyOk hpost hloop, hrdRev⟩
          · exact Or.inr
              ⟨ExecForLoop.continueIter (htrue v a L evm hInv) hbodyCont hpost hloop,
                hrdRev⟩

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

/-- `RETURNDATACOPY` terminal OOG: if the memory-expansion component alone is larger than the
    whole transaction gas, the reached cursor makes the entire run out of gas. -/
theorem RD.returndatacopyOOG_error {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256} (mcost : ℕ)
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.RETURNDATACOPY, .none))
    (hguard : b.toNat + c.toNat ≤ rdata.size)
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: c :: t →
        memoryExpansionCost s .RETURNDATACOPY = mcost)
    (hOOG : g.toNat < mcost)
    (hov : t.length ≤ 1024) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, _hmem, haw, hrdata, _hacc, _hee, _hworld⟩
  · exact hoog
  · have hmcS : memoryExpansionCost s .RETURNDATACOPY = mcost := hmc s haw hstk
    have hmemok : ¬ b.toNat + c.toNat > s.machineState.returnData.size := by
      rw [hrdata]
      omega
    have st := returndatacopy_xstep hcode hpc hdec hstk hmemok hov
    rw [hmcS] at st
    rw [collapse_two_stage] at st
    exact hX.trans (stepOOG hgas st hk hC (by
      have hcopy_nonneg :
          0 ≤ GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32) :=
        Nat.zero_le _
      omega))

/-- `RETURNDATACOPY` terminal OOG, packaged as an `RDrev` for older call sites. -/
theorem RD.returndatacopyOOG {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256} (mcost : ℕ)
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.RETURNDATACOPY, .none))
    (hguard : b.toNat + c.toNat ≤ rdata.size)
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: c :: t →
        memoryExpansionCost s .RETURNDATACOPY = mcost)
    (hOOG : g.toNat < mcost)
    (hov : t.length ≤ 1024) :
    RDrev code g s0 :=
  Or.inl (RD.returndatacopyOOG_error mcost h hdec hguard hmc hOOG hov)

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
theorem RDrev.reEquivElim
    {cfg contract cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code : ByteArray}
    (hcode : I.code = code)
    (h : RDrev code g (initState cA gh bl σ_evm σ₀ g A I))
    (k : ∀ g' o,
          Ξ cA gh bl σ_evm σ₀ g.toUInt256 A I = .ok (.revert g' o) →
          runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
            g.toUInt256 A I) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I := by
  rcases h with hoog | ⟨g', o, hX⟩
  · exact reEquiv_outOfGas (Xi_error_of_X_sat (by rw [← hcode] at hoog; exact hoog))
  · exact k g' o (Xi_revert_of_X_sat (by rw [← hcode] at hX; exact hX))

/-- `RDrev ⇒ noDispatch`: revert with Act failing to dispatch. Solm-side maps unconstrained. -/
theorem RDrev.reEquivNoDispatch
    {cfg contract cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code : ByteArray}
    (hcode : I.code = code) (h : RDrev code g (initState cA gh bl σ_evm σ₀ g A I))
    (hd : dispatchMsg contract I.calldata = none) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I :=
  h.reEquivElim hcode fun _ _ hrev => reEquiv_noDispatch hd hrev

/-- `RDrev ⇒ decodingFailed`: Act dispatches to `t` but calldata-decoding fails.  Solm-side maps
    unconstrained. -/
theorem RDrev.reEquivDecodingFailed
    {cfg contract cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code : ByteArray} {t}
    (hcode : I.code = code) (h : RDrev code g (initState cA gh bl σ_evm σ₀ g A I))
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
              (transitionSignature t).paramTypes I.calldata = none) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I :=
  h.reEquivElim hcode fun _ _ hrev => reEquiv_decodingFailed hd hdec hrev

/-- Eliminate an `RDret` into a `runtimeEquivalenceFor`: the OOG alternative becomes the
    `outOfGas` case automatically; the continuation `k` receives the `Ξ`-level success, with
    accounts already projected back to the carried `(cA, σ_evm)`. -/
theorem RDret.reEquivElim
    {cfg contract cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code o : ByteArray}
    (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ_evm σ₀ g A I) (cA, σ_evm) o)
    (k : ∀ (g' : UInt256) (A' : Substate),
          Ξ cA gh bl σ_evm σ₀ g.toUInt256 A I = .ok (.success (cA, σ_evm, g', A') o) →
          runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
            g.toUInt256 A I) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact reEquiv_outOfGas (Xi_error_of_X_sat (by rw [← hcode] at hoog; exact hoog))
  · have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ_evm := congrArg Prod.snd hacc
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
            -- The first auto-supplied proof is the `decode code pc = …` obligation; discharge it
            -- with `native_decide` rather than `decide`.  `decode` kernel-reduces by scanning the
            -- bytecode `ByteArray` literal (O(pc) per step), so `decide` costs ~300–450ms per
            -- opcode on the large ERC20 bytecode; `native_decide` compiles the check and runs it in
            -- ~15ms.  This adds no new trust category: every `jump (by jump_dest)` already trusts the
            -- compiler via `native_decide`, so the proofs depend on it pervasively already.
            match op.getId with
            | `jump    => acc ← `($(acc).jump (by native_decide) $(args[0]!) (by evm_ov))
            | `jumpiT  => acc ← `($(acc).jumpiT (by native_decide) $(args[0]!) $(args[1]!) (by evm_ov))
            | `jumpiNT => acc ← `($(acc).jumpiNT (by native_decide) $(args[0]!) (by evm_ov))
            | _        => acc ← `($(acc).$op $args* (by native_decide) (by evm_ov))
        | _ => Macro.throwUnsupported
      return acc

end Reasoning.Reach
