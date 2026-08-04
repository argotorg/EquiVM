import Reasoning.Reach

/-!
# Threshold-exact bytecode reachability

`RDx` is the gas-threshold-preserving counterpart of `RD`.  At cumulative cost `C` it retains
both sides of the gas split:

* if the initial gas is below `C`, the whole execution is out of gas; and
* if at least `C` gas is supplied, execution reaches the described cursor with exactly `g - C`
  gas remaining.

Unlike the disjunction in `RD`, taking the low-gas branch therefore does not discard the threshold
which caused it.  The generic `RDx.step` rule applies to operations whose transition and charge do
not inspect the amount of available gas except for the standard up-front gas guard.  In particular,
this file deliberately provides no rule for `GAS` or `CALL`.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Reach

open Reasoning.Theory

set_option maxRecDepth 10000

/-- The non-gas fields asserted at an exact reachability cursor. -/
def RDxMatches (code : ByteArray) (ee : ExecutionEnv) (s0 : State)
    (pc : UInt256) (stk : List UInt256) (mem : ByteArray) (aw : UInt256)
    (rdata : ByteArray) (acc : Batteries.RBSet AccountAddress compare × AccountMap)
    (s : State) : Prop :=
  s.executionEnv.code = code ∧
  s.machineState.pc = pc ∧
  s.machineState.stack = stk ∧
  s.machineState.memory = mem ∧
  s.machineState.activeWords = aw ∧
  s.machineState.returnData = rdata ∧
  (s.createdAccounts, s.accountMap) = acc ∧
  s.executionEnv = ee ∧
  RDWorld s0 s

/-- Exact reachability with a retained out-of-gas threshold.

The step-count condition `k ≤ C` supplies enough iterator fuel whenever the cursor is reachable.
Every continuing EVM instruction covered by this relation has positive gas cost. -/
def RDx (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (pc : UInt256) (stk : List UInt256) (mem : ByteArray) (aw : UInt256)
    (rdata : ByteArray) (acc : Batteries.RBSet AccountAddress compare × AccountMap)
    (k C : Nat) : Prop :=
  k ≤ C ∧
  (g.toNat < C → X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass) ∧
  (C ≤ g.toNat → ∃ s : State,
    X (g.toNat + 1) (D_J code 0) s0 = X (g.toNat + 1 - k) (D_J code 0) s ∧
    s.machineState.gasAvailable = g.subNat C ∧
    RDxMatches code ee s0 pc stk mem aw rdata acc s)

/-- Cursor-packed form of `RDx`. -/
def RDxc (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (cur : Cursor) (k C : Nat) : Prop :=
  RDx code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C

/-- A threshold-exact fact implies the old reached-or-OOG disjunction. -/
theorem RDx.toRD {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C) :
    RD code ee g s0 pc stk mem aw rdata acc k C := by
  rcases h with ⟨hk, hoog, hreach⟩
  by_cases hC : C ≤ g.toNat
  · obtain ⟨s, hX, hgas, hm⟩ := hreach hC
    rcases hm with ⟨hcode, hpc, hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    exact Or.inr ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata,
      hacc, hee, hworld⟩
  · exact Or.inl (hoog (Nat.lt_of_not_ge hC))

/-- Reassociate or normalize the exact step and cost indices. -/
theorem RDx.withIndices {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C k' C' : Nat}
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C)
    (hk : k = k') (hC : C = C') :
    RDx code ee g s0 pc stk mem aw rdata acc k' C' := by
  subst k'
  subst C'
  exact h

/-- Exact entry cursor for the state constructed by `Ξ`. -/
theorem RDx.initState {code : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = code) :
    RDx code I g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) ⟨0⟩ []
      ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 := by
  refine ⟨by omega, ?_, ?_⟩
  · omega
  · intro _
    refine ⟨Reasoning.Theory.initState cA gh bl σ σ₀ g A I, by simp,
      by simp [Reasoning.Theory.initState], ?_⟩
    simp [RDxMatches, Reasoning.Theory.initState, hcode, RDWorld]
    native_decide

/-- Generic exact continuation rule for a gas-agnostic operation.

The caller supplies the ordinary one-step gas guard, the successor cursor facts, and the local gas
update.  All threshold case analysis and iterator arithmetic is handled here. -/
theorem RDx.step
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc pc' : UInt256} {stk stk' : List UInt256} {mem mem' : ByteArray}
    {aw aw' : UInt256} {rdata rdata' : ByteArray}
    {acc acc' : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C cost : Nat} (next : State → State)
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C)
    (hcost : 0 < cost)
    (hstep : ∀ s : State, RDxMatches code ee s0 pc stk mem aw rdata acc s →
      Xstep (D_J code 0) s =
        if s.machineState.gasAvailable.toNat < cost then .error .OutOfGass
        else .ok (next s, .none))
    (hnext : ∀ s : State, RDxMatches code ee s0 pc stk mem aw rdata acc s →
      RDxMatches code ee s0 pc' stk' mem' aw' rdata' acc' (next s))
    (hnextGas : ∀ s : State, RDxMatches code ee s0 pc stk mem aw rdata acc s →
      (next s).machineState.gasAvailable = s.machineState.gasAvailable.subNat cost) :
    RDx code ee g s0 pc' stk' mem' aw' rdata' acc' (k + 1) (C + cost) := by
  rcases h with ⟨hk, hoog, hreach⟩
  refine ⟨by omega, ?_, ?_⟩
  · intro hlow
    by_cases hC : C ≤ g.toNat
    · obtain ⟨s, hX, hgas, hm⟩ := hreach hC
      exact hX.trans (stepOOG hgas (hstep s hm) hk hC hlow)
    · exact hoog (Nat.lt_of_not_ge hC)
  · intro henough
    have hC : C ≤ g.toNat := by omega
    obtain ⟨s, hX, hgas, hm⟩ := hreach hC
    refine ⟨next s, hX.trans (stepContinue hgas (hstep s hm) hk henough), ?_, hnext s hm⟩
    rw [hnextGas s hm, hgas, Sat256.subNat_subNat]

/-! ## Gas-agnostic opcode families -/

/-- Shared exact wrapper for the cost-3 `stSwap` family (SWAP and most DUP operations). -/
theorem RDx.stepSwap
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stkIn stkOut : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (h : RDx code ee g s0 pc stkIn mem aw rdata acc k C)
    (hstep : ∀ s : State, s.executionEnv.code = code → s.machineState.pc = pc →
      s.machineState.stack = stkIn →
      Xstep (D_J code 0) s =
        if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
        else .ok (stSwap s stkOut, .none)) :
    RDx code ee g s0 (pc + ⟨1⟩) stkOut mem aw rdata acc (k + 1) (C + 3) := by
  apply RDx.step (cost := 3) (fun s => stSwap s stkOut) h (by omega)
  · intro s hm
    exact hstep s hm.1 hm.2.1 hm.2.2.1
  · intro s hm
    rcases hm with ⟨hcode, hpc, _hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stSwap] using hcode
    · simp only [stSwap, hpc]
    · simpa only [stSwap] using hmem
    · simpa only [stSwap] using haw
    · simpa only [stSwap] using hrdata
    · simpa only [stSwap] using hacc
    · simpa only [stSwap] using hee
    · simpa only [stSwap] using hworld
  · intro s _
    rfl

/-- Shared exact wrapper for cost-3 binary operations. -/
theorem RDx.stepBinop
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b res : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hstep : ∀ s : State, s.executionEnv.code = code → s.machineState.pc = pc →
      s.machineState.stack = a :: b :: t →
      Xstep (D_J code 0) s =
        if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
        else .ok (stBinop s res t, .none)) :
    RDx code ee g s0 (pc + ⟨1⟩) (res :: t) mem aw rdata acc (k + 1) (C + 3) := by
  apply RDx.step (cost := 3) (fun s => stBinop s res t) h (by omega)
  · intro s hm
    exact hstep s hm.1 hm.2.1 hm.2.2.1
  · intro s hm
    rcases hm with ⟨hcode, hpc, _hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stBinop] using hcode
    · simp only [stBinop, hpc]
    · simpa only [stBinop] using hmem
    · simpa only [stBinop] using haw
    · simpa only [stBinop] using hrdata
    · simpa only [stBinop] using hacc
    · simpa only [stBinop] using hee
    · simpa only [stBinop] using hworld
  · intro s _
    rfl

/-- Shared exact wrapper for cost-5 binary operations. -/
theorem RDx.stepBinop5
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b res : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hstep : ∀ s : State, s.executionEnv.code = code → s.machineState.pc = pc →
      s.machineState.stack = a :: b :: t →
      Xstep (D_J code 0) s =
        if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
        else .ok (stBinop5 s res t, .none)) :
    RDx code ee g s0 (pc + ⟨1⟩) (res :: t) mem aw rdata acc (k + 1) (C + 5) := by
  apply RDx.step (cost := 5) (fun s => stBinop5 s res t) h (by omega)
  · intro s hm
    exact hstep s hm.1 hm.2.1 hm.2.2.1
  · intro s hm
    rcases hm with ⟨hcode, hpc, _hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stBinop5] using hcode
    · simp only [stBinop5, hpc]
    · simpa only [stBinop5] using hmem
    · simpa only [stBinop5] using haw
    · simpa only [stBinop5] using hrdata
    · simpa only [stBinop5] using hacc
    · simpa only [stBinop5] using hee
    · simpa only [stBinop5] using hworld
  · intro s _
    rfl

theorem RDx.swap1
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP1, .none)) (hov : t.length + 2 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (b :: a :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap1_xstep hc hp hdec hs hov)

theorem RDx.swap2
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b c : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP2, .none)) (hov : t.length + 3 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (c :: b :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap2_xstep hc hp hdec hs hov)

theorem RDx.swap3
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b c d : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP3, .none)) (hov : t.length + 4 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (d :: b :: c :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap3_xstep hc hp hdec hs hov)

theorem RDx.swap4 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: c :: d :: e :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP4, .none)) (hov : t.length + 5 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (e :: b :: c :: d :: a :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap4_xstep hc hp hdec hs hov)

/-- **SWAP5**: exchange the stack top with the 6th element (cost `Gverylow = 3`, pc += 1). -/
theorem RDx.swap5 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256}
    (rd : RDx code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP5, .none)) (hov : t.length + 6 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (f :: b :: c :: d :: e :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap5_xstep hc hp hdec hs hov)

/-- **SWAP6**: exchange the stack top with the 7th element (cost `Gverylow = 3`, pc += 1). -/
theorem RDx.swap6 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg : UInt256} {t : List UInt256}
    (rd : RDx code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP6, .none)) (hov : t.length + 7 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (gg :: b :: c :: d :: e :: f :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap6_xstep hc hp hdec hs hov)

/-- **SWAP7**: exchange the stack top with the 8th element (cost `Gverylow = 3`, pc += 1). -/
theorem RDx.swap7 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h : UInt256} {t : List UInt256}
    (rd : RDx code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: h :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP7, .none)) (hov : t.length + 8 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (h :: b :: c :: d :: e :: f :: gg :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap7_xstep hc hp hdec hs hov)

theorem RDx.swap8 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii : UInt256} {t : List UInt256}
    (rd : RDx code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP8, .none)) (hov : t.length + 9 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (ii :: b :: c :: d :: e :: f :: gg :: hh :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap8_xstep hc hp hdec hs hov)

theorem RDx.swap10 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk : UInt256} {t : List UInt256}
    (rd : RDx code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP10, .none)) (hov : t.length + 11 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩)
      (kk :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap10_xstep hc hp hdec hs hov)

theorem RDx.swap11 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (rd : RDx code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP11, .none)) (hov : t.length + 12 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩)
      (ll :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap11_xstep hc hp hdec hs hov)


theorem RDx.dup2
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP2, .none)) (hov : t.length + 3 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (b :: a :: b :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup2_xstep hc hp hdec hs hov)

theorem RDx.dup3
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b c : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP3, .none)) (hov : t.length + 4 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (c :: a :: b :: c :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup3_xstep hc hp hdec hs hov)

/-- Exact JUMPDEST step. -/
theorem RDx.jumpdest
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.JUMPDEST, .none)) (hov : stk.length ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) stk mem aw rdata acc (k + 1) (C + 1) := by
  apply RDx.step (cost := 1) stJumpdest h (by omega)
  · intro s hm
    exact jumpdest_xstep hm.1 hm.2.1 hdec (by rw [hm.2.2.1]; exact hov)
  · intro s hm
    rcases hm with ⟨hcode, hpc, hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    simp only [RDxMatches, stJumpdest]
    exact ⟨hcode, by rw [hpc], hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
  · intro _ _
    rfl

/-- Exact PUSH0 step. -/
theorem RDx.push0
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.PUSH0, .none)) (hov : stk.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (⟨0⟩ :: stk) mem aw rdata acc (k + 1) (C + 2) := by
  apply RDx.step (cost := 2) stPush0 h (by omega)
  · intro s hm
    exact push0_xstep hm.1 hm.2.1 hdec hm.2.2.1 hov
  · intro s hm
    rcases hm with ⟨hcode, hpc, hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    simp only [RDxMatches, stPush0]
    exact ⟨hcode, by rw [hpc], by rw [hstk], hmem, haw, hrdata, hacc, hee, hworld⟩
  · intro _ _
    rfl

/-- Exact PUSH1 step. -/
theorem RDx.push1
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} (arg : UInt256)
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.Push .PUSH1, some (arg, 1)))
    (hov : stk.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + UInt256.ofNat 2) (arg :: stk) mem aw rdata acc
      (k + 1) (C + 3) := by
  apply RDx.step (cost := 3) (fun s => stPush1 s arg) h (by omega)
  · intro s hm
    exact push1_xstep hm.1 hm.2.1 hdec hm.2.2.1 hov
  · intro s hm
    rcases hm with ⟨hcode, hpc, hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    simp only [RDxMatches, stPush1]
    exact ⟨hcode, by rw [hpc], by rw [hstk], hmem, haw, hrdata, hacc, hee, hworld⟩
  · intro _ _
    rfl

/-- Exact PUSH2 step. -/
theorem RDx.push2
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} (arg : UInt256)
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.Push .PUSH2, some (arg, 2)))
    (hov : stk.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + UInt256.ofNat 3) (arg :: stk) mem aw rdata acc
      (k + 1) (C + 3) := by
  apply RDx.step (cost := 3) (fun s => stPush2 s arg) h (by omega)
  · intro s hm
    exact push2_xstep hm.1 hm.2.1 hdec hm.2.2.1 hov
  · intro s hm
    rcases hm with ⟨hcode, hpc, hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    simp only [RDxMatches, stPush2]
    exact ⟨hcode, by rw [hpc], by rw [hstk], hmem, haw, hrdata, hacc, hee, hworld⟩
  · intro _ _
    rfl

theorem RDx.eq {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.EQ, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.eq a b :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => eq_xstep hc hp hdec hs hov)

theorem RDx.lt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LT, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.lt a b :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => lt_xstep hc hp hdec hs hov)

theorem RDx.gt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.GT, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.gt a b :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => gt_xstep hc hp hdec hs hov)

theorem RDx.slt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SLT, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.slt a b :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => slt_xstep hc hp hdec hs hov)

theorem RDx.sgt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SGT, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.sgt a b :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => sgt_xstep hc hp hdec hs hov)

theorem RDx.add {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.ADD, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) ((a + b) :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => add_xstep hc hp hdec hs hov)

theorem RDx.sub {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SUB, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.sub a b :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => sub_xstep hc hp hdec hs hov)

theorem RDx.and {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.AND, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.land a b :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => and_xstep hc hp hdec hs hov)

theorem RDx.or {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.OR, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.lor a b :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => or_xstep hc hp hdec hs hov)

theorem RDx.xor {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.XOR, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.xor a b :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => xor_xstep hc hp hdec hs hov)

theorem RDx.shl {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SHL, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.shiftLeft b a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => shl_xstep hc hp hdec hs hov)

theorem RDx.shr {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SHR, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.shiftRight b a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => shr_xstep hc hp hdec hs hov)

theorem RDx.mul {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MUL, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.mul a b :: t) mem aw rdata acc
      (k + 1) (C + 5) :=
  h.stepBinop5 (fun _ hc hp hs => mul_xstep hc hp hdec hs hov)

theorem RDx.div {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DIV, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.div a b :: t) mem aw rdata acc
      (k + 1) (C + 5) :=
  h.stepBinop5 (fun _ hc hp hs => div_xstep hc hp hdec hs hov)

theorem RDx.mod {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MOD, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.mod a b :: t) mem aw rdata acc
      (k + 1) (C + 5) :=
  h.stepBinop5 (fun _ hc hp hs => mod_xstep hc hp hdec hs hov)

/-- Width-generic exact PUSH step. -/
theorem RDx.pushConst
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C)
    (arg : UInt256) {width : Nat} {op : Operation.POp}
    (hop : op ≠ .PUSH0)
    (hdec : decode code pc = some (.Push op, some (arg, width)))
    (hov : stk.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + UInt256.ofNat width.succ) (arg :: stk) mem aw rdata acc
      (k + 1) (C + 3) := by
  apply RDx.step (cost := 3) (fun s => stPushConst s arg width) h (by omega)
  · intro s hm
    exact pushConst_xstep hm.1 hm.2.1 hop hdec hm.2.2.1 hov
  · intro s hm
    rcases hm with ⟨hcode, hpc, hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    simp only [RDxMatches, stPushConst]
    exact ⟨hcode, by rw [hpc], by rw [hstk], hmem, haw, hrdata, hacc, hee, hworld⟩
  · intro _ _
    rfl

theorem RDx.push4
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C) (arg : UInt256)
    (hdec : decode code pc = some (.Push .PUSH4, some (arg, 4)))
    (hov : stk.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + UInt256.ofNat 5) (arg :: stk) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.pushConst arg (by decide) hdec hov

theorem RDx.push20
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C) (arg : UInt256)
    (hdec : decode code pc = some (.Push .PUSH20, some (arg, 20)))
    (hov : stk.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + UInt256.ofNat 21) (arg :: stk) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.pushConst arg (by decide) hdec hov

theorem RDx.pop
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.POP, .none)) (hov : t.length ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) t mem aw rdata acc (k + 1) (C + 2) := by
  apply RDx.step (cost := 2) (fun s => stPop s t) h (by omega)
  · intro s hm
    exact pop_xstep hm.1 hm.2.1 hdec hm.2.2.1 hov
  · intro s hm
    rcases hm with ⟨hcode, hpc, _hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stPop] using hcode
    · simp only [stPop, hpc]
    · simp only [stPop]
    · simpa only [stPop] using hmem
    · simpa only [stPop] using haw
    · simpa only [stPop] using hrdata
    · simpa only [stPop] using hacc
    · simpa only [stPop] using hee
    · simpa only [stPop] using hworld
  · intro _ _
    rfl

theorem RDx.jump
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {target : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (target :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.JUMP, .none))
    (hjd : (D_J code 0).contains target = true) (hov : t.length ≤ 1024) :
    RDx code ee g s0 target t mem aw rdata acc (k + 1) (C + 8) := by
  apply RDx.step (cost := 8) (fun s => stJump s target t) h (by omega)
  · intro s hm
    exact jump_xstep hm.1 hm.2.1 hdec hm.2.2.1 hjd hov
  · intro s hm
    rcases hm with ⟨hcode, _hpc, _hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stJump] using hcode
    · simp only [stJump]
    · simp only [stJump]
    · simpa only [stJump] using hmem
    · simpa only [stJump] using haw
    · simpa only [stJump] using hrdata
    · simpa only [stJump] using hacc
    · simpa only [stJump] using hee
    · simpa only [stJump] using hworld
  · intro _ _
    rfl

theorem RDx.jumpiT
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {target condition : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (target :: condition :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.JUMPI, .none)) (hcondition : condition ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains target = true) (hov : t.length ≤ 1024) :
    RDx code ee g s0 target t mem aw rdata acc (k + 1) (C + 10) := by
  apply RDx.step (cost := 10) (fun s => stJumpiT s target t) h (by omega)
  · intro s hm
    exact jumpi_t_xstep hm.1 hm.2.1 hdec hm.2.2.1 hcondition hjd hov
  · intro s hm
    rcases hm with ⟨hcode, _hpc, _hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stJumpiT] using hcode
    · simp only [stJumpiT]
    · simp only [stJumpiT]
    · simpa only [stJumpiT] using hmem
    · simpa only [stJumpiT] using haw
    · simpa only [stJumpiT] using hrdata
    · simpa only [stJumpiT] using hacc
    · simpa only [stJumpiT] using hee
    · simpa only [stJumpiT] using hworld
  · intro _ _
    rfl

theorem RDx.jumpiNT
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {target condition : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (target :: condition :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.JUMPI, .none)) (hcondition : condition = ⟨0⟩)
    (hov : t.length ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) t mem aw rdata acc (k + 1) (C + 10) := by
  apply RDx.step (cost := 10) (fun s => stJumpiNT s t) h (by omega)
  · intro s hm
    have hstk := hm.2.2.1
    rw [hcondition] at hstk
    exact jumpi_nt_xstep hm.1 hm.2.1 hdec hstk hov
  · intro s hm
    rcases hm with ⟨hcode, hpc, _hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stJumpiNT] using hcode
    · simp only [stJumpiNT, hpc]
    · simp only [stJumpiNT]
    · simpa only [stJumpiNT] using hmem
    · simpa only [stJumpiNT] using haw
    · simpa only [stJumpiNT] using hrdata
    · simpa only [stJumpiNT] using hacc
    · simpa only [stJumpiNT] using hee
    · simpa only [stJumpiNT] using hworld
  · intro _ _
    rfl

/-! ### Dynamic but gas-agnostic memory operations -/

theorem RDx.mstore
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {offset value : UInt256} {t : List UInt256}
    (memoryCost : Nat) (memOut : ByteArray) (awOut : UInt256)
    (h : RDx code ee g s0 pc (offset :: value :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MSTORE, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = offset :: value :: t → memoryExpansionCost s .MSTORE = memoryCost)
    (hmem : value.toByteArray.write 0 mem offset.toNat 32 = memOut)
    (haw : UInt256.ofNat (MachineState.M aw.toNat offset.toNat 32) = awOut)
    (hov : t.length ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) t memOut awOut rdata acc
      (k + 1) (C + (memoryCost + 3)) := by
  apply RDx.step (cost := memoryCost + 3) (fun s => stMStore s offset value t) h (by omega)
  · intro s hm
    have hs := mstore_xstep hm.1 hm.2.1 hdec hm.2.2.1 hov
    rw [hmc s hm.2.2.2.2.1 hm.2.2.1] at hs
    exact hs
  · intro s hm
    rcases hm with ⟨hcode, hpc, hstk, hsMem, hsAw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stMStore] using hcode
    · simp only [stMStore, hpc]
    · simp only [stMStore]
    · simp only [stMStore]
      rw [hsMem, hmem]
    · simp only [stMStore]
      rw [hsAw, haw]
    · simpa only [stMStore] using hrdata
    · simpa only [stMStore] using hacc
    · simpa only [stMStore] using hee
    · simpa only [stMStore] using hworld
  · intro s hm
    simp only [stMStore]
    rw [hmc s hm.2.2.2.2.1 hm.2.2.1, Sat256.subNat_subNat]

theorem RDx.mload
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {offset : UInt256} {t : List UInt256}
    (memoryCost : Nat) (value awOut : UInt256)
    (h : RDx code ee g s0 pc (offset :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MLOAD, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = offset :: t → memoryExpansionCost s .MLOAD = memoryCost)
    (hvalue :
      (if offset.toNat ≥ mem.size ∨ offset ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding offset.toNat 32))) = value)
    (haw : UInt256.ofNat (MachineState.M aw.toNat offset.toNat 32) = awOut)
    (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (value :: t) mem awOut rdata acc
      (k + 1) (C + (memoryCost + 3)) := by
  apply RDx.step (cost := memoryCost + 3) (fun s => stMLoad s offset t) h (by omega)
  · intro s hm
    have hs := mload_xstep hm.1 hm.2.1 hdec hm.2.2.1 hov
    rw [hmc s hm.2.2.2.2.1 hm.2.2.1] at hs
    exact hs
  · intro s hm
    rcases hm with ⟨hcode, hpc, _hstk, hsMem, hsAw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stMLoad] using hcode
    · simp only [stMLoad, hpc]
    · simp only [stMLoad]
      rw [hsMem, hsAw, hvalue]
    · simpa only [stMLoad] using hsMem
    · simp only [stMLoad]
      rw [hsAw, haw]
    · simpa only [stMLoad] using hrdata
    · simpa only [stMLoad] using hacc
    · simpa only [stMLoad] using hee
    · simpa only [stMLoad] using hworld
  · intro s hm
    simp only [stMLoad]
    rw [hmc s hm.2.2.2.2.1 hm.2.2.1, Sat256.subNat_subNat]

theorem RDx.dup4 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP4, .none)) (hov : t.length + 5 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (d :: a :: b :: c :: d :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup4_xstep hc hp hdec hs hov)

theorem RDx.dup5 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: c :: d :: e :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP5, .none)) (hov : t.length + 6 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (e :: a :: b :: c :: d :: e :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup5_xstep hc hp hdec hs hov)

theorem RDx.dup6 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP6, .none)) (hov : t.length + 7 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (f :: a :: b :: c :: d :: e :: f :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup6_xstep hc hp hdec hs hov)

theorem RDx.dup7 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP7, .none)) (hov : t.length + 8 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (gg :: a :: b :: c :: d :: e :: f :: gg :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup7_xstep hc hp hdec hs hov)

theorem RDx.dup8 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP8, .none)) (hov : t.length + 9 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (hh :: a :: b :: c :: d :: e :: f :: gg :: hh :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup8_xstep hc hp hdec hs hov)

theorem RDx.dup9 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP9, .none)) (hov : t.length + 10 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (ii :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup9_xstep hc hp hdec hs hov)

theorem RDx.dup10 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP10, .none)) (hov : t.length + 11 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩)
      (jj :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup10_xstep hc hp hdec hs hov)

theorem RDx.dup11 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP11, .none)) (hov : t.length + 12 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩)
      (kk :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup11_xstep hc hp hdec hs hov)

theorem RDx.dup13 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP13, .none)) (hov : t.length + 14 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩)
      (mm :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup13_xstep hc hp hdec hs hov)

theorem RDx.dup14 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP14, .none)) (hov : t.length + 15 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩)
      (nn :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup14_xstep hc hp hdec hs hov)

theorem RDx.dup15 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn oo : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP15, .none)) (hov : t.length + 16 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩)
      (oo :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup15_xstep hc hp hdec hs hov)



theorem RDx.dup1
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP1, .none)) (hov : t.length + 2 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (a :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) := by
  apply RDx.step (cost := 3) (fun s => stDup1 s a t) h (by omega)
  · intro s hm
    exact dup1_xstep hm.1 hm.2.1 hdec hm.2.2.1 (by simp only [List.length_cons]; omega)
  · intro s hm
    rcases hm with ⟨hcode, hpc, _hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stDup1] using hcode
    · simp only [stDup1, hpc]
    · simp only [stDup1]
    · simpa only [stDup1] using hmem
    · simpa only [stDup1] using haw
    · simpa only [stDup1] using hrdata
    · simpa only [stDup1] using hacc
    · simpa only [stDup1] using hee
    · simpa only [stDup1] using hworld
  · intro _ _
    rfl

theorem RDx.iszero
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.ISZERO, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.isZero a :: t) mem aw rdata acc
      (k + 1) (C + 3) := by
  apply RDx.step (cost := 3) (fun s => stIsZero s a t) h (by omega)
  · intro s hm
    exact iszero_xstep hm.1 hm.2.1 hdec hm.2.2.1 (by simp only [List.length_cons]; omega)
  · intro s hm
    rcases hm with ⟨hcode, hpc, _hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stIsZero] using hcode
    · simp only [stIsZero, hpc]
    · simp only [stIsZero]
    · simpa only [stIsZero] using hmem
    · simpa only [stIsZero] using haw
    · simpa only [stIsZero] using hrdata
    · simpa only [stIsZero] using hacc
    · simpa only [stIsZero] using hee
    · simpa only [stIsZero] using hworld
  · intro _ _
    rfl

theorem RDx.not
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {a : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.NOT, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.lnot a :: t) mem aw rdata acc
      (k + 1) (C + 3) := by
  apply RDx.step (cost := 3) (fun s => stNot s a t) h (by omega)
  · intro s hm
    exact not_xstep hm.1 hm.2.1 hdec hm.2.2.1 hov
  · intro s hm
    rcases hm with ⟨hcode, hpc, _hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stNot] using hcode
    · simp only [stNot, hpc]
    · simp only [stNot]
    · simpa only [stNot] using hmem
    · simpa only [stNot] using haw
    · simpa only [stNot] using hrdata
    · simpa only [stNot] using hacc
    · simpa only [stNot] using hee
    · simpa only [stNot] using hworld
  · intro _ _
    rfl

theorem RDx.callvalue
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.CALLVALUE, .none)) (hov : stk.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (ee.weiValue :: stk) mem aw rdata acc
      (k + 1) (C + 2) := by
  apply RDx.step (cost := 2) stCallvalue h (by omega)
  · intro s hm
    exact callvalue_xstep hm.1 hm.2.1 hdec hm.2.2.1 hov
  · intro s hm
    rcases hm with ⟨hcode, hpc, hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stCallvalue] using hcode
    · simp only [stCallvalue, hpc]
    · simp only [stCallvalue]
      rw [hee, hstk]
    · simpa only [stCallvalue] using hmem
    · simpa only [stCallvalue] using haw
    · simpa only [stCallvalue] using hrdata
    · simpa only [stCallvalue] using hacc
    · simpa only [stCallvalue] using hee
    · simpa only [stCallvalue] using hworld
  · intro _ _
    rfl

theorem RDx.calldatasize
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.CALLDATASIZE, .none)) (hov : stk.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.ofNat ee.calldata.size :: stk)
      mem aw rdata acc (k + 1) (C + 2) := by
  apply RDx.step (cost := 2) stCalldatasize h (by omega)
  · intro s hm
    exact calldatasize_xstep hm.1 hm.2.1 hdec hm.2.2.1 hov
  · intro s hm
    rcases hm with ⟨hcode, hpc, hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stCalldatasize] using hcode
    · simp only [stCalldatasize, hpc]
    · simp only [stCalldatasize]
      rw [hee, hstk]
    · simpa only [stCalldatasize] using hmem
    · simpa only [stCalldatasize] using haw
    · simpa only [stCalldatasize] using hrdata
    · simpa only [stCalldatasize] using hacc
    · simpa only [stCalldatasize] using hee
    · simpa only [stCalldatasize] using hworld
  · intro _ _
    rfl

theorem RDx.calldataload
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {offset : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (offset :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.CALLDATALOAD, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩)
      (uInt256OfByteArray (ee.calldata.readBytes offset.toNat 32) :: t)
      mem aw rdata acc (k + 1) (C + 3) := by
  apply RDx.step (cost := 3) (fun s => stCalldataload s offset t) h (by omega)
  · intro s hm
    exact calldataload_xstep hm.1 hm.2.1 hdec hm.2.2.1 hov
  · intro s hm
    rcases hm with ⟨hcode, hpc, _hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stCalldataload] using hcode
    · simp only [stCalldataload, hpc]
    · simp only [stCalldataload]
      rw [hee]
    · simpa only [stCalldataload] using hmem
    · simpa only [stCalldataload] using haw
    · simpa only [stCalldataload] using hrdata
    · simpa only [stCalldataload] using hacc
    · simpa only [stCalldataload] using hee
    · simpa only [stCalldataload] using hworld
  · intro _ _
    rfl

theorem RDx.calldatacopy
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {dst src len : UInt256} {t : List UInt256}
    (memoryCost : Nat) (memOut : ByteArray) (awOut : UInt256)
    (h : RDx code ee g s0 pc (dst :: src :: len :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.CALLDATACOPY, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = dst :: src :: len :: t →
      memoryExpansionCost s .CALLDATACOPY = memoryCost)
    (hmem : ee.calldata.write src.toNat mem dst.toNat len.toNat = memOut)
    (haw : UInt256.ofNat (MachineState.M aw.toNat dst.toNat len.toNat) = awOut)
    (hov : t.length ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) t memOut awOut rdata acc (k + 1)
      (C + (memoryCost +
        (GasConstants.Gverylow + GasConstants.Gcopy * ((len.toNat + 31) / 32)))) := by
  let copyCost := GasConstants.Gverylow + GasConstants.Gcopy * ((len.toNat + 31) / 32)
  apply RDx.step (cost := memoryCost + copyCost)
    (fun s => stCalldatacopy s dst src len t) h (by simp [copyCost, GasConstants.Gverylow])
  · intro s hm
    have hs := calldatacopy_xstep hm.1 hm.2.1 hdec hm.2.2.1 hov
    rw [hmc s hm.2.2.2.2.1 hm.2.2.1, collapse_two_stage] at hs
    simpa only [copyCost] using hs
  · intro s hm
    rcases hm with ⟨hcode, hpc, _hstk, hsMem, hsAw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stCalldatacopy] using hcode
    · simp only [stCalldatacopy, hpc]
    · simp only [stCalldatacopy]
    · simp only [stCalldatacopy]
      rw [hee, hsMem, hmem]
    · simp only [stCalldatacopy]
      rw [hsAw, haw]
    · simpa only [stCalldatacopy] using hrdata
    · simpa only [stCalldatacopy] using hacc
    · simpa only [stCalldatacopy] using hee
    · simpa only [stCalldatacopy] using hworld
  · intro s hm
    simp only [stCalldatacopy]
    rw [hmc s hm.2.2.2.2.1 hm.2.2.1, Sat256.subNat_subNat]

/-- Exact loop induction with a closed-form gas threshold. -/
theorem RDx.whileLoopGas
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {α : Type}
    (header exit : UInt256) (Inv : Nat → α → Prop) (stk : α → List UInt256)
    (exitStk : List UInt256) (cost : Nat → α → Nat)
    (hexit : ∀ a, Inv 0 a → ∀ k C,
      RDx code ee g s0 header (stk a) mem aw rdata acc k C →
      ∃ k', RDx code ee g s0 exit exitStk mem aw rdata acc k' (C + cost 0 a))
    (hbody : ∀ v a, Inv (v + 1) a → ∀ k C,
      RDx code ee g s0 header (stk a) mem aw rdata acc k C →
      ∃ a' k' dC,
        Inv v a' ∧ cost (v + 1) a = dC + cost v a' ∧
        RDx code ee g s0 header (stk a') mem aw rdata acc k' (C + dC)) :
    ∀ v a, Inv v a → ∀ k C,
      RDx code ee g s0 header (stk a) mem aw rdata acc k C →
      ∃ k', RDx code ee g s0 exit exitStk mem aw rdata acc k' (C + cost v a) := by
  intro v
  induction v with
  | zero => intro a hInv k C h; exact hexit a hInv k C h
  | succ v ih =>
    intro a hInv k C h
    obtain ⟨a', k', dC, hInv', hcost, h'⟩ := hbody v a hInv k C h
    obtain ⟨k'', h''⟩ := ih a' hInv' k' (C + dC) h'
    exact ⟨k'', by simpa only [hcost, Nat.add_assoc] using h''⟩

/-- State-carrying exact loop induction. -/
theorem RDx.whileLoopCarryGas
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {α : Type}
    (header exit : UInt256) (Inv : Nat → α → Prop) (stk : α → List UInt256)
    (mem : α → ByteArray) (aw : α → UInt256) (exitStk : α → List UInt256)
    (cost : Nat → α → Nat)
    (hexit : ∀ a, Inv 0 a → ∀ k C,
      RDx code ee g s0 header (stk a) (mem a) (aw a) rdata acc k C →
      ∃ k', RDx code ee g s0 exit (exitStk a) (mem a) (aw a) rdata acc k'
        (C + cost 0 a))
    (hbody : ∀ v a, Inv (v + 1) a → ∀ k C,
      RDx code ee g s0 header (stk a) (mem a) (aw a) rdata acc k C →
      ∃ a' k' dC,
        Inv v a' ∧ cost (v + 1) a = dC + cost v a' ∧
        RDx code ee g s0 header (stk a') (mem a') (aw a') rdata acc k' (C + dC)) :
    ∀ v a, Inv v a → ∀ k C,
      RDx code ee g s0 header (stk a) (mem a) (aw a) rdata acc k C →
      ∃ a' k', Inv 0 a' ∧
        RDx code ee g s0 exit (exitStk a') (mem a') (aw a') rdata acc k'
          (C + cost v a) := by
  intro v
  induction v with
  | zero =>
    intro a hInv k C h
    obtain ⟨k', h'⟩ := hexit a hInv k C h
    exact ⟨a, k', hInv, h'⟩
  | succ v ih =>
    intro a hInv k C h
    obtain ⟨a', k', dC, hInv', hcost, h'⟩ := hbody v a hInv k C h
    obtain ⟨a'', k'', hInv'', h''⟩ := ih a' hInv' k' (C + dC) h'
    exact ⟨a'', k'', hInv'', by simpa only [hcost, Nat.add_assoc] using h''⟩

/-- Threshold-exact successful termination. -/
def RDxRet (code : ByteArray) (g : Sat256) (s0 : State)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap)
    (output : ByteArray) (cost : Nat) : Prop :=
  (g.toNat < cost → X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass) ∧
  (cost ≤ g.toNat → ∃ s' : State,
    X (g.toNat + 1) (D_J code 0) s0 = .ok (.success s' output) ∧
    (s'.createdAccounts, s'.accountMap) = acc ∧
    s'.machineState.gasAvailable = g.subNat cost)

/-- Threshold-exact revert termination. -/
def RDxRev (code : ByteArray) (g : Sat256) (s0 : State) (cost : Nat) : Prop :=
  (g.toNat < cost → X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass) ∧
  (cost ≤ g.toNat → ∃ g' output,
    X (g.toNat + 1) (D_J code 0) s0 = .ok (.revert g' output) ∧
    g' = (g.subNat cost).toUInt256)

/-- Threshold-exact exceptional termination.

This is distinct from `RDxRev`: an EVM exception has no return payload or remaining-gas result.
At the call boundary it is therefore suitable for precompile-style validation failures that consume
all gas forwarded to the failed call. -/
def RDxErr (code : ByteArray) (g : Sat256) (s0 : State)
    (exception : ExecutionException) (cost : Nat) : Prop :=
  (g.toNat < cost → X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass) ∧
  (cost ≤ g.toNat → X (g.toNat + 1) (D_J code 0) s0 = .error exception)

private theorem terminalOOGExact
    {code : ByteArray} {g : Sat256} {s0 s next : State}
    {k C cost : Nat} {cause : HaltCause} {output : ByteArray}
    (hgas : s.machineState.gasAvailable = g.subNat C)
    (hstep : Xstep (D_J code 0) s =
      if s.machineState.gasAvailable.toNat < cost then .error .OutOfGass
      else .ok (next, .some (cause, output)))
    (hk : k ≤ C) (hC : C ≤ g.toNat) (hlow : g.toNat < C + cost)
    (hX : X (g.toNat + 1) (D_J code 0) s0 =
      X (g.toNat + 1 - k) (D_J code 0) s) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass := by
  rw [hX]
  have hgg : s.machineState.gasAvailable.toNat < cost := by
    rw [hgas, Sat256.subNat_toNat]
    omega
  have hs : Xstep (D_J code 0) s = .error .OutOfGass := by
    rw [hstep, if_pos hgg]
  have hfuel : g.toNat + 1 - k = (g.toNat + 1 - (k + 1)) + 1 := by omega
  rw [hfuel]
  exact Ethereum.EVM.Xstep_X_X_except _ s _ _ hs

/-- Generic threshold-exact successful halt for a gas-agnostic terminal operation. -/
theorem RDx.haltSuccess
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata output : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C cost : Nat} (next : State → State)
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C)
    (hstep : ∀ s : State, RDxMatches code ee s0 pc stk mem aw rdata acc s →
      Xstep (D_J code 0) s =
        if s.machineState.gasAvailable.toNat < cost then .error .OutOfGass
        else .ok (next s, .some (.success, output)))
    (hacc : ∀ s : State, RDxMatches code ee s0 pc stk mem aw rdata acc s →
      ((next s).createdAccounts, (next s).accountMap) = acc)
    (hnextGas : ∀ s : State, RDxMatches code ee s0 pc stk mem aw rdata acc s →
      (next s).machineState.gasAvailable = s.machineState.gasAvailable.subNat cost) :
    RDxRet code g s0 acc output (C + cost) := by
  rcases h with ⟨hk, hoog, hreach⟩
  constructor
  · intro hlow
    by_cases hC : C ≤ g.toNat
    · obtain ⟨s, hX, hgas, hm⟩ := hreach hC
      exact terminalOOGExact hgas (hstep s hm) hk hC hlow hX
    · exact hoog (Nat.lt_of_not_ge hC)
  · intro henough
    have hC : C ≤ g.toNat := by omega
    obtain ⟨s, hX, hgas, hm⟩ := hreach hC
    refine ⟨next s, hX.trans (stepHaltSuccess hgas (hstep s hm) hk henough),
      hacc s hm, ?_⟩
    rw [hnextGas s hm, hgas, Sat256.subNat_subNat]

/-- Generic threshold-exact reverting halt for a gas-agnostic terminal operation. -/
theorem RDx.haltRevert
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata output : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C cost : Nat} (next : State → State)
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C)
    (hstep : ∀ s : State, RDxMatches code ee s0 pc stk mem aw rdata acc s →
      Xstep (D_J code 0) s =
        if s.machineState.gasAvailable.toNat < cost then .error .OutOfGass
        else .ok (next s, .some (.revert, output)))
    (hnextGas : ∀ s : State, RDxMatches code ee s0 pc stk mem aw rdata acc s →
      (next s).machineState.gasAvailable = s.machineState.gasAvailable.subNat cost) :
    RDxRev code g s0 (C + cost) := by
  rcases h with ⟨hk, hoog, hreach⟩
  constructor
  · intro hlow
    by_cases hC : C ≤ g.toNat
    · obtain ⟨s, hX, hgas, hm⟩ := hreach hC
      exact terminalOOGExact hgas (hstep s hm) hk hC hlow hX
    · exact hoog (Nat.lt_of_not_ge hC)
  · intro henough
    have hC : C ≤ g.toNat := by omega
    obtain ⟨s, hX, hgas, hm⟩ := hreach hC
    refine ⟨(next s).machineState.gasAvailable.toUInt256, output,
      hX.trans (stepHaltRevert hgas (hstep s hm) hk henough), ?_⟩
    rw [hnextGas s hm, hgas, Sat256.subNat_subNat]

/-- Close an exact cursor with a gas-guarded exceptional instruction. -/
theorem RDx.haltError
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C cost : Nat} {exception : ExecutionException}
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C)
    (hstep : ∀ s : State, RDxMatches code ee s0 pc stk mem aw rdata acc s →
      Xstep (D_J code 0) s =
        if s.machineState.gasAvailable.toNat < cost then .error .OutOfGass
        else .error exception) :
    RDxErr code g s0 exception (C + cost) := by
  rcases h with ⟨hk, hoog, hreach⟩
  constructor
  · intro hlow
    by_cases hC : C ≤ g.toNat
    · obtain ⟨s, hX, hgas, hm⟩ := hreach hC
      rw [hX]
      have hgg : s.machineState.gasAvailable.toNat < cost := by
        rw [hgas, Sat256.subNat_toNat]
        omega
      have hs : Xstep (D_J code 0) s = .error .OutOfGass := by
        rw [hstep s hm, if_pos hgg]
      have hfuel : g.toNat + 1 - k = (g.toNat + 1 - (k + 1)) + 1 := by omega
      rw [hfuel]
      exact Ethereum.EVM.Xstep_X_X_except _ s _ _ hs
    · exact hoog (Nat.lt_of_not_ge hC)
  · intro henough
    have hC : C ≤ g.toNat := by omega
    obtain ⟨s, hX, hgas, hm⟩ := hreach hC
    rw [hX]
    have hgg : ¬s.machineState.gasAvailable.toNat < cost := by
      rw [hgas, Sat256.subNat_toNat]
      omega
    have hs : Xstep (D_J code 0) s = .error exception := by
      rw [hstep s hm, if_neg hgg]
    have hfuel : g.toNat + 1 - k = (g.toNat + 1 - (k + 1)) + 1 := by omega
    rw [hfuel]
    exact Ethereum.EVM.Xstep_X_X_except _ s _ _ hs

/-- Close an exact cursor with an exceptional instruction that has no ordinary gas guard, such as
`INVALID`.  The exact threshold is the cost already accumulated on the path to that instruction. -/
theorem RDx.fail
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {exception : ExecutionException}
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C)
    (hstep : ∀ s : State, RDxMatches code ee s0 pc stk mem aw rdata acc s →
      Xstep (D_J code 0) s = .error exception) :
    RDxErr code g s0 exception C := by
  have herr := RDx.haltError (cost := 0) h (fun s hm => by simpa using hstep s hm)
  simpa using herr

/-- Exact `RETURN`: insufficient total gas is precisely OOG; sufficient gas returns `output` with
exactly `C + memoryCost` gas consumed. -/
theorem RDx.ret
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {off len : UInt256} {t : List UInt256} (memoryCost : Nat) (output : ByteArray)
    (h : RDx code ee g s0 pc (off :: len :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.RETURN, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = off :: len :: t → memoryExpansionCost s .RETURN = memoryCost)
    (houtput : mem.readWithPadding off.toNat len.toNat = output)
    (hov : t.length ≤ 1024) :
    RDxRet code g s0 acc output (C + memoryCost) := by
  apply RDx.haltSuccess (cost := memoryCost) (fun s => stReturn s off len t) h
  · intro s hm
    rcases hm with ⟨hcode, hpc, hstk, hmem, haw, _hrdata, _hacc, _hee, _hworld⟩
    have hs := return_xstep hcode hpc hdec hstk hov
    rw [hmc s haw hstk, show s.machineState.memory.readWithPadding off.toNat len.toNat = output
      from by rw [hmem, houtput]] at hs
    exact hs
  · intro s hm
    rcases hm with ⟨_hcode, _hpc, _hstk, _hmem, _haw, _hrdata, hacc, _hee, _hworld⟩
    simpa only [stReturn] using hacc
  · intro s hm
    rcases hm with ⟨_hcode, _hpc, hstk, _hmem, haw, _hrdata, _hacc, _hee, _hworld⟩
    simp only [stReturn]
    rw [hmc s haw hstk]
    simp

/-- Exact `STOP`, whose local charge is zero. -/
theorem RDx.stop
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.STOP, .none))
    (hov : stk.length ≤ 1024) :
    RDxRet code g s0 acc ByteArray.empty C := by
  have hr := RDx.haltSuccess (cost := 0) stStop h
    (fun s hm => by
      rcases hm with ⟨hcode, hpc, hstk, _hmem, _haw, _hrdata, _hacc, _hee, _hworld⟩
      have hs := stop_xstep hcode hpc hdec hstk hov
      simpa using hs)
    (fun _ hm => by simpa only [stStop] using hm.2.2.2.2.2.2.1)
    (fun _ _ => by simp [stStop])
  simpa using hr

/-- Exact `REVERT` with a resolved return byte array. -/
theorem RDx.revOutput
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {off len : UInt256} {t : List UInt256} (memoryCost : Nat) (output : ByteArray)
    (h : RDx code ee g s0 pc (off :: len :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.REVERT, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = off :: len :: t → memoryExpansionCost s .REVERT = memoryCost)
    (houtput : mem.readWithPadding off.toNat len.toNat = output)
    (hov : t.length ≤ 1024) :
    RDxRev code g s0 (C + memoryCost) := by
  apply RDx.haltRevert (cost := memoryCost) (fun s => stRevert s off len t) h
  · intro s hm
    rcases hm with ⟨hcode, hpc, hstk, hmem, haw, _hrdata, _hacc, _hee, _hworld⟩
    have hs := revert_xstep hcode hpc hdec hstk hov
    rw [hmc s haw hstk, show s.machineState.memory.readWithPadding off.toNat len.toNat = output
      from by rw [hmem, houtput]] at hs
    exact hs
  · intro s hm
    rcases hm with ⟨_hcode, _hpc, hstk, _hmem, haw, _hrdata, _hacc, _hee, _hworld⟩
    simp only [stRevert]
    rw [hmc s haw hstk]
    simp

/-- Exact `REVERT` in the argument order used by the established symbolic-execution DSL.  The
revert payload is intentionally existential in `RDxRev`, so no output-resolution premise is
needed. -/
theorem RDx.rev
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    {off len : UInt256} {t : List UInt256} (memoryCost : Nat)
    (h : RDx code ee g s0 pc (off :: len :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.REVERT, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = off :: len :: t → memoryExpansionCost s .REVERT = memoryCost)
    (hov : t.length ≤ 1024) :
    RDxRev code g s0 (C + memoryCost) := by
  exact RDx.revOutput memoryCost (mem.readWithPadding off.toNat len.toNat)
    h hdec hmc rfl hov

/-- `INVALID` closes an exact cursor with `InvalidInstruction`, rather than with `REVERT`. -/
theorem RDx.invalid
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.INVALID, .none)) :
    RDxErr code g s0 .InvalidInstruction C := by
  apply RDx.fail h
  intro s hm
  have hs : decode s.executionEnv.code s.machineState.pc = some (.INVALID, .none) := by
    simpa only [hm.1, hm.2.1] using hdec
  simpa only [hm.1] using step_invalid s hs

/-- Forget the retained threshold and exact remaining gas, recovering ordinary functional
termination. -/
theorem RDxRet.toRDret
    {code : ByteArray} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {output : ByteArray} {cost : Nat}
    (h : RDxRet code g s0 acc output cost) : RDret code g s0 acc output := by
  rcases h with ⟨hoog, hsuccess⟩
  by_cases hC : cost ≤ g.toNat
  · obtain ⟨s, hX, hacc, _hgas⟩ := hsuccess hC
    exact Or.inr ⟨s, hX, hacc⟩
  · exact Or.inl (hoog (Nat.lt_of_not_ge hC))

/-- Forget the threshold retained by an exact revert proof. -/
theorem RDxRev.toRDrev
    {code : ByteArray} {g : Sat256} {s0 : State} {cost : Nat}
    (h : RDxRev code g s0 cost) : RDrev code g s0 := by
  rcases h with ⟨hoog, hrevert⟩
  by_cases hC : cost ≤ g.toNat
  · obtain ⟨g', output, hX, _hgas⟩ := hrevert hC
    exact Or.inr ⟨g', output, hX⟩
  · exact Or.inl (hoog (Nat.lt_of_not_ge hC))

/-- At the iterator level, OOG occurs exactly below the retained threshold. -/
theorem RDxRet.oog_iff
    {code : ByteArray} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {output : ByteArray} {cost : Nat}
    (h : RDxRet code g s0 acc output cost) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ↔ g.toNat < cost := by
  rcases h with ⟨hoog, hsuccess⟩
  constructor
  · intro hresult
    by_contra hnot
    obtain ⟨s, hsuccess, _hacc, _hgas⟩ := hsuccess (Nat.le_of_not_gt hnot)
    rw [hresult] at hsuccess
    contradiction
  · exact hoog

/-- At the iterator level, an exact exceptional trace is OOG precisely below its threshold, as
long as its deliberate exception is not itself `OutOfGass`. -/
theorem RDxErr.oog_iff
    {code : ByteArray} {g : Sat256} {s0 : State}
    {exception : ExecutionException} {cost : Nat}
    (hneq : exception ≠ .OutOfGass)
    (h : RDxErr code g s0 exception cost) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ↔ g.toNat < cost := by
  rcases h with ⟨hoog, herror⟩
  constructor
  · intro hresult
    by_contra hnot
    have herr := herror (Nat.le_of_not_gt hnot)
    have heq : (.OutOfGass : ExecutionException) = exception :=
      Except.error.inj (hresult.symm.trans herr)
    exact hneq heq.symm
  · exact hoog

private theorem xiErrorOfXExact
    {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {e} {g : Sat256}
    (h : X (g.toNat + 1) (D_J I.code 0)
      (Reasoning.Theory.initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .error e) :
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g.toUInt256 A I = .error e :=
  Xi_error_of_X (g := g.toUInt256) (by
    simpa [Reasoning.Theory.initState, Sat256.ofUInt256, Sat256.toUInt256] using h)

private theorem xiSuccessOfXExact
    {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {s' output} {g : Sat256}
    (h : X (g.toNat + 1) (D_J I.code 0)
      (Reasoning.Theory.initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .ok (.success s' output)) :
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g.toUInt256 A I =
      .ok (.success (s'.createdAccounts, s'.accountMap,
        s'.machineState.gasAvailable.toUInt256, s'.substate) output) :=
  Xi_success_of_X (g := g.toUInt256) (by
    simpa [Reasoning.Theory.initState, Sat256.ofUInt256, Sat256.toUInt256] using h)

/-- Exact raw `Ξ` characterization.  Both gas cases retain their conditions, so sufficient gas
rules out the OOG alternative. -/
theorem RDxRet.xiResult
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {code output : ByteArray} {cost : Nat}
    (hcode : I.code = code)
    (h : RDxRet code g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      (cA, σ) output cost) :
    (g.toNat < cost → Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass) ∧
    (cost ≤ g.toNat → ∃ A' : Substate,
      Ξ cA gh bl σ σ₀ g.toUInt256 A I =
        .ok (.success (cA, σ, (g.subNat cost).toUInt256, A') output)) := by
  rcases h with ⟨hoog, hsuccess⟩
  constructor
  · intro hlow
    apply xiErrorOfXExact
    rw [hcode]
    exact hoog hlow
  · intro henough
    obtain ⟨s, hX, hacc, hgas⟩ := hsuccess henough
    have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    refine ⟨s.substate, ?_⟩
    have hxi := xiSuccessOfXExact (by rw [hcode]; exact hX)
    rw [hcA, hσ, hgas] at hxi
    exact hxi

/-- Exact public `Ξ` characterization of an exceptional trace. -/
theorem RDxErr.xiResult
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {code : ByteArray} {exception : ExecutionException} {cost : Nat}
    (hcode : I.code = code)
    (h : RDxErr code g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      exception cost) :
    (g.toNat < cost → Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass) ∧
    (cost ≤ g.toNat → Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error exception) := by
  rcases h with ⟨hoog, herror⟩
  constructor
  · intro hlow
    apply xiErrorOfXExact
    rw [hcode]
    exact hoog hlow
  · intro henough
    apply xiErrorOfXExact
    rw [hcode]
    exact herror henough

/-- At the public boundary, a deliberate non-OOG exception occurs exactly on the sufficient-gas
side of the threshold. -/
theorem RDxErr.xiOOG_iff
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {code : ByteArray} {exception : ExecutionException} {cost : Nat}
    (hneq : exception ≠ .OutOfGass)
    (hcode : I.code = code)
    (h : RDxErr code g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      exception cost) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass ↔ g.toNat < cost := by
  have hresult := h.xiResult hcode
  constructor
  · intro hoog
    by_contra hnot
    have herr := hresult.2 (Nat.le_of_not_gt hnot)
    have heq : (.OutOfGass : ExecutionException) = exception :=
      Except.error.inj (hoog.symm.trans herr)
    exact hneq heq.symm
  · exact hresult.1

/-- At the public `Ξ` boundary, OOG is equivalent to supplying less than the exact cost. -/
theorem RDxRet.xiOOG_iff
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {code output : ByteArray} {cost : Nat}
    (hcode : I.code = code)
    (h : RDxRet code g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      (cA, σ) output cost) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass ↔ g.toNat < cost := by
  have hresult := h.xiResult hcode
  constructor
  · intro hoog
    by_contra hnot
    obtain ⟨A', hsuccess⟩ := hresult.2 (Nat.le_of_not_gt hnot)
    rw [hoog] at hsuccess
    contradiction
  · exact hresult.1

/-! A small end-to-end check of the public rules: `PUSH0; STOP` has threshold and exact cost 2. -/

private def push0StopCode : ByteArray := ⟨#[0x5f, 0x00]⟩

private def push0InvalidCode : ByteArray := ⟨#[0x5f, 0xfe]⟩

example
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = push0StopCode) :
    RDxRet push0StopCode g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      (cA, σ) ByteArray.empty 2 := by
  have h0 := RDx.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hcode
  have h1 := h0.push0 (by native_decide) (by norm_num)
  simpa using h1.stop (by native_decide) (by norm_num)

/-- The same exact prefix closed by `INVALID`: below gas 2 the prefix is OOG; otherwise execution
fails with `InvalidInstruction`. -/
example
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hcode : I.code = push0InvalidCode) :
    RDxErr push0InvalidCode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) .InvalidInstruction 2 := by
  have h0 := RDx.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hcode
  have h1 := h0.push0 (by native_decide) (by norm_num)
  simpa using h1.invalid (by native_decide)

end Reasoning.Reach
