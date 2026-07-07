import Benchmarks.WETH9.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.WETH9

/-! ### SELFBALANCE (cost `Glow = 5`, pc += 1, pushes the code owner's balance)

    Mirrors `CHAINID`/`CALLER`: a 0-pop / 1-push opcode.  The pushed word is the balance of
    `codeOwner` in the current account map (`accountMap.find? codeOwner |>.elim ⟨0⟩ (·.balance)`).
    `RD` hides the cursor `s`, so the combinator states the pushed value through the tracked
    `acc = (createdAccounts, accountMap)` and `ee` (`acc.2` is the account map, `ee.codeOwner`
    the owner). -/

def stSelfbalance (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := (s.accountMap.find? s.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) ::
        s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat GasConstants.Glow } }

theorem selfbalance_xstep {s : State} {code : ByteArray} {pcv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SELFBALANCE, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < GasConstants.Glow then .error .OutOfGass
         else .ok (stSelfbalance s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SELFBALANCE, .none) := by
    rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_selfbalance s hd, if_neg hov']
  simp only [GasConstants.Glow, stSelfbalance]

/-- **SELFBALANCE**: push the code owner's balance (`acc.2.find? ee.codeOwner |>.elim ⟨0⟩ (·.balance)`)
    onto the stack (cost `Glow = 5`, pc += 1). -/
theorem RD.selfbalance {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.SELFBALANCE, .none))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      ((acc.2.find? ee.codeOwner |>.elim ⟨0⟩ (·.balance)) :: stk) mem aw rdata acc
      (k + 1) (C + GasConstants.Glow) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := selfbalance_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + GasConstants.Glow
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stSelfbalance s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
        (by have : 1 ≤ GasConstants.Glow := (by decide); omega), by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stSelfbalance]; exact hcode
      · simp only [stSelfbalance]; rw [hpc]
      · have haccm : s.accountMap = acc.2 := by rw [← hacc]
        simp only [stSelfbalance]; rw [hstk, hee, haccm]
      · simp only [stSelfbalance]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stSelfbalance]; exact hmem
      · simp only [stSelfbalance]; exact haw
      · simp only [stSelfbalance]; exact hrdata
      · simp only [stSelfbalance]; exact hacc
      · exact hee
      · exact hworld

/-! ### LOG2 (pops `[offset, size, t1, t2]`, appends a 2-topic log, pushes nothing)

    Identical to `LOG3` with one fewer topic: pops 4 (no `e`), topics `#[c, d]`, and
    `2 * Glogtopic` instead of `3 * Glogtopic`.  The `substate.logSeries` append is invisible to
    `RD`.  Requires `ee.perm` (aborts in static mode). -/

def stLog2 (s : State) (a b c d : UInt256) (t : List UInt256) : State :=
  {s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG2)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat
            + 2 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

theorem log2_xstep {s : State} {code : ByteArray} {pcv a b c d : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG2, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat
            < memoryExpansionCost s .LOG2
              + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
         then .error .OutOfGass else .ok (stLog2 s a b c d t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG2, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_log2 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: t).length - 4 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, stLog2]

/-- **LOG2**: pop `[offset, size, t1, t2]`, append a log over `mem[offset..offset+size]` with the
    two topics (cost `memExp + Glog + Glogdata·size + 2·Glogtopic`, pc += 1).  Requires `ee.perm`
    (aborts in static mode).  The `substate.logSeries` append is invisible to `RD`. -/
theorem RD.log2 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG2, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: t →
        memoryExpansionCost s .LOG2 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 2 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG2 = mcost := hmc s haw hstk
    have hperms : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have st := log2_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stLog2 s a b c d t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stLog2]; exact hcode
      · simp only [stLog2]; rw [hpc]
      · simp only [stLog2]
      · simp only [stLog2, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stLog2]; exact hmem
      · simp only [stLog2]; rw [haw, hawout]
      · simp only [stLog2]; exact hrdata
      · simp only [stLog2]; exact hacc
      · simp only [stLog2]; exact hee
      · simp only [stLog2]; exact hworld

end Benchmarks.WETH9
