import TruthClaude.Theory

/-!
# Stepping — reusable per-opcode `Xstep` wrappers

For each opcode used by a trace we give:
* a **successor-state** `def st<Op>` matching the `Ethereum.Theory.OpcodeLemmas` `step_*`
  output (so the successor is *named* and its fields project cleanly), and
* an `<op>_xstep` lemma putting `Xstep` into the single-guard shape
  `if gas < cost then OutOfGass else .ok (st<Op> …, ctrl)`
  that `TruthClaude.Theory.stepContinue`/`stepOOG`/`stepHalt*` consume.

These are **contract-agnostic** (parameterised by the code `ByteArray`); only the `decode`
facts fed to them are contract-specific.
-/

open Act ABI Ethereum Ethereum.EVM

namespace TruthClaude.Theory

/-- The derived `BEq UInt256` is lawful (it reduces to `Fin` equality). -/
instance : LawfulBEq UInt256 where
  eq_of_beq {a b} h := by
    rcases a with ⟨a⟩; rcases b with ⟨b⟩
    have : a = b := eq_of_beq h
    rw [this]
  rfl {a} := by rcases a with ⟨a⟩; exact beq_self_eq_true a

/-- `isZero` of a non-zero word is `0`. -/
theorem isZero_eq_zero_of_ne {a : UInt256} (h : a ≠ ⟨0⟩) : UInt256.isZero a = ⟨0⟩ := by
  simp only [UInt256.isZero, UInt256.eq0]
  rw [beq_eq_false_iff_ne.mpr h]
  rfl

/-! ### PUSH1 (cost 3, pc += 2) -/

def stPush1 (s : State) (arg : UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + UInt256.ofNat 2,
      stack := arg :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 3 } }

theorem push1_xstep {s : State} {code : ByteArray} {pcv argv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.Push .PUSH1, some (argv, 1)))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stPush1 s argv, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.Push .PUSH1, some (argv, 1)) := by
    rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_push1 s argv hd, if_neg hov']
  simp only [GasConstants.Gverylow, stPush1]

/-! ### PUSH0 (cost 2, pc += 1, pushes 0) -/

def stPush0 (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := ⟨0⟩ :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 2 } }

theorem push0_xstep {s : State} {code : ByteArray} {pcv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.PUSH0, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
         else .ok (stPush0 s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.PUSH0, .none) := by
    rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_push0 s hd, if_neg hov']
  simp only [GasConstants.Gbase, stPush0]

/-! ### CALLVALUE (cost 2, pc += 1, pushes weiValue) -/

def stCallvalue (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := s.executionEnv.weiValue :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 2 } }

theorem callvalue_xstep {s : State} {code : ByteArray} {pcv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.CALLVALUE, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
         else .ok (stCallvalue s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.CALLVALUE, .none) := by
    rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_callvalue s hd, if_neg hov']
  simp only [GasConstants.Gbase, stCallvalue]

/-! ### DUP1 (cost 3, pc += 1, duplicates top) -/

def stDup1 (s : State) (a : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := a :: a :: t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 3 } }

theorem dup1_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP1, .none))
    (hstk : s.machineState.stack = a :: t) (hov : (a :: t).length - 1 + 2 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stDup1 s a t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP1, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup1 s hd, hstk]
  have hov' : ¬ ((a :: t).length - 1 + 2 > 1024) := by simp only [List.length_cons] at hov ⊢; omega
  simp only [if_neg hov', GasConstants.Gverylow, stDup1]

/-! ### ISZERO (cost 3, pc += 1, top ↦ isZero top) -/

def stIsZero (s : State) (a : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.isZero a :: t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 3 } }

theorem iszero_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.ISZERO, .none))
    (hstk : s.machineState.stack = a :: t) (hov : (a :: t).length - 1 + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stIsZero s a t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.ISZERO, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_iszero s hd, hstk]
  have hov' : ¬ ((a :: t).length - 1 + 1 > 1024) := by simp only [List.length_cons] at hov ⊢; omega
  simp only [if_neg hov', GasConstants.Gverylow, stIsZero]

/-! ### MSTORE (two-stage cost `memExp + 3`, pc += 1, pops 2) -/

def stMStore (s : State) (a b : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := t,
      memory := b.toByteArray.write 0 s.machineState.memory a.toNat 32,
      activeWords := UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat 32),
      execLength := s.machineState.execLength + 1,
      gasAvailable :=
        (s.machineState.gasAvailable - UInt256.ofNat (memoryExpansionCost s .MSTORE))
          - UInt256.ofNat 3 } }

theorem mstore_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.MSTORE, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .MSTORE + 3
         then .error .OutOfGass else .ok (stMStore s a b t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.MSTORE, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_mstore s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov']
  rw [collapse_two_stage]
  simp only [GasConstants.Gverylow, stMStore]

/-! ### JUMPI not-taken (condition `⟨0⟩` ⇒ no jump, cost 10, pc += 1, pops 2) -/

def stJumpiNT (s : State) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 10 } }

theorem jumpi_nt_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.JUMPI, .none))
    (hstk : s.machineState.stack = a :: ⟨0⟩ :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 10 then .error .OutOfGass
         else .ok (stJumpiNT s t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.JUMPI, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_jumpi s hd, hstk]
  have hbne : ((⟨0⟩ : UInt256) != (⟨0⟩ : UInt256)) = false := by decide
  have hov' : ¬ ((a :: (⟨0⟩ : UInt256) :: t).length - 2 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [hbne, Bool.false_eq_true, false_and, hov', GasConstants.Ghigh, stJumpiNT,
    if_false]

/-! ### REVERT (halt; cost `memExp`, output `m[a..a+b]`) -/

def stRevert (s : State) (a b : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := t,
      H_return := s.machineState.memory.readWithPadding a.toNat b.toNat,
      activeWords :=
        let m := MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat
        UInt256.ofNat (MachineState.M (UInt256.ofNat m).toNat a.toNat b.toNat),
      execLength := s.machineState.execLength + 1,
      gasAvailable :=
        (s.machineState.gasAvailable - UInt256.ofNat (memoryExpansionCost s .REVERT))
          - UInt256.ofNat 0 } }

theorem revert_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.REVERT, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .REVERT
         then .error .OutOfGass
         else .ok (stRevert s a b t,
                   .some (false, s.machineState.memory.readWithPadding a.toNat b.toNat))) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.REVERT, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_revert s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gzero, stRevert]

end TruthClaude.Theory
