import Reasoning.Theory

/-!
# Stepping — reusable per-opcode `Xstep` wrappers

For each opcode used by a trace we give:
* a **successor-state** `def st<Op>` matching the `Ethereum.Theory.OpcodeLemmas` `step_*`
  output (so the successor is *named* and its fields project cleanly), and
* an `<op>_xstep` lemma putting `Xstep` into the single-guard shape
  `if gas < cost then OutOfGass else .ok (st<Op> …, ctrl)`
  that `Reasoning.Theory.stepContinue`/`stepOOG`/`stepHalt*` consume.

These are **contract-agnostic** (parameterised by the code `ByteArray`); only the `decode`
facts fed to them are contract-specific.
-/

open Act ABI Ethereum Ethereum.EVM

namespace Reasoning.Theory

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

/-- Equal `ByteArray`s under `==` have equal size. -/
theorem byteArray_size_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a.size = b.size := by
  unfold ByteArray.size
  refine congrArg Array.size (eq_of_beq ?_)
  simpa [BEq.beq, ByteArray.instBEq] using h

/-- `1 ≠ 0` as `UInt256`. -/
theorem one_ne_zero_uint : (⟨1⟩ : UInt256) ≠ ⟨0⟩ := by decide

/-- `ofNat` reflects `<` for non-wrapping naturals. -/
theorem ofNat_lt_ofNat {a b : ℕ} (ha : a < UInt256.size) (hb : b < UInt256.size) :
    (UInt256.ofNat a < UInt256.ofNat b) ↔ a < b := by
  have hva : (UInt256.ofNat a).val.val = a := by
    simp [UInt256.ofNat, Id.run, Fin.ofNat, Nat.mod_eq_of_lt ha]
  have hvb : (UInt256.ofNat b).val.val = b := by
    simp [UInt256.ofNat, Id.run, Fin.ofNat, Nat.mod_eq_of_lt hb]
  show (UInt256.ofNat a).val.val < (UInt256.ofNat b).val.val ↔ a < b
  rw [hva, hvb]

/-- `calldatasize < 4` ⇒ the dispatcher's `LT` guard is non-zero (the short-calldata revert). -/
theorem lt_four_ne_zero_of_lt {n : ℕ} (h : n < 4) :
    UInt256.lt (UInt256.ofNat n) (UInt256.ofNat 4) ≠ ⟨0⟩ := by
  have hlt : UInt256.ofNat n < UInt256.ofNat 4 :=
    (ofNat_lt_ofNat (lt_trans h (by decide)) (by decide)).mpr h
  simp only [UInt256.lt, decide_eq_true hlt]; decide

/-- `calldatasize ≥ 4` (no wrap) ⇒ the dispatcher's `LT` guard is zero (the dispatch path). -/
theorem lt_four_eq_zero_of_ge {n : ℕ} (h : 4 ≤ n) (hb : n < UInt256.size) :
    UInt256.lt (UInt256.ofNat n) (UInt256.ofNat 4) = ⟨0⟩ := by
  have hnlt : ¬ (UInt256.ofNat n < UInt256.ofNat 4) := by
    rw [ofNat_lt_ofNat hb (by decide)]; omega
  simp only [UInt256.lt, decide_eq_false hnlt]; decide

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

/-! ### PUSH2 (cost 3, pc += 3) -/

def stPush2 (s : State) (arg : UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + UInt256.ofNat 3,
      stack := arg :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 3 } }

theorem push2_xstep {s : State} {code : ByteArray} {pcv argv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.Push .PUSH2, some (argv, 2)))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stPush2 s argv, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.Push .PUSH2, some (argv, 2)) := by
    rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_push2 s argv hd, if_neg hov']
  simp only [GasConstants.Gverylow, stPush2]

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

/-! ### RETURN (halt *success*, output `mem[a .. a+b]`, single memory-gas guard) -/

def stReturn (s : State) (a b : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := t,
      H_return := s.machineState.memory.readWithPadding a.toNat b.toNat,
      activeWords :=
        UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat),
      execLength := s.machineState.execLength + 1,
      gasAvailable :=
        (s.machineState.gasAvailable - UInt256.ofNat (memoryExpansionCost s .RETURN))
          - UInt256.ofNat 0 } }

theorem return_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.RETURN, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .RETURN
         then .error .OutOfGass
         else .ok (stReturn s a b t,
                   .some (true, s.machineState.memory.readWithPadding a.toNat b.toNat))) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.RETURN, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_return s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gzero, stReturn]

/-! ### MLOAD (pop 1, push `mem`-word, two-stage gas `memCost + 3`) -/

def stMLoad (s : State) (a : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack :=
        (if a.toNat ≥ s.machineState.memory.size ∨ a ≥ s.machineState.activeWords * ⟨32⟩ then ⟨0⟩
         else UInt256.ofNat
                (fromByteArrayBigEndian (s.machineState.memory.readWithPadding a.toNat 32))) :: t,
      activeWords :=
        UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat 32),
      execLength := s.machineState.execLength + 1,
      gasAvailable :=
        (s.machineState.gasAvailable - UInt256.ofNat (memoryExpansionCost s .MLOAD))
          - UInt256.ofNat 3 } }

theorem mload_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.MLOAD, .none))
    (hstk : s.machineState.stack = a :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .MLOAD + 3
         then .error .OutOfGass else .ok (stMLoad s a t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.MLOAD, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_mload s hd, hstk]
  have hov' : ¬ ((a :: t).length - 1 + 1 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov']
  rw [collapse_two_stage]
  simp only [GasConstants.Gverylow, stMLoad]

/-! ### Binary ops (`a :: b :: t ↦ res :: t`, cost 3, pc += 1) -/

def stBinop (s : State) (res : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩, stack := res :: t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 3 } }

theorem eq_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.EQ, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.eq a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.EQ, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_eq s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem lt_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LT, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.lt a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LT, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_lt s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem shr_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SHR, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.shiftRight b a) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SHR, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_shr s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem sub_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SUB, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.sub a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SUB, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_sub s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem slt_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SLT, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.slt a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SLT, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_slt s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem add_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.ADD, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (a + b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.ADD, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_add s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

/-! ### MUL (cost 5 = `Glow`, `a :: b :: t ↦ mul a b :: t`, pc += 1) -/

def stMul (s : State) (res : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩, stack := res :: t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 5 } }

theorem mul_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.MUL, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
         else .ok (stMul s (UInt256.mul a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.MUL, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_mul s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Glow, stMul]

/-! ### POP (cost 2, pc += 1, drops top) -/

def stPop (s : State) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩, stack := t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 2 } }

theorem pop_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.POP, .none))
    (hstk : s.machineState.stack = a :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
         else .ok (stPop s t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.POP, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_pop s hd, hstk]
  have hov' : ¬ ((a :: t).length - 1 + 0 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gbase, stPop]

/-! ### CALLDATASIZE (cost 2, pc += 1, pushes calldata size) -/

def stCalldatasize (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.ofNat s.executionEnv.calldata.size :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 2 } }

theorem calldatasize_xstep {s : State} {code : ByteArray} {pcv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.CALLDATASIZE, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
         else .ok (stCalldatasize s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.CALLDATASIZE, .none) := by rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_calldatasize s hd, if_neg hov']
  simp only [GasConstants.Gbase, stCalldatasize]

/-! ### CALLDATALOAD (cost 3, pc += 1, loads a 32-byte calldata word) -/

def stCalldataload (s : State) (a : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := (uInt256OfByteArray <| s.executionEnv.calldata.readBytes a.toNat 32) :: t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 3 } }

theorem calldataload_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.CALLDATALOAD, .none))
    (hstk : s.machineState.stack = a :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stCalldataload s a t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.CALLDATALOAD, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_calldataload s hd, hstk]
  have hov' : ¬ ((a :: t).length - 1 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stCalldataload]

/-! ### PUSH4 (cost 3, pc += 5) -/

def stPush4 (s : State) (arg : UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + UInt256.ofNat 5,
      stack := arg :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 3 } }

theorem push4_xstep {s : State} {code : ByteArray} {pcv argv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.Push .PUSH4, some (argv, 4)))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stPush4 s argv, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.Push .PUSH4, some (argv, 4)) := by rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_push4 s argv hd, if_neg hov']
  simp only [GasConstants.Gverylow, stPush4]

/-! ### JUMPDEST (cost 1, pc += 1) -/

def stJumpdest (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 1 } }

theorem jumpdest_xstep {s : State} {code : ByteArray} {pcv : UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.JUMPDEST, .none))
    (hov : s.machineState.stack.length ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 1 then .error .OutOfGass
         else .ok (stJumpdest s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.JUMPDEST, .none) := by rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 0 > 1024) := by omega
  rw [← hcode, step_jumpdest s hd, if_neg hov']
  simp only [GasConstants.Gjumpdest, stJumpdest]

/-! ### JUMP / JUMPI taken (need the valid-jump fact `(D_J code 0).contains target`) -/

def stJump (s : State) (a : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := a, stack := t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 8 } }

theorem jump_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.JUMP, .none))
    (hstk : s.machineState.stack = a :: t)
    (hjd : (D_J code ⟨0⟩).contains a = true) (hov : t.length ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 8 then .error .OutOfGass
         else .ok (stJump s a t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.JUMP, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_jump s hd, hstk]
  have hov' : ¬ ((a :: t).length - 1 + 0 > 1024) := by simp only [List.length_cons]; omega
  simp only [hcode, hjd, not_true_eq_false, if_false, if_neg hov', GasConstants.Gmid, stJump]

/-! ### SWAP / DUP (cost 3, pc += 1) -/

def stSwap (s : State) (stk : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩, stack := stk,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 3 } }

theorem swap1_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP1, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 2 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (b :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP1, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap1 s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 2 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem swap2_xstep {s : State} {code : ByteArray} {pcv a b c : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP2, .none))
    (hstk : s.machineState.stack = a :: b :: c :: t) (hov : t.length + 3 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (c :: b :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP2, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap2 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: t).length - 3 + 3 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem swap3_xstep {s : State} {code : ByteArray} {pcv a b c d : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP3, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: t) (hov : t.length + 4 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (d :: b :: c :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP3, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap3 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: t).length - 4 + 4 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem dup2_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP2, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 3 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (b :: a :: b :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP2, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup2 s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 3 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem dup3_xstep {s : State} {code : ByteArray} {pcv a b c : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP3, .none))
    (hstk : s.machineState.stack = a :: b :: c :: t) (hov : t.length + 4 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (c :: a :: b :: c :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP3, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup3 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: t).length - 3 + 4 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem dup4_xstep {s : State} {code : ByteArray} {pcv a b c d : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP4, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: t) (hov : t.length + 5 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (d :: a :: b :: c :: d :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP4, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup4 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: t).length - 4 + 5 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem dup5_xstep {s : State} {code : ByteArray} {pcv a b c d e : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP5, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: t) (hov : t.length + 6 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (e :: a :: b :: c :: d :: e :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP5, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup5 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: t).length - 5 + 6 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem dup6_xstep {s : State} {code : ByteArray} {pcv a b c d e f : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP6, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: t) (hov : t.length + 7 ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (f :: a :: b :: c :: d :: e :: f :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP6, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup6 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: t).length - 6 + 7 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

def stJumpiT (s : State) (a : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := a, stack := t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable - UInt256.ofNat 10 } }

theorem jumpi_t_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.JUMPI, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hb : b ≠ ⟨0⟩)
    (hjd : (D_J code ⟨0⟩).contains a = true) (hov : t.length ≤ 1024) :
    Xstep (D_J code ⟨0⟩) s
      = (if s.machineState.gasAvailable.toNat < 10 then .error .OutOfGass
         else .ok (stJumpiT s a t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.JUMPI, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_jumpi s hd, hstk]
  have hbtrue : (b != (⟨0⟩ : UInt256)) = true := by rw [bne_iff_ne]; exact hb
  have hov' : ¬ ((a :: b :: t).length - 2 + 0 > 1024) := by simp only [List.length_cons]; omega
  simp only [hbtrue, hcode, hjd, not_true_eq_false, and_false, if_neg hov',
    GasConstants.Ghigh, stJumpiT, if_false, reduceIte]

end Reasoning.Theory
