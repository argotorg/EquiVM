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

open Solm ABI Ethereum Ethereum.EVM

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

/-- `ByteArray` `==` reflects equality. -/
theorem byteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  apply ByteArray.ext
  exact eq_of_beq (by simpa [BEq.beq, ByteArray.instBEq] using h)

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
      gasAvailable := s.machineState.gasAvailable.subNat 3 } }

theorem push1_xstep {s : State} {code : ByteArray} {pcv argv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.Push .PUSH1, some (argv, 1)))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
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
      gasAvailable := s.machineState.gasAvailable.subNat  3 } }

theorem push2_xstep {s : State} {code : ByteArray} {pcv argv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.Push .PUSH2, some (argv, 2)))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
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
      gasAvailable := s.machineState.gasAvailable.subNat  2 } }

def stGas (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := (s.machineState.gasAvailable.subNat  2).toUInt256 :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat  2 } }

theorem gas_xstep {s : State} {code : ByteArray} {pcv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.GAS, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
         else .ok (stGas s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.GAS, .none) := by
    rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_gas s hd, if_neg hov']
  simp only [GasConstants.Gbase, stGas]

theorem push0_xstep {s : State} {code : ByteArray} {pcv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.PUSH0, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
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
      gasAvailable := s.machineState.gasAvailable.subNat  2 } }

theorem callvalue_xstep {s : State} {code : ByteArray} {pcv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.CALLVALUE, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
         else .ok (stCallvalue s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.CALLVALUE, .none) := by
    rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_callvalue s hd, if_neg hov']
  simp only [GasConstants.Gbase, stCallvalue]

/-! ### TIMESTAMP (cost 2, pc += 1, pushes block timestamp) -/

def stTimestamp (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.ofNat s.executionEnv.header.timestamp :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat 2 } }

theorem timestamp_xstep {s : State} {code : ByteArray} {pcv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.TIMESTAMP, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
         else .ok (stTimestamp s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.TIMESTAMP, .none) := by
    rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_timestamp s hd, if_neg hov']
  simp only [GasConstants.Gbase, stTimestamp]

/-! ### CHAINID (cost 2, pc += 1, pushes the configured chain id) -/

def stChainid (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.ofNat Ethereum.chainId :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat 2 } }

theorem chainid_xstep {s : State} {code : ByteArray} {pcv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.CHAINID, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
         else .ok (stChainid s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.CHAINID, .none) := by
    rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_chainid s hd, if_neg hov']
  simp only [GasConstants.Gbase, stChainid]

/-! ### DUP1 (cost 3, pc += 1, duplicates top) -/

def stDup1 (s : State) (a : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := a :: a :: t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat  3 } }

theorem dup1_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP1, .none))
    (hstk : s.machineState.stack = a :: t) (hov : (a :: t).length - 1 + 2 ≤ 1024) :
    Xstep (D_J code 0) s
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
      gasAvailable := s.machineState.gasAvailable.subNat  3 } }

theorem iszero_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.ISZERO, .none))
    (hstk : s.machineState.stack = a :: t) (hov : (a :: t).length - 1 + 1 ≤ 1024) :
    Xstep (D_J code 0) s
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
        (s.machineState.gasAvailable.subNat  (memoryExpansionCost s .MSTORE)).subNat 3 } }

theorem mstore_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.MSTORE, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
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
      gasAvailable := s.machineState.gasAvailable.subNat  10 } }

theorem jumpi_nt_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.JUMPI, .none))
    (hstk : s.machineState.stack = a :: ⟨0⟩ :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
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
        (s.machineState.gasAvailable.subNat  (memoryExpansionCost s .REVERT)).subNat 0 } }

theorem revert_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.REVERT, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .REVERT
         then .error .OutOfGass
         else .ok (stRevert s a b t,
                   .some (.revert, s.machineState.memory.readWithPadding a.toNat b.toNat))) := by
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
        (s.machineState.gasAvailable.subNat  (memoryExpansionCost s .RETURN)).subNat 0 } }

theorem return_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.RETURN, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .RETURN
         then .error .OutOfGass
         else .ok (stReturn s a b t,
                   .some (.success, s.machineState.memory.readWithPadding a.toNat b.toNat))) := by
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
        (s.machineState.gasAvailable.subNat  (memoryExpansionCost s .MLOAD)).subNat 3 } }

theorem mload_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.MLOAD, .none))
    (hstk : s.machineState.stack = a :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
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
      gasAvailable := s.machineState.gasAvailable.subNat  3 } }

theorem eq_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.EQ, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
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
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.lt a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LT, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_lt s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem gt_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.GT, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.gt a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.GT, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_gt s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem shr_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SHR, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
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
    Xstep (D_J code 0) s
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
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.slt a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SLT, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_slt s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem sgt_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SGT, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.sgt a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SGT, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_sgt s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem add_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.ADD, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (a + b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.ADD, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_add s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem and_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.AND, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.land a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.AND, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_and s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem or_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.OR, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.lor a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.OR, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_or s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem xor_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.XOR, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.xor a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.XOR, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_xor s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

def stMul (s : State) (res : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩, stack := res :: t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat  5 } }

theorem mod_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.MOD, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
         else .ok (stMul s (UInt256.mod a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.MOD, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_mod s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Glow, stMul]

theorem shl_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SHL, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.shiftLeft b a) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SHL, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_shl s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

/-! ### MUL (cost 5 = `Glow`, `a :: b :: t ↦ mul a b :: t`, pc += 1) -/

theorem mul_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.MUL, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
         else .ok (stMul s (UInt256.mul a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.MUL, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_mul s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Glow, stMul]

theorem div_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DIV, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
         else .ok (stMul s (UInt256.div a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DIV, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_div s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Glow, stMul]

/-! ### EXP (dynamic cost, `a :: b :: t ↦ exp a b :: t`, pc += 1) -/

def expGasCost (b : UInt256) : ℕ :=
  if b = ⟨0⟩ then
    GasConstants.Gexp
  else
    GasConstants.Gexp + GasConstants.Gexpbyte * (1 + Nat.log 256 b.toNat)

theorem expGasCost_pos (b : UInt256) : 0 < expGasCost b := by
  unfold expGasCost
  split <;> simp [GasConstants.Gexp]

def stExp (s : State) (a b : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.exp a b :: t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat (expGasCost b) } }

theorem exp_xstep {s : State} {code : ByteArray} {pcv a b : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.EXP, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < expGasCost b
         then .error .OutOfGass else .ok (stExp s a b t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.EXP, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_exp s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', expGasCost, stExp]

/-! ### POP (cost 2, pc += 1, drops top) -/

def stPop (s : State) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩, stack := t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat  2 } }

theorem pop_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.POP, .none))
    (hstk : s.machineState.stack = a :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
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
      gasAvailable := s.machineState.gasAvailable.subNat  2 } }

theorem calldatasize_xstep {s : State} {code : ByteArray} {pcv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.CALLDATASIZE, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
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
      gasAvailable := s.machineState.gasAvailable.subNat  3 } }

theorem calldataload_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.CALLDATALOAD, .none))
    (hstk : s.machineState.stack = a :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
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
      gasAvailable := s.machineState.gasAvailable.subNat  3 } }

def stPush20 (s : State) (arg : UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + UInt256.ofNat 21,
      stack := arg :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat  3 } }

theorem push20_xstep {s : State} {code : ByteArray} {pcv argv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.Push .PUSH20, some (argv, 20)))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stPush20 s argv, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.Push .PUSH20, some (argv, 20)) := by rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_push s .PUSH20 argv 20 (by decide) hd, if_neg hov']
  simp only [GasConstants.Gverylow, stPush20]

theorem push4_xstep {s : State} {code : ByteArray} {pcv argv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.Push .PUSH4, some (argv, 4)))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
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
      gasAvailable := s.machineState.gasAvailable.subNat  1 } }

theorem jumpdest_xstep {s : State} {code : ByteArray} {pcv : UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.JUMPDEST, .none))
    (hov : s.machineState.stack.length ≤ 1024) :
    Xstep (D_J code 0) s
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
      gasAvailable := s.machineState.gasAvailable.subNat  8 } }

theorem jump_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.JUMP, .none))
    (hstk : s.machineState.stack = a :: t)
    (hjd : (D_J code 0).contains a = true) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
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
      gasAvailable := s.machineState.gasAvailable.subNat 3 } }

theorem swap1_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP1, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 2 ≤ 1024) :
    Xstep (D_J code 0) s
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
    Xstep (D_J code 0) s
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
    Xstep (D_J code 0) s
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
    Xstep (D_J code 0) s
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
    Xstep (D_J code 0) s
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
    Xstep (D_J code 0) s
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
    Xstep (D_J code 0) s
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
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (f :: a :: b :: c :: d :: e :: f :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP6, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup6 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: t).length - 6 + 7 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem dup7_xstep {s : State} {code : ByteArray} {pcv a b c d e f gg : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP7, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: t) (hov : t.length + 8 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (gg :: a :: b :: c :: d :: e :: f :: gg :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP7, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup7 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: gg :: t).length - 7 + 8 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem dup8_xstep {s : State} {code : ByteArray} {pcv a b c d e f gg hh : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP8, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: hh :: t) (hov : t.length + 9 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (hh :: a :: b :: c :: d :: e :: f :: gg :: hh :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP8, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup8 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: t).length - 8 + 9 > 1024) := by simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem dup9_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP9, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: t)
    (hov : t.length + 10 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (ii :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: t),
          .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP9, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup9 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: t).length - 9 + 10 >
      1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem dup10_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP10, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
    (hov : t.length + 11 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s (jj :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP10, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup10 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t).length - 10
      + 11 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem dup11_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP11, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: t)
    (hov : t.length + 12 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s (kk :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP11, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup11 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: t).length - 11
      + 12 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem dup13_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP13, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: t)
    (hov : t.length + 14 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (mm :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP13, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup13 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: t).length -
          13 + 14 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem dup14_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP14, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: t)
    (hov : t.length + 15 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (nn :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
              nn :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP14, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup14 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
          t).length - 14 + 15 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem dup15_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn oo : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP15, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: t)
    (hov : t.length + 16 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (oo :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
              nn :: oo :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP15, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup15 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
          oo :: t).length - 15 + 16 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

def stJumpiT (s : State) (a : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := a, stack := t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat  10 } }

theorem jumpi_t_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.JUMPI, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hb : b ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains a = true) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 10 then .error .OutOfGass
         else .ok (stJumpiT s a t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.JUMPI, .none) := by rw [hcode, hpc]; exact hdec
  rw [← hcode, step_jumpi s hd, hstk]
  have hbtrue : (b != (⟨0⟩ : UInt256)) = true := by rw [bne_iff_ne]; exact hb
  have hov' : ¬ ((a :: b :: t).length - 2 + 0 > 1024) := by simp only [List.length_cons]; omega
  simp only [hbtrue, hcode, hjd, not_true_eq_false, and_false, if_neg hov',
    GasConstants.Ghigh, stJumpiT, if_false, reduceIte]

/-! ### SSTORE (storage write; cost `Csstore` with the call-stipend floor, pops 2)

The successor mirrors `step_sstore` verbatim — including the EIP-2200 refund bookkeeping on the
substate, which `RD` does not track but must still be reproduced so the equation holds by `rfl`.
The gas guard combines `step_sstore`'s two out-of-gas conditions — `gas < Csstore` and the
`gas ≤ Gcallstipend` floor — into the single threshold `max (Csstore s) (Gcallstipend + 1)`, fitting
the `if gas < cost then OOG else …` shape the `RD` machinery consumes. -/

def stSStore (s : State) (slot val : UInt256) (t : List UInt256) : State :=
  let Iₐ := s.executionEnv.codeOwner
  let v₀ :=
    match s.σ₀.find? Iₐ with
    | none => ⟨0⟩
    | some acc => acc.storage.findD slot ⟨0⟩
  let v := (s.accountMap.find! Iₐ).storage.findD slot ⟨0⟩
  let v' := val
  let r_dirtyclear : ℤ :=
    if v₀ ≠ UInt256.ofNat 0 && v = UInt256.ofNat 0 then - GasConstants.Rsclear else
    if v₀ ≠ UInt256.ofNat 0 && v' = UInt256.ofNat 0 then GasConstants.Rsclear else
    0
  let r_dirtyreset : ℤ :=
    if v₀ = v' && v₀ = UInt256.ofNat 0 then GasConstants.Gsset - GasConstants.Gwarmaccess else
    if v₀ = v' && v₀ ≠ UInt256.ofNat 0 then GasConstants.Gsreset - GasConstants.Gwarmaccess else
    0
  let ΔAᵣ : ℤ :=
    if v ≠ v' && v₀ = v && v' = UInt256.ofNat 0 then GasConstants.Rsclear else
    if v ≠ v' && v₀ ≠ v then r_dirtyclear + r_dirtyreset else
    0
  let newAᵣ : UInt256 :=
    match ΔAᵣ with
    | .ofNat n => s.substate.refundBalance + UInt256.ofNat n
    | .negSucc n => s.substate.refundBalance - UInt256.ofNat n - ⟨1⟩
  let accountMap :=
    s.accountMap.find? Iₐ |>.option s.accountMap
      (fun acc =>
        s.accountMap.insert Iₐ
          (if val == default then
            {acc with storage := acc.storage.erase slot}
          else
            {acc with storage := acc.storage.insert slot val}))
  let substate :=
    s.accountMap.find? Iₐ |>.option s.substate
      (fun _ =>
        {s.substate with
          accessedStorageKeys := s.substate.accessedStorageKeys.insert (Iₐ, slot)
          refundBalance := newAᵣ})
  {s with
      accountMap := accountMap
      substate := substate
      machineState.stack := t
      machineState.gasAvailable := s.machineState.gasAvailable.subNat  (Csstore s)
      machineState.pc := s.machineState.pc + ⟨1⟩
      machineState.execLength := s.machineState.execLength + 1 }

theorem sstore_xstep {s : State} {code : ByteArray} {pcv slot val : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SSTORE, .none))
    (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = slot :: val :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < max (Csstore s) (GasConstants.Gcallstipend + 1)
         then .error .OutOfGass else .ok (stSStore s slot val t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SSTORE, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_sstore s hd, hstk]
  have hg2 : ((slot :: val :: t).length - 2 + 0 > 1024) = False :=
    eq_false (by simp only [List.length_cons]; omega)
  have hg3 : (¬ (s.executionEnv.perm = true)) = False := eq_false (by simp [hperm])
  simp only [hg2, hg3, if_false]
  by_cases h1 : s.machineState.gasAvailable.toNat < Csstore s
  · rw [if_pos h1,
      if_pos (show s.machineState.gasAvailable.toNat
          < max (Csstore s) (GasConstants.Gcallstipend + 1) from
        lt_of_lt_of_le h1 (le_max_left _ _))]
  · by_cases h2 : s.machineState.gasAvailable.toNat ≤ GasConstants.Gcallstipend
    · rw [if_neg h1, if_pos h2,
        if_pos (show s.machineState.gasAvailable.toNat
            < max (Csstore s) (GasConstants.Gcallstipend + 1) from
          lt_of_lt_of_le (Nat.lt_succ_of_le h2) (le_max_right _ _))]
    · rw [if_neg h1, if_neg h2,
        if_neg (show ¬ s.machineState.gasAvailable.toNat
            < max (Csstore s) (GasConstants.Gcallstipend + 1) from
          Nat.not_lt.mpr (max_le (Nat.le_of_not_lt h1) (by omega)))]
      rfl

/-- The `accountMap` after an `SSTORE` of `val` at `slot` by `Iₐ` (the field `RD` carries). -/
def sstoreAccountMap (Iₐ : AccountAddress) (σ : AccountMap) (slot val : UInt256) : AccountMap :=
  σ.find? Iₐ |>.option σ
    (fun acc =>
      σ.insert Iₐ
        (if val == default then {acc with storage := acc.storage.erase slot}
         else {acc with storage := acc.storage.insert slot val}))

/-- `EVM.storageStore` updates the account map exactly as `sstoreAccountMap` does. -/
theorem storageStore_accountMap (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (EVM.storageStore evm a slot val).accountMap = sstoreAccountMap a evm.accountMap slot val := by
  simp only [EVM.storageStore, sstoreAccountMap, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

/-- `EVM.storageStore` does not change the created-account set. -/
theorem storageStore_createdAccounts (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (EVM.storageStore evm a slot val).createdAccounts = evm.createdAccounts := by
  simp only [EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount]

@[simp] theorem stSStore_accountMap (s : State) (slot val : UInt256) (t : List UInt256) :
    (stSStore s slot val t).accountMap
      = sstoreAccountMap s.executionEnv.codeOwner s.accountMap slot val := rfl

@[simp] theorem stSStore_createdAccounts (s : State) (slot val : UInt256) (t : List UInt256) :
    (stSStore s slot val t).createdAccounts = s.createdAccounts := rfl

@[simp] theorem stSStore_pc (s : State) (slot val : UInt256) (t : List UInt256) :
    (stSStore s slot val t).machineState.pc = s.machineState.pc + ⟨1⟩ := rfl

@[simp] theorem stSStore_stack (s : State) (slot val : UInt256) (t : List UInt256) :
    (stSStore s slot val t).machineState.stack = t := rfl

@[simp] theorem stSStore_memory (s : State) (slot val : UInt256) (t : List UInt256) :
    (stSStore s slot val t).machineState.memory = s.machineState.memory := rfl

@[simp] theorem stSStore_activeWords (s : State) (slot val : UInt256) (t : List UInt256) :
    (stSStore s slot val t).machineState.activeWords = s.machineState.activeWords := rfl

@[simp] theorem stSStore_executionEnv (s : State) (slot val : UInt256) (t : List UInt256) :
    (stSStore s slot val t).executionEnv = s.executionEnv := rfl

theorem stSStore_gas (s : State) (slot val : UInt256) (t : List UInt256) :
    (stSStore s slot val t).machineState.gasAvailable
      = s.machineState.gasAvailable.subNat (Csstore s) := by
  simp [stSStore]

/-- `SSTORE` always costs at least its warm-access store component, so it is non-zero — needed so a
    continue step's `k + 1 ≤ C + Csstore s` invariant survives. -/
theorem Csstore_pos (s : State) : 1 ≤ Csstore s := by
  unfold Csstore
  simp only [GasConstants.Gwarmaccess, GasConstants.Gsset, GasConstants.Gsreset,
    GasConstants.Gcoldsload]
  split_ifs <;> omega

/-! ### RETURNDATASIZE (cost `Gbase = 2`, pc += 1, pushes `|returnData|`) -/

def stReturndatasize (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.ofNat s.machineState.returnData.size :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat 2 } }

theorem returndatasize_xstep {s : State} {code : ByteArray} {pcv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.RETURNDATASIZE, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
         else .ok (stReturndatasize s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.RETURNDATASIZE, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_returndatasize s hd]
  by_cases hg : s.machineState.gasAvailable.toNat < GasConstants.Gbase
  · have : s.machineState.gasAvailable.toNat < 2 := by simpa [GasConstants.Gbase] using hg
    rw [if_pos hg, if_pos this]
  · have hg2 : ¬ s.machineState.gasAvailable.toNat < 2 := by simpa [GasConstants.Gbase] using hg
    have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
    rw [if_neg hg, if_neg hov', if_neg hg2]
    simp only [GasConstants.Gbase, stReturndatasize]

/-! ### CODESIZE (cost 2, pushes `|code|`) -/

def stCodesize (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.ofNat s.executionEnv.code.size :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat 2 } }

theorem codesize_xstep {s : State} {code : ByteArray} {pcv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.CODESIZE, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
         else .ok (stCodesize s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.CODESIZE, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_codesize s hd]
  by_cases hg : s.machineState.gasAvailable.toNat < GasConstants.Gbase
  · have : s.machineState.gasAvailable.toNat < 2 := by simpa [GasConstants.Gbase] using hg
    rw [if_pos hg, if_pos this]
  · have hg2 : ¬ s.machineState.gasAvailable.toNat < 2 := by simpa [GasConstants.Gbase] using hg
    have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
    rw [if_neg hg, if_neg hov', if_neg hg2]
    simp only [GasConstants.Gbase, stCodesize]

/-! ### RETURNDATACOPY (`a :: b :: c :: t ↦ t`, copy `returnData[b .. b+c]` to `mem[a .. a+c]`;
    two-stage gas `memCost` then `Gverylow + Gcopy·⌈c/32⌉`, plus the `b + c ≤ |returnData|` guard) -/

def stReturndatacopy (s : State) (a b c : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := t,
      memory := s.machineState.returnData.write b.toNat s.machineState.memory a.toNat c.toNat,
      activeWords := UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat),
      execLength := s.machineState.execLength + 1,
      gasAvailable :=
        (s.machineState.gasAvailable.subNat (memoryExpansionCost s .RETURNDATACOPY)).subNat
          (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)) } }

theorem returndatacopy_xstep {s : State} {code : ByteArray} {pcv a b c : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.RETURNDATACOPY, .none))
    (hstk : s.machineState.stack = a :: b :: c :: t)
    (hmemok : ¬ b.toNat + c.toNat > s.machineState.returnData.size)
    (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .RETURNDATACOPY
         then .error .OutOfGass
         else if (s.machineState.gasAvailable.subNat (memoryExpansionCost s .RETURNDATACOPY)).toNat
                < GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
              then .error .OutOfGass
              else .ok (stReturndatacopy s a b c t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.RETURNDATACOPY, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_returndatacopy s hd, hstk]
  by_cases hg1 : s.machineState.gasAvailable.toNat < memoryExpansionCost s .RETURNDATACOPY
  · simp only [hg1, if_true]
  · by_cases hg2 : (s.machineState.gasAvailable.subNat
        (memoryExpansionCost s .RETURNDATACOPY)).toNat
        < GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
    · simp only [hg1, hg2, if_true, if_false]
    · have hov' : ¬ ((a :: b :: c :: t).length - 3 + 0 > 1024) := by
        simp only [List.length_cons]; omega
      simp only [hg1, hg2, hmemok, hov', if_false, stReturndatacopy]

/-! ### CALLDATACOPY (`a :: b :: c :: t ↦ t`, copy calldata bytes into memory) -/

def stCalldatacopy (s : State) (a b c : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := t,
      memory := s.executionEnv.calldata.write b.toNat s.machineState.memory a.toNat c.toNat,
      activeWords := UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat),
      execLength := s.machineState.execLength + 1,
      gasAvailable :=
        (s.machineState.gasAvailable.subNat (memoryExpansionCost s .CALLDATACOPY)).subNat
          (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)) } }

theorem calldatacopy_xstep {s : State} {code : ByteArray} {pcv a b c : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.CALLDATACOPY, .none))
    (hstk : s.machineState.stack = a :: b :: c :: t)
    (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .CALLDATACOPY
         then .error .OutOfGass
         else if (s.machineState.gasAvailable.subNat (memoryExpansionCost s .CALLDATACOPY)).toNat
                < GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
              then .error .OutOfGass
              else .ok (stCalldatacopy s a b c t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.CALLDATACOPY, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_calldatacopy s hd, hstk]
  by_cases hg1 : s.machineState.gasAvailable.toNat < memoryExpansionCost s .CALLDATACOPY
  · simp only [hg1, if_true]
  · by_cases hg2 : (s.machineState.gasAvailable.subNat
        (memoryExpansionCost s .CALLDATACOPY)).toNat
        < GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
    · simp only [hg1, hg2, if_true, if_false]
    · have hov' : ¬ ((a :: b :: c :: t).length - 3 + 0 > 1024) := by
        simp only [List.length_cons]; omega
      simp only [hg1, hg2, hov', if_false, stCalldatacopy]

/-! ### CODECOPY (`a :: b :: c :: t ↦ t`, copy `code[b .. b+c]` to `mem[a .. a+c]`) -/

def stCodecopy (s : State) (a b c : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := t,
      memory := s.executionEnv.code.write b.toNat s.machineState.memory a.toNat c.toNat,
      activeWords := UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat c.toNat),
      execLength := s.machineState.execLength + 1,
      gasAvailable :=
        (s.machineState.gasAvailable.subNat (memoryExpansionCost s .CODECOPY)).subNat
          (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)) } }

theorem codecopy_xstep {s : State} {code : ByteArray} {pcv a b c : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.CODECOPY, .none))
    (hstk : s.machineState.stack = a :: b :: c :: t)
    (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .CODECOPY
         then .error .OutOfGass
         else if (s.machineState.gasAvailable.subNat (memoryExpansionCost s .CODECOPY)).toNat
                < GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
              then .error .OutOfGass
              else .ok (stCodecopy s a b c t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.CODECOPY, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_codecopy s hd, hstk]
  by_cases hg1 : s.machineState.gasAvailable.toNat < memoryExpansionCost s .CODECOPY
  · simp only [hg1, if_true]
  · by_cases hg2 : (s.machineState.gasAvailable.subNat
        (memoryExpansionCost s .CODECOPY)).toNat
        < GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
    · simp only [hg1, hg2, if_true, if_false]
    · have hov' : ¬ ((a :: b :: c :: t).length - 3 + 0 > 1024) := by
        simp only [List.length_cons]; omega
      simp only [hg1, hg2, hov', if_false, stCodecopy]

/-! ### STOP (halt *success*, empty output, cost `Gzero = 0`) -/

def stStop (s : State) : State :=
  { s with machineState := { s.machineState with
      execLength := s.machineState.execLength + 1,
      returnData := .empty,
      gasAvailable := s.machineState.gasAvailable.subNat 0 } }

theorem stop_xstep {s : State} {code : ByteArray} {pcv : UInt256} {stk : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.STOP, .none))
    (hstk : s.machineState.stack = stk) (hov : stk.length ≤ 1024) :
    Xstep (D_J code 0) s = .ok (stStop s, .some (.success, ByteArray.empty)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.STOP, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_stop s hd]
  have hov' : ¬ (s.machineState.stack.length - 0 + 0 > 1024) := by rw [hstk]; omega
  rw [if_neg hov']
  simp only [GasConstants.Gzero, stStop]

/-! ### NOT (`a :: t ↦ lnot a :: t`, cost `Gverylow = 3`, pc += 1) -/

def stNot (s : State) (a : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.lnot a :: t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat 3 } }

theorem not_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.NOT, .none))
    (hstk : s.machineState.stack = a :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stNot s a t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.NOT, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_not s hd, hstk]
  by_cases hg : s.machineState.gasAvailable.toNat < GasConstants.Gverylow
  · have h3 : s.machineState.gasAvailable.toNat < 3 := by simpa [GasConstants.Gverylow] using hg
    simp only [hg, h3, if_true]
  · have hg2 : ¬ s.machineState.gasAvailable.toNat < 3 := by simpa [GasConstants.Gverylow] using hg
    have hov' : ¬ ((a :: t).length - 1 + 1 > 1024) := by simp only [List.length_cons]; omega
    simp only [hg2, hov', if_false, GasConstants.Gverylow, stNot]

/-! ### CALLER (cost `Gbase = 2`, pc += 1, pushes `msg.sender = source`) -/

def stCaller (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.ofNat s.executionEnv.source.val :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat 2 } }

theorem caller_xstep {s : State} {code : ByteArray} {pcv : UInt256} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.CALLER, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
         else .ok (stCaller s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.CALLER, .none) := by
    rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_caller s hd, if_neg hov']
  simp only [GasConstants.Gbase, stCaller]

/-! ### ADDRESS (cost `Gbase = 2`, pc += 1, pushes current contract address) -/

def stAddress (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.ofNat s.executionEnv.codeOwner.val :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat 2 } }

theorem address_xstep {s : State} {code : ByteArray} {pcv : UInt256}
    {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.ADDRESS, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
         else .ok (stAddress s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.ADDRESS, .none) := by
    rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_address s hd, if_neg hov']
  simp only [GasConstants.Gbase, stAddress]

/-! ### EXTCODESIZE (dynamic `Caccess`, pc += 1) -/

def extCodeSizeWord (σ : AccountMap) (target : UInt256) : UInt256 :=
  σ.find? (AccountAddress.ofUInt256 target) |>.option ⟨0⟩
    (UInt256.ofNat ∘ ByteArray.size ∘ (·.code))

def stExtcodesize (s : State) (target : UInt256) (t : List UInt256) : State :=
  let addr := AccountAddress.ofUInt256 target
  { s with
      substate :=
        { s.substate with accessedAccounts := s.substate.accessedAccounts.insert addr },
      machineState :=
        { s.machineState with
          pc := s.machineState.pc + ⟨1⟩,
          stack := extCodeSizeWord s.accountMap target :: t,
          execLength := s.machineState.execLength + 1,
          gasAvailable := s.machineState.gasAvailable.subNat (Caccess addr s.substate) } }

theorem extcodesize_xstep {s : State} {code : ByteArray} {pcv target : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.EXTCODESIZE, .none))
    (hstk : s.machineState.stack = target :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < Caccess (AccountAddress.ofUInt256 target) s.substate
       then .error .OutOfGass else .ok (stExtcodesize s target t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.EXTCODESIZE, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_extcodesize s hd, hstk]
  have hov' : ¬ ((target :: t).length - 1 + 1 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', stExtcodesize, extCodeSizeWord]

/-! ### SWAP4–SWAP6 (cost `Gverylow = 3`, pc += 1) -/

theorem swap4_xstep {s : State} {code : ByteArray} {pcv a b c d e : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP4, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: t) (hov : t.length + 5 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (e :: b :: c :: d :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP4, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap4 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: t).length - 5 + 5 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem swap5_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP5, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: t)
    (hov : t.length + 6 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (f :: b :: c :: d :: e :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP5, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap5 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: t).length - 6 + 6 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem swap6_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP6, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: t)
    (hov : t.length + 7 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (gg :: b :: c :: d :: e :: f :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP6, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap6 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: gg :: t).length - 7 + 7 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem swap7_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP7, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: t)
    (hov : t.length + 8 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (h :: b :: c :: d :: e :: f :: gg :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP7, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap7 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: t).length - 8 + 8 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem swap8_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP8, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: t)
    (hov : t.length + 9 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (ii :: b :: c :: d :: e :: f :: gg :: hh :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP8, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap8 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: t).length - 9 + 9 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem swap10_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP10, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: t)
    (hov : t.length + 11 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (kk :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: a :: t),
          .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP10, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap10 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: t).length - 11 + 11 >
          1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem swap11_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP11, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
    (hov : t.length + 12 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s (ll :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: a :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP11, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap11 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t).length - 12 +
          12 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

/-! ### KECCAK256 (two-stage cost `memExp + hashCost`, pc += 1, pops 2, pushes `KEC(mem[a..a+b])`) -/

def stKeccak (s : State) (a b : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.ofNat (fromByteArrayBigEndian
                 (ffi.KEC (s.machineState.memory.readWithPadding a.toNat b.toNat))) :: t,
      activeWords := UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat),
      execLength := s.machineState.execLength + 1,
      gasAvailable :=
        (s.machineState.gasAvailable.subNat (memoryExpansionCost s .KECCAK256)).subNat
          (GasConstants.Gkeccak256
              + GasConstants.Gkeccak256word * ((b.toNat + 31) / 32)) } }

theorem keccak_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.KECCAK256, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat
            < memoryExpansionCost s .KECCAK256
              + (GasConstants.Gkeccak256 + GasConstants.Gkeccak256word * ((b.toNat + 31) / 32))
         then .error .OutOfGass else .ok (stKeccak s a b t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.KECCAK256, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_keccak s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [collapse_two_stage, if_neg hov', stKeccak]

/-! ### SLOAD (cost `Csload`, pc += 1, pops slot, pushes `storage[codeOwner][slot]`) -/

def stSload (s : State) (a : UInt256) (t : List UInt256) : State :=
  {s with
    substate := {s.substate with
      accessedStorageKeys := s.substate.accessedStorageKeys.insert (s.executionEnv.codeOwner, a)}
    machineState.stack :=
      (s.accountMap.find? s.executionEnv.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD a ⟨0⟩)) :: t
    machineState.gasAvailable :=
      s.machineState.gasAvailable.subNat (Csload (a :: t) s.substate s.executionEnv)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

theorem sload_xstep {s : State} {code : ByteArray} {pcv a : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SLOAD, .none))
    (hstk : s.machineState.stack = a :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < Csload (a :: t) s.substate s.executionEnv
         then .error .OutOfGass else .ok (stSload s a t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SLOAD, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_sload s hd, hstk]
  have hov' : ¬ ((a :: t).length - 1 + 1 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', stSload]

/-! ### LOG1/LOG3/LOG4 (two-stage cost `memExp + logCost`, appends a log; needs `perm`) -/

def stLog1 (s : State) (a b c : UInt256) (t : List UInt256) : State :=
  {s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG1)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat + GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

theorem log1_xstep {s : State} {code : ByteArray} {pcv a b c : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG1, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat
            < memoryExpansionCost s .LOG1
              + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + GasConstants.Glogtopic)
         then .error .OutOfGass else .ok (stLog1 s a b c t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG1, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_log1 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: t).length - 3 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, stLog1]

def stLog3 (s : State) (a b c d e : UInt256) (t : List UInt256) : State :=
  {s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d, e], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG3)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat
            + 3 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

theorem log3_xstep {s : State} {code : ByteArray} {pcv a b c d e : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG3, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat
            < memoryExpansionCost s .LOG3
              + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 3 * GasConstants.Glogtopic)
         then .error .OutOfGass else .ok (stLog3 s a b c d e t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG3, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_log3 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: t).length - 5 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, stLog3]

def stLog4 (s : State) (a b c d e f : UInt256) (t : List UInt256) : State :=
  {s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d, e, f],
        s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG4)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat
            + 4 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

theorem log4_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG4, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: t)
    (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat
            < memoryExpansionCost s .LOG4
              + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 4 * GasConstants.Glogtopic)
         then .error .OutOfGass else .ok (stLog4 s a b c d e f t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG4, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_log4 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: t).length - 6 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, stLog4]

/-! ### PUSHk (width-generic, cost `Gverylow = 3`, pc += k+1, pushes the literal `arg`) -/

def stPushConst (s : State) (arg : UInt256) (width : ℕ) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + UInt256.ofNat width.succ,
      stack := arg :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat 3 } }

/-- One `Xstep` for any `PUSHk` (`k ≥ 1`), the width carried by the decode fact — so a generic
    dispatcher trace need not fork on `PUSH1`/`PUSH2`.  Mirrors `push1_xstep`/`push2_xstep`. -/
theorem pushConst_xstep {s : State} {code : ByteArray} {pcv arg : UInt256} {width : ℕ}
    {op : Operation.POp} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv) (hop : op ≠ .PUSH0)
    (hdec : decode code pcv = some (.Push op, some (arg, width)))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stPushConst s arg width, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.Push op, some (arg, width)) := by
    rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_push s op arg width hop hd, if_neg hov']
  simp only [GasConstants.Gverylow, stPushConst]

end Reasoning.Theory
