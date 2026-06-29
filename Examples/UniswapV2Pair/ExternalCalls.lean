import Examples.UniswapV2Pair.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Reasoning.Theory

theorem uniswapNatLandComm (a b : ℕ) : Nat.land a b = Nat.land b a := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (a &&& b).testBit i = (b &&& a).testBit i
  rw [Nat.testBit_and, Nat.testBit_and, Bool.and_comm]

-- GENERALIZES Examples.Caller.Correct.uland_comm — same generic `UInt256.land`
-- commutativity proof; belongs in `Reasoning.EVMWord`.
-- LIBRARY CANDIDATE: Reasoning.EVMWord — generic `UInt256.land` commutativity.
theorem uniswapULandComm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply u256_inj
  show (Fin.land a.val b.val).val = (Fin.land b.val a.val).val
  simp only [Fin.land]
  rw [uniswapNatLandComm]

-- LIBRARY CANDIDATE: Reasoning.Stepping — generic successor state for the EVM `ADDRESS`
-- opcode, parallel to `stCaller`.
def uniswapStAddress (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.ofNat s.executionEnv.codeOwner.val :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat 2 } }

-- LIBRARY CANDIDATE: Reasoning.Stepping — generic `ADDRESS` `Xstep` wrapper, parallel to
-- `caller_xstep`.
theorem uniswapAddress_xstep {s : State} {code : ByteArray} {pcv : UInt256}
    {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.ADDRESS, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
         else .ok (uniswapStAddress s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.ADDRESS, .none) := by
    rw [hcode, hpc]; exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  rw [← hcode, step_address s hd, if_neg hov']
  simp only [GasConstants.Gbase, uniswapStAddress]

end Reasoning.Theory

namespace Reasoning.Reach

-- LIBRARY CANDIDATE: Reasoning.Reach — generic `RD` combinator for the EVM `ADDRESS`
-- opcode, parallel to `RD.caller`.
theorem RD.uniswapAddress {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.ADDRESS, .none)) (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.ofNat ee.codeOwner.val :: stk) mem aw rdata acc
      (k + 1) (C + 2) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := uniswapAddress_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨uniswapStAddress s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [uniswapStAddress]; exact hcode
      · simp only [uniswapStAddress]; rw [hpc]
      · simp only [uniswapStAddress]; rw [hstk, hee]
      · simp only [uniswapStAddress]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [uniswapStAddress]; exact hmem
      · simp only [uniswapStAddress]; exact haw
      · simp only [uniswapStAddress]; exact hrdata
      · simp only [uniswapStAddress]; exact hacc
      · exact hee
      · exact hworld

end Reasoning.Reach

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: Reasoning.Stepping — generic successor state for the EVM
-- `EXTCODESIZE` opcode, mirroring `Ethereum.State.extCodeSize`.
def uniswapStExtcodesize (s : State) (target : UInt256) (t : List UInt256) : State :=
  let addr := AccountAddress.ofUInt256 target
  { s with
      substate :=
        { s.substate with accessedAccounts := s.substate.accessedAccounts.insert addr },
      machineState :=
        { s.machineState with
          pc := s.machineState.pc + ⟨1⟩,
          stack := uniswapExtCodeSizeWord s.accountMap target :: t,
          execLength := s.machineState.execLength + 1,
          gasAvailable := s.machineState.gasAvailable.subNat (Caccess addr s.substate) } }

-- LIBRARY CANDIDATE: Reasoning.Stepping — generic `EXTCODESIZE` `Xstep` wrapper.
theorem uniswapExtcodesize_xstep {s : State} {code : ByteArray} {pcv target : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.EXTCODESIZE, .none))
    (hstk : s.machineState.stack = target :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < Caccess (AccountAddress.ofUInt256 target) s.substate
       then .error .OutOfGass else .ok (uniswapStExtcodesize s target t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.EXTCODESIZE, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_extcodesize s hd, hstk]
  have hov' : ¬ ((target :: t).length - 1 + 1 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', uniswapStExtcodesize, uniswapExtCodeSizeWord]

end Reasoning.Theory

namespace Reasoning.Reach

-- LIBRARY CANDIDATE: Reasoning.Reach — generic `RD` combinator for `EXTCODESIZE`,
-- existentializing the warm/cold `Caccess` gas cost like `RD.sload` does for `Csload`.
theorem RD.uniswapExtcodesize {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {target : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (target :: t) mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.EXTCODESIZE, .none)) (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩)
      (Reasoning.Theory.uniswapExtCodeSizeWord σ target :: t) mem aw rdata (cA, σ) k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee,
    hworld⟩
  · exact ⟨k, C, Or.inl hoog⟩
  · have st := Reasoning.Theory.uniswapExtcodesize_xstep hcode hpc hdec hstk hov
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    by_cases gg : g.toNat < C + Caccess (AccountAddress.ofUInt256 target) s.substate
    · exact ⟨k, C, Or.inl (hX.trans (stepOOG hgas st hk hC gg))⟩
    · refine ⟨k + 1, C + Caccess (AccountAddress.ofUInt256 target) s.substate,
        Or.inr ⟨Reasoning.Theory.uniswapStExtcodesize s target t,
          hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          by
            have hpos : 1 ≤ Caccess (AccountAddress.ofUInt256 target) s.substate := by
              unfold Caccess; split <;> decide
            omega,
          by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · simp only [Reasoning.Theory.uniswapStExtcodesize]; exact hcode
      · simp only [Reasoning.Theory.uniswapStExtcodesize]; rw [hpc]
      · simp only [Reasoning.Theory.uniswapStExtcodesize,
          Reasoning.Theory.uniswapExtCodeSizeWord, hσ]
      · simp only [Reasoning.Theory.uniswapStExtcodesize]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [Reasoning.Theory.uniswapStExtcodesize]; exact hmem
      · simp only [Reasoning.Theory.uniswapStExtcodesize]; exact haw
      · simp only [Reasoning.Theory.uniswapStExtcodesize]; exact hrdata
      · simp only [Reasoning.Theory.uniswapStExtcodesize]; rw [hcA, hσ]
      · simp only [Reasoning.Theory.uniswapStExtcodesize]; exact hee
      · exact hworld

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc high-level-call
-- `EXTCODESIZE` guard for the branch where the target account has deployed code.
theorem RD.uniswapExtcodesizeGuardOk {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc okPc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {target : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (target :: target :: R) mem aw rdata (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ target ≠ ⟨0⟩)
    (hExt : decode code pc = some (.EXTCODESIZE, .none))
    (hIszero0 : decode code (pc + ⟨1⟩) = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPop : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (okPc + ⟨1⟩ + ⟨1⟩) (target :: R) mem aw rdata
      (cA, σ) k' C' := by
  obtain ⟨_, _, rdExt⟩ :=
    RD.uniswapExtcodesize h hExt
      (by simp only [List.length_cons]; omega)
  have rdIszero0 := RD.iszero rdExt hIszero0
    (by simp only [List.length_cons]; omega)
  have rdDup1 := RD.dup1 rdIszero0 hDup1
    (by simp only [List.length_cons]; omega)
  have rdIszero1 := RD.iszero rdDup1 hIszero1
    (by simp only [List.length_cons]; omega)
  have rdPush := RD.push2 rdIszero1 okPc hPush
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.isZero
          (Reasoning.Theory.uniswapExtCodeSizeWord σ target)) ≠ ⟨0⟩ := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hcodeSize]
    decide
  have rdJumpi := RD.jumpiT rdPush hJumpi hcond hjd
    (by simp only [List.length_cons]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi hJumpdest
    (by simp only [List.length_cons]; omega)
  have rdPop := RD.pop rdJumpdest hPop
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rdPop⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc high-level-call
-- `EXTCODESIZE` guard plus `GAS`, stopping at the call opcode with existential gas.
theorem RD.uniswapExtcodesizeGuardOkGas {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {target : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (target :: target :: R) mem aw rdata (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ target ≠ ⟨0⟩)
    (hExt : decode code pc = some (.EXTCODESIZE, .none))
    (hIszero0 : decode code (pc + ⟨1⟩) = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPop : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hGas : decode code (okPc + ⟨1⟩ + ⟨1⟩) = some (.GAS, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ gasWord k' C', RD code ee g s0 (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
      (gasWord :: target :: R) mem aw rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rdReady⟩ :=
    RD.uniswapExtcodesizeGuardOk h hcodeSize hExt hIszero0 hDup1 hIszero1 hPush hJumpi
      hjd hJumpdest hPop hov
  obtain ⟨gasWord, rdGas⟩ :=
    RD.gas rdReady hGas (by simp only [List.length_cons]; omega)
  exact ⟨gasWord, _, _, rdGas⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc high-level-call
-- `EXTCODESIZE` guard for the branch where the target account has no deployed code.
theorem RD.uniswapExtcodesizeGuardMissing {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {target : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (target :: target :: R) mem aw rdata (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ target = ⟨0⟩)
    (hExt : decode code pc = some (.EXTCODESIZE, .none))
    (hIszero0 : decode code (pc + ⟨1⟩) = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hPush0 :
      decode code (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hDupZero :
      decode code
          ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) +
            UInt256.ofNat 2) =
        some (.DUP1, .none))
    (hRevert :
      decode code
          (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) +
              UInt256.ofNat 2) + ⟨1⟩) =
        some (.REVERT, .none))
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, rdExt⟩ :=
    RD.uniswapExtcodesize h hExt
      (by simp only [List.length_cons]; omega)
  have rdIszero0 := RD.iszero rdExt hIszero0
    (by simp only [List.length_cons]; omega)
  have rdDup1 := RD.dup1 rdIszero0 hDup1
    (by simp only [List.length_cons]; omega)
  have rdIszero1 := RD.iszero rdDup1 hIszero1
    (by simp only [List.length_cons]; omega)
  have rdPush := RD.push2 rdIszero1 okPc hPush
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.isZero
          (Reasoning.Theory.uniswapExtCodeSizeWord σ target)) = ⟨0⟩ := by
    rw [hcodeSize]
    decide
  have rdFallthrough := RD.jumpiNT rdPush hJumpi hcond
    (by simp only [List.length_cons]; omega)
  exact RD.uniswapPush1Dup1Revert0 rdFallthrough hPush0 hDupZero hRevert
    (by simp only [List.length_cons]; omega)

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc high-level-call success
-- guard for the branch where a CALL-like status word is nonzero.
theorem RD.uniswapCallSuccessGuardOk {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {status : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (status :: R) mem aw rdata acc k C)
    (hstatus : status ≠ ⟨0⟩)
    (hIszero0 : decode code pc = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi : decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
      some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPop : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (okPc + ⟨1⟩ + ⟨1⟩) R mem aw rdata acc k' C' := by
  have rdIszero0 := RD.iszero h hIszero0
    (by omega)
  have rdDup1 := RD.dup1 rdIszero0 hDup1
    (by omega)
  have rdIszero1 := RD.iszero rdDup1 hIszero1
    (by simp only [List.length_cons]; omega)
  have rdPush := RD.push2 rdIszero1 okPc hPush
    (by simp only [List.length_cons]; omega)
  have hcond : UInt256.isZero (UInt256.isZero status) ≠ ⟨0⟩ := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hstatus]
    decide
  have rdJumpi := RD.jumpiT rdPush hJumpi hcond hjd
    (by simp only [List.length_cons]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi hJumpdest
    (by simp only [List.length_cons]; omega)
  have rdPop := RD.pop rdJumpdest hPop
    (by omega)
  exact ⟨_, _, rdPop⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc high-level-call success guard for the
-- branch where a CALL-like status word is zero and the revert-data bubbling tail is executed.
theorem RD.uniswapCallSuccessGuardMissing {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {status : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (status :: R) mem aw rdata acc k C)
    (hstatus : status = ⟨0⟩)
    (hIszero0 : decode code pc = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi : decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
      some (.JUMPI, .none))
    (hReturndatasize :
      decode code (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush0 :
      decode code
          ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) =
      some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hDupZero :
      decode code
          (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) +
            UInt256.ofNat 2) =
        some (.DUP1, .none))
    (hReturndatacopy :
      decode code
          ((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) +
              UInt256.ofNat 2) + ⟨1⟩) =
        some (.RETURNDATACOPY, .none))
    (hReturndatasizeRevert :
      decode code
          (((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) +
                UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPushRevert0 :
      decode code
          ((((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) +
                  UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hRevert :
      decode code
          (((((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) +
                    UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) =
        some (.REVERT, .none))
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  have rdIszero0 := RD.iszero h hIszero0
    (by omega)
  have rdDup1 := RD.dup1 rdIszero0 hDup1
    (by omega)
  have rdIszero1 := RD.iszero rdDup1 hIszero1
    (by simp only [List.length_cons]; omega)
  have rdPush := RD.push2 rdIszero1 okPc hPush
    (by simp only [List.length_cons]; omega)
  have hcond : UInt256.isZero (UInt256.isZero status) = ⟨0⟩ := by
    rw [hstatus]
    decide
  have rdFallthrough := RD.jumpiNT rdPush hJumpi hcond
    (by simp only [List.length_cons]; omega)
  have rdReturndatasize := RD.returndatasize rdFallthrough hReturndatasize
    (by simp only [List.length_cons]; omega)
  have rdPush0 := RD.push1 rdReturndatasize ⟨0⟩ hPush0
    (by simp only [List.length_cons]; omega)
  have rdDupZero := RD.dup1 rdPush0 hDupZero
    (by simp only [List.length_cons]; omega)
  let len := UInt256.ofNat rdata.size
  let memout := rdata.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rdCopy := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rdDupZero hReturndatacopy
    (by
      change 0 + len.toNat ≤ rdata.size
      dsimp [len]
      rw [ulit_toNat' rdata.size hrdataSize]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, len, awout])
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rdReturndatasizeRevert := RD.returndatasize rdCopy hReturndatasizeRevert
    (by simp only [List.length_cons]; omega)
  have rdPushRevert0 := RD.push1 rdReturndatasizeRevert ⟨0⟩ hPushRevert0
    (by simp only [List.length_cons]; omega)
  exact RD.rev (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rdPushRevert0 hRevert
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

-- GENERALIZES Reasoning.Reach.RD.call — same opaque `Θ` reach proof for
-- `STATICCALL`, parameterizing the call opcode, stack arity, transferred value, and callee
-- static-permission flag.
-- LIBRARY CANDIDATE: Reasoning.Reach — generic `STATICCALL` call-made `RD` combinator.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapStaticcall {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {gasArg target inOffset inSize outOffset outSize : UInt256}
    {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.STATICCALL, .none))
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
          (mem.readWithPadding inOffset.toNat inSize.toNat) (ee.depth + 1) ee.header false)
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
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.STATICCALL, .none) := by
      rw [hcode, hpc]; exact hdec
    have hdepth' : s.executionEnv.depth.val < 1024 := by rw [hee]; exact hdepth
    have st := step_staticcall s hd
    rw [hstk] at st
    have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 - 6 + 1 > 1024) = False :=
      eq_false (by omega)
    have hdepthLt : s.executionEnv.depth < 1024 := by rw [Fin.lt_def]; exact hdepth'
    have hbal : ∀ y : UInt256, ((⟨0⟩ : UInt256) ≤ y) = True :=
      fun _ => eq_true (Fin.zero_le _)
    have hgtF : ∀ y : UInt256, ((⟨0⟩ : UInt256) > y) = False :=
      fun _ => eq_false (Fin.not_lt_zero _)
    have hdeqF : (s.executionEnv.depth == 1024) = false := by
      rw [beq_eq_false_iff_ne]; intro hh; rw [hh] at hdepth'; exact absurd hdepth' (by decide)
    simp only [List.length_cons, hovF, hdepthLt, hbal, hgtF, hdeqF, and_true, if_true,
      Bool.or_false] at st
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
      set mc := memoryExpansionCost s Operation.STATICCALL with hmc
      set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        (⟨0⟩ : UInt256) gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack,
          execLength := s.machineState.execLength,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return }
        s.substate with hgc
      set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        (⟨0⟩ : UInt256) gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack,
          execLength := s.machineState.execLength + 1,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return }
        s.substate with hG
      set cg := UInt256.ofNat G with hcg
      set ce := Cextra (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        (⟨0⟩ : UInt256) s.accountMap s.substate with hce
      set θs := Θ s.executionEnv.blobVersionedHashes s.createdAccounts s.genesisBlockHeader
        s.blocks s.accountMap s.σ₀
        (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
        (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner))
        s.executionEnv.sender (AccountAddress.ofUInt256 target)
        (toExecute s.accountMap (AccountAddress.ofUInt256 target)) cg
        (UInt256.ofNat s.executionEnv.gasPrice) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)
        (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (s.executionEnv.depth + 1) s.executionEnv.header false with hθs
      set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - θs.2.2.1.toNat)
        with hgv
      have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
      have hσ : s.accountMap = σ := congrArg Prod.snd hacc
      have hw1 : s.σ₀ = s0.σ₀ := hworld.1
      have hw2 : s.genesisBlockHeader = s0.genesisBlockHeader := hworld.2.1
      have hw3 : s.blocks = s0.blocks := hworld.2.2
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hmcle : mc ≤ s.machineState.gasAvailable.toNat := by omega
      have hretle : θs.2.2.1.toNat ≤ cg.toNat := by
        rw [hθs]
        exact Theta_returnedGas_le s.executionEnv.blobVersionedHashes s.createdAccounts
          s.genesisBlockHeader s.blocks s.accountMap s.σ₀
          (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
          (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner))
          s.executionEnv.sender (AccountAddress.ofUInt256 target)
          (toExecute s.accountMap (AccountAddress.ofUInt256 target)) cg
          (UInt256.ofNat s.executionEnv.gasPrice) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)
          (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
          (s.executionEnv.depth + 1) s.executionEnv.header false
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
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      have hrefundCostPos : 1 ≤ gc - θs.2.2.1.toNat := by omega
      set callCharge := mc + (gc - θs.2.2.1.toNat) with hcallCharge
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
          s.accountMap s.σ₀
          (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
          (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner))
          s.executionEnv.sender (AccountAddress.ofUInt256 target)
          (toExecute s.accountMap (AccountAddress.ofUInt256 target))
          (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
          cg (UInt256.ofNat s.executionEnv.gasPrice) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)
          (s.executionEnv.depth + 1) s.executionEnv.header false
          (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)

-- LIBRARY CANDIDATE: Reasoning.Reach — generic `STATICCALL` depth-limit `RD` combinator.
theorem RD.uniswapStaticcallDepthLimit {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {gasArg target inOffset inSize outOffset outSize : UInt256}
    {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.STATICCALL, .none))
    (hdepth : ee.depth = 1024)
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
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.STATICCALL, .none) := by
      rw [hcode, hpc]; exact hdec
    have hdepth1024 : s.executionEnv.depth = 1024 := by rw [hee]; exact hdepth
    have st := step_staticcall s hd
    rw [hstk] at st
    have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 - 6 + 1 > 1024) = False :=
      eq_false (by omega)
    have hdepthF : (s.executionEnv.depth < 1024) = False :=
      eq_false (by rw [hdepth1024]; exact lt_irrefl _)
    have hbal : ∀ y : UInt256, ((⟨0⟩ : UInt256) ≤ y) = True :=
      fun _ => eq_true (Fin.zero_le _)
    have hgtF : ∀ y : UInt256, ((⟨0⟩ : UInt256) > y) = False :=
      fun _ => eq_false (Fin.not_lt_zero _)
    have hdeqT : (s.executionEnv.depth == 1024) = true := by
      rw [beq_iff_eq]; exact hdepth1024
    simp only [List.length_cons, hovF, hdepthF, hbal, hgtF, hdeqT, and_false,
      Bool.or_true, if_true] at st
    rw [collapse_two_stage, hcode] at st
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    set mc := memoryExpansionCost s Operation.STATICCALL with hmc
    set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
      (⟨0⟩ : UInt256) gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack,
        execLength := s.machineState.execLength,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return }
      s.substate with hgc
    set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
      (⟨0⟩ : UInt256) gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack,
        execLength := s.machineState.execLength + 1,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return }
      s.substate with hG
    set ce := Cextra (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
      (⟨0⟩ : UInt256) s.accountMap s.substate with hce
    set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - (UInt256.ofNat G).toNat)
      with hgv
    have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    split at hXP
    · exact ⟨k, C, by unfold RD; exact Or.inl hXP⟩
    · rename_i hP
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hmcle : mc ≤ s.machineState.gasAvailable.toNat := by omega
      have hcgle : (UInt256.ofNat G).toNat ≤ G := by
        show G % UInt256.size ≤ G
        exact Nat.mod_le _ _
      have hgcG : gc = G + ce := by
        rw [hgc, hG, hce]
        rfl
      have hce1 : 1 ≤ ce := by
        rw [hce]
        have hcacc : 1 ≤ Caccess (AccountAddress.ofUInt256 target) s.substate := by
          unfold Caccess; split <;> decide
        unfold Cextra
        omega
      have hgcle' : gc ≤ (s.machineState.gasAvailable.subNat mc).toNat := by
        rw [toNat_sub_ofNat hmcle]
        omega
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

end Reasoning.Reach

namespace UniswapV2Pair

/-! ## Shared external-call calldata buffers -/

abbrev balanceOfSelectorWord : UInt256 := ⟨1889567281⟩

abbrev balanceOfSelectorShifted : UInt256 :=
  UInt256.shiftLeft balanceOfSelectorWord ⟨224⟩

noncomputable def balanceOfThisSelectorMem : ByteArray :=
  (UInt256.toByteArray balanceOfSelectorShifted).write 0 solcFreePtrMem 128 32

noncomputable def balanceOfThisCalldataMem (self : UInt256) : ByteArray :=
  (UInt256.toByteArray self).write 0 balanceOfThisSelectorMem 132 32

noncomputable def balanceOfThisStaticcallMem (self : UInt256) (o : ByteArray) : ByteArray :=
  o.write 0 (balanceOfThisCalldataMem self) 128 (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat

noncomputable def balanceOfThisRebuiltSelectorMem (self : UInt256) (o : ByteArray) : ByteArray :=
  (UInt256.toByteArray balanceOfSelectorShifted).write 0
    (balanceOfThisStaticcallMem self o) 128 32

noncomputable def balanceOfThisRebuiltCalldataMem (self : UInt256) (o : ByteArray) : ByteArray :=
  (UInt256.toByteArray self).write 0 (balanceOfThisRebuiltSelectorMem self o) 132 32

noncomputable def balanceOfThisRebuiltStaticcallMem
    (self : UInt256) (oPrev o : ByteArray) : ByteArray :=
  o.write 0 (balanceOfThisRebuiltCalldataMem self oPrev) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat

abbrev balanceOfThisStaticcallActiveWords : UInt256 :=
  UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat 128 36) 128 32)

theorem balanceOfThisSelectorMem_size : balanceOfThisSelectorMem.size = 160 :=
  solcReturnMem_size balanceOfSelectorShifted

theorem balanceOfThisSelectorMem_read64 :
    balanceOfThisSelectorMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  solcReturnMem_read64 balanceOfSelectorShifted

theorem balanceOfThisCalldataMem_size (self : UInt256) :
    (balanceOfThisCalldataMem self).size = 164 := by
  unfold balanceOfThisCalldataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [balanceOfThisSelectorMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, balanceOfThisSelectorMem_size,
    toByteArray_size]
  omega

theorem balanceOfThisCalldataMem_read64 (self : UInt256) :
    (balanceOfThisCalldataMem self).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfThisCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [balanceOfThisSelectorMem_size]; omega) (by omega),
    balanceOfThisSelectorMem_read64]

theorem balanceOfThisCalldataMem_mload64 (self : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (balanceOfThisCalldataMem self).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfThisCalldataMem self).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [balanceOfThisCalldataMem_size]; decide) (by decide)
    (balanceOfThisCalldataMem_read64 self)

-- LIBRARY CANDIDATE: Reasoning.Memory — split an in-bounds padded read into adjacent pieces.
theorem byteArray_readWithPadding_split (source : ByteArray) (addr len₁ len₂ : Nat)
    (hpos₁ : 0 < len₁) (hpos₂ : 0 < len₂)
    (hlen₁ : len₁ < 2 ^ 64) (hlen₂ : len₂ < 2 ^ 64)
    (hsum : len₁ + len₂ < 2 ^ 64)
    (hin : addr + len₁ + len₂ ≤ source.size) :
    source.readWithPadding addr (len₁ + len₂) =
      source.readWithPadding addr len₁ ++ source.readWithPadding (addr + len₁) len₂ := by
  rw [readWithPadding_eq_extract' source addr (len₁ + len₂) (by omega) hsum (by omega)]
  rw [readWithPadding_eq_extract' source addr len₁ hpos₁ hlen₁ (by omega)]
  rw [readWithPadding_eq_extract' source (addr + len₁) len₂ hpos₂ hlen₂ (by omega)]
  symm
  rw [ByteArray.extract_append_extract]
  congr <;> omega

theorem balanceOfThisSelectorMem_read128_4 :
    balanceOfThisSelectorMem.readWithPadding 128 4 = balanceOfSelector := by
  have hzero32 : (ffi.ByteArray.zeroes (USize.ofNat 32)).size = 32 := by
    rw [ByteArray_zeroes_size]
    exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))
  rw [show balanceOfThisSelectorMem = solcReturnMem balanceOfSelectorShifted from rfl]
  rw [readWithPadding_eq_extract' _ 128 4 (by norm_num) (by norm_num)
      (by rw [solcReturnMem_size]; omega)]
  rw [solcReturnMem_eq]
  rw [extract_append_right_window
      (solcFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat 32))
      (UInt256.toByteArray balanceOfSelectorShifted) 128 132 (by
        simp [ByteArray.size_append, solcFreePtrMem_size, hzero32])]
  rw [ByteArray.size_append, solcFreePtrMem_size, hzero32]
  native_decide

theorem balanceOfThisCalldataMem_read132_32 (self : UInt256) :
    (balanceOfThisCalldataMem self).readWithPadding 132 32 = UInt256.toByteArray self := by
  unfold balanceOfThisCalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by simp [balanceOfThisSelectorMem_size])]
  rw [show (UInt256.toByteArray self).extract 0 32 = UInt256.toByteArray self by
    rw [show 32 = (UInt256.toByteArray self).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem balanceOfThisCalldataMem_read128_4 (self : UInt256) :
    (balanceOfThisCalldataMem self).readWithPadding 128 4 = balanceOfSelector := by
  unfold balanceOfThisCalldataMem
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
      (by simp [balanceOfThisSelectorMem_size]) (by omega)
      (by simp [balanceOfThisSelectorMem_size]) (by norm_num) (by norm_num)]
  exact balanceOfThisSelectorMem_read128_4

theorem balanceOfThisCalldataMem_read128_36 (self : UInt256) :
    (balanceOfThisCalldataMem self).readWithPadding 128 36 =
      balanceOfSelector ++ UInt256.toByteArray self := by
  rw [byteArray_readWithPadding_split _ 128 4 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by simp [balanceOfThisCalldataMem_size])]
  rw [balanceOfThisCalldataMem_read128_4, balanceOfThisCalldataMem_read132_32]

theorem balanceOfThisCalldataMem_encode (self : AccountAddress) :
    config.externalABI.encode? "balanceOf" [.address self] =
      some ((balanceOfThisCalldataMem (UInt256.ofNat self.val)).readWithPadding 128 36) := by
  rw [balanceOfThisCalldataMem_read128_36]
  change uniswapExternalABI.encode? "balanceOf" [.address self] =
    some (balanceOfSelector ++ (UInt256.ofNat self.val).toByteArray)
  unfold uniswapExternalABI ABI.encodeCallWithSelector? ABI.encodeABIValues?
  simp [addr, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
    ABI.isDynamicABIType, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.encodeABIValuesFrom?]
  rw [word_toBytesBE_toByteArray_eq_toByteArray]
  rfl

-- LIBRARY CANDIDATE: Reasoning.EVMWord — `min (literal word) (UInt256.ofNat n)` collapses
-- to the literal when `n` is large enough and in range.
theorem balanceOfThisStaticcallWriteLen_of_size_ge (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 := by
  show (if (⟨32⟩ : UInt256) ≤ UInt256.ofNat o.size then (⟨32⟩ : UInt256)
    else UInt256.ofNat o.size).toNat = 32
  rw [if_pos]
  · rfl
  · show (32 : Nat) ≤ (UInt256.ofNat o.size).val.val
    rw [show (UInt256.ofNat o.size).val.val = (UInt256.ofNat o.size).toNat from rfl,
      ulit_toNat' o.size hhi]
    exact hlo

theorem balanceOfThisStaticcallMem_size_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisStaticcallMem self o).size = 164 := by
  unfold balanceOfThisStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge o hlo hhi]
  rw [write32_eq _ _ _ hlo (by rw [balanceOfThisCalldataMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, balanceOfThisCalldataMem_size]
  omega

-- LIBRARY CANDIDATE: Reasoning.Memory — free-pointer read below an external-call returndata
-- write into the ABI output region.
theorem balanceOfThisStaticcallMem_read64_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisStaticcallMem self o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfThisStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge o hlo hhi]
  rw [write32_read_below _ _ 128 64 hlo
    (by rw [balanceOfThisCalldataMem_size]; omega) (by omega)]
  exact balanceOfThisCalldataMem_read64 self

theorem balanceOfThisStaticcallMem_mload64_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (balanceOfThisStaticcallMem self o).size
        ∨ (⟨64⟩ : UInt256) ≥ balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfThisStaticcallMem self o).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [balanceOfThisStaticcallMem_size_of_size_ge self o hlo hhi]; decide)
    (by decide)
    (balanceOfThisStaticcallMem_read64_of_size_ge self o hlo hhi)

theorem balanceOfThisStaticcallWriteLen_of_size_lt (o : ByteArray)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size := by
  show (if (⟨32⟩ : UInt256) ≤ UInt256.ofNat o.size then (⟨32⟩ : UInt256)
    else UInt256.ofNat o.size).toNat = o.size
  rw [if_neg]
  · exact ulit_toNat' o.size hhi
  · show ¬ (32 : Nat) ≤ (UInt256.ofNat o.size).val.val
    rw [show (UInt256.ofNat o.size).val.val = (UInt256.ofNat o.size).toNat from rfl,
      ulit_toNat' o.size hhi]
    omega

theorem balanceOfThisStaticcallMem_size_of_size_lt (self : UInt256) (o : ByteArray)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size) :
    (balanceOfThisStaticcallMem self o).size = 164 := by
  unfold balanceOfThisStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_lt o hshort hhi]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero, balanceOfThisCalldataMem_size]
  · rw [write_eq_gen _ _ 128 o.size hzero le_rfl
      (by rw [balanceOfThisCalldataMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, balanceOfThisCalldataMem_size]
    omega

theorem balanceOfThisStaticcallMem_read64_of_size_lt (self : UInt256) (o : ByteArray)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size) :
    (balanceOfThisStaticcallMem self o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfThisStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_lt o hshort hhi]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact balanceOfThisCalldataMem_read64 self
  · rw [write_read_below_gen _ _ 128 o.size 64 hzero le_rfl
      (by rw [balanceOfThisCalldataMem_size]; omega) (by omega)]
    exact balanceOfThisCalldataMem_read64 self

theorem balanceOfThisStaticcallMem_mload64_of_size_lt (self : UInt256) (o : ByteArray)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (balanceOfThisStaticcallMem self o).size
        ∨ (⟨64⟩ : UInt256) ≥ balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfThisStaticcallMem self o).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [balanceOfThisStaticcallMem_size_of_size_lt self o hshort hhi]; decide)
    (by decide)
    (balanceOfThisStaticcallMem_read64_of_size_lt self o hshort hhi)

-- LIBRARY CANDIDATE: Reasoning.Memory — read back the first ABI return word copied by a
-- CALL-like opcode into the output region.
theorem balanceOfThisStaticcallMem_read128_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisStaticcallMem self o).readWithPadding 128 32 = o.extract 0 32 := by
  unfold balanceOfThisStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge o hlo hhi]
  exact write32_read_back _ _ 128 hlo (by rw [balanceOfThisCalldataMem_size]; omega)

theorem balanceOfThisStaticcallMem_mload128_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (balanceOfThisStaticcallMem self o).size
        ∨ (⟨128⟩ : UInt256) ≥ balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfThisStaticcallMem self o).readWithPadding (⟨128⟩ : UInt256).toNat 32)))
      = UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) := by
  rw [if_neg]
  · rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      balanceOfThisStaticcallMem_read128_of_size_ge self o hlo hhi]
  · rw [not_or]
    constructor
    · rw [balanceOfThisStaticcallMem_size_of_size_ge self o hlo hhi]
      decide
    · decide

theorem balanceOfThisRebuiltSelectorMem_size_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisRebuiltSelectorMem self o).size = 164 := by
  unfold balanceOfThisRebuiltSelectorMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [balanceOfThisStaticcallMem_size_of_size_ge self o hlo hhi]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    balanceOfThisStaticcallMem_size_of_size_ge self o hlo hhi, toByteArray_size]
  omega

theorem balanceOfThisRebuiltSelectorMem_read64_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisRebuiltSelectorMem self o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfThisRebuiltSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [balanceOfThisStaticcallMem_size_of_size_ge self o hlo hhi]; omega) (by omega),
    balanceOfThisStaticcallMem_read64_of_size_ge self o hlo hhi]

theorem balanceOfThisRebuiltCalldataMem_size_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisRebuiltCalldataMem self o).size = 164 := by
  unfold balanceOfThisRebuiltCalldataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [balanceOfThisRebuiltSelectorMem_size_of_size_ge self o hlo hhi]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    balanceOfThisRebuiltSelectorMem_size_of_size_ge self o hlo hhi, toByteArray_size]
  omega

-- LIBRARY CANDIDATE: Reasoning.Memory — free-pointer read survives repeated
-- calldata-buffer rewrites above the free-pointer word.
theorem balanceOfThisRebuiltCalldataMem_read64_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisRebuiltCalldataMem self o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfThisRebuiltCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [balanceOfThisRebuiltSelectorMem_size_of_size_ge self o hlo hhi]; omega)
      (by omega),
    balanceOfThisRebuiltSelectorMem_read64_of_size_ge self o hlo hhi]

theorem balanceOfThisRebuiltCalldataMem_mload64_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (balanceOfThisRebuiltCalldataMem self o).size
        ∨ (⟨64⟩ : UInt256) ≥ balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfThisRebuiltCalldataMem self o).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [balanceOfThisRebuiltCalldataMem_size_of_size_ge self o hlo hhi]; decide)
    (by decide)
    (balanceOfThisRebuiltCalldataMem_read64_of_size_ge self o hlo hhi)

theorem balanceOfThisRebuiltStaticcallMem_size_of_size_ge
    (self : UInt256) (oPrev o : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisRebuiltStaticcallMem self oPrev o).size = 164 := by
  unfold balanceOfThisRebuiltStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge o hlo hhi]
  rw [write32_eq _ _ _ hlo
      (by rw [balanceOfThisRebuiltCalldataMem_size_of_size_ge self oPrev hprevlo hprevhi];
          omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    balanceOfThisRebuiltCalldataMem_size_of_size_ge self oPrev hprevlo hprevhi]
  omega

-- LIBRARY CANDIDATE: Reasoning.Memory — free-pointer read survives a second
-- external-call returndata write into the ABI output region.
theorem balanceOfThisRebuiltStaticcallMem_read64_of_size_ge
    (self : UInt256) (oPrev o : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisRebuiltStaticcallMem self oPrev o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfThisRebuiltStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge o hlo hhi]
  rw [write32_read_below _ _ 128 64 hlo
      (by rw [balanceOfThisRebuiltCalldataMem_size_of_size_ge self oPrev hprevlo hprevhi];
          omega) (by omega),
    balanceOfThisRebuiltCalldataMem_read64_of_size_ge self oPrev hprevlo hprevhi]

theorem balanceOfThisRebuiltStaticcallMem_mload64_of_size_ge
    (self : UInt256) (oPrev o : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (balanceOfThisRebuiltStaticcallMem self oPrev o).size
        ∨ (⟨64⟩ : UInt256) ≥ balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfThisRebuiltStaticcallMem self oPrev o).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by
      rw [balanceOfThisRebuiltStaticcallMem_size_of_size_ge self oPrev o hprevlo hprevhi
        hlo hhi]
      decide)
    (by decide)
    (balanceOfThisRebuiltStaticcallMem_read64_of_size_ge self oPrev o hprevlo hprevhi
      hlo hhi)

-- LIBRARY CANDIDATE: Reasoning.Memory — read back the first ABI return word copied by a
-- second CALL-like opcode into a rebuilt output region.
theorem balanceOfThisRebuiltStaticcallMem_read128_of_size_ge
    (self : UInt256) (oPrev o : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisRebuiltStaticcallMem self oPrev o).readWithPadding 128 32 =
      o.extract 0 32 := by
  unfold balanceOfThisRebuiltStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge o hlo hhi]
  exact write32_read_back _ _ 128 hlo
    (by
      rw [balanceOfThisRebuiltCalldataMem_size_of_size_ge self oPrev hprevlo hprevhi]
      omega)

theorem balanceOfThisRebuiltStaticcallMem_mload128_of_size_ge
    (self : UInt256) (oPrev o : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (balanceOfThisRebuiltStaticcallMem self oPrev o).size
        ∨ (⟨128⟩ : UInt256) ≥ balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfThisRebuiltStaticcallMem self oPrev o).readWithPadding
          (⟨128⟩ : UInt256).toNat 32)))
      = UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) := by
  rw [if_neg]
  · rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      balanceOfThisRebuiltStaticcallMem_read128_of_size_ge self oPrev o hprevlo hprevhi
        hlo hhi]
  · rw [not_or]
    constructor
    · rw [balanceOfThisRebuiltStaticcallMem_size_of_size_ge self oPrev o hprevlo hprevhi
        hlo hhi]
      decide
    · decide

end UniswapV2Pair

namespace Reasoning.Reach

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc high-level-call uint256 return decoder
-- after a successful CALL-like opcode, parameterized by the output buffer and dead stack pops.
set_option maxHeartbeats 2000000 in
theorem RD.uniswapUint256ReturnWordDecodeOk {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {d0 d1 d2 retWord : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (d0 :: d1 :: d2 :: R) mem
      UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k C)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥
            UniswapV2Pair.balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥
            UniswapV2Pair.balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.MLOAD, .none))
    (hReturndatasize :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush32 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hLt :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hIszero :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hPushOk :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code
          ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPopLen : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hMload128 : decode code (okPc + ⟨1⟩ + ⟨1⟩) = some (.MLOAD, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) (retWord :: R)
      mem UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k' C' := by
  have rdPop0 := RD.pop h hPop0 (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0 hPop1 (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1 hPop2 (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ hPush64 (by omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ UniswapV2Pair.balanceOfThisStaticcallActiveWords
    rdPush64 hMload64
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
      native_decide)
    hMload64Value
    (by native_decide)
    (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64 hReturndatasize
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ hPush32
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 hDup2 (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 hLt (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' o.size hhi]
    exact hlo
  have rdIszero := RD.iszero rdLt hIszero (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero okPc hPushOk
    (by simp only [List.length_cons]; omega)
  have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rdJumpi := RD.jumpiT rdPushOk hJumpi hcond hjd
    (by simp only [List.length_cons]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi hJumpdest
    (by simp only [List.length_cons]; omega)
  have rdPopLen := RD.pop rdJumpdest hPopLen (by simp only [List.length_cons]; omega)
  have rdMload128 := RD.mload 0 retWord UniswapV2Pair.balanceOfThisStaticcallActiveWords
    rdPopLen hMload128
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
      native_decide)
    hMload128Value
    (by native_decide)
    (by omega)
  exact ⟨_, _, rdMload128⟩

set_option maxHeartbeats 2000000 in
theorem RD.uniswapUint256ReturnWordDecodeShortReverts {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (d0 :: d1 :: d2 :: R) mem
      UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k C)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥
            UniswapV2Pair.balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.MLOAD, .none))
    (hReturndatasize :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush32 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hLt :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hIszero :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hPushOk :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code
          ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hPush0 :
      decode code
          (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
            ⟨1⟩) =
        some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hDupZero :
      decode code
          ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
                UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
              ⟨1⟩) + UInt256.ofNat 2) =
        some (.DUP1, .none))
    (hRevert :
      decode code
          (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
                  UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
                ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩) =
        some (.REVERT, .none))
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  have rdPop0 := RD.pop h hPop0 (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0 hPop1 (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1 hPop2 (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ hPush64 (by omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ UniswapV2Pair.balanceOfThisStaticcallActiveWords
    rdPush64 hMload64
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
      native_decide)
    hMload64Value
    (by native_decide)
    (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64 hReturndatasize
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ hPush32
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 hDup2 (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 hLt (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' o.size hhi]
    exact hshort
  have rdIszero := RD.iszero rdLt hIszero (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero okPc hPushOk
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk hJumpi hcond
    (by simp only [List.length_cons]; omega)
  exact RD.uniswapPush1Dup1Revert0 rdFallthrough hPush0 hDupZero hRevert
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapBalanceOfReturnWordDecodeOk {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc self : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (d0 :: d1 :: d2 :: R)
      (UniswapV2Pair.balanceOfThisStaticcallMem self o)
      UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k C)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.MLOAD, .none))
    (hReturndatasize :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush32 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hLt :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hIszero :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hPushOk :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code
          ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPopLen : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hMload128 : decode code (okPc + ⟨1⟩ + ⟨1⟩) = some (.MLOAD, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) :: R)
      (UniswapV2Pair.balanceOfThisStaticcallMem self o)
      UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k' C' := by
  exact RD.uniswapUint256ReturnWordDecodeOk h hlo hhi
    (UniswapV2Pair.balanceOfThisStaticcallMem_mload64_of_size_ge self o hlo hhi)
    (UniswapV2Pair.balanceOfThisStaticcallMem_mload128_of_size_ge self o hlo hhi)
    hPop0 hPop1 hPop2 hPush64 hMload64 hReturndatasize hPush32 hDup2 hLt hIszero
    hPushOk hJumpi hjd hJumpdest hPopLen hMload128 hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapBalanceOfReturnWordDecodeShortReverts {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc self : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (d0 :: d1 :: d2 :: R)
      (UniswapV2Pair.balanceOfThisStaticcallMem self o)
      UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k C)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.MLOAD, .none))
    (hReturndatasize :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush32 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hLt :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hIszero :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hPushOk :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code
          ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hPush0 :
      decode code
          (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
            ⟨1⟩) =
        some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hDupZero :
      decode code
          ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
                UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
              ⟨1⟩) + UInt256.ofNat 2) =
        some (.DUP1, .none))
    (hRevert :
      decode code
          (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
                  UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
                ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩) =
        some (.REVERT, .none))
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.uniswapUint256ReturnWordDecodeShortReverts h hshort hhi
    (UniswapV2Pair.balanceOfThisStaticcallMem_mload64_of_size_lt self o hshort hhi)
    hPop0 hPop1 hPop2 hPush64 hMload64 hReturndatasize hPush32 hDup2 hLt hIszero
    hPushOk hJumpi hPush0 hDupZero hRevert hov

theorem RD.uniswapRebuiltBalanceOfReturnWordDecodeOk {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc self : UInt256} {oPrev o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (d0 :: d1 :: d2 :: R)
      (UniswapV2Pair.balanceOfThisRebuiltStaticcallMem self oPrev o)
      UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k C)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.MLOAD, .none))
    (hReturndatasize :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush32 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hLt :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hIszero :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hPushOk :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code
          ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPopLen : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hMload128 : decode code (okPc + ⟨1⟩ + ⟨1⟩) = some (.MLOAD, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) :: R)
      (UniswapV2Pair.balanceOfThisRebuiltStaticcallMem self oPrev o)
      UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k' C' := by
  exact RD.uniswapUint256ReturnWordDecodeOk h hlo hhi
    (UniswapV2Pair.balanceOfThisRebuiltStaticcallMem_mload64_of_size_ge self oPrev o
      hprevlo hprevhi hlo hhi)
    (UniswapV2Pair.balanceOfThisRebuiltStaticcallMem_mload128_of_size_ge self oPrev o
      hprevlo hprevhi hlo hhi)
    hPop0 hPop1 hPop2 hPush64 hMload64 hReturndatasize hPush32 hDup2 hLt hIszero
    hPushOk hJumpi hjd hJumpdest hPopLen hMload128 hov

end Reasoning.Reach
