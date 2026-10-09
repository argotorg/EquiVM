import EVMReasoning.Trace
import EVMReasoning.Solc

/-!
# SolcTrace — the solc compiler idioms on `Run`

The compiler-shape lemmas of `EVMReasoning.Solc` restated on the `Run`/`Returned`/`Reverted`
tracker of `EVMReasoning.Trace`.  The pure facts of `Solc.lean` (bytecode-shape predicates
`*Wf`, pc arithmetic, memory shapes, mapping slots, the address mask) are reused unchanged; only
the trace-level lemmas are restated.  Compared with their `RD` originals they

* read the execution environment from `s0` and carry the world `w` (accounts **and** logs);
* state every revert with its exact data: `ByteArray.empty` for the `revert(0,0)` stubs, the
  `Error(string)` payload of the string-revert tails, the bubbled return data of a failed call;
* expose the `LogEntry` an event suffix appends;
* take the cursor they start from as a plain `Run` hypothesis (no `∃ k C` inputs), over an
  arbitrary `s0`/world/memory wherever the shape allows it.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Trace

open Reasoning.Theory
open Reasoning.Reach (pushAt armSelNat armTgt armTgtOp armTgtWidth armWellFormed selArmNextPc
  selectorSplitWellFormed nthArmPc Theta_returnedGas_le Theta_returnData_size_lt
  solcAddressSlotGetterWf solcGetterEntryWf solcWordSlotGetterWf solcConstGetterWf solcSlotWord
  twoWordHashMem_solcMappingSlot solcSingleMappingLoadToRoutineMemWf
  solcSingleMappingStoreDebitMemWf solcSingleMappingStoreDebitOutPc
  solcSingleMappingStoreCreditMemWf solcSingleMappingStoreCreditOutPc
  solcNestedMappingStoreInnerHashWf solcNestedMappingStoreInnerHashOutPc
  solcNestedMappingStoreOuterSstoreWf solcNestedMappingStoreOuterSstoreOutPc
  solcNestedMappingCallerHashMem solcNestedMappingCallerStoreMemWf
  solcNestedMappingCallerStoreMemOutPc solcNestedMappingCallerLoadWf
  solcNestedMappingCallerLoadOutPc solcUintMaxEqBranchWf solcUintMaxEqBranchFallthroughPc
  solcNestedMappingCallerReloadToRoutineMemWf solcPreparedSingleMappingLoadToRoutineMemWf
  solcSingleMappingGetterWf solcNestedMappingGetterWf solcNestedMappingGetterSloadPc
  solcNestedMappingGetterAfterInnerHashPc solcLockEnterOkWf solcCheckedSubSuccessWf
  solcCheckedAddSuccessWf solcCheckedArithmeticRevertPc solcErrorStringRevertTailWf
  solcLockEnterGuardWf solcLockEnterRevertPc solcDiscard2ReturnTrueWf solcDiscard4ReturnTrueWf
  solcMaskedTransferLog3AndJumpWf solcPlainLog3AndJumpWf solcReturnWordFromMemWf
  solcReturnAddressFromMemWf solcReturnUint8FromMemWf solcReturnBoolFromMemWf
  solcInlinedDecodeAddrPc1 solcInlinedDecodeAddrPc2 solcInlinedDecodeAddrPc3
  solcInlinedDecodeAddrPc5 solcInlinedDecodeAddrPc7 solcInlinedDecodeAddrPc9
  solcInlinedDecodeAddrPc10 solcInlinedDecodeAddrPc11 solcInlinedDecodeAddrPc12
  solcInlinedDecodeAddrPc13 solcInlinedDecodeAddrPc14 solcInlinedDecodeAddrPc15
  solcInlinedDecodeAddrPc18 solcInlinedDecodeAddrPc19 solcInlinedDecodeAddrPc22
  solcInlinedDecodeAddrPc23 solcInlinedDecodeAddrPc24 solcInlinedDecodeAddrPc25
  solcInlinedDecodeAddrPc26 solcGuardTgtOp solcGuardTgt solcGuardTgtWidth solcGuardJumpiPc
  solcDispatchBodyPc solcCalldataRevertPushPc solcCalldataRevertTgtOp solcCalldataRevertTgt
  solcCalldataRevertTgtWidth solcCalldataJumpiPc solcSelectorLoadPc solcFirstArmPcFromPrefix
  solcDispatchPrefixWellFormed)

set_option maxRecDepth 10000

variable {code : ByteArray} {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray}
  {aw : UInt256} {rdata : ByteArray} {w : World} {k C : ℕ} {R : List UInt256}

@[simp] theorem initState_executionEnv {cA gh bl σ σ₀ A I} {g : Sat256} :
    (Reasoning.Theory.initState cA gh bl σ σ₀ g A I).executionEnv = I := rfl

/-! ## `revert(0,0)` stubs -/

/-- `PUSH0; PUSH0; REVERT`: the run reverts with empty data. -/
theorem Run.revertStub (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hd0 : decode code pc = some (.PUSH0, .none))
    (hd1 : decode code (pc + ⟨1⟩) = some (.PUSH0, .none))
    (hd2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none))
    (hov : stk.length + 2 ≤ 1024) :
    Reverted code s0 ByteArray.empty :=
  h.push0 hd0 (by omega)
    |>.push0 hd1 (by simp only [List.length_cons]; omega)
    |>.rev 0 ByteArray.empty hd2 (fun s _ hstks => memExpRevert0 s hstks)
      (byteArray_readWithPadding_zero _ _) (by omega)

/-- Legacy `PUSH1 0; DUP1; REVERT`. -/
theorem Run.solcPush1Dup1Revert0 (h : Run code s0 ⟨pc, stk, mem, aw, rdata, w⟩ k C)
    (hd0 : decode code pc = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hd1 : decode code (pc + UInt256.ofNat 2) = some (.DUP1, .none))
    (hd2 : decode code (pc + UInt256.ofNat 2 + ⟨1⟩) = some (.REVERT, .none))
    (hov : stk.length + 2 ≤ 1024) :
    Reverted code s0 ByteArray.empty :=
  h.push1 ⟨0⟩ hd0 (by omega)
    |>.dup1 hd1 (by omega)
    |>.rev 0 ByteArray.empty hd2 (fun s _ hstks => memExpRevert0 s hstks)
      (byteArray_readWithPadding_zero _ _) (by omega)

/-! ## Entry prologue and dispatcher scaffold

`PUSH1 0x80; PUSH1 0x40; MSTORE; CALLVALUE; DUP1; ISZERO` opens every solc contract.  The
lemmas after the prologue are stated over an arbitrary run `s0` (the prologue's cursor carries
`s0.executionEnv.weiValue`; for `s0 = initState … I` that is `I.weiValue` by unfolding). -/

theorem Run.solcGuardPrologue {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = code)
    (hd0 : decode code ⟨0⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)))
    (hd2 : decode code ⟨2⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hd4 : decode code ⟨4⟩ = some (.MSTORE, .none))
    (hd5 : decode code ⟨5⟩ = some (.CALLVALUE, .none))
    (hd6 : decode code ⟨6⟩ = some (.DUP1, .none))
    (hd7 : decode code ⟨7⟩ = some (.ISZERO, .none)) :
    Run code (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      ⟨⟨8⟩, [UInt256.isZero I.weiValue, I.weiValue], solcFreePtrMem, UInt256.ofNat 3,
        ByteArray.empty, ⟨cA, σ, A.logSeries⟩⟩ 6 26 :=
  Run.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (g := g) (A := A) hcode
    |>.push1 ⟨128⟩ hd0 (by decide)
    |>.push1 ⟨64⟩ hd2 (by decide)
    |>.mstore 9 solcFreePtrMem (UInt256.ofNat 3) hd4 mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl) (by decide) (by decide)
    |>.callvalue hd5 (by decide)
    |>.dup1 hd6 (by simp only [List.length_nil]; omega)
    |>.iszero hd7 (by simp only [List.length_cons, List.length_nil]; omega)

/-- **Callvalue-zero guard**: the guard `JUMPI` is taken, `JUMPDEST; POP` leave an empty stack at
    `ctgt + 2`. -/
theorem Run.solcGuardCallvalueZero {ctgt : UInt256} {wC : ℕ} {opC : Operation.POp}
    (h : Run code s0 ⟨⟨8⟩, [UInt256.isZero s0.executionEnv.weiValue, s0.executionEnv.weiValue],
      mem, aw, rdata, w⟩ k C)
    (hwv : s0.executionEnv.weiValue = ⟨0⟩) (hopC : opC ≠ .PUSH0)
    (hpushC : decode code ⟨8⟩ = some (.Push opC, some (ctgt, wC)))
    (hjumpi : decode code (⟨8⟩ + UInt256.ofNat wC.succ) = some (.JUMPI, .none))
    (hjmpdest : decode code ctgt = some (.JUMPDEST, .none))
    (hpop : decode code (ctgt + ⟨1⟩) = some (.POP, .none))
    (hjd : (D_J code 0).contains ctgt = true) :
    ∃ k' C', Run code s0 ⟨ctgt + ⟨1⟩ + ⟨1⟩, [], mem, aw, rdata, w⟩ k' C' :=
  ⟨_, _, h.pushConst ctgt hopC hpushC (by simp only [List.length]; omega)
    |>.jumpiT hjumpi (by rw [hwv]; decide) hjd (by simp only [List.length]; omega)
    |>.jumpdest hjmpdest (by simp only [List.length]; omega)
    |>.pop hpop (by simp only [List.length]; omega)⟩

/-- **Callvalue-nonzero revert**: the guard falls into `PUSH0; PUSH0; REVERT`. -/
theorem Run.solcGuardCallvalueNonzeroRevert {ctgt : UInt256} {wC : ℕ} {opC : Operation.POp}
    (h : Run code s0 ⟨⟨8⟩, [UInt256.isZero s0.executionEnv.weiValue, s0.executionEnv.weiValue],
      mem, aw, rdata, w⟩ k C)
    (hwv : s0.executionEnv.weiValue ≠ ⟨0⟩) (hopC : opC ≠ .PUSH0)
    (hpushC : decode code ⟨8⟩ = some (.Push opC, some (ctgt, wC)))
    (hjumpi : decode code (⟨8⟩ + UInt256.ofNat wC.succ) = some (.JUMPI, .none))
    (hr0 : decode code (⟨8⟩ + UInt256.ofNat wC.succ + ⟨1⟩) = some (.PUSH0, .none))
    (hr1 : decode code (⟨8⟩ + UInt256.ofNat wC.succ + ⟨1⟩ + ⟨1⟩) = some (.PUSH0, .none))
    (hr2 : decode code (⟨8⟩ + UInt256.ofNat wC.succ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none)) :
    Reverted code s0 ByteArray.empty :=
  (h.pushConst ctgt hopC hpushC (by simp only [List.length]; omega)
    |>.jumpiNT hjumpi (isZero_eq_zero_of_ne hwv) (by simp only [List.length]; omega)).revertStub
    hr0 hr1 hr2 (by simp only [List.length]; omega)

/-- **Short-calldata revert**: `calldatasize < 4` sends the size check into `revert(0,0)`. -/
theorem Run.solcCalldataShortRevert {bodyPc rtgt : UInt256} {wR : ℕ} {opR : Operation.POp}
    (h : Run code s0 ⟨bodyPc, [], mem, aw, rdata, w⟩ k C)
    (hsz : s0.executionEnv.calldata.size < 4)
    (hd_p4 : decode code bodyPc = some (.Push .PUSH1, some (⟨4⟩, 1)))
    (hd_cds : decode code (bodyPc + UInt256.ofNat 2) = some (.CALLDATASIZE, .none))
    (hd_lt : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩) = some (.LT, .none))
    (hopR : opR ≠ .PUSH0)
    (hd_pR : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = some (.Push opR, some (rtgt, wR)))
    (hd_ji : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat wR.succ)
              = some (.JUMPI, .none))
    (hd_jd : decode code rtgt = some (.JUMPDEST, .none)) (hjd : (D_J code 0).contains rtgt = true)
    (hr0 : decode code (rtgt + ⟨1⟩) = some (.PUSH0, .none))
    (hr1 : decode code (rtgt + ⟨1⟩ + ⟨1⟩) = some (.PUSH0, .none))
    (hr2 : decode code (rtgt + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none)) :
    Reverted code s0 ByteArray.empty :=
  (h.push1 ⟨4⟩ hd_p4 (by simp only [List.length]; omega)
    |>.calldatasize hd_cds (by simp only [List.length]; omega)
    |>.lt hd_lt (by simp only [List.length]; omega)
    |>.pushConst rtgt hopR hd_pR (by simp only [List.length]; omega)
    |>.jumpiT hd_ji (lt_four_ne_zero_of_lt hsz) hjd (by simp only [List.length]; omega)
    |>.jumpdest hd_jd (by simp only [List.length]; omega)).revertStub
    hr0 hr1 hr2 (by simp only [List.length]; omega)

/-- **Calldata-ok continue**: `calldatasize ≥ 4` falls through to the selector load. -/
theorem Run.solcCalldataOk {bodyPc selLoadTgt : UInt256} {wR : ℕ} {opR : Operation.POp}
    (h : Run code s0 ⟨bodyPc, [], mem, aw, rdata, w⟩ k C)
    (hsz : 4 ≤ s0.executionEnv.calldata.size) (hsize : s0.executionEnv.calldata.size < UInt256.size)
    (hd_p4 : decode code bodyPc = some (.Push .PUSH1, some (⟨4⟩, 1)))
    (hd_cds : decode code (bodyPc + UInt256.ofNat 2) = some (.CALLDATASIZE, .none))
    (hd_lt : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩) = some (.LT, .none))
    (hopR : opR ≠ .PUSH0)
    (hd_pR : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩)
              = some (.Push opR, some (selLoadTgt, wR)))
    (hd_ji : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat wR.succ)
              = some (.JUMPI, .none)) :
    ∃ k' C', Run code s0
      ⟨bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat wR.succ + ⟨1⟩, [], mem, aw, rdata, w⟩
      k' C' :=
  ⟨_, _, h.push1 ⟨4⟩ hd_p4 (by simp only [List.length]; omega)
    |>.calldatasize hd_cds (by simp only [List.length]; omega)
    |>.lt hd_lt (by simp only [List.length]; omega)
    |>.pushConst selLoadTgt hopR hd_pR (by simp only [List.length]; omega)
    |>.jumpiNT hd_ji (lt_four_eq_zero_of_ge hsz hsize) (by simp only [List.length]; omega)⟩

/-- **Selector load** `PUSH0; CALLDATALOAD; PUSH1 0xe0; SHR`. -/
theorem Run.solcSelectorLoad {loadPc : UInt256}
    (h : Run code s0 ⟨loadPc, R, mem, aw, rdata, w⟩ k C)
    (hp0 : decode code loadPc = some (.PUSH0, .none))
    (hcdl : decode code (loadPc + ⟨1⟩) = some (.CALLDATALOAD, .none))
    (hp1 : decode code (loadPc + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH1, some (⟨224⟩, 1)))
    (hshr : decode code (loadPc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) = some (.SHR, .none))
    (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨loadPc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩,
      UInt256.shiftRight (uInt256OfByteArray (s0.executionEnv.calldata.readBytes 0 32)) ⟨224⟩ :: R,
      mem, aw, rdata, w⟩ k' C' :=
  ⟨_, _, h.push0 hp0 (by omega)
    |>.calldataload hcdl (by omega)
    |>.push1 ⟨224⟩ hp1 (by simp only [List.length]; omega)
    |>.shr hshr (by omega)⟩

/-- Legacy selector load `PUSH1 0; CALLDATALOAD; PUSH1 0xe0; SHR`. -/
theorem Run.solcLegacySelectorLoad {loadPc : UInt256}
    (h : Run code s0 ⟨loadPc, R, mem, aw, rdata, w⟩ k C)
    (hp0 : decode code loadPc = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hcdl : decode code (loadPc + UInt256.ofNat 2) = some (.CALLDATALOAD, .none))
    (hp1 : decode code (loadPc + UInt256.ofNat 2 + ⟨1⟩) = some (.Push .PUSH1, some (⟨224⟩, 1)))
    (hshr : decode code (loadPc + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2) = some (.SHR, .none))
    (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨loadPc + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩,
      UInt256.shiftRight (uInt256OfByteArray (s0.executionEnv.calldata.readBytes 0 32)) ⟨224⟩ :: R,
      mem, aw, rdata, w⟩ k' C' :=
  ⟨_, _, h.push1 ⟨0⟩ hp0 (by omega)
    |>.calldataload hcdl (by omega)
    |>.push1 ⟨224⟩ hp1 (by simp only [List.length]; omega)
    |>.shr hshr (by omega)⟩

/-- **Dispatcher prefix**: prologue, callvalue guard, calldata-size guard and selector load, from
    `initState` to the first selector arm with the selector word on the stack. -/
theorem Run.solcDispatchReachSelector {cA gh bl σ σ₀ A I} {g : Sat256} {firstPc : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hprefix : solcDispatchPrefixWellFormed code firstPc)
    (hguardJd : (D_J code 0).contains (solcGuardTgt code) = true) :
    ∃ k C, Run code (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      ⟨firstPc, [solcSelectorWord I], solcFreePtrMem, UInt256.ofNat 3, ByteArray.empty,
        ⟨cA, σ, A.logSeries⟩⟩ k C := by
  obtain ⟨hd0, hd2, hd4, hd5, hd6, hd7,
    hguardOp, hguardPush, hguardJumpi, hguardDest, hguardPop,
    hcdPush4, hcdSize, hcdLt, hcdOp, hcdPushRevert, hcdJumpi,
    hselPush0, hselLoad, hselPush224, hselShr, hfirst⟩ := hprefix
  have h0 := Run.solcGuardPrologue (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode hd0 hd2 hd4 hd5 hd6 hd7
  obtain ⟨_, _, h1⟩ := Run.solcGuardCallvalueZero
    (ctgt := solcGuardTgt code) (opC := solcGuardTgtOp code) (wC := solcGuardTgtWidth code)
    h0 hwv hguardOp hguardPush hguardJumpi hguardDest hguardPop hguardJd
  obtain ⟨_, _, h2⟩ := Run.solcCalldataOk
    (selLoadTgt := solcCalldataRevertTgt code)
    (opR := solcCalldataRevertTgtOp code) (wR := solcCalldataRevertTgtWidth code)
    h1 hsz hsize hcdPush4 hcdSize hcdLt hcdOp hcdPushRevert hcdJumpi
  obtain ⟨k3, C3, h3⟩ := Run.solcSelectorLoad h2 hselPush0 hselLoad hselPush224 hselShr (by simp)
  refine ⟨k3, C3, ?_⟩
  rw [← hfirst]
  exact h3

/-- Legacy dispatcher prefix (`PUSH1 0` selector load, all pcs explicit). -/
theorem Run.solcLegacyDispatchReachSelector {cA gh bl σ σ₀ A I} {g : Sat256}
    {bodyPc loadPc firstPc guardTgt revertTgt : UInt256}
    {guardWidth revertWidth : ℕ} {guardOp revertOp : Operation.POp}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hd0 : decode code ⟨0⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)))
    (hd2 : decode code ⟨2⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hd4 : decode code ⟨4⟩ = some (.MSTORE, .none))
    (hd5 : decode code ⟨5⟩ = some (.CALLVALUE, .none))
    (hd6 : decode code ⟨6⟩ = some (.DUP1, .none))
    (hd7 : decode code ⟨7⟩ = some (.ISZERO, .none))
    (hguardOp : guardOp ≠ .PUSH0)
    (hguardPush : decode code ⟨8⟩ = some (.Push guardOp, some (guardTgt, guardWidth)))
    (hguardJumpi : decode code (⟨8⟩ + UInt256.ofNat guardWidth.succ) = some (.JUMPI, .none))
    (hguardDest : decode code guardTgt = some (.JUMPDEST, .none))
    (hguardPop : decode code (guardTgt + ⟨1⟩) = some (.POP, .none))
    (hguardJd : (D_J code 0).contains guardTgt = true)
    (hbody : guardTgt + ⟨1⟩ + ⟨1⟩ = bodyPc)
    (hcdPush4 : decode code bodyPc = some (.Push .PUSH1, some (⟨4⟩, 1)))
    (hcdSize : decode code (bodyPc + UInt256.ofNat 2) = some (.CALLDATASIZE, .none))
    (hcdLt : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩) = some (.LT, .none))
    (hrevertOp : revertOp ≠ .PUSH0)
    (hrevertPush : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩)
        = some (.Push revertOp, some (revertTgt, revertWidth)))
    (hcdJumpi : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat revertWidth.succ)
        = some (.JUMPI, .none))
    (hload : bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat revertWidth.succ + ⟨1⟩ = loadPc)
    (hselPush0 : decode code loadPc = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hselLoad : decode code (loadPc + UInt256.ofNat 2) = some (.CALLDATALOAD, .none))
    (hselPush224 : decode code (loadPc + UInt256.ofNat 2 + ⟨1⟩)
        = some (.Push .PUSH1, some (⟨224⟩, 1)))
    (hselShr : decode code (loadPc + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2) = some (.SHR, .none))
    (hfirst : loadPc + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ = firstPc) :
    ∃ k C, Run code (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      ⟨firstPc, [solcSelectorWord I], solcFreePtrMem, UInt256.ofNat 3, ByteArray.empty,
        ⟨cA, σ, A.logSeries⟩⟩ k C := by
  have h0 := Run.solcGuardPrologue (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode hd0 hd2 hd4 hd5 hd6 hd7
  obtain ⟨_, _, h1⟩ := Run.solcGuardCallvalueZero
    (ctgt := guardTgt) (opC := guardOp) (wC := guardWidth)
    h0 hwv hguardOp hguardPush hguardJumpi hguardDest hguardPop hguardJd
  rw [hbody] at h1
  obtain ⟨_, _, h2⟩ := Run.solcCalldataOk
    (selLoadTgt := revertTgt) (opR := revertOp) (wR := revertWidth)
    h1 hsz hsize hcdPush4 hcdSize hcdLt hrevertOp hrevertPush hcdJumpi
  rw [hload] at h2
  obtain ⟨k3, C3, h3⟩ :=
    Run.solcLegacySelectorLoad h2 hselPush0 hselLoad hselPush224 hselShr (by simp)
  rw [hfirst] at h3
  exact ⟨k3, C3, h3⟩

/-- **Standard dispatcher reach**: prefix plus the linear `EQ` chain to the matched body. -/
theorem Run.solcDispatchReachBody {cA gh bl σ σ₀ A I} {g : Sat256} {firstArmPc bodyPC : UInt256}
    {i : ℕ}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hprefix : solcDispatchPrefixWellFormed code firstArmPc)
    (hguardJd : (D_J code 0).contains (solcGuardTgt code) = true)
    (hwf : ∀ j, j ≤ i → armWellFormed code (nthArmPc code firstArmPc j))
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat code (nthArmPc code firstArmPc j)) (solcSelectorWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat code (nthArmPc code firstArmPc i)) (solcSelectorWord I) ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains bodyPC = true)
    (hbody : armTgt code (nthArmPc code firstArmPc i) = bodyPC) :
    ∃ k C, Run code (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      ⟨bodyPC, [solcSelectorWord I], solcFreePtrMem, UInt256.ofNat 3, ByteArray.empty,
        ⟨cA, σ, A.logSeries⟩⟩ k C := by
  obtain ⟨_, _, h3⟩ := Run.solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hprefix hguardJd
  exact Run.dispatchTo bodyPC i h3 hwf heq0 htake (by rw [hbody]; exact hjd) hbody (by simp)

/-- One-level binary dispatch, **fall-through/high** half. -/
theorem Run.solcBinaryDispatchReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {splitPc bodyPC : UInt256} {i : ℕ}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hprefix : solcDispatchPrefixWellFormed code splitPc)
    (hguardJd : (D_J code 0).contains (solcGuardTgt code) = true)
    (hsplit : selectorSplitWellFormed code splitPc)
    (hpivot : UInt256.gt (armSelNat code splitPc) (solcSelectorWord I) = ⟨0⟩)
    (hwf : ∀ j, j ≤ i →
      armWellFormed code (nthArmPc code (selArmNextPc splitPc (armTgtWidth code splitPc)) j))
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat code (nthArmPc code (selArmNextPc splitPc (armTgtWidth code splitPc)) j))
        (solcSelectorWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat code (nthArmPc code (selArmNextPc splitPc (armTgtWidth code splitPc)) i))
        (solcSelectorWord I) ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains bodyPC = true)
    (hbody : armTgt code (nthArmPc code (selArmNextPc splitPc (armTgtWidth code splitPc)) i)
        = bodyPC) :
    ∃ k C, Run code (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      ⟨bodyPC, [solcSelectorWord I], solcFreePtrMem, UInt256.ofNat 3, ByteArray.empty,
        ⟨cA, σ, A.logSeries⟩⟩ k C := by
  obtain ⟨_, _, hsplitPc⟩ := Run.solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hprefix hguardJd
  have hfirst := hsplitPc.selectorSplitNotTakenAuto hsplit hpivot (by simp)
  exact Run.dispatchTo bodyPC i hfirst hwf heq0 htake (by rw [hbody]; exact hjd) hbody (by simp)

/-- One-level binary dispatch, **taken/low** half. -/
theorem Run.solcBinaryDispatchReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {splitPc bodyPC : UInt256} {i : ℕ}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hprefix : solcDispatchPrefixWellFormed code splitPc)
    (hguardJd : (D_J code 0).contains (solcGuardTgt code) = true)
    (hsplit : selectorSplitWellFormed code splitPc)
    (hpivot : UInt256.gt (armSelNat code splitPc) (solcSelectorWord I) ≠ ⟨0⟩)
    (hsplitJd : (D_J code 0).contains (armTgt code splitPc) = true)
    (hlowJumpdest : decode code (armTgt code splitPc) = some (.JUMPDEST, .none))
    (hwf : ∀ j, j ≤ i → armWellFormed code (nthArmPc code (armTgt code splitPc + ⟨1⟩) j))
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat code (nthArmPc code (armTgt code splitPc + ⟨1⟩) j))
        (solcSelectorWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat code (nthArmPc code (armTgt code splitPc + ⟨1⟩) i))
        (solcSelectorWord I) ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains bodyPC = true)
    (hbody : armTgt code (nthArmPc code (armTgt code splitPc + ⟨1⟩) i) = bodyPC) :
    ∃ k C, Run code (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      ⟨bodyPC, [solcSelectorWord I], solcFreePtrMem, UInt256.ofNat 3, ByteArray.empty,
        ⟨cA, σ, A.logSeries⟩⟩ k C := by
  obtain ⟨_, _, hsplitPc⟩ := Run.solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hprefix hguardJd
  have hfirst := (hsplitPc.selectorSplitTakenAuto hsplit hpivot hsplitJd (by simp)).jumpdest
    hlowJumpdest (by simp)
  exact Run.dispatchTo bodyPC i hfirst hwf heq0 htake (by rw [hbody]; exact hjd) hbody (by simp)

/-! ## External-function argument decoders

The ABI decoder prologue of an external function with static arguments: the calldata length
check (`PUSH2 ret; PUSH1 4; DUP1; CALLDATASIZE; SUB; PUSH1 need; DUP2; LT; ISZERO; PUSH2 decoded;
JUMPI`, falling into `PUSH1 0; DUP1; REVERT` when short), then the per-argument loads with the
160-bit address mask.  The address-mask literal solc builds inline is `solcAddrMask`. -/

theorem solcAddrMask_lit :
    UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide

@[reducible] def solcStaticArgsLenCheckWf (code : ByteArray) (entry ret need decoded : UInt256) :
    Prop :=
  let p1 := entry + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p17 := p14 + UInt256.ofNat 3
  decode code entry = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH2, some (ret, 2))
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p6 = some (.DUP1, .none)
  ∧ decode code p7 = some (.CALLDATASIZE, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.Push .PUSH1, some (need, 1))
  ∧ decode code p11 = some (.DUP2, .none)
  ∧ decode code p12 = some (.LT, .none)
  ∧ decode code p13 = some (.ISZERO, .none)
  ∧ decode code p14 = some (.Push .PUSH2, some (decoded, 2))
  ∧ decode code p17 = some (.JUMPI, .none)

/-- The `PUSH1 0; DUP1; REVERT` the length check falls into. -/
@[reducible] def solcStaticArgsLenRevertPc (entry : UInt256) : UInt256 :=
  entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩
    + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩

/-- Length check passed (`calldatasize - 4 ≥ need`): reach `decoded` with
    `[calldatasize - 4, 4, ret]` pushed. -/
theorem Run.solcExternalStaticArgsLenOk {entry ret need decoded : UInt256}
    (h : Run code s0 ⟨entry, R, mem, aw, rdata, w⟩ k C)
    (hwf : solcStaticArgsLenCheckWf code entry ret need decoded)
    (hdecoded : (D_J code 0).contains decoded = true)
    (hlt : UInt256.lt (UInt256.sub (UInt256.ofNat s0.executionEnv.calldata.size) ⟨4⟩) need = ⟨0⟩)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨decoded,
      UInt256.sub (UInt256.ofNat s0.executionEnv.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: R,
      mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17⟩
  have hcond : UInt256.isZero
      (UInt256.lt (UInt256.sub (UInt256.ofNat s0.executionEnv.calldata.size) ⟨4⟩) need) ≠ ⟨0⟩ := by
    rw [hlt]; decide
  have h14 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push2 ret hd1 (by evm_ov),
    raw push1 ⟨4⟩ hd4 (by evm_ov),
    raw dup1 hd6 (by evm_ov),
    raw calldatasize hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw push1 need hd9 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw lt hd12 (by evm_ov),
    raw iszero hd13 (by evm_ov),
    raw push2 decoded hd14 (by evm_ov)]
  exact ⟨_, _, h14.jumpiT hd17 hcond hdecoded (by evm_ov)⟩

/-- One static argument (`need = 32`): `36 ≤ calldatasize`. -/
theorem Run.solcOneAddressExternalLenOk {entry ret decoded : UInt256}
    (h : Run code s0 ⟨entry, R, mem, aw, rdata, w⟩ k C)
    (hwf : solcStaticArgsLenCheckWf code entry ret ⟨32⟩ decoded)
    (hdecoded : (D_J code 0).contains decoded = true)
    (hsz36 : 36 ≤ s0.executionEnv.calldata.size)
    (hsize : s0.executionEnv.calldata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨decoded,
      UInt256.sub (UInt256.ofNat s0.executionEnv.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: R,
      mem, aw, rdata, w⟩ k' C' :=
  Run.solcExternalStaticArgsLenOk h hwf hdecoded
    (solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize) hov

/-- Two static arguments (`need = 64`): `68 ≤ calldatasize`. -/
theorem Run.solcTwoAddressExternalLenOk {entry ret decoded : UInt256}
    (h : Run code s0 ⟨entry, R, mem, aw, rdata, w⟩ k C)
    (hwf : solcStaticArgsLenCheckWf code entry ret ⟨64⟩ decoded)
    (hdecoded : (D_J code 0).contains decoded = true)
    (hsz68 : 68 ≤ s0.executionEnv.calldata.size)
    (hsize : s0.executionEnv.calldata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨decoded,
      UInt256.sub (UInt256.ofNat s0.executionEnv.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: R,
      mem, aw, rdata, w⟩ k' C' :=
  Run.solcExternalStaticArgsLenOk h hwf hdecoded
    (solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize) hov

/-- Length check failed (`calldatasize - 4 < need`): the run reverts with empty data. -/
theorem Run.solcExternalStaticArgsShortReverts {entry ret need decoded : UInt256}
    (h : Run code s0 ⟨entry, R, mem, aw, rdata, w⟩ k C)
    (hwf : solcStaticArgsLenCheckWf code entry ret need decoded)
    (hr0 : decode code (solcStaticArgsLenRevertPc entry) = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hr1 : decode code (solcStaticArgsLenRevertPc entry + UInt256.ofNat 2) = some (.DUP1, .none))
    (hr2 : decode code (solcStaticArgsLenRevertPc entry + UInt256.ofNat 2 + ⟨1⟩)
        = some (.REVERT, .none))
    (hlt : UInt256.lt (UInt256.sub (UInt256.ofNat s0.executionEnv.calldata.size) ⟨4⟩) need = ⟨1⟩)
    (hov : R.length + 5 ≤ 1024) :
    Reverted code s0 ByteArray.empty := by
  rcases hwf with ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17⟩
  have h13 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push2 ret hd1 (by evm_ov),
    raw push1 ⟨4⟩ hd4 (by evm_ov),
    raw dup1 hd6 (by evm_ov),
    raw calldatasize hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw push1 need hd9 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw lt hd12 (by evm_ov)]
  rw [hlt] at h13
  have h14 := h13.iszero hd13 (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h14
  exact ((h14.push2 decoded hd14 (by evm_ov)).jumpiNT hd17 rfl (by evm_ov)).solcPush1Dup1Revert0
    hr0 hr1 hr2 (by evm_ov)

/-- `JUMPDEST; POP; CALLDATALOAD; PUSH1 1; PUSH1 1; PUSH1 160; SHL; SUB; AND; PUSH2 routine;
    JUMP`: load and mask one address argument, then jump to the body. -/
@[reducible] def solcOneAddressExternalDecodeWf (code : ByteArray) (decoded routine : UInt256) :
    Prop :=
  let p1 := decoded + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p9 := p7 + UInt256.ofNat 2
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p15 := p12 + UInt256.ofNat 3
  decode code decoded = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.POP, .none)
  ∧ decode code p2 = some (.CALLDATALOAD, .none)
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p7 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p9 = some (.SHL, .none)
  ∧ decode code p10 = some (.SUB, .none)
  ∧ decode code p11 = some (.AND, .none)
  ∧ decode code p12 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p15 = some (.JUMP, .none)

theorem Run.solcOneAddressExternalMaskAndJumpMasked {decoded ret routine de : UInt256}
    (h : Run code s0 ⟨decoded, de :: ⟨4⟩ :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcOneAddressExternalDecodeWf code decoded routine)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨routine,
      UInt256.land solcAddrMask (calldataWord s0.executionEnv.calldata 4) :: ret :: R,
      mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd3, hd5, hd7, hd9, hd10, hd11, hd12, hd15⟩
  have h15 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw pop hd1 (by evm_ov),
    raw calldataload hd2 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨1⟩ hd5 (by evm_ov),
    raw push1 ⟨160⟩ hd7 (by evm_ov),
    raw shl hd9 (by evm_ov),
    raw sub hd10 (by evm_ov),
    raw and hd11 (by evm_ov),
    raw push2 routine hd12 (by evm_ov)]
  rw [solcAddrMask_lit] at h15
  exact ⟨_, _, h15.jump hd15 hroutine (by evm_ov)⟩

theorem Run.solcOneAddressExternalMaskAndJump {decoded ret routine de : UInt256}
    (h : Run code s0 ⟨decoded, de :: ⟨4⟩ :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcOneAddressExternalDecodeWf code decoded routine)
    (hcanon : (calldataWord s0.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨routine, calldataWord s0.executionEnv.calldata 4 :: ret :: R,
      mem, aw, rdata, w⟩ k' C' := by
  obtain ⟨k', C', h'⟩ := Run.solcOneAddressExternalMaskAndJumpMasked h hwf hroutine hov
  rw [solcAddrMask_clean_left hcanon] at h'
  exact ⟨k', C', h'⟩

/-- Two arguments `(address, address)`: mask both, jump to the body with `[a2, a1, ret]`. -/
@[reducible] def solcTwoAddressExternalDecodeWf (code : ByteArray) (decoded routine : UInt256) :
    Prop :=
  let p1 := decoded + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p6 := p4 + UInt256.ofNat 2
  let p8 := p6 + UInt256.ofNat 2
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p23 := p20 + UInt256.ofNat 3
  decode code decoded = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.POP, .none)
  ∧ decode code p2 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p8 = some (.SHL, .none)
  ∧ decode code p9 = some (.SUB, .none)
  ∧ decode code p10 = some (.DUP2, .none)
  ∧ decode code p11 = some (.CALLDATALOAD, .none)
  ∧ decode code p12 = some (.DUP2, .none)
  ∧ decode code p13 = some (.AND, .none)
  ∧ decode code p14 = some (.SWAP2, .none)
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p17 = some (.ADD, .none)
  ∧ decode code p18 = some (.CALLDATALOAD, .none)
  ∧ decode code p19 = some (.AND, .none)
  ∧ decode code p20 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p23 = some (.JUMP, .none)

theorem Run.solcTwoAddressExternalMaskAndJumpMasked {decoded ret routine de : UInt256}
    (h : Run code s0 ⟨decoded, de :: ⟨4⟩ :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcTwoAddressExternalDecodeWf code decoded routine)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨routine,
      UInt256.land (calldataWord s0.executionEnv.calldata 36) solcAddrMask ::
        UInt256.land solcAddrMask (calldataWord s0.executionEnv.calldata 4) :: ret :: R,
      mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd4, hd6, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15, hd17,
    hd18, hd19, hd20, hd23⟩
  have h23 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw pop hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd2 (by evm_ov),
    raw push1 ⟨1⟩ hd4 (by evm_ov),
    raw push1 ⟨160⟩ hd6 (by evm_ov),
    raw shl hd8 (by evm_ov),
    raw sub hd9 (by evm_ov),
    raw dup2 hd10 (by evm_ov),
    raw calldataload hd11 (by evm_ov),
    raw dup2 hd12 (by evm_ov),
    raw and hd13 (by evm_ov),
    raw swap2 hd14 (by evm_ov),
    raw push1 ⟨32⟩ hd15 (by evm_ov),
    raw add hd17 (by evm_ov),
    raw calldataload hd18 (by evm_ov),
    raw and hd19 (by evm_ov),
    raw push2 routine hd20 (by evm_ov)]
  rw [solcAddrMask_lit] at h23
  exact ⟨_, _, h23.jump hd23 hroutine (by evm_ov)⟩

theorem Run.solcTwoAddressExternalMaskAndJump {decoded ret routine de : UInt256}
    (h : Run code s0 ⟨decoded, de :: ⟨4⟩ :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcTwoAddressExternalDecodeWf code decoded routine)
    (hcanon0 : (calldataWord s0.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord s0.executionEnv.calldata 36).toNat < EVM.addressModulus)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨routine,
      calldataWord s0.executionEnv.calldata 36 :: calldataWord s0.executionEnv.calldata 4 :: ret :: R,
      mem, aw, rdata, w⟩ k' C' := by
  obtain ⟨k', C', h'⟩ := Run.solcTwoAddressExternalMaskAndJumpMasked h hwf hroutine hov
  rw [solcAddrMask_clean_left hcanon0, solcAddrMask_clean hcanon1] at h'
  exact ⟨k', C', h'⟩

/-- Two arguments `(address, uint256)`: mask the address, jump with `[u, a, ret]`. -/
@[reducible] def solcAddressUint256ExternalDecodeWf (code : ByteArray) (decoded routine : UInt256) :
    Prop :=
  let p1 := decoded + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p6 := p4 + UInt256.ofNat 2
  let p8 := p6 + UInt256.ofNat 2
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p16 := p14 + UInt256.ofNat 2
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p21 := p18 + UInt256.ofNat 3
  decode code decoded = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.POP, .none)
  ∧ decode code p2 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p8 = some (.SHL, .none)
  ∧ decode code p9 = some (.SUB, .none)
  ∧ decode code p10 = some (.DUP2, .none)
  ∧ decode code p11 = some (.CALLDATALOAD, .none)
  ∧ decode code p12 = some (.AND, .none)
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p16 = some (.ADD, .none)
  ∧ decode code p17 = some (.CALLDATALOAD, .none)
  ∧ decode code p18 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p21 = some (.JUMP, .none)

theorem Run.solcAddressUint256ExternalMaskAndJumpMasked {decoded ret routine de : UInt256}
    (h : Run code s0 ⟨decoded, de :: ⟨4⟩ :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcAddressUint256ExternalDecodeWf code decoded routine)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨routine,
      calldataWord s0.executionEnv.calldata 36 ::
        UInt256.land (calldataWord s0.executionEnv.calldata 4) solcAddrMask :: ret :: R,
      mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd4, hd6, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd16, hd17,
    hd18, hd21⟩
  have h21 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw pop hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd2 (by evm_ov),
    raw push1 ⟨1⟩ hd4 (by evm_ov),
    raw push1 ⟨160⟩ hd6 (by evm_ov),
    raw shl hd8 (by evm_ov),
    raw sub hd9 (by evm_ov),
    raw dup2 hd10 (by evm_ov),
    raw calldataload hd11 (by evm_ov),
    raw and hd12 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw push1 ⟨32⟩ hd14 (by evm_ov),
    raw add hd16 (by evm_ov),
    raw calldataload hd17 (by evm_ov),
    raw push2 routine hd18 (by evm_ov)]
  rw [solcAddrMask_lit] at h21
  exact ⟨_, _, h21.jump hd21 hroutine (by evm_ov)⟩

theorem Run.solcAddressUint256ExternalMaskAndJump {decoded ret routine de : UInt256}
    (h : Run code s0 ⟨decoded, de :: ⟨4⟩ :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcAddressUint256ExternalDecodeWf code decoded routine)
    (hcanon : (calldataWord s0.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨routine,
      calldataWord s0.executionEnv.calldata 36 :: calldataWord s0.executionEnv.calldata 4 :: ret :: R,
      mem, aw, rdata, w⟩ k' C' := by
  obtain ⟨k', C', h'⟩ := Run.solcAddressUint256ExternalMaskAndJumpMasked h hwf hroutine hov
  rw [solcAddrMask_clean hcanon] at h'
  exact ⟨k', C', h'⟩

/-- Three arguments `(address, address, uint256)`: mask both addresses, jump with
    `[u, a2, a1, ret]`. -/
@[reducible] def solcAddressAddressUint256ExternalDecodeWf (code : ByteArray)
    (decoded routine : UInt256) : Prop :=
  let p1 := decoded + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p6 := p4 + UInt256.ofNat 2
  let p8 := p6 + UInt256.ofNat 2
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p31 := p28 + UInt256.ofNat 3
  decode code decoded = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.POP, .none)
  ∧ decode code p2 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p8 = some (.SHL, .none)
  ∧ decode code p9 = some (.SUB, .none)
  ∧ decode code p10 = some (.DUP2, .none)
  ∧ decode code p11 = some (.CALLDATALOAD, .none)
  ∧ decode code p12 = some (.DUP2, .none)
  ∧ decode code p13 = some (.AND, .none)
  ∧ decode code p14 = some (.SWAP2, .none)
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p17 = some (.DUP2, .none)
  ∧ decode code p18 = some (.ADD, .none)
  ∧ decode code p19 = some (.CALLDATALOAD, .none)
  ∧ decode code p20 = some (.SWAP1, .none)
  ∧ decode code p21 = some (.SWAP2, .none)
  ∧ decode code p22 = some (.AND, .none)
  ∧ decode code p23 = some (.SWAP1, .none)
  ∧ decode code p24 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p26 = some (.ADD, .none)
  ∧ decode code p27 = some (.CALLDATALOAD, .none)
  ∧ decode code p28 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p31 = some (.JUMP, .none)

theorem Run.solcAddressAddressUint256ExternalMaskAndJumpMasked {decoded ret routine de : UInt256}
    (h : Run code s0 ⟨decoded, de :: ⟨4⟩ :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcAddressAddressUint256ExternalDecodeWf code decoded routine)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨routine,
      calldataWord s0.executionEnv.calldata 68 ::
        UInt256.land solcAddrMask (calldataWord s0.executionEnv.calldata 36) ::
        UInt256.land solcAddrMask (calldataWord s0.executionEnv.calldata 4) :: ret :: R,
      mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd4, hd6, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15, hd17,
    hd18, hd19, hd20, hd21, hd22, hd23, hd24, hd26, hd27, hd28, hd31⟩
  have h31 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw pop hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd2 (by evm_ov),
    raw push1 ⟨1⟩ hd4 (by evm_ov),
    raw push1 ⟨160⟩ hd6 (by evm_ov),
    raw shl hd8 (by evm_ov),
    raw sub hd9 (by evm_ov),
    raw dup2 hd10 (by evm_ov),
    raw calldataload hd11 (by evm_ov),
    raw dup2 hd12 (by evm_ov),
    raw and hd13 (by evm_ov),
    raw swap2 hd14 (by evm_ov),
    raw push1 ⟨32⟩ hd15 (by evm_ov),
    raw dup2 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw calldataload hd19 (by evm_ov),
    raw swap1 hd20 (by evm_ov),
    raw swap2 hd21 (by evm_ov),
    raw and hd22 (by evm_ov),
    raw swap1 hd23 (by evm_ov),
    raw push1 ⟨64⟩ hd24 (by evm_ov),
    raw add hd26 (by evm_ov),
    raw calldataload hd27 (by evm_ov),
    raw push2 routine hd28 (by evm_ov)]
  rw [solcAddrMask_lit] at h31
  exact ⟨_, _, h31.jump hd31 hroutine (by evm_ov)⟩

theorem Run.solcAddressAddressUint256ExternalMaskAndJump {decoded ret routine de : UInt256}
    (h : Run code s0 ⟨decoded, de :: ⟨4⟩ :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcAddressAddressUint256ExternalDecodeWf code decoded routine)
    (hcanon0 : (calldataWord s0.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord s0.executionEnv.calldata 36).toNat < EVM.addressModulus)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨routine,
      calldataWord s0.executionEnv.calldata 68 :: calldataWord s0.executionEnv.calldata 36 ::
        calldataWord s0.executionEnv.calldata 4 :: ret :: R,
      mem, aw, rdata, w⟩ k' C' := by
  obtain ⟨k', C', h'⟩ := Run.solcAddressAddressUint256ExternalMaskAndJumpMasked h hwf hroutine hov
  rw [solcAddrMask_clean_left hcanon0, solcAddrMask_clean_left hcanon1] at h'
  exact ⟨k', C', h'⟩

/-! ## Inlined address decoder

`JUMPDEST; DUP1; CALLDATALOAD; PUSH1 1; PUSH1 1; PUSH1 160; SHL; SUB; DUP2; AND; DUP2; EQ;
PUSH2 ok; JUMPI; PUSH0; PUSH0; REVERT; JUMPDEST; SWAP2; SWAP1; POP; JUMP`. -/

theorem Run.solcInlinedDecodeAddrOk {off ret : UInt256}
    (h : Run code s0 ⟨pc, off :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hcanon : (uInt256OfByteArray (s0.executionEnv.calldata.readBytes off.toNat 32)).toNat
        < EVM.addressModulus)
    (hret : (D_J code 0).contains ret = true)
    (hd0 : decode code pc = some (.JUMPDEST, .none))
    (hd1 : decode code (solcInlinedDecodeAddrPc1 pc) = some (.DUP1, .none))
    (hd2 : decode code (solcInlinedDecodeAddrPc2 pc) = some (.CALLDATALOAD, .none))
    (hd3 : decode code (solcInlinedDecodeAddrPc3 pc) = some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd5 : decode code (solcInlinedDecodeAddrPc5 pc) = some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd7 : decode code (solcInlinedDecodeAddrPc7 pc) = some (.Push .PUSH1, some (⟨160⟩, 1)))
    (hd9 : decode code (solcInlinedDecodeAddrPc9 pc) = some (.SHL, .none))
    (hd10 : decode code (solcInlinedDecodeAddrPc10 pc) = some (.SUB, .none))
    (hd11 : decode code (solcInlinedDecodeAddrPc11 pc) = some (.DUP2, .none))
    (hd12 : decode code (solcInlinedDecodeAddrPc12 pc) = some (.AND, .none))
    (hd13 : decode code (solcInlinedDecodeAddrPc13 pc) = some (.DUP2, .none))
    (hd14 : decode code (solcInlinedDecodeAddrPc14 pc) = some (.EQ, .none))
    (hd15 : decode code (solcInlinedDecodeAddrPc15 pc)
        = some (.Push .PUSH2, some (solcInlinedDecodeAddrPc22 pc, 2)))
    (hd18 : decode code (solcInlinedDecodeAddrPc18 pc) = some (.JUMPI, .none))
    (hd22 : decode code (solcInlinedDecodeAddrPc22 pc) = some (.JUMPDEST, .none))
    (hjd22 : (D_J code 0).contains (solcInlinedDecodeAddrPc22 pc) = true)
    (hd23 : decode code (solcInlinedDecodeAddrPc23 pc) = some (.SWAP2, .none))
    (hd24 : decode code (solcInlinedDecodeAddrPc24 pc) = some (.SWAP1, .none))
    (hd25 : decode code (solcInlinedDecodeAddrPc25 pc) = some (.POP, .none))
    (hd26 : decode code (solcInlinedDecodeAddrPc26 pc) = some (.JUMP, .none))
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret,
      uInt256OfByteArray (s0.executionEnv.calldata.readBytes off.toNat 32) :: R,
      mem, aw, rdata, w⟩ k' C' := by
  have hb : UInt256.eq (uInt256OfByteArray (s0.executionEnv.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (s0.executionEnv.calldata.readBytes off.toNat 32))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) ≠ ⟨0⟩ := by
    rw [solcAddrMask_lit, solcAddrCanon_eq hcanon]
    decide
  exact ⟨_, _, h.jumpdest hd0 (by evm_ov)
    |>.dup1 hd1 (by evm_ov)
    |>.calldataload hd2 (by evm_ov)
    |>.push1 ⟨1⟩ hd3 (by evm_ov)
    |>.push1 ⟨1⟩ hd5 (by evm_ov)
    |>.push1 ⟨160⟩ hd7 (by evm_ov)
    |>.shl hd9 (by evm_ov)
    |>.sub hd10 (by evm_ov)
    |>.dup2 hd11 (by evm_ov)
    |>.and hd12 (by evm_ov)
    |>.dup2 hd13 (by evm_ov)
    |>.eq hd14 (by evm_ov)
    |>.push2 (solcInlinedDecodeAddrPc22 pc) hd15 (by evm_ov)
    |>.jumpiT hd18 hb hjd22 (by evm_ov)
    |>.jumpdest hd22 (by evm_ov)
    |>.swap2 hd23 (by evm_ov)
    |>.swap1 hd24 (by evm_ov)
    |>.pop hd25 (by evm_ov)
    |>.jump hd26 hret (by evm_ov)⟩

theorem Run.solcInlinedDecodeAddrRevert {off ret : UInt256}
    (h : Run code s0 ⟨pc, off :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hnc : UInt256.eq (uInt256OfByteArray (s0.executionEnv.calldata.readBytes off.toNat 32))
        (UInt256.land (uInt256OfByteArray (s0.executionEnv.calldata.readBytes off.toNat 32))
          solcAddrMask) = ⟨0⟩)
    (hd0 : decode code pc = some (.JUMPDEST, .none))
    (hd1 : decode code (solcInlinedDecodeAddrPc1 pc) = some (.DUP1, .none))
    (hd2 : decode code (solcInlinedDecodeAddrPc2 pc) = some (.CALLDATALOAD, .none))
    (hd3 : decode code (solcInlinedDecodeAddrPc3 pc) = some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd5 : decode code (solcInlinedDecodeAddrPc5 pc) = some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd7 : decode code (solcInlinedDecodeAddrPc7 pc) = some (.Push .PUSH1, some (⟨160⟩, 1)))
    (hd9 : decode code (solcInlinedDecodeAddrPc9 pc) = some (.SHL, .none))
    (hd10 : decode code (solcInlinedDecodeAddrPc10 pc) = some (.SUB, .none))
    (hd11 : decode code (solcInlinedDecodeAddrPc11 pc) = some (.DUP2, .none))
    (hd12 : decode code (solcInlinedDecodeAddrPc12 pc) = some (.AND, .none))
    (hd13 : decode code (solcInlinedDecodeAddrPc13 pc) = some (.DUP2, .none))
    (hd14 : decode code (solcInlinedDecodeAddrPc14 pc) = some (.EQ, .none))
    (hd15 : decode code (solcInlinedDecodeAddrPc15 pc)
        = some (.Push .PUSH2, some (solcInlinedDecodeAddrPc22 pc, 2)))
    (hd18 : decode code (solcInlinedDecodeAddrPc18 pc) = some (.JUMPI, .none))
    (hr0 : decode code (solcInlinedDecodeAddrPc19 pc) = some (.PUSH0, .none))
    (hr1 : decode code (solcInlinedDecodeAddrPc19 pc + ⟨1⟩) = some (.PUSH0, .none))
    (hr2 : decode code (solcInlinedDecodeAddrPc19 pc + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none))
    (hov : R.length + 6 ≤ 1024) :
    Reverted code s0 ByteArray.empty := by
  have hb : UInt256.eq (uInt256OfByteArray (s0.executionEnv.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (s0.executionEnv.calldata.readBytes off.toNat 32))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨0⟩ := by
    rw [solcAddrMask_lit]; exact hnc
  exact (h.jumpdest hd0 (by evm_ov)
    |>.dup1 hd1 (by evm_ov)
    |>.calldataload hd2 (by evm_ov)
    |>.push1 ⟨1⟩ hd3 (by evm_ov)
    |>.push1 ⟨1⟩ hd5 (by evm_ov)
    |>.push1 ⟨160⟩ hd7 (by evm_ov)
    |>.shl hd9 (by evm_ov)
    |>.sub hd10 (by evm_ov)
    |>.dup2 hd11 (by evm_ov)
    |>.and hd12 (by evm_ov)
    |>.dup2 hd13 (by evm_ov)
    |>.eq hd14 (by evm_ov)
    |>.push2 (solcInlinedDecodeAddrPc22 pc) hd15 (by evm_ov)
    |>.jumpiNT hd18 hb (by evm_ov)).revertStub hr0 hr1 hr2 (by evm_ov)

/-! ## Internal-call thunks -/

/-- `JUMPDEST; PUSH1 0; PUSH2 cont; CALLER; DUP5; DUP5; PUSH2 routine; JUMP`: enter a
    `_transfer(msg.sender, to, value)`-style routine with the caller as first argument. -/
theorem Run.solcCallerTransferThunk {contPc routinePc value toWord ret : UInt256}
    (h : Run code s0 ⟨pc, value :: toWord :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcCallerTransferThunkWf code pc contPc routinePc)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨routinePc,
      value :: toWord :: solcSourceWord s0.executionEnv :: contPc :: ⟨0⟩ :: value :: toWord ::
        ret :: R, mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd6, hd7, hd8, hd9, hd12⟩
  have h12 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨0⟩ hd1 (by evm_ov),
    raw push2 contPc hd3 (by evm_ov),
    raw caller hd6 (by evm_ov),
    raw dup5 hd7 (by evm_ov),
    raw dup5 hd8 (by evm_ov),
    raw push2 routinePc hd9 (by evm_ov)]
  exact ⟨_, _, h12.jump hd12 hroutine (by evm_ov)⟩

/-- `JUMPDEST; PUSH2 cont; DUP5; DUP5; DUP5; PUSH2 routine; JUMP`: enter a three-argument
    internal routine. -/
theorem Run.solcInternalCallSetup3 {contPc routinePc discard a b c ret : UInt256}
    (h : Run code s0 ⟨pc, discard :: a :: b :: c :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcInternalCallSetup3Wf code pc contPc routinePc)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨routinePc,
      a :: b :: c :: contPc :: discard :: a :: b :: c :: ret :: R, mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd4, hd5, hd6, hd7, hd10⟩
  have h10 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push2 contPc hd1 (by evm_ov),
    raw dup5 hd4 (by evm_ov),
    raw dup5 hd5 (by evm_ov),
    raw dup5 hd6 (by evm_ov),
    raw push2 routinePc hd7 (by evm_ov)]
  exact ⟨_, _, h10.jump hd10 hroutine (by evm_ov)⟩

/-! ## Getter thunks and simple getter routines -/

/-- `JUMPDEST; PUSH2 returnPc; PUSH2 routine; JUMP`. -/
theorem Run.solcGetterThunk {entry returnPc routine : UInt256}
    (h : Run code s0 ⟨entry, R, mem, aw, rdata, w⟩ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨routine, returnPc :: R, mem, aw, rdata, w⟩ k' C' := by
  rcases hentry with ⟨hd0, hd1, hd4, hd7⟩
  exact ⟨_, _, h.jumpdest hd0 (by evm_ov)
    |>.push2 returnPc hd1 (by evm_ov)
    |>.push2 routine hd4 (by evm_ov)
    |>.jump hd7 hroutine (by evm_ov)⟩

/-- Address getter routine: `SLOAD slot`, mask, return to `ret`. -/
theorem Run.solcAddressSlotGetter {slot ret : UInt256}
    (h : Run code s0 ⟨pc, ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcAddressSlotGetterWf code pc slot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret,
      UInt256.land solcAddrMask (solcSlotWord w.accounts s0.executionEnv slot) :: ret :: R,
      mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10⟩
  have h3 := h.jumpdest hd0 (by evm_ov) |>.push1 slot hd1 (by evm_ov)
  obtain ⟨_, _, h4⟩ := h3.sload hd2 (by evm_ov)
  have h13 := evm_run h4 with [
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨1⟩ hd4 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd6 (by evm_ov),
    raw sub hd7 (by evm_ov),
    raw and hd8 (by evm_ov),
    raw dup2 hd9 (by evm_ov)]
  rw [solcAddrMask_lit] at h13
  exact ⟨_, _, h13.jump hd10 hret (by evm_ov)⟩

/-- Word getter routine: `SLOAD slot`, return to `ret`. -/
theorem Run.solcWordSlotGetter {slot ret : UInt256}
    (h : Run code s0 ⟨pc, ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcWordSlotGetterWf code pc slot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret, solcSlotWord w.accounts s0.executionEnv slot :: ret :: R,
      mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd3, hd4⟩
  have h3 := h.jumpdest hd0 (by evm_ov) |>.push1 slot hd1 (by evm_ov)
  obtain ⟨_, _, h4⟩ := h3.sload hd2 (by evm_ov)
  exact ⟨_, _, h4.dup2 hd3 (by evm_ov) |>.jump hd4 hret (by evm_ov)⟩

/-- Constant getter routine: push `val`, return to `ret`. -/
theorem Run.solcConstGetter {val ret : UInt256} {width : ℕ} {op : Operation.POp}
    (h : Run code s0 ⟨pc, ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcConstGetterWf code pc val width op)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret, val :: ret :: R, mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hop, hd1, hdNext, hdJump⟩
  exact ⟨_, _, h.jumpdest hd0 (by evm_ov)
    |>.pushConst val (width := width) (op := op) hop hd1 (by evm_ov)
    |>.dup2 hdNext (by evm_ov)
    |>.jump hdJump hret (by evm_ov)⟩

/-! ## Mapping routines

Loads and stores through `keccak256(key ‖ baseSlot)` in scratch memory `[0, 64)`.  The memory
shapes (`wordAt0Mem`, `twoWordHashMem`, `solcMappingHashMem`, …) and the slot facts
(`solcMappingSlot`, `twoWordHashMem_solcMappingSlot`, …) come from `Solc.lean`. -/

set_option maxHeartbeats 1000000 in
theorem Run.solcSingleMappingLoadToRoutineMem
    {baseSlot afterLoadPc routinePc value aux key ret : UInt256}
    (h : Run code s0 ⟨pc, value :: aux :: key :: ret :: R, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcSingleMappingLoadToRoutineMemWf code pc baseSlot afterLoadPc routinePc)
    (hmem : mem.size = 96)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hroutineMask : UInt256.land routinePc ⟨0xffffffff⟩ = routinePc)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨routinePc,
      value :: solcSlotWord w.accounts s0.executionEnv (solcMappingSlot baseSlot key) ::
        afterLoadPc :: value :: aux :: key :: ret :: R,
      twoWordHashMem key baseSlot mem, UInt256.ofNat 3, rdata, w⟩ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd11, hd13, hd14, hd15, hd16,
      hd18, hd20, hd21, hd23, hd24, hd25, hd26, hd29, hd30, hd31, hd36, hd39, hd40⟩
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot key :=
    twoWordHashMem_solcMappingSlot baseSlot key hmem
  have hMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw dup4 hd9 (by evm_ov),
    raw and hd10 (by evm_ov)]
  rw [solcAddrMask_lit, solcAddrMask_clean hcanonKey] at hMasked
  have hMstore0Prefix := evm_run hMasked with [
    raw push1 ⟨0⟩ hd11 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw dup2 hd14 (by evm_ov)]
  have hAfterKey := hMstore0Prefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd15 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hMstoreSlotPrefix := evm_run hAfterKey with [
    raw push1 baseSlot hd16 (by evm_ov),
    raw push1 ⟨32⟩ hd18 (by evm_ov)]
  have hHashMem := hMstoreSlotPrefix.mstore 0 (twoWordHashMem key baseSlot mem)
    (UInt256.ofNat 3) hd20 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hKeccakPrefix := evm_run hHashMem with [
    raw push1 ⟨64⟩ hd21 (by evm_ov),
    raw swap1 hd23 (by evm_ov)]
  have hSlot := hKeccakPrefix.keccak256 0 (solcMappingSlot baseSlot key)
    (UInt256.ofNat 3) hd24 mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, hLoaded⟩ := hSlot.sload hd25 (by evm_ov)
  have hJump := evm_run hLoaded with [
    raw push2 afterLoadPc hd26 (by evm_ov),
    raw swap1 hd29 (by evm_ov),
    raw dup3 hd30 (by evm_ov),
    raw push4 ⟨0xffffffff⟩ hd31 (by evm_ov),
    raw push2 routinePc hd36 (by evm_ov),
    raw and hd39 (by evm_ov)]
  rw [hroutineMask] at hJump
  exact ⟨_, _, hJump.jump hd40 hroutine (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem Run.solcSingleMappingStoreDebitMem {baseSlot newValue value aux key ret : UInt256}
    (h : Run code s0 ⟨pc, newValue :: value :: aux :: key :: ret :: R,
      twoWordHashMem key baseSlot mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcSingleMappingStoreDebitMemWf code pc baseSlot)
    (hmem : mem.size = 96)
    (hperm : s0.executionEnv.perm = true)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨solcSingleMappingStoreDebitOutPc pc,
      ⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: aux :: key :: ret :: R,
      twoWordHashMem key baseSlot (twoWordHashMem key baseSlot mem), UInt256.ofNat 3, rdata,
      { w with
          accounts := sstoreAccountMap s0.executionEnv.codeOwner w.accounts
            (solcMappingSlot baseSlot key) newValue }⟩ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd11, hd12, hd14, hd15, hd16,
      hd17, hd19, hd21, hd22, hd24, hd25, hd26, hd27, hd28, hd29, hd30⟩
  have hbaseSize : (twoWordHashMem key baseSlot mem).size = 96 :=
    twoWordHashMem_size_96 key baseSlot hmem
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem key baseSlot
            (twoWordHashMem key baseSlot mem)).readWithPadding 0 64))) =
        solcMappingSlot baseSlot key :=
    twoWordHashMem_solcMappingSlot baseSlot key hbaseSize
  have hMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw dup1 hd9 (by evm_ov),
    raw dup6 hd10 (by evm_ov),
    raw and hd11 (by evm_ov)]
  rw [solcAddrMask_lit, solcAddrMask_clean hcanonKey] at hMasked
  have hMstore0Prefix := evm_run hMasked with [
    raw push1 ⟨0⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov),
    raw dup2 hd15 (by evm_ov)]
  have hAfterKey := hMstore0Prefix.mstore 0
    (wordAt0Mem key (twoWordHashMem key baseSlot mem))
    (UInt256.ofNat 3) hd16 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hMstoreSlotPrefix := evm_run hAfterKey with [
    raw push1 baseSlot hd17 (by evm_ov),
    raw push1 ⟨32⟩ hd19 (by evm_ov)]
  have hHashMem := hMstoreSlotPrefix.mstore 0
    (twoWordHashMem key baseSlot (twoWordHashMem key baseSlot mem))
    (UInt256.ofNat 3) hd21 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hKeccakPrefix := evm_run hHashMem with [
    raw push1 ⟨64⟩ hd22 (by evm_ov),
    raw dup1 hd24 (by evm_ov),
    raw dup3 hd25 (by evm_ov)]
  have hSlot := hKeccakPrefix.keccak256 0 (solcMappingSlot baseSlot key)
    (UInt256.ofNat 3) hd26 mem_cost hslot (by native_decide) (by evm_ov)
  have hBeforeStore := evm_run hSlot with [
    raw swap4 hd27 (by evm_ov),
    raw swap1 hd28 (by evm_ov),
    raw swap4 hd29 (by evm_ov)]
  obtain ⟨_, _, hOut⟩ := hBeforeStore.sstore hperm hd30 (by evm_ov)
  exact ⟨_, _, hOut⟩

set_option maxHeartbeats 1000000 in
theorem Run.solcSingleMappingStoreCreditMem {baseSlot newValue value key aux ret : UInt256}
    (h : Run code s0 ⟨pc, newValue :: value :: key :: aux :: ret :: R, mem, UInt256.ofNat 3,
      rdata, w⟩ k C)
    (hwf : solcSingleMappingStoreCreditMemWf code pc baseSlot)
    (hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot key)
    (hperm : s0.executionEnv.perm = true)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨solcSingleMappingStoreCreditOutPc pc,
      ⟨64⟩ :: key :: solcAddrMask :: ⟨32⟩ :: value :: key :: aux :: ret :: R,
      twoWordHashMem key baseSlot mem, UInt256.ofNat 3, rdata,
      { w with
          accounts := sstoreAccountMap s0.executionEnv.codeOwner w.accounts
            (solcMappingSlot baseSlot key) newValue }⟩ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd11, hd12, hd14, hd15, hd16,
      hd17, hd19, hd21, hd22, hd23, hd24, hd26, hd27, hd28, hd29, hd30, hd31, hd32, hd33⟩
  have hMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw dup1 hd9 (by evm_ov),
    raw dup5 hd10 (by evm_ov),
    raw and hd11 (by evm_ov)]
  rw [solcAddrMask_lit, solcAddrMask_clean hcanonKey] at hMasked
  have hMstore0Prefix := evm_run hMasked with [
    raw push1 ⟨0⟩ hd12 (by evm_ov),
    raw dup2 hd14 (by evm_ov),
    raw dup2 hd15 (by evm_ov)]
  have hAfterKey := hMstore0Prefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd16 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hMstoreSlotPrefix := evm_run hAfterKey with [
    raw push1 baseSlot hd17 (by evm_ov),
    raw push1 ⟨32⟩ hd19 (by evm_ov),
    raw swap1 hd21 (by evm_ov),
    raw dup2 hd22 (by evm_ov)]
  have hHashMem := hMstoreSlotPrefix.mstore 0 (twoWordHashMem key baseSlot mem)
    (UInt256.ofNat 3) hd23 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hKeccakPrefix := evm_run hHashMem with [
    raw push1 ⟨64⟩ hd24 (by evm_ov),
    raw swap2 hd26 (by evm_ov),
    raw dup3 hd27 (by evm_ov),
    raw swap1 hd28 (by evm_ov)]
  have hSlot := hKeccakPrefix.keccak256 0 (solcMappingSlot baseSlot key)
    (UInt256.ofNat 3) hd29 mem_cost hslot (by native_decide) (by evm_ov)
  have hBeforeStore := evm_run hSlot with [
    raw swap5 hd30 (by evm_ov),
    raw swap1 hd31 (by evm_ov),
    raw swap5 hd32 (by evm_ov)]
  obtain ⟨_, _, hOut⟩ := hBeforeStore.sstore hperm hd33 (by evm_ov)
  exact ⟨_, _, hOut⟩

theorem Run.solcNestedMappingStoreInnerHash {baseSlot value spender owner ret : UInt256}
    (h : Run code s0 ⟨pc, value :: spender :: owner :: ret :: R, mem, UInt256.ofNat 3, rdata, w⟩
      k C)
    (hwf : solcNestedMappingStoreInnerHashWf code pc baseSlot)
    (hmem : mem.size = 96)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨solcNestedMappingStoreInnerHashOutPc pc,
      solcMappingSlot baseSlot owner :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask ::
        value :: spender :: owner :: ret :: R,
      twoWordHashMem owner baseSlot mem, UInt256.ofNat 3, rdata, w⟩ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd11, hd12, hd14, hd15, hd16,
      hd17, hd19, hd21, hd22, hd23, hd24, hd26, hd27, hd28⟩
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem owner baseSlot mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot owner :=
    twoWordHashMem_solcMappingSlot baseSlot owner hmem
  have hMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw dup1 hd9 (by evm_ov),
    raw dup5 hd10 (by evm_ov),
    raw and hd11 (by evm_ov)]
  rw [solcAddrMask_lit, solcAddrMask_clean hcanonOwner] at hMasked
  have hMstore0Prefix := evm_run hMasked with [
    raw push1 ⟨0⟩ hd12 (by evm_ov),
    raw dup2 hd14 (by evm_ov),
    raw dup2 hd15 (by evm_ov)]
  have hInnerKey := hMstore0Prefix.mstore 0 (wordAt0Mem owner mem)
    (UInt256.ofNat 3) hd16 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hInnerMemPrefix := evm_run hInnerKey with [
    raw push1 baseSlot hd17 (by evm_ov),
    raw push1 ⟨32⟩ hd19 (by evm_ov),
    raw swap1 hd21 (by evm_ov),
    raw dup2 hd22 (by evm_ov)]
  have hInnerMem := hInnerMemPrefix.mstore 0 (twoWordHashMem owner baseSlot mem)
    (UInt256.ofNat 3) hd23 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hInnerHashPrefix := evm_run hInnerMem with [
    raw push1 ⟨64⟩ hd24 (by evm_ov),
    raw dup1 hd26 (by evm_ov),
    raw dup4 hd27 (by evm_ov)]
  exact ⟨_, _, hInnerHashPrefix.keccak256 0 (solcMappingSlot baseSlot owner)
    (UInt256.ofNat 3) hd28 mem_cost hslot (by native_decide) (by evm_ov)⟩

theorem Run.solcNestedMappingStoreOuterSstore {innerSlot value spender owner ret : UInt256}
    (h : Run code s0 ⟨pc,
      innerSlot :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask ::
        value :: spender :: owner :: ret :: R, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcNestedMappingStoreOuterSstoreWf code pc)
    (hmem : mem.size = 96)
    (hperm : s0.executionEnv.perm = true)
    (hcanonSpender : spender.toNat < EVM.addressModulus)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨solcNestedMappingStoreOuterSstoreOutPc pc,
      ⟨32⟩ :: ⟨64⟩ :: owner :: spender :: value :: spender :: owner :: ret :: R,
      twoWordHashMem spender innerSlot mem, UInt256.ofNat 3, rdata,
      { w with
          accounts := sstoreAccountMap s0.executionEnv.codeOwner w.accounts
            (solcMappingSlot innerSlot spender) value }⟩ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15⟩
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem spender innerSlot mem).readWithPadding 0 64))) =
        solcMappingSlot innerSlot spender :=
    twoWordHashMem_solcMappingSlot innerSlot spender hmem
  have hMasked := evm_run h with [
    raw swap5 hd0 (by evm_ov),
    raw dup8 hd1 (by evm_ov),
    raw and hd2 (by evm_ov)]
  rw [solcAddrMask_clean hcanonSpender] at hMasked
  have hOuterKeyPrefix := evm_run hMasked with [
    raw dup1 hd3 (by evm_ov),
    raw dup5 hd4 (by evm_ov)]
  have hOuterKey := hOuterKeyPrefix.mstore 0 (wordAt0Mem spender mem)
    (UInt256.ofNat 3) hd5 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hOuterMemPrefix := evm_run hOuterKey with [
    raw swap5 hd6 (by evm_ov),
    raw dup3 hd7 (by evm_ov)]
  have hOuterMem := hOuterMemPrefix.mstore 0 (twoWordHashMem spender innerSlot mem)
    (UInt256.ofNat 3) hd8 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hHashPrefix := evm_run hOuterMem with [
    raw swap2 hd9 (by evm_ov),
    raw dup3 hd10 (by evm_ov),
    raw swap1 hd11 (by evm_ov)]
  have hSlot := hHashPrefix.keccak256 0 (solcMappingSlot innerSlot spender)
    (UInt256.ofNat 3) hd12 mem_cost hslot (by native_decide) (by evm_ov)
  have hBeforeStore := evm_run hSlot with [
    raw dup6 hd13 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  obtain ⟨_, _, hOut⟩ := hBeforeStore.sstore hperm hd15 (by evm_ov)
  exact ⟨_, _, hOut⟩

set_option maxHeartbeats 1000000 in
theorem Run.solcNestedMappingCallerStoreMem
    {baseSlot newValue discard value aux owner ret : UInt256}
    (h : Run code s0 ⟨pc, newValue :: discard :: value :: aux :: owner :: ret :: R, mem,
      UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcNestedMappingCallerStoreMemWf code pc baseSlot)
    (hmem : mem.size = 96)
    (hperm : s0.executionEnv.perm = true)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨solcNestedMappingCallerStoreMemOutPc pc,
      discard :: value :: aux :: owner :: ret :: R,
      solcNestedMappingCallerHashMem baseSlot owner s0.executionEnv mem, UInt256.ofNat 3, rdata,
      { w with
          accounts := sstoreAccountMap s0.executionEnv.codeOwner w.accounts
            (solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord s0.executionEnv))
            newValue }⟩ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd11, hd13, hd14, hd15,
      hd16, hd18, hd20, hd21, hd22, hd23, hd25, hd26, hd27, hd28, hd29,
      hd30, hd31, hd32, hd33, hd34, hd35, hd36⟩
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem owner baseSlot mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot owner :=
    twoWordHashMem_solcMappingSlot baseSlot owner hmem
  have hinnerSize : (twoWordHashMem owner baseSlot mem).size = 96 :=
    twoWordHashMem_size_96 owner baseSlot hmem
  have houter :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC (ByteArray.readWithPadding
            (solcNestedMappingCallerHashMem baseSlot owner s0.executionEnv mem) 0 64))) =
        solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord s0.executionEnv) := by
    unfold solcNestedMappingCallerHashMem
    exact twoWordHashMem_solcMappingSlot (solcMappingSlot baseSlot owner)
      (solcSourceWord s0.executionEnv) hinnerSize
  have hMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw dup6 hd9 (by evm_ov),
    raw and hd10 (by evm_ov)]
  rw [solcAddrMask_lit, solcAddrMask_clean hcanonOwner] at hMasked
  have hMstore0Prefix := evm_run hMasked with [
    raw push1 ⟨0⟩ hd11 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw dup2 hd14 (by evm_ov)]
  have hInnerKey := hMstore0Prefix.mstore 0 (wordAt0Mem owner mem)
    (UInt256.ofNat 3) hd15 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hInnerMemPrefix := evm_run hInnerKey with [
    raw push1 baseSlot hd16 (by evm_ov),
    raw push1 ⟨32⟩ hd18 (by evm_ov),
    raw swap1 hd20 (by evm_ov),
    raw dup2 hd21 (by evm_ov)]
  have hInnerMem := hInnerMemPrefix.mstore 0 (twoWordHashMem owner baseSlot mem)
    (UInt256.ofNat 3) hd22 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hInnerHashPrefix := evm_run hInnerMem with [
    raw push1 ⟨64⟩ hd23 (by evm_ov),
    raw dup1 hd25 (by evm_ov),
    raw dup4 hd26 (by evm_ov)]
  have hInnerHash := hInnerHashPrefix.keccak256 0 (solcMappingSlot baseSlot owner)
    (UInt256.ofNat 3) hd27 mem_cost hinner (by native_decide) (by evm_ov)
  have hCaller := evm_run hInnerHash with [
    raw caller hd28 (by evm_ov),
    raw dup5 hd29 (by evm_ov)]
  have hOuterKey := hCaller.mstore 0
    (wordAt0Mem (solcSourceWord s0.executionEnv) (twoWordHashMem owner baseSlot mem))
    (UInt256.ofNat 3) hd30 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hOuterMemPrefix := evm_run hOuterKey with [
    raw swap1 hd31 (by evm_ov),
    raw swap2 hd32 (by evm_ov)]
  have hOuterMem := hOuterMemPrefix.mstore 0
    (solcNestedMappingCallerHashMem baseSlot owner s0.executionEnv mem)
    (UInt256.ofNat 3) hd33 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hOuterHashPrefix := evm_run hOuterMem with [raw swap1 hd34 (by evm_ov)]
  have hOuterHash := hOuterHashPrefix.keccak256 0
    (solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord s0.executionEnv))
    (UInt256.ofNat 3) hd35 mem_cost houter (by native_decide) (by evm_ov)
  obtain ⟨_, _, hOut⟩ := hOuterHash.sstore hperm hd36 (by evm_ov)
  exact ⟨_, _, hOut⟩

set_option maxHeartbeats 1000000 in
theorem Run.solcNestedMappingCallerLoad {baseSlot value aux owner ret : UInt256}
    (h : Run code s0 ⟨pc, value :: aux :: owner :: ret :: R, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcNestedMappingCallerLoadWf code pc baseSlot)
    (hmem : mem.size = 96)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨solcNestedMappingCallerLoadOutPc pc,
      solcSlotWord w.accounts s0.executionEnv
          (solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord s0.executionEnv)) ::
        ⟨0⟩ :: value :: aux :: owner :: ret :: R,
      solcNestedMappingCallerHashMem baseSlot owner s0.executionEnv mem, UInt256.ofNat 3, rdata, w⟩
      k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd11, hd13, hd14, hd15,
      hd16, hd18, hd20, hd21, hd22, hd23, hd25, hd26, hd27, hd28, hd29,
      hd30, hd31, hd32, hd33, hd34, hd35, hd36⟩
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem owner baseSlot mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot owner :=
    twoWordHashMem_solcMappingSlot baseSlot owner hmem
  have hinnerSize : (twoWordHashMem owner baseSlot mem).size = 96 :=
    twoWordHashMem_size_96 owner baseSlot hmem
  have houter :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC (ByteArray.readWithPadding
            (solcNestedMappingCallerHashMem baseSlot owner s0.executionEnv mem) 0 64))) =
        solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord s0.executionEnv) := by
    unfold solcNestedMappingCallerHashMem
    exact twoWordHashMem_solcMappingSlot (solcMappingSlot baseSlot owner)
      (solcSourceWord s0.executionEnv) hinnerSize
  have hMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw dup4 hd9 (by evm_ov),
    raw and hd10 (by evm_ov)]
  rw [solcAddrMask_lit, solcAddrMask_clean hcanonOwner] at hMasked
  have hMstore0Prefix := evm_run hMasked with [
    raw push1 ⟨0⟩ hd11 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw dup2 hd14 (by evm_ov)]
  have hInnerKey := hMstore0Prefix.mstore 0 (wordAt0Mem owner mem)
    (UInt256.ofNat 3) hd15 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hInnerMemPrefix := evm_run hInnerKey with [
    raw push1 baseSlot hd16 (by evm_ov),
    raw push1 ⟨32⟩ hd18 (by evm_ov),
    raw swap1 hd20 (by evm_ov),
    raw dup2 hd21 (by evm_ov)]
  have hInnerMem := hInnerMemPrefix.mstore 0 (twoWordHashMem owner baseSlot mem)
    (UInt256.ofNat 3) hd22 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hInnerHashPrefix := evm_run hInnerMem with [
    raw push1 ⟨64⟩ hd23 (by evm_ov),
    raw dup1 hd25 (by evm_ov),
    raw dup4 hd26 (by evm_ov)]
  have hInnerHash := hInnerHashPrefix.keccak256 0 (solcMappingSlot baseSlot owner)
    (UInt256.ofNat 3) hd27 mem_cost hinner (by native_decide) (by evm_ov)
  have hCaller := evm_run hInnerHash with [
    raw caller hd28 (by evm_ov),
    raw dup5 hd29 (by evm_ov)]
  have hOuterKey := hCaller.mstore 0
    (wordAt0Mem (solcSourceWord s0.executionEnv) (twoWordHashMem owner baseSlot mem))
    (UInt256.ofNat 3) hd30 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hOuterMemPrefix := evm_run hOuterKey with [
    raw swap1 hd31 (by evm_ov),
    raw swap2 hd32 (by evm_ov)]
  have hOuterMem := hOuterMemPrefix.mstore 0
    (solcNestedMappingCallerHashMem baseSlot owner s0.executionEnv mem)
    (UInt256.ofNat 3) hd33 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hOuterHashPrefix := evm_run hOuterMem with [raw dup2 hd34 (by evm_ov)]
  have hOuterHash := hOuterHashPrefix.keccak256 0
    (solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord s0.executionEnv))
    (UInt256.ofNat 3) hd35 mem_cost houter (by native_decide) (by evm_ov)
  obtain ⟨_, _, hLoaded⟩ := hOuterHash.sload hd36 (by evm_ov)
  exact ⟨_, _, hLoaded⟩

/-- `PUSH1 0; NOT; EQ; PUSH2 target; JUMPI`, branch taken (`word = 2^256 - 1`). -/
theorem Run.solcUintMaxEqBranchTrue {targetPc word discard : UInt256}
    (h : Run code s0 ⟨pc, word :: discard :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcUintMaxEqBranchWf code pc targetPc)
    (hmax : word.toNat = UInt256.size - 1)
    (htarget : (D_J code 0).contains targetPc = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨targetPc, discard :: R, mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd2, hd3, hd4, hd7⟩
  have hlnot0 : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot; decide
  have hword : word = UInt256.lnot (⟨0⟩ : UInt256) := by
    apply u256_inj; rw [hmax, hlnot0]
  have heq : UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) word = ⟨1⟩ := by
    rw [hword]; exact u256_eq_refl _
  have hEq := evm_run h with [
    raw push1 ⟨0⟩ hd0 (by evm_ov),
    raw not hd2 (by evm_ov),
    raw eq hd3 (by evm_ov)]
  rw [heq] at hEq
  exact ⟨_, _, evm_run hEq with [
    raw push2 targetPc hd4 (by evm_ov),
    raw jumpiT hd7 one_ne_zero_uint htarget (by evm_ov)]⟩

/-- `PUSH1 0; NOT; EQ; PUSH2 target; JUMPI`, fall-through (`word ≠ 2^256 - 1`). -/
theorem Run.solcUintMaxEqBranchFalse {targetPc word discard : UInt256}
    (h : Run code s0 ⟨pc, word :: discard :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcUintMaxEqBranchWf code pc targetPc)
    (hnotMax : word.toNat ≠ UInt256.size - 1)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨solcUintMaxEqBranchFallthroughPc pc, discard :: R, mem, aw, rdata, w⟩
      k' C' := by
  rcases hwf with ⟨hd0, hd2, hd3, hd4, hd7⟩
  have hlnot0 : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot; decide
  have hneq : UInt256.lnot (⟨0⟩ : UInt256) ≠ word := by
    intro hword; apply hnotMax; rw [← hword, hlnot0]
  have heq : UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) word = ⟨0⟩ := u256_eq_of_ne hneq
  have hEq := evm_run h with [
    raw push1 ⟨0⟩ hd0 (by evm_ov),
    raw not hd2 (by evm_ov),
    raw eq hd3 (by evm_ov)]
  rw [heq] at hEq
  exact ⟨_, _, (hEq.push2 targetPc hd4 (by evm_ov)).jumpiNT hd7 rfl (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem Run.solcNestedMappingCallerReloadToRoutineMem
    {baseSlot contPc routinePc discard value aux owner ret : UInt256}
    (h : Run code s0 ⟨pc, discard :: value :: aux :: owner :: ret :: R, mem, UInt256.ofNat 3,
      rdata, w⟩ k C)
    (hwf : solcNestedMappingCallerReloadToRoutineMemWf code pc baseSlot contPc routinePc)
    (hmem : mem.size = 96)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hroutineMask : UInt256.land routinePc ⟨0xffffffff⟩ = routinePc)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨routinePc,
      value ::
        solcSlotWord w.accounts s0.executionEnv
          (solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord s0.executionEnv)) ::
        contPc :: discard :: value :: aux :: owner :: ret :: R,
      solcNestedMappingCallerHashMem baseSlot owner s0.executionEnv mem, UInt256.ofNat 3, rdata, w⟩
      k' C' := by
  rcases hwf with
    ⟨hd0, hd2, hd4, hd6, hd7, hd8, hd9, hd10, hd12, hd13, hd14, hd15, hd17,
      hd19, hd20, hd21, hd22, hd24, hd25, hd26, hd27, hd28, hd29, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd39, hd40, hd41, hd46, hd49, hd50⟩
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem owner baseSlot mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot owner :=
    twoWordHashMem_solcMappingSlot baseSlot owner hmem
  have hinnerSize : (twoWordHashMem owner baseSlot mem).size = 96 :=
    twoWordHashMem_size_96 owner baseSlot hmem
  have houter :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC (ByteArray.readWithPadding
            (solcNestedMappingCallerHashMem baseSlot owner s0.executionEnv mem) 0 64))) =
        solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord s0.executionEnv) := by
    unfold solcNestedMappingCallerHashMem
    exact twoWordHashMem_solcMappingSlot (solcMappingSlot baseSlot owner)
      (solcSourceWord s0.executionEnv) hinnerSize
  have hMasked := evm_run h with [
    raw push1 ⟨1⟩ hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd2 (by evm_ov),
    raw push1 ⟨160⟩ hd4 (by evm_ov),
    raw shl hd6 (by evm_ov),
    raw sub hd7 (by evm_ov),
    raw dup5 hd8 (by evm_ov),
    raw and hd9 (by evm_ov)]
  rw [solcAddrMask_lit, solcAddrMask_clean hcanonOwner] at hMasked
  have hMstore0Prefix := evm_run hMasked with [
    raw push1 ⟨0⟩ hd10 (by evm_ov),
    raw swap1 hd12 (by evm_ov),
    raw dup2 hd13 (by evm_ov)]
  have hInnerKey := hMstore0Prefix.mstore 0 (wordAt0Mem owner mem)
    (UInt256.ofNat 3) hd14 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hInnerMemPrefix := evm_run hInnerKey with [
    raw push1 baseSlot hd15 (by evm_ov),
    raw push1 ⟨32⟩ hd17 (by evm_ov),
    raw swap1 hd19 (by evm_ov),
    raw dup2 hd20 (by evm_ov)]
  have hInnerMem := hInnerMemPrefix.mstore 0 (twoWordHashMem owner baseSlot mem)
    (UInt256.ofNat 3) hd21 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hInnerHashPrefix := evm_run hInnerMem with [
    raw push1 ⟨64⟩ hd22 (by evm_ov),
    raw dup1 hd24 (by evm_ov),
    raw dup4 hd25 (by evm_ov)]
  have hInnerHash := hInnerHashPrefix.keccak256 0 (solcMappingSlot baseSlot owner)
    (UInt256.ofNat 3) hd26 mem_cost hinner (by native_decide) (by evm_ov)
  have hCaller := evm_run hInnerHash with [
    raw caller hd27 (by evm_ov),
    raw dup5 hd28 (by evm_ov)]
  have hOuterKey := hCaller.mstore 0
    (wordAt0Mem (solcSourceWord s0.executionEnv) (twoWordHashMem owner baseSlot mem))
    (UInt256.ofNat 3) hd29 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hOuterMemPrefix := evm_run hOuterKey with [
    raw swap1 hd30 (by evm_ov),
    raw swap2 hd31 (by evm_ov)]
  have hOuterMem := hOuterMemPrefix.mstore 0
    (solcNestedMappingCallerHashMem baseSlot owner s0.executionEnv mem)
    (UInt256.ofNat 3) hd32 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hOuterHashPrefix := evm_run hOuterMem with [raw swap1 hd33 (by evm_ov)]
  have hOuterHash := hOuterHashPrefix.keccak256 0
    (solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord s0.executionEnv))
    (UInt256.ofNat 3) hd34 mem_cost houter (by native_decide) (by evm_ov)
  obtain ⟨_, _, hLoaded⟩ := hOuterHash.sload hd35 (by evm_ov)
  have hJump := evm_run hLoaded with [
    raw push2 contPc hd36 (by evm_ov),
    raw swap1 hd39 (by evm_ov),
    raw dup4 hd40 (by evm_ov),
    raw push4 ⟨0xffffffff⟩ hd41 (by evm_ov),
    raw push2 routinePc hd46 (by evm_ov),
    raw and hd49 (by evm_ov)]
  rw [hroutineMask] at hJump
  exact ⟨_, _, hJump.jump hd50 hroutine (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem Run.solcPreparedSingleMappingLoadToRoutineMem
    {baseSlot afterLoadPc routinePc value key other ret : UInt256}
    (h : Run code s0 ⟨pc, ⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: key :: other :: ret :: R,
      mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcPreparedSingleMappingLoadToRoutineMemWf code pc afterLoadPc routinePc)
    (hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((wordAt0Mem key mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot key)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hroutineMask : UInt256.land routinePc ⟨0xffffffff⟩ = routinePc)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨routinePc,
      value :: solcSlotWord w.accounts s0.executionEnv (solcMappingSlot baseSlot key) ::
        afterLoadPc :: value :: key :: other :: ret :: R,
      wordAt0Mem key mem, UInt256.ofNat 3, rdata, w⟩ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd10, hd11, hd12, hd17, hd20, hd21⟩
  have hMasked := evm_run h with [
    raw swap1 hd0 (by evm_ov),
    raw dup5 hd1 (by evm_ov),
    raw and hd2 (by evm_ov)]
  rw [solcAddrMask_clean hcanonKey] at hMasked
  have hBeforeHash := evm_run hMasked with [raw dup2 hd3 (by evm_ov)]
  have hHashMem := hBeforeHash.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd4 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hSlot := hHashMem.keccak256 0 (solcMappingSlot baseSlot key)
    (UInt256.ofNat 3) hd5 mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, hLoaded⟩ := hSlot.sload hd6 (by evm_ov)
  have hJump := evm_run hLoaded with [
    raw push2 afterLoadPc hd7 (by evm_ov),
    raw swap1 hd10 (by evm_ov),
    raw dup3 hd11 (by evm_ov),
    raw push4 ⟨0xffffffff⟩ hd12 (by evm_ov),
    raw push2 routinePc hd17 (by evm_ov),
    raw and hd20 (by evm_ov)]
  rw [hroutineMask] at hJump
  exact ⟨_, _, hJump.jump hd21 hroutine (by evm_ov)⟩

/-- Single-mapping getter routine from the free-pointer memory: `mapping[key]`. -/
theorem Run.solcSingleMappingGetter {baseSlot key ret : UInt256}
    (h : Run code s0 ⟨pc, key :: ret :: R, solcFreePtrMem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcSingleMappingGetterWf code pc baseSlot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret,
      solcSlotWord w.accounts s0.executionEnv (solcMappingSlot baseSlot key) :: ret :: R,
      solcMappingHashMem baseSlot key, UInt256.ofNat 3, rdata, w⟩ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd8, hd9, hd10, hd11, hd13, hd14, hd15, hd16, hd17⟩
  have h5 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 baseSlot hd1 (by evm_ov),
    raw push1 ⟨32⟩ hd3 (by evm_ov)]
  have h6 := h5.mstore 0 (solcMappingBaseSlotMem baseSlot)
    (UInt256.ofNat 3) hd5 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have h10 := evm_run h6 with [
    raw push1 ⟨0⟩ hd6 (by evm_ov),
    raw swap1 hd8 (by evm_ov),
    raw dup2 hd9 (by evm_ov)]
  have h11 := h10.mstore 0 (solcMappingHashMem baseSlot key)
    (UInt256.ofNat 3) hd10 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have h14 := evm_run h11 with [
    raw push1 ⟨64⟩ hd11 (by evm_ov),
    raw swap1 hd13 (by evm_ov)]
  have hslot := solcMappingKeccakSlot baseSlot key
  have h15 := h14.keccak256 0 (solcMappingSlot baseSlot key)
    (UInt256.ofNat 3) hd14 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, h16⟩ := h15.sload hd15 (by evm_ov)
  exact ⟨_, _, h16.dup2 hd16 (by evm_ov) |>.jump hd17 hret (by evm_ov)⟩

set_option maxHeartbeats 2000000 in
/-- Nested-mapping getter, first half: hash the outer key. -/
theorem Run.solcNestedMappingInnerHash {baseSlot owner spender ret : UInt256}
    (h : Run code s0 ⟨pc, spender :: owner :: ret :: R, solcFreePtrMem, UInt256.ofNat 3, rdata, w⟩
      k C)
    (hwf : solcNestedMappingGetterWf code pc baseSlot)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨solcNestedMappingGetterAfterInnerHashPc pc,
      solcMappingSlot baseSlot owner :: ⟨64⟩ :: ⟨32⟩ :: spender :: ⟨0⟩ :: ret :: R,
      solcMappingHashMem baseSlot owner, UInt256.ofNat 3, rdata, w⟩ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd10, hd11, hd12, hd13, hd15, hd16, hd17,
      _, _, _, _, _, _, _, _, _, _, _⟩
  have h7 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 baseSlot hd1 (by evm_ov),
    raw push1 ⟨32⟩ hd3 (by evm_ov),
    raw swap1 hd5 (by evm_ov),
    raw dup2 hd6 (by evm_ov)]
  have h9 := h7.mstore 0 (solcMappingBaseSlotMem baseSlot)
    (UInt256.ofNat 3) hd7 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have h12 := evm_run h9 with [
    raw push1 ⟨0⟩ hd8 (by evm_ov),
    raw swap3 hd10 (by evm_ov),
    raw dup4 hd11 (by evm_ov)]
  have h14 := h12.mstore 0 (solcMappingHashMem baseSlot owner)
    (UInt256.ofNat 3) hd12 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have h17 := evm_run h14 with [
    raw push1 ⟨64⟩ hd13 (by evm_ov),
    raw dup1 hd15 (by evm_ov),
    raw dup5 hd16 (by evm_ov)]
  have hinner := solcMappingKeccakSlot baseSlot owner
  exact ⟨_, _, h17.keccak256 0 (solcMappingSlot baseSlot owner)
    (UInt256.ofNat 3) hd17 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hinner)
    (by native_decide) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
/-- Nested-mapping getter, second half: hash the inner key over the outer slot. -/
theorem Run.solcNestedMappingOuterHash {baseSlot owner spender ret : UInt256}
    (h : Run code s0 ⟨solcNestedMappingGetterAfterInnerHashPc pc,
      solcMappingSlot baseSlot owner :: ⟨64⟩ :: ⟨32⟩ :: spender :: ⟨0⟩ :: ret :: R,
      solcMappingHashMem baseSlot owner, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcNestedMappingGetterWf code pc baseSlot)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨solcNestedMappingGetterSloadPc pc,
      solcMappingSlot (solcMappingSlot baseSlot owner) spender :: ret :: R,
      solcNestedMappingHashMem baseSlot owner spender, UInt256.ofNat 3, rdata, w⟩ k' C' := by
  rcases hwf with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hd18, hd19, hd20, hd21, hd22, hd23, hd24, hd25,
      _, _, _⟩
  have h20 := evm_run h with [raw swap1 hd18 (by evm_ov), raw swap2 hd19 (by evm_ov)]
  have h21 := h20.mstore 0 (solcNestedMappingOuterBaseMem baseSlot owner)
    (UInt256.ofNat 3) hd20 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have h23 := evm_run h21 with [raw swap1 hd21 (by evm_ov), raw dup3 hd22 (by evm_ov)]
  have h24 := h23.mstore 0 (solcNestedMappingHashMem baseSlot owner spender)
    (UInt256.ofNat 3) hd23 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have h25 := evm_run h24 with [raw swap1 hd24 (by evm_ov)]
  have hslot := solcNestedMappingKeccakSlot baseSlot owner spender
  exact ⟨_, _, h25.keccak256 0 (solcMappingSlot (solcMappingSlot baseSlot owner) spender)
    (UInt256.ofNat 3) hd25 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)⟩

/-- Nested-mapping getter, tail: `SLOAD; DUP2; JUMP`. -/
theorem Run.solcNestedMappingLoadAndJump {baseSlot slot ret : UInt256}
    (h : Run code s0 ⟨solcNestedMappingGetterSloadPc pc, slot :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcNestedMappingGetterWf code pc baseSlot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret, solcSlotWord w.accounts s0.executionEnv slot :: ret :: R,
      mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd26, hd27, hd28⟩
  obtain ⟨_, _, h27⟩ := h.sload hd26 (by evm_ov)
  exact ⟨_, _, h27.dup2 hd27 (by evm_ov) |>.jump hd28 hret (by evm_ov)⟩

/-! ## Reentrancy-lock prefix -/

set_option maxHeartbeats 1000000 in
/-- `JUMPDEST; PUSH1 slot; SLOAD; PUSH1 unlocked; EQ; PUSH2 ok; JUMPI; …; JUMPDEST; PUSH1 locked;
    PUSH1 slot; SSTORE`, lock free: take the lock. -/
theorem Run.solcLockEnterOk {okPc slot unlocked locked : UInt256}
    (h : Run code s0 ⟨pc, R, mem, aw, rdata, w⟩ k C)
    (hwf : solcLockEnterOkWf code pc okPc slot unlocked locked)
    (hperm : s0.executionEnv.perm = true)
    (hunlocked : solcSlotWord w.accounts s0.executionEnv slot = unlocked)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨okPc + UInt256.ofNat 6, R, mem, aw, rdata,
      { w with accounts := sstoreAccountMap s0.executionEnv.codeOwner w.accounts slot locked }⟩
      k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10, hdOk, hdOk1, hdOk3, hdOk5⟩
  have hunlockedRaw :
      (w.accounts.find? s0.executionEnv.codeOwner
        |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) = unlocked := hunlocked
  have h3 := h.jumpdest hd0 (by omega) |>.push1 slot hd1 (by omega)
  obtain ⟨_, _, h4⟩ := h3.sload hd3 (by omega)
  rw [hunlockedRaw] at h4
  have h7 := h4.push1 unlocked hd4 (by evm_ov) |>.eq hd6 (by omega)
  rw [uInt256_eq_self] at h7
  have hOk5 := h7.push2 okPc hd7 (by evm_ov)
    |>.jumpiT hd10 one_ne_zero_uint hok (by omega)
    |>.jumpdest hdOk (by omega)
    |>.push1 locked hdOk1 (by omega)
    |>.push1 slot hdOk3 (by evm_ov)
  obtain ⟨_, _, hAfter⟩ := hOk5.sstore hperm hdOk5 (by omega)
  have hpcOut : okPc + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ = okPc + UInt256.ofNat 6 := by
    rw [u256_add_assoc okPc ⟨1⟩ (UInt256.ofNat 2),
      u256_add_assoc okPc (⟨1⟩ + UInt256.ofNat 2) (UInt256.ofNat 2),
      u256_add_assoc okPc (⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2) ⟨1⟩]
    congr 1
  rw [hpcOut] at hAfter
  exact ⟨_, _, hAfter⟩

/-! ## Checked arithmetic

`JUMPDEST; DUP1; DUP3; SUB/ADD; DUP3; DUP2; GT/LT; ISZERO; PUSH2 ok; JUMPI` followed either by the
success tail `JUMPDEST; SWAP3; SWAP2; POP; POP; JUMP` or by the `Error(string)` revert tail. -/

set_option maxHeartbeats 1000000 in
theorem Run.solcCheckedSubSuccess {okPc a b ret : UInt256}
    (h : Run code s0 ⟨pc, b :: a :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcCheckedSubSuccessWf code pc okPc)
    (hle : b.toNat ≤ a.toNat)
    (hret : (D_J code 0).contains ret = true)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret, UInt256.sub a b :: R, mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, hdOk, hdOk1, hdOk2, hdOk3, hdOk4, hdOk5⟩
  have hsubNat : (UInt256.sub a b).toNat = a.toNat - b.toNat := usub_toNat hle
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ := ugt_zero (by rw [hsubNat]; omega)
  have h7 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw sub hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov),
    raw gt hd6 (by evm_ov)]
  rw [hgt] at h7
  have h8 := h7.iszero hd7 (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h8
  exact ⟨_, _, evm_run h8 with [
    raw push2 okPc hd8 (by evm_ov),
    raw jumpiT hd11 one_ne_zero_uint hok (by evm_ov),
    raw jumpdest hdOk (by evm_ov),
    raw swap3 hdOk1 (by evm_ov),
    raw swap2 hdOk2 (by evm_ov),
    raw pop hdOk3 (by evm_ov),
    raw pop hdOk4 (by evm_ov),
    raw jump hdOk5 hret (by evm_ov)]⟩

set_option maxHeartbeats 1000000 in
theorem Run.solcCheckedAddSuccess {okPc a b ret : UInt256}
    (h : Run code s0 ⟨pc, b :: a :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcCheckedAddSuccessWf code pc okPc)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J code 0).contains ret = true)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret, (a + b) :: R, mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, hdOk, hdOk1, hdOk2, hdOk3, hdOk4, hdOk5⟩
  have haddNat : (a + b).toNat = a.toNat + b.toNat := by rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hlt : UInt256.lt (a + b) a = ⟨0⟩ := ult_zero (by rw [haddNat]; omega)
  have h7 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw add hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov),
    raw lt hd6 (by evm_ov)]
  rw [hlt] at h7
  have h8 := h7.iszero hd7 (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h8
  exact ⟨_, _, evm_run h8 with [
    raw push2 okPc hd8 (by evm_ov),
    raw jumpiT hd11 one_ne_zero_uint hok (by evm_ov),
    raw jumpdest hdOk (by evm_ov),
    raw swap3 hdOk1 (by evm_ov),
    raw swap2 hdOk2 (by evm_ov),
    raw pop hdOk3 (by evm_ov),
    raw pop hdOk4 (by evm_ov),
    raw jump hdOk5 hret (by evm_ov)]⟩

/-! ## `Error(string)` revert tail

The tail builds the `Error(string)` ABI encoding at the free pointer `0x80` — selector, offset
`32`, length `len`, the (left-aligned) string word — and reverts with the 100 bytes at `0x80`. -/

/-- The bytes an `Error(string)` tail reverts with: `mem[0x80 .. 0x80+100)` of the built memory. -/
noncomputable def solcErrorStringPayload (len word : UInt256) (mem : ByteArray) : ByteArray :=
  (solcErrorStringMem3 len word mem).readWithPadding 128 100

set_option maxHeartbeats 1000000 in
theorem Run.solcErrorStringRevertTail {len rawWord shift word : UInt256} {op : Operation.POp}
    {width : ℕ}
    (h : Run code s0 ⟨pc, stk, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    Reverted code s0 (solcErrorStringPayload len word mem) := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have hMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd3 mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64) (by decide) (by evm_ov)]
  have hSelectorRaw := hMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by evm_ov)
  have hPrefix := evm_run hSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5) hd12 mem_cost (by rfl) (by decide)
      (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6) hd19 mem_cost (by rfl) (by decide)
      (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem) (UInt256.ofNat 7) hd26 mem_cost (by rfl)
      (by decide) (by evm_ov)]
  have hRaw := hPrefix.pushConst rawWord (width := width) (op := op) hpush hd27 (by evm_ov)
  have hWord := evm_run hRaw with [
    raw push1 shift hdRawOut (by evm_ov),
    raw shl hdShl (by evm_ov)]
  rw [hword] at hWord
  exact evm_run hWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 len word mem) (UInt256.ofNat 8) hdMstore3 mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hdMload mem_cost
      (solcErrorStringMem3_mload64 len word hmem hread64) (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 (solcErrorStringPayload len word mem) hdRev mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
            show ((⟨100⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 100
              from by decide]
          rfl)
      (by evm_ov)]

set_option maxHeartbeats 1000000 in
/-- Lock held: the guard falls into the `Error(string)` tail. -/
theorem Run.solcLockEnterLockedStringRevert {okPc slot unlocked len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ}
    (h : Run code s0 ⟨pc, R, solcFreePtrMem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hlock : solcLockEnterGuardWf code pc okPc slot unlocked)
    (htail : solcErrorStringRevertTailWf code (solcLockEnterRevertPc pc) len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hlocked : solcSlotWord w.accounts s0.executionEnv slot ≠ unlocked)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hov : R.length + 6 ≤ 1024) :
    Reverted code s0 (solcErrorStringPayload len word solcFreePtrMem) := by
  rcases hlock with ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10⟩
  have heqZero : UInt256.eq unlocked (solcSlotWord w.accounts s0.executionEnv slot) = ⟨0⟩ :=
    u256_eq_of_ne (fun hbad => hlocked hbad.symm)
  have h3 := h.jumpdest hd0 (by omega) |>.push1 slot hd1 (by omega)
  obtain ⟨_, _, h4⟩ := h3.sload hd3 (by omega)
  have h7 := h4.push1 unlocked hd4 (by evm_ov) |>.eq hd6 (by omega)
  rw [heqZero] at h7
  have hRevert := (h7.push2 okPc hd7 (by evm_ov)).jumpiNT hd10 rfl (by omega)
  exact hRevert.solcErrorStringRevertTail htail hpush hword solcFreePtrMem_size
    solcFreePtrMem_read64 (by omega)

set_option maxHeartbeats 1000000 in
/-- Checked subtraction underflow: the `Error(string)` tail. -/
theorem Run.solcCheckedSubStringRevert {okPc len rawWord shift word a b ret : UInt256}
    {op : Operation.POp} {width : ℕ}
    (h : Run code s0 ⟨pc, b :: a :: ret :: R, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hsub : solcCheckedSubSuccessWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (solcCheckedArithmeticRevertPc pc)
      len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hlt : a.toNat < b.toNat)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    Reverted code s0 (solcErrorStringPayload len word mem) := by
  rcases hsub with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsubNat : (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub a b > a)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub a b).toNat > a.toNat
      rw [hsubNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have h7 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw sub hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov),
    raw gt hd6 (by evm_ov)]
  rw [hgt] at h7
  have h8 := h7.iszero hd7 (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h8
  have hTail := (h8.push2 okPc hd8 (by evm_ov)).jumpiNT hd11 rfl (by evm_ov)
  exact hTail.solcErrorStringRevertTail htail hpush hword hmem hread64 (by evm_ov)

set_option maxHeartbeats 1000000 in
/-- Checked addition overflow: the `Error(string)` tail. -/
theorem Run.solcCheckedAddStringRevert {okPc len rawWord shift word a b ret : UInt256}
    {op : Operation.POp} {width : ℕ}
    (h : Run code s0 ⟨pc, b :: a :: ret :: R, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hadd : solcCheckedAddSuccessWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (solcCheckedArithmeticRevertPc pc)
      len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    Reverted code s0 (solcErrorStringPayload len word mem) := by
  rcases hadd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hmod : (a.toNat + b.toNat) % UInt256.size = a.toNat + b.toNat - UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (a + b) a = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have h7 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw add hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov),
    raw lt hd6 (by evm_ov)]
  rw [hlt] at h7
  have h8 := h7.iszero hd7 (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h8
  have hTail := (h8.push2 okPc hd8 (by evm_ov)).jumpiNT hd11 rfl (by evm_ov)
  exact hTail.solcErrorStringRevertTail htail hpush hword hmem hread64 (by evm_ov)

/-- Mapping load followed by a successful checked subtraction (`balances[key] -= value`). -/
theorem Run.solcSingleMappingLoadCheckedSubMem
    {baseSlot afterLoadPc routinePc checkedOkPc value aux key ret : UInt256}
    (h : Run code s0 ⟨pc, value :: aux :: key :: ret :: R, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hload : solcSingleMappingLoadToRoutineMemWf code pc baseSlot afterLoadPc routinePc)
    (hsub : solcCheckedSubSuccessWf code routinePc checkedOkPc)
    (hmem : mem.size = 96)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hbalance : value.toNat
        ≤ (solcSlotWord w.accounts s0.executionEnv (solcMappingSlot baseSlot key)).toNat)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hroutineMask : UInt256.land routinePc ⟨0xffffffff⟩ = routinePc)
    (hafterLoad : (D_J code 0).contains afterLoadPc = true)
    (hcheckedOk : (D_J code 0).contains checkedOkPc = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨afterLoadPc,
      UInt256.sub (solcSlotWord w.accounts s0.executionEnv (solcMappingSlot baseSlot key)) value ::
        value :: aux :: key :: ret :: R,
      twoWordHashMem key baseSlot mem, UInt256.ofNat 3, rdata, w⟩ k' C' := by
  obtain ⟨_, _, hRoutine⟩ := h.solcSingleMappingLoadToRoutineMem hload hmem hcanonKey hroutine
    hroutineMask hov
  obtain ⟨_, _, hAfterLoad⟩ := hRoutine.solcCheckedSubSuccess hsub hbalance hafterLoad hcheckedOk
    (by evm_ov)
  exact ⟨_, _, hAfterLoad⟩

/-- Prepared mapping load followed by a successful checked addition (`balances[key] += value`). -/
theorem Run.solcPreparedSingleMappingLoadCheckedAddMem
    {baseSlot afterLoadPc routinePc checkedOkPc value key other ret : UInt256}
    (h : Run code s0 ⟨pc, ⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: key :: other :: ret :: R,
      mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hload : solcPreparedSingleMappingLoadToRoutineMemWf code pc afterLoadPc routinePc)
    (hadd : solcCheckedAddSuccessWf code routinePc checkedOkPc)
    (hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((wordAt0Mem key mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot key)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hfit : (solcSlotWord w.accounts s0.executionEnv (solcMappingSlot baseSlot key)).toNat
        + value.toNat < UInt256.size)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hroutineMask : UInt256.land routinePc ⟨0xffffffff⟩ = routinePc)
    (hafterLoad : (D_J code 0).contains afterLoadPc = true)
    (hcheckedOk : (D_J code 0).contains checkedOkPc = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨afterLoadPc,
      (solcSlotWord w.accounts s0.executionEnv (solcMappingSlot baseSlot key) + value) ::
        value :: key :: other :: ret :: R,
      wordAt0Mem key mem, UInt256.ofNat 3, rdata, w⟩ k' C' := by
  obtain ⟨_, _, hRoutine⟩ := h.solcPreparedSingleMappingLoadToRoutineMem hload hslot hcanonKey
    hroutine hroutineMask hov
  obtain ⟨_, _, hAfterLoad⟩ := hRoutine.solcCheckedAddSuccess hadd hfit hafterLoad hcheckedOk
    (by evm_ov)
  exact ⟨_, _, hAfterLoad⟩

/-! ## Boolean-success continuations -/

theorem Run.solcDiscard2ReturnTrue {discard a b ret : UInt256}
    (h : Run code s0 ⟨pc, discard :: a :: b :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcDiscard2ReturnTrueWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret, ⟨1⟩ :: R, mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd8, hd9⟩
  exact ⟨_, _, evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw pop hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd2 (by evm_ov),
    raw jumpdest hd4 (by evm_ov),
    raw swap3 hd5 (by evm_ov),
    raw swap2 hd6 (by evm_ov),
    raw pop hd7 (by evm_ov),
    raw pop hd8 (by evm_ov),
    raw jump hd9 hret (by evm_ov)]⟩

theorem Run.solcDiscard4ReturnTrue {discard value toWord src ret : UInt256}
    (h : Run code s0 ⟨pc, discard :: value :: toWord :: src :: ret :: R, mem, aw, rdata, w⟩ k C)
    (hwf : solcDiscard4ReturnTrueWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret, ⟨1⟩ :: R, mem, aw, rdata, w⟩ k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd8, hd9⟩
  exact ⟨_, _, evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw pop hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd2 (by evm_ov),
    raw swap4 hd4 (by evm_ov),
    raw swap3 hd5 (by evm_ov),
    raw pop hd6 (by evm_ov),
    raw pop hd7 (by evm_ov),
    raw pop hd8 (by evm_ov),
    raw jump hd9 hret (by evm_ov)]⟩

/-! ## Event-log suffixes

Both `LOG3` suffixes store `value` at the free pointer `0x80` and log the 32 bytes there, so the
appended entry's data is exactly `abi.encode(value)`. -/

/-- Reading back a 32-byte word written at `off`, also when the write extends the base. -/
theorem toByteArray_write_read_back_ext (base : ByteArray) (word : UInt256) (off : ℕ)
    (hoff : off < 2 ^ 32) :
    ((UInt256.toByteArray word).write 0 base off 32).readWithPadding off 32 =
      UInt256.toByteArray word := by
  by_cases h : off ≤ base.size
  · exact toByteArray_write32_read_back base word off h
  · have hlt : base.size < off := Nat.lt_of_not_ge h
    rw [toByteArray_write_eq _ _ _ (by omega) (lt_usize _ (by omega))]
    have hz : (ffi.ByteArray.zeroes (off - base.size)).size = off - base.size :=
      zeroes_ofNat_size _ (by omega)
    have hpre : (base ++ ffi.ByteArray.zeroes (off - base.size)).size = off := by
      rw [ByteArray.size_append, hz]; omega
    rw [readWithPadding_eq_extract _ _ (by rw [ByteArray.size_append, hpre, toByteArray_size]),
      extract_append_right' _ _ _ _ hpre.symm (by rw [hpre, toByteArray_size])]

set_option maxHeartbeats 1000000 in
/-- `Transfer`-style `LOG3` suffix with the masked `from` topic: appends
    `⟨this, [topic, src, to], abi.encode(value)⟩` and jumps to `ret`. -/
theorem Run.solcMaskedTransferLog3AndJump {topic value toWord src ret : UInt256}
    (h : Run code s0 ⟨pc,
      ⟨64⟩ :: toWord :: solcAddrMask :: ⟨32⟩ :: value :: toWord :: src :: ret :: R,
      mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcMaskedTransferLog3AndJumpWf code pc topic)
    (hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hlogMload :
      (if (⟨64⟩ : UInt256).toNat ≥ ((UInt256.toByteArray value).write 0 mem 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (((UInt256.toByteArray value).write 0 mem 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hperm : s0.executionEnv.perm = true)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret, R, (UInt256.toByteArray value).write 0 mem 128 32, UInt256.ofNat 5,
      rdata,
      { w with logs := w.logs.push ⟨s0.executionEnv.codeOwner, #[topic, src, toWord],
                                     UInt256.toByteArray value⟩ }⟩ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12,
      hd13, hd46, hd47, hd48, hd49, hd50, hd51, hd52, hd53, hd54, hd55, hd56, hd57⟩
  have h2 := evm_run h with [
    raw dup1 hd0 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd1 mem_cost hmload (by decide) (by evm_ov)]
  have h4 := evm_run h2 with [raw dup6 hd2 (by evm_ov), raw dup2 hd3 (by evm_ov)]
  have h5 := h4.mstore 6 ((UInt256.toByteArray value).write 0 mem 128 32)
    (UInt256.ofNat 5) hd4 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have h12 := evm_run h5 with [
    raw swap1 hd5 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd6 mem_cost hlogMload (by decide) (by evm_ov),
    raw swap2 hd7 (by evm_ov),
    raw swap4 hd8 (by evm_ov),
    raw swap3 hd9 (by evm_ov),
    raw dup8 hd10 (by evm_ov),
    raw and hd11 (by evm_ov)]
  rw [solcAddrMask_clean hcanonSrc] at h12
  have h13 := evm_run h12 with [raw swap3 hd12 (by evm_ov)]
  have h46 := h13.pushConst topic (width := 32) (op := .PUSH32) (by decide) hd13 (by evm_ov)
  have h53 := evm_run h46 with [
    raw swap3 hd46 (by evm_ov),
    raw swap2 hd47 (by evm_ov),
    raw dup3 hd48 (by evm_ov),
    raw swap1 hd49 (by evm_ov),
    raw sub hd50 (by evm_ov),
    raw add hd51 (by evm_ov),
    raw swap1 hd52 (by evm_ov)]
  have h54 := h53.log3 0 (UInt256.ofNat 5) hd53 hperm mem_cost (by decide) (by evm_ov)
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
    show (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨32⟩).toNat = 32 from by decide,
    toByteArray_write_read_back_ext _ _ _ (by norm_num)] at h54
  have h57 := evm_run h54 with [
    raw pop hd54 (by evm_ov),
    raw pop hd55 (by evm_ov),
    raw pop hd56 (by evm_ov)]
  exact ⟨_, _, h57.jump hd57 hret (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
/-- Plain `LOG3` suffix (both indexed topics already clean): appends
    `⟨this, [topic, topic1, topic2], abi.encode(value)⟩` and jumps to `ret`. -/
theorem Run.solcPlainLog3AndJump {topic value topic1 topic2 ret : UInt256}
    (h : Run code s0 ⟨pc,
      ⟨32⟩ :: ⟨64⟩ :: topic1 :: topic2 :: value :: topic2 :: topic1 :: ret :: R,
      mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcPlainLog3AndJumpWf code pc topic)
    (hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hlogMload :
      (if (⟨64⟩ : UInt256).toNat ≥ ((UInt256.toByteArray value).write 0 mem 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (((UInt256.toByteArray value).write 0 mem 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hperm : s0.executionEnv.perm = true)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨ret, R, (UInt256.toByteArray value).write 0 mem 128 32, UInt256.ofNat 5,
      rdata,
      { w with logs := w.logs.push ⟨s0.executionEnv.codeOwner, #[topic, topic1, topic2],
                                     UInt256.toByteArray value⟩ }⟩ k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd40, hd41, hd42, hd43, hd44,
      hd45, hd46, hd47, hd48, hd49, hd50, hd51, hd52⟩
  have h2 := evm_run h with [
    raw dup2 hd0 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd1 mem_cost hmload (by decide) (by evm_ov)]
  have h4 := evm_run h2 with [raw dup6 hd2 (by evm_ov), raw dup2 hd3 (by evm_ov)]
  have h5 := h4.mstore 6 ((UInt256.toByteArray value).write 0 mem 128 32)
    (UInt256.ofNat 5) hd4 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have h7 := evm_run h5 with [
    raw swap2 hd5 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd6 mem_cost hlogMload (by decide) (by evm_ov)]
  have h40 := h7.pushConst topic (width := 32) (op := .PUSH32) (by decide) hd7 (by evm_ov)
  have h48 := evm_run h40 with [
    raw swap3 hd40 (by evm_ov),
    raw dup2 hd41 (by evm_ov),
    raw swap1 hd42 (by evm_ov),
    raw sub hd43 (by evm_ov),
    raw swap1 hd44 (by evm_ov),
    raw swap2 hd45 (by evm_ov),
    raw add hd46 (by evm_ov),
    raw swap1 hd47 (by evm_ov)]
  have h49 := h48.log3 0 (UInt256.ofNat 5) hd48 hperm mem_cost (by decide) (by evm_ov)
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
    show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32 from by decide,
    toByteArray_write_read_back_ext _ _ _ (by norm_num)] at h49
  have h52 := evm_run h49 with [
    raw pop hd49 (by evm_ov),
    raw pop hd50 (by evm_ov),
    raw pop hd51 (by evm_ov)]
  exact ⟨_, _, h52.jump hd52 hret (by evm_ov)⟩

/-! ## One-word return wrappers from scratch memory -/

theorem Run.solcReturnWordFromMem {val ret : UInt256} {memout : ByteArray}
    (h : Run code s0 ⟨pc, val :: ret :: R, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcReturnWordFromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout : (UInt256.toByteArray val).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray val)
    (hov : R.length + 5 ≤ 1024) :
    Returned code s0 w (UInt256.toByteArray val) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd15, hd16, hd17⟩
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw swap2 hd5 (by evm_ov),
    raw dup3 hd6 (by evm_ov),
    raw mstore 6 memout (UInt256.ofNat 5) hd7 mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd8 mem_cost hmemoutLoad64 (by decide) (by evm_ov),
    raw swap1 hd9 (by evm_ov),
    raw dup2 hd10 (by evm_ov),
    raw swap1 hd11 (by evm_ov),
    raw sub hd12 (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw add hd15 (by evm_ov),
    raw swap1 hd16 (by evm_ov),
    raw ret 0 (UInt256.toByteArray val) hd17 mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
            show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
              from by decide]
          exact hread128)
      (by evm_ov)]

theorem Run.solcReturnAddressFromMem {val ret : UInt256} {memout : ByteArray}
    (h : Run code s0 ⟨pc, val :: ret :: R, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcReturnAddressFromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout : (UInt256.toByteArray (UInt256.land val solcAddrMask)).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray (UInt256.land val solcAddrMask))
    (hov : R.length + 9 ≤ 1024) :
    Returned code s0 w (UInt256.toByteArray (UInt256.land val solcAddrMask)) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd7, hd9, hd11, hd12, hd13, hd14, hd15, hd16, hd17,
      hd18, hd19, hd20, hd21, hd22, hd23, hd25, hd26, hd27⟩
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw push1 ⟨1⟩ hd5 (by evm_ov),
    raw push1 ⟨1⟩ hd7 (by evm_ov),
    raw push1 ⟨160⟩ hd9 (by evm_ov),
    raw shl hd11 (by evm_ov),
    raw sub hd12 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw swap3 hd14 (by evm_ov),
    raw and hd15 (by evm_ov),
    raw dup3 hd16 (by evm_ov),
    raw mstore 6 memout (UInt256.ofNat 5) hd17 mem_cost
      (by rw [solcAddrMask_lit, show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd18 mem_cost hmemoutLoad64 (by decide) (by evm_ov),
    raw swap1 hd19 (by evm_ov),
    raw dup2 hd20 (by evm_ov),
    raw swap1 hd21 (by evm_ov),
    raw sub hd22 (by evm_ov),
    raw push1 ⟨32⟩ hd23 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw swap1 hd26 (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.land val solcAddrMask)) hd27 mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
            show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
              from by decide]
          exact hread128)
      (by evm_ov)]

theorem Run.solcReturnUint8FromMem {val ret : UInt256} {memout : ByteArray}
    (h : Run code s0 ⟨pc, val :: ret :: R, mem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hwf : solcReturnUint8FromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout : (UInt256.toByteArray (UInt256.land val ⟨255⟩)).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray (UInt256.land val ⟨255⟩))
    (hov : R.length + 9 ≤ 1024) :
    Returned code s0 w (UInt256.toByteArray (UInt256.land val ⟨255⟩)) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
      hd16, hd17, hd19, hd20, hd21⟩
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw push1 ⟨255⟩ hd5 (by evm_ov),
    raw swap1 hd7 (by evm_ov),
    raw swap3 hd8 (by evm_ov),
    raw and hd9 (by evm_ov),
    raw dup3 hd10 (by evm_ov),
    raw mstore 6 memout (UInt256.ofNat 5) hd11 mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd12 mem_cost hmemoutLoad64 (by decide) (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw dup2 hd14 (by evm_ov),
    raw swap1 hd15 (by evm_ov),
    raw sub hd16 (by evm_ov),
    raw push1 ⟨32⟩ hd17 (by evm_ov),
    raw add hd19 (by evm_ov),
    raw swap1 hd20 (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.land val ⟨255⟩)) hd21 mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
            show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
              from by decide]
          exact hread128)
      (by evm_ov)]

theorem Run.solcReturnBoolFromMem {val : UInt256} {memout : ByteArray}
    (h : Run code s0 ⟨pc, val :: R, mem, UInt256.ofNat 5, rdata, w⟩ k C)
    (hwf : solcReturnBoolFromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout : (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))).write 0 mem 128 32
        = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32
        = UInt256.toByteArray (UInt256.isZero (UInt256.isZero val)))
    (hov : R.length + 5 ≤ 1024) :
    Returned code s0 w (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14,
      hd15, hd17, hd18, hd19⟩
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw swap2 hd5 (by evm_ov),
    raw iszero hd6 (by evm_ov),
    raw iszero hd7 (by evm_ov),
    raw dup3 hd8 (by evm_ov),
    raw mstore 0 memout (UInt256.ofNat 5) hd9 mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd10 mem_cost hmemoutLoad64 (by decide) (by evm_ov),
    raw swap1 hd11 (by evm_ov),
    raw dup2 hd12 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw sub hd14 (by evm_ov),
    raw push1 ⟨32⟩ hd15 (by evm_ov),
    raw add hd17 (by evm_ov),
    raw swap1 hd18 (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))) hd19 mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
            show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
              from by decide]
          exact hread128)
      (by evm_ov)]

/-! ## Whole external getters (thunk + routine + return wrapper) -/

theorem Run.solcAddressGetterExternal {sel entry routine slot returnPc : UInt256}
    (h : Run code s0 ⟨entry, [sel], solcFreePtrMem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcAddressSlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnAddressFromMemWf code returnPc) :
    Returned code s0 w (UInt256.toByteArray
      (UInt256.land (solcSlotWord w.accounts s0.executionEnv slot) solcAddrMask)) := by
  obtain ⟨_, _, hRoutine⟩ := h.solcGetterThunk hentry hroutine (by simp)
  obtain ⟨_, _, hReturn⟩ := hRoutine.solcAddressSlotGetter hgetter hret (by simp)
  have hclean :
      UInt256.land (UInt256.land solcAddrMask (solcSlotWord w.accounts s0.executionEnv slot))
          solcAddrMask =
        UInt256.land (solcSlotWord w.accounts s0.executionEnv slot) solcAddrMask := by
    rw [u256_land_comm solcAddrMask (solcSlotWord w.accounts s0.executionEnv slot)]
    exact solcAddrMask_clean
      (solcAddrMask_result_canonical (solcSlotWord w.accounts s0.executionEnv slot))
  have hrd := hReturn.solcReturnAddressFromMem hreturn solcFreePtrMem_mload64 rfl
    (solcReturnMem_mload64
      (UInt256.land (UInt256.land solcAddrMask (solcSlotWord w.accounts s0.executionEnv slot))
        solcAddrMask))
    (solcReturnMem_read128
      (UInt256.land (UInt256.land solcAddrMask (solcSlotWord w.accounts s0.executionEnv slot))
        solcAddrMask))
    (by simp)
  rw [hclean] at hrd
  exact hrd

theorem Run.solcWordGetterExternal {sel entry routine slot returnPc : UInt256}
    (h : Run code s0 ⟨entry, [sel], solcFreePtrMem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcWordSlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnWordFromMemWf code returnPc) :
    Returned code s0 w (UInt256.toByteArray (solcSlotWord w.accounts s0.executionEnv slot)) := by
  obtain ⟨_, _, hRoutine⟩ := h.solcGetterThunk hentry hroutine (by simp)
  obtain ⟨_, _, hReturn⟩ := hRoutine.solcWordSlotGetter hgetter hret (by simp)
  exact hReturn.solcReturnWordFromMem hreturn solcFreePtrMem_mload64 rfl
    (solcReturnMem_mload64 (solcSlotWord w.accounts s0.executionEnv slot))
    (solcReturnMem_read128 (solcSlotWord w.accounts s0.executionEnv slot)) (by simp)

theorem Run.solcWordConstGetterExternal {sel entry routine returnPc val : UInt256} {width : ℕ}
    {op : Operation.POp}
    (h : Run code s0 ⟨entry, [sel], solcFreePtrMem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnWordFromMemWf code returnPc) :
    Returned code s0 w (UInt256.toByteArray val) := by
  obtain ⟨_, _, hRoutine⟩ := h.solcGetterThunk hentry hroutine (by simp)
  obtain ⟨_, _, hReturn⟩ := hRoutine.solcConstGetter hgetter hret (by simp)
  exact hReturn.solcReturnWordFromMem hreturn solcFreePtrMem_mload64 rfl
    (solcReturnMem_mload64 val) (solcReturnMem_read128 val) (by simp)

theorem Run.solcUint8ConstGetterExternal {sel entry routine returnPc val : UInt256} {width : ℕ}
    {op : Operation.POp}
    (h : Run code s0 ⟨entry, [sel], solcFreePtrMem, UInt256.ofNat 3, rdata, w⟩ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnUint8FromMemWf code returnPc) :
    Returned code s0 w (UInt256.toByteArray (UInt256.land val ⟨255⟩)) := by
  obtain ⟨_, _, hRoutine⟩ := h.solcGetterThunk hentry hroutine (by simp)
  obtain ⟨_, _, hReturn⟩ := hRoutine.solcConstGetter hgetter hret (by simp)
  exact hReturn.solcReturnUint8FromMem hreturn solcFreePtrMem_mload64 rfl
    (solcReturnMem_mload64 (UInt256.land val ⟨255⟩))
    (solcReturnMem_read128 (UInt256.land val ⟨255⟩)) (by simp)

/-! ## High-level external calls: return decoding and guards -/

set_option maxHeartbeats 2000000 in
/-- `uint256` return decoder after a successful call: `POP; POP; POP; PUSH1 0x40; MLOAD;
    RETURNDATASIZE; PUSH1 32; DUP2; LT; ISZERO; PUSH2 ok; JUMPI; JUMPDEST; POP; MLOAD`, with at
    least 32 bytes of return data: pushes the word at `0x80`. -/
theorem Run.solcUint256ReturnWordDecodeOk {okPc d0 d1 d2 retWord : UInt256}
    (h : Run code s0 ⟨pc, d0 :: d1 :: d2 :: R, mem, aw, rdata, w⟩ k C)
    (hlo : 32 ≤ rdata.size) (hhi : rdata.size < UInt256.size)
    (hMload64Cost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨64⟩ : UInt256) :: R → memoryExpansionCost s .MLOAD = 0)
    (hMload64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size ∨ (⟨128⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) = retWord)
    (hMload128Cost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨128⟩ : UInt256) :: R → memoryExpansionCost s .MLOAD = 0)
    (hMload128Aw : UInt256.ofNat (MachineState.M aw.toNat 128 32) = aw)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) = some (.MLOAD, .none))
    (hReturndatasize : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩)
        = some (.RETURNDATASIZE, .none))
    (hPush32 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩)
        = some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2)
        = some (.DUP2, .none))
    (hLt : decode code
        (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩)
        = some (.LT, .none))
    (hIszero : decode code
        (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩)
        = some (.ISZERO, .none))
    (hPushOk : decode code
        (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
        = some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi : decode code
        ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
          + UInt256.ofNat 3)
        = some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPopLen : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hMload128 : decode code (okPc + ⟨1⟩ + ⟨1⟩) = some (.MLOAD, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩, retWord :: R, mem, aw, rdata, w⟩ k' C' := by
  have hlt : UInt256.lt (UInt256.ofNat rdata.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' rdata.size hhi]
    exact hlo
  have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (⟨32⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hlt]; decide
  have hMl64 := h.pop hPop0 (by evm_ov) |>.pop hPop1 (by evm_ov) |>.pop hPop2 (by evm_ov)
    |>.push1 ⟨64⟩ hPush64 (by evm_ov)
    |>.mload 0 ⟨128⟩ aw hMload64 hMload64Cost hMload64Value hMload64Aw (by evm_ov)
  have hPopLen' := hMl64.returndatasize hReturndatasize (by evm_ov)
    |>.push1 ⟨32⟩ hPush32 (by evm_ov)
    |>.dup2 hDup2 (by evm_ov)
    |>.lt hLt (by evm_ov)
    |>.iszero hIszero (by evm_ov)
    |>.push2 okPc hPushOk (by evm_ov)
    |>.jumpiT hJumpi hcond hjd (by evm_ov)
    |>.jumpdest hJumpdest (by evm_ov)
    |>.pop hPopLen (by evm_ov)
  exact ⟨_, _, hPopLen'.mload 0 retWord aw hMload128 hMload128Cost hMload128Value hMload128Aw
    (by evm_ov)⟩

set_option maxHeartbeats 2000000 in
/-- The same decoder with fewer than 32 bytes of return data: `revert(0,0)`. -/
theorem Run.solcUint256ReturnWordDecodeShortReverts {okPc d0 d1 d2 : UInt256}
    (h : Run code s0 ⟨pc, d0 :: d1 :: d2 :: R, mem, aw, rdata, w⟩ k C)
    (hshort : rdata.size < 32) (hhi : rdata.size < UInt256.size)
    (hMload64Cost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨64⟩ : UInt256) :: R → memoryExpansionCost s .MLOAD = 0)
    (hMload64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) = some (.MLOAD, .none))
    (hReturndatasize : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩)
        = some (.RETURNDATASIZE, .none))
    (hPush32 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩)
        = some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2)
        = some (.DUP2, .none))
    (hLt : decode code
        (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩)
        = some (.LT, .none))
    (hIszero : decode code
        (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩)
        = some (.ISZERO, .none))
    (hPushOk : decode code
        (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
        = some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi : decode code
        ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
          + UInt256.ofNat 3)
        = some (.JUMPI, .none))
    (hPush0 : decode code
        (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
          + UInt256.ofNat 3) + ⟨1⟩)
        = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hDupZero : decode code
        ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
          + UInt256.ofNat 3) + ⟨1⟩) + UInt256.ofNat 2)
        = some (.DUP1, .none))
    (hRevert : decode code
        (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
          + UInt256.ofNat 3) + ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩)
        = some (.REVERT, .none))
    (hov : R.length + 4 ≤ 1024) :
    Reverted code s0 ByteArray.empty := by
  have hlt : UInt256.lt (UInt256.ofNat rdata.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' rdata.size hhi]
    exact hshort
  have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (⟨32⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]; decide
  have hMl64 := h.pop hPop0 (by evm_ov) |>.pop hPop1 (by evm_ov) |>.pop hPop2 (by evm_ov)
    |>.push1 ⟨64⟩ hPush64 (by evm_ov)
    |>.mload 0 ⟨128⟩ aw hMload64 hMload64Cost hMload64Value hMload64Aw (by evm_ov)
  have hFall := hMl64.returndatasize hReturndatasize (by evm_ov)
    |>.push1 ⟨32⟩ hPush32 (by evm_ov)
    |>.dup2 hDup2 (by evm_ov)
    |>.lt hLt (by evm_ov)
    |>.iszero hIszero (by evm_ov)
    |>.push2 okPc hPushOk (by evm_ov)
    |>.jumpiNT hJumpi hcond (by evm_ov)
  exact hFall.solcPush1Dup1Revert0 hPush0 hDupZero hRevert (by evm_ov)

/-- `EXTCODESIZE; ISZERO; DUP1; ISZERO; PUSH2 ok; JUMPI; …; JUMPDEST; POP`, target has code. -/
theorem Run.solcExtcodesizeGuardOk {okPc target : UInt256}
    (h : Run code s0 ⟨pc, target :: target :: R, mem, aw, rdata, w⟩ k C)
    (hcodeSize : extCodeSizeWord w.accounts target ≠ ⟨0⟩)
    (hExt : decode code pc = some (.EXTCODESIZE, .none))
    (hIszero0 : decode code (pc + ⟨1⟩) = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi : decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) = some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPop : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨okPc + ⟨1⟩ + ⟨1⟩, target :: R, mem, aw, rdata, w⟩ k' C' := by
  obtain ⟨_, _, hExt'⟩ := h.extcodesize hExt (by evm_ov)
  have hcond : UInt256.isZero (UInt256.isZero (extCodeSizeWord w.accounts target)) ≠ ⟨0⟩ := by
    rw [isZero_eq_zero_of_ne hcodeSize]; decide
  exact ⟨_, _, hExt'.iszero hIszero0 (by evm_ov)
    |>.dup1 hDup1 (by evm_ov)
    |>.iszero hIszero1 (by evm_ov)
    |>.push2 okPc hPush (by evm_ov)
    |>.jumpiT hJumpi hcond hjd (by evm_ov)
    |>.jumpdest hJumpdest (by evm_ov)
    |>.pop hPop (by evm_ov)⟩

/-- The `EXTCODESIZE` guard followed by `GAS`, stopping at the call opcode. -/
theorem Run.solcExtcodesizeGuardOkGas {okPc target : UInt256}
    (h : Run code s0 ⟨pc, target :: target :: R, mem, aw, rdata, w⟩ k C)
    (hcodeSize : extCodeSizeWord w.accounts target ≠ ⟨0⟩)
    (hExt : decode code pc = some (.EXTCODESIZE, .none))
    (hIszero0 : decode code (pc + ⟨1⟩) = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi : decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) = some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPop : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hGas : decode code (okPc + ⟨1⟩ + ⟨1⟩) = some (.GAS, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ gasWord k' C', Run code s0 ⟨okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩, gasWord :: target :: R, mem, aw, rdata, w⟩
      k' C' := by
  obtain ⟨_, _, hReady⟩ := h.solcExtcodesizeGuardOk hcodeSize hExt hIszero0 hDup1 hIszero1 hPush
    hJumpi hjd hJumpdest hPop hov
  obtain ⟨gasWord, hGas'⟩ := hReady.gas hGas (by evm_ov)
  exact ⟨gasWord, _, _, hGas'⟩

/-- The `EXTCODESIZE` guard with no code at the target: `revert(0,0)`. -/
theorem Run.solcExtcodesizeGuardMissing {okPc target : UInt256}
    (h : Run code s0 ⟨pc, target :: target :: R, mem, aw, rdata, w⟩ k C)
    (hcodeSize : extCodeSizeWord w.accounts target = ⟨0⟩)
    (hExt : decode code pc = some (.EXTCODESIZE, .none))
    (hIszero0 : decode code (pc + ⟨1⟩) = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi : decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) = some (.JUMPI, .none))
    (hPush0 : decode code (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩)
        = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hDupZero : decode code ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩)
        + UInt256.ofNat 2) = some (.DUP1, .none))
    (hRevert : decode code (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩)
        + UInt256.ofNat 2) + ⟨1⟩) = some (.REVERT, .none))
    (hov : R.length + 4 ≤ 1024) :
    Reverted code s0 ByteArray.empty := by
  obtain ⟨_, _, hExt'⟩ := h.extcodesize hExt (by evm_ov)
  have hcond : UInt256.isZero (UInt256.isZero (extCodeSizeWord w.accounts target)) = ⟨0⟩ := by
    rw [hcodeSize]; decide
  exact (hExt'.iszero hIszero0 (by evm_ov)
    |>.dup1 hDup1 (by evm_ov)
    |>.iszero hIszero1 (by evm_ov)
    |>.push2 okPc hPush (by evm_ov)
    |>.jumpiNT hJumpi hcond (by evm_ov)).solcPush1Dup1Revert0 hPush0 hDupZero hRevert (by evm_ov)

/-- `ISZERO; DUP1; ISZERO; PUSH2 ok; JUMPI; …; JUMPDEST; POP` on a nonzero call status. -/
theorem Run.solcCallSuccessGuardOk {okPc status : UInt256}
    (h : Run code s0 ⟨pc, status :: R, mem, aw, rdata, w⟩ k C)
    (hstatus : status ≠ ⟨0⟩)
    (hIszero0 : decode code pc = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi : decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) = some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPop : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', Run code s0 ⟨okPc + ⟨1⟩ + ⟨1⟩, R, mem, aw, rdata, w⟩ k' C' := by
  have hcond : UInt256.isZero (UInt256.isZero status) ≠ ⟨0⟩ := by
    rw [isZero_eq_zero_of_ne hstatus]; decide
  exact ⟨_, _, h.iszero hIszero0 (by evm_ov)
    |>.dup1 hDup1 (by evm_ov)
    |>.iszero hIszero1 (by evm_ov)
    |>.push2 okPc hPush (by evm_ov)
    |>.jumpiT hJumpi hcond hjd (by evm_ov)
    |>.jumpdest hJumpdest (by evm_ov)
    |>.pop hPop (by evm_ov)⟩

/-- The revert-bubbling tail `RETURNDATASIZE; PUSH1 0; DUP1; RETURNDATACOPY; RETURNDATASIZE;
    PUSH1 0; REVERT` copies the callee's return data to `mem[0]` and reverts with exactly it
    (as the EVM reads it back: the whole buffer once it is below `2^64` bytes). -/
theorem solcBubbledRevertData_eq (mem rdata : ByteArray) (h64 : rdata.size < 2 ^ 64) :
    (rdata.write 0 mem 0 (UInt256.ofNat rdata.size).toNat).readWithPadding 0
        (UInt256.ofNat rdata.size).toNat = rdata := by
  have hn : (UInt256.ofNat rdata.size).toNat = rdata.size :=
    ulit_toNat' _ (lt_trans h64 (by decide))
  rw [hn]
  by_cases hz : rdata.size = 0
  · rw [hz, byteArray_readWithPadding_zero, byteArray_eq_empty_of_size_eq_zero rdata hz]
  · rw [write0_read_back_gen rdata mem rdata.size hz (le_refl _) h64, byteArray_extract_self]

/-- Zero call status: the revert-bubbling tail, with the revert data as the EVM builds it. -/
theorem Run.solcCallSuccessGuardMissingRaw {okPc status : UInt256}
    (h : Run code s0 ⟨pc, status :: R, mem, aw, rdata, w⟩ k C)
    (hstatus : status = ⟨0⟩)
    (hIszero0 : decode code pc = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi : decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) = some (.JUMPI, .none))
    (hReturndatasize : decode code (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩)
        = some (.RETURNDATASIZE, .none))
    (hPush0 : decode code ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩)
        = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hDupZero : decode code (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩)
        + UInt256.ofNat 2) = some (.DUP1, .none))
    (hReturndatacopy : decode code ((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩)
        + UInt256.ofNat 2) + ⟨1⟩) = some (.RETURNDATACOPY, .none))
    (hReturndatasizeRevert : decode code
        (((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩)
          + ⟨1⟩) = some (.RETURNDATASIZE, .none))
    (hPushRevert0 : decode code
        ((((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩)
          + ⟨1⟩) + ⟨1⟩) = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hRevert : decode code
        (((((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩)
          + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) = some (.REVERT, .none))
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    Reverted code s0 ((rdata.write 0 mem 0 (UInt256.ofNat rdata.size).toNat).readWithPadding 0
      (UInt256.ofNat rdata.size).toNat) := by
  have hcond : UInt256.isZero (UInt256.isZero status) = ⟨0⟩ := by rw [hstatus]; decide
  have hCopyReady := h.iszero hIszero0 (by evm_ov)
    |>.dup1 hDup1 (by evm_ov)
    |>.iszero hIszero1 (by evm_ov)
    |>.push2 okPc hPush (by evm_ov)
    |>.jumpiNT hJumpi hcond (by evm_ov)
    |>.returndatasize hReturndatasize (by evm_ov)
    |>.push1 ⟨0⟩ hPush0 (by evm_ov)
    |>.dup1 hDupZero (by evm_ov)
  obtain ⟨_, _, hCopied⟩ := hCopyReady.returndatacopyVar hReturndatacopy
    (by show (⟨0⟩ : UInt256).toNat + (UInt256.ofNat rdata.size).toNat ≤ rdata.size
        rw [ulit_toNat' _ hrdataSize]; simp)
    (by evm_ov)
  have hRev := hCopied.returndatasize hReturndatasizeRevert (by evm_ov)
    |>.push1 ⟨0⟩ hPushRevert0 (by evm_ov)
  exact hRev.rev _ _ hRevert (fun s haw hstk => by rw [memExpRevertZeroOff s hstk, haw]) rfl
    (by evm_ov)

/-- Zero call status: the run reverts with the callee's return data. -/
theorem Run.solcCallSuccessGuardMissing {okPc status : UInt256}
    (h : Run code s0 ⟨pc, status :: R, mem, aw, rdata, w⟩ k C)
    (hstatus : status = ⟨0⟩)
    (hIszero0 : decode code pc = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi : decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) = some (.JUMPI, .none))
    (hReturndatasize : decode code (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩)
        = some (.RETURNDATASIZE, .none))
    (hPush0 : decode code ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩)
        = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hDupZero : decode code (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩)
        + UInt256.ofNat 2) = some (.DUP1, .none))
    (hReturndatacopy : decode code ((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩)
        + UInt256.ofNat 2) + ⟨1⟩) = some (.RETURNDATACOPY, .none))
    (hReturndatasizeRevert : decode code
        (((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩)
          + ⟨1⟩) = some (.RETURNDATASIZE, .none))
    (hPushRevert0 : decode code
        ((((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩)
          + ⟨1⟩) + ⟨1⟩) = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hRevert : decode code
        (((((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩)
          + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) = some (.REVERT, .none))
    (hrdata64 : rdata.size < 2 ^ 64)
    (hov : R.length + 5 ≤ 1024) :
    Reverted code s0 rdata := by
  have hraw := h.solcCallSuccessGuardMissingRaw hstatus hIszero0 hDup1 hIszero1 hPush hJumpi
    hReturndatasize hPush0 hDupZero hReturndatacopy hReturndatasizeRevert hPushRevert0 hRevert
    (lt_trans hrdata64 (by decide)) hov
  rwa [solcBubbledRevertData_eq mem rdata hrdata64] at hraw

/-! ## `STATICCALL`

Same opaque `Θ` shape as `Run.call`, with `perm := false` and no value. -/

/-- The `Θ` invocation of a `STATICCALL` from the cursor world `w`. -/
abbrev staticcallTheta (s0 : State) (w : World) (A_in : Substate) (target callGas : UInt256)
    (input : ByteArray) :=
  Ethereum.EVM.Θ s0.executionEnv.blobVersionedHashes w.created s0.genesisBlockHeader s0.blocks
    w.accounts s0.σ₀ A_in (AccountAddress.ofUInt256 (UInt256.ofNat s0.executionEnv.codeOwner))
    s0.executionEnv.sender (AccountAddress.ofUInt256 target)
    (toExecute w.accounts (AccountAddress.ofUInt256 target)) callGas
    (UInt256.ofNat s0.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩ input (s0.executionEnv.depth + 1)
    s0.executionEnv.header false

set_option maxHeartbeats 1000000 in
theorem Run.solcStaticcall {gasArg target inOffset inSize outOffset outSize : UInt256}
    {t : List UInt256}
    (h : Run code s0 ⟨pc, gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: t,
      mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.STATICCALL, .none))
    (hdepth : s0.executionEnv.depth.val < 1024) (hov : t.length + 1 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (g'' : UInt256)
      (A_in A' : Substate) (z : Bool) (o : ByteArray) (callGas : UInt256) (k' C' : ℕ),
      A_in.logSeries = w.logs
      ∧ (cA', σ', g'', A', z, o) = staticcallTheta s0 w A_in target callGas
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
  have hd : decode s.executionEnv.code s.machineState.pc = some (.STATICCALL, .none) := by
    rw [hcode, hpc]; exact hdec
  have hdepth' : s.executionEnv.depth.val < 1024 := by rw [hee]; exact hdepth
  have st := step_staticcall s hd
  rw [hstk] at st
  have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 - 6 + 1 > 1024) = False := eq_false (by omega)
  have hdepthLt : s.executionEnv.depth < 1024 := by rw [Fin.lt_def]; exact hdepth'
  have hbal : ∀ y : UInt256, (({val := 0} : UInt256) ≤ y) = True := fun y => eq_true (Fin.zero_le _)
  have hgtF : ∀ y : UInt256, (({val := 0} : UInt256) > y) = False :=
    fun y => eq_false (Fin.not_lt_zero _)
  have hdeqF : (s.executionEnv.depth == 1024) = false := by
    rw [beq_eq_false_iff_ne]; intro hh; rw [hh] at hdepth'; exact absurd hdepth' (by decide)
  simp only [List.length_cons, hovF, hdepthLt, hbal, hgtF, hdeqF, and_true, if_true,
    Bool.or_false] at st
  rw [collapse_two_stage, hcode] at st
  have hfuel : (budget s0).toNat + 1 - k = ((budget s0).toNat - k) + 1 := by omega
  have hXP := hX.trans (hfuel.symm ▸ X_peel (f := (budget s0).toNat - k) st)
  split at hXP
  · exact ⟨_, _, _, { (default : Substate) with logSeries := w.logs }, _, _, _, ⟨0⟩, k, C, rfl, rfl,
      Or.inl hXP,
      Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)⟩
  · rename_i hP
    set mc := memoryExpansionCost s Operation.STATICCALL with hmc
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
      s.executionEnv.header false with hθs
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
        (s.executionEnv.depth + 1) s.executionEnv.header false
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
        cg (UInt256.ofNat s.executionEnv.gasPrice) { val := 0 } { val := 0 }
        (s.executionEnv.depth + 1) s.executionEnv.header false
        (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)

set_option maxHeartbeats 1000000 in
/-- `STATICCALL` at the call-depth limit: `Θ` is not invoked, status `0`. -/
theorem Run.solcStaticcallDepthLimit {gasArg target inOffset inSize outOffset outSize : UInt256}
    {t : List UInt256}
    (h : Run code s0 ⟨pc, gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: t,
      mem, aw, rdata, w⟩ k C)
    (hdec : decode code pc = some (.STATICCALL, .none))
    (hdepth : s0.executionEnv.depth = 1024) (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', Run code s0 (noCallCursor pc t mem aw inOffset inSize outOffset outSize w) k' C' := by
  rcases h with hoog | ⟨s, hX, hcode, hcur, hgas, hk, hC, hst⟩
  · exact ⟨k, C, Or.inl hoog⟩
  obtain ⟨hpc, hstk, hmem, haw, hrdata, hcA, hσ, hlogs⟩ := cursorOf_eq.mp hcur
  have hee := hst.1
  have hd : decode s.executionEnv.code s.machineState.pc = some (.STATICCALL, .none) := by
    rw [hcode, hpc]; exact hdec
  have hdepth1024 : s.executionEnv.depth = 1024 := by rw [hee]; exact hdepth
  have st := step_staticcall s hd
  rw [hstk] at st
  have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 - 6 + 1 > 1024) = False := eq_false (by omega)
  have hdepthF : (s.executionEnv.depth < 1024) = False :=
    eq_false (by rw [hdepth1024]; exact lt_irrefl _)
  have hbal : ∀ y : UInt256, (({val := 0} : UInt256) ≤ y) = True := fun y => eq_true (Fin.zero_le _)
  have hgtF : ∀ y : UInt256, (({val := 0} : UInt256) > y) = False :=
    fun y => eq_false (Fin.not_lt_zero _)
  have hdeqT : (s.executionEnv.depth == 1024) = true := by rw [beq_iff_eq]; exact hdepth1024
  simp only [List.length_cons, hovF, if_false, hdepthF, hbal, hgtF, hdeqT, and_false, Bool.or_true,
    if_true] at st
  rw [collapse_two_stage, hcode] at st
  have hfuel : (budget s0).toNat + 1 - k = ((budget s0).toNat - k) + 1 := by omega
  have hXP := hX.trans (hfuel.symm ▸ X_peel (f := (budget s0).toNat - k) st)
  set mc := memoryExpansionCost s Operation.STATICCALL with hmc
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

end Reasoning.Trace
