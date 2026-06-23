import Examples.OpenZeppelinBench.Pausable.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Pausable

/-! ## `pause()` -/

def pauseSenderWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

theorem pauseSenderWord_toNat (I : ExecutionEnv) :
    (pauseSenderWord I).toNat = I.source.val := by
  unfold pauseSenderWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem pauseSenderWord_canonical (I : ExecutionEnv) :
    (pauseSenderWord I).toNat < EVM.addressModulus := by
  rw [pauseSenderWord_toNat]
  exact I.source.isLt

-- PROMOTE -> Reasoning.EVMWord.
theorem pausableNat_lor_comm (a b : ℕ) : Nat.lor a b = Nat.lor b a := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (a ||| b).testBit i = (b ||| a).testBit i
  rw [Nat.testBit_or, Nat.testBit_or, Bool.or_comm]

-- PROMOTE -> Reasoning.EVMWord.
theorem pausableU256_lor_comm (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  apply u256_inj
  show Nat.lor a.toNat b.toNat % UInt256.size =
    Nat.lor b.toNat a.toNat % UInt256.size
  rw [pausableNat_lor_comm]

def pausedTopic : UInt256 :=
  ⟨0x62e78cea01bee320cd4e420270b5ea74000d11b0c9f74754ebdbfc544b05a258⟩

noncomputable def pauseEventMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (pauseSenderWord I)).write 0 solcFreePtrMem 128 32

theorem pauseEventMem_size (I : ExecutionEnv) : (pauseEventMem I).size = 160 := by
  simpa [pauseEventMem, solcReturnMem] using solcReturnMem_size (pauseSenderWord I)

theorem pauseEventMem_read64 (I : ExecutionEnv) :
    (pauseEventMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  simpa [pauseEventMem, solcReturnMem] using solcReturnMem_read64 (pauseSenderWord I)

theorem pauseEventMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (pauseEventMem I).size ∨
        (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 5) * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((pauseEventMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      (⟨128⟩ : UInt256) := by
  exact mloadFreePtrValue (by rw [pauseEventMem_size]; decide) (by decide) (pauseEventMem_read64 I)

theorem pausablePauseSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x84, 0x56, 0xcb, 0x59]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x84, 0x56, 0xcb, 0x59]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem pausableDispatch_pause {cd : ByteArray}
    (hsel : ((⟨#[0x84, 0x56, 0xcb, 0x59]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some pauseTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x84, 0x56, 0xcb, 0x59]⟩ : ByteArray) :=
    (pausableByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [guardedWhenNotPausedTransition, guardedWhenPausedTransition])
    (post := [pausedTransition, unpauseTransition]) rfl ?_
    (by rw [selectorOf, pauseSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, guardedWhenNotPausedSelectorBytes, hcd]; decide
  · rw [selectorOf, guardedWhenPausedSelectorBytes, hcd]; decide

theorem pausableDecode_pause {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (pauseTransition.params.map Param.name)
      (transitionSignature pauseTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem evalExpr_pause_paused (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := ∅ } evm (.storage pausedRef) =
      .ok (wordToElem .bool
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩)) := by
  have her : evalStorageRef config { contract := contract, locals := ∅ } evm
      pausedRef = .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool) (hbase := by simp) (her := her)
    (hty := hty) (hloc := by rfl), pausableStorageLocLoad_bool_offset0]

theorem evalExpr_pause_whenNotPaused_true (evm : EVM.State)
    (hzero :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩ =
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := ∅ } evm
      (.unary .not (.storage pausedRef)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_pause_paused, EvalResult.bind, bind]
  rw [hzero]
  rfl

theorem evalExpr_pause_whenNotPaused_false (evm : EVM.State)
    (hnz :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    evalExpr? config { contract := contract, locals := ∅ } evm
      (.unary .not (.storage pausedRef)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_pause_paused, EvalResult.bind, bind]
  have hbeq :
      ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩).val == 0) =
        false := by
    rw [beq_eq_false_iff_ne]
    intro h
    exact hnz (uint256_toNat_eq_zero (by simpa [UInt256.toNat] using congrArg Fin.val h))
  rw [wordToElem, hbeq]
  rfl

theorem evalExpr_pause_true (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := ∅ } evm (.boolLit true) =
      .ok (.bool true) := by
  simp [evalExpr?, pure]

theorem pauseAssign (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := ∅ } evm .storage pausedRef
        (.bool true) =
      .ok ({ contract := contract, locals := ∅ }, pausePostState evm) := by
  have her : evalStorageRef config { contract := contract, locals := ∅ } evm
      pausedRef = .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some boolSt := by
    decide
  have hstore :
      storageLocStore evm (boolLoc ⟨0⟩) (.bool true) = some (pausePostState evm) := by
    simpa [pausePostState] using pausableStorageLocStore_bool_true_offset0 evm ⟨0⟩
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := ∅ }) (evm := evm) (evm' := pausePostState evm)
    (slot := pausedRef) (er := { base := "_paused", steps := [] }) (ty := boolSt)
    (loc := boolLoc ⟨0⟩) (value := .bool true) (by simp) her hty (by rfl)
    (by trivial) hstore

theorem pausablePauseBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩ =
        ⟨0⟩) :
    ExecTransitionBody config contract evm ∅ pauseTransition.body
      (.returned { contract := contract, locals := ∅ } (pausePostState evm) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_pause_whenNotPaused_true evm hzero)) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (evalExpr_pause_true evm) (pauseAssign evm))
    ExecBlock.nil

theorem pausablePauseBodyReverts_paused (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnz :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    ExecTransitionBody config contract evm ∅ pauseTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_pause_whenNotPaused_false evm hnz))

-- PROMOTE -> Reasoning.Stepping / Reasoning.Reach: generic OR combinator.
theorem pausableOr_xstep {s : State} {code : ByteArray} {pcv a b : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.OR, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.lor a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.OR, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_or s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

-- PROMOTE -> Reasoning.Reach: generic OR combinator.
theorem pausableRDOr {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.OR, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.lor a b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => pausableOr_xstep hc hp hdec hs hov)

theorem pausableX_pause_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD pausableBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨125⟩ [pausableSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hzero : pausedWord σ I = ⟨0⟩) :
    RDret pausableBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, pausePostMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd125⟩ := hreach
  have rd159 := evm_run rd125 with [
    jumpdest, push2 ⟨97⟩, push2 ⟨159⟩, jump (by jump_dest), jumpdest]
  have rd272 := evm_run rd159 with [push2 ⟨157⟩, push2 ⟨272⟩, jump (by jump_dest)]
  have rd332 := evm_run rd272 with [jumpdest, push2 ⟨280⟩, push2 ⟨332⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd280⟩ :=
    RD.pausableWhenNotPausedPass (ret := ⟨280⟩)
      (R := [⟨157⟩, ⟨97⟩, pausableSelWord I]) rd332 hzero
      (by jump_dest) (by simp)
  have rd283 := evm_run rd280 with [jumpdest, push0, dup1]
  obtain ⟨_, _, rd284₀⟩ := rd283.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd284⟩ : ∃ k C, RD pausableBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨284⟩
      [pausedRawWord σ I, ⟨0⟩, ⟨157⟩, ⟨97⟩, pausableSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [pausedRawWord] using rd284₀⟩
  have rd288₀ := evm_run rd284 with [push1 ⟨255⟩, not, and, push1 ⟨1⟩]
  have rd288 := rd288₀
  have hland : UInt256.land (UInt256.lnot ⟨255⟩) (pausedRawWord σ I) =
      UInt256.land (pausedRawWord σ I) (UInt256.lnot ⟨255⟩) := by
    exact pausableU256_land_comm (UInt256.lnot ⟨255⟩) (pausedRawWord σ I)
  rw [hland] at rd288
  have rd291₀ := pausableRDOr rd288 (by decide) (by evm_ov)
  have rd291 := evm_run rd291₀ with [swap1]
  have hlor : UInt256.lor ⟨1⟩ (UInt256.land (pausedRawWord σ I) (UInt256.lnot ⟨255⟩)) =
      pausedSetTrueWord (pausedRawWord σ I) := by
    unfold pausedSetTrueWord
    exact pausableU256_lor_comm ⟨1⟩
      (UInt256.land (pausedRawWord σ I) (UInt256.lnot ⟨255⟩))
  rw [hlor] at rd291
  obtain ⟨_, _, rd293₀⟩ := rd291.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd293⟩ : ∃ k C, RD pausableBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨293⟩
      [⟨157⟩, ⟨97⟩, pausableSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, pausePostMap σ I) k C := by
    exact ⟨_, _, by simpa [pausePostMap] using rd293₀⟩
  have rd326 := rd293.pushConst pausedTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd243 := evm_run rd326 with [push2 ⟨243⟩, caller, swap1, jump (by jump_dest), jumpdest]
  have rd247 := evm_run rd243 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd258₀ := evm_run rd247 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2, and, dup2]
  have rd258 := rd258₀
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  rw [haddrMask] at rd258
  have hcaller : UInt256.land (UInt256.ofNat I.source.val) solcAddrMask = pauseSenderWord I := by
    rw [pausableU256_land_comm]
    simpa [pauseSenderWord] using solcAddrMask_clean_left (pauseSenderWord_canonical I)
  rw [hcaller] at rd258
  have rd260 := evm_run rd258 with [
    raw mstore 6 (pauseEventMem I) (UInt256.ofNat 5) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd270 := evm_run rd260 with [
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (pauseEventMem_mload64 I) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have hlen32 : ((⟨32⟩ : UInt256) + ⟨128⟩).sub ⟨128⟩ = ⟨32⟩ := by
    decide
  have rd270' := rd270
  rw [hlen32] at rd270'
  have rd271 := RD.log1 0 (UInt256.ofNat 5) rd270' (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by decide) (by evm_ov)
  have rd97 := evm_run rd271 with [jump (by jump_dest), jumpdest, jump (by jump_dest), jumpdest]
  exact rd97.stop (by decide) (by evm_ov)

theorem pausableX_pause_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD pausableBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨125⟩ [pausableSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : pausedWord σ I ≠ ⟨0⟩) :
    RDrev pausableBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd125⟩ := hreach
  have rd159 := evm_run rd125 with [
    jumpdest, push2 ⟨97⟩, push2 ⟨159⟩, jump (by jump_dest), jumpdest]
  have rd272 := evm_run rd159 with [push2 ⟨157⟩, push2 ⟨272⟩, jump (by jump_dest)]
  have rd332 := evm_run rd272 with [jumpdest, push2 ⟨280⟩, push2 ⟨332⟩, jump (by jump_dest)]
  exact RD.pausableWhenNotPausedRevert (ret := ⟨280⟩)
    (R := [⟨157⟩, ⟨97⟩, pausableSelWord I]) rd332 hnz
    (by simp)

theorem pausablePauseBody {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I}
    {g : UInt256}
    (hcode : I.code = pausableBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x84, 0x56, 0xcb, 0x59]⟩)
    (hreach : ∃ k C, RD pausableBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨125⟩
      [pausableSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hsz := pausablePauseSelector_size hsel
  have hd := pausableDispatch_pause (cd := I.calldata) hsel
  have hdec := pausableDecode_pause (I := I) hsz
  have hpaused :
      pausedWord σ_evm I = pausedWord σ_solm I := by
    unfold pausedWord pausedRawWord
    rw [accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩]
  by_cases hzero : pausedWord σ_evm I = ⟨0⟩
  · have hbody := pausablePauseBodyReturns
      (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv)
      (by
        have hzeroSolm : pausedWord σ_solm I = ⟨0⟩ := by
          simpa [hpaused] using hzero
        simpa [pausedWord, pausedRawWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
          using hzeroSolm)
    have hσPost : EVMStateEquiv
        (pausePostState (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I))
        (pausePostState (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)) := by
      have hσ : EVMStateEquiv
          (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) := by
        exact EVMStateEquiv.initState hAccounts
      exact hσ.storageStore_codeOwner ⟨0⟩ (by
        have hraw :
            pausedRawWord σ_evm I = pausedRawWord σ_solm I := by
          unfold pausedRawWord
          rw [accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩]
        simpa [pausePostState, initState, Solm.EVM.storageLoad, State.lookupAccount,
          pausedRawWord] using congrArg pausedSetTrueWord hraw)
    exact (pausableX_pause_success (g := Sat256.ofUInt256 g) hperm hreach hzero)
      |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
        (by rw [pausePostState_createdAccounts]; simp [initState])
        (accountMapEquiv.of_eq (by
          rw [pausePostState_accountMap]
          simp [pausePostMap, initState, pausedRawWord, Solm.EVM.storageLoad,
            State.lookupAccount, Account.lookupStorage]))
        hσPost
        (returnEquiv.void rfl rfl rfl)
  · have hbody := pausablePauseBodyReverts_paused
      (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv)
      (by
        have hnzSolm : pausedWord σ_solm I ≠ ⟨0⟩ := by
          simpa [hpaused] using hzero
        simpa [pausedWord, pausedRawWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
          using hnzSolm)
    exact (pausableX_pause_revert (g := Sat256.ofUInt256 g) hreach hzero)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end OpenZeppelinBench.Pausable
