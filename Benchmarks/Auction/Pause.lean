import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

def auctionPausedTopic : UInt256 :=
  ⟨0x62e78cea01bee320cd4e420270b5ea74000d11b0c9f74754ebdbfc544b05a258⟩

def auctionPauseOnlyOwnerStringWord : UInt256 :=
  ⟨0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572⟩

def auctionPausablePausedRawStringWord : UInt256 :=
  ⟨0x14185d5cd8589b194e881c185d5cd959⟩

def auctionPausablePausedStringWord : UInt256 :=
  ⟨0x5061757361626c653a2070617573656400000000000000000000000000000000⟩

theorem auctionDispatch_pause {I : ExecutionEnv} (hsel : selIs I (auctionSelBytes 10)) :
    dispatchMsg auctionContract I.calldata = some pauseTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition, createBidTransition, settleAndCreateTransition,
      settleAuctionTransition])
    (post := [unpauseTransition, setTimeBufferTransition, setReservePriceTransition,
      setMinBidIncTransition, transferOwnershipTransition, renounceOwnershipTransition,
      ownerGetter, pausedGetter, nounsGetter, wethGetter, timeBufferGetter, reservePriceGetter,
      minBidIncGetter, durationGetter, auctionGetter])
    (ti := pauseTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 10 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, initializeSelectorBytes, createBidSelectorBytes,
        settleAndCreateSelectorBytes, settleAuctionSelectorBytes, hcd, auctionSelBytes]
      native_decide
  · rw [selectorOf, pauseSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_pause {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (pauseTransition.params.map Param.name)
        (transitionSignature pauseTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode auctionConfig.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem evalExpr_pause_owner (evm : EVM.State) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
        evm (.storage ownerRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef auctionConfig
      { contract := auctionContract, locals := ∅ } evm ownerRef =
        .ok { base := "_owner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address) (hbase := by simp)
    (her := her) (hty := hty) (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    simpa [auctionAddrLoc] using auctionStorageLocLoad_address_offset0 evm ⟨151⟩)

theorem evalExpr_pause_sender (evm : EVM.State) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
      evm sender = .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_pause_owner_eq_true (evm : EVM.State)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
      evm (.binary .eq sender (.storage ownerRef)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_pause_sender, evalExpr_pause_owner, bind, EvalResult.bind,
    evalBinaryOp?]
  rw [auctionMaskedAddress_eq_source_of_word_eq (I := evm.executionEnv) howner]
  simp [BEq.beq]

theorem evalExpr_pause_owner_eq_false (evm : EVM.State)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask ≠
        auctionSourceWord evm.executionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
      evm (.binary .eq sender (.storage ownerRef)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_pause_sender, evalExpr_pause_owner, bind, EvalResult.bind,
    evalBinaryOp?]
  have haddr :
      evm.executionEnv.source ≠
        AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩)
            solcAddrMask).toNat := by
    intro haddr
    exact howner (auctionWord_eq_of_maskedAddress_eq_source haddr.symm)
  rw [show ((.address evm.executionEnv.source : Value) ==
          .address (AccountAddress.ofNat
            (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩)
              solcAddrMask).toNat)) = false by
    simp [BEq.beq, haddr]]

theorem evalExpr_pause_true (evm : EVM.State) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ } evm (.boolLit true) =
      .ok (.bool true) := by
  simp [evalExpr?, pure]

theorem evalExpr_pause_paused_false (evm : EVM.State)
    (hzero :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
      evm (.storage pausedRef) = .ok (.bool false) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := ∅ } evm
      pausedRef = .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool) (hbase := by simp) (her := her) (hty := hty)
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    simpa [auctionBoolLoc, boolOffset0Loc] using
      auctionStorageLocLoad_bool_offset0_false evm ⟨51⟩ hzero)

theorem evalExpr_pause_paused_true (evm : EVM.State)
    (hnz :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
      evm (.storage pausedRef) = .ok (.bool true) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := ∅ } evm
      pausedRef = .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool) (hbase := by simp) (her := her) (hty := hty)
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (by
    simpa [auctionBoolLoc, boolOffset0Loc] using
      auctionStorageLocLoad_bool_offset0_true evm ⟨51⟩ hnz)

theorem evalExpr_pause_notPaused_true (evm : EVM.State)
    (hzero :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
      evm (.unary .not (.storage pausedRef)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, evalExpr_pause_paused_false evm hzero, evalUnaryOp?]
  rfl

theorem evalExpr_pause_notPaused_false (evm : EVM.State)
    (hnz :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    evalExpr? auctionConfig { contract := auctionContract, locals := ∅ }
      evm (.unary .not (.storage pausedRef)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, evalExpr_pause_paused_true evm hnz, evalUnaryOp?]
  rfl

theorem auctionPauseAssign (evm : EVM.State) :
    assignStorageRef? auctionConfig { contract := auctionContract, locals := ∅ } evm .storage
        pausedRef (.bool true) =
      .ok ({ contract := auctionContract, locals := ∅ }, auctionPausePostState evm) := by
  have her : evalStorageRef auctionConfig { contract := auctionContract, locals := ∅ } evm
      pausedRef = .ok { base := "_paused", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pausedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? auctionContract.storage
      ({ base := "_paused", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  have hstore :
      storageLocStore evm (auctionBoolLoc ⟨51⟩) (.bool true) =
        some (auctionPausePostState evm) := by
    simpa [auctionBoolLoc, boolOffset0Loc, auctionPausePostState, auctionPausedSetTrueWord,
      setBoolOffset0Word] using
      auctionStorageLocStore_bool_true_offset0 evm ⟨51⟩
  exact assignStorageRef_storage_scalar_value (cfg := auctionConfig)
    (solm := { contract := auctionContract, locals := ∅ }) (evm := evm)
    (evm' := auctionPausePostState evm) (slot := pausedRef)
    (er := { base := "_paused", steps := [] }) (ty := .elem .bool)
    (loc := auctionBoolLoc ⟨51⟩) (value := .bool true) (by simp) her hty (by rfl)
    (by trivial) hstore

theorem auctionPauseBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hzero :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ =
        ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ pauseTransition.body
      (.returned { contract := auctionContract, locals := ∅ } (auctionPausePostState evm) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_notPaused_true evm hzero)) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (evalExpr_pause_true evm) (auctionPauseAssign evm))
    ExecBlock.nil

theorem auctionPauseBodyReverts_callvalue (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ pauseTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false hwv))

theorem auctionPauseBodyReverts_owner (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask ≠
        auctionSourceWord evm.executionEnv) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ pauseTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_pause_owner_eq_false evm howner))

theorem auctionPauseBodyReverts_paused (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨151⟩) solcAddrMask =
        auctionSourceWord evm.executionEnv)
    (hnz :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅ pauseTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_owner_eq_true evm howner)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_pause_notPaused_false evm hnz))

theorem auctionReachPauseBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 10)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨685⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0x84, 0x56, 0xcb, 0x59]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0x8456cb59⟩ :=
    auctionSelWord_eq_of_beq I hsz 0x84 0x56 0xcb 0x59 ⟨0x8456cb59⟩
      (by native_decide) hsel'
  obtain ⟨_, _, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hroot :
      UInt256.gt (armSelNat auctionBytecode auctionSplitPc) (auctionSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h29 := auctionSelectorSplitNotTakenTo hsplit auctionSplitWellFormed hroot
      auctionRootSplitNextPc (by simp)
  have hupper :
      UInt256.gt (armSelNat auctionBytecode auctionUpperSplitPc) (auctionSelWord I) ≠
        ⟨0⟩ := by
    rw [hword]
    native_decide
  have h98 := auctionSelectorSplitTakenTo h29 auctionUpperSplitWellFormed hupper
      auctionUpperSplitTargetPc
    (by jump_dest) (by simp)
  have h99 := h98.jumpdest (by native_decide) (by simp)
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionUpperLowFirstArmPc 0))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hrd := h99.selectorArmTakenAuto (auctionUpperLowArmsWellFormed 0 (by omega)) htake
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [auctionUpperLowFirstArmPc, nthArmPc, armTgt, pushAt] using hrd⟩

theorem auctionX_pause_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨685⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd685⟩ := hreach
  exact evm_run rd685 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨696⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem auctionPauseX_toBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨685⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2080⟩
      [⟨413⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd685⟩ := hreach
  exact ⟨_, _, evm_run rd685 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨696⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨413⟩, push2 ⟨2080⟩, jump (by jump_dest)]⟩

theorem auctionPauseX_toWhenNotPaused {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask = auctionSourceWord I)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨685⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3655⟩
      [⟨1163⟩, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2080⟩ := auctionPauseX_toBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := auctionSelWord I) hreach hwv
  have rd2095₀ := evm_run rd2080 with [
    jumpdest, push1 ⟨151⟩]
  obtain ⟨_, _, rd2083₀⟩ := rd2095₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2084⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2084⟩
      [auctionSlotWord ⟨151⟩ σ I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2083₀⟩
  have rd2095₁ := evm_run rd2084 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, caller, eq]
  have hmask :
      UInt256.land solcAddrMask (auctionSlotWord ⟨151⟩ σ I) = auctionSourceWord I := by
    rw [u256_land_comm, howner]
  have heq :
      UInt256.eq (UInt256.ofNat I.source.val)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (auctionSlotWord ⟨151⟩ σ I)) = ⟨1⟩ := by
    change UInt256.eq (auctionSourceWord I)
      (UInt256.land solcAddrMask (auctionSlotWord ⟨151⟩ σ I)) = ⟨1⟩
    rw [hmask, u256_eq_refl]
  have rd2095 := rd2095₁
  rw [heq] at rd2095
  have rd2122 := evm_run rd2095 with [
    push2 ⟨2122⟩, jumpiT (by decide) (by jump_dest), jumpdest]
  exact ⟨_, _, evm_run rd2122 with [push2 ⟨1163⟩, push2 ⟨3655⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
theorem auctionX_pause_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask = auctionSourceWord I)
    (hzero : auctionPausedWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨685⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, auctionPausePostMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd3655⟩ := auctionPauseX_toWhenNotPaused (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hwv howner hreach
  have rd3663₀ := evm_run rd3655 with [jumpdest, push1 ⟨51⟩]
  obtain ⟨_, _, rd3659₀⟩ := rd3663₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3659⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3659⟩
      [auctionSlotWord ⟨51⟩ σ I, ⟨1163⟩, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3659₀⟩
  have rd3663 := evm_run rd3659 with [push1 ⟨255⟩, and, iszero]
  have hmask : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) = auctionPausedWord σ I := by
    rw [auctionPausedWord, u256_land_comm]
  have hcond : UInt256.isZero (UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I)) ≠ ⟨0⟩ := by
    rw [hmask, hzero]
    decide
  have rd3725 := evm_run rd3663 with [
    push2 ⟨3725⟩, jumpiT hcond (by jump_dest), jumpdest]
  have rd3734₀ := evm_run rd3725 with [push1 ⟨51⟩, dup1]
  obtain ⟨_, _, rd3730₀⟩ := rd3734₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3730⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3730⟩
      [auctionSlotWord ⟨51⟩ σ I, ⟨51⟩, ⟨1163⟩, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3730₀⟩
  have rd3737₀ := evm_run rd3730 with [push1 ⟨255⟩, not, and, push1 ⟨1⟩]
  have rd3737₁ := rd3737₀
  have hland :
      UInt256.land (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨51⟩ σ I) =
        UInt256.land (auctionSlotWord ⟨51⟩ σ I) (UInt256.lnot ⟨255⟩) := by
    exact u256_land_comm (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨51⟩ σ I)
  rw [hland] at rd3737₁
  have rd3737₂ := RD.lor rd3737₁ (by native_decide) (by evm_ov)
  have hlor :
      UInt256.lor ⟨1⟩
          (UInt256.land (auctionSlotWord ⟨51⟩ σ I) (UInt256.lnot ⟨255⟩)) =
        auctionPausedSetTrueWord (auctionSlotWord ⟨51⟩ σ I) := by
    unfold auctionPausedSetTrueWord
    exact u256_lor_comm ⟨1⟩
      (UInt256.land (auctionSlotWord ⟨51⟩ σ I) (UInt256.lnot ⟨255⟩))
  rw [hlor] at rd3737₂
  have rd3738 := evm_run rd3737₂ with [swap1]
  obtain ⟨_, _, rd3739₀⟩ := rd3738.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3739⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3739⟩
      [⟨1163⟩, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, auctionPausePostMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionPausePostMap] using rd3739₀⟩
  have rd3772 := rd3739.pushConst auctionPausedTopic (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd2971 := evm_run rd3772 with [push2 ⟨2971⟩, caller, swap1, jump (by jump_dest)]
  have rd2988₀ := evm_run rd2971 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2, and, dup2]
  have rd2988 := rd2988₀
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  rw [haddrMask] at rd2988
  have hcaller : UInt256.land (UInt256.ofNat I.source.val) solcAddrMask = auctionSourceWord I := by
    rw [u256_land_comm]
    simpa [auctionSourceWord] using solcAddrMask_clean_left (auctionSourceWord_canonical I)
  rw [hcaller] at rd2988
  have rd2991 := evm_run rd2988 with [
    raw mstore 6 (auctionEventMem I) (UInt256.ofNat 5) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd2998₀ := evm_run rd2991 with [
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (auctionEventMem_mload64 I) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have hlen32 : ((⟨32⟩ : UInt256) + ⟨128⟩).sub ⟨128⟩ = ⟨32⟩ := by
    decide
  have rd2998 := rd2998₀
  rw [hlen32] at rd2998
  have rd2999 := RD.log1 0 (UInt256.ofNat 5) rd2998 (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by decide) (by evm_ov)
  have rd1163 := evm_run rd2999 with [jump (by jump_dest), jumpdest]
  have rd413 := evm_run rd1163 with [jump (by jump_dest), jumpdest]
  exact rd413.stop (by native_decide) (by evm_ov)

theorem auctionX_pause_revert_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask ≠ auctionSourceWord I)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨685⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2080⟩ := auctionPauseX_toBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := auctionSelWord I) hreach hwv
  have rd2095₀ := evm_run rd2080 with [
    jumpdest, push1 ⟨151⟩]
  obtain ⟨_, _, rd2083₀⟩ := rd2095₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2084⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2084⟩
      [auctionSlotWord ⟨151⟩ σ I, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2083₀⟩
  have rd2095₁ := evm_run rd2084 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, caller, eq]
  have hmask :
      UInt256.land solcAddrMask (auctionSlotWord ⟨151⟩ σ I) ≠ auctionSourceWord I := by
    intro hmask
    exact howner (by
      rw [u256_land_comm] at hmask
      exact hmask)
  have hneq :
      UInt256.ofNat I.source.val ≠
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (auctionSlotWord ⟨151⟩ σ I) := by
    change auctionSourceWord I ≠ UInt256.land solcAddrMask (auctionSlotWord ⟨151⟩ σ I)
    exact fun h => hmask h.symm
  have heq :
      UInt256.eq (UInt256.ofNat I.source.val)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (auctionSlotWord ⟨151⟩ σ I)) = ⟨0⟩ := by
    exact u256_eq_of_ne hneq
  have rd2095 := rd2095₁
  rw [heq] at rd2095
  have rd2102 := evm_run rd2095 with [
    push2 ⟨2122⟩, jumpiNT (by decide),
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd2106 := rd2102.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by native_decide) (by evm_ov)
  have rd5522 := evm_run rd2106 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcReturnMem ⟨0x08c379a000000000000000000000000000000000000000000000000000000000⟩)
      (UInt256.ofNat 5) (by native_decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨4⟩, add, push2 ⟨994⟩, swap1, push2 ⟨5522⟩, jump (by jump_dest)]
  have rd5532 := evm_run rd5522 with [
    jumpdest, push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup2, dup2, add,
    raw mstore 3 (solcErrorStringMem2 ⟨32⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd5565 := rd5532.pushConst auctionPauseOnlyOwnerStringWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd5574₀ := evm_run rd5565 with [
    push1 ⟨64⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem3 ⟨32⟩ auctionPauseOnlyOwnerStringWord solcFreePtrMem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨96⟩, add, swap1]
  have rd5574 := rd5574₀
  rw [show (⟨96⟩ : UInt256) + (⟨4⟩ + ⟨128⟩) = ⟨228⟩ by decide] at rd5574
  have rd994 := evm_run rd5574 with [jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨32⟩ auctionPauseOnlyOwnerStringWord
        solcFreePtrMem_size solcFreePtrMem_read64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨228⟩ : UInt256) ⟨128⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem auctionX_pause_revert_paused {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (auctionSlotWord ⟨151⟩ σ I) solcAddrMask = auctionSourceWord I)
    (hnz : auctionPausedWord σ I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨685⟩ [auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3655⟩ := auctionPauseX_toWhenNotPaused (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hwv howner hreach
  have rd3663₀ := evm_run rd3655 with [jumpdest, push1 ⟨51⟩]
  obtain ⟨_, _, rd3659₀⟩ := rd3663₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3659⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3659⟩
      [auctionSlotWord ⟨51⟩ σ I, ⟨1163⟩, ⟨413⟩, auctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3659₀⟩
  have rd3663 := evm_run rd3659 with [push1 ⟨255⟩, and, iszero]
  have hmask : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) = auctionPausedWord σ I := by
    rw [auctionPausedWord, u256_land_comm]
  have hcond : UInt256.isZero (UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I)) = ⟨0⟩ := by
    exact isZero_eq_zero_of_ne (by simpa [hmask] using hnz)
  have rd3667 := evm_run rd3663 with [
    push2 ⟨3725⟩, jumpiNT hcond]
  have rd3670 := evm_run rd3667 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd3674 := rd3670.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by native_decide) (by evm_ov)
  have rd3693 := evm_run rd3674 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨16⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (solcErrorStringMem2 ⟨16⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd3710 := rd3693.pushConst auctionPausablePausedRawStringWord
    (width := 16) (op := .PUSH16) (by decide) (by native_decide) (by evm_ov)
  have rd3713₀ := evm_run rd3710 with [push1 ⟨130⟩, shl]
  have hword :
      UInt256.shiftLeft auctionPausablePausedRawStringWord ⟨130⟩ =
        auctionPausablePausedStringWord := by
    native_decide
  have rd3713 := rd3713₀
  rw [hword] at rd3713
  have rd3721₀ := evm_run rd3713 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 3
      (solcErrorStringMem3 ⟨16⟩ auctionPausablePausedStringWord solcFreePtrMem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, add]
  have rd3721 := rd3721₀
  rw [show (⟨100⟩ : UInt256) + ⟨128⟩ = ⟨228⟩ by decide] at rd3721
  have rd994 := evm_run rd3721 with [push2 ⟨994⟩, jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨16⟩ auctionPausablePausedStringWord
        solcFreePtrMem_size solcFreePtrMem_read64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨228⟩ : UInt256) ⟨128⟩ = ⟨100⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem auctionPauseBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 10))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 10) rfl _hsel
  have hdispatch := auctionDispatch_pause _hsel
  have hdecode := auctionDecode_pause (I := I) hsz4
  have hreach := auctionReachPauseBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hcode hsz4 _hsize _hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
    let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hownerWord :
        auctionSlotWord ⟨151⟩ σ_evm I = auctionSlotWord ⟨151⟩ σ_solm I :=
      accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨151⟩ ⟨0⟩
    by_cases howner :
        UInt256.land (auctionSlotWord ⟨151⟩ σ_evm I) solcAddrMask = auctionSourceWord I
    · have hownerSolm :
          UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨151⟩)
              solcAddrMask =
            auctionSourceWord evmS.executionEnv := by
        have hmap :
            UInt256.land (auctionSlotWord ⟨151⟩ σ_solm I) solcAddrMask =
              auctionSourceWord I := by
          simpa [hownerWord] using howner
        simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
          auctionSourceWord] using hmap
      have hpausedWord :
          auctionSlotWord ⟨51⟩ σ_evm I = auctionSlotWord ⟨51⟩ σ_solm I :=
        accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨51⟩ ⟨0⟩
      by_cases hzero : auctionPausedWord σ_evm I = ⟨0⟩
      · have hzeroSolm :
            UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨51⟩)
                ⟨255⟩ =
              ⟨0⟩ := by
          have hmap : auctionPausedWord σ_solm I = ⟨0⟩ := by
            simpa [auctionPausedWord, hpausedWord] using hzero
          simpa [evmS, initState, auctionPausedWord, auctionSlotWord, Solm.EVM.storageLoad,
            State.lookupAccount] using hmap
        have hbody := auctionPauseBodyReturns evmS
          (by simp only [evmS, initState]; exact hwv) hownerSolm hzeroSolm
        have hpostAccountsEvm :
            accountMapEquiv (auctionPausePostMap σ_evm I)
              (auctionPausePostState evmE).accountMap := by
          apply accountMapEquiv.of_eq
          simp [auctionPausePostMap, auctionPausePostState, evmE, initState,
            storageStore_accountMap, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage]
        have hpostState :
            EVMStateEquiv (auctionPausePostState evmE) (auctionPausePostState evmS) := by
          have hσ : EVMStateEquiv evmE evmS := by
            exact EVMStateEquiv.initState _hAccounts
          exact hσ.storageStore_codeOwner ⟨51⟩ (by
            have hval :
                auctionPausedSetTrueWord (auctionSlotWord ⟨51⟩ σ_evm I) =
                  auctionPausedSetTrueWord (auctionSlotWord ⟨51⟩ σ_solm I) := by
              rw [hpausedWord]
            simpa [auctionPausePostState, evmE, evmS, initState, auctionSlotWord,
              Solm.EVM.storageLoad, State.lookupAccount] using hval)
        exact (auctionX_pause_success (g := Sat256.ofUInt256 g)
            _hperm hwv howner hzero hreach)
          |>.reEquivExecutionGenEVMStateEquiv _hcode hdispatch hdecode hbody
            (by simp [auctionPausePostState, evmE, initState, storageStore_createdAccounts])
            hpostAccountsEvm
            hpostState
            (returnEquiv.fallthrough rfl rfl (by native_decide))
      · have hnzSolm :
            UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨51⟩)
                ⟨255⟩ ≠
              ⟨0⟩ := by
          intro h
          apply hzero
          have hmap : auctionPausedWord σ_solm I = ⟨0⟩ := by
            simpa [evmS, initState, auctionPausedWord, auctionSlotWord, Solm.EVM.storageLoad,
              State.lookupAccount] using h
          simpa [auctionPausedWord, hpausedWord] using hmap
        have hbody := auctionPauseBodyReverts_paused evmS
          (by simp only [evmS, initState]; exact hwv) hownerSolm hnzSolm
        exact (auctionX_pause_revert_paused (g := Sat256.ofUInt256 g)
            hwv howner hzero hreach)
          |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
    · have hownerSolm :
          UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨151⟩)
              solcAddrMask ≠
            auctionSourceWord evmS.executionEnv := by
        intro h
        apply howner
        have hmap :
            UInt256.land (auctionSlotWord ⟨151⟩ σ_solm I) solcAddrMask =
              auctionSourceWord I := by
          simpa [evmS, initState, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
            auctionSourceWord] using h
        simpa [hownerWord] using hmap
      have hbody := auctionPauseBodyReverts_owner evmS
        (by simp only [evmS, initState]; exact hwv) hownerSolm
      exact (auctionX_pause_revert_owner (g := Sat256.ofUInt256 g) hwv howner hreach)
        |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
  · have hbody := auctionPauseBodyReverts_callvalue
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (by simpa only [initState] using hwv)
    exact (auctionX_pause_callvalue_ne hreach hwv)
      |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody

end Auction
