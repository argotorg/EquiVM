import Benchmarks.Dss.Cure.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Cure

/-! ## `lift(address)` -/

abbrev liftSrc (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev liftKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev liftLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "src" (.address (liftSrc I))

abbrev liftPosEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "pos", steps := [.mindex (.address (liftSrc I))] }

abbrev liftPosSlotFor (I : ExecutionEnv) : UInt256 :=
  posSlot (.address (liftSrc I))

abbrev liftSrcsEvaledRef : EvaledStorageRef :=
  { base := "srcs", steps := [] }

abbrev liftSrcsLengthRef : EvaledStorageRef :=
  { base := "srcs", steps := [.length] }

-- Placeholder-free slot abbreviations for the EVM side of `srcs.push(src)`.
abbrev liftSrcsLenWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  cureSlotWord ⟨2⟩ σ I

abbrev liftSrcsElemEvaledRef (σ : AccountMap) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "srcs", steps := [.aindex (.int (Int.ofNat (liftSrcsLenWord σ I).toNat))] }

abbrev liftSrcsElemSlotForLen (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  srcsDataSlot + liftSrcsLenWord σ I

abbrev liftAfterSrcsLengthState (evm : EVM.State) (len : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩ (len + ⟨1⟩)

abbrev liftAfterSrcsElemState (evm : EVM.State) (len : UInt256)
    (srcWord : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (srcsDataSlot + len)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (srcsDataSlot + len))
      srcWord)

abbrev liftAfterPosState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (liftPosSlotFor I)
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)

abbrev liftLengthAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨2⟩ (liftSrcsLenWord σ I + ⟨1⟩)

abbrev liftElemAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  let σLen := liftLengthAccountMap σ I
  let elemSlot := liftSrcsElemSlotForLen σ I
  sstoreAccountMap I.codeOwner σLen elemSlot
    (setAddressOffset0Word (solcSlotWord σLen I elemSlot) (liftKey I))

abbrev liftFinalAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  let σElem := liftElemAccountMap σ I
  sstoreAccountMap I.codeOwner σElem (liftPosSlotFor I) (solcSlotWord σElem I ⟨2⟩)

theorem liftPosSlotFor_eq (I : ExecutionEnv) :
    liftPosSlotFor I = solcMappingSlot ⟨5⟩ (liftKey I) := by
  unfold liftPosSlotFor liftSrc liftKey posSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem liftSrcsElemSlotForLen_eq (σ : AccountMap) (I : ExecutionEnv) :
    srcElemSlot (.int (Int.ofNat (liftSrcsLenWord σ I).toNat)) =
      liftSrcsElemSlotForLen σ I := by
  unfold liftSrcsElemSlotForLen liftSrcsLenWord srcElemSlot
  rw [keyValueToWord_uint256]

theorem liftSrcElemSlot_intWord (w : UInt256) :
    srcElemSlot (.int (Int.ofNat w.toNat)) = srcsDataSlot + w := by
  unfold srcElemSlot
  rw [keyValueToWord_uint256]

theorem liftWordOfInt_succ (w : UInt256) :
    EVM.wordOfInt (Int.ofNat w.toNat + 1) = w + ⟨1⟩ := by
  have hnonneg : 0 ≤ Int.ofNat w.toNat + 1 :=
    Int.add_nonneg (Int.natCast_nonneg _) (by decide)
  rw [wordOfInt_nonneg (Int.ofNat w.toNat + 1) hnonneg]
  apply u256_inj
  change ((Int.ofNat w.toNat + 1).toNat % UInt256.size) = (w + ⟨1⟩).toNat
  have hto : (Int.ofNat w.toNat + 1).toNat = w.toNat + 1 := by
    have hcast : (((Int.ofNat w.toNat + 1).toNat : Nat) : Int) = w.toNat + 1 := by
      rw [Int.toNat_of_nonneg hnonneg]
      norm_num
    omega
  rw [hto, uadd_toNat]
  rfl

theorem liftStorageLocStore_uint256_succ (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (wordLoc slot) (.int (Int.ofNat val.toNat + 1)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (val + ⟨1⟩)) := by
  unfold storageLocStore storageLocWriteWord wordLoc
  simp only [valueToWord, liftWordOfInt_succ, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (val + ⟨1⟩)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = (val + ⟨1⟩).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

theorem liftPushArray_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonSrc : (liftKey I).toNat < EVM.addressModulus) :
    pushArray? config { contract := contract, locals := liftLocals I }
      (initState cA gh bl σ σ₀ g A I) srcsRef (some (.address (liftSrc I))) =
        .ok (liftAfterSrcsElemState
          (liftAfterSrcsLengthState (initState cA gh bl σ σ₀ g A I)
            (liftSrcsLenWord σ I))
          (liftSrcsLenWord σ I) (liftKey I)) := by
  unfold pushArray? resolveStorageRef? evalStorageRef evalStorageRefSteps
    evalStorageRefStep srcsRef storageTypeAt? storageTypeStep? contract storageDecls
    config storageLayout solidityStorageLayout storageLayoutRaw liftLocals addrSt
    liftAfterSrcsLengthState liftAfterSrcsElemState liftSrcsLenWord cureSlotWord solcSlotWord
  simp [EvalResult.bind, bind, pure, EvalResult.ofOption, initState, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage]
  rw [cureStorageLocLoad_uint256]
  simp only [EvalResult.bind, bind]
  rw [liftStorageLocStore_uint256_succ]
  simp only [Option.bind, EvalResult.bind, bind, pure]
  rw [writeStorage?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [liftSrcElemSlot_intWord]
  rw [show ∀ slot, addrLoc slot = addressOffset0Loc slot by intro slot; rfl]
  have haddrWord :
      Value.address (liftSrc I) =
        Value.address (AccountAddress.ofNat (liftKey I).toNat) := by
    simpa [liftSrc, liftKey] using solcAddressValue_masked (calldataWord I.calldata 4)
  rw [haddrWord]
  rw [storageLocStore_address_offset0]
  · rfl
  · exact hcanonSrc

theorem evalExpr_liftPosStorage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := liftLocals I } evm
      (.storage (posRef (.var "src"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (liftPosSlotFor I)).toNat)) := by
  rw [evalExpr_storage_scalar
    (er := liftPosEvaledRef I) (t := .int uint256Int) (loc := wordLoc (liftPosSlotFor I))]
  · exact congrArg EvalResult.ok (cureStorageLocLoad_uint256 evm (liftPosSlotFor I))
  · simp [liftLocals, posRef]
  · simp [liftPosEvaledRef, liftSrc, posRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      pure, bind, liftLocals]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
      liftPosEvaledRef, liftPosSlotFor]

theorem evalExpr_liftPosZero_true (evm : EVM.State) (I : ExecutionEnv)
    (hpos : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (liftPosSlotFor I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := liftLocals I } evm
      (.binary .eq (.storage (posRef (.var "src"))) (.intLit 0)) = .ok (.bool true) := by
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_liftPosStorage evm I]
  simp [evalExpr?, evalBinaryOp?, hpos]
  all_goals native_decide

theorem evalExpr_liftPosZero_false (evm : EVM.State) (I : ExecutionEnv)
    (hpos : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (liftPosSlotFor I) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := liftLocals I } evm
      (.binary .eq (.storage (posRef (.var "src"))) (.intLit 0)) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_liftPosStorage evm I]
  simp [evalExpr?, evalBinaryOp?]
  intro hnat
  apply hpos
  apply u256_inj
  simpa using hnat
  all_goals native_decide

theorem evalExpr_liftSrcsLength (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := liftLocals I } evm
      (.arrayLength .storage srcsRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)) := by
  simp [evalExpr?, liftLocals, srcsRef, config, contract, storageDecls, storageLayout,
    solidityStorageLayout, storageLayoutRaw, readStorageArrayLength?, resolveStorageRef?,
    storageTypeAt?, evalStorageRef, evalStorageRefSteps, wordLoc, EvalResult.ofOption,
    EvalResult.bind, pure, bind]
  change
    (match storageLocLoad evm (wordLoc ⟨2⟩) with
    | Value.int n => EvalResult.ok (Value.int n)
    | _ => EvalResult.error EvalError.storageError) =
      EvalResult.ok (Value.int ↑(Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
  rw [cureStorageLocLoad_uint256]
  rfl

theorem liftAssignPos_ok (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := liftLocals I } evm
      .storage (posRef (.var "src"))
      (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)) =
        .ok ({ contract := contract, locals := liftLocals I }, liftAfterPosState evm I) := by
  have her :
      evalStorageRef config { contract := contract, locals := liftLocals I } evm
        (posRef (.var "src")) = .ok (liftPosEvaledRef I) := by
    simp [liftPosEvaledRef, liftSrc, posRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      pure, bind, liftLocals]
  have hstore :
      storageLocStore evm (wordLoc (liftPosSlotFor I))
        (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)) =
          some (liftAfterPosState evm I) := by
    simpa [liftAfterPosState] using
      storageLocStore_uint256 evm (liftPosSlotFor I)
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc (liftPosSlotFor I))
    (hbase := by simp [liftLocals, posRef])
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm'
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        liftPosEvaledRef, liftPosSlotFor])
    (hstore := hstore)

theorem cureLiftSourceBodyOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩)
    (hpos : cureSlotWord (liftPosSlotFor I) σ I = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let len := liftSrcsLenWord σ I
    let evm1 := liftAfterSrcsLengthState evm0 len
    let evm2 := liftAfterSrcsElemState evm1 len (liftKey I)
    let evm3 := liftAfterPosState evm2 I
    ExecTransitionBody config contract evm0 (liftLocals I) liftTransition.body
      (.returned { contract := contract, locals := liftLocals I } evm3 none) := by
  intro evm0 len evm1 evm2 evm3
  have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := liftLocals I) (by simp [liftLocals]) hauth
  have hguardLive := cureLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := liftLocals I) (by simp [liftLocals]) hlive
  have hposLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (liftPosSlotFor I) = ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hpos
  have hguardPos := evalExpr_liftPosZero_true evm0 I hposLoad
  have hsrc :
      evalExpr? config { contract := contract, locals := liftLocals I } evm0 (.var "src") =
        .ok (.address (liftSrc I)) := by
    simp [evalExpr?, liftLocals, EvalResult.ofOption]
  have hpush : pushArray? config { contract := contract, locals := liftLocals I } evm0
      srcsRef (some (.address (liftSrc I))) = .ok evm2 := by
    simpa [evm0, len, evm1, evm2] using
      liftPushArray_ok (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (by
          dsimp [liftKey]
          simpa [u256_land_comm solcAddrMask (calldataWord I.calldata 4)] using
            solcAddrMask_result_canonical (calldataWord I.calldata 4))
  have hlen := evalExpr_liftSrcsLength evm2 I
  have hassign := liftAssignPos_ok evm2 I
  have hblock :
      ExecBlock config { contract := contract, locals := liftLocals I } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
          .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .require (.binary .eq (.storage (posRef (.var "src"))) (.intLit 0)),
          .push srcsRef (some (.var "src")),
          .assign .storage (posRef (.var "src")) (.arrayLength .storage srcsRef) ]
        (.ok { contract := contract, locals := liftLocals I } evm3) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ?_
    refine ExecBlock.consNormal (ExecStmt.pushVal hsrc hpush) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hlen hassign) ExecBlock.nil
  simpa [ExecTransitionBody, liftTransition, nonpayable, auth, live, evm0, evm1, evm2, evm3]
    using ExecFuncBody.execBlockOK hblock

theorem cureLiftSourceBodyPosRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩)
    (hpos : cureSlotWord (liftPosSlotFor I) σ I ≠ ⟨0⟩) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (liftLocals I)
      liftTransition.body .reverted := by
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := liftLocals I) (by simp [liftLocals]) hauth
  have hguardLive := cureLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := liftLocals I) (by simp [liftLocals]) hlive
  have hposLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (liftPosSlotFor I) ≠ ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hpos
  have hguardPos := evalExpr_liftPosZero_false evm0 I hposLoad
  have hblock :
      ExecBlock config { contract := contract, locals := liftLocals I } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
          .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .require (.binary .eq (.storage (posRef (.var "src"))) (.intLit 0)),
          .push srcsRef (some (.var "src")),
          .assign .storage (posRef (.var "src")) (.arrayLength .storage srcsRef) ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardPos)
  simpa [ExecTransitionBody, liftTransition, nonpayable, auth, live, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem RD.cureLiftPosZeroOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1985⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata (cA, σ) k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hpos : solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) = ⟨0⟩)
    (hmem : mem.size = 96)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨2092⟩ (key :: ret :: R)
      (twoWordHashMem key ⟨5⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hmask : UInt256.land solcAddrMask key = key :=
    solcAddrMask_clean_left hcanonKey
  have hmaskLiteral :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) key =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hmaskLiteral' :
      UInt256.land key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        key := by
    rw [u256_land_comm key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)]
    exact hmaskLiteral
  have rdMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmaskLiteral'] at rdMasked
  have rdMstoreKeyPrefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by
      simp only [List.length_cons]; omega)]
  have rdAfterKey := rdMstoreKeyPrefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by
      simp only [List.length_cons]; omega)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨5⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by
      simp only [List.length_cons]; omega)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨5⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨5⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoad⟩ := rdSlot.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hposRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (solcMappingSlot ⟨5⟩ key) ⟨0⟩)) = ⟨0⟩ := by
    simpa [solcSlotWord] using hpos
  rw [hposRaw] at rdLoad
  have rdIsZero := rdLoad.iszero (by native_decide) (by simp only [List.length_cons]; omega)
  have rdIsZero' := rdIsZero
  rw [show UInt256.isZero ⟨0⟩ = ⟨1⟩ by native_decide] at rdIsZero'
  have rdPush := rdIsZero'.push2 ⟨2092⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rdPush.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by simp only [List.length_cons]; omega)⟩

abbrev cureSrcAlreadyDefinedRawWord : UInt256 :=
  ⟨0x437572652f616c72656164792d6578697374696e672d736f7572636500000000⟩

theorem RD.cureLiftPosNonzeroRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1985⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata (cA, σ) k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hpos : solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 8 ≤ 1024) :
    RDrev cureBytecode g s0 := by
  have hmask : UInt256.land solcAddrMask key = key :=
    solcAddrMask_clean_left hcanonKey
  have hmaskLiteral :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) key =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hmaskLiteral' :
      UInt256.land key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        key := by
    rw [u256_land_comm key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)]
    exact hmaskLiteral
  have rdMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmaskLiteral'] at rdMasked
  have rdMstoreKeyPrefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by
      simp only [List.length_cons]; omega),
    raw dup2 (by native_decide) (by
      simp only [List.length_cons]; omega)]
  have rdAfterKey := rdMstoreKeyPrefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by
      simp only [List.length_cons]; omega)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨5⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by
      simp only [List.length_cons]; omega)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨5⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨5⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoad⟩ := rdSlot.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hposRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (solcMappingSlot ⟨5⟩ key) ⟨0⟩)) ≠ ⟨0⟩ := by
    simpa [solcSlotWord] using hpos
  have rdIsZero := rdLoad.iszero (by native_decide) (by simp only [List.length_cons]; omega)
  have rdIsZero' := rdIsZero
  rw [isZero_eq_zero_of_ne hposRaw] at rdIsZero'
  have rdPush := rdIsZero'.push2 ⟨2092⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdTail := rdPush.jumpiNT (by native_decide) (by rfl)
    (by simp only [List.length_cons]; omega)
  have htailMem : (twoWordHashMem key ⟨5⟩ mem).size = 96 :=
    twoWordHashMem_size_96 key ⟨5⟩ hmem
  have htailRead64 :
      (twoWordHashMem key ⟨5⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 key ⟨5⟩ hmem hread64
  have rdMload := evm_run rdTail with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [htailMem]; decide) (by decide) htailRead64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 (twoWordHashMem key ⟨5⟩ mem))
      (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 (twoWordHashMem key ⟨5⟩ mem))
      (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨28⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨28⟩ (twoWordHashMem key ⟨5⟩ mem))
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst cureSrcAlreadyDefinedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨28⟩ cureSrcAlreadyDefinedRawWord
      (twoWordHashMem key ⟨5⟩ mem)) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨28⟩ cureSrcAlreadyDefinedRawWord htailMem htailRead64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

abbrev cureLiftEventTopic : UInt256 :=
  ⟨0x2b07094bdf192088dc9d18c2c3a2b11b7f1df5d6f3460343964c059221e3f048⟩

abbrev liftSrcsDataSlotLiteral : UInt256 :=
  ⟨29102676481673041902632991033461445430619272659676223336789171408008386403022⟩

abbrev liftStoreLogAccountMap (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) :
    AccountMap :=
  let len := solcSlotWord σ I ⟨2⟩
  let σLen := sstoreAccountMap I.codeOwner σ ⟨2⟩ (len + ⟨1⟩)
  let elemSlot := srcsDataSlot + len
  let σElem := sstoreAccountMap I.codeOwner σLen elemSlot
    (setAddressOffset0Word (solcSlotWord σLen I elemSlot) key)
  sstoreAccountMap I.codeOwner σElem (solcMappingSlot ⟨5⟩ key) (solcSlotWord σElem I ⟨2⟩)

theorem RD.cureLiftStoreAndLog {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2092⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata (cA, σ) k C)
    (hret : (D_J cureBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ret R
      (twoWordHashMem key ⟨5⟩ mem) (UInt256.ofNat 3) rdata
      (cA, liftStoreLogAccountMap σ ee key) k' C' := by
  let len := solcSlotWord σ ee ⟨2⟩
  let σLen := sstoreAccountMap ee.codeOwner σ ⟨2⟩ (len + ⟨1⟩)
  let elemSlot := srcsDataSlot + len
  let σElem := sstoreAccountMap ee.codeOwner σLen elemSlot
    (setAddressOffset0Word (solcSlotWord σLen ee elemSlot) key)
  have hmask : UInt256.land solcAddrMask key = key :=
    solcAddrMask_clean_left hcanonKey
  have hmaskKey : UInt256.land key solcAddrMask = key :=
    solcAddrMask_clean hcanonKey
  have hmaskR :
      UInt256.land key
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        key := by
    rw [u256_land_comm key
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hslotLiteral :
      liftSrcsDataSlotLiteral = srcsDataSlot := by
    simpa [liftSrcsDataSlotLiteral] using cureSrcsDataSlot_trusted
  have rdLenPrefix := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdLenLoaded'⟩ := rdLenPrefix.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdLenLoaded⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨2097⟩
      (len :: ⟨2⟩ :: key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [len, solcSlotWord] using rdLenLoaded'⟩
  have rdBeforeLenStore := evm_run rdLenLoaded with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdAfterLenStore'⟩ := rdBeforeLenStore.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdAfterLenStore⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨2103⟩
      (len :: ⟨2⟩ :: key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σLen) k' C' := by
    exact ⟨_, _, by simpa [σLen, len, u256_add_comm] using rdAfterLenStore'⟩
  have rdBase := rdAfterLenStore.pushConst liftSrcsDataSlotLiteral
    (op := .PUSH32) (width := 32) (by decide) (by native_decide) (by evm_ov)
  have rdElemSlotPrefix := rdBase.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdElemSlot⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨2137⟩
      (elemSlot :: ⟨2⟩ :: key :: ret :: R) mem (UInt256.ofNat 3) rdata
      (cA, σLen) k' C' := by
    exact ⟨_, _, by simpa [elemSlot, hslotLiteral, u256_add_comm] using rdElemSlotPrefix⟩
  have rdElemLoadPrefix := rdElemSlot.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdElemLoaded'⟩ := rdElemLoadPrefix.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdElemLoaded⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨2139⟩
      (solcSlotWord σLen ee elemSlot :: elemSlot :: ⟨2⟩ :: key :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σLen) k' C' := by
    exact ⟨_, _, by simpa [solcSlotWord] using rdElemLoaded'⟩
  have rdCleared := evm_run rdElemLoaded with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmaskR] at rdCleared
  have hnewWord :
      UInt256.lor key
          (UInt256.land
            (UInt256.lnot
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
            (solcSlotWord σLen ee elemSlot)) =
        setAddressOffset0Word (solcSlotWord σLen ee elemSlot) key := by
    unfold setAddressOffset0Word
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σLen ee elemSlot)]
    rw [hmaskKey, u256_lor_comm]
  have rdElemStorePre := evm_run rdCleared with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov)]
  rw [hnewWord] at rdElemStorePre
  have rdElemStoreReady := evm_run rdElemStorePre with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdAfterElemStore'⟩ := rdElemStoreReady.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdAfterElemStore⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨2165⟩
      (key :: ⟨2⟩ :: key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σElem) k' C' := by
    exact ⟨_, _, by simpa [σElem] using rdAfterElemStore'⟩
  have rdReloadLenPrefix := rdAfterElemStore.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdReloadedLen'⟩ := rdReloadLenPrefix.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdReloadedLen⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨2167⟩
      (solcSlotWord σElem ee ⟨2⟩ :: key :: key :: ret :: R) mem (UInt256.ofNat 3)
      rdata (cA, σElem) k' C' := by
    exact ⟨_, _, by simpa [solcSlotWord] using rdReloadedLen'⟩
  have rdMstoreKeyPrefix := evm_run rdReloadedLen with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdAfterKey := rdMstoreKeyPrefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨5⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have hposSlot := twoWordHashMem_solcMappingSlot ⟨5⟩ key hmem
  have rdPosSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨5⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost hposSlot (by native_decide) (by evm_ov)
  have rdPosStoreReady := evm_run rdPosSlot with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdAfterPosStore'⟩ := rdPosStoreReady.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdAfterPosStore⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨2186⟩
      (⟨0⟩ :: ⟨64⟩ :: key :: key :: ret :: R) (twoWordHashMem key ⟨5⟩ mem)
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σElem (solcMappingSlot ⟨5⟩ key)
        (solcSlotWord σElem ee ⟨2⟩)) k' C' := by
    exact ⟨_, _, by simpa [solcSlotWord] using rdAfterPosStore'⟩
  have rdMloadPrefix := rdAfterPosStore.swap1 (by native_decide) (by evm_ov)
  have hread64' :
      (twoWordHashMem key ⟨5⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 key ⟨5⟩ hmem hread64
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (twoWordHashMem key ⟨5⟩ mem).size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩
        then ⟨0⟩ else UInt256.ofNat (fromByteArrayBigEndian
          ((twoWordHashMem key ⟨5⟩ mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
    rw [if_neg (by
      rw [twoWordHashMem_size_96 key ⟨5⟩ hmem]
      native_decide)]
    rw [show (⟨64⟩ : UInt256).toNat = 64 from rfl, hread64']
    native_decide
  have rdMload := rdMloadPrefix.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
    mem_cost hmload64 (by native_decide) (by evm_ov)
  have rdTopic := rdMload.pushConst cureLiftEventTopic
    (op := .PUSH32) (width := 32) (by decide) (by native_decide) (by evm_ov)
  have rdLogPrefix := evm_run rdTopic with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdLogged := RD.cureLog2 0 (UInt256.ofNat 3) rdLogPrefix
    (by native_decide) hperm mem_cost (by native_decide) (by evm_ov)
  have rdPop := rdLogged.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [liftStoreLogAccountMap, len, σLen, elemSlot, σElem] using
      rdPop.jump (by native_decide) hret (by evm_ov)⟩

theorem cureDispatchLift {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 6)) :
    dispatchMsg contract I.calldata = some liftTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 6 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some liftTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes,
    cureAmtSelectorBytes, cureCageSelectorBytes, cureDenySelectorBytes,
    cureDropSelectorBytes, cureFileSelectorBytes, cureLCountSelectorBytes,
    cureLiftSelectorBytes]
  native_decide

theorem cureDecode_lift_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (liftTransition.params.map Param.name)
      (transitionSignature liftTransition).paramTypes I.calldata =
        some (liftLocals I) := by
  simpa [config, liftTransition, liftLocals, liftSrc] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "src") hsz36)

theorem cureDecode_lift_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (liftTransition.params.map Param.name)
      (transitionSignature liftTransition).paramTypes I.calldata = none := by
  simpa [config, liftTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "src") hsz4 hshort)

theorem cureReachLiftBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 6)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨524⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x3c278bd5⟩ :=
    cureSelWord_eq_of_beq I hsz 0x3c 0x27 0x8b 0xd5 ⟨0x3c278bd5⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h125⟩ := cureReachLowLowerFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨524⟩ 4 h125 (fun j hj => cureLowLowerArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem cureLiftBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 6))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let sel := cureSelWord I
  let key := liftKey I
  let callerSlot := cureCallerWardsSlot I
  let locals := liftLocals I
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 6) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some liftTransition :=
    cureDispatchLift hsel
  have hreach := cureReachLiftBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode :
        decodeCalldataWithMode config.abiDecodeMode (liftTransition.params.map Param.name)
          (transitionSignature liftTransition).paramTypes I.calldata = some (liftLocals I) :=
      cureDecode_lift_ok hsz36
    have hcallerWord :
        cureSlotWord callerSlot σ_evm I = cureSlotWord callerSlot σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
    have hliveWord :
        cureSlotWord ⟨1⟩ σ_evm I = cureSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    have hposSlotEq : liftPosSlotFor I = solcMappingSlot ⟨5⟩ key := by
      simpa [key] using liftPosSlotFor_eq I
    have hposWord :
        cureSlotWord (liftPosSlotFor I) σ_evm I =
          cureSlotWord (liftPosSlotFor I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (liftPosSlotFor I) ⟨0⟩
    obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
      (code := cureBytecode) (sel := sel) (entry := ⟨524⟩) (ret := ⟨484⟩)
      (decoded := ⟨546⟩) hreach
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by jump_dest) hsz36 hsize
    obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
      (code := cureBytecode) (decoded := ⟨546⟩) (ret := ⟨484⟩) (routine := ⟨1824⟩)
      (R := [sel]) hdecoded
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
    by_cases hauthEvm : cureSlotWord callerSlot σ_evm I = ⟨1⟩
    · have hauthSolm : cureSlotWord callerSlot σ_solm I = ⟨1⟩ := by
        rw [← hcallerWord]
        exact hauthEvm
      have hauthSolc :
          solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
        simpa [callerSlot, cureCallerWardsSlot, cureSlotWord] using hauthEvm
      obtain ⟨_, _, hafterAuth⟩ := RD.cureAuthCheckOk
        (code := cureBytecode) (pc := ⟨1824⟩) (okPc := ⟨1914⟩)
        (key := key) (ret := ⟨484⟩) (R := [sel])
        (by simpa [key] using hroutine)
        (by
          unfold cureAuthCheckWf
          repeat' first | apply And.intro | native_decide)
        hauthSolc (by jump_dest) (by simp)
      by_cases hliveEvm : cureSlotWord ⟨1⟩ σ_evm I = ⟨1⟩
      · have hliveSolm : cureSlotWord ⟨1⟩ σ_solm I = ⟨1⟩ := by
          rw [← hliveWord]
          exact hliveEvm
        have hliveSolc : solcSlotWord σ_evm I ⟨1⟩ = ⟨1⟩ := by
          simpa [cureSlotWord] using hliveEvm
        obtain ⟨_, _, hafterLive⟩ := RD.cureLiveGuardOk
          (code := cureBytecode) (pc := ⟨1914⟩) (okPc := ⟨1985⟩)
          (key := key) (ret := ⟨484⟩) (R := [sel]) hafterAuth
          (by
            unfold cureLiveGuardWf
            repeat' first | apply And.intro | native_decide)
          hliveSolc (by jump_dest) (by simp)
        have hmemAuth :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
          twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
        have hreadAuth64 :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
            solcFreePtrMem_read64
        have hcanonKey : key.toNat < EVM.addressModulus := by
          dsimp [key, liftKey]
          rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
          exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
        by_cases hposEvm : cureSlotWord (liftPosSlotFor I) σ_evm I = ⟨0⟩
        · have hposSolm : cureSlotWord (liftPosSlotFor I) σ_solm I = ⟨0⟩ := by
            rw [← hposWord]
            exact hposEvm
          let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          let len := liftSrcsLenWord σ_solm I
          let evm1 := liftAfterSrcsLengthState evm0 len
          let evm2 := liftAfterSrcsElemState evm1 len (liftKey I)
          let evm3 := liftAfterPosState evm2 I
          have hbody :
              ExecTransitionBody config contract evm0 locals liftTransition.body
                (.returned { contract := contract, locals := locals } evm3 none) := by
            simpa [evm0, len, evm1, evm2, evm3, locals] using
              (cureLiftSourceBodyOk (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hauthSolm hliveSolm hposSolm)
          have hposSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨5⟩ key) = ⟨0⟩ := by
            rw [← hposSlotEq]
            simpa [cureSlotWord] using hposEvm
          obtain ⟨_, _, hposPc⟩ := RD.cureLiftPosZeroOk
            (g := Sat256.ofUInt256 g)
            (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (ee := I) (key := key) (ret := ⟨484⟩) (R := [sel])
            hafterLive hcanonKey hposSolc hmemAuth (by simp)
          have hmemPos :
              (twoWordHashMem key ⟨5⟩
                (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)).size = 96 :=
            twoWordHashMem_size_96 key ⟨5⟩ hmemAuth
          have hreadPos64 :
              (twoWordHashMem key ⟨5⟩
                (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)).readWithPadding 64 32 =
                UInt256.toByteArray ⟨128⟩ :=
            twoWordHashMem_read64 key ⟨5⟩ hmemAuth hreadAuth64
          obtain ⟨_, _, hretPc⟩ := RD.cureLiftStoreAndLog
            (g := Sat256.ofUInt256 g)
            (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (ee := I) (key := key) (ret := ⟨484⟩) (R := [sel])
            hposPc (by jump_dest) hperm hmemPos hreadPos64 hcanonKey (by simp)
          have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
          have hret :
              RDret cureBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (cA, liftStoreLogAccountMap σ_evm I key) ByteArray.empty := by
            simpa using RD.stop hretPc' (by native_decide) (by simp)
          have hcreated :
              (cA, liftStoreLogAccountMap σ_evm I key).1 = evm3.createdAccounts := by
            simp [evm3, evm2, evm1, evm0, liftAfterPosState, liftAfterSrcsElemState,
              liftAfterSrcsLengthState, initState, storageStore_createdAccounts]
          have hlenWord : liftSrcsLenWord σ_evm I = liftSrcsLenWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
          have haccountsLen :
              accountMapEquiv (liftLengthAccountMap σ_evm I) (liftLengthAccountMap σ_solm I) := by
            simpa [liftLengthAccountMap, liftSrcsLenWord, hlenWord] using
              accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩
                (liftSrcsLenWord σ_solm I + ⟨1⟩) hAccounts
          have helemSlot :
              liftSrcsElemSlotForLen σ_evm I = liftSrcsElemSlotForLen σ_solm I := by
            simp [liftSrcsElemSlotForLen, hlenWord]
          have helemOld :
              solcSlotWord (liftLengthAccountMap σ_evm I) I
                  (liftSrcsElemSlotForLen σ_evm I) =
                solcSlotWord (liftLengthAccountMap σ_solm I) I
                  (liftSrcsElemSlotForLen σ_solm I) := by
            rw [helemSlot]
            exact accountMapEquiv_storage_findD haccountsLen I.codeOwner
              (liftSrcsElemSlotForLen σ_solm I) ⟨0⟩
          have haccountsElem :
              accountMapEquiv (liftElemAccountMap σ_evm I) (liftElemAccountMap σ_solm I) := by
            have helemOld' :
                solcSlotWord (liftLengthAccountMap σ_evm I) I
                    (liftSrcsElemSlotForLen σ_solm I) =
                  solcSlotWord (liftLengthAccountMap σ_solm I) I
                    (liftSrcsElemSlotForLen σ_solm I) := by
              simpa [helemSlot] using helemOld
            simpa [liftElemAccountMap, helemSlot, helemOld'] using
              accountMapEquiv_sstoreAccountMap I.codeOwner
              (liftSrcsElemSlotForLen σ_solm I)
              (setAddressOffset0Word
                (solcSlotWord (liftLengthAccountMap σ_solm I) I
                  (liftSrcsElemSlotForLen σ_solm I)) (liftKey I))
              haccountsLen
          have hposValue :
              solcSlotWord (liftElemAccountMap σ_evm I) I ⟨2⟩ =
                solcSlotWord (liftElemAccountMap σ_solm I) I ⟨2⟩ :=
            accountMapEquiv_storage_findD haccountsElem I.codeOwner ⟨2⟩ ⟨0⟩
          have haccountsFinal :
              accountMapEquiv (liftStoreLogAccountMap σ_evm I key)
                (liftFinalAccountMap σ_solm I) := by
            have hstoreEq :
                liftStoreLogAccountMap σ_evm I key = liftFinalAccountMap σ_evm I := by
              simp [liftStoreLogAccountMap, liftFinalAccountMap, liftElemAccountMap,
                liftLengthAccountMap, liftSrcsElemSlotForLen, liftSrcsLenWord, key,
                liftPosSlotFor_eq, cureSlotWord]
            rw [hstoreEq]
            dsimp [liftFinalAccountMap]
            rw [hposValue]
            exact accountMapEquiv_sstoreAccountMap I.codeOwner (liftPosSlotFor I)
              (solcSlotWord (liftElemAccountMap σ_solm I) I ⟨2⟩) haccountsElem
          have haccounts :
              accountMapEquiv (cA, liftStoreLogAccountMap σ_evm I key).2 evm3.accountMap := by
            simpa [evm3, evm2, evm1, evm0, liftAfterPosState, liftAfterSrcsElemState,
              liftAfterSrcsLengthState, initState, storageStore_accountMap,
              storageStore_executionEnv, Solm.EVM.storageLoad, State.lookupAccount,
              liftFinalAccountMap, liftElemAccountMap, liftLengthAccountMap,
              liftSrcsElemSlotForLen, liftSrcsLenWord, cureSlotWord, solcSlotWord, len] using haccountsFinal
          have henc : returnEquiv ByteArray.empty none liftTransition.returnType := by
            rw [show liftTransition.returnType = [] by rfl]
            exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
          exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
            hcreated haccounts henc
        · have hposSolm : cureSlotWord (liftPosSlotFor I) σ_solm I ≠ ⟨0⟩ := by
            intro hsolm
            exact hposEvm (by rw [hposWord, hsolm])
          let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          have hbody : ExecTransitionBody config contract evm0 locals liftTransition.body .reverted := by
            simpa [evm0, locals] using
              (cureLiftSourceBodyPosRevert (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hauthSolm hliveSolm hposSolm)
          have hposSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩ := by
            rw [← hposSlotEq]
            simpa [cureSlotWord] using hposEvm
          have hrev := RD.cureLiftPosNonzeroRevert
            (g := Sat256.ofUInt256 g)
            (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (ee := I) (key := key) (ret := ⟨484⟩) (R := [sel])
            hafterLive hcanonKey hposSolc hmemAuth hreadAuth64 (by simp)
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hliveSolm : cureSlotWord ⟨1⟩ σ_solm I ≠ ⟨1⟩ := by
          intro hsolm
          exact hliveEvm (by rw [hliveWord, hsolm])
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hbody : ExecTransitionBody config contract evm0 locals liftTransition.body .reverted := by
          have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := locals)
            (by simp [locals]) hauthSolm
          have hguardLive := cureLiveGuardEval_false (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := locals)
            (by simp [locals]) hliveSolm
          have hblock :
              ExecBlock config { contract := contract, locals := locals } evm0
                [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
                  .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
                  .require (.binary .eq (.storage liveRef) (.intLit 1)),
                  .require (.binary .eq (.storage (posRef (.var "src"))) (.intLit 0)),
                  .push srcsRef (some (.var "src")),
                  .assign .storage (posRef (.var "src")) (.arrayLength .storage srcsRef) ]
                .reverted := by
            refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
            · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
            refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
            exact ExecBlock.consRevert (ExecStmt.requireFalse hguardLive)
          simpa [ExecTransitionBody, liftTransition, nonpayable, auth, live, evm0] using
            ExecFuncBody.execBlockRevert hblock
        have hliveSolc : solcSlotWord σ_evm I ⟨1⟩ ≠ ⟨1⟩ := by
          simpa [cureSlotWord] using hliveEvm
        have hmemAuth :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
          twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
        have hread64 :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
            solcFreePtrMem_read64
        have hrev := RD.cureLiveGuardRevert
          (code := cureBytecode) (pc := ⟨1914⟩) (okPc := ⟨1985⟩)
          (key := key) (ret := ⟨484⟩) (R := [sel]) hafterAuth
          (by
            unfold cureLiveGuardWf
            repeat' first | apply And.intro | native_decide)
          (by
            unfold solcErrorStringRevertTailWf cureLiveGuardTailPc cureNotLiveRawWord
            repeat' first | apply And.intro | native_decide)
          hliveSolc hmemAuth hread64 (by simp)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : cureSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hauthEvm (by rw [hcallerWord, hsolm])
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody : ExecTransitionBody config contract evm0 locals liftTransition.body .reverted := by
        have hguard := cureAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals]) hauthSolm
        have hblock := nonpayableSecondRequireReverts
          (cfg := config) (solm := { contract := contract, locals := locals })
          (evm := evm0)
          (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
          (rest := [
            .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .require (.binary .eq (.storage (posRef (.var "src"))) (.intLit 0)),
            .push srcsRef (some (.var "src")),
            .assign .storage (posRef (.var "src")) (.arrayLength .storage srcsRef)])
          (by simp [evm0, initState]; exact hwv)
          hguard
        simpa [ExecTransitionBody, liftTransition, nonpayable, auth, evm0] using
          ExecFuncBody.execBlockRevert hblock
      have hauthSolc :
          solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
        simpa [callerSlot, cureCallerWardsSlot, cureSlotWord] using hauthEvm
      have hrev := RD.cureAuthCheckRevert
        (code := cureBytecode) (pc := ⟨1824⟩) (okPc := ⟨1914⟩)
        (key := key) (ret := ⟨484⟩) (R := [sel])
        (by simpa [key] using hroutine)
        (by
          unfold cureAuthCheckWf
          repeat' first | apply And.intro | native_decide)
        (by
          unfold solcErrorStringRevertTailWf cureAuthTailPc cureNotAuthorizedRawWord
          repeat' first | apply And.intro | native_decide)
        hauthSolc (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hlt :
        UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
      apply ult_one
      rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
      change I.calldata.size - 4 < 32
      omega
    have hrev := RD.solcExternalStaticArgsShortReverts
      (code := cureBytecode) (sel := sel) (entry := ⟨524⟩) (ret := ⟨484⟩)
      (decoded := ⟨546⟩) (need := ⟨32⟩) hreach
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) hlt
    exact hrev.reEquivDecodingFailed hcode hdispatch
      (cureDecode_lift_none_short hsz4 (by omega))

end Benchmarks.Dss.Cure
