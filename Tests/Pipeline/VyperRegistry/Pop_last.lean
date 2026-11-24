import Tests.Pipeline.VyperRegistry.Count
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

/-!
# Registry `pop_last()`

Dispatcher bucket 5, arm entry pc 430: the `callvalue` guard, `ownable._check_owner` (pc 435 →
1537, back to 442), `assert len(self.ids) > 0` (pc 442/450), the pop (pc 581: the length store and
the read of `ids[len-1]`), `if self.entries[id].active` (the hash at 581), the `totalWeight`
decrement with its underflow check (pc 624/659) and the three zeroing stores plus `RETURN` (pc 666).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperBounded

namespace Tests.Pipeline.VyperRegistry

set_option maxRecDepth 2000000

abbrev pIds : StorageRef := { base := "ids", steps := [] }
abbrev pTwRef : StorageRef := { base := "totalWeight", steps := [] }
abbrev pActiveRef : StorageRef := { base := "entries", steps := [.mindex (.var "id"), .field "active"] }
abbrev pWeightRef : StorageRef := { base := "entries", steps := [.mindex (.var "id"), .field "weight"] }
abbrev pEntryRef : StorageRef := { base := "entries", steps := [.mindex (.var "id")] }

theorem pop_lastBody_eq : pop_lastTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .internalCall "ownable__check_owner" [] "__c0",
     .require (.binary .gt (.arrayLength .storage pIds) (.intLit 0)),
     .letDecl "id" (some (.elem (.int (.uint ⟨256, by decide⟩))))
       (.storage { base := "ids", steps := [.aindex (.binary .sub (.arrayLength .storage pIds) (.intLit 1))] }),
     .pop pIds,
     .ite (.storage pActiveRef)
       [.assign .storage pTwRef (.inRange (.uint ⟨256, by decide⟩) (.binary .sub (.storage pTwRef) (.storage pWeightRef)))]
       [],
     .assign .storage pEntryRef
       (.structLit "Entry" [("account", .cast (.intLit 0) (.elem .address)), ("weight", .intLit 0),
         ("active", .boolLit false)]),
     .return [.var "id"]] := by rfl

/-! ### The words along the body -/

/-- `len(self.ids)` at the initial state. -/
abbrev pLen (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcSlotWordAt (UInt256.ofNat 2) σ I
/-- `len - 1`. -/
abbrev pw (σ : AccountMap) (I : ExecutionEnv) : UInt256 := UInt256.sub (pLen σ I) (UInt256.ofNat 1)
/-- The account map after the length store. -/
abbrev pσ1 (σ : AccountMap) (I : ExecutionEnv) : AccountMap := sstoreAccountMap I.codeOwner σ (UInt256.ofNat 2) (pw σ I)
/-- The popped id `ids[len-1]`. -/
abbrev pId (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcSlotWordAt (UInt256.ofNat 3 + pw σ I) σ I
abbrev pAct (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt (entrySlot (pId σ I) + UInt256.ofNat 2) (pσ1 σ I) I
abbrev pWt (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt (entrySlot (pId σ I) + UInt256.ofNat 1) (pσ1 σ I) I
abbrev pTw (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcSlotWordAt (UInt256.ofNat 20) (pσ1 σ I) I

/-! ### Memory: the id at offset 256, then the hash scratch re-written at each `entries[id]` access -/

abbrev pM1 (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (pId σ I).toByteArray.write 0 (registryDispatchMem 5) 256 32
abbrev pH (w : UInt256) (M : ByteArray) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0 (w.toByteArray.write 0 M 32 32) 0 32

theorem pM1_size (σ : AccountMap) (I : ExecutionEnv) : (pM1 σ I).size = 288 :=
  toByteArray_write32_size_of_ge _ _ 256 32 288 (dispatchMem_size 5 (by decide)) (by omega) (lt_usize _ (by decide)) rfl

theorem pH_inner_size (w : UInt256) (M : ByteArray) (hM : M.size = 288) : (w.toByteArray.write 0 M 32 32).size = 288 := by
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hM]; omega)]; exact hM

theorem pH_size (w : UInt256) (M : ByteArray) (hM : M.size = 288) : (pH w M).size = 288 := by
  have h1 := pH_inner_size w M hM
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h1]; omega)]; exact h1

theorem pH_load256 (w : UInt256) (M : ByteArray) (hM : M.size = 288) :
    memLoad (UInt256.ofNat 256) (pH w M) = memLoad (UInt256.ofNat 256) M := by
  have h1 := pH_inner_size w M hM
  rw [memLoad_above_write _ _ 0 256 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide),
    memLoad_above_write _ _ 32 256 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide)]

theorem pH_read256 (w : UInt256) (M : ByteArray) (hM : M.size = 288) :
    (pH w M).readWithPadding 256 32 = M.readWithPadding 256 32 := by
  have h1 := pH_inner_size w M hM
  rw [write32_read_above _ _ 0 256 (by rw [toByteArray_size]) (by omega) (by omega) (by omega),
    write32_read_above _ _ 32 256 (by rw [toByteArray_size]) (by omega) (by omega) (by omega)]

theorem pH_kec (w : UInt256) (M : ByteArray) (hM : M.size = 288) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) (pH w M) = entrySlot w :=
  keccak_entry_over M (by omega) w

theorem pM1_load256 (σ : AccountMap) (I : ExecutionEnv) : memLoad (UInt256.ofNat 256) (pM1 σ I) = pId σ I :=
  memLoad_write_back _ _ 256 (by decide) (by rw [dispatchMem_size 5 (by decide)]; exact lt_usize _ (by decide))

theorem pM1_read256 (σ : AccountMap) (I : ExecutionEnv) : (pM1 σ I).readWithPadding 256 32 = (pId σ I).toByteArray :=
  toByteArray_write_read_back_of_gap _ _ 256 (by rw [dispatchMem_size 5 (by decide)]; exact lt_usize _ (by decide))

/-- `len - 1` as an expression, on a `uint256` length. -/
theorem evalExpr_sub_one {cfg : Config} {stele : Frame} {evm : EVM.State} {e : Expr} {a : UInt256}
    (ha : evalExpr? cfg stele evm e = .ok (uint256Value a)) (hpos : 0 < a.toNat) :
    evalExpr? cfg stele evm (.binary .sub e (.intLit 1)) = .ok (.int (Int.ofNat (a.toNat - 1))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, evalExpr?]
  simp only [EvalResult.bind, bind, evalBinaryOp?, uint256Value, pure, Int.ofNat_eq_natCast]
  congr 2
  omega

/-- `pop_last()`: the theorem `Correct.lean` routes selector 9 to. -/
theorem registryPop_lastBody {σ σ₀ A I} {g : UInt256} (hwf : storageWF σ I)
    (hcode : I.code = registryBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (registrySelBytes 9)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (registrySelBytes 9) rfl hsel
  obtain ⟨_, _, rd⟩ := registryReachPop_lastBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some pop_lastTransition :=
    registryDispatch_pop_last (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) hsel
  have hdec : config.externalABI.decodeCalldata? (pop_lastTransition.params.map Param.name)
      (transitionSignature pop_lastTransition).paramTypes I.calldata = some ∅ := by
    simpa [config, contract, Syntax.contractSyntax, pop_lastTransition] using
      (decodeCalldataWithMode_empty_ok (mode := DecodeMode.vyper) (cd := I.calldata) hsz)
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := registryBlocks.registry_block_430_taken (by simp) (fun h => hwv h) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode hd
      (fun _ => by rw [pop_lastBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := registryBlocks.registry_block_430_fallthrough (by simp) (by rw [hwv]; rfl) rd
  have rd2 := registryBlocks.registry_block_435 (by simp) (by jump_dest) rd1
  simp only [registryBlocks.registry_block_435_stack] at rd2
  have hcv : evalExpr? config (frame ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simpa [initState] using hwv)
  have howner : evalExpr? config (frame ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .caller) (.storage ownerRef)) =
      .ok (.bool (decide (UInt256.ofNat I.source.val = solcSlotWordAt ⟨0⟩ σ I))) := by
    rw [evalCallerEqOwner _ (by simp) (by rw [storageLoad_initState_ofUInt256_solcSlotWordAt]; exact hwf.1),
      storageLoad_initState_ofUInt256_solcSlotWordAt]
    rfl
  by_cases hown : UInt256.ofNat I.source.val = solcSlotWordAt ⟨0⟩ σ I
  swap
  · obtain ⟨_, _, rd3⟩ := registryBlocks.registry_block_1537_fallthrough (by simp)
      (by rw [slotWord_eq]; exact isZero_xor_eq_zero_of_ne hown) rd2
    have rd4 := registryBlocks.registry_block_1547 (by simp) rd3
    refine RDrev.reEquivExecutionRevert hcode rd4 hd hdec ?_
    rw [pop_lastBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consRevert (ExecStmt.internalCallRevert (callee := checkOwnerCallee) rfl checkOwnerCallee_lookup rfl
        (ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse
          (by rw [howner, decide_eq_false hown])))))))
  obtain ⟨_, _, rd3⟩ := registryBlocks.registry_block_1537_taken (by simp)
    (by rw [slotWord_eq]; exact isZero_xor_ne_zero_of_eq hown) (by jump_dest) rd2
  have rd4 := registryBlocks.registry_block_1659 (by simp) (by jump_dest) rd3
  simp only [registryBlocks.registry_block_1659_stack] at rd4
  have hcheck : ExecStmt fork config (frame ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.internalCall "ownable__check_owner" [] "__c0")
      (.ok (resumeAfterInternalCall (frame ∅) "__c0" none) (initState σ σ₀ (Sat256.ofUInt256 g) A I)) :=
    ExecStmt.internalCallReturn (callee := checkOwnerCallee) rfl checkOwnerCallee_lookup rfl
      (ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue (by rw [howner, decide_eq_true hown]))
        ExecBlock.nil))
  set L1 : Store := (∅ : Store).insert "__c0" .unit with hL1def
  have hszL : (pLen σ I).toNat < UInt256.size := (pLen σ I).val.isLt
  have hlenE : evalExpr? config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.arrayLength .storage pIds) = .ok (uint256Value (pLen σ I)) :=
    evalIdsLength L1 (by simp [hL1def])
  have hgt : evalExpr? config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .gt (.arrayLength .storage pIds) (.intLit 0)) = .ok (.bool (decide (0 < (pLen σ I).toNat))) :=
    evalExpr_gt_zero hlenE
  -- pc 442: `len(self.ids) > 0`
  by_cases hpos : solcSlotWordAt (UInt256.ofNat 2) σ I = ⟨0⟩
  · obtain ⟨_, _, rd5⟩ := registryBlocks.registry_block_442_fallthrough (by simp) (by rw [slotWord_eq, hpos]; rfl) rd4
    have rd6 := registryBlocks.registry_block_450 (by simp) rd5
    refine RDrev.reEquivExecutionRevert hcode rd6 hd hdec ?_
    rw [pop_lastBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal hcheck (ExecBlock.consRevert (ExecStmt.requireFalse (by
        show evalExpr? config (frame L1) _ _ = _
        rw [hgt]; simp only [hpos]; rfl)))))
  have hposN : 0 < (pLen σ I).toNat := by
    rcases Nat.eq_zero_or_pos (pLen σ I).toNat with h | h
    · exact absurd (u256_inj (b := (⟨0⟩ : UInt256)) h) hpos
    · exact h
  have hgtT : evalExpr? config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .gt (.arrayLength .storage pIds) (.intLit 0)) = .ok (.bool true) := by
    rw [hgt, decide_eq_true hposN]
  obtain ⟨_, _, rd5⟩ := registryBlocks.registry_block_442_taken (by simp) (by rw [slotWord_eq]; exact fun h => hpos h)
    (by jump_dest) rd4
  obtain ⟨_, _, rd6⟩ := registryBlocks.registry_block_569_fallthrough (by simp)
    (by rw [slotWord_eq]; exact isZero_eq_zero_of_ne hpos) rd5
  simp only [registryBlocks.registry_block_569_fallthrough_stack] at rd6
  rw [slotWord_eq] at rd6
  -- Stele: `id = ids[len - 1]`
  have hpw : (pw σ I).toNat = (pLen σ I).toNat - 1 := by
    show (UInt256.sub (pLen σ I) (UInt256.ofNat 1)).toNat = _
    rw [usub_toNat (by rw [ulit_toNat' 1 (by decide)]; omega), ulit_toNat' 1 (by decide)]
  have hsub1 : UInt256.ofNat ((pLen σ I).toNat - 1) = pw σ I :=
    u256_inj (by rw [ulit_toNat' _ (by omega), hpw])
  have hidx := evalExpr_sub_one hlenE hposN
  rw [← hpw] at hidx
  have hlenB := idsLength_initState (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hlt : (pw σ I).toNat < (pLen σ I).toNat := by omega
  have hidRead : evalExpr? config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.storage { base := "ids", steps := [.aindex (.binary .sub (.arrayLength .storage pIds) (.intLit 1))] }) =
      .ok (uint256Value (pId σ I)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl)
        (er := { base := "ids", steps := [.aindex (.int (Int.ofNat (pw σ I).toNat))] })
        (physicalSlot := UInt256.ofNat 2 + UInt256.ofNat 1 +
          UInt256.ofNat ((keyValueToWord (.int (Int.ofNat (pw σ I).toNat))).toNat * 1)) (hbase := by simp [hL1def])
        (her := evalStorageRef_aindex_ok hidx (by show storageTypeAt? contract.storage _ = _; decide) ⟨_, rfl⟩ hlenB hlt)
        (hty := rfl)
        (hcheck := vyperCheckRef_aindex_ok (hbounds := rfl) (hanchor := rfl)
          (by rw [storageLoad_initState_ofUInt256_solcSlotWordAt]; exact hlt))
        (hloc := rfl),
      storageLoad_initState_ofUInt256_solcSlotWordAt, idsSlot_eq]
  set L2 : Store := L1.insert "id" (uint256Value (pId σ I)) with hL2def
  have hid : ∀ evm, evalExpr? config (frame L2) evm (.var "id") = .ok (uint256Value (pId σ I)) := fun evm =>
    evalVar _ _ "id" _ (by rw [hL2def]; exact store_get_self _ _ _)
  have hL2id : L2.get? "id" = some (uint256Value (pId σ I)) := by rw [hL2def]; exact store_get_self _ _ _
  -- Stele: `ids.pop()`
  have hpop : popArray? config (frame L2) (initState σ σ₀ (Sat256.ofUInt256 g) A I) pIds =
      .ok (Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner (UInt256.ofNat 2) (pw σ I)) := by
    rw [popArray_vyper_ok (hbackend := rfl) (hcheck := rfl) (hbounds := rfl) (hanchor := rfl)
        (hbase := by simp [hL2def, hL1def]) (er := { base := "ids", steps := [] }) (elem := .elem (.int (.uint ⟨256, by decide⟩)))
        (s := UInt256.ofNat 2) (cap := 16)
        (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (hty := by show storageTypeAt? contract.storage _ = _; decide) (hnotrans := rfl)
        (by rw [storageLoad_initState_ofUInt256_solcSlotWordAt]; exact hposN),
      storageLoad_initState_ofUInt256_solcSlotWordAt, hsub1]
    rfl
  -- pc 581: the static halt on the length store
  by_cases hperm : I.perm = true
  swap
  · have hpf : I.perm = false := by simpa using hperm
    have r1 := rd6.sub (by native_decide) (by evm_ov)
    have r2 := r1.dup1 (by native_decide) (by evm_ov)
    have r3 := r2.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
    have rs := r3.sstoreStatic hpf (by native_decide) (by evm_ov)
    refine RDstatic.reEquivStaticHalt hcode rs hd hdec ?_
    rw [pop_lastBody_eq]
    exact ExecFuncBody.execBlockStatic (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal hcheck (ExecBlock.consNormal (ExecStmt.requireTrue hgtT)
        (ExecBlock.consNormal (ExecStmt.letDecl hidRead)
          (ExecBlock.consStatic (ExecStmt.popStatic hpop (by show I.perm = false; exact hpf)))))))
  -- the EVM reads `ids[len-1]` after the length store: a different slot
  have hne32 : UInt256.ofNat 3 + pw σ I ≠ UInt256.ofNat 2 := by
    intro h
    have h' := congrArg UInt256.toNat h
    rw [uadd_toNat, ulit_toNat' 3 (by decide), ulit_toNat' 2 (by decide), hpw] at h'
    -- `len + 2` only wraps to `0` or `1`
    by_cases hwrap : 3 + ((pLen σ I).toNat - 1) < UInt256.size
    · rw [Nat.mod_eq_of_lt hwrap] at h'; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h'; omega
  have hIdE : solcSlotWordAt (UInt256.ofNat 3 + pw σ I) (pσ1 σ I) I = pId σ I :=
    solcSlotWordAt_sstore_ne _ _ _ _ _ hne32
  have hM2 : (pH (pId σ I) (pM1 σ I)).size = 288 := pH_size _ _ (pM1_size σ I)
  have hM3 : (pH (pId σ I) (pH (pId σ I) (pM1 σ I))).size = 288 := pH_size _ _ hM2
  -- Stele after the pop
  set evm1 := Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner (UInt256.ofNat 2) (pw σ I)
    with hevm1
  have hs1 : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I (pσ1 σ I) evm1 := SourceState.init.storageWrite _ _
  have hactE : evalExpr? config (frame L2) evm1 (.storage pActiveRef) =
      .ok (wordToElem .bool (solcSlotWordAt (entrySlot (pId σ I) + UInt256.ofNat 2) (pσ1 σ I) I)) := by
    rw [evalExpr_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl) (t := .bool)
        (er := { base := "entries", steps := [.mindex (.int (Int.ofNat (pId σ I).toNat)), .field "active"] })
        (loc := vyperWordLoc (entrySlot (pId σ I) + UInt256.ofNat 2) .bool) (hbase := by simp [hL2def, hL1def])
        (her := evalEntriesFieldRef _ _ (pId σ I) "id" "active" hL2id) (hty := rfl) (hloc := rfl),
      storageLocLoad_vyperWord, hs1.storageRead]
    rfl
  have hwt : evalExpr? config (frame L2) evm1 (.storage pWeightRef) = .ok (uint256Value (pWt σ I)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "entries", steps := [.mindex (.int (Int.ofNat (pId σ I).toNat)), .field "weight"] })
        (physicalSlot := entrySlot (pId σ I) + UInt256.ofNat 1) (hbase := by simp [hL2def, hL1def])
        (her := evalEntriesFieldRef _ _ (pId σ I) "id" "weight" hL2id) (hty := rfl) (hloc := rfl),
      hs1.storageRead]
    rfl
  have htw : evalExpr? config (frame L2) evm1 (.storage pTwRef) = .ok (uint256Value (pTw σ I)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "totalWeight", steps := [] }) (physicalSlot := UInt256.ofNat 20) (hbase := by simp [hL2def, hL1def])
        (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl), hs1.storageRead]
    rfl
  have hzeroLit : ∀ evm, evalExpr? config (frame L2) evm
      (.structLit "Entry" [("account", .cast (.intLit 0) (.elem .address)), ("weight", .intLit 0),
        ("active", .boolLit false)]) =
      .ok (.struct "Entry" [("account", .address (AccountAddress.ofNat 0)), ("weight", uint256Value ⟨0⟩),
        ("active", .bool false)]) := by
    intro evm
    rw [evalExpr?]
    simp [evalStructFields?, evalExpr?, castValue?, EvalResult.bind, bind, pure, EvalResult.ofOption, uint256Value]
  have hassignZ : ∀ evm, assignStorageRef? config (frame L2) evm .storage pEntryRef
      (.struct "Entry" [("account", .address (AccountAddress.ofNat 0)), ("weight", uint256Value ⟨0⟩),
        ("active", .bool false)]) =
      .ok (frame L2, Stele.EVM.storageStore (Stele.EVM.storageStore (Stele.EVM.storageStore evm
        evm.executionEnv.codeOwner (entrySlot (pId σ I)) ⟨0⟩)
        evm.executionEnv.codeOwner (entrySlot (pId σ I) + UInt256.ofNat 1) ⟨0⟩)
        evm.executionEnv.codeOwner (entrySlot (pId σ I) + UInt256.ofNat 2) ⟨0⟩) := by
    intro evm
    apply assignStorageRef_storage_vyper_of_write (hbackend := rfl) (hcheck := by rfl) (hbase := by simp [hL2def, hL1def])
      (er := { base := "entries", steps := [.mindex (.int (Int.ofNat (pId σ I).toNat))] })
      (her := evalEntriesRef _ _ (pId σ I) "id" hL2id) (hty := rfl)
    apply vyperWriteRaw_struct3 (l1 := vyperWordLoc (entrySlot (pId σ I)) .address)
      (l2 := vyperUint256Loc (entrySlot (pId σ I) + UInt256.ofNat 1))
      (l3 := vyperWordLoc (entrySlot (pId σ I) + UInt256.ofNat 2) .bool)
      rfl rfl rfl (storageLocStore_vyperWord_value _ _ _ _ ⟨0⟩ rfl)
    · erw [storageLocStore_uint256, storageStore_executionEnv]
    · rw [storageLocStore_vyperWord_value _ _ _ _ ⟨0⟩ rfl, storageStore_executionEnv, storageStore_executionEnv]
  by_cases hact : solcSlotWordAt (entrySlot (pId σ I) + UInt256.ofNat 2) (pσ1 σ I) I = ⟨0⟩
  · -- inactive: straight to the zeroing stores
    obtain ⟨_, _, rd7⟩ := registryBlocks.registry_block_581_taken (by simp) hperm
      (by
        simp only [ulit_toNat' 32 (by decide), ulit_toNat' 256 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
        rw [slotWord_eq, slotWord_eq, hIdE, pM1_load256, pH_kec _ _ (pM1_size σ I), hact]
        decide) (by jump_dest) rd6
    simp only [registryBlocks.registry_block_581_taken_stack, registryBlocks.registry_block_581_taken_memory,
      ulit_toNat' 32 (by decide), ulit_toNat' 256 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd7
    rw [slotWord_eq, hIdE, pM1_load256] at rd7
    have rd8 := registryBlocks.registry_block_666 (by simp) hperm rd7
    simp only [ulit_toNat' 32 (by decide), ulit_toNat' 256 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      pH_load256 _ _ (pM1_size σ I), pM1_load256, pH_kec _ _ hM2, pH_read256 _ _ hM2, pH_read256 _ _ (pM1_size σ I),
      pM1_read256] at rd8
    have hactF : evalExpr? config (frame L2) evm1 (.storage pActiveRef) = .ok (.bool false) := by
      rw [hactE, wordToElemBool, hact]; simp
    have hz := hassignZ evm1
    simp only [hs1.env] at hz
    have hs3 := ((hs1.storageWrite (entrySlot (pId σ I)) ⟨0⟩).storageWrite (entrySlot (pId σ I) + UInt256.ofNat 1) ⟨0⟩).storageWrite
      (entrySlot (pId σ I) + UInt256.ofNat 2) ⟨0⟩
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ pop_lastTransition.body
        (.returned (frame L2) (Stele.EVM.storageStore (Stele.EVM.storageStore (Stele.EVM.storageStore evm1
          I.codeOwner (entrySlot (pId σ I)) ⟨0⟩) I.codeOwner (entrySlot (pId σ I) + UInt256.ofNat 1) ⟨0⟩)
          I.codeOwner (entrySlot (pId σ I) + UInt256.ofNat 2) ⟨0⟩) (some [uint256Value (pId σ I)])) := by
      rw [pop_lastBody_eq]
      exact ExecFuncBody.execBlockRet (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
        (ExecBlock.consNormal hcheck (ExecBlock.consNormal (ExecStmt.requireTrue hgtT)
          (ExecBlock.consNormal (ExecStmt.letDecl hidRead)
            (ExecBlock.consNormal (ExecStmt.pop (hperm := by first | assumption | exact Or.inr ‹_› | exact Or.inl rfl) hpop)
              (ExecBlock.consNormal (ExecStmt.iteFalse hactF ExecBlock.nil)
                (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs1.env] using hperm)) (hzeroLit _) hz)
                  (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (hid _)))))))))))
    exact rd8.reEquivExecutionGen hcode hd hdec hbody hs3.accounts (returnEquiv_of_encode (uint256ReturnEncoding _))
  -- active: `totalWeight -= entries[id].weight`
  obtain ⟨_, _, rd7⟩ := registryBlocks.registry_block_581_fallthrough (by simp) hperm
    (by
      simp only [ulit_toNat' 32 (by decide), ulit_toNat' 256 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
      rw [slotWord_eq, slotWord_eq, hIdE, pM1_load256, pH_kec _ _ (pM1_size σ I)]
      exact isZero_eq_zero_of_ne hact) rd6
  simp only [registryBlocks.registry_block_581_fallthrough_stack, registryBlocks.registry_block_581_fallthrough_memory,
    ulit_toNat' 32 (by decide), ulit_toNat' 256 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd7
  rw [slotWord_eq, hIdE, pM1_load256] at rd7
  have hactT : evalExpr? config (frame L2) evm1 (.storage pActiveRef) = .ok (.bool true) := by
    rw [hactE, wordToElemBool, decide_eq_false hact]; rfl
  by_cases hund : (pWt σ I).toNat ≤ (pTw σ I).toNat
  swap
  · obtain ⟨_, _, rd8⟩ := registryBlocks.registry_block_624_taken (by simp)
      (by
        simp only [ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
        rw [slotWord_eq, slotWord_eq, pH_load256 _ _ (pM1_size σ I), pM1_load256, pH_kec _ _ hM2]
        rw [ugt_one (a := UInt256.sub (pTw σ I) (pWt σ I)) (b := pTw σ I) (by
          rw [usub_toNat_underflow (by omega)]
          have hlt := (pWt σ I).val.isLt
          change (pWt σ I).toNat < UInt256.size at hlt
          omega)]
        decide) (by jump_dest) rd7
    have rd9 := registryBlocks.registry_block_1661 (by simp [registryBlocks.registry_block_624_taken_stack]) rd8
    refine RDrev.reEquivExecutionRevert hcode rd9 hd hdec ?_
    rw [pop_lastBody_eq]
    exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal hcheck (ExecBlock.consNormal (ExecStmt.requireTrue hgtT)
        (ExecBlock.consNormal (ExecStmt.letDecl hidRead)
          (ExecBlock.consNormal (ExecStmt.pop (hperm := by first | assumption | exact Or.inr ‹_› | exact Or.inl rfl) hpop)
            (ExecBlock.consRevert (ExecStmt.iteTrue hactT (ExecBlock.consRevert (ExecStmt.assignExprRevert
              (evalExpr_uint256_sub_underflow htw hwt (by omega)))))))))))
  obtain ⟨_, _, rd8⟩ := registryBlocks.registry_block_624_fallthrough (by simp)
    (by
      simp only [ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
      rw [slotWord_eq, slotWord_eq, pH_load256 _ _ (pM1_size σ I), pM1_load256, pH_kec _ _ hM2]
      exact ugt_zero (a := UInt256.sub (pTw σ I) (pWt σ I)) (b := pTw σ I) (by rw [usub_toNat hund]; omega)) rd7
  simp only [registryBlocks.registry_block_624_fallthrough_stack, registryBlocks.registry_block_624_fallthrough_memory,
    ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd8
  rw [slotWord_eq, slotWord_eq, pH_load256 _ _ (pM1_size σ I), pM1_load256, pH_kec _ _ hM2] at rd8
  obtain ⟨_, _, rd9⟩ := registryBlocks.registry_block_659 (by simp) hperm rd8
  simp only [registryBlocks.registry_block_659_stack] at rd9
  have rd10 := registryBlocks.registry_block_666 (by simp) hperm rd9
  simp only [ulit_toNat' 32 (by decide), ulit_toNat' 256 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    pH_load256 _ _ hM2, pH_load256 _ _ (pM1_size σ I), pM1_load256, pH_kec _ _ hM3, pH_read256 _ _ hM3,
    pH_read256 _ _ hM2, pH_read256 _ _ (pM1_size σ I), pM1_read256] at rd10
  set evm2 := Stele.EVM.storageStore evm1 I.codeOwner (UInt256.ofNat 20) (UInt256.sub (pTw σ I) (pWt σ I)) with hevm2
  have hs2 : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I
      (sstoreAccountMap I.codeOwner (pσ1 σ I) (UInt256.ofNat 20) (UInt256.sub (pTw σ I) (pWt σ I))) evm2 :=
    hs1.storageWrite _ _
  have hsub := evalExpr_uint256_sub htw hwt hund
  have hassignT : assignStorageRef? config (frame L2) evm1 .storage pTwRef
      (uint256Value (UInt256.sub (pTw σ I) (pWt σ I))) = .ok (frame L2, evm2) := by
    apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "totalWeight", steps := [] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc (UInt256.ofNat 20))
      (hbase := by simp [hL2def, hL1def]) (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
    erw [storageLocStore_uint256, hs1.env]
  have hz := hassignZ evm2
  simp only [hs2.env] at hz
  have hs3 := ((hs2.storageWrite (entrySlot (pId σ I)) ⟨0⟩).storageWrite (entrySlot (pId σ I) + UInt256.ofNat 1) ⟨0⟩).storageWrite
    (entrySlot (pId σ I) + UInt256.ofNat 2) ⟨0⟩
  have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ pop_lastTransition.body
      (.returned (frame L2) (Stele.EVM.storageStore (Stele.EVM.storageStore (Stele.EVM.storageStore evm2
        I.codeOwner (entrySlot (pId σ I)) ⟨0⟩) I.codeOwner (entrySlot (pId σ I) + UInt256.ofNat 1) ⟨0⟩)
        I.codeOwner (entrySlot (pId σ I) + UInt256.ofNat 2) ⟨0⟩) (some [uint256Value (pId σ I)])) := by
    rw [pop_lastBody_eq]
    exact ExecFuncBody.execBlockRet (ExecBlock.consNormal (ExecStmt.requireTrue hcv)
      (ExecBlock.consNormal hcheck (ExecBlock.consNormal (ExecStmt.requireTrue hgtT)
        (ExecBlock.consNormal (ExecStmt.letDecl hidRead)
          (ExecBlock.consNormal (ExecStmt.pop (hperm := by first | assumption | exact Or.inr ‹_› | exact Or.inl rfl) hpop)
            (ExecBlock.consNormal (ExecStmt.iteTrue hactT (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs1.env] using hperm)) hsub hassignT) ExecBlock.nil))
              (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs2.env] using hperm)) (hzeroLit _) hz)
                (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (hid _)))))))))))
  exact rd10.reEquivExecutionGen hcode hd hdec hbody hs3.accounts (returnEquiv_of_encode (uint256ReturnEncoding _))

end Tests.Pipeline.VyperRegistry
