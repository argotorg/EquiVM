import Tests.Pipeline.VyperRegistry.Helpers
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

/-!
# Registry `register(address)` and `register(address,uint256)`

Both selectors bind `weight` (the default `1`, or calldata word 2) into memory offset 288 and
jump to the shared body at pc 793: address validation, `ownable._check_owner`, `weight > 0`,
`id = nextId` with the checked increment (pc 944), the four `SSTORE`s of `nextId` and
`entries[id]` (pc 967), `ids.append(id)` with the capacity check (pc 967/1021), the checked
`totalWeight += weight` (pc 1021/1055), the log and the `uint256` return.  The shared body is
`registerTail`; the two `…Body` theorems supply the guard, the decode and the `weight` binding.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperBounded

namespace Tests.Pipeline.VyperRegistry

set_option maxRecDepth 2000000

abbrev nextIdRef : StorageRef := { base := "nextId", steps := [] }
abbrev twRef' : StorageRef := { base := "totalWeight", steps := [] }
abbrev idsRef0 : StorageRef := { base := "ids", steps := [] }
abbrev entryIdRef : StorageRef := { base := "entries", steps := [.mindex (.var "id")] }

/-- The statements shared by both `register` variants after `weight` is bound. -/
abbrev registerTailStmts : List Stmt :=
  [.internalCall "ownable__check_owner" [] "__c0",
   .require (.binary .gt (.var "weight") (.intLit 0)),
   .letDecl "id" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.storage nextIdRef),
   .assign .storage nextIdRef (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "id") (.intLit 1))),
   .assign .storage entryIdRef
     (.structLit "Entry" [("account", .var "account"), ("weight", .var "weight"), ("active", .boolLit true)]),
   .push idsRef0 (some (.var "id")),
   .assign .storage twRef' (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.storage twRef') (.var "weight"))),
   .emit "Registered" [.var "id", .var "account", .var "weight"],
   .return [.var "id"]]

theorem register_addressBody_eq : register_addressTransition.body =
    .require (.binary .eq (.env .callvalue) (.intLit 0)) ::
    .letDecl "weight" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 1) :: registerTailStmts := by rfl

theorem register_address_uint256Body_eq : register_address_uint256Transition.body =
    .require (.binary .eq (.env .callvalue) (.intLit 0)) :: registerTailStmts := by rfl

/-! ### Memory along the shared body -/

abbrev rM0 (m : Nat) (wgt : UInt256) : ByteArray := wgt.toByteArray.write 0 (registryDispatchMem m) 288 32
abbrev rM1 (m : Nat) (wgt : UInt256) (I : ExecutionEnv) : ByteArray := (argWord I).toByteArray.write 0 (rM0 m wgt) 256 32
abbrev rM2 (m : Nat) (wgt : UInt256) (I : ExecutionEnv) (nid : UInt256) : ByteArray :=
  nid.toByteArray.write 0 (rM1 m wgt I) 320 32
abbrev rM3 (m : Nat) (wgt : UInt256) (I : ExecutionEnv) (nid : UInt256) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0 (nid.toByteArray.write 0 (rM2 m wgt I nid) 32 32) 0 32

theorem rM_sizes (m : Nat) (hm : m < 10) (wgt : UInt256) (I : ExecutionEnv) (nid : UInt256) :
    (rM0 m wgt).size = 320 ∧ (rM1 m wgt I).size = 320 ∧ (rM2 m wgt I nid).size = 352 ∧
    (nid.toByteArray.write 0 (rM2 m wgt I nid) 32 32).size = 352 ∧ (rM3 m wgt I nid).size = 352 := by
  have h0 : (rM0 m wgt).size = 320 :=
    toByteArray_write32_size_of_ge _ _ 288 32 320 (dispatchMem_size m hm) (by omega) (lt_usize _ (by decide)) rfl
  have h1 : (rM1 m wgt I).size = 320 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h0]; omega)]; exact h0
  have h2 : (rM2 m wgt I nid).size = 352 :=
    toByteArray_write32_size_of_ge _ _ 320 320 352 h1 (by omega) (lt_usize _ (by decide)) rfl
  have h3 : (nid.toByteArray.write 0 (rM2 m wgt I nid) 32 32).size = 352 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h2]; omega)]; exact h2
  refine ⟨h0, h1, h2, h3, ?_⟩
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h3]; omega)]; exact h3

theorem rM1_load288 (m : Nat) (hm : m < 10) (wgt : UInt256) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 288) (rM1 m wgt I) = wgt := by
  obtain ⟨h0, -, -, -, -⟩ := rM_sizes m hm wgt I ⟨0⟩
  rw [memLoad_above_write _ _ 256 288 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide)]
  exact memLoad_write_back _ _ 288 (by decide) (by rw [dispatchMem_size m hm]; exact lt_usize _ (by decide))

theorem rM2_load320 (m : Nat) (hm : m < 10) (wgt : UInt256) (I : ExecutionEnv) (nid : UInt256) :
    memLoad (UInt256.ofNat 320) (rM2 m wgt I nid) = nid :=
  memLoad_write_back _ _ 320 (by decide) (by rw [(rM_sizes m hm wgt I nid).2.1]; exact lt_usize _ (by decide))

theorem rM3_load (m : Nat) (hm : m < 10) (wgt : UInt256) (I : ExecutionEnv) (nid : UInt256) :
    memLoad (UInt256.ofNat 256) (rM3 m wgt I nid) = argWord I ∧
    memLoad (UInt256.ofNat 288) (rM3 m wgt I nid) = wgt ∧
    memLoad (UInt256.ofNat 320) (rM3 m wgt I nid) = nid := by
  obtain ⟨h0, h1, h2, h3, -⟩ := rM_sizes m hm wgt I nid
  refine ⟨?_, ?_, ?_⟩
  · rw [memLoad_above_write _ _ 0 256 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide),
      memLoad_above_write _ _ 32 256 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide),
      memLoad_below_write _ _ 320 256 (by rw [h1] <;> omega) (by omega) (by rw [h1]; exact lt_usize _ (by decide)) (by decide)]
    exact memLoad_write_back _ _ 256 (by decide) (by rw [h0]; exact lt_usize _ (by decide))
  · rw [memLoad_above_write _ _ 0 288 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide),
      memLoad_above_write _ _ 32 288 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide),
      memLoad_below_write _ _ 320 288 (by rw [h1] <;> omega) (by omega) (by rw [h1]; exact lt_usize _ (by decide)) (by decide)]
    exact rM1_load288 m hm wgt I
  · rw [memLoad_above_write _ _ 0 320 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide),
      memLoad_above_write _ _ 32 320 (by rw [toByteArray_size]) (by omega) (by omega) (by omega) (by decide)]
    exact rM2_load320 m hm wgt I nid

theorem rM3_return (m : Nat) (hm : m < 10) (wgt : UInt256) (I : ExecutionEnv) (nid x : UInt256) :
    (x.toByteArray.write 0 (rM3 m wgt I nid) 352 32).readWithPadding 320 32 = nid.toByteArray := by
  obtain ⟨-, -, h2, h3, h4⟩ := rM_sizes m hm wgt I nid
  rw [toByteArray_write_read_below_of_gap x _ 352 320 (by rw [h4] <;> omega) (by omega) (by rw [h4]; exact lt_usize _ (by decide)),
    write32_read_above _ _ 0 320 (by rw [toByteArray_size]) (by omega) (by omega) (by rw [h3] <;> omega),
    write32_read_above _ _ 32 320 (by rw [toByteArray_size]) (by omega) (by omega) (by rw [h2] <;> omega),
    toByteArray_write_read_back_of_gap nid _ 320 (by rw [(rM_sizes m hm wgt I nid).2.1]; exact lt_usize _ (by decide))]

/-! ### The account maps along the shared body -/

abbrev rσ1 (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (UInt256.ofNat 19) (solcSlotWordAt (UInt256.ofNat 19) σ I + UInt256.ofNat 1)
abbrev rσ4 (σ : AccountMap) (I : ExecutionEnv) (wgt : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner (rσ1 σ I)
    (entrySlot (solcSlotWordAt (UInt256.ofNat 19) σ I)) (argWord I))
    (entrySlot (solcSlotWordAt (UInt256.ofNat 19) σ I) + UInt256.ofNat 1) wgt)
    (entrySlot (solcSlotWordAt (UInt256.ofNat 19) σ I) + UInt256.ofNat 2) (UInt256.ofNat 1)
abbrev rLen (σ : AccountMap) (I : ExecutionEnv) (wgt : UInt256) : UInt256 := solcSlotWordAt (UInt256.ofNat 2) (rσ4 σ I wgt) I
abbrev rσ6 (σ : AccountMap) (I : ExecutionEnv) (wgt : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner (rσ4 σ I wgt)
    (UInt256.ofNat 3 + rLen σ I wgt) (solcSlotWordAt (UInt256.ofNat 19) σ I)) (UInt256.ofNat 2) (rLen σ I wgt + UInt256.ofNat 1)
abbrev rTw (σ : AccountMap) (I : ExecutionEnv) (wgt : UInt256) : UInt256 := solcSlotWordAt (UInt256.ofNat 20) (rσ6 σ I wgt) I

/-- The shared body from pc 805 (after the address validation) to the end. -/
theorem registerTail {σ σ₀ A I} {g : UInt256} (hwf : storageWF σ I) (hcode : I.code = registryBytecode)
    (m : Nat) (hm : m < 10) (wgt : UInt256) {aw : UInt256} {k C : Nat}
    (rd : RD fork registryBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (UInt256.ofNat 805)
      [argWord I, solcSelectorWord I] (rM0 m wgt) aw ByteArray.empty σ k C)
    (hcanon : (argWord I).toNat < EVM.addressModulus)
    (t : TransitionDecl) (hd : dispatchMsg contract I.calldata = some t) (callargs : Store)
    (hdec : config.externalABI.decodeCalldata? (t.params.map Param.name) (transitionSignature t).paramTypes I.calldata =
      some callargs)
    (hret : t.returnType = [.elem (.int (.uint ⟨256, by decide⟩))])
    (L : Store) (hLacc : L.get? "account" = some (.address (AccountAddress.ofNat (argWord I).toNat)))
    (hLw : L.get? "weight" = some (uint256Value wgt))
    (hL1 : L.get? "nextId" = none) (hL2 : L.get? "entries" = none) (hL3 : L.get? "ids" = none)
    (hL4 : L.get? "totalWeight" = none)
    (hprefix : ∀ result, ExecBlock fork config (frame L) (initState σ σ₀ (Sat256.ofUInt256 g) A I) registerTailStmts result →
      ExecBlock fork config (frame callargs) (initState σ σ₀ (Sat256.ofUInt256 g) A I) t.body result) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have rd1 := registryBlocks.registry_block_805 (by simp) (by jump_dest) rd
  simp only [registryBlocks.registry_block_805_stack, registryBlocks.registry_block_805_memory,
    ulit_toNat' 256 (by decide)] at rd1
  have howner : evalExpr? config (frame ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .caller) (.storage ownerRef)) =
      .ok (.bool (decide (UInt256.ofNat I.source.val = solcSlotWordAt ⟨0⟩ σ I))) := by
    rw [evalCallerEqOwner _ (by simp) (by rw [storageLoad_initState_ofUInt256_solcSlotWordAt]; exact hwf.1),
      storageLoad_initState_ofUInt256_solcSlotWordAt]
    rfl
  by_cases hown : UInt256.ofNat I.source.val = solcSlotWordAt ⟨0⟩ σ I
  swap
  · obtain ⟨_, _, rd2⟩ := registryBlocks.registry_block_1537_fallthrough (by simp)
      (by rw [slotWord_eq]; exact isZero_xor_eq_zero_of_ne hown) rd1
    have rd3 := registryBlocks.registry_block_1547 (by simp) rd2
    refine RDrev.reEquivExecutionRevert hcode rd3 hd hdec (ExecFuncBody.execBlockRevert (hprefix _ ?_))
    exact ExecBlock.consRevert (ExecStmt.internalCallRevert (callee := checkOwnerCallee) rfl checkOwnerCallee_lookup rfl
      (ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse (by rw [howner, decide_eq_false hown])))))
  obtain ⟨_, _, rd2⟩ := registryBlocks.registry_block_1537_taken (by simp)
    (by rw [slotWord_eq]; exact isZero_xor_ne_zero_of_eq hown) (by jump_dest) rd1
  have rd3 := registryBlocks.registry_block_1659 (by simp) (by jump_dest) rd2
  simp only [registryBlocks.registry_block_1659_stack] at rd3
  have hcheck : ExecStmt fork config (frame L) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.internalCall "ownable__check_owner" [] "__c0")
      (.ok (resumeAfterInternalCall (frame L) "__c0" none) (initState σ σ₀ (Sat256.ofUInt256 g) A I)) :=
    ExecStmt.internalCallReturn (callee := checkOwnerCallee) rfl checkOwnerCallee_lookup rfl
      (ExecFuncBody.execBlockOK (ExecBlock.consNormal (ExecStmt.requireTrue (by rw [howner, decide_eq_true hown]))
        ExecBlock.nil))
  set L1 : Store := L.insert "__c0" .unit with hL1def
  have hw1 : ∀ evm, evalExpr? config (frame L1) evm (.var "weight") = .ok (uint256Value wgt) := fun evm =>
    evalVar _ _ "weight" _ (by rw [hL1def, store_get_ne _ _ (by decide), hLw])
  have hgt : evalExpr? config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .gt (.var "weight") (.intLit 0)) = .ok (.bool (decide (0 < wgt.toNat))) :=
    evalExpr_gt_zero (hw1 _)
  -- pc 816: `weight > 0`
  by_cases hwpos : wgt = ⟨0⟩
  · have rd4 := registryBlocks.registry_block_816_fallthrough (by simp) (by rw [rM1_load288 m hm, hwpos]; rfl) rd3
    have rd5 := registryBlocks.registry_block_825 (by simp) rd4
    refine RDrev.reEquivExecutionRevert hcode rd5 hd hdec (ExecFuncBody.execBlockRevert (hprefix _ ?_))
    exact ExecBlock.consNormal hcheck (ExecBlock.consRevert (ExecStmt.requireFalse
      (by show evalExpr? config (frame L1) _ _ = _; rw [hgt, hwpos]; rfl)))
  have rd4 := registryBlocks.registry_block_816_taken (by simp) (by rw [rM1_load288 m hm]; exact fun h => hwpos h) (by jump_dest) rd3
  have hwpos' : 0 < wgt.toNat := by
    by_contra h; exact hwpos (uint256_toNat_eq_zero (by omega))
  have hgt' : evalExpr? config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .gt (.var "weight") (.intLit 0)) = .ok (.bool true) := by
    rw [hgt, decide_eq_true hwpos']
  -- pc 944: `id = nextId`, `id + 1`
  set nid := solcSlotWordAt (UInt256.ofNat 19) σ I with hnid
  have hidRead : evalExpr? config (frame L1) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.storage nextIdRef) =
      .ok (uint256Value nid) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "nextId", steps := [] }) (physicalSlot := UInt256.ofNat 19)
        (hbase := by rw [hL1def, store_get_ne _ _ (by decide), hL1])
        (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl),
      storageLoad_initState_ofUInt256_solcSlotWordAt]
  set L2 : Store := L1.insert "id" (uint256Value nid) with hL2def
  have hid : ∀ evm, evalExpr? config (frame L2) evm (.var "id") = .ok (uint256Value nid) := fun evm =>
    evalVar _ _ "id" _ (by rw [hL2def, store_get_self])
  have hw2 : ∀ evm, evalExpr? config (frame L2) evm (.var "weight") = .ok (uint256Value wgt) := fun evm =>
    evalVar _ _ "weight" _ (by rw [hL2def, store_get_ne _ _ (by decide), hL1def, store_get_ne _ _ (by decide), hLw])
  have hacc2 : ∀ evm, evalExpr? config (frame L2) evm (.var "account") =
      .ok (.address (AccountAddress.ofNat (argWord I).toNat)) := fun evm =>
    evalVar _ _ "account" _ (by rw [hL2def, store_get_ne _ _ (by decide), hL1def, store_get_ne _ _ (by decide), hLacc])
  have hnone2 : L2.get? "nextId" = none ∧ L2.get? "entries" = none ∧ L2.get? "ids" = none ∧ L2.get? "totalWeight" = none := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      rw [hL2def, store_get_ne _ _ (by decide), hL1def, store_get_ne _ _ (by decide)] <;> assumption
  have hnidlt : nid.toNat < UInt256.size := nid.val.isLt
  by_cases hfit1 : nid.toNat + 1 < UInt256.size
  swap
  · obtain ⟨_, _, rd5⟩ := registryBlocks.registry_block_944_taken (by simp)
      (by
        rw [ulit_toNat' 320 (by decide), slotWord_eq]
        rw [show memLoad (UInt256.ofNat 320) (nid.toByteArray.write 0 (rM1 m wgt I) 320 32) = nid from rM2_load320 m hm wgt I nid]
        rw [u256_add_overflow_lt nid (UInt256.ofNat 1) (by rw [ulit_toNat' 1 (by decide)]; omega)]
        decide) (by jump_dest) rd4
    have rd6 := registryBlocks.registry_block_1661 (by simp [registryBlocks.registry_block_944_taken_stack]) rd5
    refine RDrev.reEquivExecutionRevert hcode rd6 hd hdec (ExecFuncBody.execBlockRevert (hprefix _ ?_))
    exact ExecBlock.consNormal hcheck (ExecBlock.consNormal (ExecStmt.requireTrue hgt')
      (ExecBlock.consNormal (ExecStmt.letDecl hidRead)
        (ExecBlock.consRevert (ExecStmt.assignExprRevert
          (evalExpr_uint256_add_overflow (hid _) (evalExpr_intLit_word _ 1 (by decide))
            (by rw [ulit_toNat' 1 (by decide)]; omega))))))
  obtain ⟨_, _, rd5⟩ := registryBlocks.registry_block_944_fallthrough (by simp)
    (by
      rw [ulit_toNat' 320 (by decide), slotWord_eq]
      rw [show memLoad (UInt256.ofNat 320) (nid.toByteArray.write 0 (rM1 m wgt I) 320 32) = nid from rM2_load320 m hm wgt I nid]
      exact ult_zero (by rw [uadd_toNat, ulit_toNat' 1 (by decide), Nat.mod_eq_of_lt hfit1]; omega)) rd4
  simp only [registryBlocks.registry_block_944_fallthrough_stack, registryBlocks.registry_block_944_fallthrough_memory,
    ulit_toNat' 320 (by decide)] at rd5
  rw [slotWord_eq, show memLoad (UInt256.ofNat 320) (nid.toByteArray.write 0 (rM1 m wgt I) 320 32) = nid from
    rM2_load320 m hm wgt I nid] at rd5
  -- Stele: `nextId = id + 1`
  have hadd1 := evalExpr_uint256_add (hid (initState σ σ₀ (Sat256.ofUInt256 g) A I)) (evalExpr_intLit_word _ 1 (by decide))
    (by rw [ulit_toNat' 1 (by decide)]; exact hfit1)
  have hassign1 : assignStorageRef? config (frame L2) (initState σ σ₀ (Sat256.ofUInt256 g) A I) .storage nextIdRef
      (uint256Value (nid + UInt256.ofNat 1)) =
      .ok (frame L2, Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner (UInt256.ofNat 19)
        (nid + UInt256.ofNat 1)) := by
    apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "nextId", steps := [] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc (UInt256.ofNat 19))
      (hbase := hnone2.1) (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
    erw [storageLocStore_uint256]
    rfl
  by_cases hperm : I.perm = true
  swap
  · have hpf : I.perm = false := by simpa using hperm
    have r1 := rd5.swap1 (by native_decide) (by evm_ov)
    have r2 := r1.pop (by native_decide) (by evm_ov)
    have r3 := r2.push1 (UInt256.ofNat 19) (by native_decide) (by evm_ov)
    have rs := r3.sstoreStatic hpf (by native_decide) (by evm_ov)
    refine RDstatic.reEquivStaticHalt hcode rs hd hdec (ExecFuncBody.execBlockStatic (hprefix _ ?_))
    exact ExecBlock.consNormal hcheck (ExecBlock.consNormal (ExecStmt.requireTrue hgt')
      (ExecBlock.consNormal (ExecStmt.letDecl hidRead)
        (ExecBlock.consStatic (ExecStmt.assignStatic hadd1 hassign1 (by show I.perm = false; exact hpf)))))
  set evm1 := Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner (UInt256.ofNat 19) (nid + UInt256.ofNat 1)
    with hevm1
  have hs1 : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I (rσ1 σ I) evm1 := SourceState.init.storageWrite _ _
  have hlit := evalEntryLit L2 evm1 (AccountAddress.ofNat (argWord I).toNat) wgt
    (by rw [hL2def, store_get_ne _ _ (by decide), hL1def, store_get_ne _ _ (by decide), hLacc])
    (by rw [hL2def, store_get_ne _ _ (by decide), hL1def, store_get_ne _ _ (by decide), hLw])
  set evm4 := Stele.EVM.storageStore (Stele.EVM.storageStore (Stele.EVM.storageStore evm1 I.codeOwner (entrySlot nid) (argWord I))
    I.codeOwner (entrySlot nid + UInt256.ofNat 1) wgt) I.codeOwner (entrySlot nid + UInt256.ofNat 2) (UInt256.ofNat 1) with hevm4
  have hassign2 : assignStorageRef? config (frame L2) evm1 .storage entryIdRef
      (.struct "Entry" [("account", .address (AccountAddress.ofNat (argWord I).toNat)), ("weight", uint256Value wgt),
        ("active", .bool true)]) = .ok (frame L2, evm4) := by
    have h2 := assignEntry L2 evm1 nid (AccountAddress.ofNat (argWord I).toNat) wgt (by rw [hL2def, store_get_self]) hnone2.2.1
    simp only [hs1.env, word_roundtrip hcanon] at h2
    exact h2
  have hs4 : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I (rσ4 σ I wgt) evm4 :=
    ((hs1.storageWrite _ _).storageWrite _ _).storageWrite _ _
  -- pc 967: the capacity check on the length word as it is after the entry stores (both sides
  -- read it raw, so the entry slots may even alias it)
  obtain ⟨hm256, hm288, hm320⟩ := rM3_load m hm wgt I nid
  have hkec := keccak_entry_over (rM2 m wgt I nid) (by rw [(rM_sizes m hm wgt I nid).2.2.1]; omega) nid
  by_cases hfull : (rLen σ I wgt).toNat ≤ 15
  swap
  · obtain ⟨_, _, rd6⟩ := registryBlocks.registry_block_967_taken (by simp) hperm
      (by
        simp only [ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
        rw [rM2_load320 m hm, hkec, hm256, hm288, slotWord_eq]
        rw [ugt_one (a := rLen σ I wgt) (by rw [ulit_toNat' 15 (by decide)]; omega)]
        decide) (by jump_dest) rd5
    have rd7 := registryBlocks.registry_block_1661 (by simp [registryBlocks.registry_block_967_taken_stack]) rd6
    refine RDrev.reEquivExecutionRevert hcode rd7 hd hdec (ExecFuncBody.execBlockRevert (hprefix _ ?_))
    exact ExecBlock.consNormal hcheck (ExecBlock.consNormal (ExecStmt.requireTrue hgt')
      (ExecBlock.consNormal (ExecStmt.letDecl hidRead)
        (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr hperm) hadd1 hassign1)
          (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs1.env] using hperm)) hlit hassign2)
            (ExecBlock.consRevert (ExecStmt.pushValStoreRevert (hid _)
              (pushArray_vyper_full (hbackend := rfl) (hcheck := rfl) (hbounds := rfl) (hanchor := rfl)
                (hbase := hnone2.2.2.1) (er := { base := "ids", steps := [] })
                (elem := .elem (.int (.uint ⟨256, by decide⟩)))
                (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
                (hty := by show storageTypeAt? contract.storage _ = _; decide) (hnotrans := rfl)
                (by rw [hs4.storageRead]; show 16 ≤ (rLen σ I wgt).toNat; omega))))))))
  have hlen16 : (rLen σ I wgt).toNat ≤ 16 := by omega
  obtain ⟨_, _, rd6⟩ := registryBlocks.registry_block_967_fallthrough (by simp) hperm
    (by
      simp only [ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl]
      rw [rM2_load320 m hm, hkec, hm256, hm288, slotWord_eq]
      exact ugt_zero (a := rLen σ I wgt) (by rw [ulit_toNat' 15 (by decide)]; omega)) rd5
  simp only [registryBlocks.registry_block_967_fallthrough_stack, registryBlocks.registry_block_967_fallthrough_memory,
    ulit_toNat' 32 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd6
  rw [rM2_load320 m hm, hkec, hm256, hm288, slotWord_eq] at rd6
  -- Stele: `ids.append(id)`
  have hofnat : UInt256.ofNat ((rLen σ I wgt).toNat + 1) = rLen σ I wgt + UInt256.ofNat 1 := by
    have h := u256_ofNat_toNat_add_eq_add_of_lt (rLen σ I wgt) (UInt256.ofNat 1)
      (by rw [ulit_toNat' 1 (by decide)]; exact lt_size_of_lt_sign (by omega))
    rwa [ulit_toNat' 1 (by decide)] at h
  set evm6 := Stele.EVM.storageStore (Stele.EVM.storageStore evm4 I.codeOwner (UInt256.ofNat 3 + rLen σ I wgt) nid)
    I.codeOwner (UInt256.ofNat 2) (rLen σ I wgt + UInt256.ofNat 1) with hevm6
  have hpush : pushArray? config (frame L2) evm4 idsRef0 (some (uint256Value nid)) = .ok evm6 := by
    have h := pushIds L2 evm4 nid hnone2.2.2.1 (by rw [hs4.storageRead]; show (rLen σ I wgt).toNat < 16; omega)
    rw [hs4.storageRead] at h
    simp only [storageStore_executionEnv, hs4.env] at h
    rw [h]
    show EvalResult.ok (Stele.EVM.storageStore (Stele.EVM.storageStore evm4 I.codeOwner
      (UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat ((keyValueToWord (.int (Int.ofNat (rLen σ I wgt).toNat))).toNat * 1)) nid)
      I.codeOwner (UInt256.ofNat 2) (UInt256.ofNat ((rLen σ I wgt).toNat + 1))) = _
    rw [idsSlot_eq, hofnat]
  have hs6 : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I (rσ6 σ I wgt) evm6 :=
    (hs4.storageWrite _ _).storageWrite _ _
  have htw : evalExpr? config (frame L2) evm6 (.storage twRef') = .ok (uint256Value (rTw σ I wgt)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "totalWeight", steps := [] }) (physicalSlot := UInt256.ofNat 20) (hbase := hnone2.2.2.2)
        (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl), hs6.storageRead]
    rfl
  -- pc 1021
  by_cases hfit2 : (rTw σ I wgt).toNat + wgt.toNat < UInt256.size
  swap
  · obtain ⟨_, _, rd7⟩ := registryBlocks.registry_block_1021_taken (by simp) hperm
      (by
        rw [hm320, hm288, slotWord_eq, u256_add_overflow_lt (rTw σ I wgt) wgt (by omega)]
        decide) (by jump_dest) rd6
    have rd8 := registryBlocks.registry_block_1661 (by simp [registryBlocks.registry_block_1021_taken_stack]) rd7
    refine RDrev.reEquivExecutionRevert hcode rd8 hd hdec (ExecFuncBody.execBlockRevert (hprefix _ ?_))
    exact ExecBlock.consNormal hcheck (ExecBlock.consNormal (ExecStmt.requireTrue hgt')
      (ExecBlock.consNormal (ExecStmt.letDecl hidRead)
        (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr hperm) hadd1 hassign1)
          (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs1.env] using hperm)) hlit hassign2)
            (ExecBlock.consNormal (ExecStmt.pushVal (hperm := by simpa only [hs4.env] using hperm) (hid _) hpush)
              (ExecBlock.consRevert (ExecStmt.assignExprRevert
                (evalExpr_uint256_add_overflow htw (hw2 _) (by omega)))))))))
  have hnoover : (rTw σ I wgt).toNat ≤ (rTw σ I wgt + wgt).toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit2]; omega
  obtain ⟨_, _, rd7⟩ := registryBlocks.registry_block_1021_fallthrough (by simp) hperm
    (by
      rw [hm320, hm288, slotWord_eq]
      exact ult_zero hnoover) rd6
  simp only [registryBlocks.registry_block_1021_fallthrough_stack] at rd7
  rw [hm320, hm288, slotWord_eq] at rd7
  have rd8 := registryBlocks.registry_block_1055 (by simp) hperm rd7
  rw [ulit_toNat' 352 (by decide), ulit_toNat' 320 (by decide), ulit_toNat' 32 (by decide), hm288,
    rM3_return m hm wgt I nid wgt] at rd8
  have hadd3 := evalExpr_uint256_add htw (hw2 _) hfit2
  have hassign3 : assignStorageRef? config (frame L2) evm6 .storage twRef' (uint256Value (rTw σ I wgt + wgt)) =
      .ok (frame L2, Stele.EVM.storageStore evm6 I.codeOwner (UInt256.ofNat 20) (rTw σ I wgt + wgt)) := by
    apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "totalWeight", steps := [] })
      (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc (UInt256.ofNat 20))
      (hbase := hnone2.2.2.2) (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)
    erw [storageLocStore_uint256, hs6.env]
  have hemit : evalExprs? config (frame L2) (Stele.EVM.storageStore evm6 I.codeOwner (UInt256.ofNat 20) (rTw σ I wgt + wgt))
      [.var "id", .var "account", .var "weight"] =
      .ok [uint256Value nid, .address (AccountAddress.ofNat (argWord I).toNat), uint256Value wgt] := by
    rw [evalExprs?, hid, evalExprs?, hacc2, evalExprs?, hw2, evalExprs?]
    rfl
  have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) callargs t.body
      (.returned (frame L2) (Stele.EVM.storageStore evm6 I.codeOwner (UInt256.ofNat 20) (rTw σ I wgt + wgt))
        (some [uint256Value nid])) :=
    ExecFuncBody.execBlockRet (hprefix _
      (ExecBlock.consNormal hcheck (ExecBlock.consNormal (ExecStmt.requireTrue hgt')
        (ExecBlock.consNormal (ExecStmt.letDecl hidRead)
          (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr hperm) hadd1 hassign1)
            (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs1.env] using hperm)) hlit hassign2)
              (ExecBlock.consNormal (ExecStmt.pushVal (hperm := by simpa only [hs4.env] using hperm) (hid _) hpush)
                (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs6.env] using hperm)) hadd3 hassign3)
                  (ExecBlock.consNormal (ExecStmt.emit (hperm := by simpa only [storageStore_executionEnv, hs6.env] using hperm) hemit)
                    (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (hid _)))))))))))))
  exact rd8.reEquivExecutionGen hcode hd hdec hbody ((hs6.storageWrite _ _).accounts)
    (by rw [hret]; exact returnEquiv_of_encode (uint256ReturnEncoding _))

/-! ### The two selectors -/

abbrev raStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "account" (.address (AccountAddress.ofNat (argWord I).toNat))

theorem raDecode_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hcanon : (argWord I).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (register_addressTransition.params.map Param.name)
      (transitionSignature register_addressTransition).paramTypes I.calldata = some (raStore I) := by
  rw [argWord_eq] at hcanon
  simpa [config, contract, Syntax.contractSyntax, register_addressTransition, raStore, argWord_eq] using
    decodeCalldataWithMode_vyper_address_ok (cd := I.calldata) (x := "account") hsz36 hcanon

theorem raDecode_short {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (register_addressTransition.params.map Param.name)
      (transitionSignature register_addressTransition).paramTypes I.calldata = none := by
  simpa [config, contract, Syntax.contractSyntax, register_addressTransition] using
    decodeCalldataWithMode_vyper_address_none_short (cd := I.calldata) (x := "account") hsz hshort

theorem raDecode_noncanon {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size)
    (hnc : ¬ (argWord I).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (register_addressTransition.params.map Param.name)
      (transitionSignature register_addressTransition).paramTypes I.calldata = none := by
  rw [argWord_eq] at hnc
  simpa [config, contract, Syntax.contractSyntax, register_addressTransition] using
    decodeCalldataWithMode_vyper_address_none_noncanon (cd := I.calldata) (x := "account") hsz36 hnc

/-- `register(address)`: the theorem `Correct.lean` routes selector 2 to. -/
theorem registryRegister_addressBody {σ σ₀ A I} {g : UInt256} (hwf : storageWF σ I)
    (hcode : I.code = registryBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (registrySelBytes 2)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (registrySelBytes 2) rfl hsel
  obtain ⟨_, _, rd⟩ := registryReachRegister_addressBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some register_addressTransition :=
    registryDispatch_register_address (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) hsel
  by_cases hshort : I.calldata.size < 36
  · have rd1 := registryBlocks.registry_block_716_taken (by simp) (guard_short hsize hshort) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivDecodingFailed hcode rd2 hd (raDecode_short hsz hshort)
  have hsz36 : 36 ≤ I.calldata.size := by omega
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := registryBlocks.registry_block_716_taken (by simp) (guard_wv hwv) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode hd
      (fun _ => by rw [register_addressBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := registryBlocks.registry_block_716_fallthrough (by simp) (guard_ok hwv hsz36 hsize) rd
  have rd2 := registryBlocks.registry_block_726 (by simp) (by jump_dest) rd1
  simp only [registryBlocks.registry_block_726_memory, ulit_toNat' 288 (by decide)] at rd2
  by_cases hcanon : (argWord I).toNat < EVM.addressModulus
  swap
  · have rd3 := registryBlocks.registry_block_793_taken (by simp)
      (by intro h; exact hcanon (u256_lt_addressModulus_of_shiftRight160_zero _ h)) (by jump_dest) rd2
    have rd4 := registryBlocks.registry_block_1661 (by simp [registryBlocks.registry_block_793_taken_stack]) rd3
    exact RDrev.reEquivDecodingFailed hcode rd4 hd (raDecode_noncanon hsz36 hcanon)
  have rd3 := registryBlocks.registry_block_793_fallthrough (by simp) (u256_shiftRight160_zero_of_lt _ hcanon) rd2
  simp only [registryBlocks.registry_block_793_fallthrough_stack] at rd3
  have hcv : evalExpr? config (frame (raStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simpa [initState] using hwv)
  refine registerTail hwf hcode 2 (by decide) (UInt256.ofNat 1) rd3 hcanon register_addressTransition hd (raStore I)
    (raDecode_ok hsz36 hcanon) rfl ((raStore I).insert "weight" (uint256Value (UInt256.ofNat 1)))
    (by rw [store_get_ne _ _ (by decide), store_get_self]) (store_get_self _ _ _) (by simp) (by simp) (by simp) (by simp) ?_
  intro result h
  rw [register_addressBody_eq]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hcv)
    (ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_intLit_word _ 1 (by decide))) h)

end Tests.Pipeline.VyperRegistry
