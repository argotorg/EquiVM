import Benchmarks.Dss.Dai.Dispatch
import Benchmarks.Dss.Dai.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and source-level body for `approve(address,uint256)` -/

abbrev approveUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev approveUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (approveUsrWord I)

abbrev approveWadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev approveOwnerWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev approveUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (approveUsrWord I).toNat)

abbrev approveWadValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (approveWadWord I).toNat)

abbrev approveOwnerKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev approveUsrKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (approveUsrWord I).toNat)

abbrev approveStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "usr" (approveUsrValue I)).insert "wad" (approveWadValue I)

def approveStorageSlot (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (approveOwnerKey I) (approveUsrKey I)

def approvePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (approveStorageSlot I) (approveWadWord I)

abbrev approveEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance", steps := [.mindex (approveOwnerKey I), .mindex (approveUsrKey I)] }

theorem approveStore_get_usr (I : ExecutionEnv) :
    (approveStore I).get? "usr" = some (approveUsrValue I) := by
  unfold approveStore
  rw [store_get_ne
    (L := (∅ : Store).insert "usr" (approveUsrValue I))
    (k := "wad") (a := "usr") (approveWadValue I) (by native_decide)]
  simp

theorem approveStore_get_wad (I : ExecutionEnv) :
    (approveStore I).get? "wad" = some (approveWadValue I) := by
  unfold approveStore
  simp

theorem approveStore_allowance (I : ExecutionEnv) :
    (approveStore I).get? "allowance" = none := by
  unfold approveStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
  simp

theorem approveStore_index_usr (I : ExecutionEnv) :
    (approveStore I)["usr"] = approveUsrValue I := by
  unfold approveStore
  rw [Std.HashMap.getElem_insert]
  simp

theorem approveOwnerWord_toNat (I : ExecutionEnv) :
    (approveOwnerWord I).toNat = I.source.val := by
  unfold approveOwnerWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem approveOwnerWord_canonical (I : ExecutionEnv) :
    (approveOwnerWord I).toNat < EVM.addressModulus := by
  rw [approveOwnerWord_toNat]
  change I.source.val < AccountAddress.size
  exact I.source.isLt

theorem approveStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    approveStorageSlot I =
      mapSlot (approveUsrMaskedWord I) (mapSlot (approveOwnerWord I) ⟨3⟩) := by
  unfold approveStorageSlot allowanceSlot allowanceOwnerSlot approveOwnerKey approveUsrKey
    approveUsrMaskedWord approveOwnerWord
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address]

theorem daiDecode_approve_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata =
        some (approveStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["usr", "wad"] [addr, uint256]
    I.calldata = _
  simpa [approveStore, approveUsrValue, approveWadValue, approveUsrWord, approveWadWord,
    calldataWord]
    using decodeCalldata_legacyAddress_uint256_ok
      (cd := I.calldata) (x := "usr") (y := "wad") hsz68

theorem daiDecode_approve_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["usr", "wad"] [addr, uint256]
    I.calldata = none
  simpa using decodeCalldata_legacyAddress_uint256_none_short
    (cd := I.calldata) (x := "usr") (y := "wad") hsz4 hshort

theorem evalExpr_approve_wad (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := approveStore I } evm
      (.var "wad") = .ok (approveWadValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [approveStore_get_wad]

theorem evalStorageRef_approve_allowance (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := approveStore I } evm
      (allowanceRef sender (.var "usr")) = .ok (approveEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, allowanceRef, sender, envValue, approveEvaledRef, hsrc,
    approveUsrValue, approveOwnerKey, approveUsrKey, valueToKey?, EvalResult.seqList,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, approveStore_get_usr,
    approveStore_index_usr]

theorem approveAssign (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := approveStore I } evm
      .storage (allowanceRef sender (.var "usr")) (approveWadValue I) =
        .ok ({ contract := contract, locals := approveStore I }, approvePostState evm I) := by
  simp only [allowanceRef]
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (approveStorageSlot I) (.int uint256Int))
      (hbase := approveStore_allowance I)
      (her := evalStorageRef_approve_allowance evm I hsrc)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, approveEvaledRef,
          approveOwnerKey, approveUsrKey, uint256St])
      (hloc := by rfl)
  simpa [approvePostState, wordLoc, uint256Loc, uint256Int] using
    storageLocStore_uint256 evm (approveStorageSlot I) (approveWadWord I)

/-- The Solm `approve(address,uint256)` body stores `allowance[msg.sender][usr] = wad`. -/
theorem daiApproveBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source) :
    ExecTransitionBody config contract evm (approveStore I) approveTransition.body
      (.returned { contract := contract, locals := approveStore I }
        (approvePostState evm I) (some [.bool true])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true h)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_approve_wad evm I) (approveAssign evm I hsrc)) ?_
  exact ExecBlock.consReturn
    (ExecStmt.return (evalExprs?_singleton (by simp [evalExpr?, pure])))

/-! ## EVM trace -/

noncomputable abbrev approveInnerMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (approveOwnerWord I) ⟨3⟩ solcFreePtrMem

noncomputable abbrev approveInnerSlot (I : ExecutionEnv) : UInt256 :=
  mapSlot (approveOwnerWord I) ⟨3⟩

noncomputable abbrev approveHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (approveUsrMaskedWord I) (approveInnerSlot I) (approveInnerMem I)

noncomputable abbrev approveLogMem (I : ExecutionEnv) : ByteArray :=
  solcScratchReturnMem (approveHashMem I) (approveWadWord I)

noncomputable abbrev approveBoolReturnMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)))).write 0
    (approveLogMem I) 128 32

theorem approveUsrMaskedWord_canonical (I : ExecutionEnv) :
    (approveUsrMaskedWord I).toNat < EVM.addressModulus := by
  unfold approveUsrMaskedWord
  rw [u256_land_comm solcAddrMask (approveUsrWord I)]
  exact solcAddrMask_result_canonical (approveUsrWord I)

theorem approveStorageSlot_eq_innerSlot (I : ExecutionEnv) :
    approveStorageSlot I = mapSlot (approveUsrMaskedWord I) (approveInnerSlot I) := by
  simpa [approveInnerSlot] using approveStorageSlot_eq_mapSlot_masked I

theorem approveInnerMem_size (I : ExecutionEnv) :
    (approveInnerMem I).size = 96 := by
  exact twoWordHashMem_size_96 (approveOwnerWord I) ⟨3⟩ solcFreePtrMem_size

theorem approveInnerMem_read64 (I : ExecutionEnv) :
    (approveInnerMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (approveOwnerWord I) ⟨3⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem approveHashMem_size (I : ExecutionEnv) :
    (approveHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (approveUsrMaskedWord I) (approveInnerSlot I)
    (approveInnerMem_size I)

theorem approveHashMem_read64 (I : ExecutionEnv) :
    (approveHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (approveUsrMaskedWord I) (approveInnerSlot I)
    (approveInnerMem_size I) (approveInnerMem_read64 I)

theorem approveHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (approveHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((approveHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact mloadFreePtrValue (by rw [approveHashMem_size]; decide) (by decide)
    (approveHashMem_read64 I)

theorem approveLogMem_size (I : ExecutionEnv) :
    (approveLogMem I).size = 160 := by
  exact solcScratchReturnMem_size (approveWadWord I) (approveHashMem_size I)

theorem approveLogMem_read64 (I : ExecutionEnv) :
    (approveLogMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact solcScratchReturnMem_read64 (approveWadWord I) (approveHashMem_size I)
    (approveHashMem_read64 I)

theorem approveLogMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (approveLogMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((approveLogMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact solcScratchReturnMem_mload64 (approveWadWord I) (approveHashMem_size I)
    (approveHashMem_read64 I)

theorem approveBoolReturnMem_size (I : ExecutionEnv) :
    (approveBoolReturnMem I).size = 160 := by
  unfold approveBoolReturnMem
  exact toByteArray_write32_size_of_le (approveLogMem I)
    (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) 128 160 160
    (approveLogMem_size I) (by rw [approveLogMem_size]; decide) (by decide)

theorem approveBoolReturnMem_read64 (I : ExecutionEnv) :
    (approveBoolReturnMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold approveBoolReturnMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [approveLogMem_size]; omega) (by omega)]
  exact approveLogMem_read64 I

theorem approveBoolReturnMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (approveBoolReturnMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((approveBoolReturnMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact mloadFreePtrValue (by rw [approveBoolReturnMem_size]; decide) (by decide)
    (approveBoolReturnMem_read64 I)

theorem approveBoolReturnMem_read128 (I : ExecutionEnv) :
    (approveBoolReturnMem I).readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) := by
  unfold approveBoolReturnMem
  exact toByteArray_write32_read_back (approveLogMem I)
    (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) 128
    (by rw [approveLogMem_size]; decide)

abbrev approveApprovalTopic : UInt256 :=
  ⟨0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925⟩

theorem daiApproveX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨452⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1302⟩
        [approveWadWord I, approveUsrMaskedWord I, ⟨496⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd474⟩ := RD.daiAddressUint256ExternalLenOk
    (entry := ⟨452⟩) (ret := ⟨496⟩) (routine := ⟨1302⟩) hreach
    dai_address_uint256_external_entry_wf (by jump_dest) hsz68 hsize
  obtain ⟨_, _, rd1302⟩ := RD.daiAddressUint256ExternalMaskAndJumpMasked
    (entry := ⟨452⟩) (ret := ⟨496⟩) (routine := ⟨1302⟩) (R := [sel])
    rd474 dai_address_uint256_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by
    simpa [approveWadWord, approveUsrMaskedWord, approveUsrWord, calldataWord] using rd1302⟩

theorem daiApproveX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨452⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.daiAddressUint256ExternalShort
    (entry := ⟨452⟩) (ret := ⟨496⟩) (routine := ⟨1302⟩)
    hreach dai_address_uint256_external_entry_wf hsz4 hsize hshort

set_option maxHeartbeats 1000000 in
theorem daiApproveX_logReady {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD daiBytecode I g s0 ⟨1302⟩
      [approveWadWord I, approveUsrMaskedWord I, ⟨496⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨496⟩ [⟨1⟩, sel]
      (approveLogMem I) (UInt256.ofNat 5) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (approveStorageSlot I) (approveWadWord I)) k' C' := by
  have hinnerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((approveInnerMem I).readWithPadding 0 64))) =
        approveInnerSlot I := by
    simpa [approveInnerMem, approveInnerSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨3⟩ : UInt256) (approveOwnerWord I)
        solcFreePtrMem_size
  have houterSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((approveHashMem I).readWithPadding 0 64))) =
        mapSlot (approveUsrMaskedWord I) (approveInnerSlot I) := by
    simpa [approveHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (approveInnerSlot I) (approveUsrMaskedWord I)
        (approveInnerMem_size I)
  have rd1308pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1309 := rd1308pre.mstore 0 (wordAt0Mem (approveOwnerWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1315pre := evm_run rd1309 with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1316 := rd1315pre.mstore 0 (approveInnerMem I) (UInt256.ofNat 3)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1320pre := evm_run rd1316 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rd1321 := rd1320pre.keccak256 0 (approveInnerSlot I) (UInt256.ofNat 3)
    (by native_decide) mem_cost hinnerSlot (by native_decide) (by evm_ov)
  have rd1333pre := evm_run rd1321 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land (approveUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        = approveUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (approveUsrMaskedWord_canonical I)
  rw [hmask] at rd1333pre
  have rd1334 := rd1333pre.mstore 0 (wordAt0Mem (approveUsrMaskedWord I) (approveInnerMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1336pre := evm_run rd1334 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rd1337 := rd1336pre.mstore 0 (approveHashMem I) (UInt256.ofNat 3)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1339pre := evm_run rd1337 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rd1340 := rd1339pre.keccak256 0
    (mapSlot (approveUsrMaskedWord I) (approveInnerSlot I)) (UInt256.ofNat 3)
    (by native_decide) mem_cost houterSlot (by native_decide) (by evm_ov)
  have rd1342pre := evm_run rd1340 with [
    raw dup7 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1343raw⟩ := rd1342pre.sstore hperm (by native_decide)
    (by change 9 ≤ 1024; decide)
  have rd1347pre := evm_run rd1343raw with [
    raw dup2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      (approveHashMem_mload64 I) (by decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1348 := rd1347pre.mstore 6 (approveLogMem I) (UInt256.ofNat 5)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1356pre := evm_run rd1348 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost
      (approveLogMem_mload64 I) (by decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  have rd1389 := rd1356pre.pushConst approveApprovalTopic (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd1395pre := evm_run rd1389 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1396 := rd1395pre.log3 0 (UInt256.ofNat 5) (by native_decide) hperm
    mem_cost (by decide) (by change 5 ≤ 1024; decide)
  have rd1404pre := evm_run rd1396 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [approveStorageSlot_eq_innerSlot I, approveOwnerWord] using
      rd1404pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiX_approve_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨452⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (approveStorageSlot I) (approveWadWord I))
      (UInt256.toByteArray ⟨1⟩) := by
  obtain ⟨_, _, rd1302⟩ := daiApproveX_decoded (g := g) hsz68 hsize hreach
  obtain ⟨_, _, rd496⟩ := daiApproveX_logReady (I := I) hperm rd1302
  have hretWf : solcReturnBoolFromMemWf daiBytecode ⟨496⟩ := by
    unfold solcReturnBoolFromMemWf
    repeat' first | apply And.intro | native_decide
  have hbool :
      UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ := by
    native_decide
  simpa [hbool] using
    RD.solcReturnBoolFromMem rd496 hretWf (approveLogMem_mload64 I) (by rfl)
      (approveBoolReturnMem_mload64 I) (approveBoolReturnMem_read128 I)
      (by simp only [List.length_singleton]; omega)

theorem daiApproveBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hdispatch : dispatchMsg contract I.calldata = some approveTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (approveTransition.params.map Param.name)
        (transitionSignature approveTransition).paramTypes I.calldata =
          some (approveStore I))
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨452⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evmSolm (approveStore I)
        approveTransition.body
        (.returned { contract := contract, locals := approveStore I }
          (approvePostState evmSolm I) (some [.bool true])) := by
    simpa [evmSolm] using
      daiApproveBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
  exact (daiX_approve_ok (g := Sat256.ofUInt256 g) hsz68 hsize hperm hreach)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by
        simp [approvePostState, evmSolm, initState, storageStore_createdAccounts])
      (by
        simpa [approvePostState, evmSolm, initState, storageStore_accountMap] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (approveStorageSlot I)
            (approveWadWord I) hAccounts)
      (returnEquiv_of_encode
        (by simpa [boolTy] using boolTrueReturnEncoding))

theorem daiApproveBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some approveTransition)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨452⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := daiDecode_approve_none_short (I := I) hsz4 hshort
  exact (daiApproveX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- `approve(address,uint256)` body refines its Solm transition. -/
theorem daiApproveBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 1))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 1) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some approveTransition :=
    daiDispatchApprove hsel
  have hreach := daiReachApproveBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · exact daiApproveBodyCoreOk hcode hsize hperm hwv hsz68 hdispatch
      (daiDecode_approve_ok hsz68) hreach hAccounts
  · exact daiApproveBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dai
