import Benchmarks.Dss.Dai.Dispatch
import Benchmarks.Dss.Dai.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and source-level body for `rely(address)` -/

abbrev relyGuyWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev relyGuyMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (relyGuyWord I)

abbrev relySourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev relyGuyValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (relyGuyWord I).toNat)

abbrev relyGuyKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (relyGuyWord I).toNat)

abbrev relyAuthKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev relyStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "guy" (relyGuyValue I)

def relyGuyStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (relyGuyKey I)

def relyAuthStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (relyAuthKey I)

def relyAuthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (relyAuthStorageSlot I) ⟨0⟩)

def relyPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (relyGuyStorageSlot I) ⟨1⟩

abbrev relyGuyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (relyGuyKey I)] }

abbrev relyAuthEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (relyAuthKey I)] }

theorem relyStore_get_guy (I : ExecutionEnv) :
    (relyStore I).get? "guy" = some (relyGuyValue I) := by
  unfold relyStore
  simp

theorem relyStore_wards (I : ExecutionEnv) :
    (relyStore I).get? "wards" = none := by
  unfold relyStore
  rw [store_get_ne _ _ (by native_decide)]
  simp

theorem relyStore_index_guy (I : ExecutionEnv) :
    (relyStore I)["guy"] = relyGuyValue I := by
  unfold relyStore
  rw [Std.HashMap.getElem_insert]
  simp

theorem relySourceWord_toNat (I : ExecutionEnv) :
    (relySourceWord I).toNat = I.source.val := by
  unfold relySourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem relyGuyStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    relyGuyStorageSlot I = mapSlot (relyGuyMaskedWord I) ⟨0⟩ := by
  unfold relyGuyStorageSlot wardsSlot relyGuyKey relyGuyMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem relyAuthStorageSlot_eq_mapSlot_source (I : ExecutionEnv) :
    relyAuthStorageSlot I = mapSlot (relySourceWord I) ⟨0⟩ := by
  unfold relyAuthStorageSlot wardsSlot relyAuthKey relySourceWord
  rw [keyValueToWord_address]

theorem daiDecode_rely_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["guy"] [addr] I.calldata = _
  simpa [relyStore, relyGuyValue, relyGuyWord, calldataWord]
    using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "guy") hsz36

theorem daiDecode_rely_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["guy"] [addr] I.calldata = none
  simpa using decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "guy")
    hsz4 hshort

theorem evalStorageRef_rely_guy (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := relyStore I } evm
      (wardsRef (.var "guy")) = .ok (relyGuyEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, relyStore, relyGuyValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalStorageRef_rely_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := relyStore I } evm
      (wardsRef sender) = .ok (relyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, relyAuthEvaledRef,
    relyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem uint256_toNat_eq_one {a : UInt256} (h : a.toNat = 1) : a = ⟨1⟩ := by
  apply u256_inj
  simpa using h

theorem evalExpr_rely_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := relyStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := relyStore I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I) (.int uint256Int))
      (value := .int 1)
      (hbase := by
        simp [relyStore, wardsRef])
      (her := evalStorageRef_rely_auth evm I hsrc)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, relyAuthKey, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [wordLoc, uint256Loc, uint256Int, hload] using
          storageLocLoad_uint256 evm (relyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_rely_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := relyStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := relyStore I } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (relyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I) (.int uint256Int))
      (hbase := by
        simp [relyStore, wardsRef])
      (her := evalStorageRef_rely_auth evm I hsrc)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, relyAuthKey, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [wordLoc, uint256Loc, uint256Int] using
          storageLocLoad_uint256 evm (relyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (relyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (relyAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_rely_one (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := relyStore I } evm
      (.intLit 1) = .ok (.int 1) := by
  simp [evalExpr?, pure]

theorem relyAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := relyStore I } evm
      .storage (wardsRef (.var "guy")) (.int 1) =
        .ok ({ contract := contract, locals := relyStore I }, relyPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (relyGuyStorageSlot I) (.int uint256Int))
      (hbase := relyStore_wards I)
      (her := evalStorageRef_rely_guy evm I)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, relyGuyKey, uint256St])
      (hloc := by rfl)
  simpa [relyPostState, wordLoc, uint256Loc, uint256Int] using
    storageLocStore_uint256 evm (relyGuyStorageSlot I) ⟨1⟩

/-- The Solm `rely(address)` body stores `wards[guy] = 1` when `msg.sender` is authorized. -/
theorem daiRelyBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    ExecTransitionBody config contract evm (relyStore I) relyTransition.body
      (.returned { contract := contract, locals := relyStore I }
        (relyPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [relyTransition, nonpayable, auth] using
    nonpayableRequireAssignStorageBlock
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (evm := evm)
      (evm' := relyPostState evm I)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 1)
      (ref := wardsRef (.var "guy"))
      (value := .int 1)
      hwv
      (evalExpr_rely_auth_true evm I hsrc hauth)
      (evalExpr_rely_one evm I)
      (relyAssign evm I)

/-- The Solm `rely(address)` body reverts when `msg.sender` is not authorized. -/
theorem daiRelyBodyReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (relyStore I) relyTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [relyTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.assign .storage (wardsRef (.var "guy")) (.intLit 1)])
      hwv
      (evalExpr_rely_auth_false evm I hsrc hauth)

/-! ## EVM trace -/

noncomputable abbrev relyAuthHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (relySourceWord I) ⟨0⟩ solcFreePtrMem

noncomputable abbrev relyStoreHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (relyGuyMaskedWord I) ⟨0⟩ (relyAuthHashMem I)

theorem relyGuyMaskedWord_canonical (I : ExecutionEnv) :
    (relyGuyMaskedWord I).toNat < EVM.addressModulus := by
  unfold relyGuyMaskedWord
  rw [u256_land_comm solcAddrMask (relyGuyWord I)]
  exact solcAddrMask_result_canonical (relyGuyWord I)

theorem relyAuthHashMem_size (I : ExecutionEnv) :
    (relyAuthHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (relySourceWord I) ⟨0⟩ solcFreePtrMem_size

theorem relyAuthHashMem_read64 (I : ExecutionEnv) :
    (relyAuthHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (relySourceWord I) ⟨0⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem relyStoreHashMem_size (I : ExecutionEnv) :
    (relyStoreHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (relyGuyMaskedWord I) ⟨0⟩ (relyAuthHashMem_size I)

theorem relyNotAuthorizedWord :
    UInt256.shiftLeft (⟨0x11185a4bdb9bdd0b585d5d1a1bdc9a5e9959⟩ : UInt256) ⟨114⟩ =
      ⟨0x4461692f6e6f742d617574686f72697a65640000000000000000000000000000⟩ := by
  native_decide

theorem daiRelyX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨696⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2274⟩
        [relyGuyMaskedWord I, ⟨686⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd718⟩ := RD.daiOneAddressExternalLenOk
    (entry := ⟨696⟩) (ret := ⟨686⟩) (routine := ⟨2274⟩) hreach
    dai_one_address_external_entry_wf (by jump_dest) hsz36 hsize
  obtain ⟨_, _, rd2274⟩ := RD.daiOneAddressExternalMaskAndJumpMasked
    (entry := ⟨696⟩) (ret := ⟨686⟩) (routine := ⟨2274⟩) (R := [sel])
    rd718 dai_one_address_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [relyGuyMaskedWord, relyGuyWord, calldataWord] using rd2274⟩

theorem daiRelyX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨696⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.daiOneAddressExternalShort
    (entry := ⟨696⟩) (ret := ⟨686⟩) (routine := ⟨2274⟩)
    hreach dai_one_address_external_entry_wf hsz4 hsize hshort

set_option maxHeartbeats 1000000 in
theorem daiRelyX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD daiBytecode I g s0 ⟨2274⟩
      [relyGuyMaskedWord I, ⟨686⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨2363⟩
      [relyGuyMaskedWord I, ⟨686⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd2280pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2281 := rd2280pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2285pre := evm_run rd2281 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2286 := rd2285pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2290pre := evm_run rd2286 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2290 := rd2290pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k2291, C2291, rd2291raw⟩ := rd2290.sload (by native_decide) (by evm_ov)
  have rd2291 : RD daiBytecode I g s0 ⟨2291⟩
      (relyAuthWord σ I :: relyGuyMaskedWord I :: ⟨686⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2291 C2291 := by
    simpa [relyAuthWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd2291raw
  have rd2294pre := evm_run rd2291 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd2294pre
  have rd2297 := rd2294pre.pushConst (⟨2363⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2297.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiRelyX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD daiBytecode I g s0 ⟨2274⟩
      [relyGuyMaskedWord I, ⟨686⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd2280pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2281 := rd2280pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2285pre := evm_run rd2281 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2286 := rd2285pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2290pre := evm_run rd2286 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2290 := rd2290pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k2291, C2291, rd2291raw⟩ := rd2290.sload (by native_decide) (by evm_ov)
  have rd2291 : RD daiBytecode I g s0 ⟨2291⟩
      (relyAuthWord σ I :: relyGuyMaskedWord I :: ⟨686⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2291 C2291 := by
    simpa [relyAuthWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd2291raw
  have rd2294pre := evm_run rd2291 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd2294pre
  have rd2297 := rd2294pre.pushConst (⟨2363⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd2298 := rd2297.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨2298⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x11185a4bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨114⟩)
    (word := ⟨0x4461692f6e6f742d617574686f72697a65640000000000000000000000000000⟩)
    (op := .PUSH18)
    (width := 18)
    rd2298
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem daiRelyX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD daiBytecode I g s0 ⟨2363⟩
      [relyGuyMaskedWord I, ⟨686⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (relyGuyStorageSlot I) ⟨1⟩)
      ByteArray.empty := by
  have hstoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyStoreHashMem I).readWithPadding 0 64))) =
        mapSlot (relyGuyMaskedWord I) ⟨0⟩ := by
    simpa [relyStoreHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relyGuyMaskedWord I)
        (relyAuthHashMem_size I)
  have rd2372pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (relyGuyMaskedWord I)
        = relyGuyMaskedWord I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (relyGuyMaskedWord_canonical I)
  rw [hmask] at rd2372pre
  have rd2377pre := evm_run rd2372pre with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2378 := rd2377pre.mstore 0
    (wordAt0Mem (relyGuyMaskedWord I) (relyAuthHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2382pre := evm_run rd2378 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2383 := rd2382pre.mstore 0 (relyStoreHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2386pre := evm_run rd2383 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2387 := rd2386pre.keccak256 0 (mapSlot (relyGuyMaskedWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hstoreSlot (by native_decide)
    (by evm_ov)
  have rd2390pre := evm_run rd2387 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2391raw⟩ := rd2390pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd686 := rd2391raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd687 := rd686.jumpdest (by native_decide) (by evm_ov)
  simpa [relyGuyStorageSlot_eq_mapSlot_masked I] using
    RD.stop rd687 (by native_decide) (by evm_ov)

theorem daiX_rely_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hauth : relyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨696⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (relyGuyStorageSlot I) ⟨1⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd2274⟩ := daiRelyX_decoded (g := g) hsz36 hsize hreach
  obtain ⟨_, _, rd2363⟩ := daiRelyX_authorized (I := I) hauth rd2274
  exact daiRelyX_storeAuthorized hperm rd2363

theorem daiX_rely_unauthorized {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨696⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2274⟩ := daiRelyX_decoded (g := g) hsz36 hsize hreach
  exact daiRelyX_unauthorized (I := I) hauth rd2274

theorem daiRelyBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨696⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evmSolm (relyStore I)
        relyTransition.body
        (.returned { contract := contract, locals := relyStore I }
          (relyPostState evmSolm I) none) := by
    simpa [evmSolm, relyAuthWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      daiRelyBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (daiX_rely_ok (g := Sat256.ofUInt256 g) hsz36 hsize hperm hauth hreach)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by
        simp [relyPostState, evmSolm, initState, storageStore_createdAccounts])
      (by
        simpa [relyPostState, evmSolm, initState, storageStore_accountMap] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (relyGuyStorageSlot I) ⟨1⟩
            hAccounts)
      (by
        simpa [relyTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem daiRelyBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨696⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evmSolm (relyStore I)
        relyTransition.body .reverted := by
    simpa [evmSolm, relyAuthWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      daiRelyBodyReverts evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (daiX_rely_unauthorized (g := Sat256.ofUInt256 g) hsz36 hsize hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem daiRelyBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨696⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := daiDecode_rely_none_short (I := I) hsz4 hshort
  exact (daiRelyX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- `rely(address)` body refines its Solm transition. -/
theorem daiRelyBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 15))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 15) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some relyTransition :=
    daiDispatchRely hsel
  have hreach := daiReachRelyBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · exact daiRelyBodyCoreOk hcode hsize hperm hwv hsz36 hauth hdispatch
        (daiDecode_rely_ok hsz36) hreach hAccounts
    · exact daiRelyBodyCoreUnauthorized hcode hsize hwv hsz36 hauth hdispatch
        (daiDecode_rely_ok hsz36) hreach hAccounts
  · exact daiRelyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dai
