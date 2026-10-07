import Benchmarks.Dss.GemJoin.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.GemJoin

/-! ## `deny(address)` -/

def denyPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (relyUsrStorageSlot I) ⟨0⟩

theorem gemJoinDecode_deny_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata = some (relyStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["usr"] [addr] I.calldata = _
  simpa [relyStore, relyUsrValue, relyUsrWord, calldataWord] using
    decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36

theorem gemJoinDecode_deny_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["usr"] [addr] I.calldata = none
  simpa using decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr")
    hsz4 hshort

theorem denyAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := relyStore I } evm
      .storage (wardsRef (.var "usr")) (.int 0) =
        .ok ({ contract := contract, locals := relyStore I }, denyPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (relyUsrStorageSlot I))
      (hbase := relyStore_wards I)
      (her := evalStorageRef_rely_usr evm I)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [denyPostState, wordLoc, uint256Loc] using
    storageLocStore_uint256 evm (relyUsrStorageSlot I) ⟨0⟩

theorem gemJoinDenyBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    ExecTransitionBody config contract evm (relyStore I) denyTransition.body
      (.returned { contract := contract, locals := relyStore I } (denyPostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [denyTransition, nonpayable, auth] using
    nonpayableRequireAssignStorageBlock
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (evm := evm)
      (evm' := denyPostState evm I)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 0)
      (ref := wardsRef (.var "usr"))
      (value := .int 0)
      hwv
      (evalExpr_auth_true_of_wards_none evm I (relyStore I) (relyStore_wards I) hsrc hauth)
      (by simp [evalExpr?, pure])
      (denyAssign evm I)

theorem gemJoinDenyBodyStatic (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (relyStore I) denyTransition.body
      .staticViolation := by
  refine ExecFuncBody.execBlockStatic ?_
  simpa [denyTransition, nonpayable, auth] using
    nonpayableRequireAssignStorageBlockStatic
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 0)
      (ref := wardsRef (.var "usr"))
      (value := .int 0)
      (rest := [])
      hwv
      (evalExpr_auth_true_of_wards_none evm I (relyStore I) (relyStore_wards I) hsrc hauth)
      (by simp [evalExpr?, pure])
      (denyAssign evm I)
      hperm

theorem gemJoinDenyBodyReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (relyStore I) denyTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [denyTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := relyStore I })
      (evm := evm)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.assign .storage (wardsRef (.var "usr")) (.intLit 0)])
      hwv
      (evalExpr_auth_false_of_wards_none evm I (relyStore I) (relyStore_wards I) hsrc hauth)

theorem gemJoinReachDenyBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (gemJoinSelBytes 2)) :
    ∃ k C, RD gemJoinBytecode I g (initState σ σ₀ g A I)
        ⟨336⟩ [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : gemJoinSelWord I = ⟨0x9c52a7f1⟩ :=
    gemJoinSelWord_eq_of_beq I hsz 0x9c 0x52 0xa7 0xf1 ⟨0x9c52a7f1⟩
      (by native_decide) (by simpa [gemJoinSelBytes] using hsel)
  have hroot :
      UInt256.gt (armSelNat gemJoinBytecode gemJoinRootSplitPc) (gemJoinSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinHighFirstArmPc j))
        (gemJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinHighFirstArmPc 1))
        (gemJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact gemJoinReachHighBody 1 (by omega) ⟨336⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem gemJoinDenyX_decoded {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD gemJoinBytecode I g
      (initState σ σ₀ g A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD gemJoinBytecode I g (initState σ σ₀ g A I) ⟨1353⟩
        [relyUsrMaskedWord I, ⟨254⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := gemJoinBytecode) (sel := sel) (entry := ⟨336⟩) (ret := ⟨254⟩)
    (decoded := ⟨358⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := gemJoinBytecode) (decoded := ⟨358⟩) (ret := ⟨254⟩) (routine := ⟨1353⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [relyUsrMaskedWord, relyUsrWord, calldataWord] using hroutine⟩

theorem gemJoinDenyX_shortarg {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD gemJoinBytecode I g
      (initState σ σ₀ g A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev gemJoinBytecode g (initState σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := gemJoinBytecode) (sel := sel) (entry := ⟨336⟩) (ret := ⟨254⟩)
    (decoded := ⟨358⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem gemJoinDenyX_authorized {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD gemJoinBytecode I g s0 ⟨1353⟩
      [relyUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD gemJoinBytecode I g s0 ⟨1446⟩
      [relyUsrMaskedWord I, ⟨254⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1359pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1360 := rd1359pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1364pre := evm_run rd1360 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1365 := rd1364pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1368pre := evm_run rd1365 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1369 := rd1368pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1370, C1370, rd1370raw⟩ := rd1369.sload (by native_decide) (by evm_ov)
  have rd1370 : RD gemJoinBytecode I g s0 ⟨1370⟩
      (relyAuthWord σ I :: relyUsrMaskedWord I :: ⟨254⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k1370 C1370 := by
    simpa [relyAuthWord, solcSlotWordAt, relyAuthStorageSlot_eq_mapSlot_source I] using rd1370raw
  have rd1373pre := evm_run rd1370 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1373pre
  have rd1376 := rd1373pre.pushConst (⟨1446⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1376.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem gemJoinDenyX_unauthorized {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD gemJoinBytecode I g s0 ⟨1353⟩
      [relyUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev gemJoinBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1359pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1360 := rd1359pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1364pre := evm_run rd1360 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1365 := rd1364pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1368pre := evm_run rd1365 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1369 := rd1368pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1370, C1370, rd1370raw⟩ := rd1369.sload (by native_decide) (by evm_ov)
  have rd1370 : RD gemJoinBytecode I g s0 ⟨1370⟩
      (relyAuthWord σ I :: relyUsrMaskedWord I :: ⟨254⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k1370 C1370 := by
    simpa [relyAuthWord, solcSlotWordAt, relyAuthStorageSlot_eq_mapSlot_source I] using rd1370raw
  have rd1373pre := evm_run rd1370 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1373pre
  have rd1376 := rd1373pre.pushConst (⟨1446⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1377 := rd1376.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1377⟩)
    (len := ⟨22⟩)
    (rawWord := ⟨0x11d95b529bda5b8bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨82⟩)
    (word := ⟨0x47656d4a6f696e2f6e6f742d617574686f72697a656400000000000000000000⟩)
    (op := .PUSH22)
    (width := 22)
    rd1377
    (by
      unfold solcErrorStringRevertTailWf
      repeat' apply And.intro
      all_goals native_decide)
    (by decide)
    (by native_decide)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 2000000 in
theorem gemJoinDenyX_storeAuthorizedSplit {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (h : RD gemJoinBytecode I g s0 ⟨1446⟩
      [relyUsrMaskedWord I, ⟨254⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    (I.perm = true ∧
      RDret gemJoinBytecode g s0
        (sstoreAccountMap I.codeOwner σ (relyUsrStorageSlot I) ⟨0⟩)
        ByteArray.empty) ∨
      (I.perm = false ∧ RDstatic gemJoinBytecode g s0) := by
  have hstoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((relyStoreHashMem I).readWithPadding 0 64))) =
        mapSlot (relyUsrMaskedWord I) ⟨0⟩ := by
    simpa [relyStoreHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relyUsrMaskedWord I)
        (relyAuthHashMem_size I)
  have rd1457pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land (relyUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        = relyUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (relyUsrMaskedWord_canonical I)
  rw [hmask] at rd1457pre
  have rd1461pre := evm_run rd1457pre with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1462 := rd1461pre.mstore 0
    (wordAt0Mem (relyUsrMaskedWord I) (relyAuthHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1466pre := evm_run rd1462 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1467 := rd1466pre.mstore 0 (relyStoreHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1471pre := evm_run rd1467 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd1472 := rd1471pre.keccak256 0 (mapSlot (relyUsrMaskedWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hstoreSlot (by native_decide)
    (by evm_ov)
  have rd1474pre := evm_run rd1472 with [
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hstoreDec : decode gemJoinBytecode ⟨1474⟩ = some (.SSTORE, none) := by
    native_decide
  by_cases hperm : I.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      rd1474pre.sstoreStatic (by simpa using hperm) hstoreDec (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨_, _, rd1475raw⟩ := rd1474pre.sstore hperm hstoreDec
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1476pre := evm_run rd1475raw with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [relyStoreHashMem_size I]; decide)
        (relyStoreHashMem_read64 I))
      (by native_decide) (by evm_ov)]
  have rd1509 := rd1476pre.pushConst
    (⟨0x184450df2e323acec0ed3b5c7531b81f9b4cdef7914dfd4c0a4317416bb5251b⟩ : UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1511pre := evm_run rd1509 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1512 := RD.log2
    (a := ⟨128⟩) (b := ⟨0⟩)
    (c := ⟨0x184450df2e323acec0ed3b5c7531b81f9b4cdef7914dfd4c0a4317416bb5251b⟩)
    (d := relyUsrMaskedWord I)
    (t := [relyUsrMaskedWord I, ⟨254⟩, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat))
    rd1511pre (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1513pre := evm_run rd1512 with [
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rd255 := rd1513pre.jumpdest (by native_decide) (by evm_ov)
  simpa [relyUsrStorageSlot_eq_mapSlot_masked I] using
    RD.stop rd255 (by native_decide) (by evm_ov)

theorem gemJoinX_deny_okSplit {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD gemJoinBytecode I g
      (initState σ σ₀ g A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    (I.perm = true ∧
      RDret gemJoinBytecode g (initState σ σ₀ g A I)
        (sstoreAccountMap I.codeOwner σ (relyUsrStorageSlot I) ⟨0⟩)
        ByteArray.empty) ∨
      (I.perm = false ∧ RDstatic gemJoinBytecode g (initState σ σ₀ g A I)) := by
  obtain ⟨_, _, rd1353⟩ := gemJoinDenyX_decoded (g := g) hsz36 hsize hreach
  obtain ⟨_, _, rd1446⟩ := gemJoinDenyX_authorized (I := I) hauth rd1353
  exact gemJoinDenyX_storeAuthorizedSplit rd1446

theorem gemJoinX_deny_ok {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hauth : relyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD gemJoinBytecode I g
      (initState σ σ₀ g A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret gemJoinBytecode g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner σ (relyUsrStorageSlot I) ⟨0⟩)
      ByteArray.empty :=
  permSplit_true hperm (gemJoinX_deny_okSplit hsz36 hsize hauth hreach)

theorem gemJoinX_deny_unauthorized {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD gemJoinBytecode I g
      (initState σ σ₀ g A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev gemJoinBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd1353⟩ := gemJoinDenyX_decoded (g := g) hsz36 hsize hreach
  exact gemJoinDenyX_unauthorized (I := I) hauth rd1353

theorem gemJoinDenyBodyCoreOk
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
        (transitionSignature denyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : relyAuthWord σ I = ⟨1⟩ := hauth
  have hbody :
      ExecTransitionBody config contract evmSolm (relyStore I)
        denyTransition.body
        (.returned { contract := contract, locals := relyStore I }
          (denyPostState evmSolm I) none) := by
    simpa [evmSolm, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      gemJoinDenyBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (gemJoinX_deny_ok (g := Sat256.ofUInt256 g) hsz36 hsize hperm hauth hreach)
    |>.reEquivExecutionGen hcode hdispatch hdecode hbody
      (by
        simpa [denyPostState, evmSolm, initState, storageStore_accountMap,
          storageStore_executionEnv, sstoreAccountMap])
      (by
        simpa [denyTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem gemJoinDenyBodyCoreStatic
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = false) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
        (transitionSignature denyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : relyAuthWord σ I = ⟨1⟩ := hauth
  have hbody :
      ExecTransitionBody config contract evmSolm (relyStore I)
        denyTransition.body
        .staticViolation := by
    simpa [evmSolm, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      gemJoinDenyBodyStatic evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
        (by simp only [evmSolm, initState]; exact hperm)
  exact (permSplit_false hperm (gemJoinX_deny_okSplit
      (g := Sat256.ofUInt256 g) hsz36 hsize hauth hreach))
    |>.reEquivStaticHalt hcode hdispatch hdecode hbody

theorem gemJoinDenyBodyCoreUnauthorized
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
        (transitionSignature denyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hauthWord : relyAuthWord σ I ≠ ⟨1⟩ := hauth
  have hbody :
      ExecTransitionBody config contract evmSolm (relyStore I)
        denyTransition.body .reverted := by
    simpa [evmSolm, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      gemJoinDenyBodyReverts evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (gemJoinX_deny_unauthorized (g := Sat256.ofUInt256 g) hsz36 hsize hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinDenyBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨336⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  exact (gemJoinDenyX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (gemJoinDecode_deny_none_short hsz4 hshort)

theorem gemJoinDenyBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = gemJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (gemJoinSelBytes 2)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (gemJoinSelBytes 2) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some denyTransition :=
    gemJoinDispatchDeny hsel
  have hreach := gemJoinReachDenyBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ I = ⟨1⟩
    · exact gemJoinDenyBodyCoreOk hcode hsize hperm hwv hsz36 hauth hdispatch
        (gemJoinDecode_deny_ok hsz36) hreach
    · exact gemJoinDenyBodyCoreUnauthorized hcode hsize hwv hsz36 hauth hdispatch
        (gemJoinDecode_deny_ok hsz36) hreach
  · exact gemJoinDenyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

theorem gemJoinDenyBodyCoreAnyPerm {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = gemJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (gemJoinSelBytes 2)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  by_cases hperm : I.perm = true
  · exact gemJoinDenyBodyCore hcode hsize hperm hwv hsel
  have hstatic : I.perm = false := by simpa using hperm
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (gemJoinSelBytes 2) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some denyTransition :=
    gemJoinDispatchDeny hsel
  have hreach := gemJoinReachDenyBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ I = ⟨1⟩
    · exact gemJoinDenyBodyCoreStatic hcode hsize hstatic hwv hsz36 hauth hdispatch
        (gemJoinDecode_deny_ok hsz36) hreach
    · exact gemJoinDenyBodyCoreUnauthorized hcode hsize hwv hsz36 hauth hdispatch
        (gemJoinDecode_deny_ok hsz36) hreach
  · exact gemJoinDenyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.GemJoin
