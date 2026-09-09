import Benchmarks.Dss.Flopper.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper

/-! ## `deny(address)` -/

def denyPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (relyUsrStorageSlot I) ⟨0⟩

theorem flopperDecode_deny_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata = some (relyStore I) := by
  simpa [config, denyTransition, relyStore, relyUsrValue, relyUsrWord, calldataWord] using
    decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36

theorem flopperDecode_deny_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata = none := by
  simpa [config, denyTransition] using
    decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort

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

theorem flopperDenyBodyReturns (evm : EVM.State) (I : ExecutionEnv)
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
      (evalExpr_rely_auth_true evm I hsrc hauth)
      (by simp [evalExpr?, pure])
      (denyAssign evm I)

theorem flopperDenyBodyReverts (evm : EVM.State) (I : ExecutionEnv)
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
      (evalExpr_rely_auth_false evm I hsrc hauth)

theorem flopperReachDenyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flopperSelBytes 5)) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨678⟩ [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flopperSelWord I = ⟨0x9c52a7f1⟩ := by
    simpa [flopperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0x9c 0x52 0xa7 0xf1 ⟨0x9c52a7f1⟩
        (by decide +native) (by simpa [flopperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hhigh : UInt256.gt (armSelNat flopperBytecode flopperHighSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  obtain ⟨_, _, hfirst⟩ :=
    flopperReachHighLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have heq0 : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighLowFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighLowFirstArmPc 3))
        (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact RD.dispatchTo ⟨678⟩ 3 hfirst
    (fun j hj => flopperHighLowArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by decide +native) (by simp)

theorem flopperDenyX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨678⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3282⟩
        [relyUsrMaskedWord I, ⟨334⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := flopperBytecode) (sel := sel) (entry := ⟨678⟩) (ret := ⟨334⟩)
    (decoded := ⟨700⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := flopperBytecode) (decoded := ⟨700⟩) (ret := ⟨334⟩) (routine := ⟨3282⟩)
    (R := [sel]) hdecoded
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [relyUsrMaskedWord, relyUsrWord, calldataWord] using hroutine⟩

theorem flopperDenyX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨678⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flopperBytecode) (sel := sel) (entry := ⟨678⟩) (ret := ⟨334⟩)
    (decoded := ⟨700⟩) (need := ⟨32⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt

set_option maxHeartbeats 1000000 in
theorem flopperDenyX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD flopperBytecode I g s0 ⟨3282⟩
      [relyUsrMaskedWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flopperBytecode I g s0 ⟨3375⟩
      [relyUsrMaskedWord I, ⟨334⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1844pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd1845 := rd1844pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1849pre := evm_run rd1845 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1850 := rd1849pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1853pre := evm_run rd1850 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1854 := rd1853pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by decide +native) mem_cost hauthSlot (by decide +native)
    (by evm_ov)
  obtain ⟨k1855, C1855, rd1855raw⟩ := rd1854.sload (by decide +native) (by evm_ov)
  have rd1855 : RD flopperBytecode I g s0 ⟨3299⟩
      (relyAuthWord σ I :: relyUsrMaskedWord I :: ⟨334⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1855 C1855 := by
    simpa [relyAuthWord, flopperSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1855raw
  have rd1858pre := evm_run rd1855 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1858pre
  have rd1861 := rd1858pre.pushConst (⟨3375⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  exact ⟨_, _, rd1861.jumpiT (by decide +native) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flopperDenyX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD flopperBytecode I g s0 ⟨3282⟩
      [relyUsrMaskedWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1844pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd1845 := rd1844pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1849pre := evm_run rd1845 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1850 := rd1849pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd1853pre := evm_run rd1850 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1854 := rd1853pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by decide +native) mem_cost hauthSlot (by decide +native)
    (by evm_ov)
  obtain ⟨k1855, C1855, rd1855raw⟩ := rd1854.sload (by decide +native) (by evm_ov)
  have rd1855 : RD flopperBytecode I g s0 ⟨3299⟩
      (relyAuthWord σ I :: relyUsrMaskedWord I :: ⟨334⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1855 C1855 := by
    simpa [relyAuthWord, flopperSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1855raw
  have rd1858pre := evm_run rd1855 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1858pre
  have rd1861 := rd1858pre.pushConst (⟨3375⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  have rd1862 := rd1861.jumpiNT (by decide +native) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3306⟩)
    (len := ⟨22⟩)
    (rawWord := ⟨0x119b1bdc1c195c8bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨82⟩)
    (word := ⟨0x466c6f707065722f6e6f742d617574686f72697a656400000000000000000000⟩)
    (op := .PUSH22)
    (width := 22)
    rd1862
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem flopperDenyX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD flopperBytecode I g s0 ⟨3375⟩
      [relyUsrMaskedWord I, ⟨334⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flopperBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (relyUsrStorageSlot I) ⟨0⟩)
      ByteArray.empty := by
  have hstoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyStoreHashMem I).readWithPadding 0 64))) =
        mapSlot (relyUsrMaskedWord I) ⟨0⟩ := by
    simpa [relyStoreHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relyUsrMaskedWord I)
        (relyAuthHashMem_size I)
  have rd1936pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov)]
  have hmask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (relyUsrMaskedWord I)
        = relyUsrMaskedWord I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (relyUsrMaskedWord_canonical I)
  rw [hmask] at rd1936pre
  have rd1941pre := evm_run rd1936pre with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd1942 := rd1941pre.mstore 0
    (wordAt0Mem (relyUsrMaskedWord I) (relyAuthHashMem I))
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd1946pre := evm_run rd1942 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1947 := rd1946pre.mstore 0 (relyStoreHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd1950pre := evm_run rd1947 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd1951 := rd1950pre.keccak256 0 (mapSlot (relyUsrMaskedWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by decide +native) mem_cost hstoreSlot (by decide +native)
    (by evm_ov)
  obtain ⟨_, _, rd1952raw⟩ := rd1951.sstore hperm (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd226 := rd1952raw.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd227 := rd226.jumpdest (by decide +native) (by evm_ov)
  simpa [relyUsrStorageSlot_eq_mapSlot_masked I] using
    RD.stop rd227 (by decide +native) (by evm_ov)

theorem flopperX_deny_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hauth : relyAuthWord σ I = ⟨1⟩)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨678⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flopperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (relyUsrStorageSlot I) ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd1838⟩ := flopperDenyX_decoded (g := g) hsz36 hsize hreach
  obtain ⟨_, _, rd1927⟩ := flopperDenyX_authorized (I := I) hauth rd1838
  exact flopperDenyX_storeAuthorized hperm rd1927

theorem flopperX_deny_unauthorized {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨678⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1838⟩ := flopperDenyX_decoded (g := g) hsz36 hsize hreach
  exact flopperDenyX_unauthorized (I := I) hauth rd1838

theorem flopperDenyBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
        (transitionSignature denyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨678⟩ [sel]
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
        denyTransition.body
        (.returned { contract := contract, locals := relyStore I }
          (denyPostState evmSolm I) none) := by
    simpa [evmSolm, relyAuthWord, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperDenyBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (flopperX_deny_ok (g := Sat256.ofUInt256 g) hsz36 hsize hperm hauth hreach)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by simp [denyPostState, evmSolm, initState, storageStore_createdAccounts])
      (by
        simpa [denyPostState, evmSolm, initState, storageStore_accountMap] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (relyUsrStorageSlot I) ⟨0⟩
            hAccounts)
      (by
        simpa [denyTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by decide +native) (by decide +native)))

theorem flopperDenyBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
        (transitionSignature denyTransition).paramTypes I.calldata = some (relyStore I))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨678⟩ [sel]
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
        denyTransition.body .reverted := by
    simpa [evmSolm, relyAuthWord, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      flopperDenyBodyReverts evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
        hauthWord
  exact (flopperX_deny_unauthorized (g := Sat256.ofUInt256 g) hsz36 hsize hauth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperDenyBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨678⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (flopperDenyX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (flopperDecode_deny_none_short hsz4 hshort)

theorem flopperDenyBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flopperSelBytes 5))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flopperSelBytes 5) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some denyTransition :=
    flopperDispatchDeny hsel
  have hreach := flopperReachDenyBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · exact flopperDenyBodyCoreOk hcode hsize hperm hwv hsz36 hauth hdispatch
        (flopperDecode_deny_ok hsz36) hreach hAccounts
    · exact flopperDenyBodyCoreUnauthorized hcode hsize hwv hsz36 hauth hdispatch
        (flopperDecode_deny_ok hsz36) hreach hAccounts
  · exact flopperDenyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Flopper
