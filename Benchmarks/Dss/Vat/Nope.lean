import Benchmarks.Dss.Vat.Hope

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vat

/-! ## `nope(address)` -/

def nopePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (hopeStorageSlot I) ⟨0⟩

theorem vatDecode_nope_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (nopeTransition.params.map Param.name)
      (transitionSignature nopeTransition).paramTypes I.calldata = some (hopeStore I) := by
  simpa [config, nopeTransition, hopeStore, hopeUsrValue, hopeUsrWord, calldataWord] using
    decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36

theorem vatDecode_nope_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (nopeTransition.params.map Param.name)
      (transitionSignature nopeTransition).paramTypes I.calldata = none := by
  simpa [config, nopeTransition] using
    decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort

theorem nopeAssign (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := hopeStore I } evm
      .storage (canRef sender (.var "usr")) (.int 0) =
        .ok ({ contract := contract, locals := hopeStore I }, nopePostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (hopeStorageSlot I))
      (hbase := hopeStore_can I)
      (her := evalStorageRef_hope_can evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
        hopeSourceKey, hopeUsrKey, uint256St])
      (hloc := by rfl)
  simpa [nopePostState] using vatStorageLocStore_uint256 evm (hopeStorageSlot I) ⟨0⟩

theorem vatNopeBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source) :
    ExecTransitionBody config contract evm (hopeStore I) nopeTransition.body
      (.returned { contract := contract, locals := hopeStore I } (nopePostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [nopeTransition, nonpayable] using
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.assign (by simp [evalExpr?, pure]) (nopeAssign evm I hsrc)) <|
        ExecBlock.nil

theorem vatDispatchNope {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 20)) :
    dispatchMsg contract I.calldata = some nopeTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 20 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some nopeTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes, foldSelectorBytes,
    forkSelectorBytes, frobSelectorBytes, gemSelectorBytes, grabSelectorBytes,
    healSelectorBytes, hopeSelectorBytes, ilksSelectorBytes, initSelectorBytes,
    liveSelectorBytes, moveSelectorBytes, nopeSelectorBytes]
  native_decide

theorem vatReachNopeBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 20)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1467⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0xdc4d20fa⟩ :=
    vatSelWord_eq_of_beq I hsz 0xdc 0x4d 0x20 0xfa ⟨0xdc4d20fa⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhighhigh :
      UInt256.gt (armSelNat vatBytecode vatHighHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms65FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms65FirstPc 0))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms65Body 0 (by omega) ⟨1467⟩ hcode hwv hsz hsize
    hroot hhigh hhighhigh heq0 htake (by jump_dest) (by native_decide)

set_option maxHeartbeats 1000000 in
theorem vatNopeX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6131⟩
        [hopeUsrMaskedWord I, ⟨524⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨1467⟩) (ret := ⟨524⟩)
    (decoded := ⟨1489⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := vatBytecode) (decoded := ⟨1489⟩) (ret := ⟨524⟩) (routine := ⟨6131⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [hopeUsrMaskedWord, hopeUsrWord, calldataWord] using hroutine⟩

theorem vatNopeX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨1467⟩) (ret := ⟨524⟩)
    (decoded := ⟨1489⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem vatNopeX_storeOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD vatBytecode I g s0 ⟨6131⟩
      [hopeUsrMaskedWord I, ⟨524⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret vatBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (hopeStorageSlot I) ⟨0⟩)
      ByteArray.empty := by
  have hinnerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((hopeInnerMem I).readWithPadding 0 64))) =
        hopeInnerSlot I := by
    simpa [hopeInnerMem, hopeInnerSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨1⟩ : UInt256) (hopeSourceWord I)
        solcFreePtrMem_size
  have houterSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((hopeHashMem I).readWithPadding 0 64))) =
        mapSlot (hopeUsrMaskedWord I) (hopeInnerSlot I) := by
    simpa [hopeHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (hopeInnerSlot I) (hopeUsrMaskedWord I)
        (hopeInnerMem_size I)
  have rd6137pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6138 := rd6137pre.mstore 0 (wordAt0Mem (hopeSourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6144pre := evm_run rd6138 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6145 := rd6144pre.mstore 0 (hopeInnerMem I) (UInt256.ofNat 3)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6149pre := evm_run rd6145 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rd6150 := rd6149pre.keccak256 0 (hopeInnerSlot I) (UInt256.ofNat 3)
    (by native_decide) mem_cost hinnerSlot (by native_decide) (by evm_ov)
  have rd6163pre := evm_run rd6150 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (hopeUsrMaskedWord I)
        = hopeUsrMaskedWord I := by
    rw [u256_land_comm]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (hopeUsrMaskedWord_canonical I)
  rw [hmask] at rd6163pre
  have rd6164 := rd6163pre.mstore 0 (wordAt0Mem (hopeUsrMaskedWord I) (hopeInnerMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6166pre := evm_run rd6164 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd6167 := rd6166pre.mstore 0 (hopeHashMem I) (UInt256.ofNat 3)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6169pre := evm_run rd6167 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6170 := rd6169pre.keccak256 0
    (mapSlot (hopeUsrMaskedWord I) (hopeInnerSlot I)) (UInt256.ofNat 3)
    (by native_decide) mem_cost houterSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd6171raw⟩ := rd6170.sstore hperm (by native_decide) (by evm_ov)
  have rd524 := rd6171raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd525 := rd524.jumpdest (by native_decide) (by evm_ov)
  simpa [hopeStorageSlot_eq_innerSlot I] using RD.stop rd525 (by native_decide) (by evm_ov)

theorem vatNopeBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hdispatch : dispatchMsg contract I.calldata = some nopeTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (nopeTransition.params.map Param.name)
        (transitionSignature nopeTransition).paramTypes I.calldata = some (hopeStore I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evmSolm (hopeStore I)
        nopeTransition.body
        (.returned { contract := contract, locals := hopeStore I }
          (nopePostState evmSolm I) none) := by
    simpa [evmSolm] using
      vatNopeBodyReturns evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        (by simp [evmSolm, initState])
  obtain ⟨_, _, rd6131⟩ := vatNopeX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  exact (vatNopeX_storeOk (I := I) hperm rd6131)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by simp [nopePostState, evmSolm, initState, storageStore_createdAccounts])
      (by
        simpa [nopePostState, evmSolm, initState, storageStore_accountMap] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (hopeStorageSlot I) ⟨0⟩ hAccounts)
      (by
        simpa [nopeTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))

theorem vatNopeBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some nopeTransition)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (vatNopeX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (vatDecode_nope_none_short hsz4 hshort)

theorem vatNopeBodyCore : VatBodyTheorem 20 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 20) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some nopeTransition :=
    vatDispatchNope hsel
  have hreach := vatReachNopeBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact vatNopeBodyCoreOk hcode hsize hperm hwv hsz36 hdispatch
      (vatDecode_nope_ok hsz36) hreach hAccounts
  · exact vatNopeBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Vat
