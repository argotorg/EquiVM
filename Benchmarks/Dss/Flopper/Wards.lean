import Benchmarks.Dss.Flopper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper

/-! ## `wards(address)` mapping getter -/

def wardsMappingArg (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

def wardsMappingKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

def wardsMappingEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address (wardsMappingArg I))] }

def wardsMappingSlotFor (I : ExecutionEnv) : UInt256 :=
  wardsSlot (.address (wardsMappingArg I))

theorem wardsMappingSlotFor_eq (I : ExecutionEnv) :
    wardsMappingSlotFor I = solcMappingSlot ⟨0⟩ (wardsMappingKey I) := by
  unfold wardsMappingSlotFor wardsMappingArg wardsMappingKey wardsSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem flopperDecode_wards_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.address (wardsMappingArg I))) := by
  simpa [config, wardsTransition, wardsMappingArg] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem flopperDecode_wards_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata = none := by
  simpa [config, wardsTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem flopperReachWardsBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flopperSelBytes 18)) :
    ∃ k C, RD flopperBytecode I g (initState σ σ₀ g A I)
        ⟨766⟩ [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : flopperSelWord I = ⟨0xbf353dbb⟩ := by
    simpa [flopperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0xbf 0x35 0x3d 0xbb ⟨0xbf353dbb⟩
        (by native_decide) (by simpa [flopperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flopperBytecode flopperHighSplitPc)
      (flopperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flopperReachHighHighFirstArm (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have heq0 : ∀ j, j < 0 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighHighFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighHighFirstArmPc 0))
        (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨766⟩ 0 hfirst
    (fun j hj => flopperHighHighArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

set_option maxHeartbeats 0 in
private theorem wardsReturnWordWf :
    solcReturnWordFromMemWf flopperBytecode ⟨644⟩ := by
  unfold solcReturnWordFromMemWf
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 0 in
private theorem wardsMappingGetterWf :
    solcZeroSlotMappingGetterWf flopperBytecode ⟨3874⟩ := by
  unfold solcZeroSlotMappingGetterWf
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
private theorem wardsReachDecoded
    {σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨766⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨788⟩
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨644⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  exact RD.solcOneAddressExternalLenOk
    (code := flopperBytecode) (sel := sel) (entry := ⟨766⟩) (ret := ⟨644⟩)
    (decoded := ⟨788⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize

set_option maxHeartbeats 1000000 in
private theorem wardsReachRoutine
    {σ σ₀ A I} {g sel : UInt256}
    (hdecoded : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨788⟩
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨644⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3874⟩
      (UInt256.land solcAddrMask (calldataWord I.calldata 4) :: ⟨644⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, hdecoded⟩ := hdecoded
  exact RD.solcOneAddressExternalMaskAndJumpMasked
    (code := flopperBytecode) (decoded := ⟨788⟩) (ret := ⟨644⟩) (routine := ⟨3874⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)

set_option maxHeartbeats 0 in
private theorem wardsReturnFromMapping
    {σ σ₀ A I} {g sel key : UInt256} {k C : ℕ}
    (hretPc : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨644⟩
      (solcSlotWord σ I (solcMappingSlot ⟨0⟩ key) :: ⟨644⟩ :: [sel])
      (solcMappingHashMem ⟨0⟩ key) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret flopperBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
      (UInt256.toByteArray (solcSlotWord σ I (solcMappingSlot ⟨0⟩ key))) := by
  have hret' := RD.solcReturnWordFromMem
    (pc := ⟨644⟩) (val := solcSlotWord σ I (solcMappingSlot ⟨0⟩ key))
    (ret := ⟨644⟩) (R := [sel])
    (memout := solcScratchReturnMem (solcMappingHashMem ⟨0⟩ key)
      (solcSlotWord σ I (solcMappingSlot ⟨0⟩ key)))
    (by simpa [flopperSlotWord] using hretPc)
    wardsReturnWordWf
    (by simpa using solcMappingHashMem_mload64 ⟨0⟩ key)
    (by rfl)
    (by exact (solcScratchReturnMem_mload64
      (solcSlotWord σ I (solcMappingSlot ⟨0⟩ key))
      (solcMappingHashMem_size ⟨0⟩ key) (solcMappingHashMem_read64 ⟨0⟩ key)))
    (by exact (solcScratchReturnMem_read128
      (solcSlotWord σ I (solcMappingSlot ⟨0⟩ key)) (solcMappingHashMem_size ⟨0⟩ key)))
    (by simp)
  simpa [flopperSlotWord] using hret'

set_option maxHeartbeats 2000000 in
theorem flopperWardsBodyCoreOk
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some wardsTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (wardsTransition.params.map Param.name)
        (transitionSignature wardsTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (.address (wardsMappingArg I))))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨766⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let key := wardsMappingKey I
  let slot := solcMappingSlot ⟨0⟩ key
  let locals : Store := (∅ : Store).insert "arg0" (.address (wardsMappingArg I))
  have hlocal : locals.get? "arg0" = some (.address (wardsMappingArg I)) := by
    simp [locals]
  have hslot : wardsMappingSlotFor I = slot := by
    simpa only [slot, key] using wardsMappingSlotFor_eq I
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) locals wardsTransition.body
        (.returned { contract := contract, locals := locals }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int
            (Int.ofNat (flopperSlotWord (wardsMappingSlotFor I) σ I).toNat))])) := by
    simpa [wardsTransition, flopperSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, locals] using
      flopperUint256GetterBodyReturns
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) locals
        (ref := wardsRef (.var "arg0")) (er := wardsMappingEvaledRef I)
        (slot := wardsMappingSlotFor I)
        (by simp only [initState]; exact hwv) (by simp [locals, wardsRef])
        (by
          simp only [wardsMappingEvaledRef, evalStorageRef, evalStorageRefSteps,
            evalStorageRefStep, wardsRef, evalExpr?, valueToKey?, EvalResult.ofOption,
            EvalResult.bind, pure, bind, hlocal])
        (by simp [wardsMappingEvaledRef, storageTypeAt?, storageTypeStep?, contract,
          storageDecls, uint256St])
        (by rfl)
  have hdecoded := wardsReachDecoded hreach hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := wardsReachRoutine hdecoded
  obtain ⟨_, _, hretPc⟩ := RD.solcZeroSlotMappingGetter
    (code := flopperBytecode) (pc := ⟨3874⟩) (key := key) (ret := ⟨644⟩)
    (R := [sel])
    (by exact hroutine)
    wardsMappingGetterWf
    (by jump_dest) (by simp)
  have hret := wardsReturnFromMapping (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (sel := sel) (key := key) hretPc
  have henc :
      returnEquiv (UInt256.toByteArray (flopperSlotWord slot σ I))
        (some [(.int (Int.ofNat (flopperSlotWord slot σ I).toNat))])
        wardsTransition.returnType := by
    rw [show wardsTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (flopperSlotWord slot σ I))
  exact hret.reEquivExecution hcode hdispatch hdecode hbody henc

theorem flopperWardsBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some wardsTransition)
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨766⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := flopperBytecode) (sel := sel) (entry := ⟨766⟩) (ret := ⟨644⟩)
    (decoded := ⟨788⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (flopperDecode_wards_none_short hsz4 hshort)

theorem flopperWardsBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flopperSelBytes 18)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flopperSelBytes 18) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some wardsTransition :=
    flopperDispatchWards hsel
  have hreach := flopperReachWardsBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact flopperWardsBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (flopperDecode_wards_ok hsz36) hreach
  · exact flopperWardsBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Flopper
