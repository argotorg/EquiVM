import Benchmarks.Dss.Jug.DripEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

theorem jugDripBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some dripTransition)
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨328⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := jugBytecode) (sel := sel) (entry := ⟨328⟩) (ret := ⟨357⟩)
    (decoded := ⟨350⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (jugDecode_drip_none_short hsz4 hshort)

theorem jugDripBodyCoreInvalidNow
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (solcSlotWordAt (fileDutyRhoSlotFor I) σ I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dripTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
        (transitionSignature dripTransition).paramTypes I.calldata = some (dripLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨328⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let locals := dripLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
    simpa [evm0, locals] using
      (jugDripSourceBodyRhoReverts (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz36 hlt)
  obtain ⟨_, _, hdecoded⟩ := jugDripX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  exact (jugDripX_invalidNow (I := I) hsz36 hlt hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugDripBodyCoreVatIlksNoCode
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (solcSlotWordAt (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dripTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
        (transitionSignature dripTransition).paramTypes I.calldata = some (dripLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨328⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (dripVatTargetWord σ I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let locals := dripLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatNoCodeSolm :
      (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 :=
    dripVatCode_zero_of_codeSize_zero (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSize
  have hbody :
      ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
    simpa [evm0, locals] using
      (jugDripSourceBodyVatIlksNoCode (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz36 hle hvatNoCodeSolm)
  obtain ⟨_, _, hdecoded⟩ := jugDripX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  obtain ⟨_, _, hnowOk⟩ := jugDripX_nowOk (I := I) hsz36 hle hdecoded
  exact (RD.jugDripVatIlksNoCode hnowOk hcodeSize)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugDripBodyCoreVatIlksCallFailed
    {σ σ' σ₀ A I} {g : UInt256} {sel : UInt256}
    {out : ByteArray} {Ain : Substate} {gasWord : UInt256} {k C : ℕ}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (solcSlotWordAt (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dripTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
        (transitionSignature dripTransition).paramTypes I.calldata = some (dripLocals I))
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (dripVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd1400 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1400⟩
      (⟨0⟩ :: dripVatIlksEndPtr :: dripVatIlksSelectorWord ::
        dripVatTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ ::
        sel :: [])
      (dripVatIlksPostCallMem I out) (UInt256.ofNat 6) out σ' k C)
    (hΘ :
      ∃ (g'' : UInt256) (A' : Substate),
        (σ', g'', A', false, out) = Ethereum.EVM.Θ σ σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (dripVatTargetWord σ I))
          (toExecute σ (AccountAddress.ofUInt256 (dripVatTargetWord σ I)))
          gasWord (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (I.depth + 1) I.header I.blobVersionedHashes I.blocks I.perm)
    (hout : out.size < UInt256.size) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let locals := dripLocals I
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeSolm :
      0 <
        (UInt256.ofNat
          (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat :=
    dripVatCode_pos_of_codeSize_ne_zero
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSize
  rcases hΘ with ⟨g'', A', hΘ⟩
  have hdepthNe : evm.executionEnv.depth ≠ 1024 := by
    intro hbad
    simp [evm, initState] at hbad
    rw [hbad] at hdepth
    omega
  have htgtAddr :
      dripVatAddress σ I = AccountAddress.ofUInt256 (dripVatTargetWord σ I) :=
    dripVatAddress_eq_target σ I
  have htgt :
      EVM.address (dripVatAddress σ I) =
        AccountAddress.ofUInt256 (dripVatTargetWord σ I) := by
    rw [htgtAddr]
    exact address_of_val _
  have hΘE :
      (σ', g'', A', false, out) =
        Ethereum.EVM.Θ evm.accountMap evm.σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat evm.executionEnv.codeOwner))
          evm.executionEnv.sender (AccountAddress.ofUInt256 (dripVatTargetWord σ I))
          (toExecute evm.accountMap (AccountAddress.ofUInt256 (dripVatTargetWord σ I)))
          gasWord (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks (true && evm.executionEnv.perm) := by
    simpa [evm, initState] using hΘ
  have hcall :
      typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
        (false, { evm with accountMap := σ', substate := A' }, out) true :=
    callCoincides hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
  have hbody :
      ExecTransitionBody config contract evm locals dripTransition.body .reverted := by
    simpa [evm, locals] using
      (jugDripSourceBodyVatIlksCallFailed
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmVat := { evm with accountMap := σ', substate := A' })
        (out := out) hwv hsz36 hle hvatCodeSolm (by simpa [evm] using hcall))
  have hrev := RD.jugDripVatIlksCallFailed rd1400 hout
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugDripBodyCoreVatIlksCallDepthLimit
    {σ σ₀ A I} {g : UInt256} {sel : UInt256} {k C : ℕ}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (solcSlotWordAt (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dripTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
        (transitionSignature dripTransition).paramTypes I.calldata = some (dripLocals I))
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (dripVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (rd1400 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1400⟩
      (⟨0⟩ :: dripVatIlksEndPtr :: dripVatIlksSelectorWord ::
        dripVatTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ ::
        sel :: [])
      (dripVatIlksCalldataMem I (dripIlkHashMem I)) (UInt256.ofNat 6)
      ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let locals := dripLocals I
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeSolm :
      0 <
        (UInt256.ofNat
          (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat :=
    dripVatCode_pos_of_codeSize_ne_zero
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSize
  let A_vat := (evm.addAccessedAccount (EVM.address (dripVatAddress σ I))).substate
  have hdepthInit : evm.executionEnv.depth = 1024 := by
    simpa [evm, initState] using hdepth
  have hcallSolm :
      typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
        (false, { evm with substate := A_vat }, ByteArray.empty) true := by
    simpa [A_vat] using
      (callNotMade_depthLimit (cfg := config) (evm := evm)
        (tgt := EVM.address (dripVatAddress σ I)) (name := "ilks")
        (args := [.fixedBytes bytes32Width (fileDutyIlkBytes I)])
        (callPerm := true)
        (calldata :=
          (dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
        (dripVatIlksEncode_eq I hsz36) hdepthInit)
  have hbody :
      ExecTransitionBody config contract evm locals dripTransition.body .reverted := by
    simpa [evm, locals] using
      (jugDripSourceBodyVatIlksCallFailed
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmVat := { evm with substate := A_vat }) (out := ByteArray.empty)
        hwv hsz36 hle hvatCodeSolm (by simpa [evm] using hcallSolm))
  have hrev := RD.jugDripVatIlksCallFailed rd1400 (by native_decide)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugDripBodyCoreVatIlksReturnDecodeShort
    {σ σ' σ₀ A I} {g : UInt256} {sel : UInt256}
    {out : ByteArray} {Ain : Substate} {gasWord : UInt256} {k C : ℕ}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (solcSlotWordAt (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dripTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
        (transitionSignature dripTransition).paramTypes I.calldata = some (dripLocals I))
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (dripVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd1400 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1400⟩
      (⟨1⟩ :: dripVatIlksEndPtr :: dripVatIlksSelectorWord ::
        dripVatTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ ::
        sel :: [])
      (dripVatIlksPostCallMem I out) (UInt256.ofNat 6) out σ' k C)
    (hΘ :
      ∃ (g'' : UInt256) (A' : Substate),
        (σ', g'', A', true, out) = Ethereum.EVM.Θ σ σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (dripVatTargetWord σ I))
          (toExecute σ (AccountAddress.ofUInt256 (dripVatTargetWord σ I)))
          gasWord (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (I.depth + 1) I.header I.blobVersionedHashes I.blocks I.perm)
    (hshort : out.size < 64)
    (hout : out.size < UInt256.size) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let locals := dripLocals I
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeSolm :
      0 <
        (UInt256.ofNat
          (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat :=
    dripVatCode_pos_of_codeSize_ne_zero
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSize
  rcases hΘ with ⟨g'', A', hΘ⟩
  have hdepthNe : evm.executionEnv.depth ≠ 1024 := by
    intro hbad
    simp [evm, initState] at hbad
    rw [hbad] at hdepth
    omega
  have htgtAddr :
      dripVatAddress σ I = AccountAddress.ofUInt256 (dripVatTargetWord σ I) :=
    dripVatAddress_eq_target σ I
  have htgt :
      EVM.address (dripVatAddress σ I) =
        AccountAddress.ofUInt256 (dripVatTargetWord σ I) := by
    rw [htgtAddr]
    exact address_of_val _
  have hΘE :
      (σ', g'', A', true, out) =
        Ethereum.EVM.Θ evm.accountMap evm.σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat evm.executionEnv.codeOwner))
          evm.executionEnv.sender (AccountAddress.ofUInt256 (dripVatTargetWord σ I))
          (toExecute evm.accountMap (AccountAddress.ofUInt256 (dripVatTargetWord σ I)))
          gasWord (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks (true && evm.executionEnv.perm) := by
    simpa [evm, initState] using hΘ
  have hcall :
      typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
        (true, { evm with accountMap := σ', substate := A' }, out) true :=
    callCoincides hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
  have hbody :
      ExecTransitionBody config contract evm locals dripTransition.body .reverted := by
    simpa [evm, locals] using
      (jugDripSourceBodyVatIlksReturnDecodeReverts
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmVat := { evm with accountMap := σ', substate := A' })
        (out := out) hwv hsz36 hle hvatCodeSolm (by simpa [evm] using hcall)
        (dripVatIlksDecode_none_short hshort))
  obtain ⟨_, _, rd1418⟩ := RD.jugDripVatIlksCallSucceeded rd1400
  have hrev := RD.jugDripVatIlksReturnDecodeShortReverts rd1418 hshort hout
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugDripBodyCoreVatIlksAddOverflow
    {σ σ' σ₀ A I} {g sel : UInt256}
    {out mem : ByteArray} {Ain : Substate} {callGas : UInt256} {k C : ℕ}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (solcSlotWordAt (fileDutyRhoSlotFor I) σ I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dripTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
        (transitionSignature dripTransition).paramTypes I.calldata = some (dripLocals I))
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (dripVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd2131 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2131⟩
      (solcSlotWordAt (fileDutyDutySlotFor I) σ' I :: solcSlotWordAt ⟨4⟩ σ' I ::
        ⟨1485⟩ :: ⟨1524⟩ :: ⟨1530⟩ :: dripVatIlksPrevWord out :: ⟨0⟩ ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out σ' k C)
    (hΘ :
      ∃ (g'' : UInt256) (A' : Substate),
        (σ', g'', A', true, out) = Ethereum.EVM.Θ σ σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (dripVatTargetWord σ I))
          (toExecute σ (AccountAddress.ofUInt256 (dripVatTargetWord σ I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (I.depth + 1) I.header I.blobVersionedHashes I.blocks I.perm)
    (hdec :
      config.externalABI.decode? "ilks" out =
        some [.int (Int.ofNat (dripVatIlksArtWord out).toNat),
          .int (Int.ofNat (dripVatIlksPrevWord out).toNat)])
    (haddOverflow :
      UInt256.size ≤ (solcSlotWordAt ⟨4⟩ σ' I).toNat +
        (solcSlotWordAt (fileDutyDutySlotFor I) σ' I).toNat) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let locals := dripLocals I
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hvatCodeSolm :
      0 <
        (UInt256.ofNat
          (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat :=
    dripVatCode_pos_of_codeSize_ne_zero
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSize
  rcases hΘ with ⟨g'', A', hΘ⟩
  have hΘE :
      (σ', g'', A', true, out) =
        Ethereum.EVM.Θ evm.accountMap evm.σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat evm.executionEnv.codeOwner))
          evm.executionEnv.sender (AccountAddress.ofUInt256 (dripVatTargetWord σ I))
          (toExecute evm.accountMap (AccountAddress.ofUInt256 (dripVatTargetWord σ I)))
          callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (evm.executionEnv.depth + 1) evm.executionEnv.header evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks (true && evm.executionEnv.perm) := by
    simpa [evm, initState] using hΘ
  have htgt :
      EVM.address (dripVatAddress σ I) =
        AccountAddress.ofUInt256 (dripVatTargetWord σ I) := by
    rw [dripVatAddress_eq_target σ I]
    exact address_of_val _
  have hcall :
      typedCallViaEVM config evm (EVM.address (dripVatAddress σ I)) "ilks" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
        (true, { evm with accountMap := σ', substate := A' }, out) true :=
    callCoincides
      (initStateDepth_ne_1024_of_lt
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hdepth)
      htgt (dripVatIlksEncode_eq I hsz36) hΘE
  have hbody :
      ExecTransitionBody config contract evm locals dripTransition.body .reverted := by
    simpa [evm, locals, initState, solcSlotWordAt] using
      (jugDripSourceBodyVatIlksAddOverflowReverts
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmVat := { evm with accountMap := σ', substate := A' })
        (out := out) hwv hsz36 hle hvatCodeSolm
        (by simpa [evm] using hcall) hdec
        (by simpa [evm, initState, solcSlotWordAt] using haddOverflow))
  have hrev := RD.jugDripAddOverflowReverts haddOverflow rd2131
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Jug
