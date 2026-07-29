import Benchmarks.Dss.Jug.DripEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

theorem jugDripBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some dripTransition)
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨328⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
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
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlt :
      (UInt256.ofNat I.header.timestamp).toNat <
        (jugSlotWord (fileDutyRhoSlotFor I) σ_evm I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dripTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
        (transitionSignature dripTransition).paramTypes I.calldata = some (dripLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨328⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := dripLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ_evm I =
      jugSlotWord (fileDutyRhoSlotFor I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (fileDutyRhoSlotFor I) ⟨0⟩
  have hltSolm :
      (UInt256.ofNat I.header.timestamp).toNat <
        (jugSlotWord (fileDutyRhoSlotFor I) σ_solm I).toNat := by
    rw [← hrhoWord]
    exact hlt
  have hbody :
      ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
    simpa [evm0, locals] using
      (jugDripSourceBodyRhoReverts (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz36 hltSolm)
  obtain ⟨_, _, hdecoded⟩ := jugDripX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  exact (jugDripX_invalidNow (I := I) hsz36 hlt hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugDripBodyCoreVatIlksNoCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) σ_evm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dripTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
        (transitionSignature dripTransition).paramTypes I.calldata = some (dripLocals I))
    (hreach : ∃ k C, RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨328⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm (dripVatTargetWord σ_evm I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := dripLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ_evm I =
      jugSlotWord (fileDutyRhoSlotFor I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (fileDutyRhoSlotFor I) ⟨0⟩
  have hleSolm :
      (jugSlotWord (fileDutyRhoSlotFor I) σ_solm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat := by
    rw [← hrhoWord]
    exact hle
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (dripVatTargetWord σ_solm I) = ⟨0⟩ :=
    dripVatCodeSize_zero_accountMapEquiv hAccounts hcodeSize
  have hvatNoCodeSolm :
      (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (dripVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat = 0 :=
    dripVatCode_zero_of_codeSize_zero (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSizeSolm
  have hbody :
      ExecTransitionBody config contract evm0 locals dripTransition.body .reverted := by
    simpa [evm0, locals] using
      (jugDripSourceBodyVatIlksNoCode (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz36 hleSolm hvatNoCodeSolm)
  obtain ⟨_, _, hdecoded⟩ := jugDripX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  obtain ⟨_, _, hnowOk⟩ := jugDripX_nowOk (I := I) hsz36 hle hdecoded
  exact (RD.jugDripVatIlksNoCode hnowOk hcodeSize)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugDripBodyCoreVatIlksCallFailed
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A I} {g : UInt256} {sel : UInt256}
    {out : ByteArray} {Ain : Substate} {gasWord : UInt256} {k C : ℕ}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) σ_evm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dripTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
        (transitionSignature dripTransition).paramTypes I.calldata = some (dripLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm (dripVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd1400 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1400⟩
      (⟨0⟩ :: dripVatIlksEndPtr :: dripVatIlksSelectorWord ::
        dripVatTargetWord σ_evm I :: ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ ::
        sel :: [])
      (dripVatIlksPostCallMem I out) (UInt256.ofNat 6) out (cA', σ') k C)
    (hΘ :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', false, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          σ_evm σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I))
          (toExecute σ_evm (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (I.depth + 1) I.header I.perm)
    (hout : out.size < UInt256.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := dripLocals I
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ_evm I =
      jugSlotWord (fileDutyRhoSlotFor I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (fileDutyRhoSlotFor I) ⟨0⟩
  have hleSolm :
      (jugSlotWord (fileDutyRhoSlotFor I) σ_solm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat := by
    rw [← hrhoWord]
    exact hle
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (dripVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
    dripVatCodeSize_ne_zero_accountMapEquiv hAccounts hcodeSize
  have hvatCodeSolm :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat :=
    dripVatCode_pos_of_codeSize_ne_zero (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSizeSolm
  rcases hΘ with ⟨g'', A', hΘ⟩
  have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
    intro hbad
    simp [evmE, initState] at hbad
    rw [hbad] at hdepth
    omega
  have htgtAddr :
      dripVatAddress σ_solm I = AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I) := by
    rw [← dripVatAddress_accountMapEquiv hAccounts]
    exact dripVatAddress_eq_target σ_evm I
  have htgt :
      EVM.address (dripVatAddress σ_solm I) =
        AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I) := by
    rw [htgtAddr]
    exact evmAddress_accountAddress _
  have hΘE :
      (cA', σ', g'', A', false, out) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes evmE.createdAccounts
          evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I))
          (toExecute evmE.accountMap (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header true := by
    simpa [evmE, initState, hperm] using hΘ
  obtain ⟨σ'_solm, A'_solm, hcallSolm, _hAccounts'⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
      (tgt := EVM.address (dripVatAddress σ_solm I))
      (targetWord := dripVatTargetWord σ_evm I)
      (name := "ilks") (args := [.fixedBytes bytes32Width (fileDutyIlkBytes I)])
      (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain) (z := false)
      (out := out) (g'' := g'') (callGas := gasWord)
      (mem := dripVatIlksCalldataMem I (dripIlkHashMem I))
      (inOff := dripVatIlksOutPtr) (inSize := dripVatIlksInSize) (callPerm := true)
      hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
      (by simpa [evmE, evmS, initState] using hAccounts)
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
  have hbody :
      ExecTransitionBody config contract evmS locals dripTransition.body .reverted := by
    simpa [evmS, locals] using
      (jugDripSourceBodyVatIlksCallFailed (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmVat := { evmS with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' })
        (out := out) hwv hsz36 hleSolm hvatCodeSolm (by simpa [evmS] using hcallSolm))
  have hrev := RD.jugDripVatIlksCallFailed rd1400 hout
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugDripBodyCoreVatIlksCallDepthLimit
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256} {k C : ℕ}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) σ_evm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dripTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
        (transitionSignature dripTransition).paramTypes I.calldata = some (dripLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm (dripVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (rd1400 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1400⟩
      (⟨0⟩ :: dripVatIlksEndPtr :: dripVatIlksSelectorWord ::
        dripVatTargetWord σ_evm I :: ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ ::
        sel :: [])
      (dripVatIlksCalldataMem I (dripIlkHashMem I)) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := dripLocals I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ_evm I =
      jugSlotWord (fileDutyRhoSlotFor I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (fileDutyRhoSlotFor I) ⟨0⟩
  have hleSolm :
      (jugSlotWord (fileDutyRhoSlotFor I) σ_solm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat := by
    rw [← hrhoWord]
    exact hle
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (dripVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
    dripVatCodeSize_ne_zero_accountMapEquiv hAccounts hcodeSize
  have hvatCodeSolm :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat :=
    dripVatCode_pos_of_codeSize_ne_zero (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSizeSolm
  let A_vat := (evmS.addAccessedAccount (EVM.address (dripVatAddress σ_solm I))).substate
  have hdepthInit : evmS.executionEnv.depth = 1024 := by
    simpa [evmS, initState] using hdepth
  have hcallSolm :
      typedCallViaEVM config evmS (EVM.address (dripVatAddress σ_solm I)) "ilks" 0
        [.fixedBytes bytes32Width (fileDutyIlkBytes I)]
        (false, { evmS with substate := A_vat }, ByteArray.empty) true := by
    simpa [A_vat] using
      (callNotMade_depthLimit (cfg := config) (evm := evmS)
        (tgt := EVM.address (dripVatAddress σ_solm I)) (name := "ilks")
        (args := [.fixedBytes bytes32Width (fileDutyIlkBytes I)])
        (callPerm := true)
        (calldata :=
          (dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
        (dripVatIlksEncode_eq I hsz36) hdepthInit)
  have hbody :
      ExecTransitionBody config contract evmS locals dripTransition.body .reverted := by
    simpa [evmS, locals] using
      (jugDripSourceBodyVatIlksCallFailed (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmVat := { evmS with substate := A_vat }) (out := ByteArray.empty)
        hwv hsz36 hleSolm hvatCodeSolm (by simpa [evmS] using hcallSolm))
  have hrev := RD.jugDripVatIlksCallFailed rd1400 (by native_decide)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugDripBodyCoreVatIlksReturnDecodeShort
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A I} {g : UInt256} {sel : UInt256}
    {out : ByteArray} {Ain : Substate} {gasWord : UInt256} {k C : ℕ}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) σ_evm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dripTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
        (transitionSignature dripTransition).paramTypes I.calldata = some (dripLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm (dripVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd1400 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1400⟩
      (⟨1⟩ :: dripVatIlksEndPtr :: dripVatIlksSelectorWord ::
        dripVatTargetWord σ_evm I :: ⟨0⟩ :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ ::
        sel :: [])
      (dripVatIlksPostCallMem I out) (UInt256.ofNat 6) out (cA', σ') k C)
    (hΘ :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', true, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          σ_evm σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I))
          (toExecute σ_evm (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (I.depth + 1) I.header I.perm)
    (hshort : out.size < 64)
    (hout : out.size < UInt256.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := dripLocals I
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ_evm I =
      jugSlotWord (fileDutyRhoSlotFor I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (fileDutyRhoSlotFor I) ⟨0⟩
  have hleSolm :
      (jugSlotWord (fileDutyRhoSlotFor I) σ_solm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat := by
    rw [← hrhoWord]
    exact hle
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (dripVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
    dripVatCodeSize_ne_zero_accountMapEquiv hAccounts hcodeSize
  have hvatCodeSolm :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat :=
    dripVatCode_pos_of_codeSize_ne_zero (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSizeSolm
  rcases hΘ with ⟨g'', A', hΘ⟩
  have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
    intro hbad
    simp [evmE, initState] at hbad
    rw [hbad] at hdepth
    omega
  have htgtAddr :
      dripVatAddress σ_solm I = AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I) := by
    rw [← dripVatAddress_accountMapEquiv hAccounts]
    exact dripVatAddress_eq_target σ_evm I
  have htgt :
      EVM.address (dripVatAddress σ_solm I) =
        AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I) := by
    rw [htgtAddr]
    exact evmAddress_accountAddress _
  have hΘE :
      (cA', σ', g'', A', true, out) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes evmE.createdAccounts
          evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I))
          (toExecute evmE.accountMap (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header true := by
    simpa [evmE, initState, hperm] using hΘ
  obtain ⟨σ'_solm, A'_solm, hcallSolm, _hAccounts'⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
      (tgt := EVM.address (dripVatAddress σ_solm I))
      (targetWord := dripVatTargetWord σ_evm I)
      (name := "ilks") (args := [.fixedBytes bytes32Width (fileDutyIlkBytes I)])
      (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain) (z := true)
      (out := out) (g'' := g'') (callGas := gasWord)
      (mem := dripVatIlksCalldataMem I (dripIlkHashMem I))
      (inOff := dripVatIlksOutPtr) (inSize := dripVatIlksInSize) (callPerm := true)
      hdepthNe htgt (dripVatIlksEncode_eq I hsz36) hΘE
      (by simpa [evmE, evmS, initState] using hAccounts)
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
  have hbody :
      ExecTransitionBody config contract evmS locals dripTransition.body .reverted := by
    simpa [evmS, locals] using
      (jugDripSourceBodyVatIlksReturnDecodeReverts (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmVat := { evmS with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' })
        (out := out) hwv hsz36 hleSolm hvatCodeSolm (by simpa [evmS] using hcallSolm)
        (dripVatIlksDecode_none_short hshort))
  obtain ⟨_, _, rd1418⟩ := RD.jugDripVatIlksCallSucceeded rd1400
  have hrev := RD.jugDripVatIlksReturnDecodeShortReverts rd1418 hshort hout
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem jugDripBodyCoreVatIlksAddOverflow
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A I} {g sel : UInt256}
    {out mem : ByteArray} {Ain : Substate} {callGas : UInt256} {k C : ℕ}
    (hcode : I.code = jugBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) σ_evm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some dripTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
        (transitionSignature dripTransition).paramTypes I.calldata = some (dripLocals I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm (dripVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd2131 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2131⟩
      (jugSlotWord (fileDutyDutySlotFor I) σ' I :: jugSlotWord ⟨4⟩ σ' I ::
        ⟨1485⟩ :: ⟨1524⟩ :: ⟨1530⟩ :: dripVatIlksPrevWord out :: ⟨0⟩ ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k C)
    (hΘ :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', true, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          σ_evm σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I))
          (toExecute σ_evm (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (I.depth + 1) I.header I.perm)
    (hdec :
      config.externalABI.decode? "ilks" out =
        some [.int (Int.ofNat (dripVatIlksArtWord out).toNat),
          .int (Int.ofNat (dripVatIlksPrevWord out).toNat)])
    (haddOverflow :
      UInt256.size ≤ (jugSlotWord ⟨4⟩ σ' I).toNat +
        (jugSlotWord (fileDutyDutySlotFor I) σ' I).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := dripLocals I
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrhoWord : jugSlotWord (fileDutyRhoSlotFor I) σ_evm I =
      jugSlotWord (fileDutyRhoSlotFor I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (fileDutyRhoSlotFor I) ⟨0⟩
  have hleSolm :
      (jugSlotWord (fileDutyRhoSlotFor I) σ_solm I).toNat ≤
        (UInt256.ofNat I.header.timestamp).toNat := by
    rw [← hrhoWord]
    exact hle
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (dripVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
    dripVatCodeSize_ne_zero_accountMapEquiv hAccounts hcodeSize
  have hvatCodeSolm :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (dripVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat :=
    dripVatCode_pos_of_codeSize_ne_zero (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcodeSizeSolm
  rcases hΘ with ⟨g'', A', hΘ⟩
  have hΘE :
      (cA', σ', g'', A', true, out) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes evmE.createdAccounts
          evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I))
          (toExecute evmE.accountMap (AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I)))
          callGas (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
            dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header true := by
    simpa [evmE, initState, hperm] using hΘ
  obtain ⟨σ'_solm, A'_solm, hcallSolm, hAccounts'⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
      (tgt := EVM.address (dripVatAddress σ_solm I))
      (targetWord := dripVatTargetWord σ_evm I)
      (name := "ilks") (args := [.fixedBytes bytes32Width (fileDutyIlkBytes I)])
      (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain) (z := true)
      (out := out) (g'' := g'') (callGas := callGas)
      (mem := dripVatIlksCalldataMem I (dripIlkHashMem I))
      (inOff := dripVatIlksOutPtr) (inSize := dripVatIlksInSize) (callPerm := true)
      (jugInitStateDepth_ne_1024_of_lt (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hdepth)
      (dripVatEvmAddress_eq_target_of_accountMapEquiv hAccounts)
      (dripVatIlksEncode_eq I hsz36) hΘE
      (by simpa [evmE, evmS, initState] using hAccounts)
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
      (by simp [evmE, evmS, initState])
  have hbaseWord : jugSlotWord ⟨4⟩ σ' I =
      jugSlotWord ⟨4⟩ σ'_solm I :=
    accountMapEquiv_storage_findD hAccounts' I.codeOwner ⟨4⟩ ⟨0⟩
  have hdutyWord : jugSlotWord (fileDutyDutySlotFor I) σ' I =
      jugSlotWord (fileDutyDutySlotFor I) σ'_solm I :=
    accountMapEquiv_storage_findD hAccounts' I.codeOwner (fileDutyDutySlotFor I) ⟨0⟩
  have haddOverflowSolm :
      UInt256.size ≤ (jugSlotWord ⟨4⟩ σ'_solm I).toNat +
        (jugSlotWord (fileDutyDutySlotFor I) σ'_solm I).toNat := by
    rw [← hbaseWord, ← hdutyWord]
    exact haddOverflow
  have hbody :
      ExecTransitionBody config contract evmS locals dripTransition.body .reverted := by
    simpa [evmS, locals, initState, jugSlotWord] using
      (jugDripSourceBodyVatIlksAddOverflowReverts (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmVat :=
          { evmS with
            accountMap := σ'_solm
            substate := A'_solm
            createdAccounts := cA' })
        (out := out) hwv hsz36 hleSolm hvatCodeSolm
        (by simpa [evmS] using hcallSolm) hdec
        (by simpa [evmS, initState, jugSlotWord] using haddOverflowSolm))
  have hrev := RD.jugDripAddOverflowReverts haddOverflow rd2131
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Jug
