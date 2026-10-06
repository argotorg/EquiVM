import Examples.UniswapV2Pair.PermitCoupling
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace UniswapV2Pair

theorem uniswapPermitBodyCoreOk_afterNonce
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {σ' : AccountMap}
    {o : ByteArray} {evmCallS : EVM.State}
    (hcode : I.code = uniswapV2PairBytecode)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hstruct :
      evalExpr? config
        { contract := contract,
          locals := permitAfterNonceLoadStore
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) I }
        (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
        permitStructHashExpr = .ok (permitStructHashValue σ I))
    (hdigest :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) I
            (permitStructHashValue σ I) }
        (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
        permitDigestExpr = .ok (permitDigestValue σ I))
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) ::
        permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o σ' k C)
    (hcall : typedCallViaEVM config
      (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
      (AccountAddress.ofNat 1) "ecrecover" 0
      [permitDigestValue σ I, permitVValue I, permitRValue I, permitSValue I]
      (true, evmCallS, o) false)
    (hAccountsCall : Eq σ' evmCallS.accountMap)
    (henvCall : evmCallS.executionEnv = I)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hnz :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask ≠
        ⟨0⟩)
    (hmatch :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask =
        permitOwnerMaskedWord I) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  let recoveredValue : Value :=
    .address (AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32)))
  have hdec : config.externalABI.decode? "ecrecover" o = some [recoveredValue] := by
    simpa [recoveredValue] using uniswapEcrecoverDecode_ok (returndata := o) ho32
  have hnzSource : recoveredValue ≠ .address (AccountAddress.ofNat 0) := by
    simpa [recoveredValue] using permitRecoveredAddress_ne_zero_of_mask_ne_zero ho32 hnz
  have hmatchSource : recoveredValue = permitOwnerValue I := by
    simpa [recoveredValue] using permitRecoveredAddress_eq_owner_of_mask_eq ho32 hmatch
  have hrest :
      ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore evmS I }
        evmNonceS permitAfterNonceBody
        (.ok (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ I) (permitDigestValue σ I) recoveredValue })
          (permitApprovePostState evmCallS I)) := by
    exact uniswapPermitAfterNonceSuccessAt (base := evmS) (cur := evmNonceS)
      (cur' := evmCallS) (I := I) (structHash := permitStructHashValue σ I)
      (digest := permitDigestValue σ I) (recovered := recoveredValue) (out := o)
      (by simpa [evmS, evmNonceS] using hstruct)
      (by simpa [evmS, evmNonceS] using hdigest)
      hcall hdec hnzSource hmatchSource
  have hafterNonce :
      ExecBlock config { contract := contract, locals := permitStore I } evmS
        permitAfterDeadlineBody
        (.ok (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ I) (permitDigestValue σ I) recoveredValue })
          (permitApprovePostState evmCallS I)) := by
    exact uniswapPermitBlockAfterNonce (evm := evmS) (I := I) hrest
  have hblock :
      ExecBlock config { contract := contract, locals := permitStore I } evmS
        permitTransition.body
        (.ok (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ I) (permitDigestValue σ I) recoveredValue })
          (permitApprovePostState evmCallS I)) := by
    exact uniswapPermitBlockAfterDeadline (evm := evmS) (I := I)
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hnotExpired)
      hafterNonce
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (permitStore I)
        permitTransition.body
        (.returned (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ I) (permitDigestValue σ I) recoveredValue })
          (permitApprovePostState evmCallS I) none) := by
    simpa [evmS, ExecTransitionBody] using ExecFuncBody.execBlockOK hblock
  have hok := uniswapPermitX_ecrecoverSignatureGuardOk
    (g := Sat256.ofUInt256 g) hdecoded hnz hmatch
  have rdRet := uniswapPermitX_approveAndReturn
    (g := Sat256.ofUInt256 g) hok hperm ho32 hoSize
  have hAccountsPost :
      Eq
        (sstoreAccountMap I.codeOwner σ'
          (mapSlot (permitSpenderMaskedWord I) (mapSlot (permitOwnerMaskedWord I) ⟨2⟩))
          (permitValueWord I))
        (permitApprovePostState evmCallS I).accountMap :=
    permitApprovePostState_accountMap_eq (evm := evmCallS) (I := I) (σ := σ')
      henvCall hAccountsCall
  exact rdRet.reEquivExecutionGen hcode hdispatch
    (uniswapDecode_permit_ok hsz228) hbody hAccountsPost
    (returnEquiv.fallthrough rfl rfl (by native_decide))

theorem uniswapPermitBodyCoreOk_afterNonce_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {σ' : AccountMap}
    {o : ByteArray} {evmCallS : EVM.State}
    (hcode : I.code = uniswapV2PairBytecode)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hstruct :
      evalExpr? config
        { contract := contract,
          locals := permitAfterNonceLoadStore
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) I }
        (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
        permitStructHashExpr = .ok (permitStructHashValue σ I))
    (hdigest :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) I
            (permitStructHashValue σ I) }
        (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
        permitDigestExpr = .ok (permitDigestValue σ I))
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)) ::
        permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o σ' k C)
    (hcall : typedCallViaEVM config
      (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
      (AccountAddress.ofNat 1) "ecrecover" 0
      [permitDigestValue σ I, permitVValue I, permitRValue I, permitSValue I]
      (true, evmCallS, o) false)
    (hAccountsCall : Eq σ' evmCallS.accountMap)
    (henvCall : evmCallS.executionEnv = I)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size)
    (hnz :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask ≠
        ⟨0⟩)
    (hmatch :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask =
        permitOwnerMaskedWord I) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  let recoveredValue : Value :=
    .address (AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
  have hdec : config.externalABI.decode? "ecrecover" o = some [recoveredValue] := by
    simpa [recoveredValue] using uniswapEcrecoverDecode_padded (returndata := o)
  have hnzSource : recoveredValue ≠ .address (AccountAddress.ofNat 0) := by
    simpa [recoveredValue] using permitRecoveredPaddedAddress_ne_zero_of_mask_ne_zero hnz
  have hmatchSource : recoveredValue = permitOwnerValue I := by
    simpa [recoveredValue] using permitRecoveredPaddedAddress_eq_owner_of_mask_eq hmatch
  have hrest :
      ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore evmS I }
        evmNonceS permitAfterNonceBody
        (.ok (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ I) (permitDigestValue σ I) recoveredValue })
          (permitApprovePostState evmCallS I)) := by
    exact uniswapPermitAfterNonceSuccessAt (base := evmS) (cur := evmNonceS)
      (cur' := evmCallS) (I := I) (structHash := permitStructHashValue σ I)
      (digest := permitDigestValue σ I) (recovered := recoveredValue) (out := o)
      (by simpa [evmS, evmNonceS] using hstruct)
      (by simpa [evmS, evmNonceS] using hdigest)
      hcall hdec hnzSource hmatchSource
  have hafterNonce :
      ExecBlock config { contract := contract, locals := permitStore I } evmS
        permitAfterDeadlineBody
        (.ok (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ I) (permitDigestValue σ I) recoveredValue })
          (permitApprovePostState evmCallS I)) := by
    exact uniswapPermitBlockAfterNonce (evm := evmS) (I := I) hrest
  have hblock :
      ExecBlock config { contract := contract, locals := permitStore I } evmS
        permitTransition.body
        (.ok (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ I) (permitDigestValue σ I) recoveredValue })
          (permitApprovePostState evmCallS I)) := by
    exact uniswapPermitBlockAfterDeadline (evm := evmS) (I := I)
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hnotExpired)
      hafterNonce
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (permitStore I)
        permitTransition.body
        (.returned (show Frame from
          { contract := contract,
            locals := permitAfterApproveStore evmS I
              (permitStructHashValue σ I) (permitDigestValue σ I) recoveredValue })
          (permitApprovePostState evmCallS I) none) := by
    simpa [evmS, ExecTransitionBody] using ExecFuncBody.execBlockOK hblock
  have hok := uniswapPermitX_ecrecoverSignatureGuardOk
    (g := Sat256.ofUInt256 g) hdecoded hnz hmatch
  have rdRet := uniswapPermitX_approveAndReturnShort
    (g := Sat256.ofUInt256 g) hok hperm hshort hoSize
  have hAccountsPost :
      Eq
        (sstoreAccountMap I.codeOwner σ'
          (mapSlot (permitSpenderMaskedWord I) (mapSlot (permitOwnerMaskedWord I) ⟨2⟩))
          (permitValueWord I))
        (permitApprovePostState evmCallS I).accountMap :=
    permitApprovePostState_accountMap_eq (evm := evmCallS) (I := I) (σ := σ')
      henvCall hAccountsCall
  exact rdRet.reEquivExecutionGen hcode hdispatch
    (uniswapDecode_permit_ok hsz228) hbody hAccountsPost
    (returnEquiv.fallthrough rfl rfl (by native_decide))

theorem uniswapPermitBodyRevertsAfterNonce {evm : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hrest : ExecBlock config
      { contract := contract, locals := permitAfterNonceLoadStore evm I }
      (permitAfterNonceState evm I) permitAfterNonceBody .reverted) :
    ExecTransitionBody config contract evm (permitStore I) permitTransition.body .reverted := by
  have hafterNonce := uniswapPermitBlockAfterNonce (evm := evm) (I := I) hrest
  have hblock := uniswapPermitBlockAfterDeadline (evm := evm) (I := I)
    hwv hnotExpired hafterNonce
  exact ExecFuncBody.execBlockRevert hblock

theorem uniswapPermitBodyCoreRevert_ecrecoverFailure_afterNonce
    {σ σ₀ A I} {g : UInt256}
    {o : ByteArray} {evmCallS : EVM.State}
    (hcode : I.code = uniswapV2PairBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hrev : RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (hstruct :
      evalExpr? config
        { contract := contract,
          locals := permitAfterNonceLoadStore
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) I }
        (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
        permitStructHashExpr = .ok (permitStructHashValue σ I))
    (hdigest :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) I
            (permitStructHashValue σ I) }
        (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
        permitDigestExpr = .ok (permitDigestValue σ I))
    (hcall : typedCallViaEVM config
      (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
      (AccountAddress.ofNat 1) "ecrecover" 0
      [permitDigestValue σ I, permitVValue I, permitRValue I, permitSValue I]
      (false, evmCallS, o) false) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  have hrest :
      ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore evmS I }
        evmNonceS permitAfterNonceBody .reverted := by
    exact uniswapPermitAfterNonceEcrecoverFailureAt (base := evmS) (cur := evmNonceS)
      (cur' := evmCallS) (I := I) (structHash := permitStructHashValue σ I)
      (digest := permitDigestValue σ I) (out := o)
      (by simpa [evmS, evmNonceS] using hstruct)
      (by simpa [evmS, evmNonceS] using hdigest)
      hcall
  have hbody : ExecTransitionBody config contract evmS (permitStore I)
      permitTransition.body .reverted := by
    exact uniswapPermitBodyRevertsAfterNonce
      (evm := evmS) (I := I)
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hnotExpired)
      hrest
  exact hrev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_permit_ok hsz228)
    (by simpa [evmS] using hbody)

theorem uniswapPermitBodyCoreRevert_zero_afterNonce
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {σ' : AccountMap}
    {o : ByteArray} {evmCallS : EVM.State}
    (hcode : I.code = uniswapV2PairBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hstruct :
      evalExpr? config
        { contract := contract,
          locals := permitAfterNonceLoadStore
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) I }
        (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
        permitStructHashExpr = .ok (permitStructHashValue σ I))
    (hdigest :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) I
            (permitStructHashValue σ I) }
        (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
        permitDigestExpr = .ok (permitDigestValue σ I))
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) ::
        permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o σ' k C)
    (hcall : typedCallViaEVM config
      (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
      (AccountAddress.ofNat 1) "ecrecover" 0
      [permitDigestValue σ I, permitVValue I, permitRValue I, permitSValue I]
      (true, evmCallS, o) false)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask =
        ⟨0⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  let recoveredValue : Value :=
    .address (AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32)))
  have hdec : config.externalABI.decode? "ecrecover" o = some [recoveredValue] := by
    simpa [recoveredValue] using uniswapEcrecoverDecode_ok (returndata := o) ho32
  have hzeroSource : recoveredValue = .address (AccountAddress.ofNat 0) := by
    simpa [recoveredValue] using permitRecoveredAddress_eq_zero_of_mask_eq_zero ho32 hzero
  have hrest :
      ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore evmS I }
        evmNonceS permitAfterNonceBody .reverted := by
    exact uniswapPermitAfterNonceRequireZeroRevertAt (base := evmS) (cur := evmNonceS)
      (cur' := evmCallS) (I := I) (structHash := permitStructHashValue σ I)
      (digest := permitDigestValue σ I) (recovered := recoveredValue) (out := o)
      (by simpa [evmS, evmNonceS] using hstruct)
      (by simpa [evmS, evmNonceS] using hdigest)
      hcall hdec hzeroSource
  have hbody : ExecTransitionBody config contract evmS (permitStore I)
      permitTransition.body .reverted := by
    exact uniswapPermitBodyRevertsAfterNonce
      (evm := evmS) (I := I)
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hnotExpired)
      hrest
  have hrev := uniswapPermitX_ecrecoverSignatureGuardZeroReverts
    (g := Sat256.ofUInt256 g) hdecoded hzero ho32 hoSize
  exact hrev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_permit_ok hsz228)
    (by simpa [evmS] using hbody)

theorem uniswapPermitBodyCoreRevert_mismatch_afterNonce
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {σ' : AccountMap}
    {o : ByteArray} {evmCallS : EVM.State}
    (hcode : I.code = uniswapV2PairBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hstruct :
      evalExpr? config
        { contract := contract,
          locals := permitAfterNonceLoadStore
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) I }
        (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
        permitStructHashExpr = .ok (permitStructHashValue σ I))
    (hdigest :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) I
            (permitStructHashValue σ I) }
        (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
        permitDigestExpr = .ok (permitDigestValue σ I))
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) ::
        permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o σ' k C)
    (hcall : typedCallViaEVM config
      (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
      (AccountAddress.ofNat 1) "ecrecover" 0
      [permitDigestValue σ I, permitVValue I, permitRValue I, permitSValue I]
      (true, evmCallS, o) false)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hnz :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask ≠
        ⟨0⟩)
    (hmismatch :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) solcAddrMask ≠
        permitOwnerMaskedWord I) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  let recoveredAddr := AccountAddress.ofNat (fromByteArrayBigEndian (o.extract 0 32))
  let recoveredValue : Value := .address recoveredAddr
  have hdec : config.externalABI.decode? "ecrecover" o = some [recoveredValue] := by
    simpa [recoveredValue, recoveredAddr] using uniswapEcrecoverDecode_ok (returndata := o) ho32
  have hnzValue : recoveredValue ≠ .address (AccountAddress.ofNat 0) := by
    simpa [recoveredValue, recoveredAddr] using
      permitRecoveredAddress_ne_zero_of_mask_ne_zero ho32 hnz
  have hnzAddr : recoveredAddr ≠ AccountAddress.ofNat 0 := by
    intro haddr
    apply hnzValue
    simp [recoveredValue, haddr]
  have hneValue : recoveredValue ≠ permitOwnerValue I := by
    simpa [recoveredValue, recoveredAddr] using
      permitRecoveredAddress_ne_owner_of_mask_ne ho32 hmismatch
  have hrest :
      ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore evmS I }
        evmNonceS permitAfterNonceBody .reverted := by
    exact uniswapPermitAfterNonceRequireMismatchRevertAt (base := evmS) (cur := evmNonceS)
      (cur' := evmCallS) (I := I) (structHash := permitStructHashValue σ I)
      (digest := permitDigestValue σ I) (recovered := recoveredValue) (out := o)
      (recoveredAddr := recoveredAddr)
      (by simpa [evmS, evmNonceS] using hstruct)
      (by simpa [evmS, evmNonceS] using hdigest)
      hcall hdec rfl hnzAddr hneValue
  have hbody : ExecTransitionBody config contract evmS (permitStore I)
      permitTransition.body .reverted := by
    exact uniswapPermitBodyRevertsAfterNonce
      (evm := evmS) (I := I)
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hnotExpired)
      hrest
  have hrev := uniswapPermitX_ecrecoverSignatureGuardMismatchReverts
    (g := Sat256.ofUInt256 g) hdecoded hnz hmismatch ho32 hoSize
  exact hrev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_permit_ok hsz228)
    (by simpa [evmS] using hbody)

theorem uniswapPermitBodyCoreRevert_zero_afterNonce_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {σ' : AccountMap}
    {o : ByteArray} {evmCallS : EVM.State}
    (hcode : I.code = uniswapV2PairBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hstruct :
      evalExpr? config
        { contract := contract,
          locals := permitAfterNonceLoadStore
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) I }
        (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
        permitStructHashExpr = .ok (permitStructHashValue σ I))
    (hdigest :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) I
            (permitStructHashValue σ I) }
        (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
        permitDigestExpr = .ok (permitDigestValue σ I))
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)) ::
        permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o σ' k C)
    (hcall : typedCallViaEVM config
      (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
      (AccountAddress.ofNat 1) "ecrecover" 0
      [permitDigestValue σ I, permitVValue I, permitRValue I, permitSValue I]
      (true, evmCallS, o) false)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size)
    (hzero :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask =
        ⟨0⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  let recoveredValue : Value :=
    .address (AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
  have hdec : config.externalABI.decode? "ecrecover" o = some [recoveredValue] := by
    simpa [recoveredValue] using uniswapEcrecoverDecode_padded (returndata := o)
  have hzeroSource : recoveredValue = .address (AccountAddress.ofNat 0) := by
    simpa [recoveredValue] using permitRecoveredPaddedAddress_eq_zero_of_mask_eq_zero hzero
  have hrest :
      ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore evmS I }
        evmNonceS permitAfterNonceBody .reverted := by
    exact uniswapPermitAfterNonceRequireZeroRevertAt (base := evmS) (cur := evmNonceS)
      (cur' := evmCallS) (I := I) (structHash := permitStructHashValue σ I)
      (digest := permitDigestValue σ I) (recovered := recoveredValue) (out := o)
      (by simpa [evmS, evmNonceS] using hstruct)
      (by simpa [evmS, evmNonceS] using hdigest)
      hcall hdec hzeroSource
  have hbody : ExecTransitionBody config contract evmS (permitStore I)
      permitTransition.body .reverted := by
    exact uniswapPermitBodyRevertsAfterNonce
      (evm := evmS) (I := I)
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hnotExpired)
      hrest
  have hrev := uniswapPermitX_ecrecoverSignatureGuardZeroRevertsShort
    (g := Sat256.ofUInt256 g) hdecoded hzero hshort hoSize
  exact hrev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_permit_ok hsz228)
    (by simpa [evmS] using hbody)

theorem uniswapPermitBodyCoreRevert_mismatch_afterNonce_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {σ' : AccountMap}
    {o : ByteArray} {evmCallS : EVM.State}
    (hcode : I.code = uniswapV2PairBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hnotExpired :
      ¬ (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hstruct :
      evalExpr? config
        { contract := contract,
          locals := permitAfterNonceLoadStore
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) I }
        (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
        permitStructHashExpr = .ok (permitStructHashValue σ I))
    (hdigest :
      evalExpr? config
        { contract := contract,
          locals := permitAfterStructHashStore
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) I
            (permitStructHashValue σ I) }
        (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
        permitDigestExpr = .ok (permitDigestValue σ I))
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)) ::
        permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o σ' k C)
    (hcall : typedCallViaEVM config
      (permitAfterNonceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I)
      (AccountAddress.ofNat 1) "ecrecover" 0
      [permitDigestValue σ I, permitVValue I, permitRValue I, permitSValue I]
      (true, evmCallS, o) false)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size)
    (hnz :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask ≠
        ⟨0⟩)
    (hmismatch :
      UInt256.land (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
          solcAddrMask ≠
        permitOwnerMaskedWord I) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  let recoveredAddr := AccountAddress.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32))
  let recoveredValue : Value := .address recoveredAddr
  have hdec : config.externalABI.decode? "ecrecover" o = some [recoveredValue] := by
    simpa [recoveredValue, recoveredAddr] using uniswapEcrecoverDecode_padded (returndata := o)
  have hnzValue : recoveredValue ≠ .address (AccountAddress.ofNat 0) := by
    simpa [recoveredValue, recoveredAddr] using
      permitRecoveredPaddedAddress_ne_zero_of_mask_ne_zero hnz
  have hnzAddr : recoveredAddr ≠ AccountAddress.ofNat 0 := by
    intro haddr
    apply hnzValue
    simp [recoveredValue, haddr]
  have hneValue : recoveredValue ≠ permitOwnerValue I := by
    simpa [recoveredValue, recoveredAddr] using
      permitRecoveredPaddedAddress_ne_owner_of_mask_ne hmismatch
  have hrest :
      ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore evmS I }
        evmNonceS permitAfterNonceBody .reverted := by
    exact uniswapPermitAfterNonceRequireMismatchRevertAt (base := evmS) (cur := evmNonceS)
      (cur' := evmCallS) (I := I) (structHash := permitStructHashValue σ I)
      (digest := permitDigestValue σ I) (recovered := recoveredValue) (out := o)
      (recoveredAddr := recoveredAddr)
      (by simpa [evmS, evmNonceS] using hstruct)
      (by simpa [evmS, evmNonceS] using hdigest)
      hcall hdec rfl hnzAddr hneValue
  have hbody : ExecTransitionBody config contract evmS (permitStore I)
      permitTransition.body .reverted := by
    exact uniswapPermitBodyRevertsAfterNonce
      (evm := evmS) (I := I)
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hnotExpired)
      hrest
  have hrev := uniswapPermitX_ecrecoverSignatureGuardMismatchRevertsShort
    (g := Sat256.ofUInt256 g) hdecoded hnz hmismatch hshort hoSize
  exact hrev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_permit_ok hsz228)
    (by simpa [evmS] using hbody)

theorem uniswapPermitBodyReverts_expired (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hexpired : (permitDeadlineWord I).toNat <
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    ExecTransitionBody config contract evm (permitStore I) permitTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [permitTransition] using
    (nonpayableSecondRequireReverts
      (cfg := config) (solm := { contract := contract, locals := permitStore I })
      (evm := evm)
      hwv
      (evalExpr_permit_deadline_ge_now_false evm I hexpired))

theorem uniswapPermitBodyStatic (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnotExpired : ¬ (permitDeadlineWord I).toNat <
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (permitStore I) permitTransition.body
      .staticViolation := by
  refine ExecFuncBody.execBlockStatic (uniswapPermitBlockAfterDeadline hwv hnotExpired ?_)
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_permit_domainSeparator_storage evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_permit_afterDomain_nonce_storage evm I)) ?_
  exact ExecBlock.consStatic
    (ExecStmt.assignStatic (evalExpr_permit_nonce_next evm I) (permitAssignNonce evm I) hperm)

theorem uniswapPermitBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 228)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1340⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hdec := uniswapDecode_permit_none_short (I := I) hsz4 hshort
  exact (uniswapPermitX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapPermitBodyDecodeFailed_short
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩)
    (hshort : I.calldata.size < 228)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩ rfl hsel
  exact uniswapPermitBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hdispatch
    (uniswapReachPermitBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapPermitBodyCoreRevert_expired
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz228 : 228 ≤ I.calldata.size)
    (hexpired : (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1340⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evmS (permitStore I) permitTransition.body .reverted := by
    exact uniswapPermitBodyReverts_expired evmS I
      (by simp only [evmS, initState]; exact hwv)
      (by simpa [evmS, initState] using hexpired)
  exact (uniswapPermitX_expired (g := Sat256.ofUInt256 g) hexpired
      (uniswapPermitX_decoded_masked (g := Sat256.ofUInt256 g) hsz228 hsize hreach))
    |>.reEquivExecutionRevert hcode hdispatch (uniswapDecode_permit_ok hsz228) hbody

theorem uniswapPermitBodyRevert_expired
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩)
    (hsz228 : 228 ≤ I.calldata.size)
    (hexpired : (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩ rfl hsel
  exact uniswapPermitBodyCoreRevert_expired hcode hsize hwv hsz228 hexpired hdispatch
    (uniswapReachPermitBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapPermitBody_depthOk
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hdepth : I.depth.val < 1024) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  by_cases hsz228 : 228 ≤ I.calldata.size
  · by_cases hexpired :
      (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat
    · exact uniswapPermitBodyRevert_expired hcode hsize hwv hsel hsz228 hexpired hdispatch
    · have hsz4 : 4 ≤ I.calldata.size :=
        calldata_size_ge_of_selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩ rfl hsel
      have hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1340⟩
          [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          σ k C :=
        uniswapReachPermitBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
      have hdecoded := uniswapPermitX_decoded_masked (g := Sat256.ofUInt256 g)
        hsz228 hsize hreach
      have hdeadlineOk := uniswapPermitX_deadlineOk (g := Sat256.ofUInt256 g)
        hexpired hdecoded
      have hnonceEvm := uniswapPermitX_nonceStored (g := Sat256.ofUInt256 g)
        hperm hdeadlineOk
      have hstructEvm := uniswapPermitX_structHashed (g := Sat256.ofUInt256 g)
        hnonceEvm
      have hdigestEvm := uniswapPermitX_digestHashed (g := Sat256.ofUInt256 g)
        hstructEvm
      obtain ⟨σ', z, o, A_in, callGas, k, C, hΘ, rd5814, hoSize⟩ :=
        uniswapPermitX_ecrecoverStaticcallMade (g := Sat256.ofUInt256 g) hdigestEvm hdepth
      let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
      have hstructSource :
          evalExpr? config
            { contract := contract,
              locals := permitAfterNonceLoadStore evmS I }
            (permitAfterNonceState evmS I)
            permitStructHashExpr = .ok (permitStructHashValue σ I) := by
        simpa [evmS] using
          (evalExpr_permit_structHash_at
            (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g)
            (cur := permitAfterNonceState evmS I))
      have hdigestSource :
          evalExpr? config
            { contract := contract,
              locals := permitAfterStructHashStore evmS I (permitStructHashValue σ I) }
            (permitAfterNonceState evmS I)
            permitDigestExpr = .ok (permitDigestValue σ I) := by
        simpa [evmS] using
          (evalExpr_permit_digest_afterNonce_at
            (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g))
      obtain ⟨evmCallS, hcall, hAccountsCall, _hσ0, henv⟩ :=
        uniswapPermitEcrecoverTypedCall_source (g := g) hdepth hsz228 hΘ
      obtain ⟨hfailure, hshortDecoded, hlongDecoded⟩ :=
        uniswapPermitX_ecrecoverStatusAndReturnDecodedAllAt rd5814 hoSize
      by_cases hz : z = false
      · have hcallFalse : typedCallViaEVM config
            (permitAfterNonceState evmS I)
            (AccountAddress.ofNat 1) "ecrecover" 0
            [permitDigestValue σ I, permitVValue I, permitRValue I, permitSValue I]
            (false, evmCallS, o) false := by
          simpa [evmS, hz] using hcall
        exact uniswapPermitBodyCoreRevert_ecrecoverFailure_afterNonce
          hcode hwv hsz228 hexpired hdispatch (hfailure hz)
          (by simpa [evmS] using hstructSource)
          (by simpa [evmS] using hdigestSource)
          hcallFalse
      · have hzTrue : z = true := by
          cases z <;> simp at hz ⊢
        have hcallTrue : typedCallViaEVM config
            (permitAfterNonceState evmS I)
            (AccountAddress.ofNat 1) "ecrecover" 0
            [permitDigestValue σ I, permitVValue I, permitRValue I, permitSValue I]
            (true, evmCallS, o) false := by
          simpa [evmS, hzTrue] using hcall
        by_cases hshort : o.size < 32
        · have hdecodedShort := hshortDecoded hzTrue hshort
          let recovered :=
            UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32))
          by_cases hzero : UInt256.land recovered solcAddrMask = ⟨0⟩
          · exact uniswapPermitBodyCoreRevert_zero_afterNonce_short
              hcode hwv hsz228 hexpired hdispatch
              (by simpa [evmS] using hstructSource)
              (by simpa [evmS] using hdigestSource)
              (by simpa [recovered] using hdecodedShort)
              hcallTrue hshort hoSize
              (by simpa [recovered] using hzero)
          · by_cases hmatch : UInt256.land recovered solcAddrMask = permitOwnerMaskedWord I
            · exact uniswapPermitBodyCoreOk_afterNonce_short
                hcode hperm hwv hsz228 hexpired hdispatch
                (by simpa [evmS] using hstructSource)
                (by simpa [evmS] using hdigestSource)
                (by simpa [recovered] using hdecodedShort)
                hcallTrue hAccountsCall henv hshort hoSize
                (by simpa [recovered] using hzero)
                (by simpa [recovered] using hmatch)
            · exact uniswapPermitBodyCoreRevert_mismatch_afterNonce_short
                hcode hwv hsz228 hexpired hdispatch
                (by simpa [evmS] using hstructSource)
                (by simpa [evmS] using hdigestSource)
                (by simpa [recovered] using hdecodedShort)
                hcallTrue hshort hoSize
                (by simpa [recovered] using hzero)
                (by simpa [recovered] using hmatch)
        · have ho32 : 32 ≤ o.size := by omega
          have hdecodedLong := hlongDecoded hzTrue ho32
          let recovered := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
          by_cases hzero : UInt256.land recovered solcAddrMask = ⟨0⟩
          · exact uniswapPermitBodyCoreRevert_zero_afterNonce
              hcode hwv hsz228 hexpired hdispatch
              (by simpa [evmS] using hstructSource)
              (by simpa [evmS] using hdigestSource)
              (by simpa [recovered] using hdecodedLong)
              hcallTrue ho32 hoSize
              (by simpa [recovered] using hzero)
          · by_cases hmatch : UInt256.land recovered solcAddrMask = permitOwnerMaskedWord I
            · exact uniswapPermitBodyCoreOk_afterNonce
                hcode hperm hwv hsz228 hexpired hdispatch
                (by simpa [evmS] using hstructSource)
                (by simpa [evmS] using hdigestSource)
                (by simpa [recovered] using hdecodedLong)
                hcallTrue hAccountsCall henv ho32 hoSize
                (by simpa [recovered] using hzero)
                (by simpa [recovered] using hmatch)
            · exact uniswapPermitBodyCoreRevert_mismatch_afterNonce
                hcode hwv hsz228 hexpired hdispatch
                (by simpa [evmS] using hstructSource)
                (by simpa [evmS] using hdigestSource)
                (by simpa [recovered] using hdecodedLong)
                hcallTrue ho32 hoSize
                (by simpa [recovered] using hzero)
                (by simpa [recovered] using hmatch)
  · exact uniswapPermitBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

theorem uniswapPermitBody_depthLimit
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition)
    (hdepth : I.depth = 1024) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  by_cases hsz228 : 228 ≤ I.calldata.size
  · by_cases hexpired :
      (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat
    · exact uniswapPermitBodyRevert_expired hcode hsize hwv hsel hsz228 hexpired hdispatch
    · have hsz4 : 4 ≤ I.calldata.size :=
        calldata_size_ge_of_selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩ rfl hsel
      have hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1340⟩
          [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          σ k C :=
        uniswapReachPermitBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
      have hdecoded := uniswapPermitX_decoded_masked (g := Sat256.ofUInt256 g)
        hsz228 hsize hreach
      have hdeadlineOk := uniswapPermitX_deadlineOk (g := Sat256.ofUInt256 g)
        hexpired hdecoded
      have hnonceEvm := uniswapPermitX_nonceStored (g := Sat256.ofUInt256 g)
        hperm hdeadlineOk
      have hstructEvm := uniswapPermitX_structHashed (g := Sat256.ofUInt256 g)
        hnonceEvm
      have hdigestEvm := uniswapPermitX_digestHashed (g := Sat256.ofUInt256 g)
        hstructEvm
      have hrev := uniswapPermitX_ecrecoverStaticcallDepthReverts
        (g := Sat256.ofUInt256 g) hdigestEvm hdepth
      let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmNonceS := permitAfterNonceState evmS I
      have hstructSource :
          evalExpr? config
            { contract := contract,
              locals := permitAfterNonceLoadStore evmS I }
            evmNonceS permitStructHashExpr = .ok (permitStructHashValue σ I) := by
        simpa [evmS, evmNonceS] using
          (evalExpr_permit_structHash_at
            (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g)
            (cur := permitAfterNonceState evmS I))
      have hdigestSource :
          evalExpr? config
            { contract := contract,
              locals := permitAfterStructHashStore evmS I (permitStructHashValue σ I) }
            evmNonceS permitDigestExpr = .ok (permitDigestValue σ I) := by
        simpa [evmS, evmNonceS] using
          (evalExpr_permit_digest_afterNonce_at
            (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g))
      let evmCallS : EVM.State :=
        { evmNonceS with
          substate := (evmNonceS.addAccessedAccount (AccountAddress.ofNat 1)).substate }
      have hdepthSolm : evmNonceS.executionEnv.depth = 1024 := by
        simpa [evmNonceS, evmS, permitAfterNonceState, storageStore_executionEnv, initState]
          using hdepth
      have hcall : typedCallViaEVM config evmNonceS (AccountAddress.ofNat 1) "ecrecover" 0
          [permitDigestValue σ I, permitVValue I, permitRValue I, permitSValue I]
          (false, evmCallS, ByteArray.empty) false := by
        simpa [evmCallS] using
          (callNotMade_depthLimit
            (cfg := config) (evm := evmNonceS) (tgt := AccountAddress.ofNat 1)
            (name := "ecrecover")
            (args := [permitDigestValue σ I, permitVValue I, permitRValue I,
              permitSValue I])
            (callPerm := false)
            (uniswapEcrecoverEncode_eq σ I hsz228)
            hdepthSolm)
      exact uniswapPermitBodyCoreRevert_ecrecoverFailure_afterNonce
        hcode hwv hsz228 hexpired hdispatch hrev
        (by simpa [evmS, evmNonceS] using hstructSource)
        (by simpa [evmS, evmNonceS] using hdigestSource)
        hcall
  · exact uniswapPermitBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

theorem uniswapPermitBody
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  by_cases hdepth : I.depth.val < 1024
  · exact uniswapPermitBody_depthOk
      hcode hsize hperm hwv hsel hdispatch hdepth
  · rw [not_lt] at hdepth
    have hdepth1024 : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
    exact uniswapPermitBody_depthLimit
      hcode hsize hperm hwv hsel hdispatch hdepth1024

/-- `permit` with any call permission; a static call halts at the nonce `SSTORE`. -/
theorem uniswapPermitBodyAnyPerm
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some permitTransition) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  by_cases hperm : I.perm = true
  · exact uniswapPermitBody hcode hsize hperm hwv hsel hdispatch
  replace hperm : I.perm = false := by simpa using hperm
  by_cases hsz228 : 228 ≤ I.calldata.size
  · by_cases hexpired :
      (permitDeadlineWord I).toNat < (UInt256.ofNat I.header.timestamp).toNat
    · exact uniswapPermitBodyRevert_expired hcode hsize hwv hsel hsz228 hexpired hdispatch
    · have hsz4 : 4 ≤ I.calldata.size :=
        calldata_size_ge_of_selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩ rfl hsel
      have hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1340⟩
          [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          σ k C :=
        uniswapReachPermitBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
      exact (uniswapPermitX_nonceStoredStatic (g := Sat256.ofUInt256 g) hperm
          (uniswapPermitX_deadlineOk (g := Sat256.ofUInt256 g) hexpired
            (uniswapPermitX_decoded_masked (g := Sat256.ofUInt256 g) hsz228 hsize hreach)))
        |>.reEquivStaticHalt hcode hdispatch (uniswapDecode_permit_ok hsz228)
          (uniswapPermitBodyStatic (initState σ σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) (by simpa [initState] using hexpired)
            (by simp only [initState]; exact hperm))
  · exact uniswapPermitBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

end UniswapV2Pair
