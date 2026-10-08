import Benchmarks.EAS.Attester.MultiRevokeSource
import Benchmarks.EAS.Attester.MultiRevokeCallTrace
import Benchmarks.EAS.Attester.MultiRevokeStartTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem multiRevokeExternalCorrect (imms : Store) (hfit : immutablesFit contract imms)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {schemas rows : List Value} {locals : Store} {eas : EVM.Address} {aw k C}
    (hcode : I.code = immutableLayout.runtime attesterBytecode (wordsOf imms))
    (hselector : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = true)
    (hd : decodeArrays? bytes32 I.calldata = some (.array schemas, .array rows))
    (hshape : BatchShape I.calldata) (hrows : BatchRowsValid I.calldata)
    (heas : imms.get? "_eas" = some (.address eas))
    (hp : ExecBlock config
      ⟨contract, multiRevokeLocals schemas rows, restrictImmutables contract imms⟩
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) (multiRevokeTransition.body.take 6)
      (.ok ⟨contract, locals, restrictImmutables contract imms⟩
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)))
    (hlocalEas : locals.get? "eas" = some (.address eas))
    (hrequest : locals.get? "multiRequests" = some (multiRevokeRequests I.calldata))
    (rd : RD (immutableLayout.runtime attesterBytecode (wordsOf imms)) I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨877⟩
      [UInt256.ofNat (multiRevokeEncodedEnd I.calldata), ⟨1287121381⟩,
        UInt256.land (wordsOf imms "_eas") solcAddrMask, ⟨128⟩,
        UInt256.ofNat (arrayCount I.calldata 4), UInt256.ofNat (arrayCount I.calldata 4),
        UInt256.ofNat (arrayDataNat I.calldata 36), UInt256.ofNat (arrayCount I.calldata 4),
        UInt256.ofNat (arrayDataNat I.calldata 4), ⟨100⟩, solcSelectorWord I]
      (multiRevokeEncodedMemory I.calldata) aw ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hc := decodeArrays_some_checks hd
  have hdispatch := attesterMultiRevokeDispatch hselector
  have hdec := multiRevokeDecode_some hd
  have hw : wordsOf imms "_eas" = UInt256.ofNat eas.val := wordsOf_of_get heas rfl
  have ht : eas = AccountAddress.ofUInt256 (UInt256.land (wordsOf imms "_eas") solcAddrMask) := by
    rw [hw, u256_land_comm, easWord_mask, accountAddress_roundtrip]
  have hrecv : evalExpr? config ⟨contract, locals, restrictImmutables contract imms⟩
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) (.var "eas") = .ok (.address eas) :=
    evalLocalValue hlocalEas
  have hargs : evalExprs? config ⟨contract, locals, restrictImmutables contract imms⟩
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) [.var "multiRequests"] =
        .ok [multiRevokeRequests I.calldata] := by
    simp only [evalExprs?, evalExprList?, evalExpr?, hrequest, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
  have hguard := evalExpr_codeGuard_of_accounts_eq (σ := σ)
    (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) rfl ht hrecv
  by_cases hzero : extCodeSizeWord σ (UInt256.land (wordsOf imms "_eas") solcAddrMask) = ⟨0⟩
  · have hsource : ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (multiRevokeLocals schemas rows)
        multiRevokeTransition.body .reverted (restrictImmutables contract imms) := by
      apply ExecFuncBody.execBlockRevert
      apply multiRevokeSourceSuffix hp
      exact checkedExternalCallVarNoCode (by simpa only [hzero] using hguard)
    exact (multiRevokeNoCode rd (by simp) hzero).reEquivExecutionRevert hcode hdispatch hdec hsource
  have hpos : 0 < (extCodeSizeWord σ (UInt256.land (wordsOf imms "_eas") solcAddrMask)).toNat :=
    Nat.pos_of_ne_zero (fun hz ↦ hzero (uint256_toNat_eq_zero hz))
  simp only [hpos, decide_true] at hguard
  obtain ⟨gasArg, aw, k, C, rd⟩ := multiRevokeReachCall rd (by simp) hc hshape hrows hzero
  have hcallDec : decode (immutableLayout.runtime attesterBytecode (wordsOf imms)) ⟨906⟩ =
      some (.CALL, none) := by
    immutable_decode(immutableLayout, attesterBytecode, wordsOf imms, (⟨906⟩ : UInt256),
      UInt8.ofNat 241, .CALL, none, immutableLayout_inBounds, immutableTemplate_size64)
  have hb := multiRevokeEncodedEnd_bounds hc hshape hrows
  have hencode : config.externalABI.encode? "multiRevoke" [multiRevokeRequests I.calldata] =
      some ((multiRevokeEncodedMemory I.calldata).readWithPadding
        (UInt256.ofNat (multiRevokeBuiltFree I.calldata)).toNat
        (UInt256.ofNat (multiRevokeEncodedEnd I.calldata - multiRevokeBuiltFree I.calldata)).toNat)
            := by
    simpa only [ulit_toNat' _ (by omega : multiRevokeBuiltFree I.calldata < UInt256.size),
      ulit_toNat' _ (by omega : multiRevokeEncodedEnd I.calldata - multiRevokeBuiltFree I.calldata <
        UInt256.size)] using multiRevokeRequests_encoding hc hshape hrows
  have hfailure {evm' : State} {out : ByteArray}
      (hcall : typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I) eas
        "multiRevoke" 0 [multiRevokeRequests I.calldata] (false, evm', out)) :
      ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (multiRevokeLocals schemas rows) multiRevokeTransition.body .reverted
        (restrictImmutables contract imms) := by
    apply ExecFuncBody.execBlockRevert
    apply multiRevokeSourceSuffix hp
    exact checkedExternalCallVarFailure hguard hlocalEas hargs
      (by simpa only [address_of_val] using hcall)
  by_cases hdepth : I.depth = 1024
  · obtain ⟨k', C', rd'⟩ := RD.callDepthLimit rd hcallDec hdepth (by simp)
    have hsource := hfailure
      (callNotMade_depthLimit (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hencode hdepth)
    exact (multiRevokeAfterCallFailure rd' (by simp)).reEquivExecutionRevert
      hcode hdispatch hdec hsource
  have hdepthlt : I.depth.val < 1024 := by
    have hbound := I.depth.isLt
    have hne : I.depth.val ≠ 1024 := fun h ↦ hdepth (Fin.ext h)
    omega
  obtain ⟨σ', z, out, Ain, callGas, k', C', ⟨g'', A', hθ⟩, rd', _hout⟩ :=
    RD.call rd hcallDec hdepthlt (by simp)
  have hcall := callCoincides (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (callPerm := true) hdepth ht hencode (by simpa only [Bool.true_and] using hθ)
  cases z with
  | false =>
      exact (multiRevokeAfterCallFailure rd' (by simp)).reEquivExecutionRevert
        hcode hdispatch hdec (hfailure hcall)
  | true =>
      have hsource := ExecFuncBody.execBlockOK
        (multiRevokeSourceSuffix hp (checkedExternalCallVarSuccess hguard hlocalEas hargs
          (by simpa only [address_of_val] using hcall) (by rfl)))
      exact (multiRevokeAfterCallSuccess rd').reEquivExecutionGen hcode hdispatch hdec hsource rfl
        (.fallthrough rfl rfl (by native_decide))

end Benchmarks.EAS.Attester
