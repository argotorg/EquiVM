import Benchmarks.EAS.Attester.MultiAttestSourceReturn
import Benchmarks.EAS.Attester.MultiAttestStartTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem multiAttestExternalCorrect (imms : Store) (hfit : immutablesFit contract imms)
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {schemas rows : List Value} {locals : Store} {eas : EVM.Address} {aw k C}
    (hcode : I.code = immutableLayout.runtime attesterBytecode (wordsOf imms))
    (hselector : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = true)
    (hd : decodeArrays? uint256 I.calldata = some (.array schemas, .array rows))
    (hshape : BatchShape I.calldata) (hrows : BatchRowsValid I.calldata)
    (heas : imms.get? "_eas" = some (.address eas))
    (hp : ExecBlock config
      ⟨contract, multiAttestLocals schemas rows, restrictImmutables contract imms⟩
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) (multiAttestTransition.body.take 7)
      (.ok ⟨contract, locals, restrictImmutables contract imms⟩
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)))
    (hlocalEas : locals.get? "eas" = some (.address eas))
    (hrequest : locals.get? "multiRequests" = some (multiAttestRequests I.calldata))
    (halloc : locals.get? "allocationEnd" = some (.int (Int.ofNat (multiAttestBuiltFree
        I.calldata))))
    (rd : RD (immutableLayout.runtime attesterBytecode (wordsOf imms)) I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1772⟩
      [UInt256.ofNat (multiAttestEncodedEnd I.calldata), ⟨1152239886⟩,
        UInt256.land (wordsOf imms "_eas") solcAddrMask, ⟨128⟩,
        UInt256.ofNat (arrayCount I.calldata 4), ⟨96⟩, UInt256.ofNat (arrayCount I.calldata 4),
        UInt256.ofNat (arrayDataNat I.calldata 36), UInt256.ofNat (arrayCount I.calldata 4),
        UInt256.ofNat (arrayDataNat I.calldata 4), ⟨121⟩, solcSelectorWord I]
      (multiAttestEncodedMemory I.calldata) aw ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hc := decodeArrays_some_checks hd
  have hdispatch := attesterMultiAttestDispatch hselector
  have hdec := multiAttestDecode_some hd
  have hw : wordsOf imms "_eas" = UInt256.ofNat eas.val := wordsOf_of_get heas rfl
  have ht : eas = AccountAddress.ofUInt256 (UInt256.land (wordsOf imms "_eas") solcAddrMask) := by
    rw [hw, u256_land_comm, easWord_mask, accountAddress_roundtrip]
  obtain ⟨gasArg, aw, k, C, rd⟩ := multiAttestReachCall rd (by simp) hc hshape hrows
  have hcallDec : decode (immutableLayout.runtime attesterBytecode (wordsOf imms)) ⟨1786⟩ =
      some (.CALL, none) := by
    immutable_decode(immutableLayout, attesterBytecode, wordsOf imms, (⟨1786⟩ : UInt256),
      UInt8.ofNat 241, .CALL, none, immutableLayout_inBounds, immutableTemplate_size64)
  have hb := multiAttestEncodedEnd_bounds hc hshape hrows
  have hf := multiAttestBuiltMemory_bounds hc hshape hrows
  have hcb := multiAttestCallBounds hc hshape hrows
  have hencode : config.externalABI.encode? "multiAttest" [multiAttestRequests I.calldata] =
      some ((multiAttestEncodedMemory I.calldata).readWithPadding
        (UInt256.ofNat (multiAttestBuiltFree I.calldata)).toNat
        (UInt256.ofNat (multiAttestEncodedEnd I.calldata - multiAttestBuiltFree I.calldata)).toNat)
            := by
    simpa only [ulit_toNat' _ (by omega : multiAttestBuiltFree I.calldata < UInt256.size),
      ulit_toNat' _ (by omega : multiAttestEncodedEnd I.calldata - multiAttestBuiltFree I.calldata <
        UInt256.size)] using multiAttestRequests_encoding hc hshape hrows
  have hfailure {evm' : State} {out : ByteArray}
      (hcall : typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I) eas
        "multiAttest" 0 [multiAttestRequests I.calldata] (false, evm', out)) :
      ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (multiAttestLocals schemas rows) multiAttestTransition.body .reverted
        (restrictImmutables contract imms) := by
    apply ExecFuncBody.execBlockRevert
    exact multiAttestSourceSuffix hp
      (multiAttestSourceCallFailure hlocalEas hrequest hencode hcall)
  by_cases hdepth : I.depth = 1024
  · obtain ⟨k', C', rd'⟩ := RD.callDepthLimit rd hcallDec hdepth (by simp)
    have hsource := hfailure
      (callNotMade_depthLimit (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) hencode hdepth)
    exact (multiAttestAfterCallFailure rd' (by simp)).reEquivExecutionRevert
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
      exact (multiAttestAfterCallFailure rd' (by simp)).reEquivExecutionRevert
        hcode hdispatch hdec (hfailure hcall)
  | true =>
      have hsmall : ((multiAttestEncodedMemory I.calldata).readWithPadding
          (UInt256.ofNat (multiAttestBuiltFree I.calldata)).toNat
          (UInt256.ofNat (multiAttestEncodedEnd I.calldata - multiAttestBuiltFree
              I.calldata)).toNat).size
          ≤ maxReturnDataSizeByGas := by
        apply ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas
        rw [ulit_toNat' _ (by omega)]; exact hcb.2
      have hout := Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hθ
          hsmall
      have houtput : out.write 0 (multiAttestEncodedMemory I.calldata)
          (UInt256.ofNat (multiAttestBuiltFree I.calldata)).toNat
          ((⟨0⟩ : UInt256) ⊓ UInt256.ofNat out.size).toNat = multiAttestEncodedMemory I.calldata :=
        callOutputMem_zero _ _ _
      rw [houtput] at rd'
      obtain ⟨aw1, k1, C1, h1⟩ := multiAttestReachReturnDecoder rd' (by simp) hc hshape hrows hout
      have hsource := multiAttestSourceReturn
        (imms := restrictImmutables contract imms)
        (evm := { initState σ σ₀ (Sat256.ofUInt256 g) A I with accountMap := σ', substate := A' })
        (locals := multiAttestCallLocals locals
          ((multiAttestEncodedMemory I.calldata).readWithPadding
            (UInt256.ofNat (multiAttestBuiltFree I.calldata)).toNat
            (UInt256.ofNat (multiAttestEncodedEnd I.calldata - multiAttestBuiltFree
                I.calldata)).toNat)
          true out)
        (base := multiAttestBuiltFree I.calldata) (out := out)
        (by simpa only [multiAttestCallLocals, Std.HashMap.get?_eq_getElem?,
              Std.HashMap.getElem?_insert,
              show ("rawReturn" == "allocationEnd") = false from rfl,
              show ("ok" == "allocationEnd") = false from rfl,
              show ("encodedRequest" == "allocationEnd") = false from rfl,
              Bool.false_eq_true, if_false] using halloc)
        (by simp [multiAttestCallLocals]) (by omega)
      rcases returnArrayDecode h1 (by simp) (by omega)
          (by rw [multiAttestEncodedMemory_size hc hshape hrows]; omega)
          (by omega) (by rw [attesterRuntime_validJumps]; native_decide) with
        ⟨hbad, hrev⟩ | ⟨hchecks, hcap, aw2, k2, C2, h2⟩
      · have hbody := ExecFuncBody.execBlockRevert (multiAttestSourceSuffix hp
          (multiAttestSourceCallSuccessPrefix hlocalEas hrequest hencode hcall (hsource.1 hbad)))
        exact hrev.reEquivExecutionRevert hcode hdispatch hdec hbody
      · have hbody := ExecFuncBody.execBlockRet (multiAttestSourceSuffix hp
          (multiAttestSourceCallSuccessPrefix hlocalEas hrequest hencode hcall
            (hsource.2 hchecks hcap)))
        obtain ⟨aw3, k3, C3, h3⟩ := attesterRuntime_block_1873_packed (by simp)
          (by rw [attesterRuntime_validJumps]; native_decide) h2
        have hret := multiAttestReturnDecoded h3 (by simp) (by omega) hchecks hcap
        exact hret.reEquivExecutionGen hcode hdispatch hdec hbody rfl
          (.returned rfl (wordArrayReturn_encoding (returnArrayWords out) (returnArrayCount out)))

end Benchmarks.EAS.Attester
