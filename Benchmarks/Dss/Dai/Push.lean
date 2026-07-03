import Benchmarks.Dss.Dai.TransferFrom

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

abbrev pushStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "usr" (transferFromDstValue I)).insert "wad" (transferFromWadValue I)

theorem pushStore_index_usr (I : ExecutionEnv) :
    (pushStore I)["usr"] = transferFromDstValue I := by
  unfold pushStore
  simp [Std.HashMap.getElem_insert]

theorem pushStore_index_wad (I : ExecutionEnv) :
    (pushStore I)["wad"] = transferFromWadValue I := by
  unfold pushStore
  simp

theorem daiLookupTransferFromForPush :
    lookupCallable? contract "transferFrom" = some transferFromTransition.toCallable := by
  rfl

theorem daiDecode_push_ok {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 14)) (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (pushTransition.params.map Param.name)
      (transitionSignature pushTransition).paramTypes I.calldata = some (pushStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["usr", "wad"] [addr, uint256]
    I.calldata = _
  unfold pushStore transferFromDstValue transferFromWadValue
  rw [transferFromDstWord_of_push I hsel, transferFromWadWord_of_push I hsel]
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["usr", "wad"]
      [abiAddress, abiUInt256] I.calldata =
    some (((∅ : Store).insert "usr"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "wad"
      (.int (Int.ofNat (calldataWord I.calldata 36).toNat)))
  exact decodeCalldata_legacyAddress_uint256_ok
    (cd := I.calldata) (x := "usr") (y := "wad") hsz68

theorem daiDecode_push_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (pushTransition.params.map Param.name)
      (transitionSignature pushTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["usr", "wad"] [addr, uint256]
    I.calldata = none
  simpa using decodeCalldata_legacyAddress_uint256_none_short
    (cd := I.calldata) (x := "usr") (y := "wad") hsz4 hshort

theorem evalExprs_push_internalCall (evm : EVM.State) (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 14))
    (hsrc : evm.executionEnv.source = I.source) :
    evalExprs? config { contract := contract, locals := pushStore I } evm
      [sender, .var "usr", .var "wad"] =
        .ok [transferFromSrcValue I, transferFromDstValue I, transferFromWadValue I] := by
  have hsrcVal : Value.address evm.executionEnv.source = transferFromSrcValue I := by
    unfold transferFromSrcValue
    rw [transferFromSrcWord_of_push I hsel, hsrc, solcSource_ofNat]
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure, sender,
    envValue, pushStore_index_usr, pushStore_index_wad, hsrcVal]

theorem daiPushBodyReturns_from_transferFrom (evm evmPost : EVM.State) (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 14))
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcallee :
      ExecTransitionBody config contract evm (transferFromCallStore I) transferFromTransition.body
        (.returned { contract := contract, locals := transferFromCallStore I } evmPost
          (some [.bool true]))) :
    ∃ cs, ExecTransitionBody config contract evm (pushStore I) pushTransition.body
      (.returned cs evmPost none) := by
  let caller : Frame := { contract := contract, locals := pushStore I }
  let callerAfter : Frame :=
    { contract := contract, locals := (pushStore I).insert "_ok" (.bool true) }
  have hcall : ExecStmt config caller evm
      (.internalCall "transferFrom" [sender, .var "usr", .var "wad"] "_ok")
      (.ok callerAfter evmPost) := by
    simpa [caller, callerAfter] using
      internalCallTransitionReturn (cfg := config)
        (caller := caller) (evm := evm) (calleeEvm := evmPost)
        (name := "transferFrom") (args := [sender, .var "usr", .var "wad"])
        (retVar := "_ok")
        (argVals := [transferFromSrcValue I, transferFromDstValue I, transferFromWadValue I])
        (callee := transferFromTransition) (locals := transferFromCallStore I)
        (calleeSolm := { contract := contract, locals := transferFromCallStore I })
        (value := .bool true)
        (evalExprs_push_internalCall evm I hsel hsrc)
        daiLookupTransferFromForPush
        (daiBindTransferFromCallStore I)
        hcallee
  refine ⟨callerAfter, ExecFuncBody.execBlockOK ?_⟩
  rw [pushTransition]
  exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
    ExecBlock.consNormal hcall ExecBlock.nil

theorem daiPushBodyReverts_from_transferFrom (evm : EVM.State) (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 14))
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcallee :
      ExecTransitionBody config contract evm (transferFromCallStore I) transferFromTransition.body
        .reverted) :
    ExecTransitionBody config contract evm (pushStore I) pushTransition.body .reverted := by
  let caller : Frame := { contract := contract, locals := pushStore I }
  have hcall : ExecStmt config caller evm
      (.internalCall "transferFrom" [sender, .var "usr", .var "wad"] "_ok") .reverted := by
    exact internalCallTransitionRevert (cfg := config)
      (caller := caller) (evm := evm)
      (name := "transferFrom") (args := [sender, .var "usr", .var "wad"])
      (retVar := "_ok")
      (argVals := [transferFromSrcValue I, transferFromDstValue I, transferFromWadValue I])
      (callee := transferFromTransition) (locals := transferFromCallStore I)
      (evalExprs_push_internalCall evm I hsel hsrc)
      daiLookupTransferFromForPush
      (daiBindTransferFromCallStore I)
      hcallee
  rw [pushTransition]
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert hcall

theorem daiPushX_toTransferFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsel : selIs I (daiSelBytes 14))
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1034⟩ [daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1411⟩
      [transferFromWadWord I, transferFromDstMaskedWord I, transferFromSrcMaskedWord I,
        ⟨3886⟩, transferFromWadWord I, transferFromDstMaskedWord I, ⟨686⟩,
        daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1056⟩ := RD.daiAddressUint256ExternalLenOk
    (entry := ⟨1034⟩) (ret := ⟨686⟩) (routine := ⟨3875⟩) hreach
    dai_address_uint256_external_entry_wf (by jump_dest) hsz68 hsize
  obtain ⟨_, _, rd3875raw⟩ := RD.daiAddressUint256ExternalMaskAndJumpMasked
    (entry := ⟨1034⟩) (ret := ⟨686⟩) (routine := ⟨3875⟩)
    (R := [daiSelWord I])
    rd1056 dai_address_uint256_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  obtain ⟨_, _, rd3875⟩ :
      ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3875⟩
        [transferFromWadWord I, transferFromDstMaskedWord I, ⟨686⟩, daiSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [transferFromDstMaskedWord, transferFromDstWord_of_push I hsel,
        transferFromWadWord_of_push I hsel, calldataWord] using rd3875raw⟩
  have hsrcMask : transferFromSrcMaskedWord I = solcSourceWord I := by
    unfold transferFromSrcMaskedWord
    rw [transferFromSrcWord_of_push I hsel, u256_land_comm]
    exact solcAddrMask_clean (solcSourceWord_canonical I)
  have rd1411raw := evm_run rd3875 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨3886⟩ (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨1411⟩ (by native_decide) (by evm_ov)]
  have rd1411 := rd1411raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [hsrcMask] using rd1411⟩

theorem daiPushX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1034⟩ [daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.daiAddressUint256ExternalShort
    (entry := ⟨1034⟩) (ret := ⟨686⟩) (routine := ⟨3875⟩)
    hreach dai_address_uint256_external_entry_wf hsz4 hsize hshort

theorem daiPushFinish {cA gh bl σInit σFinal σ₀ A I} {g : Sat256}
    {scratch : ByteArray} {k C : ℕ}
    (h : RD daiBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3886⟩
      [⟨1⟩, transferFromWadWord I, transferFromDstMaskedWord I, ⟨686⟩, daiSelWord I]
      (solcScratchReturnMem scratch (transferFromWadWord I)) (UInt256.ofNat 5)
      ByteArray.empty (cA, σFinal) k C) :
    RDret daiBytecode g (initState cA gh bl σInit σ₀ g A I) (cA, σFinal)
      ByteArray.empty := by
  have rd686raw := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd686 := rd686raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd687 := rd686.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd687 (by native_decide) (by evm_ov)

theorem daiPushBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some pushTransition)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1034⟩ [daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := daiDecode_push_none_short (I := I) hsz4 hshort
  exact (daiPushX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- `push(address,uint256)` body refines its Solm transition. -/
theorem daiPushBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 14))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 14) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some pushTransition :=
    daiDispatchPush hsel
  have hreach := daiReachPushBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := daiDecode_push_ok (I := I) hsel hsz68
    obtain ⟨_, _, rd1411⟩ :=
      daiPushX_toTransferFrom (g := Sat256.ofUInt256 g) hsel hsz68 hsize hreach
    exact daiTransferFromInternalCallRuntimeCore
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (t := pushTransition) (callargs := pushStore I)
      (ret := ⟨3886⟩)
      (S := [transferFromWadWord I, transferFromDstMaskedWord I, ⟨686⟩, daiSelWord I])
      (out := ByteArray.empty)
      (retVal := none)
      hcode hdispatch hdecode hperm hwv
      (by simp only [List.length_cons, List.length_nil]; omega)
      (by jump_dest)
      hAccounts
      rd1411
      (by
        intro σ' scratch k' C' _hscratch _hread64 rd3886
        exact daiPushFinish (σInit := σ_evm) (σFinal := σ') rd3886)
      (by
        intro evmPost hcallee
        exact daiPushBodyReturns_from_transferFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) evmPost I
          hsel
          (by simp only [initState]; exact hwv)
          (by simp [initState])
          hcallee)
      (by
        intro hcallee
        exact daiPushBodyReverts_from_transferFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          hsel
          (by simp only [initState]; exact hwv)
          (by simp [initState])
          hcallee)
      (by
        simpa [pushTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by native_decide) (by native_decide)))
  · exact daiPushBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dai
