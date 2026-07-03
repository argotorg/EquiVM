import Benchmarks.Dss.Dai.TransferFrom

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and wrapper proof for `transfer(address,uint256)` -/

abbrev transferStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "dst" (transferFromDstValue I)).insert "wad" (transferFromWadValue I)

theorem transferStore_get_dst (I : ExecutionEnv) :
    (transferStore I).get? "dst" = some (transferFromDstValue I) := by
  unfold transferStore
  rw [store_get_ne
    (L := (∅ : Store).insert "dst" (transferFromDstValue I))
    (k := "wad") (a := "dst") (transferFromWadValue I) (by native_decide)]
  simp

theorem transferStore_get_wad (I : ExecutionEnv) :
    (transferStore I).get? "wad" = some (transferFromWadValue I) := by
  unfold transferStore
  simp

theorem transferStore_index_dst (I : ExecutionEnv) :
    (transferStore I)["dst"] = transferFromDstValue I := by
  unfold transferStore
  simp [Std.HashMap.getElem_insert]

theorem transferStore_index_wad (I : ExecutionEnv) :
    (transferStore I)["wad"] = transferFromWadValue I := by
  unfold transferStore
  simp [Std.HashMap.getElem_insert]

theorem daiDecode_transfer_ok {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 18)) (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata =
        some (transferStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["dst", "wad"] [addr, uint256]
    I.calldata = _
  unfold transferStore transferFromDstValue transferFromWadValue
  rw [transferFromDstWord_of_transfer I hsel, transferFromWadWord_of_transfer I hsel]
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["dst", "wad"]
      [abiAddress, abiUInt256] I.calldata =
    some (((∅ : Store).insert "dst"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "wad"
      (.int (Int.ofNat (calldataWord I.calldata 36).toNat)))
  exact decodeCalldata_legacyAddress_uint256_ok
    (cd := I.calldata) (x := "dst") (y := "wad") hsz68

theorem daiDecode_transfer_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["dst", "wad"] [addr, uint256]
    I.calldata = none
  simpa using decodeCalldata_legacyAddress_uint256_none_short
    (cd := I.calldata) (x := "dst") (y := "wad") hsz4 hshort

theorem daiLookupTransferFrom :
    lookupCallable? contract "transferFrom" = some transferFromTransition.toCallable := by
  rfl

theorem daiBindTransferFromStore (I : ExecutionEnv) :
    bindParams? transferFromTransition.params
        [transferFromSrcValue I, transferFromDstValue I, transferFromWadValue I] =
      some (transferFromCallStore I) := by
  exact daiBindTransferFromCallStore I

theorem evalExprs_transfer_internalCall (evm : EVM.State) (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 18))
    (hsrc : evm.executionEnv.source = I.source) :
    evalExprs? config { contract := contract, locals := transferStore I } evm
      [sender, .var "dst", .var "wad"] =
        .ok [transferFromSrcValue I, transferFromDstValue I, transferFromWadValue I] := by
  have hsrcVal : Value.address evm.executionEnv.source = transferFromSrcValue I := by
    unfold transferFromSrcValue
    rw [transferFromSrcWord_of_transfer I hsel, hsrc, solcSource_ofNat]
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure, sender,
    envValue, transferStore_index_dst, transferStore_index_wad, hsrcVal]

theorem daiTransferBodyReturns_from_transferFrom (evm evmPost : EVM.State) (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 18))
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcallee :
      ExecTransitionBody config contract evm (transferFromCallStore I) transferFromTransition.body
        (.returned { contract := contract, locals := transferFromCallStore I } evmPost
          (some [.bool true]))) :
    ∃ cs, ExecTransitionBody config contract evm (transferStore I) transferTransition.body
      (.returned cs evmPost (some [.bool true])) := by
  let caller : Frame := { contract := contract, locals := transferStore I }
  let callerAfter : Frame :=
    { contract := contract, locals := (transferStore I).insert "_ok" (.bool true) }
  have hcall : ExecStmt config caller evm
      (.internalCall "transferFrom" [sender, .var "dst", .var "wad"] "_ok")
      (.ok callerAfter evmPost) := by
    simpa [caller, callerAfter] using
      internalCallTransitionReturn (cfg := config)
        (caller := caller) (evm := evm) (calleeEvm := evmPost)
        (name := "transferFrom") (args := [sender, .var "dst", .var "wad"])
        (retVar := "_ok")
        (argVals := [transferFromSrcValue I, transferFromDstValue I, transferFromWadValue I])
        (callee := transferFromTransition) (locals := transferFromCallStore I)
        (calleeSolm := { contract := contract, locals := transferFromCallStore I })
        (value := .bool true)
        (evalExprs_transfer_internalCall evm I hsel hsrc)
        daiLookupTransferFrom
        (daiBindTransferFromStore I)
        hcallee
  have hret :
      evalExprs? config callerAfter evmPost [.var "_ok"] = .ok [.bool true] := by
    simp [callerAfter, evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  refine ⟨callerAfter, ExecFuncBody.execBlockRet ?_⟩
  rw [transferTransition]
  exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
    ExecBlock.consNormal hcall <|
      ExecBlock.consReturn (ExecStmt.return hret)

theorem daiTransferBodyReverts_from_transferFrom (evm : EVM.State) (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 18))
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hcallee :
      ExecTransitionBody config contract evm (transferFromCallStore I) transferFromTransition.body
        .reverted) :
    ExecTransitionBody config contract evm (transferStore I) transferTransition.body .reverted := by
  let caller : Frame := { contract := contract, locals := transferStore I }
  have hcall : ExecStmt config caller evm
      (.internalCall "transferFrom" [sender, .var "dst", .var "wad"] "_ok") .reverted := by
    exact internalCallTransitionRevert (cfg := config)
      (caller := caller) (evm := evm)
      (name := "transferFrom") (args := [sender, .var "dst", .var "wad"])
      (retVar := "_ok")
      (argVals := [transferFromSrcValue I, transferFromDstValue I, transferFromWadValue I])
      (callee := transferFromTransition) (locals := transferFromCallStore I)
      (evalExprs_transfer_internalCall evm I hsel hsrc)
      daiLookupTransferFrom
      (daiBindTransferFromStore I)
      hcallee
  rw [transferTransition]
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert hcall

theorem daiTransferX_toTransferFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsel : selIs I (daiSelBytes 18))
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨990⟩ [daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1411⟩
      [transferFromWadWord I, transferFromDstMaskedWord I, transferFromSrcMaskedWord I,
        ⟨3868⟩, ⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I, ⟨496⟩,
        daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1012⟩ := RD.daiAddressUint256ExternalLenOk
    (entry := ⟨990⟩) (ret := ⟨496⟩) (routine := ⟨3855⟩) hreach
    dai_address_uint256_external_entry_wf (by jump_dest) hsz68 hsize
  obtain ⟨_, _, rd3855raw⟩ := RD.daiAddressUint256ExternalMaskAndJumpMasked
    (entry := ⟨990⟩) (ret := ⟨496⟩) (routine := ⟨3855⟩)
    (R := [daiSelWord I])
    rd1012 dai_address_uint256_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  obtain ⟨_, _, rd3855⟩ :
      ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3855⟩
        [transferFromWadWord I, transferFromDstMaskedWord I, ⟨496⟩, daiSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [transferFromDstMaskedWord, transferFromDstWord_of_transfer I hsel,
        transferFromWadWord_of_transfer I hsel, calldataWord] using rd3855raw⟩
  have hsrcMask : transferFromSrcMaskedWord I = solcSourceWord I := by
    unfold transferFromSrcMaskedWord
    rw [transferFromSrcWord_of_transfer I hsel, u256_land_comm]
    exact solcAddrMask_clean (solcSourceWord_canonical I)
  have hwf : solcCallerTransferThunkWf daiBytecode ⟨3855⟩ ⟨3868⟩ ⟨1411⟩ := by
    unfold solcCallerTransferThunkWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, rd1411⟩ := RD.solcCallerTransferThunk
    (pc := ⟨3855⟩) (contPc := ⟨3868⟩) (routinePc := ⟨1411⟩)
    (ret := ⟨496⟩) (R := [daiSelWord I]) rd3855 hwf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [hsrcMask] using rd1411⟩

theorem daiTransferX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨990⟩ [daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.daiAddressUint256ExternalShort
    (entry := ⟨990⟩) (ret := ⟨496⟩) (routine := ⟨3855⟩)
    hreach dai_address_uint256_external_entry_wf hsz4 hsize hshort

theorem daiTransferFinish {cA gh bl σInit σFinal σ₀ A I} {g : Sat256}
    {scratch : ByteArray} {k C : ℕ}
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD daiBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3868⟩
      [⟨1⟩, ⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I, ⟨496⟩,
        daiSelWord I]
      (solcScratchReturnMem scratch (transferFromWadWord I)) (UInt256.ofNat 5)
      ByteArray.empty (cA, σFinal) k C) :
    RDret daiBytecode g (initState cA gh bl σInit σ₀ g A I) (cA, σFinal)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  have rd496raw := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd496 := rd496raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  have hretWf : solcReturnBoolFromMemWf daiBytecode ⟨496⟩ := by
    unfold solcReturnBoolFromMemWf
    repeat' first | apply And.intro | native_decide
  have hbool :
      UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ := by
    native_decide
  simpa [hbool, transferFromTailBoolReturnMem] using
    RD.solcReturnBoolFromMem rd496 hretWf
      (solcScratchReturnMem_mload64 (transferFromWadWord I) hscratch hread64)
      (by rfl)
      (transferFromTailBoolReturnMem_mload64 I hscratch hread64)
      (transferFromTailBoolReturnMem_read128 I hscratch)
      (by simp only [List.length_singleton]; omega)

theorem daiTransferBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some transferTransition)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨990⟩ [daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := daiDecode_transfer_none_short (I := I) hsz4 hshort
  exact (daiTransferX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- `transfer(address,uint256)` body refines its Solm transition. -/
theorem daiTransferBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 18))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 18) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some transferTransition :=
    daiDispatchTransfer hsel
  have hreach := daiReachTransferBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := daiDecode_transfer_ok (I := I) hsel hsz68
    obtain ⟨_, _, rd1411⟩ :=
      daiTransferX_toTransferFrom (g := Sat256.ofUInt256 g) hsel hsz68 hsize hreach
    exact daiTransferFromInternalCallRuntimeCore
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (t := transferTransition) (callargs := transferStore I)
      (ret := ⟨3868⟩)
      (S := [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I, ⟨496⟩,
        daiSelWord I])
      (out := UInt256.toByteArray (⟨1⟩ : UInt256))
      (retVal := some [.bool true])
      hcode hdispatch hdecode hperm hwv
      (by simp only [List.length_cons, List.length_nil]; omega)
      (by jump_dest)
      hAccounts
      rd1411
      (by
        intro σ' scratch k' C' hscratch hread64 rd3868
        exact daiTransferFinish (σInit := σ_evm) (σFinal := σ') hscratch hread64 rd3868)
      (by
        intro evmPost hcallee
        exact daiTransferBodyReturns_from_transferFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) evmPost I
          hsel
          (by simp only [initState]; exact hwv)
          (by simp [initState])
          hcallee)
      (by
        intro hcallee
        exact daiTransferBodyReverts_from_transferFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          hsel
          (by simp only [initState]; exact hwv)
          (by simp [initState])
          hcallee)
      (returnEquiv_of_encode
        (by simpa [boolTy] using boolTrueReturnEncoding))
  · exact daiTransferBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dai
