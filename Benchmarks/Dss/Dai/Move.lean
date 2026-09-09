import Benchmarks.Dss.Dai.TransferFrom

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

abbrev moveStore (I : ExecutionEnv) : Store :=
  transferFromStore I

theorem moveStore_index_src (I : ExecutionEnv) :
    (moveStore I)["src"] = transferFromSrcValue I := by
  unfold moveStore
  exact transferFromStore_index_src I

theorem moveStore_index_dst (I : ExecutionEnv) :
    (moveStore I)["dst"] = transferFromDstValue I := by
  unfold moveStore
  exact transferFromStore_index_dst I

theorem moveStore_index_wad (I : ExecutionEnv) :
    (moveStore I)["wad"] = transferFromWadValue I := by
  unfold moveStore transferFromStore
  simp [Std.HashMap.getElem_insert]

theorem daiLookupTransferFromForMove :
    lookupCallable? contract "transferFrom" = some transferFromTransition.toCallable := by
  rfl

theorem daiDecode_move_ok {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 8)) (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (moveTransition.params.map Param.name)
      (transitionSignature moveTransition).paramTypes I.calldata = some (moveStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["src", "dst", "wad"]
    [addr, addr, uint256] I.calldata = _
  unfold moveStore transferFromStore transferFromSrcValue transferFromDstValue
    transferFromWadValue
  rw [transferFromSrcWord_of_move I hsel, transferFromDstWord_of_move I hsel,
    transferFromWadWord_of_move I hsel]
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["src", "dst", "wad"]
      [abiAddress, abiAddress, abiUInt256] I.calldata =
    some ((((∅ : Store).insert "src"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "dst"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))).insert "wad"
      (.int (Int.ofNat (calldataWord I.calldata 68).toNat)))
  exact decodeCalldata_legacyAddress_legacyAddress_uint256_ok
    (cd := I.calldata) (x := "src") (y := "dst") (z := "wad") hsz100

theorem daiDecode_move_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (moveTransition.params.map Param.name)
      (transitionSignature moveTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["src", "dst", "wad"]
    [addr, addr, uint256] I.calldata = none
  simpa using decodeCalldata_legacyAddress_legacyAddress_uint256_none_short
    (cd := I.calldata) (x := "src") (y := "dst") (z := "wad") hsz4 hshort

theorem evalExprs_move_internalCall (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := moveStore I } evm
      [.var "src", .var "dst", .var "wad"] =
        .ok [transferFromSrcValue I, transferFromDstValue I, transferFromWadValue I] := by
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    moveStore_index_src, moveStore_index_dst, moveStore_index_wad]

theorem daiMoveBodyReturns_from_transferFrom (evm evmPost : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcallee :
      ExecTransitionBody config contract evm (transferFromCallStore I) transferFromTransition.body
        (.returned { contract := contract, locals := transferFromCallStore I } evmPost
          (some [.bool true]))) :
    ∃ cs, ExecTransitionBody config contract evm (moveStore I) moveTransition.body
      (.returned cs evmPost none) := by
  let caller : Frame := { contract := contract, locals := moveStore I }
  let callerAfter : Frame :=
    { contract := contract, locals := (moveStore I).insert "_ok" (.bool true) }
  have hcall : ExecStmt config caller evm
      (.internalCall "transferFrom" [.var "src", .var "dst", .var "wad"] "_ok")
      (.ok callerAfter evmPost) := by
    simpa [caller, callerAfter] using
      internalCallTransitionReturn (cfg := config)
        (caller := caller) (evm := evm) (calleeEvm := evmPost)
        (name := "transferFrom") (args := [.var "src", .var "dst", .var "wad"])
        (retVar := "_ok")
        (argVals := [transferFromSrcValue I, transferFromDstValue I, transferFromWadValue I])
        (callee := transferFromTransition) (locals := transferFromCallStore I)
        (calleeSolm := { contract := contract, locals := transferFromCallStore I })
        (value := .bool true)
        (evalExprs_move_internalCall evm I)
        daiLookupTransferFromForMove
        (daiBindTransferFromCallStore I)
        hcallee
  refine ⟨callerAfter, ExecFuncBody.execBlockOK ?_⟩
  rw [moveTransition]
  exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
    ExecBlock.consNormal hcall ExecBlock.nil

theorem daiMoveBodyReverts_from_transferFrom (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hcallee :
      ExecTransitionBody config contract evm (transferFromCallStore I) transferFromTransition.body
        .reverted) :
    ExecTransitionBody config contract evm (moveStore I) moveTransition.body .reverted := by
  let caller : Frame := { contract := contract, locals := moveStore I }
  have hcall : ExecStmt config caller evm
      (.internalCall "transferFrom" [.var "src", .var "dst", .var "wad"] "_ok") .reverted := by
    exact internalCallTransitionRevert (cfg := config)
      (caller := caller) (evm := evm)
      (name := "transferFrom") (args := [.var "src", .var "dst", .var "wad"])
      (retVar := "_ok")
      (argVals := [transferFromSrcValue I, transferFromDstValue I, transferFromWadValue I])
      (callee := transferFromTransition) (locals := transferFromCallStore I)
      (evalExprs_move_internalCall evm I)
      daiLookupTransferFromForMove
      (daiBindTransferFromCallStore I)
      hcallee
  rw [moveTransition]
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert hcall

theorem daiMoveX_toTransferFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsel : selIs I (daiSelBytes 8))
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1078⟩ [daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1411⟩
      [transferFromWadWord I, transferFromDstMaskedWord I, transferFromSrcMaskedWord I,
        ⟨3902⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨686⟩, daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1100⟩ := RD.daiAddressAddressUint256ExternalLenOk
    (entry := ⟨1078⟩) (ret := ⟨686⟩) (routine := ⟨3891⟩) hreach
    dai_address_address_uint256_external_entry_wf (by jump_dest) hsz100 hsize
  obtain ⟨_, _, rd3891raw⟩ := RD.daiAddressAddressUint256ExternalMaskAndJumpMasked
    (entry := ⟨1078⟩) (ret := ⟨686⟩) (routine := ⟨3891⟩)
    (R := [daiSelWord I])
    rd1100 dai_address_address_uint256_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  obtain ⟨_, _, rd3891⟩ :
      ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3891⟩
        [transferFromWadWord I, transferFromDstMaskedWord I, transferFromSrcMaskedWord I,
          ⟨686⟩, daiSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      rw [transferFromWadWord_of_move I hsel, transferFromDstMaskedWord,
        transferFromDstWord_of_move I hsel, transferFromSrcMaskedWord,
        transferFromSrcWord_of_move I hsel]
      simpa [calldataWord] using rd3891raw⟩
  have rd1411raw := evm_run rd3891 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨3902⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw push2 ⟨1411⟩ (by decide +native) (by evm_ov)]
  have rd1411 := rd1411raw.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact ⟨_, _, rd1411⟩

theorem daiMoveX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1078⟩ [daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.daiAddressAddressUint256ExternalShort
    (entry := ⟨1078⟩) (ret := ⟨686⟩) (routine := ⟨3891⟩)
    hreach dai_address_address_uint256_external_entry_wf hsz4 hsize hshort

theorem daiMoveFinish {cA gh bl σInit σFinal σ₀ A I} {g : Sat256}
    {scratch : ByteArray} {k C : ℕ}
    (h : RD daiBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3902⟩
      [⟨1⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨686⟩, daiSelWord I]
      (solcScratchReturnMem scratch (transferFromWadWord I)) (UInt256.ofNat 5)
      ByteArray.empty (cA, σFinal) k C) :
    RDret daiBytecode g (initState cA gh bl σInit σ₀ g A I) (cA, σFinal)
      ByteArray.empty := by
  have rd686raw := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  have rd686 := rd686raw.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd687 := rd686.jumpdest (by decide +native) (by evm_ov)
  exact RD.stop rd687 (by decide +native) (by evm_ov)

theorem daiMoveBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg contract I.calldata = some moveTransition)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1078⟩ [daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := daiDecode_move_none_short (I := I) hsz4 hshort
  exact (daiMoveX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- `move(address,address,uint256)` body refines its Solm transition. -/
theorem daiMoveBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 8))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 8) (by decide +native) hsel
  have hdispatch : dispatchMsg contract I.calldata = some moveTransition :=
    daiDispatchMove hsel
  have hreach := daiReachMoveBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have hdecode := daiDecode_move_ok (I := I) hsel hsz100
    obtain ⟨_, _, rd1411⟩ :=
      daiMoveX_toTransferFrom (g := Sat256.ofUInt256 g) hsel hsz100 hsize hreach
    exact daiTransferFromInternalCallRuntimeCore
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (t := moveTransition) (callargs := moveStore I)
      (ret := ⟨3902⟩)
      (S := [transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨686⟩, daiSelWord I])
      (out := ByteArray.empty)
      (retVal := none)
      hcode hdispatch hdecode hperm hwv
      (by simp only [List.length_cons, List.length_nil]; omega)
      (by jump_dest)
      hAccounts
      rd1411
      (by
        intro σ' scratch k' C' _hscratch _hread64 rd3902
        exact daiMoveFinish (σInit := σ_evm) (σFinal := σ') rd3902)
      (by
        intro evmPost hcallee
        exact daiMoveBodyReturns_from_transferFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) evmPost I
          (by simp only [initState]; exact hwv)
          hcallee)
      (by
        intro hcallee
        exact daiMoveBodyReverts_from_transferFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
          hcallee)
      (by
        simpa [moveTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl (by decide +native) (by decide +native)))
  · exact daiMoveBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dai
