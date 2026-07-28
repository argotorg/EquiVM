import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `out(bytes32,address)` nested mapping getter -/

abbrev endOutConcreteSelector : ByteArray := selectorBytes 0xc9 0x39 0xeb 0xfc
abbrev endOutUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36
abbrev endOutUsr (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (endOutUsrWord I).toNat
abbrev endOutUsrKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (endOutUsrWord I)
abbrev endOutLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "arg0" (endBytes32ArgValue I)).insert "arg1" (.address (endOutUsr I))
abbrev endOutEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "out",
    steps := [.mindex (endBytes32ArgKey I), .mindex (.address (endOutUsr I))] }
abbrev endOutSlotFor (I : ExecutionEnv) : UInt256 :=
  outSlot (endBytes32ArgKey I) (.address (endOutUsr I))

theorem endOutLocals_index_arg0 (I : ExecutionEnv) :
    (endOutLocals I)["arg0"] = endBytes32ArgValue I := by
  unfold endOutLocals
  rw [Std.HashMap.getElem_insert]
  simp

abbrev endOutHighSplitPc : UInt256 := ⟨43⟩
abbrev endOutHighJumpdestPc : UInt256 := ⟨162⟩
abbrev endOutMidSplitPc : UInt256 := ⟨163⟩
abbrev endOutFirstArmPc : UInt256 := ⟨174⟩
abbrev endOutEntryPc : UInt256 := ⟨1054⟩
abbrev endOutDecodedPc : UInt256 := ⟨1076⟩
abbrev endOutRoutinePc : UInt256 := ⟨8239⟩

theorem endOutSlotFor_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    endOutSlotFor I =
      solcMappingSlot (solcMappingSlot ⟨17⟩ (endBytes32ArgWord I)) (endOutUsrKey I) := by
  unfold endOutSlotFor outSlot outIlkSlot endOutUsr endOutUsrKey endOutUsrWord mapSlot
    solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]
  rw [endKeyValueToWord_bytes32ArgKey (I := I) (by omega)]

theorem endDecode_out_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (outTransition.params.map Param.name)
      (transitionSignature outTransition).paramTypes I.calldata =
        some (endOutLocals I) := by
  simpa [config, outTransition, endOutLocals, endBytes32ArgValue, endBytes32ArgBytes,
    endOutUsr, endOutUsrWord, bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width,
    abiAddress] using
    (endDecode_legacyBytes32_address_ok (cd := I.calldata) (x := "arg0")
      (y := "arg1") hsz68)

theorem endDecode_out_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (outTransition.params.map Param.name)
      (transitionSignature outTransition).paramTypes I.calldata = none := by
  simpa [config, outTransition, bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width,
    abiAddress] using
    (endDecode_legacyBytes32_address_none_short (cd := I.calldata) (x := "arg0")
      (y := "arg1") hsz4 hshort)

theorem endOutHighSplitWellFormed :
    selectorSplitWellFormed endBytecode endOutHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endOutMidSplitWellFormed :
    selectorSplitWellFormed endBytecode endOutMidSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem endOutArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode endOutFirstArmPc j) := by
  intro j hj
  interval_cases j
  all_goals
    dsimp [armWellFormed]
    repeat' first | apply And.intro | native_decide

theorem endReachOutBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endOutConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endOutEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xc939ebfc⟩ :=
    endSelWord_eq_of_beq I hsz 0xc9 0x39 0xeb 0xfc ⟨0xc939ebfc⟩
      (by native_decide) (by simpa [selIs, endOutConcreteSelector, selectorBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endOutHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [endRootSplitPc, endOutHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 endRootSplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have h162 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endOutHighJumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [endOutHighSplitPc, endOutHighJumpdestPc] using
      RD.selectorSplitTakenAuto h43 endOutHighSplitWellFormed
        (by rw [hword]; native_decide) (by jump_dest) (by simp)
  have h163 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endOutMidSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 1) (C32 + 22 + 22 + 1) := by
    simpa [endOutMidSplitPc] using h162.jumpdest (by native_decide) (by simp)
  have h174 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endOutFirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 1 + 5) (C32 + 22 + 22 + 1 + 22) := by
    simpa [endOutMidSplitPc, endOutFirstArmPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h163 endOutMidSplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endOutFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endOutFirstArmPc 3))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endOutEntryPc 3 h174
    (fun j hj => endOutArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endOutBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some outTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (outTransition.params.map Param.name)
        (transitionSignature outTransition).paramTypes I.calldata = some (endOutLocals I))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endOutEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let owner := endBytes32ArgWord I
  let spender := endOutUsrKey I
  let slot := solcMappingSlot (solcMappingSlot ⟨17⟩ owner) spender
  let locals := endOutLocals I
  have hslot : endOutSlotFor I = slot := by
    simp [slot, owner, spender, endOutSlotFor_eq hsz68]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals outTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (endSlotWord (endOutSlotFor I) σ_solm I).toNat))])) := by
    simpa [outTransition, endOutSlotFor, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, locals, endOutLocals, owner, spender] using
      endUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (ref := outRef (.var "arg0") (.var "arg1")) (er := endOutEvaledRef I)
        (slot := endOutSlotFor I)
        (by simp only [initState]; exact hwv) (by simp [locals, endOutLocals, outRef])
        (by
          have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
            have htlen : I.calldata.toList.length = I.calldata.size := by
              rw [byteArray_toList_eq, Array.length_toList]
              rfl
            rw [htlen]
            simp [bytes32Width]
            omega
          simp [endOutEvaledRef, endOutLocals, endBytes32ArgValue, endBytes32ArgKey,
            endOutUsr, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, outRef,
            evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind,
            locals, endOutLocals_index_arg0, hargLen])
        (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
        (by rfl)
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := endBytecode) (sel := sel) (entry := endOutEntryPc) (ret := endWordReturnPc)
    (decoded := endOutDecodedPc) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hlt
  obtain ⟨_, _, hroutine⟩ :
      ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endOutRoutinePc
        [spender, owner, endWordReturnPc, sel] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ_evm) k C := by
    have rd1077 := hdecoded.jumpdest (by native_decide) (by evm_ov)
    have rd1078 := rd1077.pop (by native_decide) (by evm_ov)
    have rd1079 := rd1078.dup1 (by native_decide) (by evm_ov)
    have rd1080 := rd1079.calldataload (by native_decide) (by evm_ov)
    have rd1081 := rd1080.swap1 (by native_decide) (by evm_ov)
    have rd1083 := rd1081.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    have rd1084 := rd1083.add (by native_decide) (by evm_ov)
    have rd1085 := rd1084.calldataload (by native_decide) (by evm_ov)
    have rd1087 := rd1085.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    have rd1089 := rd1087.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    have rd1091 := rd1089.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    have rd1092 := rd1091.shl (by native_decide) (by evm_ov)
    have rd1093 := rd1092.sub (by native_decide) (by evm_ov)
    have rd1094 := rd1093.and (by native_decide) (by evm_ov)
    have rd1097 := rd1094.push2 endOutRoutinePc (by native_decide) (by evm_ov)
    exact ⟨_, _, by
      simpa [owner, spender, endBytes32ArgWord, endOutUsrKey, endOutUsrWord, calldataWord,
        show (UInt256.add ⟨32⟩ ⟨4⟩) = ⟨36⟩ from by native_decide,
        show (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
          solcAddrMask from by native_decide,
        show (⟨4⟩ : UInt256).toNat = 4 from by decide,
        show (⟨36⟩ : UInt256).toNat = 36 from by decide]
        using rd1097.jump (by native_decide) (by jump_dest) (by evm_ov)⟩
  obtain ⟨_, _, hretPc⟩ := RD.solcNestedMappingGetter
    (code := endBytecode) (pc := endOutRoutinePc) (baseSlot := ⟨17⟩)
    (owner := owner) (spender := spender) (ret := endWordReturnPc) (R := [sel])
    hroutine
    (by
      unfold solcNestedMappingGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret endBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (endSlotWord slot σ_evm I)) := by
    have hret' := RD.solcReturnWordFromMem
      (pc := endWordReturnPc) (val := endSlotWord slot σ_evm I) (ret := endWordReturnPc)
      (R := [sel])
      (memout := solcScratchReturnMem (solcNestedMappingHashMem ⟨17⟩ owner spender)
        (endSlotWord slot σ_evm I))
      (by simpa [slot, endSlotWord] using hretPc)
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [slot] using solcNestedMappingHashMem_mload64 ⟨17⟩ owner spender)
      (by rfl)
      (by
        exact solcScratchReturnMem_mload64 (endSlotWord slot σ_evm I)
          (solcNestedMappingHashMem_size ⟨17⟩ owner spender)
          (solcNestedMappingHashMem_read64 ⟨17⟩ owner spender))
      (by
        exact solcScratchReturnMem_read128 (endSlotWord slot σ_evm I)
          (solcNestedMappingHashMem_size ⟨17⟩ owner spender))
      (by simp)
    simpa [slot, endSlotWord] using hret'
  have hword : endSlotWord slot σ_evm I = endSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (endSlotWord (endOutSlotFor I) σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (endSlotWord slot σ_evm I).toNat)] := by
    rw [hslot, hword]
  have henc :
      returnEquiv (UInt256.toByteArray (endSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (endSlotWord slot σ_evm I).toNat))])
        outTransition.returnType := by
    rw [show outTransition.returnType = [uint256] by rfl]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (endSlotWord slot σ_evm I))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem endOutBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some outTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endOutEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel) (entry := endOutEntryPc) (ret := endWordReturnPc)
    (decoded := endOutDecodedPc) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (endDecode_out_none_short hsz4 hshort)

theorem endOutBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf outTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endOutConcreteSelector := by
    simpa [endOutSelectorBytes, endOutConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endOutConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some outTransition :=
    endDispatchOut hsel
  have hreach := endReachOutBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz68 : 68 ≤ I.calldata.size
  · exact endOutBodyCoreOk hcode hwv hsz68 hsize hdispatch
      (endDecode_out_ok hsz68) hreach hAccounts
  · exact endOutBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
