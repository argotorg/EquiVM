import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `skip(bytes32,uint256)` transition -/

abbrev endSkipConcreteSelector : ByteArray := selectorBytes 0x50 0x3e 0xcf 0x06

abbrev endSkipIlkWord (I : ExecutionEnv) : UInt256 := endBytes32ArgWord I

abbrev endSkipIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev endSkipIdWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 36

abbrev endSkipStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "ilk" (.fixedBytes bytes32Width (endSkipIlkBytes I))).insert
    "id" (.int (Int.ofNat (endSkipIdWord I).toNat))

theorem endSkipStore_get_ilk (I : ExecutionEnv) :
    (endSkipStore I).get? "ilk" = some (.fixedBytes bytes32Width (endSkipIlkBytes I)) := by
  rw [endSkipStore, store_get_ne _ _ (by native_decide), store_get_self]

abbrev endSkipIlkKey (I : ExecutionEnv) : KeyValue := endBytes32ArgKey I

abbrev endSkipTagEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "tag", steps := [.mindex (endSkipIlkKey I)] }

abbrev endSkipTagSlot (I : ExecutionEnv) : UInt256 := tagSlot (endSkipIlkKey I)

abbrev endSkipTagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endSkipTagSlot I) σ I

abbrev endSkipEntryPc : UInt256 := ⟨672⟩
abbrev endSkipReturnPc : UInt256 := ⟨562⟩
abbrev endSkipDecodedPc : UInt256 := ⟨694⟩
abbrev endSkipBodyPc : UInt256 := ⟨3224⟩

theorem endSkipTagSlot_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    endSkipTagSlot I = solcMappingSlot ⟨12⟩ (endSkipIlkWord I) := by
  unfold endSkipTagSlot endSkipIlkKey tagSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem endDecode_skip_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (skipTransition.params.map Param.name)
      (transitionSignature skipTransition).paramTypes I.calldata = some (endSkipStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "id"] [bytes32, uint256]
    I.calldata = _
  simpa [config, skipTransition, bytes32, bytes32Width, uint256, uint256Int,
    endSkipStore, endSkipIlkBytes, endSkipIdWord, abiBytes32, abiBytes32Width,
    abiUInt256] using
    (endDecode_legacyBytes32_uint256_ok (cd := I.calldata) (x := "ilk")
      (y := "id") hsz68)

theorem endDecode_skip_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (skipTransition.params.map Param.name)
      (transitionSignature skipTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "id"] [bytes32, uint256]
    I.calldata = none
  simpa [config, skipTransition, bytes32, bytes32Width, uint256, uint256Int,
    abiBytes32, abiBytes32Width, abiUInt256] using
    (endDecode_legacyBytes32_uint256_none_short (cd := I.calldata) (x := "ilk")
      (y := "id") hsz4 hshort)

theorem endReachSkipBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endSkipConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endSkipEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x503ecf06⟩ :=
    endSelWord_eq_of_beq I hsz 0x50 0x3e 0xcf 0x06 ⟨0x503ecf06⟩
      (by native_decide)
      (by simpa [selIs, endSkipConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup403FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup403FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup403FirstArmPc 2))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endSkipEntryPc 2 hfirst
    (fun j hj => endGroup403ArmsWellFormed j (by omega))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem RD.endSkipDecodeToBody {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 endSkipDecodedPc (de :: ⟨4⟩ :: ret :: sel :: R)
        mem aw rdata acc k C)
    (hwf : code = endBytecode)
    (hroutine : (D_J code 0).contains endSkipBodyPc = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 endSkipBodyPc
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd694 := h.jumpdest (by native_decide) (by evm_ov)
  have rd695 := rd694.pop (by native_decide) (by evm_ov)
  have rd696 := rd695.dup1 (by native_decide) (by evm_ov)
  have rd697 := rd696.calldataload (by native_decide) (by evm_ov)
  have rd698 := rd697.swap1 (by native_decide) (by evm_ov)
  have rd700 := rd698.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd701 := rd700.add (by native_decide) (by evm_ov)
  have rd702 := rd701.calldataload (by native_decide) (by evm_ov)
  have rd703 := rd702.push2 endSkipBodyPc (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [endSkipBodyPc, endSkipDecodedPc, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd703.jump (by native_decide) hroutine (by evm_ov)⟩

theorem endSkipX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endSkipEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
        (initState cA gh bl σ σ₀ g A I) endSkipBodyPc
        [endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := endBytecode) (sel := sel)
    (entry := endSkipEntryPc) (ret := endSkipReturnPc)
    (decoded := endSkipDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.endSkipDecodeToBody
    (code := endBytecode) (ret := endSkipReturnPc) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endSkipIdWord, endSkipIlkWord] using hroutine⟩

theorem endSkipX_tagZero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkipTagWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endSkipBodyPc
      [endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let key := endSkipIlkWord I
  have hslot : endSkipTagSlot I = solcMappingSlot ⟨12⟩ key := by
    simpa [key] using endSkipTagSlot_eq (I := I) hsz68
  have rd3229pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3230 := rd3229pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3234pre := evm_run rd3230 with [
    raw push1 ⟨12⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd3235 := rd3234pre.mstore 0 (twoWordHashMem key ⟨12⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3238pre := evm_run rd3235 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨12⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨12⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨12⟩ key solcFreePtrMem_size
  have rd3239pre := rd3238pre.keccak256 0 (solcMappingSlot ⟨12⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3240raw⟩ := rd3239pre.sload (by native_decide) (by evm_ov)
  have htagRaw :
      solcSlotWord σ I (solcMappingSlot ⟨12⟩ key) = ⟨0⟩ := by
    rw [← hslot]
    simpa [key, endSkipTagWord, endSlotWord] using htag
  have htagRaw' :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun ac => ac.storage.findD (solcMappingSlot ⟨12⟩ key) ⟨0⟩)) = ⟨0⟩ := by
    simpa [solcSlotWord] using htagRaw
  have rd3240zero := rd3240raw
  rw [htagRaw'] at rd3240zero
  obtain ⟨_, _, rd3240⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3240⟩
        (⟨0⟩ :: endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSkipBodyPc, key] using rd3240zero⟩
  have rd3243pre := rd3240.push2 ⟨3314⟩ (by native_decide) (by evm_ov)
  have rd3244pre := rd3243pre.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  obtain ⟨_, _, rd3244⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3244⟩
        [endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel]
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd3244pre⟩
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3244⟩) (len := ⟨23⟩)
    (rawWord := ⟨1662547331793263672767660296024730882676930893819124057⟩)
    (shift := ⟨74⟩)
    (word := UInt256.shiftLeft
      ⟨1662547331793263672767660296024730882676930893819124057⟩ ⟨74⟩)
    (op := .PUSH23) (width := 23)
    rd3244
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl
    (twoWordHashMem_size_96 key ⟨12⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 key ⟨12⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem evalExpr_endSkip_ilk (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endSkipStore I } evm (.var "ilk") =
      .ok (.fixedBytes bytes32Width (endSkipIlkBytes I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((endSkipStore I).get? "ilk") =
    .ok (.fixedBytes bytes32Width (endSkipIlkBytes I))
  rw [endSkipStore_get_ilk]
  rfl

theorem evalStorageRef_endSkip_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := endSkipStore I } evm
      (tagRef (.var "ilk")) = .ok (endSkipTagEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  have hilk := evalExpr_endSkip_ilk evm I
  simp [endSkipTagEvaledRef, endSkipIlkKey, hilk, endSkipIlkBytes,
    endBytes32ArgKey, endBytes32ArgBytes, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, tagRef, valueToKey?, EvalResult.ofOption, EvalResult.bind,
    pure, bind]
  rw [if_pos hargLen]

theorem evalExpr_endSkip_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endSkipStore I } evm
      (.storage (tagRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endSkipTagSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := endSkipStore I })
    (slot := tagRef (.var "ilk"))
    (er := endSkipTagEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endSkipTagSlot I))
    (hbase := by simp [endSkipStore, tagRef])
    (her := evalStorageRef_endSkip_tag evm I hsz68)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endSkipTagSlot I))

theorem evalExpr_endSkip_tag_ne_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkipTagSlot I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSkipStore I } evm
      (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm
        (.storage (tagRef (.var "ilk"))) = .ok (.int 0) := by
    simpa [htag] using evalExpr_endSkip_tag evm I hsz68
  have hzero :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact endEvalExpr_ne_int_false hstorage hzero rfl

theorem endSkipBodyReverts_tagZero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkipTagWord σ I = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSkipStore I) skipTransition.body .reverted := by
  intro evm0
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endSkipTagSlot I) = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSkipTagWord, endSlotWord, solcSlotWord] using htag
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm0
        (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endSkip_tag_ne_false evm0 I hsz68 htagLoad
  refine ExecFuncBody.execBlockRevert ?_
  simpa [skipTransition, nonpayable, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := endSkipStore I })
      (evm := evm0)
      (guard := .binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0))
      (rest :=
        checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
          "catIlk" ++
        [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"] "flipBid"
          (perm := false) ++
        [ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
          .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
          .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
          .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ] ++
        checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck1" ++
        checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, thisAddr, .var "bid"] "_suck2" ++
        checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0) [.var "flip"]
          "_hope" ++
        checkedExternalCallStmts (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank" ++
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ] ++
        checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", .var "usr", thisAddr, vowAddr, asInt256 (.var "lot"),
            asInt256 (.var "art")] "_grab")
      (by simp only [evm0, initState]; exact hwv)
      hguard

theorem endSkipX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endSkipEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel)
    (entry := endSkipEntryPc) (ret := endSkipReturnPc)
    (decoded := endSkipDecodedPc) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endSkipBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some skipTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endSkipEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endSkipX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (endDecode_skip_none_short hsz4 hshort)

theorem endSkipBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf skipTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endSkipConcreteSelector := by
    simpa [endSkipSelectorBytes, endSkipConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endSkipConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some skipTransition :=
    endDispatchSkip hsel
  have hreach := endReachSkipBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := endDecode_skip_ok (I := I) hsz68
    obtain ⟨_, _, hbodyReach⟩ :=
      endSkipX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have htagCouple : endSkipTagWord σ_evm I = endSkipTagWord σ_solm I := by
      simpa [endSkipTagWord, endSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (endSkipTagSlot I) ⟨0⟩
    by_cases htag : endSkipTagWord σ_evm I = ⟨0⟩
    · have htagSolm : endSkipTagWord σ_solm I = ⟨0⟩ := by
        rw [← htagCouple]
        exact htag
      have hbody :
          ExecTransitionBody config contract evmSolm (endSkipStore I)
            skipTransition.body .reverted := by
        simpa [evmSolm] using
          endSkipBodyReverts_tagZero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hsz68 htagSolm
      exact (endSkipX_tagZero (g := Sat256.ofUInt256 g) hsz68 htag hbodyReach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · sorry
  · exact endSkipBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
