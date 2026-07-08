import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `snip(bytes32,uint256)` transition -/

abbrev endSnipConcreteSelector : ByteArray := selectorBytes 0x38 0xc6 0xde 0x40

abbrev endSnipIlkWord (I : ExecutionEnv) : UInt256 := endBytes32ArgWord I

abbrev endSnipIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev endSnipIdWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 36

abbrev endSnipStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "ilk" (.fixedBytes bytes32Width (endSnipIlkBytes I))).insert
    "id" (.int (Int.ofNat (endSnipIdWord I).toNat))

theorem endSnipStore_get_ilk (I : ExecutionEnv) :
    (endSnipStore I).get? "ilk" = some (.fixedBytes bytes32Width (endSnipIlkBytes I)) := by
  rw [endSnipStore, store_get_ne _ _ (by native_decide), store_get_self]

abbrev endSnipIlkKey (I : ExecutionEnv) : KeyValue := endBytes32ArgKey I

abbrev endSnipTagEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "tag", steps := [.mindex (endSnipIlkKey I)] }

abbrev endSnipTagSlot (I : ExecutionEnv) : UInt256 := tagSlot (endSnipIlkKey I)

abbrev endSnipTagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endSnipTagSlot I) σ I

abbrev endSnipEntryPc : UInt256 := ⟨600⟩
abbrev endSnipReturnPc : UInt256 := ⟨562⟩
abbrev endSnipDecodedPc : UInt256 := ⟨622⟩
abbrev endSnipBodyPc : UInt256 := ⟨1649⟩

theorem endSnipTagSlot_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    endSnipTagSlot I = solcMappingSlot ⟨12⟩ (endSnipIlkWord I) := by
  unfold endSnipTagSlot endSnipIlkKey tagSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem endDecode_snip_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (snipTransition.params.map Param.name)
      (transitionSignature snipTransition).paramTypes I.calldata = some (endSnipStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "id"] [bytes32, uint256]
    I.calldata = _
  simpa [config, snipTransition, bytes32, bytes32Width, uint256, uint256Int,
    endSnipStore, endSnipIlkBytes, endSnipIdWord, abiBytes32, abiBytes32Width,
    abiUInt256] using
    (endDecode_legacyBytes32_uint256_ok (cd := I.calldata) (x := "ilk")
      (y := "id") hsz68)

theorem endDecode_snip_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (snipTransition.params.map Param.name)
      (transitionSignature snipTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "id"] [bytes32, uint256]
    I.calldata = none
  simpa [config, snipTransition, bytes32, bytes32Width, uint256, uint256Int,
    abiBytes32, abiBytes32Width, abiUInt256] using
    (endDecode_legacyBytes32_uint256_none_short (cd := I.calldata) (x := "ilk")
      (y := "id") hsz4 hshort)

theorem endReachSnipBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endSnipConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endSnipEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x38c6de40⟩ :=
    endSelWord_eq_of_beq I hsz 0x38 0xc6 0xde 0x40 ⟨0x38c6de40⟩
      (by native_decide)
      (by simpa [selIs, endSnipConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachDebtFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endDebtFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endDebtFirstArmPc 3))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endSnipEntryPc 3 hfirst
    (fun j hj => endGroup452ArmsWellFormed j (by omega))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem RD.endSnipDecodeToBody {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 endSnipDecodedPc (de :: ⟨4⟩ :: ret :: sel :: R)
        mem aw rdata acc k C)
    (hwf : code = endBytecode)
    (hroutine : (D_J code 0).contains endSnipBodyPc = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 endSnipBodyPc
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd622 := h.jumpdest (by native_decide) (by evm_ov)
  have rd623 := rd622.pop (by native_decide) (by evm_ov)
  have rd624 := rd623.dup1 (by native_decide) (by evm_ov)
  have rd625 := rd624.calldataload (by native_decide) (by evm_ov)
  have rd626 := rd625.swap1 (by native_decide) (by evm_ov)
  have rd628 := rd626.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd629 := rd628.add (by native_decide) (by evm_ov)
  have rd630 := rd629.calldataload (by native_decide) (by evm_ov)
  have rd631 := rd630.push2 endSnipBodyPc (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [endSnipBodyPc, endSnipDecodedPc, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd631.jump (by native_decide) hroutine (by evm_ov)⟩

theorem endSnipX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endSnipEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
        (initState cA gh bl σ σ₀ g A I) endSnipBodyPc
        [endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := endBytecode) (sel := sel)
    (entry := endSnipEntryPc) (ret := endSnipReturnPc)
    (decoded := endSnipDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.endSnipDecodeToBody
    (code := endBytecode) (ret := endSnipReturnPc) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endSnipIdWord, endSnipIlkWord] using hroutine⟩

theorem endSnipX_tagZero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSnipTagWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endSnipBodyPc
      [endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let key := endSnipIlkWord I
  have hslot : endSnipTagSlot I = solcMappingSlot ⟨12⟩ key := by
    simpa [key] using endSnipTagSlot_eq (I := I) hsz68
  have rd1654pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1655 := rd1654pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1659pre := evm_run rd1655 with [
    raw push1 ⟨12⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd1660 := rd1659pre.mstore 0 (twoWordHashMem key ⟨12⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1663pre := evm_run rd1660 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨12⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨12⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨12⟩ key solcFreePtrMem_size
  have rd1664pre := rd1663pre.keccak256 0 (solcMappingSlot ⟨12⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1665raw⟩ := rd1664pre.sload (by native_decide) (by evm_ov)
  have htagRaw :
      solcSlotWord σ I (solcMappingSlot ⟨12⟩ key) = ⟨0⟩ := by
    rw [← hslot]
    simpa [key, endSnipTagWord, endSlotWord] using htag
  have htagRaw' :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun ac => ac.storage.findD (solcMappingSlot ⟨12⟩ key) ⟨0⟩)) = ⟨0⟩ := by
    simpa [solcSlotWord] using htagRaw
  have rd1665zero := rd1665raw
  rw [htagRaw'] at rd1665zero
  obtain ⟨_, _, rd1665⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1665⟩
        (⟨0⟩ :: endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSnipBodyPc, key] using rd1665zero⟩
  have rd1668pre := rd1665.push2 ⟨1739⟩ (by native_decide) (by evm_ov)
  have rd1669pre := rd1668pre.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  obtain ⟨_, _, rd1669⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1669⟩
        [endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, sel]
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd1669pre⟩
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1669⟩) (len := ⟨23⟩)
    (rawWord := ⟨1662547331793263672767660296024730882676930893819124057⟩)
    (shift := ⟨74⟩)
    (word := UInt256.shiftLeft
      ⟨1662547331793263672767660296024730882676930893819124057⟩ ⟨74⟩)
    (op := .PUSH23) (width := 23)
    rd1669
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl
    (twoWordHashMem_size_96 key ⟨12⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 key ⟨12⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem evalExpr_endSnip_ilk (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endSnipStore I } evm (.var "ilk") =
      .ok (.fixedBytes bytes32Width (endSnipIlkBytes I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((endSnipStore I).get? "ilk") =
    .ok (.fixedBytes bytes32Width (endSnipIlkBytes I))
  rw [endSnipStore_get_ilk]
  rfl

theorem evalStorageRef_endSnip_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := endSnipStore I } evm
      (tagRef (.var "ilk")) = .ok (endSnipTagEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  have hilk := evalExpr_endSnip_ilk evm I
  simp [endSnipTagEvaledRef, endSnipIlkKey, hilk, endSnipIlkBytes,
    endBytes32ArgKey, endBytes32ArgBytes, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, tagRef, valueToKey?, EvalResult.ofOption, EvalResult.bind,
    pure, bind]
  rw [if_pos hargLen]

theorem evalExpr_endSnip_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endSnipStore I } evm
      (.storage (tagRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endSnipTagSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := endSnipStore I })
    (slot := tagRef (.var "ilk"))
    (er := endSnipTagEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endSnipTagSlot I))
    (hbase := by simp [endSnipStore, tagRef])
    (her := evalStorageRef_endSnip_tag evm I hsz68)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endSnipTagSlot I))

theorem evalExpr_endSnip_tag_ne_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSnipTagSlot I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSnipStore I } evm
      (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm
        (.storage (tagRef (.var "ilk"))) = .ok (.int 0) := by
    simpa [htag] using evalExpr_endSnip_tag evm I hsz68
  have hzero :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact endEvalExpr_ne_int_false hstorage hzero rfl

theorem endSnipBodyReverts_tagZero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSnipTagWord σ I = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSnipStore I) snipTransition.body .reverted := by
  intro evm0
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endSnipTagSlot I) = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSnipTagWord, endSlotWord, solcSlotWord] using htag
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm0
        (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endSnip_tag_ne_false evm0 I hsz68 htagLoad
  refine ExecFuncBody.execBlockRevert ?_
  simpa [snipTransition, nonpayable, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := endSnipStore I })
      (evm := evm0)
      (guard := .binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0))
      (rest :=
        checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
          "dogIlk" ++
        [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"] "clipSale"
          (perm := false) ++
        [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
          .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
          .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ] ++
        checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck" ++
        checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
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

theorem endSnipX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endSnipEntryPc [sel]
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
    (entry := endSnipEntryPc) (ret := endSnipReturnPc)
    (decoded := endSnipDecodedPc) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endSnipBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some snipTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endSnipEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endSnipX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (endDecode_snip_none_short hsz4 hshort)

theorem endSnipBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf snipTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endSnipConcreteSelector := by
    simpa [endSnipSelectorBytes, endSnipConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endSnipConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some snipTransition :=
    endDispatchSnip hsel
  have hreach := endReachSnipBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := endDecode_snip_ok (I := I) hsz68
    obtain ⟨_, _, hbodyReach⟩ :=
      endSnipX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have htagCouple : endSnipTagWord σ_evm I = endSnipTagWord σ_solm I := by
      simpa [endSnipTagWord, endSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (endSnipTagSlot I) ⟨0⟩
    by_cases htag : endSnipTagWord σ_evm I = ⟨0⟩
    · have htagSolm : endSnipTagWord σ_solm I = ⟨0⟩ := by
        rw [← htagCouple]
        exact htag
      have hbody :
          ExecTransitionBody config contract evmSolm (endSnipStore I)
            snipTransition.body .reverted := by
        simpa [evmSolm] using
          endSnipBodyReverts_tagZero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hsz68 htagSolm
      exact (endSnipX_tagZero (g := Sat256.ofUInt256 g) hsz68 htag hbodyReach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · sorry
  · exact endSnipBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
