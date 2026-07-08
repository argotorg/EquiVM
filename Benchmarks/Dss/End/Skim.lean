import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `skim(bytes32,address)` transition -/

abbrev endSkimConcreteSelector : ByteArray := selectorBytes 0x89 0xea 0x45 0xd3

abbrev endSkimIlkWord (I : ExecutionEnv) : UInt256 := endBytes32ArgWord I

abbrev endSkimIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev endSkimUrnWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev endSkimUrnKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (endSkimUrnWord I)

abbrev endSkimUrnAddr (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (endSkimUrnWord I).toNat

abbrev endSkimStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "ilk" (.fixedBytes bytes32Width (endSkimIlkBytes I))).insert
    "urn" (.address (endSkimUrnAddr I))

theorem endSkimStore_get_ilk (I : ExecutionEnv) :
    (endSkimStore I).get? "ilk" = some (.fixedBytes bytes32Width (endSkimIlkBytes I)) := by
  rw [endSkimStore, store_get_ne _ _ (by native_decide), store_get_self]

abbrev endSkimIlkKey (I : ExecutionEnv) : KeyValue := endBytes32ArgKey I

abbrev endSkimTagEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "tag", steps := [.mindex (endSkimIlkKey I)] }

abbrev endSkimTagSlot (I : ExecutionEnv) : UInt256 := tagSlot (endSkimIlkKey I)

abbrev endSkimTagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endSkimTagSlot I) σ I

abbrev endSkimEntryPc : UInt256 := ⟨851⟩
abbrev endSkimReturnPc : UInt256 := ⟨562⟩
abbrev endSkimDecodedPc : UInt256 := ⟨873⟩
abbrev endSkimBodyPc : UInt256 := ⟨6705⟩

theorem endSkimTagSlot_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    endSkimTagSlot I = solcMappingSlot ⟨12⟩ (endSkimIlkWord I) := by
  unfold endSkimTagSlot endSkimIlkKey tagSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem endDecode_skim_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
      (transitionSignature skimTransition).paramTypes I.calldata = some (endSkimStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "urn"] [bytes32, addr]
    I.calldata = _
  simpa [config, skimTransition, bytes32, bytes32Width, addr, endSkimStore,
    endSkimIlkBytes, endSkimUrnAddr, endSkimUrnWord, abiBytes32, abiBytes32Width,
    abiAddress] using
    (endDecode_legacyBytes32_address_ok (cd := I.calldata) (x := "ilk")
      (y := "urn") hsz68)

theorem endDecode_skim_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
      (transitionSignature skimTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "urn"] [bytes32, addr]
    I.calldata = none
  simpa [config, skimTransition, bytes32, bytes32Width, addr, abiBytes32,
    abiBytes32Width, abiAddress] using
    (endDecode_legacyBytes32_address_none_short (cd := I.calldata) (x := "ilk")
      (y := "urn") hsz4 hshort)

theorem endReachSkimBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endSkimConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endSkimEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x89ea45d3⟩ :=
    endSelWord_eq_of_beq I hsz 0x89 0xea 0x45 0xd3 ⟨0x89ea45d3⟩
      (by native_decide)
      (by simpa [selIs, endSkimConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup223FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup223FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup223FirstArmPc 0))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endSkimEntryPc 0 hfirst
    (fun j hj => endGroup223ArmsWellFormed j (by omega))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem RD.endSkimDecodeToBody {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 endSkimDecodedPc (de :: ⟨4⟩ :: ret :: sel :: R)
        mem aw rdata acc k C)
    (hwf : code = endBytecode)
    (hroutine : (D_J code 0).contains endSkimBodyPc = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 endSkimBodyPc
      (endSkimUrnKey ee :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd873 := h.jumpdest (by native_decide) (by evm_ov)
  have rd874 := rd873.pop (by native_decide) (by evm_ov)
  have rd875 := rd874.dup1 (by native_decide) (by evm_ov)
  have rd876 := rd875.calldataload (by native_decide) (by evm_ov)
  have rd877 := rd876.swap1 (by native_decide) (by evm_ov)
  have rd879 := rd877.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd880 := rd879.add (by native_decide) (by evm_ov)
  have rd881 := rd880.calldataload (by native_decide) (by evm_ov)
  have rd883 := rd881.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd885 := rd883.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd887 := rd885.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd888 := rd887.shl (by native_decide) (by evm_ov)
  have rd889 := rd888.sub (by native_decide) (by evm_ov)
  have rd890 := rd889.and (by native_decide) (by evm_ov)
  have rd891 := rd890.push2 endSkimBodyPc (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [endSkimBodyPc, endSkimDecodedPc, endSkimUrnKey, endSkimUrnWord,
      calldataWord,
      show (UInt256.add ⟨32⟩ ⟨4⟩) = ⟨36⟩ from by native_decide,
      show (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        solcAddrMask from by native_decide,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd891.jump (by native_decide) hroutine (by evm_ov)⟩

theorem endSkimX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endSkimEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
        (initState cA gh bl σ σ₀ g A I) endSkimBodyPc
        [endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := endBytecode) (sel := sel)
    (entry := endSkimEntryPc) (ret := endSkimReturnPc)
    (decoded := endSkimDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.endSkimDecodeToBody
    (code := endBytecode) (ret := endSkimReturnPc) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endSkimUrnKey, endSkimUrnWord, endSkimIlkWord] using hroutine⟩

theorem endSkimX_tagZero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkimTagWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endSkimBodyPc
      [endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let key := endSkimIlkWord I
  have hslot : endSkimTagSlot I = solcMappingSlot ⟨12⟩ key := by
    simpa [key] using endSkimTagSlot_eq (I := I) hsz68
  have rd6710pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6711 := rd6710pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6715pre := evm_run rd6711 with [
    raw push1 ⟨12⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd6716 := rd6715pre.mstore 0 (twoWordHashMem key ⟨12⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6719pre := evm_run rd6716 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨12⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨12⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨12⟩ key solcFreePtrMem_size
  have rd6720pre := rd6719pre.keccak256 0 (solcMappingSlot ⟨12⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd6721raw⟩ := rd6720pre.sload (by native_decide) (by evm_ov)
  have htagRaw :
      solcSlotWord σ I (solcMappingSlot ⟨12⟩ key) = ⟨0⟩ := by
    rw [← hslot]
    simpa [key, endSkimTagWord, endSlotWord] using htag
  have htagRaw' :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun ac => ac.storage.findD (solcMappingSlot ⟨12⟩ key) ⟨0⟩)) = ⟨0⟩ := by
    simpa [solcSlotWord] using htagRaw
  have rd6721zero := rd6721raw
  rw [htagRaw'] at rd6721zero
  obtain ⟨_, _, rd6721⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6721⟩
        (⟨0⟩ :: endSkimUrnKey I :: endSkimIlkWord I :: endSkimReturnPc :: sel :: [])
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSkimBodyPc, key] using rd6721zero⟩
  have rd6724pre := rd6721.push2 ⟨6795⟩ (by native_decide) (by evm_ov)
  have rd6725pre := rd6724pre.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  obtain ⟨_, _, rd6725⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6725⟩
        [endSkimUrnKey I, endSkimIlkWord I, endSkimReturnPc, sel]
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd6725pre⟩
  exact RD.solcErrorStringRevertTail
    (pc := ⟨6725⟩) (len := ⟨23⟩)
    (rawWord := ⟨1662547331793263672767660296024730882676930893819124057⟩)
    (shift := ⟨74⟩)
    (word := UInt256.shiftLeft
      ⟨1662547331793263672767660296024730882676930893819124057⟩ ⟨74⟩)
    (op := .PUSH23) (width := 23)
    rd6725
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl
    (twoWordHashMem_size_96 key ⟨12⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 key ⟨12⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem evalExpr_endSkim_ilk (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endSkimStore I } evm (.var "ilk") =
      .ok (.fixedBytes bytes32Width (endSkimIlkBytes I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((endSkimStore I).get? "ilk") =
    .ok (.fixedBytes bytes32Width (endSkimIlkBytes I))
  rw [endSkimStore_get_ilk]
  rfl

theorem evalStorageRef_endSkim_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := endSkimStore I } evm
      (tagRef (.var "ilk")) = .ok (endSkimTagEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  have hilk := evalExpr_endSkim_ilk evm I
  simp [endSkimTagEvaledRef, endSkimIlkKey, hilk, endSkimIlkBytes,
    endBytes32ArgKey, endBytes32ArgBytes, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, tagRef, valueToKey?, EvalResult.ofOption, EvalResult.bind,
    pure, bind]
  rw [if_pos hargLen]

theorem evalExpr_endSkim_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endSkimStore I } evm
      (.storage (tagRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endSkimTagSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := endSkimStore I })
    (slot := tagRef (.var "ilk"))
    (er := endSkimTagEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endSkimTagSlot I))
    (hbase := by simp [endSkimStore, tagRef])
    (her := evalStorageRef_endSkim_tag evm I hsz68)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endSkimTagSlot I))

theorem evalExpr_endSkim_tag_ne_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkimTagSlot I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSkimStore I } evm
      (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm
        (.storage (tagRef (.var "ilk"))) = .ok (.int 0) := by
    simpa [htag] using evalExpr_endSkim_tag evm I hsz68
  have hzero :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact endEvalExpr_ne_int_false hstorage hzero rfl

theorem endSkimBodyReverts_tagZero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkimTagWord σ I = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSkimStore I) skimTransition.body .reverted := by
  intro evm0
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endSkimTagSlot I) = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSkimTagWord, endSlotWord, solcSlotWord] using htag
  have hguard :
      evalExpr? config { contract := contract, locals := endSkimStore I } evm0
        (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endSkim_tag_ne_false evm0 I hsz68 htagLoad
  refine ExecFuncBody.execBlockRevert ?_
  simpa [skimTransition, nonpayable, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := endSkimStore I })
      (evm := evm0)
      (guard := .binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0))
      (rest :=
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
          [.var "ilk", .var "urn"] "vatUrn" ++
        [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
          .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
          .internalCall "rmul" [.var "art", .var "rate"] "owe0",
          .internalCall "rmul" [.var "owe0", .storage (tagRef (.var "ilk"))] "owe",
          .internalCall "min" [.var "ink", .var "owe"] "wad",
          .internalCall "sub" [.var "owe", .var "wad"] "diff",
          .internalCall "add" [.storage (gapRef (.var "ilk")), .var "diff"] "gapNew",
          .assign .storage (gapRef (.var "ilk")) (.var "gapNew"),
          .require
            (.binary .and
              (.binary .le (.var "wad") (.intLit int256Limit))
              (.binary .le (.var "art") (.intLit int256Limit))) ] ++
        checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", .var "urn", thisAddr, vowAddr,
           .unary .neg (asInt256 (.var "wad")), .unary .neg (asInt256 (.var "art"))]
          "_grab")
      (by simp only [evm0, initState]; exact hwv)
      hguard

theorem endSkimX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endSkimEntryPc [sel]
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
    (entry := endSkimEntryPc) (ret := endSkimReturnPc)
    (decoded := endSkimDecodedPc) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endSkimBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endSkimEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endSkimX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (endDecode_skim_none_short hsz4 hshort)

theorem endSkimBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf skimTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endSkimConcreteSelector := by
    simpa [endSkimSelectorBytes, endSkimConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endSkimConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some skimTransition :=
    endDispatchSkim hsel
  have hreach := endReachSkimBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := endDecode_skim_ok (I := I) hsz68
    obtain ⟨_, _, hbodyReach⟩ :=
      endSkimX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have htagCouple : endSkimTagWord σ_evm I = endSkimTagWord σ_solm I := by
      simpa [endSkimTagWord, endSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (endSkimTagSlot I) ⟨0⟩
    by_cases htag : endSkimTagWord σ_evm I = ⟨0⟩
    · have htagSolm : endSkimTagWord σ_solm I = ⟨0⟩ := by
        rw [← htagCouple]
        exact htag
      have hbody :
          ExecTransitionBody config contract evmSolm (endSkimStore I)
            skimTransition.body .reverted := by
        simpa [evmSolm] using
          endSkimBodyReverts_tagZero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hsz68 htagSolm
      exact (endSkimX_tagZero (g := Sat256.ofUInt256 g) hsz68 htag hbodyReach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · sorry
  · exact endSkimBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
