import Benchmarks.Dss.Vat.Gem

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vat

/-! ## `urns(bytes32,address)` nested struct mapping getter -/

abbrev urnsIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev urnsUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev urnsUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (urnsUsrWord I)

abbrev urnsIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev urnsUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (urnsUsrWord I).toNat)

abbrev urnsIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev urnsUsrKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (urnsUsrWord I).toNat)

abbrev urnsStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "arg0" (urnsIlkValue I)).insert "arg1" (urnsUsrValue I)

theorem urnsStore_index_arg0 (I : ExecutionEnv) :
    (urnsStore I)["arg0"] = urnsIlkValue I := by
  unfold urnsStore
  rw [Std.HashMap.getElem_insert]
  simp

def urnsInkStorageSlot (I : ExecutionEnv) : UInt256 :=
  urnsBase (urnsIlkKey I) (urnsUsrKey I)

def urnsArtStorageSlot (I : ExecutionEnv) : UInt256 :=
  urnsInkStorageSlot I + ⟨1⟩

abbrev urnsInkEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "urns", steps := [.mindex (urnsIlkKey I), .mindex (urnsUsrKey I), .field "ink"] }

abbrev urnsArtEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "urns", steps := [.mindex (urnsIlkKey I), .mindex (urnsUsrKey I), .field "art"] }

theorem urnsIlkKeyWord_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (urnsIlkKey I) = urnsIlkWord I := by
  unfold urnsIlkKey urnsIlkWord calldataWord
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : (List.take 32 (List.drop 4 I.calldata.toList)).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      uInt256OfByteArray (I.calldata.readBytes 4 32) :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  simp [keyValueToWord, bytes32Width, ABI.bytesToWord, fromByteArrayBigEndian,
    byteArray_toList_eq, show 32 ≤ I.calldata.size - 4 by omega] at hword ⊢
  exact hword

theorem urnsInkStorageSlot_eq (I : ExecutionEnv) (hsz68 : 68 ≤ I.calldata.size) :
    urnsInkStorageSlot I =
      solcMappingSlot (solcMappingSlot ⟨3⟩ (urnsIlkWord I)) (urnsUsrMaskedWord I) := by
  unfold urnsInkStorageSlot urnsBase urnsIlkSlot urnsUsrKey urnsUsrMaskedWord
    mapSlot solcMappingSlot
  rw [urnsIlkKeyWord_eq I (by omega), keyValueToWord_address_ofNat_mask]

theorem urnsArtStorageSlot_eq (I : ExecutionEnv) (hsz68 : 68 ≤ I.calldata.size) :
    urnsArtStorageSlot I =
      solcMappingSlot (solcMappingSlot ⟨3⟩ (urnsIlkWord I)) (urnsUsrMaskedWord I) + ⟨1⟩ := by
  simp [urnsArtStorageSlot, urnsInkStorageSlot_eq I hsz68]

theorem vatDecode_urns_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (urnsTransition.params.map Param.name)
      (transitionSignature urnsTransition).paramTypes I.calldata = some (urnsStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0", "arg1"] [bytes32, addr]
    I.calldata = _
  simpa [config, urnsStore, urnsIlkValue, urnsUsrValue, urnsUsrWord] using
    decodeCalldata_legacyBytes32_legacyAddress_ok
      (cd := I.calldata) (x := "arg0") (y := "arg1") hsz68

theorem vatDecode_urns_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (urnsTransition.params.map Param.name)
      (transitionSignature urnsTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0", "arg1"] [bytes32, addr]
    I.calldata = none
  simpa [config] using decodeCalldata_legacyBytes32_legacyAddress_none_short
    (cd := I.calldata) (x := "arg0") (y := "arg1") hsz4 hshort

theorem vatDispatchUrns {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 25)) :
    dispatchMsg contract I.calldata = some urnsTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 25 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some urnsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes, foldSelectorBytes,
    forkSelectorBytes, frobSelectorBytes, gemSelectorBytes, grabSelectorBytes,
    healSelectorBytes, hopeSelectorBytes, ilksSelectorBytes, initSelectorBytes,
    liveSelectorBytes, moveSelectorBytes, nopeSelectorBytes, relySelectorBytes,
    sinSelectorBytes, slipSelectorBytes, suckSelectorBytes, urnsSelectorBytes]
  native_decide

theorem vatReachUrnsBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 25)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨570⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x2424be5c⟩ :=
    vatSelWord_eq_of_beq I hsz 0x24 0x24 0xbe 0x5c ⟨0x2424be5c⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlowlow :
      UInt256.gt (armSelNat vatBytecode vatLowLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms370FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms370FirstPc 0))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms370Body 0 (by omega) ⟨570⟩ hcode hwv hsz hsize
    hroot hlow hlowlow heq0 htake (by jump_dest) (by native_decide)

@[reducible] def solcNestedStruct2GetterWf
    (code : ByteArray) (pc baseSlot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p30 := p28 + UInt256.ofNat 2
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (baseSlot, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p5 = some (.SWAP1, .none)
  ∧ decode code p6 = some (.DUP2, .none)
  ∧ decode code p7 = some (.MSTORE, .none)
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p10 = some (.SWAP3, .none)
  ∧ decode code p11 = some (.DUP4, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p15 = some (.DUP1, .none)
  ∧ decode code p16 = some (.DUP5, .none)
  ∧ decode code p17 = some (.KECCAK256, .none)
  ∧ decode code p18 = some (.SWAP1, .none)
  ∧ decode code p19 = some (.SWAP2, .none)
  ∧ decode code p20 = some (.MSTORE, .none)
  ∧ decode code p21 = some (.SWAP1, .none)
  ∧ decode code p22 = some (.DUP3, .none)
  ∧ decode code p23 = some (.MSTORE, .none)
  ∧ decode code p24 = some (.SWAP1, .none)
  ∧ decode code p25 = some (.KECCAK256, .none)
  ∧ decode code p26 = some (.DUP1, .none)
  ∧ decode code p27 = some (.SLOAD, .none)
  ∧ decode code p28 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p30 = some (.SWAP1, .none)
  ∧ decode code p31 = some (.SWAP2, .none)
  ∧ decode code p32 = some (.ADD, .none)
  ∧ decode code p33 = some (.SLOAD, .none)
  ∧ decode code p34 = some (.DUP3, .none)
  ∧ decode code p35 = some (.JUMP, .none)

set_option maxHeartbeats 2000000 in
theorem RD.solcNestedStruct2Getter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot owner spender ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (spender :: owner :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcNestedStruct2GetterWf code pc baseSlot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot baseSlot owner) spender + ⟨1⟩) ::
        solcSlotWord σ ee (solcMappingSlot (solcMappingSlot baseSlot owner) spender) ::
        ret :: R)
      (solcNestedMappingHashMem baseSlot owner spender)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd10, hd11, hd12, hd13, hd15, hd16,
      hd17, hd18, hd19, hd20, hd21, hd22, hd23, hd24, hd25, hd26, hd27,
      hd28, hd30, hd31, hd32, hd33, hd34, hd35⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 baseSlot hd1 (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ hd3 (by evm_ov)
  have rd6 := rd5.swap1 hd5 (by evm_ov)
  have rd7 := rd6.dup2 hd6 (by evm_ov)
  have rd9 := rd7.mstore 0 (solcMappingBaseSlotMem baseSlot)
    (UInt256.ofNat 3) hd7 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd10 := rd9.push1 ⟨0⟩ hd8 (by evm_ov)
  have rd11 := rd10.swap3 hd10 (by evm_ov)
  have rd12 := rd11.dup4 hd11 (by evm_ov)
  have rd14 := rd12.mstore 0 (solcMappingHashMem baseSlot owner)
    (UInt256.ofNat 3) hd12 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd15 := rd14.push1 ⟨64⟩ hd13 (by evm_ov)
  have rd16 := rd15.dup1 hd15 (by evm_ov)
  have rd17 := rd16.dup5 hd16 (by evm_ov)
  have hinner := solcMappingKeccakSlot baseSlot owner
  have rd18 := rd17.keccak256 0 (solcMappingSlot baseSlot owner)
    (UInt256.ofNat 3) hd17 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hinner)
    (by native_decide) (by evm_ov)
  have rd19 := rd18.swap1 hd18 (by evm_ov)
  have rd20 := rd19.swap2 hd19 (by evm_ov)
  have rd21 := rd20.mstore 0 (solcNestedMappingOuterBaseMem baseSlot owner)
    (UInt256.ofNat 3) hd20 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd22 := rd21.swap1 hd21 (by evm_ov)
  have rd23 := rd22.dup3 hd22 (by evm_ov)
  have rd24 := rd23.mstore 0 (solcNestedMappingHashMem baseSlot owner spender)
    (UInt256.ofNat 3) hd23 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd25 := rd24.swap1 hd24 (by evm_ov)
  have hslot := solcNestedMappingKeccakSlot baseSlot owner spender
  have rd26 := rd25.keccak256 0
    (solcMappingSlot (solcMappingSlot baseSlot owner) spender)
    (UInt256.ofNat 3) hd25 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  have rd27 := rd26.dup1 hd26 (by evm_ov)
  obtain ⟨_, _, rd28⟩ := rd27.sload hd27 (by evm_ov)
  have rd30 := rd28.push1 ⟨1⟩ hd28 (by evm_ov)
  have rd31 := rd30.swap1 hd30 (by evm_ov)
  have rd32 := rd31.swap2 hd31 (by evm_ov)
  have rd33 := rd32.add hd32 (by evm_ov)
  obtain ⟨_, _, rd34⟩ := rd33.sload hd33 (by evm_ov)
  have rd35 := rd34.dup3 hd34 (by evm_ov)
  exact ⟨_, _, by
    simpa [solcSlotWord] using rd35.jump hd35 hret (by evm_ov)⟩

theorem vatUrnsBodyReturns {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (evm : EVM.State) (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (urnsStore I) urnsTransition.body
      (.returned { contract := contract, locals := urnsStore I } evm
        (some [(.int (Int.ofNat
          (vatSlotWord (urnsInkStorageSlot I) evm.accountMap evm.executionEnv).toNat)),
          (.int (Int.ofNat
          (vatSlotWord (urnsArtStorageSlot I) evm.accountMap evm.executionEnv).toNat))])) := by
  let frame : Frame := { contract := contract, locals := urnsStore I }
  have harg0Len : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hink :
      evalExpr? config frame evm (.storage (urnsF (.var "arg0") (.var "arg1") "ink")) =
        .ok (.int (Int.ofNat
          (vatSlotWord (urnsInkStorageSlot I) evm.accountMap evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := urnsF (.var "arg0") (.var "arg1") "ink") (er := urnsInkEvaledRef I)
      (t := .int uint256Int) (loc := wordLoc (urnsInkStorageSlot I))
      (value := .int (Int.ofNat
        (vatSlotWord (urnsInkStorageSlot I) evm.accountMap evm.executionEnv).toNat))
      (by simp [frame, urnsStore, urnsF])
      (by
        simp [frame, urnsInkEvaledRef, urnsIlkValue, urnsUsrValue, urnsIlkKey,
          urnsUsrKey, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, urnsF,
          evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind,
          urnsStore_index_arg0, harg0Len, bytes32Width])
      (by
        simp [frame, urnsIlkKey, urnsUsrKey, storageTypeAt?, storageTypeStep?,
          contract, storageDecls, UrnStructTy, uint256St])
      (by rfl)
      (by simpa [vatSlotWord] using vatStorageLocLoad_uint256 evm (urnsInkStorageSlot I))
  have hart :
      evalExpr? config frame evm (.storage (urnsF (.var "arg0") (.var "arg1") "art")) =
        .ok (.int (Int.ofNat
          (vatSlotWord (urnsArtStorageSlot I) evm.accountMap evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := urnsF (.var "arg0") (.var "arg1") "art") (er := urnsArtEvaledRef I)
      (t := .int uint256Int) (loc := wordLoc (urnsArtStorageSlot I))
      (value := .int (Int.ofNat
        (vatSlotWord (urnsArtStorageSlot I) evm.accountMap evm.executionEnv).toNat))
      (by simp [frame, urnsStore, urnsF])
      (by
        simp [frame, urnsArtEvaledRef, urnsIlkValue, urnsUsrValue, urnsIlkKey,
          urnsUsrKey, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, urnsF,
          evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind,
          urnsStore_index_arg0, harg0Len, bytes32Width])
      (by
        simp [frame, urnsIlkKey, urnsUsrKey, storageTypeAt?, storageTypeStep?,
          contract, storageDecls, UrnStructTy, uint256St])
      (by rfl)
      (by simpa [vatSlotWord] using vatStorageLocLoad_uint256 evm (urnsArtStorageSlot I))
  have hreturns :
      evalExprs? config frame evm
        [.storage (urnsF (.var "arg0") (.var "arg1") "ink"),
          .storage (urnsF (.var "arg0") (.var "arg1") "art")] =
          .ok
            [ .int (Int.ofNat
                (vatSlotWord (urnsInkStorageSlot I) evm.accountMap evm.executionEnv).toNat),
              .int (Int.ofNat
                (vatSlotWord (urnsArtStorageSlot I) evm.accountMap evm.executionEnv).toNat) ] := by
    simp [evalExprs?, hink, hart, EvalResult.bind, bind, pure]
  simpa [urnsTransition, nonpayable, frame] using
    (ExecFuncBody.execBlockRet <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consReturn (ExecStmt.return hreturns))

theorem vatUrnsBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some urnsTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (urnsTransition.params.map Param.name)
        (transitionSignature urnsTransition).paramTypes I.calldata = some (urnsStore I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨570⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let inkSlot := solcMappingSlot (solcMappingSlot ⟨3⟩ (urnsIlkWord I)) (urnsUsrMaskedWord I)
  let artSlot := inkSlot + ⟨1⟩
  let inkWord := vatSlotWord inkSlot σ_evm I
  let artWord := vatSlotWord artSlot σ_evm I
  have hinkSlot : urnsInkStorageSlot I = inkSlot := by
    simp [inkSlot, urnsInkStorageSlot_eq I hsz68]
  have hartSlot : urnsArtStorageSlot I = artSlot := by
    simp [artSlot, inkSlot, urnsArtStorageSlot_eq I hsz68]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (urnsStore I)
        urnsTransition.body
        (.returned { contract := contract, locals := urnsStore I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (vatSlotWord (urnsInkStorageSlot I) σ_solm I).toNat)),
            (.int (Int.ofNat (vatSlotWord (urnsArtStorageSlot I) σ_solm I).toNat))])) := by
    simpa [initState] using
      vatUrnsBodyReturns hsz68
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (by simp only [initState]; exact hwv)
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨570⟩) (ret := ⟨614⟩)
    (decoded := ⟨592⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcBytes32AddressExternalMaskAndJump
    (code := vatBytecode) (decoded := ⟨592⟩) (ret := ⟨614⟩) (routine := ⟨2016⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.solcNestedStruct2Getter
    (code := vatBytecode) (pc := ⟨2016⟩) (baseSlot := ⟨3⟩)
    (owner := urnsIlkWord I) (spender := urnsUsrMaskedWord I)
    (ret := ⟨614⟩) (R := [sel])
    (by simpa [urnsIlkWord, urnsUsrMaskedWord, urnsUsrWord] using hroutine)
    (by
      unfold solcNestedStruct2GetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret vatBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray inkWord ++ UInt256.toByteArray artWord) := by
    have hret' := RD.solcTwoWordReturnFromMem
      (pc := ⟨614⟩) (first := inkWord) (second := artWord) (ret := ⟨614⟩)
      (R := [sel]) (mem := solcNestedMappingHashMem ⟨3⟩ (urnsIlkWord I) (urnsUsrMaskedWord I))
      (by
        simpa [inkWord, artWord, inkSlot, artSlot, vatSlotWord] using hretPc)
      (by
        unfold solcTwoWordReturnFromMemWf
        repeat' first | apply And.intro | native_decide)
      (solcNestedMappingHashMem_mload64 ⟨3⟩ (urnsIlkWord I) (urnsUsrMaskedWord I))
      (solcNestedMappingHashMem_size ⟨3⟩ (urnsIlkWord I) (urnsUsrMaskedWord I))
      (solcNestedMappingHashMem_read64 ⟨3⟩ (urnsIlkWord I) (urnsUsrMaskedWord I))
      (by simp)
    simpa [inkWord, artWord] using hret'
  have hinkWord : vatSlotWord inkSlot σ_evm I = vatSlotWord inkSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner inkSlot ⟨0⟩
  have hartWord : vatSlotWord artSlot σ_evm I = vatSlotWord artSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner artSlot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (vatSlotWord (urnsInkStorageSlot I) σ_solm I).toNat),
        Value.int (Int.ofNat (vatSlotWord (urnsArtStorageSlot I) σ_solm I).toNat)] =
      some [Value.int (Int.ofNat inkWord.toNat), Value.int (Int.ofNat artWord.toNat)] := by
    rw [hinkSlot, hartSlot]
    simp [inkWord, artWord, hinkWord, hartWord]
  have henc :
      returnEquiv (UInt256.toByteArray inkWord ++ UInt256.toByteArray artWord)
        (some [(.int (Int.ofNat inkWord.toNat)), (.int (Int.ofNat artWord.toNat))])
        urnsTransition.returnType := by
    rw [show urnsTransition.returnType = [uint256, uint256] by rfl]
    exact returnEquiv.returned rfl (uint256PairReturnEncoding inkWord artWord)
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem vatUrnsBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some urnsTransition)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨570⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := vatDecode_urns_none_short (I := I) hsz4 hshort
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨570⟩) (ret := ⟨614⟩)
    (decoded := ⟨592⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch hdec

theorem vatUrnsBodyCore : VatBodyTheorem 25 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize _hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 25) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some urnsTransition :=
    vatDispatchUrns hsel
  have hreach := vatReachUrnsBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · exact vatUrnsBodyCoreOk hcode hwv hsz68 hsize hdispatch
      (vatDecode_urns_ok hsz68) hreach hAccounts
  · exact vatUrnsBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Vat
