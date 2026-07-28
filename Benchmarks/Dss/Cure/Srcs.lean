import Benchmarks.Dss.Cure.Common
import Ethereum.Theory.OpcodeLemmas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cure

/-! ## `srcs(uint256)` -/

abbrev srcsIndex (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev srcsEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "srcs", steps := [.aindex (.int (Int.ofNat (srcsIndex I).toNat))] }

abbrev srcsSlotFor (I : ExecutionEnv) : UInt256 :=
  srcElemSlot (.int (Int.ofNat (srcsIndex I).toNat))

theorem srcsSlotFor_eq (I : ExecutionEnv) :
    srcsSlotFor I = srcsDataSlot + srcsIndex I := by
  unfold srcsSlotFor srcsIndex srcElemSlot
  change srcsDataSlot + EVM.wordOfInt (Int.ofNat (calldataWord I.calldata 4).toNat) =
    srcsDataSlot + calldataWord I.calldata 4
  rw [wordOfInt_ofNat_toNat]

theorem cureDispatchSrcs {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 14)) :
    dispatchMsg contract I.calldata = some srcsTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 14 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some srcsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes,
    cureAmtSelectorBytes, cureCageSelectorBytes, cureDenySelectorBytes,
    cureDropSelectorBytes, cureFileSelectorBytes, cureLCountSelectorBytes,
    cureLiftSelectorBytes, cureListSelectorBytes, cureLiveSelectorBytes,
    cureLoadSelectorBytes, cureLoadedSelectorBytes, curePosSelectorBytes,
    cureRelySelectorBytes, cureSaySelectorBytes, cureSrcsSelectorBytes]
  native_decide

theorem cureDecode_srcs_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (srcsTransition.params.map Param.name)
      (transitionSignature srcsTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (.int (Int.ofNat (srcsIndex I).toNat))) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      calldataWord I.calldata 4 :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [abiUInt256] I.calldata =
    some ((∅ : Store).insert "arg0" (.int (Int.ofNat (srcsIndex I).toNat)))
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := ["arg0"])
    (types := [abiUInt256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok
    (mode := DecodeMode.legacySolc05) (bytes := I.calldata.toList.drop 4)
    (start := 0) htake4]
  change decodeCalldata.insertValues ["arg0"]
      [.int (Int.ofNat (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Store).insert "arg0" (.int (Int.ofNat (srcsIndex I).toNat)))
  simp [decodeCalldata.insertValues, srcsIndex]
  rw [hword4]

theorem cureDecode_srcs_none_short {I : ExecutionEnv} (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (srcsTransition.params.map Param.name)
      (transitionSignature srcsTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [abiUInt256] I.calldata = none
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := ["arg0"])
    (types := [abiUInt256]) (cd := I.calldata) (by decide)]
  by_cases hsz4 : I.calldata.size < 4
  · rw [if_pos (by rw [htlen]; omega : I.calldata.toList.length < 4)]
  · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
    have htakeShort :
        ¬ (((I.calldata.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    simp only [decodeScalarWordsWithMode?]
    rw [decodeScalarWordWithMode_uint256_none_short
      (mode := DecodeMode.legacySolc05) (bytes := I.calldata.toList.drop 4)
      (start := 0) htakeShort]
    simp only [Option.bind, bind]

theorem cureReachSrcsBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 14)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨816⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0xf381273f⟩ :=
    cureSelWord_eq_of_beq I hsz 0xf3 0x81 0x27 0x3f ⟨0xf381273f⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h54⟩ := cureReachHighUpperFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨816⟩ 3 h54 (fun j hj => cureHighUpperArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

abbrev srcsLenWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  cureSlotWord ⟨2⟩ σ I

abbrev srcsRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  cureSlotWord (srcsSlotFor I) σ I

abbrev srcsAddressValue (σ : AccountMap) (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (UInt256.land (srcsRawWord σ I) solcAddrMask).toNat)

theorem evalExpr_srcsStorage_inBounds {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : (srcsIndex I).toNat < (srcsLenWord σ I).toNat) :
    let locals : Store := (∅ : Store).insert "arg0" (.int (Int.ofNat (srcsIndex I).toNat))
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage (srcElemRef (.var "arg0"))) =
        .ok (srcsAddressValue σ I) := by
  intro locals
  rw [evalExpr_storage_scalar
    (er := srcsEvaledRef I) (t := .address) (loc := addrLoc (srcsSlotFor I))]
  · rw [show addrLoc (srcsSlotFor I) = addressOffset0Loc (srcsSlotFor I) by rfl]
    rw [storageLocLoad_address_offset0]
    simp [srcsAddressValue, srcsRawWord, cureSlotWord, solcSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
  · simp [locals, srcElemRef]
  · have hlenLoad :
        storageLocLoad (initState cA gh bl σ σ₀ g A I) (wordLoc ⟨2⟩) =
          .int (Int.ofNat (srcsLenWord σ I).toNat) := by
      rw [cureStorageLocLoad_uint256]
      simp [srcsLenWord, cureSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage]
    simp only [wordLoc] at hlenLoad
    simp [srcsEvaledRef, srcElemRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, evalExpr?, EvalResult.ofOption, EvalResult.bind, pure, bind,
      valueToKey?, locals, arrayIndexInBounds?, config, storageLayout, solidityStorageLayout,
      storageLayoutRaw, storageTypeAt?, contract, storageDecls, wordLoc]
    rw [hlenLoad]
    simp [hlt]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, addrSt]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, srcsEvaledRef,
      srcsSlotFor, srcElemSlot, srcsIndex]

theorem cureSrcsSourceBodyOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlt : (srcsIndex I).toNat < (srcsLenWord σ I).toNat) :
    let locals : Store := (∅ : Store).insert "arg0" (.int (Int.ofNat (srcsIndex I).toNat))
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) locals srcsTransition.body
      (.returned { contract := contract, locals := locals }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (some [srcsAddressValue σ I])) := by
  intro locals
  have hsrc :
      evalExpr? config { contract := contract, locals := locals }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.storage (srcElemRef (.var "arg0"))) =
          .ok (srcsAddressValue σ I) := by
    simpa [locals] using evalExpr_srcsStorage_inBounds (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hlt
  simpa [srcsTransition] using
    nonpayableReturnExprBodyReturns
      (cfg := config) (contract := contract)
      (evm := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (locals := locals) (expr := .storage (srcElemRef (.var "arg0")))
      (value := srcsAddressValue σ I)
      (by simp only [initState]; exact hwv)
      hsrc

theorem evalExpr_srcsStorage_oob {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle : (srcsLenWord σ I).toNat ≤ (srcsIndex I).toNat) :
    let locals : Store := (∅ : Store).insert "arg0" (.int (Int.ofNat (srcsIndex I).toNat))
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage (srcElemRef (.var "arg0"))) =
        .revert := by
  intro locals
  have hlenLoad :
      storageLocLoad (initState cA gh bl σ σ₀ g A I) (wordLoc ⟨2⟩) =
        .int (Int.ofNat (srcsLenWord σ I).toNat) := by
    rw [cureStorageLocLoad_uint256]
    simp [srcsLenWord, cureSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage]
  simp only [wordLoc] at hlenLoad
  have her :
      evalStorageRef config { contract := contract, locals := locals }
        (initState cA gh bl σ σ₀ g A I) (srcElemRef (.var "arg0")) = .revert := by
    simp [srcElemRef, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
      EvalResult.ofOption, EvalResult.bind, pure, bind, valueToKey?, locals,
      arrayIndexInBounds?, config, storageLayout, solidityStorageLayout, storageLayoutRaw,
      storageTypeAt?, contract, storageDecls, wordLoc]
    rw [hlenLoad]
    simp [Nat.not_lt.mpr hle]
  simp only [evalExpr?]
  change (do
      let __discr ← resolveStorageRef? config { contract := contract, locals := locals }
        (initState cA gh bl σ σ₀ g A I) (srcElemRef (.var "arg0"))
      readStorage? config (initState cA gh bl σ σ₀ g A I) __discr.1 __discr.2) =
    EvalResult.revert
  have hresolve :
      resolveStorageRef? config { contract := contract, locals := locals }
        (initState cA gh bl σ σ₀ g A I) (srcElemRef (.var "arg0")) = .revert := by
    unfold resolveStorageRef?
    simp [srcElemRef, locals]
    have her' :
        evalStorageRef config
          { contract := contract,
            locals := (∅ : Store).insert "arg0" (.int ↑(srcsIndex I).toNat) }
          (initState cA gh bl σ σ₀ g A I)
          { base := "srcs", steps := [.aindex (.var "arg0")] } = .revert := by
      simpa [locals, srcElemRef] using her
    simpa [her']
  rw [hresolve]
  rfl

theorem cureSrcsSourceBodyOob {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hle : (srcsLenWord σ I).toNat ≤ (srcsIndex I).toNat) :
    let locals : Store := (∅ : Store).insert "arg0" (.int (Int.ofNat (srcsIndex I).toNat))
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) locals srcsTransition.body
      .reverted := by
  intro locals
  have hsrc :
      evalExpr? config { contract := contract, locals := locals }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.storage (srcElemRef (.var "arg0"))) = .revert := by
    simpa [locals] using evalExpr_srcsStorage_oob (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hle
  simp [srcsTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
    simp only [initState]; exact hwv))) ?_
  exact ExecBlock.consRevert (ExecStmt.returnRevert (by
    change (do
      let value ← evalExpr? config { contract := contract, locals := locals }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.storage (srcElemRef (.var "arg0")))
      let values ← pure []
      pure (value :: values)) = EvalResult.revert
    rw [hsrc]
    rfl))

noncomputable abbrev srcsBaseSlotMem : ByteArray :=
  wordAt0Mem ⟨2⟩ solcFreePtrMem

theorem srcsBaseSlotMem_size : srcsBaseSlotMem.size = 96 := by
  exact wordAt0Mem_size_96 ⟨2⟩ solcFreePtrMem_size

theorem srcsBaseSlotMem_read64 :
    srcsBaseSlotMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold srcsBaseSlotMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega)
    (by rw [solcFreePtrMem_size])]
  exact solcFreePtrMem_read64

theorem srcsBaseSlotMem_keccak :
    UInt256.ofNat
      (fromByteArrayBigEndian (ffi.KEC (srcsBaseSlotMem.readWithPadding 0 32))) =
        srcsDataSlot := by
  simpa [srcsBaseSlotMem, srcsDataSlot, uInt256OfByteArray_eq] using
    wordAt0Mem_keccak_word (⟨2⟩ : UInt256) solcFreePtrMem

@[reducible] def srcsArrayGetterInBoundsWf (code : ByteArray) : Prop :=
  decode code ⟨3609⟩ = some (.JUMPDEST, .none)
  ∧ decode code ⟨3610⟩ = some (.Push .PUSH1, some (⟨2⟩, 1))
  ∧ decode code ⟨3612⟩ = some (.DUP2, .none)
  ∧ decode code ⟨3613⟩ = some (.DUP2, .none)
  ∧ decode code ⟨3614⟩ = some (.SLOAD, .none)
  ∧ decode code ⟨3615⟩ = some (.DUP2, .none)
  ∧ decode code ⟨3616⟩ = some (.LT, .none)
  ∧ decode code ⟨3617⟩ = some (.Push .PUSH2, some (⟨3622⟩, 2))
  ∧ decode code ⟨3620⟩ = some (.JUMPI, .none)
  ∧ decode code ⟨3622⟩ = some (.JUMPDEST, .none)
  ∧ decode code ⟨3623⟩ = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code ⟨3625⟩ = some (.SWAP2, .none)
  ∧ decode code ⟨3626⟩ = some (.DUP3, .none)
  ∧ decode code ⟨3627⟩ = some (.MSTORE, .none)
  ∧ decode code ⟨3628⟩ = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code ⟨3630⟩ = some (.SWAP1, .none)
  ∧ decode code ⟨3631⟩ = some (.SWAP2, .none)
  ∧ decode code ⟨3632⟩ = some (.KECCAK256, .none)
  ∧ decode code ⟨3633⟩ = some (.ADD, .none)
  ∧ decode code ⟨3634⟩ = some (.SLOAD, .none)
  ∧ decode code ⟨3635⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code ⟨3637⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code ⟨3639⟩ = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code ⟨3641⟩ = some (.SHL, .none)
  ∧ decode code ⟨3642⟩ = some (.SUB, .none)
  ∧ decode code ⟨3643⟩ = some (.AND, .none)
  ∧ decode code ⟨3644⟩ = some (.SWAP1, .none)
  ∧ decode code ⟨3645⟩ = some (.POP, .none)
  ∧ decode code ⟨3646⟩ = some (.DUP2, .none)
  ∧ decode code ⟨3647⟩ = some (.JUMP, .none)

theorem RD.cureSrcsArrayGetterInBounds {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {k C : ℕ} {idx len ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 ⟨3609⟩ (idx :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      rdata (cA, σ) k C)
    (hwf : srcsArrayGetterInBoundsWf code)
    (hlt : idx.toNat < len.toNat)
    (hlen : (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨2⟩ ⟨0⟩)) = len)
    (hjmpBounds : (D_J code 0).contains ⟨3622⟩ = true)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      ((UInt256.land
          (σ.find? ee.codeOwner |>.option ⟨0⟩
            (fun ac => ac.storage.findD (srcsDataSlot + idx) ⟨0⟩))
          solcAddrMask) :: ret :: R)
      srcsBaseSlotMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd7, hd8, hd11, hd13, hd13p, hd15, hd16, hd17,
      hd18, hd20, hd21, hd22, hd23, hd25, hd26, hd28, hd30, hd32, hd33, hd34,
      hd35, hd36, hd37, hd38⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨2⟩ hd1 (by simp only [List.length_cons]; omega)
  have rd4 := rd3.dup2 hd3 (by simp only [List.length_cons]; omega)
  have rd5 := rd4.dup2 hd4 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd6'⟩ := rd5.sload hd5 (by simp only [List.length_cons]; omega)
  have rd6 := by
    simpa [hlen] using rd6'
  have rd7 := rd6.dup2 hd6 (by simp only [List.length_cons]; omega)
  have rd8 := rd7.lt hd7 (by simp only [List.length_cons]; omega)
  have hltWord : UInt256.lt idx len = ⟨1⟩ := by
    apply ult_one
    exact hlt
  have rd11 := rd8.push2 ⟨3622⟩ hd8 (by simp only [List.length_cons]; omega)
  have hcond : UInt256.lt idx len ≠ ⟨0⟩ := by
    rw [hltWord]
    native_decide
  have rd13 := rd11.jumpiT hd11 hcond hjmpBounds
    (by simp only [List.length_cons]; omega)
  have rd14 := rd13.jumpdest hd13 (by simp only [List.length_cons]; omega)
  have rd16 := rd14.push1 ⟨0⟩ hd13p (by simp only [List.length_cons]; omega)
  have rd17 := rd16.swap2 hd15 (by simp only [List.length_cons]; omega)
  have rd18 := rd17.dup3 hd16 (by simp only [List.length_cons]; omega)
  have rd19 := rd18.mstore 0 srcsBaseSlotMem (UInt256.ofNat 3) hd17 mem_cost
    (by rfl) (by native_decide) (by simp only [List.length_cons]; omega)
  have rd21 := rd19.push1 ⟨32⟩ hd18 (by simp only [List.length_cons]; omega)
  have rd22 := rd21.swap1 hd20 (by simp only [List.length_cons]; omega)
  have rd23 := rd22.swap2 hd21 (by simp only [List.length_cons]; omega)
  have rd24 := rd23.keccak256 0 srcsDataSlot (UInt256.ofNat 3) hd22 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide] using srcsBaseSlotMem_keccak)
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd25 := rd24.add hd23 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd26'⟩ := rd25.sload hd25 (by simp only [List.length_cons]; omega)
  have rd26 := by
    simpa using rd26'
  have rd28 := rd26.push1 ⟨1⟩ hd26 (by simp only [List.length_cons]; omega)
  have rd30 := rd28.push1 ⟨1⟩ hd28 (by simp only [List.length_cons]; omega)
  have rd32 := rd30.push1 ⟨160⟩ hd30 (by simp only [List.length_cons]; omega)
  have rd33 := rd32.shl hd32 (by simp only [List.length_cons]; omega)
  have rd34 := rd33.sub hd33 (by simp only [List.length_cons]; omega)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rd35 := rd34.and hd34 (by simp only [List.length_cons]; omega)
  have rd36 := by
    simpa [hmask,
      u256_land_comm solcAddrMask
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun ac => ac.storage.findD (srcsDataSlot + idx) ⟨0⟩))] using rd35
  have rd37 := rd36.swap1 hd35 (by simp only [List.length_cons]; omega)
  have rd38 := rd37.pop hd36 (by simp only [List.length_cons]; omega)
  have rd39 := rd38.dup2 hd37
    (by
      simpa only [List.length_cons] using (show R.length + 3 ≤ 1024 by omega))
  exact ⟨_, _, rd39.jump hd38 hret
    (by
      simpa only [List.length_cons] using (show R.length + 2 ≤ 1024 by omega))⟩

def RDinvalid (code : ByteArray) (g : Sat256) (s0 : State) : Prop :=
  X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass
  ∨ X (g.toNat + 1) (D_J code 0) s0 = .error .InvalidInstruction

theorem rdInvalidHalt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.INVALID, .none)) :
    RDinvalid code g s0 := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, _hstk, _hgas, hk, hC, _hmem, _haw,
    _hrdata, _hacc, _hee, _hworld⟩
  · exact Or.inl hoog
  · right
    have hdec' : decode s.executionEnv.code s.machineState.pc = some (.INVALID, .none) := by
      rw [hcode, hpc]
      exact hdec
    have hstep : Xstep (D_J code 0) s = .error .InvalidInstruction := by
      simpa [hcode] using Ethereum.EVM.step_invalid s hdec'
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    rw [hX, hfuel]
    exact Xstep_X_X_except (g.toNat - k) s (D_J code 0) _ hstep

theorem RD.cureSrcsInBounds {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (h : RD cureBytecode I g s0 ⟨838⟩
      [UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩, ⟨4⟩, ⟨845⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlt : (srcsIndex I).toNat < (srcsLenWord σ I).toNat) :
    RDret cureBytecode g s0 (cA, σ)
      (UInt256.toByteArray (UInt256.land (srcsRawWord σ I) solcAddrMask)) := by
  have rd839 := h.jumpdest (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd840 := rd839.pop (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd841' := rd840.calldataload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd841 := by
    simpa [srcsIndex, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide] using rd841'
  have rd844 := rd841.push2 ⟨3609⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3609 := rd844.jump (by native_decide) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3609' := by
    simpa [srcsIndex, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide] using rd3609
  have hlen :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨2⟩ ⟨0⟩)) =
        srcsLenWord σ I := by
    rfl
  obtain ⟨_, _, rd845⟩ := RD.cureSrcsArrayGetterInBounds
    (idx := srcsIndex I) (len := srcsLenWord σ I) (ret := ⟨845⟩) (R := [sel])
    rd3609' (by unfold srcsArrayGetterInBoundsWf; repeat' first | apply And.intro | native_decide)
    hlt hlen (by jump_dest) (by jump_dest) (by simp)
  have hraw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun ac => ac.storage.findD (srcsDataSlot + srcsIndex I) ⟨0⟩)) =
        srcsRawWord σ I := by
    rw [← srcsSlotFor_eq I]
    rfl
  let masked := UInt256.land (srcsRawWord σ I) solcAddrMask
  have hclean : UInt256.land masked solcAddrMask = masked := by
    exact solcAddrMask_clean (solcAddrMask_result_canonical (srcsRawWord σ I))
  have hret := RD.solcReturnAddressFromMem
    (pc := ⟨845⟩) (val := masked) (ret := ⟨845⟩) (R := [sel])
    (memout := solcScratchReturnMem srcsBaseSlotMem masked)
    (by simpa [masked, hraw] using rd845)
    (by unfold solcReturnAddressFromMemWf; repeat' first | apply And.intro | native_decide)
    (by
      exact mloadFreePtrValue
        (by rw [srcsBaseSlotMem_size]; decide) (by decide) srcsBaseSlotMem_read64)
    (by
      unfold solcScratchReturnMem
      rw [hclean])
    (by
      exact solcScratchReturnMem_mload64 masked srcsBaseSlotMem_size srcsBaseSlotMem_read64)
    (by
      rw [hclean]
      exact solcScratchReturnMem_read128 masked srcsBaseSlotMem_size)
    (by simp)
  simpa [masked, hclean] using hret

theorem RD.cureSrcsOutOfBoundsInvalid {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (h : RD cureBytecode I g s0 ⟨838⟩
      [UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩, ⟨4⟩, ⟨845⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hle : (srcsLenWord σ I).toNat ≤ (srcsIndex I).toNat) :
    RDinvalid cureBytecode g s0 := by
  have rd839 := h.jumpdest (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd840 := rd839.pop (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd841' := rd840.calldataload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd841 := by
    simpa [srcsIndex, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide] using rd841'
  have rd844 := rd841.push2 ⟨3609⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3609 := rd844.jump (by native_decide) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3609n := by
    simpa [srcsIndex, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide] using rd3609
  have rd1 := rd3609n.jumpdest (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3 := rd1.push1 ⟨2⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4 := rd3.dup2 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5 := rd4.dup2 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨k6, C6, rd6'⟩ := rd5.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6 :
      RD cureBytecode I g s0 ⟨3615⟩
        [srcsLenWord σ I, srcsIndex I, ⟨2⟩, srcsIndex I, ⟨845⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6 C6 := by
    simpa [srcsLenWord, cureSlotWord, solcSlotWord, srcsIndex, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide] using rd6'
  have rd7 := rd6.dup2 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd8 := rd7.lt (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hltWord : UInt256.lt (srcsIndex I) (srcsLenWord σ I) = ⟨0⟩ := by
    exact ult_zero hle
  have rd8' := rd8
  rw [hltWord] at rd8'
  have rd11 := rd8'.push2 ⟨3622⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3621 := rd11.jumpiNT (by native_decide) rfl
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact rdInvalidHalt rd3621 (by native_decide)

private theorem Xi_error_of_X_sat_local {createdAccounts genesisBlockHeader blocks σ σ₀ A I}
    {g : Sat256} {e : ExecutionException}
    (h : X (g.toNat + 1) (D_J I.code 0)
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) = .error e) :
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g.toUInt256 A I = .error e :=
  Xi_error_of_X (g := g.toUInt256) (by
    simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using h)

theorem RDinvalid.reEquivExecutionInvalid {cfg : Config} {contract : ContractDecl}
    {t : TransitionDecl} {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code : ByteArray} {callargs}
    (hcode : I.code = code)
    (h : RDinvalid code g (initState cA gh bl σ_evm σ₀ g A I))
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
      (initState cA gh bl σ_solm σ₀ g A I) callargs t.body .reverted)
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  rcases h with hoog | hinv
  · exact reEquiv_outOfGas (Xi_error_of_X_sat_local (by rw [← hcode] at hoog; exact hoog))
  · exact reEquiv_execution hd hdec hbody
      (by
        rw [Xi_error_of_X_sat_local (by rw [← hcode] at hinv; exact hinv)]
        exact execResultsEquiv.invalidHalt rfl rfl)
      hfallback hreceive

theorem cureSrcsBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some srcsTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (srcsTransition.params.map Param.name)
        (transitionSignature srcsTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (.int (Int.ofNat (srcsIndex I).toNat))))
    (hlt : (srcsIndex I).toNat < (srcsLenWord σ_solm I).toNat)
    (hreach : ∃ k C, RD cureBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨816⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals : Store := (∅ : Store).insert "arg0" (.int (Int.ofNat (srcsIndex I).toNat))
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals srcsTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [srcsAddressValue σ_solm I])) := by
    simpa [locals] using cureSrcsSourceBodyOk
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hwv hlt
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := cureBytecode) (sel := sel) (entry := ⟨816⟩) (ret := ⟨845⟩)
    (decoded := ⟨838⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  have hlenWord :
      srcsLenWord σ_evm I = srcsLenWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hltEvm : (srcsIndex I).toNat < (srcsLenWord σ_evm I).toNat := by
    rwa [hlenWord]
  have hret := RD.cureSrcsInBounds (cA := cA) (σ := σ_evm) (I := I)
    (g := Sat256.ofUInt256 g)
    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
    hdecoded hltEvm
  have hraw :
      srcsRawWord σ_evm I = srcsRawWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (srcsSlotFor I) ⟨0⟩
  have hval :
      some [srcsAddressValue σ_solm I] =
        some [srcsAddressValue σ_evm I] := by
    simp [srcsAddressValue, srcsRawWord, hraw]
  have henc :
      returnEquiv (UInt256.toByteArray (UInt256.land (srcsRawWord σ_evm I) solcAddrMask))
        (some [srcsAddressValue σ_evm I]) srcsTransition.returnType := by
    rw [show srcsTransition.returnType = [addr] by rfl]
    exact returnEquiv_of_encode
      (by
        simpa [srcsAddressValue] using
          solcAddressReturnEncoding (addrTy := addr) rfl (srcsRawWord σ_evm I))
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem cureSrcsBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = cureBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some srcsTransition)
    (hreach : ∃ k C, RD cureBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨816⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := cureBytecode) (sel := sel) (entry := ⟨816⟩) (ret := ⟨845⟩)
    (decoded := ⟨838⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (cureDecode_srcs_none_short hshort)

theorem cureSrcsBodyCoreOob
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some srcsTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (srcsTransition.params.map Param.name)
        (transitionSignature srcsTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (.int (Int.ofNat (srcsIndex I).toNat))))
    (hle : (srcsLenWord σ_solm I).toNat ≤ (srcsIndex I).toNat)
    (hreach : ∃ k C, RD cureBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨816⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals : Store := (∅ : Store).insert "arg0" (.int (Int.ofNat (srcsIndex I).toNat))
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        srcsTransition.body .reverted := by
    simpa [locals] using cureSrcsSourceBodyOob
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hwv hle
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := cureBytecode) (sel := sel) (entry := ⟨816⟩) (ret := ⟨845⟩)
    (decoded := ⟨838⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  have hlenWord :
      srcsLenWord σ_evm I = srcsLenWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hleEvm : (srcsLenWord σ_evm I).toNat ≤ (srcsIndex I).toNat := by
    rwa [hlenWord]
  have hinv := RD.cureSrcsOutOfBoundsInvalid (cA := cA) (σ := σ_evm) (I := I)
    (g := Sat256.ofUInt256 g)
    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
    hdecoded hleEvm
  exact RDinvalid.reEquivExecutionInvalid hcode hinv hdispatch hdecode hbody

theorem cureSrcsBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 14))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 14) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some srcsTransition :=
    cureDispatchSrcs hsel
  have hreach := cureReachSrcsBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := cureDecode_srcs_ok hsz36
    by_cases hlt : (srcsIndex I).toNat < (srcsLenWord σ_solm I).toNat
    · exact cureSrcsBodyCoreOk hcode hwv hsz36 hsize hdispatch hdecode
        hlt hreach hAccounts
    · exact cureSrcsBodyCoreOob hcode hwv hsz36 hsize hdispatch hdecode
        (by omega) hreach hAccounts
  · exact cureSrcsBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Cure
