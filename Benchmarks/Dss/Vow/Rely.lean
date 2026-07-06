import Benchmarks.Dss.Vow.Deny

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

/-! ## `rely(address)` -/

abbrev relyUsr (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev relyKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev relyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address (relyUsr I))] }

abbrev relySlotFor (I : ExecutionEnv) : UInt256 :=
  wardsSlot (.address (relyUsr I))

abbrev liveEvaledRef : EvaledStorageRef :=
  { base := "live", steps := [] }

theorem relySlotFor_eq (I : ExecutionEnv) :
    relySlotFor I = solcMappingSlot ⟨0⟩ (relyKey I) := by
  unfold relySlotFor relyUsr relyKey wardsSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem vowLiveGuardEval_true {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "live" = none)
    (hlive : vowSlotWord ⟨12⟩ σ I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hload : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      ⟨12⟩ = ⟨1⟩ := by
    simpa [vowSlotWord] using hlive
  have her :
      evalStorageRef config { contract := contract, locals := locals }
        (initState cA gh bl σ σ₀ g A I) liveRef = .ok liveEvaledRef := by
    simp [liveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc ⟨12⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, liveEvaledRef])]
  rw [vowStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  rw [hload]
  simp [evalExpr?, evalBinaryOp?]
  all_goals native_decide

theorem vowLiveGuardEval_false {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "live" = none)
    (hlive : vowSlotWord ⟨12⟩ σ I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  let w := Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨12⟩
  have hload : w ≠ ⟨1⟩ := by
    intro hw
    exact hlive (by simpa [w, vowSlotWord] using hw)
  have her :
      evalStorageRef config { contract := contract, locals := locals }
        (initState cA gh bl σ σ₀ g A I) liveRef = .ok liveEvaledRef := by
    simp [liveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc ⟨12⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, liveEvaledRef])]
  rw [vowStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  simp [evalExpr?, evalBinaryOp?]
  · intro hnat
    apply hload
    apply u256_inj
    simpa using hnat
  all_goals native_decide

/-! ### `live` guard and store-one bytecode helpers -/

@[reducible] def vowLiveGuardTailPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  p10 + ⟨1⟩

@[reducible] def vowLiveGuardWf (code : ByteArray) (pc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨12⟩, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.EQ, .none)
  ∧ decode code p7 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code p10 = some (.JUMPI, .none)

abbrev vowNotLiveRawWord : UInt256 :=
  ⟨26750464447179039505881069157⟩

theorem RD.vowLiveGuardOk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vowLiveGuardWf code pc okPc)
    (hlive : solcSlotWord σ ee ⟨12⟩ = ⟨1⟩)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 okPc (key :: ret :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10⟩
  have rd3 := h.jumpdest hd0 (by evm_ov) |>.push1 ⟨12⟩ hd1 (by evm_ov)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by evm_ov)
  have hliveRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩ := by
    simpa [solcSlotWord] using hlive
  rw [hliveRaw] at rd4
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by evm_ov)
  have rd7₀ := rd6.eq hd6 (by evm_ov)
  have rd7 := rd7₀
  rw [uInt256_eq_self] at rd7
  have rd10 := rd7.push2 okPc hd7 (by evm_ov)
  exact ⟨_, _, rd10.jumpiT hd10 one_ne_zero_uint hok (by evm_ov)⟩

theorem RD.vowLiveGuardRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vowLiveGuardWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (vowLiveGuardTailPc pc) ⟨12⟩
      vowNotLiveRawWord ⟨160⟩ .PUSH12 12)
    (hlive : solcSlotWord σ ee ⟨12⟩ ≠ ⟨1⟩)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10⟩
  have rd3 := h.jumpdest hd0 (by evm_ov) |>.push1 ⟨12⟩ hd1 (by evm_ov)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by evm_ov)
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by evm_ov)
  have rd7₀ := rd6.eq hd6 (by evm_ov)
  have hliveRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠ ⟨1⟩ := by
    simpa [solcSlotWord] using hlive
  have heq0 :
      UInt256.eq ⟨1⟩
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h1 => hliveRaw h1.symm)
  have rd7 := rd7₀
  rw [heq0] at rd7
  have rd10 := rd7.push2 okPc hd7 (by evm_ov)
  have rdTail₀ := rd10.jumpiNT hd10 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail (by simpa [vowLiveGuardTailPc] using rdTail₀) htail
    (by decide) (by rfl) hmem hread64 (by simpa only [List.length_cons] using hov)

@[reducible] def vowRelyStoreOneWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p12 := p10 + UInt256.ofNat 2
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p7 = some (.SHL, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.AND, .none)
  ∧ decode code p10 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p12 = some (.SWAP1, .none)
  ∧ decode code p13 = some (.DUP2, .none)
  ∧ decode code p14 = some (.MSTORE, .none)
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p17 = some (.DUP2, .none)
  ∧ decode code p18 = some (.SWAP1, .none)
  ∧ decode code p19 = some (.MSTORE, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p22 = some (.SWAP1, .none)
  ∧ decode code p23 = some (.KECCAK256, .none)
  ∧ decode code p24 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p26 = some (.SWAP1, .none)
  ∧ decode code p27 = some (.SSTORE, .none)
  ∧ decode code p28 = some (.JUMP, .none)

theorem RD.vowRelyStoreOne {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vowRelyStoreOneWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R (twoWordHashMem key ⟨0⟩ mem) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨0⟩ key) ⟨1⟩) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd12, hd13, hd14, hd15,
      hd17, hd18, hd19, hd20, hd22, hd23, hd24, hd26, hd27, hd28⟩
  have hmask : UInt256.land solcAddrMask key = key :=
    solcAddrMask_clean_left hcanonKey
  have hmaskLiteral :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) key =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have rdMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw and hd9 (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd10 (by evm_ov),
    raw swap1 hd12 (by evm_ov),
    raw dup2 hd13 (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd14 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨32⟩ hd15 (by evm_ov),
    raw dup2 hd17 (by evm_ov),
    raw swap1 hd18 (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨0⟩ mem)
    (UInt256.ofNat 3) hd19 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ hd20 (by evm_ov),
    raw swap1 hd22 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd23 mem_cost hslot (by native_decide) (by evm_ov)
  have rdBeforeStore := evm_run rdSlot with [
    raw push1 ⟨1⟩ hd24 (by evm_ov),
    raw swap1 hd26 (by evm_ov)]
  obtain ⟨_, _, rdOut⟩ := rdBeforeStore.sstore hperm hd27 (by evm_ov)
  exact ⟨_, _, rdOut.jump hd28 hret (by evm_ov)⟩

/-! ### Dispatch, ABI, reachability, and body proof -/

theorem vowDispatch_rely {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩) :
    dispatchMsg contract I.calldata = some relyTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition, flapTransition,
      flapperTransition, flogTransition, flopTransition, flopperTransition, healTransition,
      humpTransition, kissTransition, liveTransition])
    (post := [sinTransition, sumpTransition, vatTransition, waitTransition, wardsTransition])
    (ti := relyTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, fileAddressSelectorBytes, flapSelectorBytes, flapperSelectorBytes,
        flogSelectorBytes, flopSelectorBytes, flopperSelectorBytes, healSelectorBytes,
        humpSelectorBytes, kissSelectorBytes, liveSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, relySelectorBytes]
    exact hsel

theorem vowDecode_rely_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "usr" (.address (relyUsr I))) := by
  simpa [config, relyTransition, relyUsr] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36)

theorem vowDecode_rely_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = none := by
  simpa [config, relyTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort)

theorem vowReachRelyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨517⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨1710941022⟩ :=
    vowSelWord_eq_of_beq I hsz 0x65 0xfa 0xe3 0x5e ⟨1710941022⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc 3))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachLowHighBody 3 (by omega) ⟨517⟩ hcode hwv hsz hsize hroot hlow heq0 htake
    (by jump_dest) (by native_decide)

theorem vowRelyBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "usr" (.address (relyUsr I))))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨517⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := relyKey I
  let slot := solcMappingSlot ⟨0⟩ key
  let callerSlot := vowCallerWardsSlot I
  let locals : Store := (∅ : Store).insert "usr" (.address (relyUsr I))
  have hslot : relySlotFor I = slot := by
    simp [slot, key, relySlotFor_eq]
  have hcallerWord : vowSlotWord callerSlot σ_evm I = vowSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hliveWord : vowSlotWord ⟨12⟩ σ_evm I = vowSlotWord ⟨12⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vowBytecode) (sel := sel) (entry := ⟨517⟩) (ret := ⟨412⟩)
    (decoded := ⟨539⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := vowBytecode) (decoded := ⟨539⟩) (ret := ⟨412⟩) (routine := ⟨2294⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  by_cases hauthEvm : vowSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : vowSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
    obtain ⟨_, _, hafterAuth⟩ := RD.vowAuthCheckOk
      (code := vowBytecode) (pc := ⟨2294⟩) (okPc := ⟨2383⟩) (key := key)
      (ret := ⟨412⟩) (R := [sel])
      (by simpa [key, relyKey] using hroutine)
      (by
        unfold vowAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by jump_dest) (by simp)
    by_cases hliveEvm : vowSlotWord ⟨12⟩ σ_evm I = ⟨1⟩
    · have hliveSolm : vowSlotWord ⟨12⟩ σ_solm I = ⟨1⟩ := by
        rw [← hliveWord]
        exact hliveEvm
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (relySlotFor I) ⟨1⟩
      have hbody :
          ExecTransitionBody config contract evm0 locals relyTransition.body
            (.returned { contract := contract, locals := locals } evm1 none) := by
        have hguardAuth := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals]) hauthSolm
        have hguardLive := vowLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals]) hliveSolm
        have hassign :
            assignStorageRef? config { contract := contract, locals := locals } evm0
              .storage (wardsRef (.var "usr")) (.int 1) =
                .ok ({ contract := contract, locals := locals }, evm1) := by
          have her :
              evalStorageRef config { contract := contract, locals := locals } evm0
                (wardsRef (.var "usr")) = .ok (relyEvaledRef I) := by
            simp [evm0, relyEvaledRef, relyUsr, wardsRef, evalStorageRef,
              evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
              EvalResult.ofOption, EvalResult.bind, pure, bind, locals]
          have hstore :
              storageLocStore evm0 (wordLoc (relySlotFor I)) (.int 1) = some evm1 := by
            simpa [evm1] using storageLocStore_uint256 evm0 (relySlotFor I) ⟨1⟩
          exact assignStorageRef_storage_scalar
            (ty := .elem (.int uint256Int)) (loc := wordLoc (relySlotFor I))
            (hbase := by simp [locals, wardsRef])
            (her := her)
            (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
            (hloc := by
              funext evm
              simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
                relyEvaledRef, relySlotFor])
            (hstore := hstore)
        have hblock :
            ExecBlock config { contract := contract, locals := locals } evm0
              [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
                .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
                .require (.binary .eq (.storage liveRef) (.intLit 1)),
                .assign .storage (wardsRef (.var "usr")) (.intLit 1) ]
              (.ok { contract := contract, locals := locals } evm1) := by
          refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
          · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
          refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
          refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
          exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassign)
            ExecBlock.nil
        simpa [ExecTransitionBody, relyTransition, nonpayable, auth, evm0, evm1] using
          ExecFuncBody.execBlockOK hblock
      have hliveSolc : solcSlotWord σ_evm I ⟨12⟩ = ⟨1⟩ := by
        simpa [vowSlotWord] using hliveEvm
      obtain ⟨_, _, hstorePc⟩ := RD.vowLiveGuardOk
        (code := vowBytecode) (pc := ⟨2383⟩) (okPc := ⟨2453⟩) (key := key)
        (ret := ⟨412⟩) (R := [sel]) hafterAuth
        (by
          unfold vowLiveGuardWf
          repeat' first | apply And.intro | native_decide)
        hliveSolc (by jump_dest) (by simp)
      have hmemAuth :
          (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
        twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      have hcanonKey : key.toNat < EVM.addressModulus := by
        dsimp [key, relyKey]
        rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
        exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
      obtain ⟨_, _, hretPc⟩ := RD.vowRelyStoreOne
        (code := vowBytecode) (pc := ⟨2453⟩) (key := key) (ret := ⟨412⟩) (R := [sel])
        hstorePc
        (by
          unfold vowRelyStoreOneWf
          repeat' first | apply And.intro | native_decide)
        (by jump_dest) hperm hmemAuth hcanonKey (by simp)
      have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
      have hret :
          RDret vowBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨1⟩) ByteArray.empty := by
        simpa [slot] using RD.stop hretPc' (by native_decide) (by simp)
      have hcreated :
          (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨1⟩).1 = evm1.createdAccounts := by
        simp [evm1, evm0, initState, storageStore_createdAccounts]
      have haccounts :
          accountMapEquiv (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨1⟩).2
            evm1.accountMap := by
        simpa [evm1, evm0, initState, storageStore_accountMap, hslot] using
          accountMapEquiv_sstoreAccountMap I.codeOwner slot ⟨1⟩ hAccounts
      have henc : returnEquiv ByteArray.empty none relyTransition.returnType := by
        rw [show relyTransition.returnType = [] by rfl]
        exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
      exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
        hcreated haccounts henc
    · have hliveSolm : vowSlotWord ⟨12⟩ σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hliveEvm (by rw [hliveWord, hsolm])
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody : ExecTransitionBody config contract evm0 locals relyTransition.body .reverted := by
        have hguardAuth := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals]) hauthSolm
        have hguardLive := vowLiveGuardEval_false (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals]) hliveSolm
        have hblock :
            ExecBlock config { contract := contract, locals := locals } evm0
              [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
                .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
                .require (.binary .eq (.storage liveRef) (.intLit 1)),
                .assign .storage (wardsRef (.var "usr")) (.intLit 1) ]
              .reverted := by
          refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
          · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
          refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
          exact ExecBlock.consRevert (ExecStmt.requireFalse hguardLive)
        simpa [ExecTransitionBody, relyTransition, nonpayable, auth, evm0] using
          ExecFuncBody.execBlockRevert hblock
      have hliveSolc : solcSlotWord σ_evm I ⟨12⟩ ≠ ⟨1⟩ := by
        simpa [vowSlotWord] using hliveEvm
      have hmemAuth :
          (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
        twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      have hread64 :
          (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
            UInt256.toByteArray ⟨128⟩ :=
        twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
          solcFreePtrMem_read64
      have hrev := RD.vowLiveGuardRevert
        (code := vowBytecode) (pc := ⟨2383⟩) (okPc := ⟨2453⟩) (key := key)
        (ret := ⟨412⟩) (R := [sel]) hafterAuth
        (by
          unfold vowLiveGuardWf
          repeat' first | apply And.intro | native_decide)
        (by
          unfold solcErrorStringRevertTailWf vowLiveGuardTailPc vowNotLiveRawWord
          repeat' first | apply And.intro | native_decide)
        hliveSolc hmemAuth hread64 (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hauthSolm : vowSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody : ExecTransitionBody config contract evm0 locals relyTransition.body .reverted := by
      have hguard := vowAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [
          .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .assign .storage (wardsRef (.var "usr")) (.intLit 1)])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, relyTransition, nonpayable, auth, evm0] using
        ExecFuncBody.execBlockRevert hblock
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
    have hrev := RD.vowAuthCheckRevert
      (code := vowBytecode) (pc := ⟨2294⟩) (okPc := ⟨2383⟩) (key := key)
      (ret := ⟨412⟩) (R := [sel])
      (by simpa [key, relyKey] using hroutine)
      (by
        unfold vowAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold solcErrorStringRevertTailWf vowAuthTailPc vowNotAuthorizedRawWord
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by simp)
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowRelyBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := by omega
  exact vowRelyBodyCore hcode hwv hperm hsz36 hsize (vowDispatch_rely hsel)
    (vowDecode_rely_ok hsz36)
    (vowReachRelyBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts

theorem vowRelyShort {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsel : selIs I ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hreach :=
    vowReachRelyBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vowBytecode) (sel := vowSelWord I) (entry := ⟨517⟩) (ret := ⟨412⟩)
    (decoded := ⟨539⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (vowDispatch_rely hsel)
    (vowDecode_rely_none_short hsz4 hshort)

end Benchmarks.Dss.Vow
