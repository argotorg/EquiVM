import Benchmarks.Dss.Cure.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Cure

/-! ## `rely(address)` -/

abbrev relyUsr (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev relyKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev relyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address (relyUsr I))] }

abbrev relySlotFor (I : ExecutionEnv) : UInt256 :=
  wardsSlot (.address (relyUsr I))

abbrev cureCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

abbrev cureCallerWardsEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address I.source)] }

abbrev cureLiveEvaledRef : EvaledStorageRef :=
  { base := "live", steps := [] }

theorem relySlotFor_eq (I : ExecutionEnv) :
    relySlotFor I = solcMappingSlot ⟨0⟩ (relyKey I) := by
  unfold relySlotFor relyUsr relyKey wardsSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem cureCallerWardsEvaledRef_ok {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (_hbase : locals.get? "wards" = none) :
    evalStorageRef config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (wardsRef sender) =
        .ok (cureCallerWardsEvaledRef I) := by
  simp [cureCallerWardsEvaledRef, wardsRef, sender, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, pure, bind, initState]

theorem cureAuthGuardEval_true {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have her := cureCallerWardsEvaledRef_ok (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  have hload : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      (cureCallerWardsSlot I) = ⟨1⟩ := by
    simpa [cureSlotWord] using hauth
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc (cureCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        cureCallerWardsEvaledRef, cureCallerWardsSlot, wardsSlot, mapSlot, solcMappingSlot,
        keyValueToWord_address, solcSourceWord])]
  rw [cureStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  rw [hload]
  simp [evalExpr?, evalBinaryOp?]
  all_goals decide +native

theorem cureAuthGuardEval_false {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have her := cureCallerWardsEvaledRef_ok (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  let w := Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      (cureCallerWardsSlot I)
  have hload : w ≠ ⟨1⟩ := by
    intro hw
    exact hauth (by simpa [w, cureSlotWord] using hw)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc (cureCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        cureCallerWardsEvaledRef, cureCallerWardsSlot, wardsSlot, mapSlot, solcMappingSlot,
        keyValueToWord_address, solcSourceWord])]
  rw [cureStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  simp [evalExpr?, evalBinaryOp?]
  · intro hnat
    apply hload
    apply u256_inj
    simpa using hnat
  all_goals decide +native

theorem cureLiveGuardEval_true {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "live" = none)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hload : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      ⟨1⟩ = ⟨1⟩ := by
    simpa [cureSlotWord] using hlive
  have her :
      evalStorageRef config { contract := contract, locals := locals }
        (initState cA gh bl σ σ₀ g A I) liveRef = .ok cureLiveEvaledRef := by
    simp [cureLiveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc ⟨1⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, cureLiveEvaledRef])]
  rw [cureStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  rw [hload]
  simp [evalExpr?, evalBinaryOp?]
  all_goals decide +native

theorem cureLiveGuardEval_false {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "live" = none)
    (hlive : cureSlotWord ⟨1⟩ σ I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  let w := Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨1⟩
  have hload : w ≠ ⟨1⟩ := by
    intro hw
    exact hlive (by simpa [w, cureSlotWord] using hw)
  have her :
      evalStorageRef config { contract := contract, locals := locals }
        (initState cA gh bl σ σ₀ g A I) liveRef = .ok cureLiveEvaledRef := by
    simp [cureLiveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc ⟨1⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, cureLiveEvaledRef])]
  rw [cureStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  simp [evalExpr?, evalBinaryOp?]
  · intro hnat
    apply hload
    apply u256_inj
    simpa using hnat
  all_goals decide +native

theorem cureDispatchRely {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 12)) :
    dispatchMsg contract I.calldata = some relyTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 12 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some relyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes,
    cureAmtSelectorBytes, cureCageSelectorBytes, cureDenySelectorBytes,
    cureDropSelectorBytes, cureFileSelectorBytes, cureLCountSelectorBytes,
    cureLiftSelectorBytes, cureListSelectorBytes, cureLiveSelectorBytes,
    cureLoadSelectorBytes, cureLoadedSelectorBytes, curePosSelectorBytes,
    cureRelySelectorBytes]
  decide +native

theorem cureDecode_rely_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "usr" (.address (relyUsr I))) := by
  simpa [config, relyTransition, relyUsr] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36)

theorem cureDecode_rely_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = none := by
  simpa [config, relyTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort)

theorem cureReachRelyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 12)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨594⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x65fae35e⟩ :=
    cureSelWord_eq_of_beq I hsz 0x65 0xfa 0xe3 0x5e ⟨0x65fae35e⟩
      (by decide +native) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h185⟩ := cureReachLowUpperFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; decide +native) (by rw [hsw]; decide +native)
  exact RD.dispatchTo ⟨594⟩ 4 h185 (fun j hj => cureLowUpperArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; decide +native)
    (by rw [hsw]; decide +native) (by jump_dest) (by decide +native) (by simp)

/-! ### Auth and `live` bytecode guard helpers -/

@[reducible] def cureAuthTailPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p9 := p7 + UInt256.ofNat 2
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p20 := p19 + ⟨1⟩
  let p23 := p20 + UInt256.ofNat 3
  p23 + ⟨1⟩

@[reducible] def cureAuthCheckWf (code : ByteArray) (pc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p9 := p7 + UInt256.ofNat 2
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p20 := p19 + ⟨1⟩
  let p23 := p20 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.CALLER, .none)
  ∧ decode code p2 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p4 = some (.SWAP1, .none)
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.MSTORE, .none)
  ∧ decode code p7 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p9 = some (.DUP2, .none)
  ∧ decode code p10 = some (.SWAP1, .none)
  ∧ decode code p11 = some (.MSTORE, .none)
  ∧ decode code p12 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p14 = some (.SWAP1, .none)
  ∧ decode code p15 = some (.KECCAK256, .none)
  ∧ decode code p16 = some (.SLOAD, .none)
  ∧ decode code p17 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p19 = some (.EQ, .none)
  ∧ decode code p20 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code p23 = some (.JUMPI, .none)

abbrev cureNotAuthorizedRawWord : UInt256 :=
  ⟨0x10dd5c994bdb9bdd0b585d5d1a1bdc9a5e9959⟩

theorem RD.cureAuthCheckOk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : cureAuthCheckWf code pc okPc)
    (hauth : solcSlotWord σ ee (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) = ⟨1⟩)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 okPc (key :: ret :: R)
      (twoWordHashMem (solcSourceWord ee) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd9, hd10, hd11, hd12, hd14, hd15,
      hd16, hd17, hd19, hd20, hd23⟩
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw caller hd1 (by evm_ov),
    raw push1 ⟨0⟩ hd2 (by evm_ov),
    raw swap1 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7 := rd6.mstore 0 (wordAt0Mem (solcSourceWord ee) solcFreePtrMem)
    (UInt256.ofNat 3) hd6 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd11 := evm_run rd7 with [
    raw push1 ⟨32⟩ hd7 (by evm_ov),
    raw dup2 hd9 (by evm_ov),
    raw swap1 hd10 (by evm_ov)]
  have rd12 := rd11.mstore 0 (twoWordHashMem (solcSourceWord ee) ⟨0⟩ solcFreePtrMem)
    (UInt256.ofNat 3) hd11 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd15 := evm_run rd12 with [
    raw push1 ⟨64⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ (solcSourceWord ee) solcFreePtrMem_size
  have rd16 := rd15.keccak256 0 (solcMappingSlot ⟨0⟩ (solcSourceWord ee))
    (UInt256.ofNat 3) hd15 mem_cost hslot (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd17⟩ := rd16.sload hd16 (by evm_ov)
  have rd19 := rd17.push1 ⟨1⟩ hd17 (by evm_ov)
  have rd20₀ := rd19.eq hd19 (by evm_ov)
  have hauthRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ⟨0⟩)) = ⟨1⟩ := by
    simpa [solcSlotWord] using hauth
  have rd20 := rd20₀
  rw [hauthRaw, uInt256_eq_self] at rd20
  have rd23 := rd20.push2 okPc hd20 (by evm_ov)
  exact ⟨_, _, rd23.jumpiT hd23 one_ne_zero_uint hok (by evm_ov)⟩

theorem RD.cureAuthCheckRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : cureAuthCheckWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (cureAuthTailPc pc) ⟨19⟩
      cureNotAuthorizedRawWord ⟨106⟩ .PUSH19 19)
    (hauth : solcSlotWord σ ee (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ≠ ⟨1⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd9, hd10, hd11, hd12, hd14, hd15,
      hd16, hd17, hd19, hd20, hd23⟩
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw caller hd1 (by evm_ov),
    raw push1 ⟨0⟩ hd2 (by evm_ov),
    raw swap1 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7 := rd6.mstore 0 (wordAt0Mem (solcSourceWord ee) solcFreePtrMem)
    (UInt256.ofNat 3) hd6 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd11 := evm_run rd7 with [
    raw push1 ⟨32⟩ hd7 (by evm_ov),
    raw dup2 hd9 (by evm_ov),
    raw swap1 hd10 (by evm_ov)]
  have rd12 := rd11.mstore 0 (twoWordHashMem (solcSourceWord ee) ⟨0⟩ solcFreePtrMem)
    (UInt256.ofNat 3) hd11 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd15 := evm_run rd12 with [
    raw push1 ⟨64⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ (solcSourceWord ee) solcFreePtrMem_size
  have rd16 := rd15.keccak256 0 (solcMappingSlot ⟨0⟩ (solcSourceWord ee))
    (UInt256.ofNat 3) hd15 mem_cost hslot (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd17⟩ := rd16.sload hd16 (by evm_ov)
  have rd19 := rd17.push1 ⟨1⟩ hd17 (by evm_ov)
  have rd20₀ := rd19.eq hd19 (by evm_ov)
  have hauthRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ⟨0⟩)) ≠ ⟨1⟩ := by
    simpa [solcSlotWord] using hauth
  have heq0 :
      UInt256.eq ⟨1⟩
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ⟨0⟩)) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h1 => hauthRaw h1.symm)
  have rd20 := rd20₀
  rw [heq0] at rd20
  have rd23 := rd20.push2 okPc hd20 (by evm_ov)
  have rdTail₀ := rd23.jumpiNT hd23 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail (by simpa [cureAuthTailPc] using rdTail₀) htail
    (by decide) (by rfl)
    (twoWordHashMem_size_96 (solcSourceWord ee) ⟨0⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (solcSourceWord ee) ⟨0⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons]; omega)

@[reducible] def cureLiveGuardTailPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  p10 + ⟨1⟩

@[reducible] def cureLiveGuardWf (code : ByteArray) (pc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.EQ, .none)
  ∧ decode code p7 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code p10 = some (.JUMPI, .none)

abbrev cureNotLiveRawWord : UInt256 :=
  ⟨0x437572652f6e6f742d6c697665⟩

theorem RD.cureLiveGuardOk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : cureLiveGuardWf code pc okPc)
    (hlive : solcSlotWord σ ee ⟨1⟩ = ⟨1⟩)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 okPc (key :: ret :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10⟩
  have rd3 := h.jumpdest hd0 (by evm_ov) |>.push1 ⟨1⟩ hd1 (by evm_ov)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by evm_ov)
  have hliveRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) = ⟨1⟩ := by
    simpa [solcSlotWord] using hlive
  rw [hliveRaw] at rd4
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by evm_ov)
  have rd7₀ := rd6.eq hd6 (by evm_ov)
  have rd7 := rd7₀
  rw [uInt256_eq_self] at rd7
  have rd10 := rd7.push2 okPc hd7 (by evm_ov)
  exact ⟨_, _, rd10.jumpiT hd10 one_ne_zero_uint hok (by evm_ov)⟩

theorem RD.cureLiveGuardRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : cureLiveGuardWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (cureLiveGuardTailPc pc) ⟨13⟩
      cureNotLiveRawWord ⟨152⟩ .PUSH13 13)
    (hlive : solcSlotWord σ ee ⟨1⟩ ≠ ⟨1⟩)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10⟩
  have rd3 := h.jumpdest hd0 (by evm_ov) |>.push1 ⟨1⟩ hd1 (by evm_ov)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by evm_ov)
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by evm_ov)
  have rd7₀ := rd6.eq hd6 (by evm_ov)
  have hliveRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) ≠ ⟨1⟩ := by
    simpa [solcSlotWord] using hlive
  have heq0 :
      UInt256.eq ⟨1⟩
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h1 => hliveRaw h1.symm)
  have rd7 := rd7₀
  rw [heq0] at rd7
  have rd10 := rd7.push2 okPc hd7 (by evm_ov)
  have rdTail₀ := rd10.jumpiNT hd10 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail (by simpa [cureLiveGuardTailPc] using rdTail₀) htail
    (by decide) (by rfl) hmem hread64 (by simpa only [List.length_cons] using hov)

/-! ### Event-emitting store helper -/

def cureStLog2 (s : State) (a b c d : UInt256) (t : List UInt256) : State :=
  {s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG2)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat
            + 2 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

theorem cureLog2_xstep {s : State} {code : ByteArray} {pcv a b c d : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG2, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat
            < memoryExpansionCost s .LOG2
              + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
         then .error .OutOfGass else .ok (cureStLog2 s a b c d t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG2, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_log2 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: t).length - 4 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, cureStLog2]

theorem RD.cureLog2 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG2, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: t →
        memoryExpansionCost s .LOG2 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 2 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG2 = mcost := hmc s haw hstk
    have hperms : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have st := cureLog2_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨cureStLog2 s a b c d t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [cureStLog2]; exact hcode
      · simp only [cureStLog2]; rw [hpc]
      · simp only [cureStLog2]
      · simp only [cureStLog2, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [cureStLog2]; exact hmem
      · simp only [cureStLog2]; rw [haw, hawout]
      · simp only [cureStLog2]; exact hrdata
      · simp only [cureStLog2]; exact hacc
      · exact hee
      · simp only [cureStLog2]
        exact hworld

abbrev cureRelyEventTopic : UInt256 :=
  ⟨0xdd0e34038ac38b2a1ce960229778ac48a8719bc900b6c4f8d0475c6e8b385a60⟩

theorem RD.cureRelyStoreOne {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2506⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata (cA, σ) k C)
    (hret : (D_J cureBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ret R (twoWordHashMem key ⟨0⟩ mem)
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨0⟩ key) ⟨1⟩) k' C' := by
  have hmask : UInt256.land solcAddrMask key = key :=
    solcAddrMask_clean_left hcanonKey
  have hmaskLiteral :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) key =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hmaskLiteral' :
      UInt256.land key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        key := by
    rw [u256_land_comm key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)]
    exact hmaskLiteral
  have rdMasked := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov)]
  rw [hmaskLiteral'] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨0⟩ mem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by
      simpa only [List.length_cons] using hov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) (by decide +native) mem_cost hslot (by decide +native) (by evm_ov)
  have rdBeforeStore := evm_run rdSlot with [
    raw push1 ⟨1⟩ (by decide +native) (by
      change R.length + 6 < 1024
      omega),
    raw swap1 (by decide +native) (by
      simpa only [List.length_cons] using hov)]
  obtain ⟨_, _, rdAfterStore⟩ := rdBeforeStore.sstore hperm (by decide +native)
    (by simp only [List.length_cons]; omega)
  have hread64' :
      (twoWordHashMem key ⟨0⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 key ⟨0⟩ hmem hread64
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (twoWordHashMem key ⟨0⟩ mem).size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩
        then ⟨0⟩ else UInt256.ofNat (fromByteArrayBigEndian
          ((twoWordHashMem key ⟨0⟩ mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
    rw [if_neg (by
      rw [twoWordHashMem_size_96 key ⟨0⟩ hmem]
      decide +native)]
    rw [show (⟨64⟩ : UInt256).toNat = 64 from rfl, hread64']
    decide +native
  have rdMload := rdAfterStore.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
    mem_cost hmload64 (by decide +native) (by evm_ov)
  have rdTopic := rdMload.pushConst cureRelyEventTopic
    (op := .PUSH32) (width := 32) (by decide) (by decide +native) (by evm_ov)
  have rdLogPrefix := evm_run rdTopic with [
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rdLogged := RD.cureLog2 0 (UInt256.ofNat 3) rdLogPrefix
    (by decide +native) hperm mem_cost (by decide +native) (by evm_ov)
  have rdPop := rdLogged.pop (by decide +native) (by evm_ov)
  exact ⟨_, _, rdPop.jump (by decide +native) hret (by evm_ov)⟩

theorem cureRelyBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 12))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let sel := cureSelWord I
  let key := relyKey I
  let slot := solcMappingSlot ⟨0⟩ key
  let callerSlot := cureCallerWardsSlot I
  let locals : Store := (∅ : Store).insert "usr" (.address (relyUsr I))
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 12) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some relyTransition :=
    cureDispatchRely hsel
  have hreach := cureReachRelyBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode :
        decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
          (transitionSignature relyTransition).paramTypes I.calldata =
            some ((∅ : Store).insert "usr" (.address (relyUsr I))) :=
      cureDecode_rely_ok hsz36
    have hslot : relySlotFor I = slot := by
      simp [slot, key, relySlotFor_eq]
    have hcallerWord : cureSlotWord callerSlot σ_evm I = cureSlotWord callerSlot σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
    have hliveWord : cureSlotWord ⟨1⟩ σ_evm I = cureSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
      (code := cureBytecode) (sel := sel) (entry := ⟨594⟩) (ret := ⟨484⟩)
      (decoded := ⟨616⟩) hreach
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by jump_dest) hsz36 hsize
    obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
      (code := cureBytecode) (decoded := ⟨616⟩) (ret := ⟨484⟩) (routine := ⟨2345⟩)
      (R := [sel]) hdecoded
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by jump_dest) (by simp)
    by_cases hauthEvm : cureSlotWord callerSlot σ_evm I = ⟨1⟩
    · have hauthSolm : cureSlotWord callerSlot σ_solm I = ⟨1⟩ := by
        rw [← hcallerWord]
        exact hauthEvm
      have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
        simpa [callerSlot, cureCallerWardsSlot, cureSlotWord] using hauthEvm
      obtain ⟨_, _, hafterAuth⟩ := RD.cureAuthCheckOk
        (code := cureBytecode) (pc := ⟨2345⟩) (okPc := ⟨2435⟩) (key := key)
        (ret := ⟨484⟩) (R := [sel])
        (by simpa [key, relyKey] using hroutine)
        (by
          unfold cureAuthCheckWf
          repeat' first | apply And.intro | decide +native)
        hauthSolc (by jump_dest) (by simp)
      by_cases hliveEvm : cureSlotWord ⟨1⟩ σ_evm I = ⟨1⟩
      · have hliveSolm : cureSlotWord ⟨1⟩ σ_solm I = ⟨1⟩ := by
          rw [← hliveWord]
          exact hliveEvm
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (relySlotFor I) ⟨1⟩
        have hbody :
            ExecTransitionBody config contract evm0 locals relyTransition.body
              (.returned { contract := contract, locals := locals } evm1 none) := by
          have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := locals)
            (by simp [locals]) hauthSolm
          have hguardLive := cureLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
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
        have hliveSolc : solcSlotWord σ_evm I ⟨1⟩ = ⟨1⟩ := by
          simpa [cureSlotWord] using hliveEvm
        obtain ⟨_, _, hstorePc⟩ := RD.cureLiveGuardOk
          (code := cureBytecode) (pc := ⟨2435⟩) (okPc := ⟨2506⟩) (key := key)
          (ret := ⟨484⟩) (R := [sel]) hafterAuth
          (by
            unfold cureLiveGuardWf
            repeat' first | apply And.intro | decide +native)
          hliveSolc (by jump_dest) (by simp)
        have hmemAuth :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
          twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
        have hread64 :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
            solcFreePtrMem_read64
        have hcanonKey : key.toNat < EVM.addressModulus := by
          dsimp [key, relyKey]
          rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
          exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
        obtain ⟨_, _, hretPc⟩ := RD.cureRelyStoreOne
          (g := Sat256.ofUInt256 g) (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (ee := I) (key := key) (ret := ⟨484⟩) (R := [sel])
          hstorePc (by jump_dest) hperm hmemAuth hread64 hcanonKey (by simp)
        have hretPc' := hretPc.jumpdest (by decide +native) (by evm_ov)
        have hret :
            RDret cureBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨1⟩) ByteArray.empty := by
          simpa [slot] using RD.stop hretPc' (by decide +native) (by simp)
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
          exact returnEquiv.fallthrough rfl (by rfl) (by decide +native)
        exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
          hcreated haccounts henc
      · have hliveSolm : cureSlotWord ⟨1⟩ σ_solm I ≠ ⟨1⟩ := by
          intro hsolm
          exact hliveEvm (by rw [hliveWord, hsolm])
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hbody : ExecTransitionBody config contract evm0 locals relyTransition.body .reverted := by
          have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := locals)
            (by simp [locals]) hauthSolm
          have hguardLive := cureLiveGuardEval_false (cA := cA) (gh := gh) (bl := bl)
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
        have hliveSolc : solcSlotWord σ_evm I ⟨1⟩ ≠ ⟨1⟩ := by
          simpa [cureSlotWord] using hliveEvm
        have hmemAuth :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
          twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
        have hread64 :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
            solcFreePtrMem_read64
        have hrev := RD.cureLiveGuardRevert
          (code := cureBytecode) (pc := ⟨2435⟩) (okPc := ⟨2506⟩) (key := key)
          (ret := ⟨484⟩) (R := [sel]) hafterAuth
          (by
            unfold cureLiveGuardWf
            repeat' first | apply And.intro | decide +native)
          (by
            unfold solcErrorStringRevertTailWf cureLiveGuardTailPc cureNotLiveRawWord
            repeat' first | apply And.intro | decide +native)
          hliveSolc hmemAuth hread64 (by simp)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : cureSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hauthEvm (by rw [hcallerWord, hsolm])
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody : ExecTransitionBody config contract evm0 locals relyTransition.body .reverted := by
        have hguard := cureAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
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
        simpa [callerSlot, cureCallerWardsSlot, cureSlotWord] using hauthEvm
      have hrev := RD.cureAuthCheckRevert
        (code := cureBytecode) (pc := ⟨2345⟩) (okPc := ⟨2435⟩) (key := key)
        (ret := ⟨484⟩) (R := [sel])
        (by simpa [key, relyKey] using hroutine)
        (by
          unfold cureAuthCheckWf
          repeat' first | apply And.intro | decide +native)
        (by
          unfold solcErrorStringRevertTailWf cureAuthTailPc cureNotAuthorizedRawWord
          repeat' first | apply And.intro | decide +native)
        hauthSolc (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hlt :
        UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
      apply ult_one
      rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
      change I.calldata.size - 4 < 32
      omega
    have hrev := RD.solcExternalStaticArgsShortReverts
      (code := cureBytecode) (sel := sel) (entry := ⟨594⟩) (ret := ⟨484⟩)
      (decoded := ⟨616⟩) (need := ⟨32⟩) hreach
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) hlt
    exact hrev.reEquivDecodingFailed hcode hdispatch
      (cureDecode_rely_none_short hsz4 (by omega))

end Benchmarks.Dss.Cure
