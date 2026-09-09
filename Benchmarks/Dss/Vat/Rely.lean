import Benchmarks.Dss.Vat.Nope

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vat

/-! ## `rely(address)` -/

abbrev relyUsr (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev relyKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev relyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address (relyUsr I))] }

abbrev relySlotFor (I : ExecutionEnv) : UInt256 :=
  wardsSlot (.address (relyUsr I))

abbrev vatCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (hopeSourceWord I)

abbrev vatCallerWardsEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address I.source)] }

abbrev vatLiveEvaledRef : EvaledStorageRef :=
  { base := "live", steps := [] }

theorem relySlotFor_eq (I : ExecutionEnv) :
    relySlotFor I = solcMappingSlot ⟨0⟩ (relyKey I) := by
  unfold relySlotFor relyUsr relyKey wardsSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem byteArray_write_from_zero_size_of_cover
    (src base : ByteArray) (srcAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) (hbase : len ≤ base.size) :
    (src.write srcAddr base 0 len).size = base.size := by
  rw [write_eq_gen_from src base srcAddr 0 len hlen hsrc (by simpa using hbase)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract]
  omega

theorem vatCallerWardsEvaledRef_ok {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (_hbase : locals.get? "wards" = none) :
    evalStorageRef config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (wardsRef sender) =
        .ok (vatCallerWardsEvaledRef I) := by
  simp [vatCallerWardsEvaledRef, wardsRef, sender, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, pure, bind, initState]

theorem vatAuthGuardEval_true {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have her := vatCallerWardsEvaledRef_ok (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  have hload : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      (vatCallerWardsSlot I) = ⟨1⟩ := by
    simpa [vatSlotWord] using hauth
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc (vatCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        vatCallerWardsEvaledRef, vatCallerWardsSlot, wardsSlot, mapSlot, solcMappingSlot,
        keyValueToWord_address, hopeSourceWord])]
  rw [vatStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  rw [hload]
  simp [evalExpr?, evalBinaryOp?]
  all_goals decide +native

theorem vatAuthGuardEval_false {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have her := vatCallerWardsEvaledRef_ok (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  let w := Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      (vatCallerWardsSlot I)
  have hload : w ≠ ⟨1⟩ := by
    intro hw
    exact hauth (by simpa [w, vatSlotWord] using hw)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc (vatCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        vatCallerWardsEvaledRef, vatCallerWardsSlot, wardsSlot, mapSlot, solcMappingSlot,
        keyValueToWord_address, hopeSourceWord])]
  rw [vatStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  simp [evalExpr?, evalBinaryOp?]
  · intro hnat
    apply hload
    apply u256_inj
    simpa using hnat
  all_goals decide +native

theorem vatLiveGuardEval_true {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "live" = none)
    (hlive : vatSlotWord ⟨10⟩ σ I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hload : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      ⟨10⟩ = ⟨1⟩ := by
    simpa [vatSlotWord] using hlive
  have her :
      evalStorageRef config { contract := contract, locals := locals }
        (initState cA gh bl σ σ₀ g A I) liveRef = .ok vatLiveEvaledRef := by
    simp [vatLiveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc ⟨10⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, vatLiveEvaledRef])]
  rw [vatStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  rw [hload]
  simp [evalExpr?, evalBinaryOp?]
  all_goals decide +native

theorem vatLiveGuardEval_false {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "live" = none)
    (hlive : vatSlotWord ⟨10⟩ σ I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  let w := Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨10⟩
  have hload : w ≠ ⟨1⟩ := by
    intro hw
    exact hlive (by simpa [w, vatSlotWord] using hw)
  have her :
      evalStorageRef config { contract := contract, locals := locals }
        (initState cA gh bl σ σ₀ g A I) liveRef = .ok vatLiveEvaledRef := by
    simp [vatLiveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc ⟨10⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, vatLiveEvaledRef])]
  rw [vatStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  simp [evalExpr?, evalBinaryOp?]
  · intro hnat
    apply hload
    apply u256_inj
    simpa using hnat
  all_goals decide +native

/-! ### Auth, live, and store bytecode helpers -/

@[reducible] def vatAuthTailPc (pc : UInt256) : UInt256 :=
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

@[reducible] def vatAuthRevertTailWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p8 := p4 + UInt256.ofNat 4
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p24 := p22 + UInt256.ofNat 2
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p29 := p27 + UInt256.ofNat 2
  let p30 := p29 + ⟨1⟩
  let p31 := p30 + ⟨1⟩
  let p33 := p31 + UInt256.ofNat 2
  let p36 := p33 + UInt256.ofNat 3
  let p37 := p36 + ⟨1⟩
  let p38 := p37 + ⟨1⟩
  let p39 := p38 + ⟨1⟩
  let p40 := p39 + ⟨1⟩
  let p41 := p40 + ⟨1⟩
  let p42 := p41 + ⟨1⟩
  let p44 := p42 + UInt256.ofNat 2
  let p45 := p44 + ⟨1⟩
  let p46 := p45 + ⟨1⟩
  let p47 := p46 + ⟨1⟩
  let p48 := p47 + ⟨1⟩
  let p49 := p48 + ⟨1⟩
  let p50 := p49 + ⟨1⟩
  let p51 := p50 + ⟨1⟩
  let p52 := p51 + ⟨1⟩
  let p53 := p52 + ⟨1⟩
  let p55 := p53 + UInt256.ofNat 2
  let p56 := p55 + ⟨1⟩
  let p57 := p56 + ⟨1⟩
  decode code pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p2 = some (.DUP1, .none)
  ∧ decode code p3 = some (.MLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode code p10 = some (.SHL, .none)
  ∧ decode code p11 = some (.DUP2, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p17 = some (.DUP3, .none)
  ∧ decode code p18 = some (.ADD, .none)
  ∧ decode code p19 = some (.MSTORE, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (⟨18⟩, 1))
  ∧ decode code p22 = some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode code p24 = some (.DUP3, .none)
  ∧ decode code p25 = some (.ADD, .none)
  ∧ decode code p26 = some (.MSTORE, .none)
  ∧ decode code p27 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p29 = some (.DUP1, .none)
  ∧ decode code p30 = some (.MLOAD, .none)
  ∧ decode code p31 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p33 = some (.Push .PUSH2, some (⟨6921⟩, 2))
  ∧ decode code p36 = some (.DUP4, .none)
  ∧ decode code p37 = some (.CODECOPY, .none)
  ∧ decode code p38 = some (.DUP2, .none)
  ∧ decode code p39 = some (.MLOAD, .none)
  ∧ decode code p40 = some (.SWAP2, .none)
  ∧ decode code p41 = some (.MSTORE, .none)
  ∧ decode code p42 = some (.Push .PUSH1, some (⟨68⟩, 1))
  ∧ decode code p44 = some (.DUP3, .none)
  ∧ decode code p45 = some (.ADD, .none)
  ∧ decode code p46 = some (.MSTORE, .none)
  ∧ decode code p47 = some (.SWAP1, .none)
  ∧ decode code p48 = some (.MLOAD, .none)
  ∧ decode code p49 = some (.SWAP1, .none)
  ∧ decode code p50 = some (.DUP2, .none)
  ∧ decode code p51 = some (.SWAP1, .none)
  ∧ decode code p52 = some (.SUB, .none)
  ∧ decode code p53 = some (.Push .PUSH1, some (⟨100⟩, 1))
  ∧ decode code p55 = some (.ADD, .none)
  ∧ decode code p56 = some (.SWAP1, .none)
  ∧ decode code p57 = some (.REVERT, .none)

@[reducible] def vatAuthCheckWf (code : ByteArray) (pc okPc : UInt256) : Prop :=
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

@[reducible] def vatLiveGuardTailPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  p10 + ⟨1⟩

@[reducible] def vatLiveGuardWf (code : ByteArray) (pc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨10⟩, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.EQ, .none)
  ∧ decode code p7 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code p10 = some (.JUMPI, .none)

abbrev vatNotAuthorizedRawWord : UInt256 :=
  ⟨1882396589317237868685917121345356193241433⟩

abbrev vatNotLiveRawWord : UInt256 :=
  ⟨26733525318604986088499541605⟩

abbrev vatNotAuthorizedWord : UInt256 :=
  ⟨39071091024768335266234219561122754275910411055245600260076817361237725675520⟩

theorem RD.vatAuthCheckOk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vatAuthCheckWf code pc okPc)
    (hauth : solcSlotWord σ ee (solcMappingSlot ⟨0⟩ (hopeSourceWord ee)) = ⟨1⟩)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 okPc (key :: ret :: R)
      (twoWordHashMem (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem)
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
  have rd7 := rd6.mstore 0 (wordAt0Mem (hopeSourceWord ee) solcFreePtrMem)
    (UInt256.ofNat 3) hd6 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd11 := evm_run rd7 with [
    raw push1 ⟨32⟩ hd7 (by evm_ov),
    raw dup2 hd9 (by evm_ov),
    raw swap1 hd10 (by evm_ov)]
  have rd12 := rd11.mstore 0 (twoWordHashMem (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem)
    (UInt256.ofNat 3) hd11 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd15 := evm_run rd12 with [
    raw push1 ⟨64⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ (hopeSourceWord ee) solcFreePtrMem_size
  have rd16 := rd15.keccak256 0 (solcMappingSlot ⟨0⟩ (hopeSourceWord ee))
    (UInt256.ofNat 3) hd15 mem_cost hslot (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd17⟩ := rd16.sload hd16 (by evm_ov)
  have rd19 := rd17.push1 ⟨1⟩ hd17 (by evm_ov)
  have rd20₀ := rd19.eq hd19 (by evm_ov)
  have hauthRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (hopeSourceWord ee)) ⟨0⟩)) = ⟨1⟩ := by
    simpa [solcSlotWord] using hauth
  have rd20 := rd20₀
  rw [hauthRaw, uInt256_eq_self] at rd20
  have rd23 := rd20.push2 okPc hd20 (by evm_ov)
  exact ⟨_, _, rd23.jumpiT hd23 one_ne_zero_uint hok (by evm_ov)⟩

theorem RD.vatAuthCheckRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vatAuthCheckWf vatBytecode pc okPc)
    (htail : vatAuthRevertTailWf vatBytecode (vatAuthTailPc pc))
    (hauth : solcSlotWord σ ee (solcMappingSlot ⟨0⟩ (hopeSourceWord ee)) ≠ ⟨1⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev vatBytecode g s0 := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd9, hd10, hd11, hd12, hd14, hd15,
      hd16, hd17, hd19, hd20, hd23⟩
  rcases htail with
    ⟨ht0, ht2, ht3, ht4, ht8, ht10, ht11, ht12, ht13, ht15, ht17, ht18,
      ht19, ht20, ht22, ht24, ht25, ht26, ht27, ht29, ht30, ht31, ht33,
      ht36, ht37, ht38, ht39, ht40, ht41, ht42, ht44, ht45, ht46, ht47,
      ht48, ht49, ht50, ht51, ht52, ht53, ht55, ht56, ht57⟩
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw caller hd1 (by evm_ov),
    raw push1 ⟨0⟩ hd2 (by evm_ov),
    raw swap1 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7 := rd6.mstore 0 (wordAt0Mem (hopeSourceWord ee) solcFreePtrMem)
    (UInt256.ofNat 3) hd6 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd11 := evm_run rd7 with [
    raw push1 ⟨32⟩ hd7 (by evm_ov),
    raw dup2 hd9 (by evm_ov),
    raw swap1 hd10 (by evm_ov)]
  have rd12 := rd11.mstore 0 (twoWordHashMem (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem)
    (UInt256.ofNat 3) hd11 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd15 := evm_run rd12 with [
    raw push1 ⟨64⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ (hopeSourceWord ee) solcFreePtrMem_size
  have rd16 := rd15.keccak256 0 (solcMappingSlot ⟨0⟩ (hopeSourceWord ee))
    (UInt256.ofNat 3) hd15 mem_cost hslot (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd17⟩ := rd16.sload hd16 (by evm_ov)
  have rd19 := rd17.push1 ⟨1⟩ hd17 (by evm_ov)
  have rd20₀ := rd19.eq hd19 (by evm_ov)
  have hauthRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (hopeSourceWord ee)) ⟨0⟩)) ≠ ⟨1⟩ := by
    simpa [solcSlotWord] using hauth
  have heq0 :
      UInt256.eq ⟨1⟩
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (solcMappingSlot ⟨0⟩ (hopeSourceWord ee)) ⟨0⟩)) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h1 => hauthRaw h1.symm)
  have rd20 := rd20₀
  rw [heq0] at rd20
  have rd23 := rd20.push2 okPc hd20 (by evm_ov)
  have rdTail₀ := rd23.jumpiNT hd23 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rdTail := by
    simpa [vatAuthTailPc] using rdTail₀
  have hmem :
      (twoWordHashMem (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  have rdMload := evm_run rdTail with [
    raw push1 ⟨64⟩ ht0 (by evm_ov),
    raw dup1 ht2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) ht3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) ht4 (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ ht8 (by evm_ov),
    raw shl ht10 (by evm_ov),
    raw dup2 ht11 (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 (twoWordHashMem (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem))
      (UInt256.ofNat 5) ht12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ ht13 (by evm_ov),
    raw push1 ⟨4⟩ ht15 (by evm_ov),
    raw dup3 ht17 (by evm_ov),
    raw add ht18 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 (twoWordHashMem (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem))
      (UInt256.ofNat 6) ht19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨18⟩ ht20 (by evm_ov),
    raw push1 ⟨36⟩ ht22 (by evm_ov),
    raw dup3 ht24 (by evm_ov),
    raw add ht25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨18⟩
      (twoWordHashMem (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem))
      (UInt256.ofNat 7) ht26 mem_cost (by rfl) (by decide) (by evm_ov)]
  let baseMem : ByteArray :=
    solcErrorStringMem2 ⟨18⟩
      (twoWordHashMem (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem)
  have hbaseSize : baseMem.size = 196 := by
    dsimp [baseMem]
    exact solcErrorStringMem2_size ⟨18⟩ hmem
  have hbaseRead0 :
      baseMem.readWithPadding 0 32 = UInt256.toByteArray (hopeSourceWord ee) := by
    dsimp [baseMem]
    unfold solcErrorStringMem2
    rw [toByteArray_write_read_below_of_gap ⟨18⟩
      (solcErrorStringMem1 (twoWordHashMem (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem))
      164 0]
    · unfold solcErrorStringMem1
      rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256)
        (solcErrorStringMem0 (twoWordHashMem (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem))
        132 0]
      · unfold solcErrorStringMem0
        rw [toByteArray_write_read_below_of_gap solcErrorStringSelector
          (twoWordHashMem (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem) 128 0]
        · exact twoWordHashMem_read0 (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem_size
        · rw [hmem]; omega
        · omega
        · rw [hmem]; exact lt_usize _ (by norm_num)
      · rw [solcErrorStringMem0_size hmem]; omega
      · omega
      · rw [solcErrorStringMem0_size hmem]; exact lt_usize _ (by norm_num)
    · rw [solcErrorStringMem1_size hmem]; omega
    · omega
    · rw [solcErrorStringMem1_size hmem]; exact lt_usize _ (by norm_num)
  have hbaseRead64 :
      baseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [baseMem]
    unfold solcErrorStringMem2
    rw [toByteArray_write_read_below_of_gap ⟨18⟩
      (solcErrorStringMem1 (twoWordHashMem (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem))
      164 64
      (by
        have hsz := solcErrorStringMem1_size hmem
        omega)
      (by omega)
      (by
        have hsz := solcErrorStringMem1_size hmem
        rw [hsz]
        exact lt_usize _ (by norm_num))]
    unfold solcErrorStringMem1
    rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256)
      (solcErrorStringMem0 (twoWordHashMem (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem))
      132 64
      (by
        have hsz := solcErrorStringMem0_size hmem
        omega)
      (by omega)
      (by
        have hsz := solcErrorStringMem0_size hmem
        rw [hsz]
        exact lt_usize _ (by norm_num))]
    unfold solcErrorStringMem0
    rw [toByteArray_write_read_below_of_gap solcErrorStringSelector
      (twoWordHashMem (hopeSourceWord ee) ⟨0⟩ solcFreePtrMem) 128 64
      (by omega)
      (by omega)
      (by
        rw [hmem]
        exact lt_usize _ (by norm_num))]
    exact hread64
  have hbaseMload0 :
      (if (⟨0⟩ : UInt256).toNat ≥ baseMem.size
          ∨ (⟨0⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (baseMem.readWithPadding (⟨0⟩ : UInt256).toNat 32)))
        = hopeSourceWord ee := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨0⟩ : UInt256)) (aw := UInt256.ofNat 7)
      (v := hopeSourceWord ee)
      (by rw [hbaseSize]; decide)
      (by decide)
      (by simpa using hbaseRead0)
  let copiedMem : ByteArray :=
    (UInt256.toByteArray vatNotAuthorizedWord).write 0 baseMem 0 32
  have hcodecopyMem :
      vatBytecode.write 6921 baseMem 0 32 = copiedMem := by
    have hsrc : 6921 + 32 ≤ vatBytecode.size := by
      rw [vatBytecode_size]
      norm_num
    have hwordExtract :
        vatBytecode.extract 6921 (6921 + 32) =
          (UInt256.toByteArray vatNotAuthorizedWord).extract 0 32 := by
      rw [vatBytecode_notAuthorized_extract]
      decide +native
    dsimp [copiedMem]
    rw [write_eq_gen_from vatBytecode baseMem 6921 0 32
      (by decide) hsrc (by rw [hbaseSize]; norm_num)]
    rw [write32_eq (UInt256.toByteArray vatNotAuthorizedWord) baseMem 0
      (by rw [toByteArray_size]) (by rw [hbaseSize]; omega)]
    rw [hwordExtract]
  have hcopyRead :
      copiedMem.readWithPadding 0 32 = UInt256.toByteArray vatNotAuthorizedWord := by
    dsimp [copiedMem]
    exact toByteArray_write32_read_back baseMem vatNotAuthorizedWord 0
      (by rw [hbaseSize]; omega)
  have hcopySize : 0 < copiedMem.size := by
    dsimp [copiedMem]
    rw [toByteArray_write32_size_of_le baseMem vatNotAuthorizedWord 0 196 196
      hbaseSize (by omega) (by omega)]
    norm_num
  have hcopyMload :
      (if (⟨0⟩ : UInt256).toNat ≥ copiedMem.size
          ∨ (⟨0⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (copiedMem.readWithPadding (⟨0⟩ : UInt256).toNat 32)))
        = vatNotAuthorizedWord := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨0⟩ : UInt256)) (aw := UInt256.ofNat 7)
      (v := vatNotAuthorizedWord)
      (by simpa using hcopySize)
      (by decide)
      (by simpa using hcopyRead)
  have hcopyRead64 :
      copiedMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [copiedMem]
    rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [hbaseSize]; omega) (by omega) (by rw [hbaseSize]; omega)]
    exact hbaseRead64
  have hcopySizeEq : copiedMem.size = 196 := by
    dsimp [copiedMem]
    rw [toByteArray_write32_size_of_le baseMem vatNotAuthorizedWord 0 196 196
      hbaseSize (by omega) (by omega)]
  let restoredMem : ByteArray :=
    (UInt256.toByteArray (hopeSourceWord ee)).write 0 copiedMem 0 32
  have hrestoredSize : restoredMem.size = 196 := by
    dsimp [restoredMem]
    rw [toByteArray_write32_size_of_le copiedMem (hopeSourceWord ee) 0 196 196
      hcopySizeEq (by omega) (by omega)]
  have hrestoredRead64 :
      restoredMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [restoredMem]
    rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [hcopySizeEq]; omega) (by omega) (by rw [hcopySizeEq]; omega)]
    exact hcopyRead64
  let finalMem : ByteArray :=
    (UInt256.toByteArray vatNotAuthorizedWord).write 0 restoredMem 196 32
  have hfinalRead64 :
      finalMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [finalMem]
    rw [toByteArray_write_read_below_of_gap vatNotAuthorizedWord restoredMem 196 64]
    · exact hrestoredRead64
    · rw [hrestoredSize]; omega
    · omega
    · rw [hrestoredSize]; exact lt_usize _ (by norm_num)
  have hfinalMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ finalMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (finalMem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩ := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 8) (v := (⟨128⟩ : UInt256))
      (by
        dsimp [finalMem]
        rw [toByteArray_write32_size_of_le restoredMem vatNotAuthorizedWord 196 196 228
          hrestoredSize (by omega) (by omega)]
        decide)
      (by decide)
      (by simpa using hfinalRead64)
  have rdCopied := evm_run rdPrefix with [
    raw push1 ⟨0⟩ ht27 (by evm_ov),
    raw dup1 ht29 (by evm_ov),
    raw mload 0 (hopeSourceWord ee) (UInt256.ofNat 7) ht30
      mem_cost hbaseMload0
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ ht31 (by evm_ov),
    raw push2 (⟨6921⟩ : UInt256) ht33 (by simp; omega),
    raw dup4 ht36 (by
      simpa only [List.length_cons, Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.reduceAdd] using hov),
    raw codecopy 0 copiedMem (UInt256.ofNat 7)
      ht37 mem_cost hcodecopyMem (by decide +native) (by
        simp only [List.length_cons]
        omega),
    raw dup2 ht38 (by evm_ov),
    raw mload 0 vatNotAuthorizedWord (UInt256.ofNat 7) ht39
      mem_cost hcopyMload (by decide) (by evm_ov)]
  exact evm_run rdCopied with [
    raw swap2 ht40 (by evm_ov),
    raw mstore 0 restoredMem
      (UInt256.ofNat 7) ht41 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨68⟩ ht42 (by evm_ov),
    raw dup3 ht44 (by evm_ov),
    raw add ht45 (by evm_ov),
    raw mstore 3 finalMem
      (UInt256.ofNat 8) ht46 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 ht47 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) ht48
      mem_cost hfinalMload64
      (by decide) (by evm_ov),
    raw swap1 ht49 (by evm_ov),
    raw dup2 ht50 (by evm_ov),
    raw swap1 ht51 (by evm_ov),
    raw sub ht52 (by evm_ov),
    raw push1 ⟨100⟩ ht53 (by evm_ov),
    raw add ht55 (by evm_ov),
    raw swap1 ht56 (by evm_ov),
    raw rev 0 ht57 mem_cost (by evm_ov)]

theorem RD.vatLiveGuardOk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vatLiveGuardWf code pc okPc)
    (hlive : solcSlotWord σ ee ⟨10⟩ = ⟨1⟩)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 okPc (key :: ret :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10⟩
  have rd3 := h.jumpdest hd0 (by evm_ov) |>.push1 ⟨10⟩ hd1 (by evm_ov)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by evm_ov)
  have hliveRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨10⟩ ⟨0⟩)) = ⟨1⟩ := by
    simpa [solcSlotWord] using hlive
  rw [hliveRaw] at rd4
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by evm_ov)
  have rd7₀ := rd6.eq hd6 (by evm_ov)
  have rd7 := rd7₀
  rw [uInt256_eq_self] at rd7
  have rd10 := rd7.push2 okPc hd7 (by evm_ov)
  exact ⟨_, _, rd10.jumpiT hd10 one_ne_zero_uint hok (by evm_ov)⟩

theorem RD.vatLiveGuardRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vatLiveGuardWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (vatLiveGuardTailPc pc) ⟨12⟩
      vatNotLiveRawWord ⟨160⟩ .PUSH12 12)
    (hlive : solcSlotWord σ ee ⟨10⟩ ≠ ⟨1⟩)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10⟩
  have rd3 := h.jumpdest hd0 (by evm_ov) |>.push1 ⟨10⟩ hd1 (by evm_ov)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by evm_ov)
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by evm_ov)
  have rd7₀ := rd6.eq hd6 (by evm_ov)
  have hliveRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨10⟩ ⟨0⟩)) ≠ ⟨1⟩ := by
    simpa [solcSlotWord] using hlive
  have heq0 :
      UInt256.eq ⟨1⟩
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨10⟩ ⟨0⟩)) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h1 => hliveRaw h1.symm)
  have rd7 := rd7₀
  rw [heq0] at rd7
  have rd10 := rd7.push2 okPc hd7 (by evm_ov)
  have rdTail₀ := rd10.jumpiNT hd10 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail (by simpa [vatLiveGuardTailPc] using rdTail₀) htail
    (by decide) (by rfl) hmem hread64 (by simpa only [List.length_cons] using hov)

@[reducible] def vatRelyStoreOneWf (code : ByteArray) (pc : UInt256) : Prop :=
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

theorem RD.vatRelyStoreOne {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vatRelyStoreOneWf code pc)
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
  have hmaskLiteral :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) key =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hcanonKey
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
    (UInt256.ofNat 3) hd14 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨32⟩ hd15 (by evm_ov),
    raw dup2 hd17 (by evm_ov),
    raw swap1 hd18 (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨0⟩ mem)
    (UInt256.ofNat 3) hd19 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ hd20 (by evm_ov),
    raw swap1 hd22 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd23 mem_cost hslot (by decide +native) (by evm_ov)
  have rdBeforeStore := evm_run rdSlot with [
    raw push1 ⟨1⟩ hd24 (by evm_ov),
    raw swap1 hd26 (by evm_ov)]
  obtain ⟨_, _, rdOut⟩ := rdBeforeStore.sstore hperm hd27 (by evm_ov)
  exact ⟨_, _, rdOut.jump hd28 hret (by evm_ov)⟩

/-! ### Dispatch, ABI, reachability, and body proof -/

theorem vatDecode_rely_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "usr" (.address (relyUsr I))) := by
  simpa [config, relyTransition, relyUsr] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36)

theorem vatDecode_rely_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
      (transitionSignature relyTransition).paramTypes I.calldata = none := by
  simpa [config, relyTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort)

theorem vatDispatchRely {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 21)) :
    dispatchMsg contract I.calldata = some relyTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 21 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some relyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes, foldSelectorBytes,
    forkSelectorBytes, frobSelectorBytes, gemSelectorBytes, grabSelectorBytes,
    healSelectorBytes, hopeSelectorBytes, ilksSelectorBytes, initSelectorBytes,
    liveSelectorBytes, moveSelectorBytes, nopeSelectorBytes, relySelectorBytes]
  decide +native

theorem vatReachRelyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 21)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨817⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x65fae35e⟩ :=
    vatSelWord_eq_of_beq I hsz 0x65 0xfa 0xe3 0x5e ⟨0x65fae35e⟩
      (by decide +native) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlowhigh :
      UInt256.gt (armSelNat vatBytecode vatLowHighSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms321FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms321FirstPc 2))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact vatReachArms321Body 2 (by omega) ⟨817⟩ hcode hwv hsz hsize
    hroot hlow hlowhigh heq0 htake (by jump_dest) (by decide +native)

theorem vatRelyBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (relyTransition.params.map Param.name)
        (transitionSignature relyTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "usr" (.address (relyUsr I))))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨817⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := relyKey I
  let slot := solcMappingSlot ⟨0⟩ key
  let callerSlot := vatCallerWardsSlot I
  let locals : Store := (∅ : Store).insert "usr" (.address (relyUsr I))
  have hslot : relySlotFor I = slot := by
    simp [slot, key, relySlotFor_eq]
  have hcallerWord : vatSlotWord callerSlot σ_evm I = vatSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨817⟩) (ret := ⟨524⟩)
    (decoded := ⟨839⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := vatBytecode) (decoded := ⟨839⟩) (ret := ⟨524⟩) (routine := ⟨2687⟩)
    (R := [sel]) hdecoded
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by jump_dest) (by simp)
  by_cases hauthEvm : vatSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : vatSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, vatCallerWardsSlot, vatSlotWord] using hauthEvm
    obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
      (code := vatBytecode) (pc := ⟨2687⟩) (okPc := ⟨2769⟩) (key := key)
      (ret := ⟨524⟩) (R := [sel])
      (by simpa [key, relyKey] using hroutine)
      (by
        unfold vatAuthCheckWf
        repeat' first | apply And.intro | decide +native)
      hauthSolc (by jump_dest) (by simp)
    by_cases hliveEvm : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩
    · have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
        rw [← hliveWord]
        exact hliveEvm
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (relySlotFor I) ⟨1⟩
      have hbody :
          ExecTransitionBody config contract evm0 locals relyTransition.body
            (.returned { contract := contract, locals := locals } evm1 none) := by
        have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals]) hauthSolm
        have hguardLive := vatLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
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
            simpa [evm1] using vatStorageLocStore_uint256 evm0 (relySlotFor I) ⟨1⟩
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
        simpa [ExecTransitionBody, relyTransition, nonpayable, auth, requireLive, evm0, evm1] using
          ExecFuncBody.execBlockOK hblock
      have hliveSolc : solcSlotWord σ_evm I ⟨10⟩ = ⟨1⟩ := by
        simpa [vatSlotWord] using hliveEvm
      obtain ⟨_, _, hstorePc⟩ := RD.vatLiveGuardOk
        (code := vatBytecode) (pc := ⟨2769⟩) (okPc := ⟨2839⟩) (key := key)
        (ret := ⟨524⟩) (R := [sel]) hafterAuth
        (by
          unfold vatLiveGuardWf
          repeat' first | apply And.intro | decide +native)
        hliveSolc (by jump_dest) (by simp)
      have hmemAuth :
          (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
        twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
      have hcanonKey : key.toNat < EVM.addressModulus := by
        dsimp [key, relyKey]
        rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
        exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
      obtain ⟨_, _, hretPc⟩ := RD.vatRelyStoreOne
        (code := vatBytecode) (pc := ⟨2839⟩) (key := key) (ret := ⟨524⟩) (R := [sel])
        hstorePc
        (by
          unfold vatRelyStoreOneWf
          repeat' first | apply And.intro | decide +native)
        (by jump_dest) hperm hmemAuth hcanonKey (by simp)
      have hretPc' := hretPc.jumpdest (by decide +native) (by evm_ov)
      have hret :
          RDret vatBytecode (Sat256.ofUInt256 g)
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
    · have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hliveEvm (by rw [hliveWord, hsolm])
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody : ExecTransitionBody config contract evm0 locals relyTransition.body .reverted := by
        have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals]) hauthSolm
        have hguardLive := vatLiveGuardEval_false (cA := cA) (gh := gh) (bl := bl)
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
        simpa [ExecTransitionBody, relyTransition, nonpayable, auth, requireLive, evm0] using
          ExecFuncBody.execBlockRevert hblock
      have hliveSolc : solcSlotWord σ_evm I ⟨10⟩ ≠ ⟨1⟩ := by
        simpa [vatSlotWord] using hliveEvm
      have hmemAuth :
          (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
        twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
      have hread64 :
          (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
            UInt256.toByteArray ⟨128⟩ :=
        twoWordHashMem_read64 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
          solcFreePtrMem_read64
      have hrev := RD.vatLiveGuardRevert
        (code := vatBytecode) (pc := ⟨2769⟩) (okPc := ⟨2839⟩) (key := key)
        (ret := ⟨524⟩) (R := [sel]) hafterAuth
        (by
          unfold vatLiveGuardWf
          repeat' first | apply And.intro | decide +native)
        (by
          unfold solcErrorStringRevertTailWf vatLiveGuardTailPc vatNotLiveRawWord
          repeat' first | apply And.intro | decide +native)
        hliveSolc hmemAuth hread64 (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hauthSolm : vatSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody : ExecTransitionBody config contract evm0 locals relyTransition.body .reverted := by
      have hguard := vatAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
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
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, vatCallerWardsSlot, vatSlotWord] using hauthEvm
    have hrev := RD.vatAuthCheckRevert
      (pc := ⟨2687⟩) (okPc := ⟨2769⟩) (key := key)
      (ret := ⟨524⟩) (R := [sel])
      (by simpa [key, relyKey] using hroutine)
      (by
        unfold vatAuthCheckWf
        repeat' first | apply And.intro | decide +native)
      (by
        unfold vatAuthRevertTailWf vatAuthTailPc
        repeat' first | apply And.intro | decide +native)
      hauthSolc (by simp)
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vatRelyBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some relyTransition)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨817⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨817⟩) (ret := ⟨524⟩)
    (decoded := ⟨839⟩) (need := ⟨32⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (vatDecode_rely_none_short hsz4 hshort)

theorem vatRelyBodyCore : VatBodyTheorem 21 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 21) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some relyTransition :=
    vatDispatchRely hsel
  have hreach := vatReachRelyBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact vatRelyBodyCoreOk hcode hwv hperm hsz36 hsize hdispatch
      (vatDecode_rely_ok hsz36) hreach hAccounts
  · exact vatRelyBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Vat
