import Benchmarks.Dss.Vow.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

/-! ## `deny(address)` -/

abbrev denyUsr (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev denyKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev denyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address (denyUsr I))] }

abbrev denySlotFor (I : ExecutionEnv) : UInt256 :=
  wardsSlot (.address (denyUsr I))

theorem denySlotFor_eq (I : ExecutionEnv) :
    denySlotFor I = solcMappingSlot ⟨0⟩ (denyKey I) := by
  unfold denySlotFor denyUsr denyKey wardsSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

abbrev vowCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

abbrev vowCallerWardsEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address I.source)] }

theorem vowCallerWardsEvaledRef_ok {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (_hbase : locals.get? "wards" = none) :
    evalStorageRef config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (wardsRef sender) =
        .ok (vowCallerWardsEvaledRef I) := by
  simp [vowCallerWardsEvaledRef, wardsRef, sender, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, pure, bind, initState]

theorem vowAuthGuardEval_true {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have her := vowCallerWardsEvaledRef_ok (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  have hload : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      (vowCallerWardsSlot I) = ⟨1⟩ := by
    simpa [vowSlotWord] using hauth
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc (vowCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        vowCallerWardsEvaledRef, vowCallerWardsSlot, wardsSlot, mapSlot, solcMappingSlot,
        keyValueToWord_address, solcSourceWord])]
  rw [vowStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  rw [hload]
  simp [evalExpr?, evalBinaryOp?]
  all_goals native_decide

theorem vowAuthGuardEval_false {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have her := vowCallerWardsEvaledRef_ok (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  let w := Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      (vowCallerWardsSlot I)
  have hload : w ≠ ⟨1⟩ := by
    intro hw
    exact hauth (by simpa [w, vowSlotWord] using hw)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc (vowCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        vowCallerWardsEvaledRef, vowCallerWardsSlot, wardsSlot, mapSlot, solcMappingSlot,
        keyValueToWord_address, solcSourceWord])]
  rw [vowStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  simp [evalExpr?, evalBinaryOp?]
  · intro hnat
    apply hload
    apply u256_inj
    simpa using hnat
  all_goals native_decide

/-! ### Auth and store bytecode helpers -/

@[reducible] def vowAuthTailPc (pc : UInt256) : UInt256 :=
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

@[reducible] def vowAuthCheckWf (code : ByteArray) (pc okPc : UInt256) : Prop :=
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

abbrev vowNotAuthorizedRawWord : UInt256 :=
  ⟨1882396589317237868685917121345356193241433⟩

theorem RD.vowAuthCheckOk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vowAuthCheckWf code pc okPc)
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
    (UInt256.ofNat 3) hd6 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd11 := evm_run rd7 with [
    raw push1 ⟨32⟩ hd7 (by evm_ov),
    raw dup2 hd9 (by evm_ov),
    raw swap1 hd10 (by evm_ov)]
  have rd12 := rd11.mstore 0 (twoWordHashMem (solcSourceWord ee) ⟨0⟩ solcFreePtrMem)
    (UInt256.ofNat 3) hd11 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd15 := evm_run rd12 with [
    raw push1 ⟨64⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ (solcSourceWord ee) solcFreePtrMem_size
  have rd16 := rd15.keccak256 0 (solcMappingSlot ⟨0⟩ (solcSourceWord ee))
    (UInt256.ofNat 3) hd15 mem_cost hslot (by native_decide) (by evm_ov)
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

theorem RD.vowAuthCheckRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vowAuthCheckWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (vowAuthTailPc pc) ⟨18⟩
      vowNotAuthorizedRawWord ⟨114⟩ .PUSH18 18)
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
    (UInt256.ofNat 3) hd6 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd11 := evm_run rd7 with [
    raw push1 ⟨32⟩ hd7 (by evm_ov),
    raw dup2 hd9 (by evm_ov),
    raw swap1 hd10 (by evm_ov)]
  have rd12 := rd11.mstore 0 (twoWordHashMem (solcSourceWord ee) ⟨0⟩ solcFreePtrMem)
    (UInt256.ofNat 3) hd11 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd15 := evm_run rd12 with [
    raw push1 ⟨64⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ (solcSourceWord ee) solcFreePtrMem_size
  have rd16 := rd15.keccak256 0 (solcMappingSlot ⟨0⟩ (solcSourceWord ee))
    (UInt256.ofNat 3) hd15 mem_cost hslot (by native_decide) (by evm_ov)
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
  exact RD.solcErrorStringRevertTail (by simpa [vowAuthTailPc] using rdTail₀) htail
    (by decide) (by rfl)
    (twoWordHashMem_size_96 (solcSourceWord ee) ⟨0⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (solcSourceWord ee) ⟨0⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons]; omega)

@[reducible] def vowDenyStoreZeroWf (code : ByteArray) (pc : UInt256) : Prop :=
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
  let p25 := p24 + ⟨1⟩
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
  ∧ decode code p22 = some (.DUP2, .none)
  ∧ decode code p23 = some (.KECCAK256, .none)
  ∧ decode code p24 = some (.SSTORE, .none)
  ∧ decode code p25 = some (.JUMP, .none)

theorem RD.vowDenyStoreZero {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vowDenyStoreZeroWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R (twoWordHashMem key ⟨0⟩ mem) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨0⟩ key) ⟨0⟩) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd12, hd13, hd14, hd15,
      hd17, hd18, hd19, hd20, hd22, hd23, hd24, hd25⟩
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
    raw dup2 hd22 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨0⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd23 mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdOut⟩ := rdSlot.sstore hperm hd24 (by evm_ov)
  exact ⟨_, _, rdOut.jump hd25 hret (by evm_ov)⟩

/-! ### Dispatch, ABI, reachability, and body proof -/

theorem vowDispatch_deny {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩) :
    dispatchMsg contract I.calldata = some denyTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition])
    (post := [dumpTransition, fessTransition, fileUintTransition, fileAddressTransition,
      flapTransition, flapperTransition, flogTransition, flopTransition, flopperTransition,
      healTransition, humpTransition, kissTransition, liveTransition, relyTransition,
      sinTransition, sumpTransition, vatTransition, waitTransition, wardsTransition])
    (ti := denyTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, denySelectorBytes]
    exact hsel

theorem vowDecode_deny_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "usr" (.address (denyUsr I))) := by
  simpa [config, denyTransition, denyUsr] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36)

theorem vowDecode_deny_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata = none := by
  simpa [config, denyTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort)

theorem vowReachDenyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨608⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨2622662641⟩ :=
    vowSelWord_eq_of_beq I hsz 0x9c 0x52 0xa7 0xf1 ⟨2622662641⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc 2))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachHighLowBody 2 (by omega) ⟨608⟩ hcode hwv hsz hsize hroot hhigh heq0 htake
    (by jump_dest) (by native_decide)

theorem vowDenyBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some denyTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (denyTransition.params.map Param.name)
        (transitionSignature denyTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "usr" (.address (denyUsr I))))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨608⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := denyKey I
  let slot := solcMappingSlot ⟨0⟩ key
  let callerSlot := vowCallerWardsSlot I
  let locals : Store := (∅ : Store).insert "usr" (.address (denyUsr I))
  have hslot : denySlotFor I = slot := by
    simp [slot, key, denySlotFor_eq]
  have hcallerWord : vowSlotWord callerSlot σ_evm I = vowSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vowBytecode) (sel := sel) (entry := ⟨608⟩) (ret := ⟨412⟩)
    (decoded := ⟨630⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
    (code := vowBytecode) (decoded := ⟨630⟩) (ret := ⟨412⟩) (routine := ⟨3474⟩)
    (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
  by_cases hauthEvm : vowSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : vowSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (denySlotFor I) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract evm0 locals denyTransition.body
          (.returned { contract := contract, locals := locals } evm1 none) := by
      have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauthSolm
      have hassign :
          assignStorageRef? config { contract := contract, locals := locals } evm0
            .storage (wardsRef (.var "usr")) (.int 0) =
              .ok ({ contract := contract, locals := locals }, evm1) := by
        have her :
            evalStorageRef config { contract := contract, locals := locals } evm0
              (wardsRef (.var "usr")) = .ok (denyEvaledRef I) := by
          simp [evm0, denyEvaledRef, denyUsr, wardsRef, evalStorageRef,
            evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?,
            EvalResult.ofOption, EvalResult.bind, pure, bind, locals]
        have hstore :
            storageLocStore evm0 (wordLoc (denySlotFor I)) (.int 0) = some evm1 := by
          simpa [evm1] using storageLocStore_uint256 evm0 (denySlotFor I) ⟨0⟩
        exact assignStorageRef_storage_scalar
          (ty := .elem (.int uint256Int)) (loc := wordLoc (denySlotFor I))
          (hbase := by simp [locals, wardsRef])
          (her := her)
          (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
          (hloc := by
            funext evm
            simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
              denyEvaledRef, denySlotFor])
          (hstore := hstore)
      have hblock := nonpayableRequireAssignStorageBlock
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0) (evm' := evm1)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rhs := .intLit 0) (ref := wardsRef (.var "usr")) (value := .int 0)
        (by simp [evm0, initState]; exact hwv)
        hguard (by simp [evalExpr?, pure]) hassign
      simpa [ExecTransitionBody, denyTransition, nonpayable, auth, evm0, evm1] using
        ExecFuncBody.execBlockOK hblock
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
    obtain ⟨_, _, hokPc⟩ := RD.vowAuthCheckOk
      (code := vowBytecode) (pc := ⟨3474⟩) (okPc := ⟨3563⟩) (key := key)
      (ret := ⟨412⟩) (R := [sel])
      (by simpa [key, denyKey] using hroutine)
      (by
        unfold vowAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by jump_dest) (by simp)
    have hmemAuth :
        (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
      twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
    have hcanonKey : key.toNat < EVM.addressModulus := by
      dsimp [key, denyKey]
      rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
      exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
    obtain ⟨_, _, hretPc⟩ := RD.vowDenyStoreZero
      (code := vowBytecode) (pc := ⟨3563⟩) (key := key) (ret := ⟨412⟩) (R := [sel])
      hokPc
      (by
        unfold vowDenyStoreZeroWf
        repeat' first | apply And.intro | native_decide)
      (by jump_dest) hperm hmemAuth hcanonKey (by simp)
    have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
    have hret :
        RDret vowBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨0⟩) ByteArray.empty := by
      simpa [slot] using RD.stop hretPc' (by native_decide) (by simp)
    have hcreated :
        (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨0⟩).1 = evm1.createdAccounts := by
      simp [evm1, evm0, initState, storageStore_createdAccounts]
    have haccounts :
        accountMapEquiv (cA, sstoreAccountMap I.codeOwner σ_evm slot ⟨0⟩).2
          evm1.accountMap := by
      simpa [evm1, evm0, initState, storageStore_accountMap, hslot] using
        accountMapEquiv_sstoreAccountMap I.codeOwner slot ⟨0⟩ hAccounts
    have henc : returnEquiv ByteArray.empty none denyTransition.returnType := by
      rw [show denyTransition.returnType = [] by rfl]
      exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
    exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      hcreated haccounts henc
  · have hauthSolm : vowSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody : ExecTransitionBody config contract evm0 locals denyTransition.body .reverted := by
      have hguard := vowAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [.assign .storage (wardsRef (.var "usr")) (.intLit 0)])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, denyTransition, nonpayable, auth, evm0] using
        ExecFuncBody.execBlockRevert hblock
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
    have hrev := RD.vowAuthCheckRevert
      (code := vowBytecode) (pc := ⟨3474⟩) (okPc := ⟨3563⟩) (key := key)
      (ret := ⟨412⟩) (R := [sel])
      (by simpa [key, denyKey] using hroutine)
      (by
        unfold vowAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold solcErrorStringRevertTailWf vowAuthTailPc vowNotAuthorizedRawWord
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by simp)
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowDenyBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := by omega
  exact vowDenyBodyCore hcode hwv hperm hsz36 hsize (vowDispatch_deny hsel)
    (vowDecode_deny_ok hsz36)
    (vowReachDenyBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts

theorem vowDenyShort {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsel : selIs I ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hreach :=
    vowReachDenyBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vowBytecode) (sel := vowSelWord I) (entry := ⟨608⟩) (ret := ⟨412⟩)
    (decoded := ⟨630⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (vowDispatch_deny hsel)
    (vowDecode_deny_none_short hsz4 hshort)

end Benchmarks.Dss.Vow
