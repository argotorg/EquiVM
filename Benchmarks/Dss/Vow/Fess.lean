import Benchmarks.Dss.Vow.Deny

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

/-! ## `fess(uint256)` -/

abbrev fessTab (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev fessEraKey (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

abbrev fessSinEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "sin", steps := [.mindex (.int (Int.ofNat (fessEraKey I).toNat))] }

abbrev fessSinSlotFor (I : ExecutionEnv) : UInt256 :=
  sinSlot (.int (Int.ofNat (fessEraKey I).toNat))

theorem fessSinSlotFor_eq (I : ExecutionEnv) :
    fessSinSlotFor I = solcMappingSlot ⟨4⟩ (fessEraKey I) := by
  unfold fessSinSlotFor fessEraKey sinSlot mapSlot solcMappingSlot keyValueToWord
  simp only
  rw [wordOfInt_ofNat_toNat]

abbrev sinCapitalEvaledRef : EvaledStorageRef :=
  { base := "Sin", steps := [] }

abbrev fessLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "tab" (.int (Int.ofNat (fessTab I).toNat))

abbrev fessLocalsSinNew (I : ExecutionEnv) (sinNew : UInt256) : Store :=
  (fessLocals I).insert "sinNew" (.int (Int.ofNat sinNew.toNat))

abbrev fessLocalsSinNewSinCapitalNew
    (I : ExecutionEnv) (sinNew SinNew : UInt256) : Store :=
  (fessLocalsSinNew I sinNew).insert "SinNew" (.int (Int.ofNat SinNew.toNat))

theorem fessLocals_get_tab (I : ExecutionEnv) :
    (fessLocals I).get? "tab" = some (.int (Int.ofNat (fessTab I).toNat)) := by
  rw [fessLocals, store_get_self]

theorem fessLocalsSinNew_get_tab (I : ExecutionEnv) (sinNew : UInt256) :
    (fessLocalsSinNew I sinNew).get? "tab" =
      some (.int (Int.ofNat (fessTab I).toNat)) := by
  rw [fessLocalsSinNew, store_get_ne _ _ (by decide), fessLocals_get_tab]

theorem fessLocalsSinNew_get_sinNew (I : ExecutionEnv) (sinNew : UInt256) :
    (fessLocalsSinNew I sinNew).get? "sinNew" =
      some (.int (Int.ofNat sinNew.toNat)) := by
  rw [fessLocalsSinNew, store_get_self]

theorem fessLocalsSinNewSinCapitalNew_get_tab
    (I : ExecutionEnv) (sinNew SinNew : UInt256) :
    (fessLocalsSinNewSinCapitalNew I sinNew SinNew).get? "tab" =
      some (.int (Int.ofNat (fessTab I).toNat)) := by
  rw [fessLocalsSinNewSinCapitalNew, store_get_ne _ _ (by decide),
    fessLocalsSinNew_get_tab]

theorem fessLocalsSinNewSinCapitalNew_get_SinNew
    (I : ExecutionEnv) (sinNew SinNew : UInt256) :
    (fessLocalsSinNewSinCapitalNew I sinNew SinNew).get? "SinNew" =
      some (.int (Int.ofNat SinNew.toNat)) := by
  rw [fessLocalsSinNewSinCapitalNew, store_get_self]

theorem evalExpr_add256_tab_ok {evm : EVM.State} {locals : Store}
    {x : Expr} {old tab sum : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (htab : evalExpr? config { contract := contract, locals := locals } evm (.var "tab") =
      .ok (.int (Int.ofNat tab.toNat)))
    (hsum : sum = old + tab)
    (hfit : old.toNat + tab.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm (add256 x (.var "tab")) =
      .ok (.int (Int.ofNat sum.toNat)) := by
  have hlt : ¬ Int.ofNat (old.toNat + tab.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : sum.toNat = old.toNat + tab.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, htab, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem evalExpr_add256_tab_revert {evm : EVM.State} {locals : Store}
    {x : Expr} {old tab : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat old.toNat)))
    (htab : evalExpr? config { contract := contract, locals := locals } evm (.var "tab") =
      .ok (.int (Int.ofNat tab.toNat)))
    (hover : UInt256.size ≤ old.toNat + tab.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (add256 x (.var "tab")) =
      .revert := by
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, htab, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem evalExpr_ge_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {new old : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat new.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat old.toNat)))
    (hge : old.toNat ≤ new.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hge

theorem evalExpr_fessTab {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "tab" = some (.int (Int.ofNat (fessTab I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "tab") =
      .ok (.int (Int.ofNat (fessTab I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "tab") =
    .ok (.int (Int.ofNat (fessTab I).toNat))
  rw [h]
  rfl

theorem evalExpr_fessSinStorage
    {cA gh bl σ σ₀ A I} {g : UInt256} {locals : Store}
    (hbase : locals.get? "sin" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (.storage (sinRef (.env .timestamp))) =
        .ok (.int (Int.ofNat (vowSlotWord (fessSinSlotFor I) σ I).toNat)) := by
  rw [evalExpr_storage_scalar (er := fessSinEvaledRef I) (t := .int uint256Int)
    (loc := wordLoc (fessSinSlotFor I))]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_uint256 _ (fessSinSlotFor I))
  · exact hbase
  · simp [fessSinEvaledRef, fessEraKey, sinRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, pure, bind, initState]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, fessSinEvaledRef,
      fessSinSlotFor]

theorem evalExpr_sinCapitalStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "Sin" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage SinRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)) := by
  rw [evalExpr_storage_scalar (er := sinCapitalEvaledRef) (t := .int uint256Int)
    (loc := wordLoc ⟨5⟩)]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_uint256 _ ⟨5⟩)
  · exact hbase
  · simp [sinCapitalEvaledRef, SinRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, sinCapitalEvaledRef]

theorem assign_fessSinStorage
    {cA gh bl σ σ₀ A I} {g : UInt256} {locals : Store} (sinNew : UInt256)
    (hbase : locals.get? "sin" = none) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (fessSinSlotFor I) sinNew
    assignStorageRef? config { contract := contract, locals := locals } evm0
      .storage (sinRef (.env .timestamp)) (.int (Int.ofNat sinNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm1) := by
  intro evm0 evm1
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm0
        (sinRef (.env .timestamp)) = .ok (fessSinEvaledRef I) := by
    simp [evm0, fessSinEvaledRef, fessEraKey, sinRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, pure, bind, initState]
  have hstore :
      storageLocStore evm0 (wordLoc (fessSinSlotFor I)) (.int (Int.ofNat sinNew.toNat)) =
        some evm1 := by
    simpa [evm1, evm0] using storageLocStore_uint256 evm0 (fessSinSlotFor I) sinNew
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc (fessSinSlotFor I))
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        fessSinEvaledRef, fessSinSlotFor])
    (hstore := hstore)

theorem assign_sinCapitalStorage (evm : EVM.State) {locals : Store} (SinNew : UInt256)
    (hbase : locals.get? "Sin" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ SinNew
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage SinRef (.int (Int.ofNat SinNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm SinRef =
        .ok sinCapitalEvaledRef := by
    simp [sinCapitalEvaledRef, SinRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨5⟩) (.int (Int.ofNat SinNew.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨5⟩ SinNew
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨5⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, sinCapitalEvaledRef])
    (hstore := hstore)

/-! ### `fess` bytecode helpers -/

@[reducible] def vowFessToFirstAddWf
    (code : ByteArray) (pc afterAddPc routinePc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p9 := p7 + UInt256.ofNat 2
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p20 := p17 + UInt256.ofNat 3
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p25 := p22 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.TIMESTAMP, .none)
  ∧ decode code p2 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p4 = some (.SWAP1, .none)
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.MSTORE, .none)
  ∧ decode code p7 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p9 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p11 = some (.MSTORE, .none)
  ∧ decode code p12 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p14 = some (.SWAP1, .none)
  ∧ decode code p15 = some (.KECCAK256, .none)
  ∧ decode code p16 = some (.SLOAD, .none)
  ∧ decode code p17 = some (.Push .PUSH2, some (afterAddPc, 2))
  ∧ decode code p20 = some (.SWAP1, .none)
  ∧ decode code p21 = some (.DUP3, .none)
  ∧ decode code p22 = some (.Push .PUSH2, some (routinePc, 2))
  ∧ decode code p25 = some (.JUMP, .none)

theorem RD.vowFessToFirstAdd {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc afterAddPc routinePc tab ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (tab :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : vowFessToFirstAddWf code pc afterAddPc routinePc)
    (hmem : mem.size = 96)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routinePc
      (tab :: solcSlotWord σ ee (solcMappingSlot ⟨4⟩ (UInt256.ofNat ee.header.timestamp)) ::
        afterAddPc :: tab :: ret :: R)
      (twoWordHashMem (UInt256.ofNat ee.header.timestamp) ⟨4⟩ mem)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd9, hd11, hd12, hd14, hd15, hd16,
      hd17, hd20, hd21, hd22, hd25⟩
  let ts := UInt256.ofNat ee.header.timestamp
  have rdMem0Prefix := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw timestamp hd1 (by evm_ov),
    raw push1 ⟨0⟩ hd2 (by evm_ov),
    raw swap1 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rdMem0 := rdMem0Prefix.mstore 0 (wordAt0Mem ts mem)
    (UInt256.ofNat 3) hd6 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMemSlotPrefix := evm_run rdMem0 with [
    raw push1 ⟨4⟩ hd7 (by evm_ov),
    raw push1 ⟨32⟩ hd9 (by evm_ov)]
  have rdHashMem := rdMemSlotPrefix.mstore 0 (twoWordHashMem ts ⟨4⟩ mem)
    (UInt256.ofNat 3) hd11 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨4⟩ ts hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨4⟩ ts)
    (UInt256.ofNat 3) hd15 mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoaded⟩ := rdSlot.sload hd16 (by evm_ov)
  have rdJump := evm_run rdLoaded with [
    raw push2 afterAddPc hd17 (by evm_ov),
    raw swap1 hd20 (by evm_ov),
    raw dup3 hd21 (by evm_ov),
    raw push2 routinePc hd22 (by evm_ov)]
  exact ⟨_, _, by simpa [ts, solcSlotWord] using rdJump.jump hd25 hroutine (by evm_ov)⟩

@[reducible] def vowFessStoreSinAndToSecondAddWf
    (code : ByteArray) (pc afterAddPc routinePc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p9 := p7 + UInt256.ofNat 2
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p20 := p19 + ⟨1⟩
  let p23 := p20 + UInt256.ofNat 3
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p28 := p25 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.TIMESTAMP, .none)
  ∧ decode code p2 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p4 = some (.SWAP1, .none)
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.MSTORE, .none)
  ∧ decode code p7 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p9 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p11 = some (.MSTORE, .none)
  ∧ decode code p12 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p14 = some (.SWAP1, .none)
  ∧ decode code p15 = some (.KECCAK256, .none)
  ∧ decode code p16 = some (.SSTORE, .none)
  ∧ decode code p17 = some (.Push .PUSH1, some (⟨5⟩, 1))
  ∧ decode code p19 = some (.SLOAD, .none)
  ∧ decode code p20 = some (.Push .PUSH2, some (afterAddPc, 2))
  ∧ decode code p23 = some (.SWAP1, .none)
  ∧ decode code p24 = some (.DUP3, .none)
  ∧ decode code p25 = some (.Push .PUSH2, some (routinePc, 2))
  ∧ decode code p28 = some (.JUMP, .none)

theorem RD.vowFessStoreSinAndToSecondAdd {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc afterAddPc routinePc sinNew tab ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (sinNew :: tab :: ret :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k C)
    (hwf : vowFessStoreSinAndToSecondAddWf code pc afterAddPc routinePc)
    (hmem : mem.size = 96)
    (hperm : ee.perm = true)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routinePc
      (tab ::
        solcSlotWord
          (sstoreAccountMap ee.codeOwner σ
            (solcMappingSlot ⟨4⟩ (UInt256.ofNat ee.header.timestamp)) sinNew)
          ee ⟨5⟩ ::
        afterAddPc :: tab :: ret :: R)
      (twoWordHashMem (UInt256.ofNat ee.header.timestamp) ⟨4⟩ mem)
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ
        (solcMappingSlot ⟨4⟩ (UInt256.ofNat ee.header.timestamp)) sinNew) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd9, hd11, hd12, hd14, hd15, hd16,
      hd17, hd19, hd20, hd23, hd24, hd25, hd28⟩
  let ts := UInt256.ofNat ee.header.timestamp
  have rdMem0Prefix := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw timestamp hd1 (by evm_ov),
    raw push1 ⟨0⟩ hd2 (by evm_ov),
    raw swap1 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rdMem0 := rdMem0Prefix.mstore 0 (wordAt0Mem ts mem)
    (UInt256.ofNat 3) hd6 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMemSlotPrefix := evm_run rdMem0 with [
    raw push1 ⟨4⟩ hd7 (by evm_ov),
    raw push1 ⟨32⟩ hd9 (by evm_ov)]
  have rdHashMem := rdMemSlotPrefix.mstore 0 (twoWordHashMem ts ⟨4⟩ mem)
    (UInt256.ofNat 3) hd11 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨4⟩ ts hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨4⟩ ts)
    (UInt256.ofNat 3) hd15 mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdStored⟩ := rdSlot.sstore hperm hd16 (by evm_ov)
  have rdBeforeLoad := evm_run rdStored with [raw push1 ⟨5⟩ hd17 (by evm_ov)]
  obtain ⟨_, _, rdLoaded⟩ := rdBeforeLoad.sload hd19 (by evm_ov)
  have rdJump := evm_run rdLoaded with [
    raw push2 afterAddPc hd20 (by evm_ov),
    raw swap1 hd23 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw push2 routinePc hd25 (by evm_ov)]
  exact ⟨_, _, by simpa [ts, solcSlotWord] using rdJump.jump hd28 hroutine (by evm_ov)⟩

@[reducible] def vowFessStoreSinCapitalWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨5⟩, 1))
  ∧ decode code p3 = some (.SSTORE, .none)
  ∧ decode code p4 = some (.POP, .none)
  ∧ decode code p5 = some (.JUMP, .none)

theorem RD.vowFessStoreSinCapital {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc sinNew tab ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (sinNew :: tab :: ret :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k C)
    (hwf : vowFessStoreSinCapitalWf code pc)
    (hperm : ee.perm = true)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨5⟩ sinNew) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd5⟩
  have rdStorePrefix := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨5⟩ hd1 (by evm_ov)]
  obtain ⟨_, _, rdStored⟩ := rdStorePrefix.sstore hperm hd3 (by evm_ov)
  have rdPop := rdStored.pop hd4 (by evm_ov)
  exact ⟨_, _, rdPop.jump hd5 hret (by evm_ov)⟩

/-! ### Dispatch, ABI, and reachability -/

theorem vowDispatch_fess {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x69, 0x7e, 0xfb, 0x78]⟩) :
    dispatchMsg contract I.calldata = some fessTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition])
    (post := [fileUintTransition, fileAddressTransition, flapTransition, flapperTransition,
      flogTransition, flopTransition, flopperTransition, healTransition, humpTransition,
      kissTransition, liveTransition, relyTransition, sinTransition, sumpTransition,
      vatTransition, waitTransition, wardsTransition])
    (ti := fessTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x69, 0x7e, 0xfb, 0x78]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, fessSelectorBytes]
    exact hsel

theorem vowDecode_fess_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fessTransition.params.map Param.name)
      (transitionSignature fessTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "tab" (.int (Int.ofNat (fessTab I).toNat))) := by
  simpa [config, fessTransition, fessTab, uint256] using
    (decodeCalldata_legacyUInt256_ok (cd := I.calldata) (x := "tab") hsz36)

theorem vowDecode_fess_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (fessTransition.params.map Param.name)
      (transitionSignature fessTransition).paramTypes I.calldata = none := by
  simpa [config, fessTransition, uint256] using
    (decodeCalldata_legacyUInt256_none_short (cd := I.calldata) (x := "tab") hsz4 hshort)

theorem vowReachFessBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x69, 0x7e, 0xfb, 0x78]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨571⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨1769929592⟩ :=
    vowSelWord_eq_of_beq I hsz 0x69 0x7e 0xfb 0x78 ⟨1769929592⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc 0))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachHighLowBody 0 (by omega) ⟨571⟩ hcode hwv hsz hsize hroot hhigh heq0 htake
    (by jump_dest) (by native_decide)

theorem RD.vowFessDecodeToRoutine
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨571⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3318⟩
      [fessTab I, ⟨412⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  let tab := fessTab I
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vowBytecode) (sel := sel) (entry := ⟨571⟩) (ret := ⟨412⟩)
    (decoded := ⟨593⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  have rd594 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd595 := rd594.pop (by native_decide) (by evm_ov)
  have rd596 := rd595.calldataload (by native_decide) (by evm_ov)
  have rd599 := rd596.push2 ⟨3318⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [tab, fessTab, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd599.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.vowFessSuccess
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨571⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hfitEra : (solcSlotWord σ I (solcMappingSlot ⟨4⟩ (fessEraKey I))).toNat +
      (fessTab I).toNat < UInt256.size)
    (hfitSin :
      (solcSlotWord
          (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨4⟩ (fessEraKey I))
            (solcSlotWord σ I (solcMappingSlot ⟨4⟩ (fessEraKey I)) + fessTab I))
          I ⟨5⟩).toNat + (fessTab I).toNat < UInt256.size) :
    RDret vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (cA,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨4⟩ (fessEraKey I))
            (solcSlotWord σ I (solcMappingSlot ⟨4⟩ (fessEraKey I)) + fessTab I))
          ⟨5⟩
          (solcSlotWord
              (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨4⟩ (fessEraKey I))
                (solcSlotWord σ I (solcMappingSlot ⟨4⟩ (fessEraKey I)) + fessTab I))
              I ⟨5⟩ + fessTab I))
      ByteArray.empty := by
  let tab := fessTab I
  let era := fessEraKey I
  let eraSlot := solcMappingSlot ⟨4⟩ era
  let sinNew := solcSlotWord σ I eraSlot + tab
  let σ1 := sstoreAccountMap I.codeOwner σ eraSlot sinNew
  let SinNew := solcSlotWord σ1 I ⟨5⟩ + tab
  obtain ⟨_, _, htoRoutineRD⟩ := RD.vowFessDecodeToRoutine hreach hsz36 hsize
  obtain ⟨_, _, hafterAuth⟩ := RD.vowAuthCheckOk
    (code := vowBytecode) (pc := ⟨3318⟩) (okPc := ⟨3407⟩) (key := tab)
    (ret := ⟨412⟩) (R := [sel]) htoRoutineRD
    (by
      unfold vowAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauth (by jump_dest) (by simp)
  have hmemAuth : (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  obtain ⟨_, _, hfirstAdd⟩ := RD.vowFessToFirstAdd
    (code := vowBytecode) (pc := ⟨3407⟩) (afterAddPc := ⟨3433⟩)
    (routinePc := ⟨5074⟩) (tab := tab) (ret := ⟨412⟩) (R := [sel])
    hafterAuth
    (by
      unfold vowFessToFirstAddWf
      repeat' first | apply And.intro | native_decide)
    hmemAuth (by jump_dest) (by simp)
  obtain ⟨_, _, hafterFirstAdd⟩ := RD.solcCheckedAddSuccess
    (code := vowBytecode) (pc := ⟨5074⟩) (okPc := ⟨5090⟩)
    (a := solcSlotWord σ I eraSlot) (b := tab) (ret := ⟨3433⟩)
    (R := [tab, ⟨412⟩, sel])
    (by simpa [era, eraSlot, tab] using hfirstAdd)
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [era, eraSlot, tab] using hfitEra)
    (by jump_dest) (by jump_dest) (by simp)
  have hmemFirst :
      (twoWordHashMem era ⟨4⟩
        (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)).size = 96 :=
    twoWordHashMem_size_96 era ⟨4⟩ hmemAuth
  obtain ⟨_, _, hsecondAdd⟩ := RD.vowFessStoreSinAndToSecondAdd
    (code := vowBytecode) (pc := ⟨3433⟩) (afterAddPc := ⟨3462⟩)
    (routinePc := ⟨5074⟩) (sinNew := sinNew) (tab := tab) (ret := ⟨412⟩)
    (R := [sel])
    (by simpa [sinNew, tab] using hafterFirstAdd)
    (by
      unfold vowFessStoreSinAndToSecondAddWf
      repeat' first | apply And.intro | native_decide)
    hmemFirst hperm (by jump_dest) (by simp)
  obtain ⟨_, _, hafterSecondAdd⟩ := RD.solcCheckedAddSuccess
    (code := vowBytecode) (pc := ⟨5074⟩) (okPc := ⟨5090⟩)
    (a := solcSlotWord σ1 I ⟨5⟩) (b := tab) (ret := ⟨3462⟩)
    (R := [tab, ⟨412⟩, sel])
    (by simpa [σ1, sinNew, era, eraSlot, tab] using hsecondAdd)
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [σ1, sinNew, era, eraSlot, tab] using hfitSin)
    (by jump_dest) (by jump_dest) (by simp)
  obtain ⟨_, _, hretPc⟩ := RD.vowFessStoreSinCapital
    (code := vowBytecode) (pc := ⟨3462⟩) (sinNew := SinNew) (tab := tab)
    (ret := ⟨412⟩) (R := [sel])
    (by simpa [SinNew, σ1, tab] using hafterSecondAdd)
    (by
      unfold vowFessStoreSinCapitalWf
      repeat' first | apply And.intro | native_decide)
    hperm (by jump_dest) (by simp)
  have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
  simpa [tab, era, eraSlot, sinNew, σ1, SinNew, fessEraKey, fessTab] using
    RD.stop hretPc' (by native_decide) (by simp)

theorem RD.vowFessAuthRevert
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨571⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let tab := fessTab I
  obtain ⟨_, _, htoRoutineRD⟩ := RD.vowFessDecodeToRoutine hreach hsz36 hsize
  exact RD.vowAuthCheckRevert
    (code := vowBytecode) (pc := ⟨3318⟩) (okPc := ⟨3407⟩) (key := tab)
    (ret := ⟨412⟩) (R := [sel])
    (by simpa [tab] using htoRoutineRD)
    (by
      unfold vowAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf vowAuthTailPc vowNotAuthorizedRawWord
      repeat' first | apply And.intro | native_decide)
    hauth (by simp)

theorem RD.vowFessFirstAddOverflow
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨571⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hover : UInt256.size ≤
      (solcSlotWord σ I (solcMappingSlot ⟨4⟩ (fessEraKey I))).toNat + (fessTab I).toNat) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let tab := fessTab I
  let era := fessEraKey I
  let eraSlot := solcMappingSlot ⟨4⟩ era
  obtain ⟨_, _, htoRoutineRD⟩ := RD.vowFessDecodeToRoutine hreach hsz36 hsize
  obtain ⟨_, _, hafterAuth⟩ := RD.vowAuthCheckOk
    (code := vowBytecode) (pc := ⟨3318⟩) (okPc := ⟨3407⟩) (key := tab)
    (ret := ⟨412⟩) (R := [sel])
    (by simpa [tab] using htoRoutineRD)
    (by
      unfold vowAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauth (by jump_dest) (by simp)
  have hmemAuth : (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  obtain ⟨_, _, hfirstAdd⟩ := RD.vowFessToFirstAdd
    (code := vowBytecode) (pc := ⟨3407⟩) (afterAddPc := ⟨3433⟩)
    (routinePc := ⟨5074⟩) (tab := tab) (ret := ⟨412⟩) (R := [sel])
    hafterAuth
    (by
      unfold vowFessToFirstAddWf
      repeat' first | apply And.intro | native_decide)
    hmemAuth (by jump_dest) (by simp)
  exact RD.solcCheckedAddEmptyRevert
    (code := vowBytecode) (pc := ⟨5074⟩) (okPc := ⟨5090⟩)
    (a := solcSlotWord σ I eraSlot) (b := tab) (ret := ⟨3433⟩)
    (R := [tab, ⟨412⟩, sel])
    (by simpa [era, eraSlot, tab] using hfirstAdd)
    (by
      unfold solcCheckedAddEmptyRevertWf solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [era, eraSlot, tab] using hover)
    (by simp)

theorem RD.vowFessSecondAddOverflow
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨571⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hfitEra : (solcSlotWord σ I (solcMappingSlot ⟨4⟩ (fessEraKey I))).toNat +
      (fessTab I).toNat < UInt256.size)
    (hoverSin : UInt256.size ≤
      (solcSlotWord
          (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨4⟩ (fessEraKey I))
            (solcSlotWord σ I (solcMappingSlot ⟨4⟩ (fessEraKey I)) + fessTab I))
          I ⟨5⟩).toNat + (fessTab I).toNat) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let tab := fessTab I
  let era := fessEraKey I
  let eraSlot := solcMappingSlot ⟨4⟩ era
  let sinNew := solcSlotWord σ I eraSlot + tab
  let σ1 := sstoreAccountMap I.codeOwner σ eraSlot sinNew
  obtain ⟨_, _, htoRoutineRD⟩ := RD.vowFessDecodeToRoutine hreach hsz36 hsize
  obtain ⟨_, _, hafterAuth⟩ := RD.vowAuthCheckOk
    (code := vowBytecode) (pc := ⟨3318⟩) (okPc := ⟨3407⟩) (key := tab)
    (ret := ⟨412⟩) (R := [sel])
    (by simpa [tab] using htoRoutineRD)
    (by
      unfold vowAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauth (by jump_dest) (by simp)
  have hmemAuth : (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  obtain ⟨_, _, hfirstAdd⟩ := RD.vowFessToFirstAdd
    (code := vowBytecode) (pc := ⟨3407⟩) (afterAddPc := ⟨3433⟩)
    (routinePc := ⟨5074⟩) (tab := tab) (ret := ⟨412⟩) (R := [sel])
    hafterAuth
    (by
      unfold vowFessToFirstAddWf
      repeat' first | apply And.intro | native_decide)
    hmemAuth (by jump_dest) (by simp)
  obtain ⟨_, _, hafterFirstAdd⟩ := RD.solcCheckedAddSuccess
    (code := vowBytecode) (pc := ⟨5074⟩) (okPc := ⟨5090⟩)
    (a := solcSlotWord σ I eraSlot) (b := tab) (ret := ⟨3433⟩)
    (R := [tab, ⟨412⟩, sel])
    (by simpa [era, eraSlot, tab] using hfirstAdd)
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [era, eraSlot, tab] using hfitEra)
    (by jump_dest) (by jump_dest) (by simp)
  have hmemFirst :
      (twoWordHashMem era ⟨4⟩
        (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)).size = 96 :=
    twoWordHashMem_size_96 era ⟨4⟩ hmemAuth
  obtain ⟨_, _, hsecondAdd⟩ := RD.vowFessStoreSinAndToSecondAdd
    (code := vowBytecode) (pc := ⟨3433⟩) (afterAddPc := ⟨3462⟩)
    (routinePc := ⟨5074⟩) (sinNew := sinNew) (tab := tab) (ret := ⟨412⟩)
    (R := [sel])
    (by simpa [sinNew, tab] using hafterFirstAdd)
    (by
      unfold vowFessStoreSinAndToSecondAddWf
      repeat' first | apply And.intro | native_decide)
    hmemFirst hperm (by jump_dest) (by simp)
  exact RD.solcCheckedAddEmptyRevert
    (code := vowBytecode) (pc := ⟨5074⟩) (okPc := ⟨5090⟩)
    (a := solcSlotWord σ1 I ⟨5⟩) (b := tab) (ret := ⟨3462⟩)
    (R := [tab, ⟨412⟩, sel])
    (by simpa [σ1, sinNew, era, eraSlot, tab] using hsecondAdd)
    (by
      unfold solcCheckedAddEmptyRevertWf solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [σ1, sinNew, era, eraSlot, tab] using hoverSin)
    (by simp)

/-! ### Source body and refinement -/

theorem vowFessBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fessTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fessTransition.params.map Param.name)
        (transitionSignature fessTransition).paramTypes I.calldata = some (fessLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨571⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let tab := fessTab I
  let eraSlot := solcMappingSlot ⟨4⟩ (fessEraKey I)
  let slot := fessSinSlotFor I
  let callerSlot := vowCallerWardsSlot I
  let locals := fessLocals I
  have hslot : slot = eraSlot := by
    simp [slot, eraSlot, fessSinSlotFor_eq]
  have hcallerWord : vowSlotWord callerSlot σ_evm I = vowSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hsinWord : vowSlotWord slot σ_evm I = vowSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  by_cases hauthEvm : vowSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : vowSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
    by_cases hfitEraEvm : (vowSlotWord slot σ_evm I).toNat + tab.toNat < UInt256.size
    · let sinNew := vowSlotWord slot σ_evm I + tab
      let locals1 := fessLocalsSinNew I sinNew
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 I.codeOwner slot sinNew
      let σ1_evm := sstoreAccountMap I.codeOwner σ_evm eraSlot sinNew
      have hfitEraSolm : (vowSlotWord slot σ_solm I).toNat + tab.toNat < UInt256.size := by
        rw [← hsinWord]
        exact hfitEraEvm
      have hsinNewEqSolm : sinNew = vowSlotWord slot σ_solm I + tab := by
        simp [sinNew, hsinWord]
      have hsinNewNatSolm :
          sinNew.toNat = (vowSlotWord slot σ_solm I).toNat + tab.toNat := by
        rw [hsinNewEqSolm, uadd_toNat, Nat.mod_eq_of_lt hfitEraSolm]
      have haccounts1 : accountMapEquiv σ1_evm evm1.accountMap := by
        simpa [σ1_evm, evm1, evm0, initState, storageStore_accountMap, hslot] using
          accountMapEquiv_sstoreAccountMap I.codeOwner eraSlot sinNew hAccounts
      have hsinRead0 :
          evalExpr? config { contract := contract, locals := locals } evm0
            (.storage (sinRef (.env .timestamp))) =
              .ok (.int (Int.ofNat (vowSlotWord slot σ_solm I).toNat)) := by
        simpa [evm0, locals, slot] using
          (evalExpr_fessSinStorage (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals)
            (by simp [locals, fessLocals]))
      have htab0 :
          evalExpr? config { contract := contract, locals := locals } evm0 (.var "tab") =
            .ok (.int (Int.ofNat tab.toNat)) := by
        simpa [evm0, locals, tab] using
          (evalExpr_fessTab (evm := evm0) (I := I) (locals := locals)
            (by simpa [locals] using fessLocals_get_tab I))
      have hfirstAdd :
          evalExpr? config { contract := contract, locals := locals } evm0
            (add256 (.storage (sinRef (.env .timestamp))) (.var "tab")) =
              .ok (.int (Int.ofNat sinNew.toNat)) := by
        exact evalExpr_add256_tab_ok
          (x := .storage (sinRef (.env .timestamp))) (old := vowSlotWord slot σ_solm I)
          (tab := tab) (sum := sinNew) hsinRead0 htab0 hsinNewEqSolm hfitEraSolm
      have hsinNewVar :
          evalExpr? config { contract := contract, locals := locals1 } evm0 (.var "sinNew") =
            .ok (.int (Int.ofNat sinNew.toNat)) := by
        rw [evalExpr?]
        change EvalResult.ofOption EvalError.unboundVariable (locals1.get? "sinNew") =
          .ok (.int (Int.ofNat sinNew.toNat))
        rw [show locals1.get? "sinNew" = some (.int (Int.ofNat sinNew.toNat)) by
          simpa [locals1] using fessLocalsSinNew_get_sinNew I sinNew]
        rfl
      have hfirstRequire :
          evalExpr? config { contract := contract, locals := locals1 } evm0
            (.binary .ge (.var "sinNew") (.storage (sinRef (.env .timestamp)))) =
              .ok (.bool true) := by
        have hread :
            evalExpr? config { contract := contract, locals := locals1 } evm0
              (.storage (sinRef (.env .timestamp))) =
                .ok (.int (Int.ofNat (vowSlotWord slot σ_solm I).toNat)) := by
          simpa [evm0, locals1, slot] using
            (evalExpr_fessSinStorage (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
              (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals1)
              (by simp [locals1, fessLocalsSinNew, fessLocals]))
        exact evalExpr_ge_uint256_true hsinNewVar hread (by rw [hsinNewNatSolm]; omega)
      have hassignSin :
          assignStorageRef? config { contract := contract, locals := locals1 } evm0
            .storage (sinRef (.env .timestamp)) (.int (Int.ofNat sinNew.toNat)) =
              .ok ({ contract := contract, locals := locals1 }, evm1) := by
        simpa [evm0, evm1, locals1] using
          (assign_fessSinStorage (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals1) sinNew
            (by simp [locals1, fessLocalsSinNew, fessLocals]))
      by_cases hfitSinEvm : (vowSlotWord ⟨5⟩ σ1_evm I).toNat + tab.toNat < UInt256.size
      · let SinNew := vowSlotWord ⟨5⟩ σ1_evm I + tab
        let locals2 := fessLocalsSinNewSinCapitalNew I sinNew SinNew
        let evm2 := Solm.EVM.storageStore evm1 I.codeOwner ⟨5⟩ SinNew
        have hsinCapitalWord :
            Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner ⟨5⟩ =
              vowSlotWord ⟨5⟩ σ1_evm I := by
          have hword := accountMapEquiv_storage_findD haccounts1 I.codeOwner ⟨5⟩ ⟨0⟩
          symm
          calc
            vowSlotWord ⟨5⟩ σ1_evm I = vowSlotWord ⟨5⟩ evm1.accountMap I := hword
            _ = Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner ⟨5⟩ := by
              simp [vowSlotWord, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage, storageStore_executionEnv, evm1, evm0, initState]
        have hsinCapitalRead :
            evalExpr? config { contract := contract, locals := locals1 } evm1 (.storage SinRef) =
              .ok (.int (Int.ofNat (vowSlotWord ⟨5⟩ σ1_evm I).toNat)) := by
          simpa [hsinCapitalWord] using
            (evalExpr_sinCapitalStorage evm1 (locals := locals1)
              (by simp [locals1, fessLocalsSinNew, fessLocals]))
        have htab1 :
            evalExpr? config { contract := contract, locals := locals1 } evm1 (.var "tab") =
              .ok (.int (Int.ofNat tab.toNat)) := by
          simpa [tab] using
            (evalExpr_fessTab (evm := evm1) (I := I) (locals := locals1)
              (by simpa [locals1] using fessLocalsSinNew_get_tab I sinNew))
        have hsecondAdd :
            evalExpr? config { contract := contract, locals := locals1 } evm1
              (add256 (.storage SinRef) (.var "tab")) =
                .ok (.int (Int.ofNat SinNew.toNat)) := by
          exact evalExpr_add256_tab_ok (x := .storage SinRef)
            (old := vowSlotWord ⟨5⟩ σ1_evm I) (tab := tab) (sum := SinNew)
            hsinCapitalRead htab1 (by simp [SinNew]) hfitSinEvm
        have hSinNewVar :
            evalExpr? config { contract := contract, locals := locals2 } evm1 (.var "SinNew") =
              .ok (.int (Int.ofNat SinNew.toNat)) := by
          rw [evalExpr?]
          change EvalResult.ofOption EvalError.unboundVariable (locals2.get? "SinNew") =
            .ok (.int (Int.ofNat SinNew.toNat))
          rw [show locals2.get? "SinNew" = some (.int (Int.ofNat SinNew.toNat)) by
            simpa [locals2] using fessLocalsSinNewSinCapitalNew_get_SinNew I sinNew SinNew]
          rfl
        have hsecondRequire :
            evalExpr? config { contract := contract, locals := locals2 } evm1
              (.binary .ge (.var "SinNew") (.storage SinRef)) = .ok (.bool true) := by
          have hread :
              evalExpr? config { contract := contract, locals := locals2 } evm1
                (.storage SinRef) =
                  .ok (.int (Int.ofNat (vowSlotWord ⟨5⟩ σ1_evm I).toNat)) := by
            simpa [hsinCapitalWord] using
              (evalExpr_sinCapitalStorage evm1 (locals := locals2)
                (by simp [locals2, fessLocalsSinNewSinCapitalNew, fessLocalsSinNew,
                  fessLocals]))
          have hSinNewNat :
              SinNew.toNat = (vowSlotWord ⟨5⟩ σ1_evm I).toNat + tab.toNat := by
            simp [SinNew, uadd_toNat, Nat.mod_eq_of_lt hfitSinEvm]
          exact evalExpr_ge_uint256_true hSinNewVar hread (by rw [hSinNewNat]; omega)
        have hassignSinCapital :
            assignStorageRef? config { contract := contract, locals := locals2 } evm1
              .storage SinRef (.int (Int.ofNat SinNew.toNat)) =
                .ok ({ contract := contract, locals := locals2 }, evm2) := by
          simpa [evm2, evm1, evm0, initState, storageStore_executionEnv] using
            (assign_sinCapitalStorage evm1 (locals := locals2) SinNew
              (by simp [locals2, fessLocalsSinNewSinCapitalNew, fessLocalsSinNew,
                fessLocals]))
        have hbody :
            ExecTransitionBody config contract evm0 locals fessTransition.body
              (.returned { contract := contract, locals := locals2 } evm2 none) := by
          have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := locals)
            (by simp [locals, fessLocals]) hauthSolm
          have hblock :
              ExecBlock config { contract := contract, locals := locals } evm0
                [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
                  .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
                  .letDecl "sinNew" (some uint256)
                    (add256 (.storage (sinRef (.env .timestamp))) (.var "tab")),
                  .require (.binary .ge (.var "sinNew")
                    (.storage (sinRef (.env .timestamp)))),
                  .assign .storage (sinRef (.env .timestamp)) (.var "sinNew"),
                  .letDecl "SinNew" (some uint256) (add256 (.storage SinRef) (.var "tab")),
                  .require (.binary .ge (.var "SinNew") (.storage SinRef)),
                  .assign .storage SinRef (.var "SinNew") ]
                (.ok { contract := contract, locals := locals2 } evm2) := by
            refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
            · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
            refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
            refine ExecBlock.consNormal (ExecStmt.letDecl hfirstAdd) ?_
            refine ExecBlock.consNormal (ExecStmt.requireTrue hfirstRequire) ?_
            refine ExecBlock.consNormal (ExecStmt.assign hsinNewVar hassignSin) ?_
            refine ExecBlock.consNormal (ExecStmt.letDecl hsecondAdd) ?_
            refine ExecBlock.consNormal (ExecStmt.requireTrue hsecondRequire) ?_
            exact ExecBlock.consNormal (ExecStmt.assign hSinNewVar hassignSinCapital)
              ExecBlock.nil
          simpa [ExecTransitionBody, fessTransition, nonpayable, auth, checkedAddUintInto,
            evm0, locals] using ExecFuncBody.execBlockOK hblock
        have hfitEraRD :
            (solcSlotWord σ_evm I (solcMappingSlot ⟨4⟩ (fessEraKey I))).toNat +
              (fessTab I).toNat < UInt256.size := by
          simpa [vowSlotWord, tab, slot, eraSlot, hslot] using hfitEraEvm
        have hfitSinRD :
            (solcSlotWord
                (sstoreAccountMap I.codeOwner σ_evm (solcMappingSlot ⟨4⟩ (fessEraKey I))
                  (solcSlotWord σ_evm I (solcMappingSlot ⟨4⟩ (fessEraKey I)) + fessTab I))
                I ⟨5⟩).toNat + (fessTab I).toNat < UInt256.size := by
          simpa [σ1_evm, sinNew, vowSlotWord, tab, slot, eraSlot, hslot] using hfitSinEvm
        have hret := RD.vowFessSuccess hreach hperm hsz36 hsize hauthSolc
          hfitEraRD hfitSinRD
        have hcreated :
            (cA,
              sstoreAccountMap I.codeOwner σ1_evm ⟨5⟩ SinNew).1 = evm2.createdAccounts := by
          simp [evm2, evm1, evm0, initState, storageStore_createdAccounts]
        have haccounts :
            accountMapEquiv (sstoreAccountMap I.codeOwner σ1_evm ⟨5⟩ SinNew)
              evm2.accountMap := by
          simpa [evm2, evm1, evm0, initState, storageStore_accountMap] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨5⟩ SinNew haccounts1
        have henc : returnEquiv ByteArray.empty none fessTransition.returnType := by
          rw [show fessTransition.returnType = [] by rfl]
          exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
        have hret' :
            RDret vowBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (cA, sstoreAccountMap I.codeOwner σ1_evm ⟨5⟩ SinNew) ByteArray.empty := by
          simpa [σ1_evm, sinNew, SinNew, tab, eraSlot, slot, hslot, vowSlotWord] using hret
        exact hret'.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
          hcreated haccounts henc
      · have hoverSinEvm :
            UInt256.size ≤ (vowSlotWord ⟨5⟩ σ1_evm I).toNat + tab.toNat := by
          omega
        let SinNew := vowSlotWord ⟨5⟩ σ1_evm I + tab
        let locals2 := fessLocalsSinNewSinCapitalNew I sinNew SinNew
        have hsinCapitalWord :
            Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner ⟨5⟩ =
              vowSlotWord ⟨5⟩ σ1_evm I := by
          have hword := accountMapEquiv_storage_findD haccounts1 I.codeOwner ⟨5⟩ ⟨0⟩
          symm
          calc
            vowSlotWord ⟨5⟩ σ1_evm I = vowSlotWord ⟨5⟩ evm1.accountMap I := hword
            _ = Solm.EVM.storageLoad evm1 evm1.executionEnv.codeOwner ⟨5⟩ := by
              simp [vowSlotWord, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage, storageStore_executionEnv, evm1, evm0, initState]
        have hsinCapitalRead :
            evalExpr? config { contract := contract, locals := locals1 } evm1 (.storage SinRef) =
              .ok (.int (Int.ofNat (vowSlotWord ⟨5⟩ σ1_evm I).toNat)) := by
          simpa [hsinCapitalWord] using
            (evalExpr_sinCapitalStorage evm1 (locals := locals1)
              (by simp [locals1, fessLocalsSinNew, fessLocals]))
        have htab1 :
            evalExpr? config { contract := contract, locals := locals1 } evm1 (.var "tab") =
              .ok (.int (Int.ofNat tab.toNat)) := by
          simpa [tab] using
            (evalExpr_fessTab (evm := evm1) (I := I) (locals := locals1)
              (by simpa [locals1] using fessLocalsSinNew_get_tab I sinNew))
        have hsecondAddRev :
            evalExpr? config { contract := contract, locals := locals1 } evm1
              (add256 (.storage SinRef) (.var "tab")) = .revert := by
          exact evalExpr_add256_tab_revert (x := .storage SinRef)
            (old := vowSlotWord ⟨5⟩ σ1_evm I) (tab := tab)
            hsinCapitalRead htab1 hoverSinEvm
        have hbody : ExecTransitionBody config contract evm0 locals fessTransition.body .reverted := by
          have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := locals)
            (by simp [locals, fessLocals]) hauthSolm
          have hblock :
              ExecBlock config { contract := contract, locals := locals } evm0
                [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
                  .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
                  .letDecl "sinNew" (some uint256)
                    (add256 (.storage (sinRef (.env .timestamp))) (.var "tab")),
                  .require (.binary .ge (.var "sinNew")
                    (.storage (sinRef (.env .timestamp)))),
                  .assign .storage (sinRef (.env .timestamp)) (.var "sinNew"),
                  .letDecl "SinNew" (some uint256) (add256 (.storage SinRef) (.var "tab")),
                  .require (.binary .ge (.var "SinNew") (.storage SinRef)),
                  .assign .storage SinRef (.var "SinNew") ]
                .reverted := by
            refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
            · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
            refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
            refine ExecBlock.consNormal (ExecStmt.letDecl hfirstAdd) ?_
            refine ExecBlock.consNormal (ExecStmt.requireTrue hfirstRequire) ?_
            refine ExecBlock.consNormal (ExecStmt.assign hsinNewVar hassignSin) ?_
            exact ExecBlock.consRevert (ExecStmt.letDeclRevert hsecondAddRev)
          simpa [ExecTransitionBody, fessTransition, nonpayable, auth, checkedAddUintInto,
            evm0, locals] using ExecFuncBody.execBlockRevert hblock
        have hfitEraRD :
            (solcSlotWord σ_evm I (solcMappingSlot ⟨4⟩ (fessEraKey I))).toNat +
              (fessTab I).toNat < UInt256.size := by
          simpa [vowSlotWord, tab, slot, eraSlot, hslot] using hfitEraEvm
        have hoverSinRD :
            UInt256.size ≤
              (solcSlotWord
                  (sstoreAccountMap I.codeOwner σ_evm (solcMappingSlot ⟨4⟩ (fessEraKey I))
                    (solcSlotWord σ_evm I (solcMappingSlot ⟨4⟩ (fessEraKey I)) + fessTab I))
                  I ⟨5⟩).toNat + (fessTab I).toNat := by
          simpa [σ1_evm, sinNew, vowSlotWord, tab, slot, eraSlot, hslot] using hoverSinEvm
        have hrev := RD.vowFessSecondAddOverflow hreach hperm hsz36 hsize hauthSolc
          hfitEraRD hoverSinRD
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hoverEraEvm :
          UInt256.size ≤ (vowSlotWord slot σ_evm I).toNat + tab.toNat := by
        omega
      have hoverEraSolm :
          UInt256.size ≤ (vowSlotWord slot σ_solm I).toNat + tab.toNat := by
        rw [← hsinWord]
        exact hoverEraEvm
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hsinRead0 :
          evalExpr? config { contract := contract, locals := locals } evm0
            (.storage (sinRef (.env .timestamp))) =
              .ok (.int (Int.ofNat (vowSlotWord slot σ_solm I).toNat)) := by
        simpa [evm0, locals, slot] using
          (evalExpr_fessSinStorage (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals)
            (by simp [locals, fessLocals]))
      have htab0 :
          evalExpr? config { contract := contract, locals := locals } evm0 (.var "tab") =
            .ok (.int (Int.ofNat tab.toNat)) := by
        simpa [evm0, locals, tab] using
          (evalExpr_fessTab (evm := evm0) (I := I) (locals := locals)
            (by simpa [locals] using fessLocals_get_tab I))
      have hfirstAddRev :
          evalExpr? config { contract := contract, locals := locals } evm0
            (add256 (.storage (sinRef (.env .timestamp))) (.var "tab")) = .revert := by
        exact evalExpr_add256_tab_revert
          (x := .storage (sinRef (.env .timestamp))) (old := vowSlotWord slot σ_solm I)
          (tab := tab) hsinRead0 htab0 hoverEraSolm
      have hbody : ExecTransitionBody config contract evm0 locals fessTransition.body .reverted := by
        have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals, fessLocals]) hauthSolm
        have hblock :
            ExecBlock config { contract := contract, locals := locals } evm0
              [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
                .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
                .letDecl "sinNew" (some uint256)
                  (add256 (.storage (sinRef (.env .timestamp))) (.var "tab")),
                .require (.binary .ge (.var "sinNew") (.storage (sinRef (.env .timestamp)))),
                .assign .storage (sinRef (.env .timestamp)) (.var "sinNew"),
                .letDecl "SinNew" (some uint256) (add256 (.storage SinRef) (.var "tab")),
                .require (.binary .ge (.var "SinNew") (.storage SinRef)),
                .assign .storage SinRef (.var "SinNew") ]
              .reverted := by
          refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
          · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
          refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
          exact ExecBlock.consRevert (ExecStmt.letDeclRevert hfirstAddRev)
        simpa [ExecTransitionBody, fessTransition, nonpayable, auth, checkedAddUintInto,
          evm0, locals] using ExecFuncBody.execBlockRevert hblock
      have hoverEraRD :
          UInt256.size ≤
            (solcSlotWord σ_evm I (solcMappingSlot ⟨4⟩ (fessEraKey I))).toNat +
              (fessTab I).toNat := by
        simpa [vowSlotWord, tab, slot, eraSlot, hslot] using hoverEraEvm
      have hrev := RD.vowFessFirstAddOverflow hreach hsz36 hsize hauthSolc hoverEraRD
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hauthSolm : vowSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody : ExecTransitionBody config contract evm0 locals fessTransition.body .reverted := by
      have hguard := vowAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals, fessLocals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest :=
          checkedAddUintInto "sinNew" (.storage (sinRef (.env .timestamp))) (.var "tab") ++
          [ .assign .storage (sinRef (.env .timestamp)) (.var "sinNew") ] ++
          checkedAddUintInto "SinNew" (.storage SinRef) (.var "tab") ++
          [ .assign .storage SinRef (.var "SinNew") ])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, fessTransition, nonpayable, auth, evm0, locals] using
        ExecFuncBody.execBlockRevert hblock
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
    have hrev := RD.vowFessAuthRevert hreach hsz36 hsize hauthSolc
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFessBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x69, 0x7e, 0xfb, 0x78]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := by omega
  exact vowFessBodyCore hcode hwv hperm hsz36 hsize (vowDispatch_fess hsel)
    (by simpa [fessLocals] using vowDecode_fess_ok (I := I) hsz36)
    (vowReachFessBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
    hAccounts

theorem vowFessShort {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsel : selIs I ⟨#[0x69, 0x7e, 0xfb, 0x78]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hreach :=
    vowReachFessBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vowBytecode) (sel := vowSelWord I) (entry := ⟨571⟩) (ret := ⟨412⟩)
    (decoded := ⟨593⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (vowDispatch_fess hsel)
    (vowDecode_fess_none_short hsz4 hshort)

end Benchmarks.Dss.Vow
