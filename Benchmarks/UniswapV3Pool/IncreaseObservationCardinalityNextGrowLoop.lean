import Benchmarks.UniswapV3Pool.IncreaseObservationCardinalityNextGrowTail

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

theorem execWhile_var_state {cfg : Config} {C : ContractDecl}
    {cond : Expr} {body : List Stmt} (P : ℕ → Solm.Store → EVM.State → Prop)
    (hfalse : ∀ L evm, P 0 L evm →
        evalExpr? cfg { contract := C, locals := L } evm cond = .ok (.bool false))
    (htrue : ∀ v L evm, P (v + 1) L evm →
        evalExpr? cfg { contract := C, locals := L } evm cond = .ok (.bool true))
    (hstep : ∀ v L evm, P (v + 1) L evm →
        ∃ L' evm', ExecBlock cfg { contract := C, locals := L } evm body
          (.ok { contract := C, locals := L' } evm') ∧ P v L' evm') :
    ∀ v L evm, P v L evm → ∃ L' evm',
      ExecStmt cfg { contract := C, locals := L } evm (.while cond body)
        (.ok { contract := C, locals := L' } evm') ∧ P 0 L' evm' := by
  intro v
  induction v with
  | zero =>
      intro L evm hP
      exact ⟨L, evm, ExecStmt.whileFalse (hfalse L evm hP), hP⟩
  | succ v ih =>
      intro L evm hP
      obtain ⟨L1, evm1, hbody, hP1⟩ := hstep v L evm hP
      obtain ⟨L', evm', hwhile, hP'⟩ := ih L1 evm1 hP1
      exact ⟨L', evm', ExecStmt.whileTrue (htrue v L evm hP) hbody hwhile, hP'⟩

abbrev increaseObservationCardinalityNextGrowStoreWithI
    (σ : AccountMap) (I : ExecutionEnv) (i : UInt256) : Store :=
  (increaseObservationCardinalityNextStoreWithOldNew σ I).insert "i"
    (.int (Int.ofNat i.toNat))

abbrev increaseObservationCardinalityNextGrowObservationLoc (i : UInt256) : StorageLoc :=
  loc (increaseObservationCardinalityNextGrowObservationSlot i) ⟨0, by decide⟩
    ⟨4, by decide⟩ (by decide) (.int uint32Int)

abbrev increaseObservationCardinalityNextGrowObservationState
    (evm : EVM.State) (i : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (increaseObservationCardinalityNextGrowObservationSlot i)
    (increaseObservationCardinalityNextGrowObservationWord evm.accountMap evm.executionEnv i)

theorem evalExpr_increaseObservationCardinalityNext_i_withGrowStore
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) :
    evalExpr? (config v)
        { contract := contract v,
          locals := increaseObservationCardinalityNextGrowStoreWithI σ I i }
        evm (.var "i") =
      .ok (.int (Int.ofNat i.toNat)) := by
  rw [evalExpr?]
  rw [increaseObservationCardinalityNextGrowStoreWithI, store_get_self]
  rfl

theorem evalExpr_increaseObservationCardinalityNext_new_withGrowStore
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) :
    evalExpr? (config v)
        { contract := contract v,
          locals := increaseObservationCardinalityNextGrowStoreWithI σ I i }
        evm (.var "observationCardinalityNextNew") =
      .ok (increaseObservationCardinalityNextArgValue I) := by
  rw [evalExpr?]
  rw [increaseObservationCardinalityNextGrowStoreWithI]
  rw [store_get_ne (increaseObservationCardinalityNextStoreWithOldNew σ I)
    (.int (Int.ofNat i.toNat)) (by decide)]
  rw [increaseObservationCardinalityNextStoreWithOldNew_new]
  rfl

theorem evalExpr_increaseObservationCardinalityNext_loopCond_true
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) (hlt : i.toNat < (increaseObservationCardinalityNextArgWord I).toNat) :
    evalExpr? (config v)
        { contract := contract v,
          locals := increaseObservationCardinalityNextGrowStoreWithI σ I i }
        evm (ltE (.var "i") (.var "observationCardinalityNextNew")) =
      .ok (.bool true) := by
  simp only [ltE, evalExpr?, evalExpr_increaseObservationCardinalityNext_i_withGrowStore,
    evalExpr_increaseObservationCardinalityNext_new_withGrowStore, EvalResult.bind, bind,
    evalBinaryOp?]
  simp [hlt]

theorem evalExpr_increaseObservationCardinalityNext_loopCond_false
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) (hle : (increaseObservationCardinalityNextArgWord I).toNat ≤ i.toNat) :
    evalExpr? (config v)
        { contract := contract v,
          locals := increaseObservationCardinalityNextGrowStoreWithI σ I i }
        evm (ltE (.var "i") (.var "observationCardinalityNextNew")) =
      .ok (.bool false) := by
  simp only [ltE, evalExpr?, evalExpr_increaseObservationCardinalityNext_i_withGrowStore,
    evalExpr_increaseObservationCardinalityNext_new_withGrowStore, EvalResult.bind, bind,
    evalBinaryOp?]
  simp [not_lt.mpr hle]

theorem evalExpr_increaseObservationCardinalityNext_one {v : PoolImmutables}
    (solm : Frame) (evm : EVM.State) :
    evalExpr? (config v) solm evm (.intLit 1) = .ok (.int 1) := by
  simp only [evalExpr?, pure]

theorem evalExpr_increaseObservationCardinalityNext_i_add_one_withGrowStore
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) :
    evalExpr? (config v)
        { contract := contract v,
          locals := increaseObservationCardinalityNextGrowStoreWithI σ I i }
        evm (addE (.var "i") (.intLit 1)) =
      .ok (.int (Int.ofNat (i.toNat + 1))) := by
  have hcast : Int.ofNat i.toNat + 1 = Int.ofNat (i.toNat + 1) := by
    simp only [Int.ofNat_eq_natCast]
    exact
      ((Nat.cast_add i.toNat 1 :
        ((i.toNat + 1 : Nat) : Int) = (i.toNat : Int) + (1 : Int)).symm)
  simp only [addE, evalExpr?, evalExpr_increaseObservationCardinalityNext_i_withGrowStore,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hcast]

theorem assignStorageRef_increaseObservationCardinalityNext_i_next
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) :
    assignStorageRef? (config v)
        { contract := contract v,
          locals := increaseObservationCardinalityNextGrowStoreWithI σ I i }
        evm .localVar (varRef "i") (.int (Int.ofNat (i.toNat + 1))) =
      .ok
        ({ contract := contract v,
           locals := (increaseObservationCardinalityNextGrowStoreWithI σ I i).insert "i"
             (.int (Int.ofNat (i.toNat + 1))) }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [increaseObservationCardinalityNextGrowStoreWithI, store_get_self]
  simp [updateLocalPath?, pure, bind, EvalResult.bind]

theorem natLorShift32One (q : Nat) : Nat.lor 1 (q * 2 ^ 32) = 1 + q * 2 ^ 32 := by
  rw [nat_lor_shift_add 1 q 32 (by norm_num)]

theorem increaseObservationCardinalityNextGrowObservationWord_toNat
    (old : UInt256) :
    (UInt256.lor
        (UInt256.land (⟨4294967295⟩ : UInt256) (⟨1⟩ : UInt256))
        (UInt256.land (UInt256.lnot (⟨4294967295⟩ : UInt256)) old)).toNat =
      1 + (old.toNat / 2 ^ 32) * 2 ^ 32 := by
  have hlow :
      (UInt256.land (⟨4294967295⟩ : UInt256) (⟨1⟩ : UInt256)).toNat = 1 := by
    native_decide
  have hmask :
      UInt256.lnot (⟨4294967295⟩ : UInt256) =
        UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 32) := by
    native_decide
  have hhigh :
      (UInt256.land (UInt256.lnot (⟨4294967295⟩ : UInt256)) old).toNat =
        (old.toNat / 2 ^ 32) * 2 ^ 32 := by
    rw [hmask]
    exact u256_land_high_mask_toNat old 32 (by norm_num)
  rw [u256_lor_toNat, hlow, hhigh, natLorShift32One]
  rw [Nat.mod_eq_of_lt]
  have hq : old.toNat / 2 ^ 32 < 2 ^ 224 := by
    norm_num [UInt256.size] at old ⊢
    exact Nat.div_lt_of_lt_mul old.val.isLt
  have hmul : old.toNat / 2 ^ 32 * 2 ^ 32 ≤ (2 ^ 224 - 1) * 2 ^ 32 := by
    exact Nat.mul_le_mul_right _ (Nat.le_pred_of_lt hq)
  norm_num [UInt256.size, Nat.pow_add] at hmul ⊢
  omega

theorem storageLocStore_increaseObservationCardinalityNext_growObservation
    (evm : EVM.State) (i : UInt256) :
    storageLocStore evm (increaseObservationCardinalityNextGrowObservationLoc i) (.int 1) =
      some (increaseObservationCardinalityNextGrowObservationState evm i) := by
  unfold storageLocStore storageLocWriteWord
    increaseObservationCardinalityNextGrowObservationLoc
    increaseObservationCardinalityNextGrowObservationState
    increaseObservationCardinalityNextGrowObservationWord loc
  simp only [valueToWord, bind, Option.bind]
  rw [show EVM.wordOfInt 1 = (⟨1⟩ : UInt256) by native_decide]
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (4 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (4 : Fin 33).val) _) =
        (UInt256.lor
          (UInt256.land (⟨4294967295⟩ : UInt256) (⟨1⟩ : UInt256))
          (UInt256.land (UInt256.lnot (⟨4294967295⟩ : UInt256))
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (UInt256.land (⟨65535⟩ : UInt256) i + ⟨8⟩)))).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (4 : Fin 33).val = 4 from rfl,
    List.take_zero, List.nil_append]
  rw [show List.take 4 (EVM.Word.toBytesLEWithSizeProof (⟨1⟩ : UInt256)).1 =
      [1, 0, 0, 0] by native_decide]
  rw [fromBytes'_append, fromBytes'_drop_wordLE]
  simp [fromBytes']
  rw [increaseObservationCardinalityNextGrowObservationWord_toNat]
  ring_nf

theorem increaseObservationCardinalityNextGrowObservationSlot_eq_observationBase
    (i : UInt256) (hlt : i.toNat < 65535) :
    increaseObservationCardinalityNextGrowObservationSlot i =
      observationBase (.int (Int.ofNat i.toNat)) := by
  have hclean :
      UInt256.land (⟨65535⟩ : UInt256) i = i := by
    simpa [slot0Uint16Mask] using
      slot0Uint16Mask_clean_left (w := i) (by
        simpa [EVM.twoPow] using (by omega : i.toNat < 65536))
  unfold increaseObservationCardinalityNextGrowObservationSlot observationBase
  rw [keyValueToWord_uint256, hclean, u256_ofNat_toNat]
  exact u256_add_comm i ⟨8⟩

abbrev increaseObservationCardinalityNextGrowObservationEvaledRef (i : UInt256) :
    EvaledStorageRef :=
  { base := "observationsRaw",
    steps := [.mindex (.int (Int.ofNat i.toNat)), .field "blockTimestamp"] }

theorem evalStorageRef_increaseObservationCardinalityNext_growObservation
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) :
    evalStorageRef (config v)
        { contract := contract v,
          locals := increaseObservationCardinalityNextGrowStoreWithI σ I i }
        evm (observationsRawF (.var "i") "blockTimestamp") =
      .ok (increaseObservationCardinalityNextGrowObservationEvaledRef i) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, observationsRawF,
    increaseObservationCardinalityNextGrowObservationEvaledRef,
    evalExpr_increaseObservationCardinalityNext_i_withGrowStore,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem assignStorageRef_increaseObservationCardinalityNext_growObservation
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) (hlt : i.toNat < 65535) :
    assignStorageRef? (config v)
        { contract := contract v,
          locals := increaseObservationCardinalityNextGrowStoreWithI σ I i }
        evm .storage (observationsRawF (.var "i") "blockTimestamp") (.int 1) =
      .ok
        ({ contract := contract v,
           locals := increaseObservationCardinalityNextGrowStoreWithI σ I i },
          increaseObservationCardinalityNextGrowObservationState evm i) := by
  apply assignStorageRef_storage_scalar_value
      (er := increaseObservationCardinalityNextGrowObservationEvaledRef i)
      (ty := .elem (.int uint32Int))
      (loc := increaseObservationCardinalityNextGrowObservationLoc i)
  · simp [observationsRawF, increaseObservationCardinalityNextGrowStoreWithI,
      increaseObservationCardinalityNextStoreWithOldNew,
      increaseObservationCardinalityNextStoreWithOld, increaseObservationCardinalityNextStore]
  · exact evalStorageRef_increaseObservationCardinalityNext_growObservation (v := v) evm σ I i
  · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, observationStructTy, uint32St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      increaseObservationCardinalityNextGrowObservationEvaledRef,
      increaseObservationCardinalityNextGrowObservationLoc, loc]
    exact (increaseObservationCardinalityNextGrowObservationSlot_eq_observationBase i hlt).symm
  · trivial
  · exact storageLocStore_increaseObservationCardinalityNext_growObservation evm i

theorem execBlock_increaseObservationCardinalityNext_growLoopBody
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) (hlt : i.toNat < 65535) :
    ExecBlock (config v)
      { contract := contract v,
        locals := increaseObservationCardinalityNextGrowStoreWithI σ I i }
      evm
      [ .assign .storage (observationsRawF (.var "i") "blockTimestamp") (.intLit 1),
        .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ]
      (.ok
        { contract := contract v,
          locals := (increaseObservationCardinalityNextGrowStoreWithI σ I i).insert "i"
            (.int (Int.ofNat (i.toNat + 1))) }
        (increaseObservationCardinalityNextGrowObservationState evm i)) := by
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_increaseObservationCardinalityNext_one _ _)
      (assignStorageRef_increaseObservationCardinalityNext_growObservation
        (v := v) evm σ I i hlt)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_increaseObservationCardinalityNext_i_add_one_withGrowStore
        (v := v) (increaseObservationCardinalityNextGrowObservationState evm i) σ I i)
      (assignStorageRef_increaseObservationCardinalityNext_i_next
        (v := v) (increaseObservationCardinalityNextGrowObservationState evm i) σ I i))
    ExecBlock.nil

structure increaseObservationCardinalityNextGrowLocals
    (σ : AccountMap) (I : ExecutionEnv) (i : UInt256) (L : Store) : Prop where
  i_get : L.get? "i" = some (.int (Int.ofNat i.toNat))
  new_get : L.get? "observationCardinalityNextNew" =
    some (increaseObservationCardinalityNextArgValue I)
  observationsRaw_get : L.get? "observationsRaw" = none
  slot0_get : L.get? "slot0" = none

theorem increaseObservationCardinalityNextGrowLocals_initial
    (σ : AccountMap) (I : ExecutionEnv) (i : UInt256) :
    increaseObservationCardinalityNextGrowLocals σ I i
      (increaseObservationCardinalityNextGrowStoreWithI σ I i) := by
  constructor
  · rw [increaseObservationCardinalityNextGrowStoreWithI, store_get_self]
  · rw [increaseObservationCardinalityNextGrowStoreWithI]
    rw [store_get_ne (increaseObservationCardinalityNextStoreWithOldNew σ I)
      (.int (Int.ofNat i.toNat)) (by decide)]
    exact increaseObservationCardinalityNextStoreWithOldNew_new σ I
  · simp [increaseObservationCardinalityNextGrowStoreWithI,
      increaseObservationCardinalityNextStoreWithOldNew,
      increaseObservationCardinalityNextStoreWithOld,
      increaseObservationCardinalityNextStore]
  · simp [increaseObservationCardinalityNextGrowStoreWithI,
      increaseObservationCardinalityNextStoreWithOldNew,
      increaseObservationCardinalityNextStoreWithOld,
      increaseObservationCardinalityNextStore]

theorem increaseObservationCardinalityNextGrowLocals_insert_next
    {σ : AccountMap} {I : ExecutionEnv} {i : UInt256} {L : Store}
    (hL : increaseObservationCardinalityNextGrowLocals σ I i L)
    (hlt : i.toNat < 65535) :
    increaseObservationCardinalityNextGrowLocals σ I (UInt256.ofNat (i.toNat + 1))
      (L.insert "i" (.int (Int.ofNat (i.toNat + 1)))) := by
  have htoNat : (UInt256.ofNat (i.toNat + 1)).toNat = i.toNat + 1 := by
    exact ulit_toNat' (i.toNat + 1) (by
      norm_num [UInt256.size]
      omega)
  constructor
  · rw [store_get_self, htoNat]
  · rw [store_get_ne L (.int (Int.ofNat (i.toNat + 1))) (by decide)]
    exact hL.new_get
  · rw [store_get_ne L (.int (Int.ofNat (i.toNat + 1))) (by decide)]
    exact hL.observationsRaw_get
  · rw [store_get_ne L (.int (Int.ofNat (i.toNat + 1))) (by decide)]
    exact hL.slot0_get

theorem evalExpr_increaseObservationCardinalityNext_i_withGrowLocals
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) (L : Store)
    (hL : increaseObservationCardinalityNextGrowLocals σ I i L) :
    evalExpr? (config v) { contract := contract v, locals := L } evm (.var "i") =
      .ok (.int (Int.ofNat i.toNat)) := by
  rw [evalExpr?]
  rw [hL.i_get]
  rfl

theorem evalExpr_increaseObservationCardinalityNext_new_withGrowLocals
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) (L : Store)
    (hL : increaseObservationCardinalityNextGrowLocals σ I i L) :
    evalExpr? (config v) { contract := contract v, locals := L } evm
        (.var "observationCardinalityNextNew") =
      .ok (increaseObservationCardinalityNextArgValue I) := by
  rw [evalExpr?]
  rw [hL.new_get]
  rfl

theorem evalExpr_increaseObservationCardinalityNext_loopCond_true_withGrowLocals
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) (L : Store)
    (hL : increaseObservationCardinalityNextGrowLocals σ I i L)
    (hlt : i.toNat < (increaseObservationCardinalityNextArgWord I).toNat) :
    evalExpr? (config v) { contract := contract v, locals := L } evm
        (ltE (.var "i") (.var "observationCardinalityNextNew")) =
      .ok (.bool true) := by
  simp only [ltE, evalExpr?,
    evalExpr_increaseObservationCardinalityNext_i_withGrowLocals
      (v := v) evm σ I i L hL,
    evalExpr_increaseObservationCardinalityNext_new_withGrowLocals
      (v := v) evm σ I i L hL,
    EvalResult.bind, bind, evalBinaryOp?]
  simp [hlt]

theorem evalExpr_increaseObservationCardinalityNext_loopCond_false_withGrowLocals
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) (L : Store)
    (hL : increaseObservationCardinalityNextGrowLocals σ I i L)
    (hle : (increaseObservationCardinalityNextArgWord I).toNat ≤ i.toNat) :
    evalExpr? (config v) { contract := contract v, locals := L } evm
        (ltE (.var "i") (.var "observationCardinalityNextNew")) =
      .ok (.bool false) := by
  simp only [ltE, evalExpr?,
    evalExpr_increaseObservationCardinalityNext_i_withGrowLocals
      (v := v) evm σ I i L hL,
    evalExpr_increaseObservationCardinalityNext_new_withGrowLocals
      (v := v) evm σ I i L hL,
    EvalResult.bind, bind, evalBinaryOp?]
  simp [not_lt.mpr hle]

theorem evalExpr_increaseObservationCardinalityNext_i_add_one_withGrowLocals
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) (L : Store)
    (hL : increaseObservationCardinalityNextGrowLocals σ I i L) :
    evalExpr? (config v) { contract := contract v, locals := L } evm
        (addE (.var "i") (.intLit 1)) =
      .ok (.int (Int.ofNat (i.toNat + 1))) := by
  have hcast : Int.ofNat i.toNat + 1 = Int.ofNat (i.toNat + 1) := by
    simp only [Int.ofNat_eq_natCast]
    exact
      ((Nat.cast_add i.toNat 1 :
        ((i.toNat + 1 : Nat) : Int) = (i.toNat : Int) + (1 : Int)).symm)
  simp only [addE, evalExpr?,
    evalExpr_increaseObservationCardinalityNext_i_withGrowLocals
      (v := v) evm σ I i L hL,
    EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hcast]

theorem evalStorageRef_increaseObservationCardinalityNext_growObservation_withGrowLocals
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) (L : Store)
    (hL : increaseObservationCardinalityNextGrowLocals σ I i L) :
    evalStorageRef (config v) { contract := contract v, locals := L } evm
        (observationsRawF (.var "i") "blockTimestamp") =
      .ok (increaseObservationCardinalityNextGrowObservationEvaledRef i) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, observationsRawF,
    increaseObservationCardinalityNextGrowObservationEvaledRef,
    evalExpr_increaseObservationCardinalityNext_i_withGrowLocals
      (v := v) evm σ I i L hL,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem assignStorageRef_increaseObservationCardinalityNext_growObservation_withGrowLocals
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) (L : Store)
    (hL : increaseObservationCardinalityNextGrowLocals σ I i L) (hlt : i.toNat < 65535) :
    assignStorageRef? (config v) { contract := contract v, locals := L } evm .storage
        (observationsRawF (.var "i") "blockTimestamp") (.int 1) =
      .ok
        ({ contract := contract v, locals := L },
          increaseObservationCardinalityNextGrowObservationState evm i) := by
  apply assignStorageRef_storage_scalar_value
      (er := increaseObservationCardinalityNextGrowObservationEvaledRef i)
      (ty := .elem (.int uint32Int))
      (loc := increaseObservationCardinalityNextGrowObservationLoc i)
  · exact hL.observationsRaw_get
  · exact evalStorageRef_increaseObservationCardinalityNext_growObservation_withGrowLocals
      (v := v) evm σ I i L hL
  · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, observationStructTy, uint32St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      increaseObservationCardinalityNextGrowObservationEvaledRef,
      increaseObservationCardinalityNextGrowObservationLoc, loc]
    exact (increaseObservationCardinalityNextGrowObservationSlot_eq_observationBase i hlt).symm
  · trivial
  · exact storageLocStore_increaseObservationCardinalityNext_growObservation evm i

theorem assignStorageRef_increaseObservationCardinalityNext_i_next_withGrowLocals
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) (L : Store)
    (hL : increaseObservationCardinalityNextGrowLocals σ I i L) :
    assignStorageRef? (config v) { contract := contract v, locals := L } evm .localVar
        (varRef "i") (.int (Int.ofNat (i.toNat + 1))) =
      .ok
        ({ contract := contract v,
           locals := L.insert "i" (.int (Int.ofNat (i.toNat + 1))) }, evm) := by
  rw [assignStorageRef?]
  rw [varRef]
  rw [hL.i_get]
  simp [updateLocalPath?, pure, bind, EvalResult.bind]

theorem execBlock_increaseObservationCardinalityNext_growLoopBody_withGrowLocals
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) (L : Store)
    (hL : increaseObservationCardinalityNextGrowLocals σ I i L) (hlt : i.toNat < 65535) :
    ExecBlock (config v) { contract := contract v, locals := L } evm
      [ .assign .storage (observationsRawF (.var "i") "blockTimestamp") (.intLit 1),
        .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ]
      (.ok
        { contract := contract v,
          locals := L.insert "i" (.int (Int.ofNat (i.toNat + 1))) }
        (increaseObservationCardinalityNextGrowObservationState evm i)) := by
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_increaseObservationCardinalityNext_one _ _)
      (assignStorageRef_increaseObservationCardinalityNext_growObservation_withGrowLocals
        (v := v) evm σ I i L hL hlt)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_increaseObservationCardinalityNext_i_add_one_withGrowLocals
        (v := v) (increaseObservationCardinalityNextGrowObservationState evm i) σ I i L hL)
      (assignStorageRef_increaseObservationCardinalityNext_i_next_withGrowLocals
        (v := v) (increaseObservationCardinalityNextGrowObservationState evm i) σ I i L hL))
    ExecBlock.nil

def increaseObservationCardinalityNextGrowLoopSourceState :
    Nat → EVM.State → UInt256 → EVM.State
  | 0, evm, _ => evm
  | n + 1, evm, i =>
      increaseObservationCardinalityNextGrowLoopSourceState n
        (increaseObservationCardinalityNextGrowObservationState evm i)
        (UInt256.ofNat (i.toNat + 1))

theorem execStmt_increaseObservationCardinalityNext_growLoopAux
    {v : PoolImmutables} (σ : AccountMap) (I : ExecutionEnv) :
    ∀ (n : Nat) (evm : EVM.State) (i : UInt256) (L : Store),
      increaseObservationCardinalityNextGrowLocals σ I i L →
      i.toNat ≤ (increaseObservationCardinalityNextArgWord I).toNat →
      n = (increaseObservationCardinalityNextArgWord I).toNat - i.toNat →
      (increaseObservationCardinalityNextArgWord I).toNat ≤ 65535 →
      ∃ L',
        ExecStmt (config v) { contract := contract v, locals := L } evm
          (.while (ltE (.var "i") (.var "observationCardinalityNextNew"))
            [ .assign .storage (observationsRawF (.var "i") "blockTimestamp") (.intLit 1),
              .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ])
          (.ok { contract := contract v, locals := L' }
            (increaseObservationCardinalityNextGrowLoopSourceState n evm i)) ∧
        increaseObservationCardinalityNextGrowLocals σ I
          (increaseObservationCardinalityNextArgWord I) L' := by
  intro n
  induction n with
  | zero =>
      intro evm i L hL hle hn _hnewBound
      have hge : (increaseObservationCardinalityNextArgWord I).toNat ≤ i.toNat := by
        omega
      have hiNat : i.toNat = (increaseObservationCardinalityNextArgWord I).toNat := by
        omega
      have hi : i = increaseObservationCardinalityNextArgWord I := by
        exact u256_inj hiNat
      subst i
      refine ⟨L, ?_, hL⟩
      simpa [increaseObservationCardinalityNextGrowLoopSourceState] using
        ExecStmt.whileFalse
          (evalExpr_increaseObservationCardinalityNext_loopCond_false_withGrowLocals
            (v := v) evm σ I (increaseObservationCardinalityNextArgWord I) L hL
            (by omega))
  | succ n ih =>
      intro evm i L hL hle hn hnewBound
      have hlt : i.toNat < (increaseObservationCardinalityNextArgWord I).toNat := by
        omega
      have hiBound : i.toNat < 65535 := by
        omega
      let i' : UInt256 := UInt256.ofNat (i.toNat + 1)
      have hbody :=
        execBlock_increaseObservationCardinalityNext_growLoopBody_withGrowLocals
          (v := v) evm σ I i L hL hiBound
      have hLnext :
          increaseObservationCardinalityNextGrowLocals σ I i'
            (L.insert "i" (.int (Int.ofNat (i.toNat + 1)))) := by
        dsimp [i']
        exact increaseObservationCardinalityNextGrowLocals_insert_next hL hiBound
      have hi'toNat : i'.toNat = i.toNat + 1 := by
        dsimp [i']
        exact ulit_toNat' (i.toNat + 1) (by
          norm_num [UInt256.size]
          omega)
      have hleNext : i'.toNat ≤ (increaseObservationCardinalityNextArgWord I).toNat := by
        rw [hi'toNat]
        omega
      have hnNext : n = (increaseObservationCardinalityNextArgWord I).toNat - i'.toNat := by
        rw [hi'toNat]
        omega
      obtain ⟨L', hwhile, hL'⟩ :=
        ih (increaseObservationCardinalityNextGrowObservationState evm i) i'
          (L.insert "i" (.int (Int.ofNat (i.toNat + 1)))) hLnext hleNext hnNext hnewBound
      refine ⟨L', ?_, hL'⟩
      exact ExecStmt.whileTrue
        (evalExpr_increaseObservationCardinalityNext_loopCond_true_withGrowLocals
          (v := v) evm σ I i L hL hlt)
        hbody
        (by
          simpa [increaseObservationCardinalityNextGrowLoopSourceState, i'] using hwhile)

theorem execStmt_increaseObservationCardinalityNext_growLoop
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (i : UInt256) (L : Store)
    (hL : increaseObservationCardinalityNextGrowLocals σ I i L)
    (hle : i.toNat ≤ (increaseObservationCardinalityNextArgWord I).toNat)
    (hnewBound : (increaseObservationCardinalityNextArgWord I).toNat ≤ 65535) :
    ∃ L',
      ExecStmt (config v) { contract := contract v, locals := L } evm
        (.while (ltE (.var "i") (.var "observationCardinalityNextNew"))
          [ .assign .storage (observationsRawF (.var "i") "blockTimestamp") (.intLit 1),
            .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ])
        (.ok { contract := contract v, locals := L' }
          (increaseObservationCardinalityNextGrowLoopSourceState
            ((increaseObservationCardinalityNextArgWord I).toNat - i.toNat) evm i)) ∧
      increaseObservationCardinalityNextGrowLocals σ I
        (increaseObservationCardinalityNextArgWord I) L' := by
  exact execStmt_increaseObservationCardinalityNext_growLoopAux (v := v) σ I
    ((increaseObservationCardinalityNextArgWord I).toNat - i.toNat) evm i L
    hL hle rfl hnewBound

abbrev increaseObservationCardinalityNextObsNextSlotWord
    (evm : EVM.State) (obsNext : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromBytes'
      ((List.take 27
          (EVM.Word.toBytesLEWithSizeProof
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).1 ++
        List.take 2 (EVM.Word.toBytesLEWithSizeProof obsNext).1) ++
        List.drop (27 + 2)
          (EVM.Word.toBytesLEWithSizeProof
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).1))

abbrev increaseObservationCardinalityNextAfterObsNextState
    (evm : EVM.State) (obsNext : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (increaseObservationCardinalityNextObsNextSlotWord evm obsNext)

theorem storageLocStore_increaseObservationCardinalityNext_obsNext
    (evm : EVM.State) (obsNext : UInt256) :
    storageLocStore evm increaseObservationCardinalityNextObservationCardinalityNextLoc
        (.int (Int.ofNat obsNext.toNat)) =
      some (increaseObservationCardinalityNextAfterObsNextState evm obsNext) := by
  unfold storageLocStore storageLocWriteWord
    increaseObservationCardinalityNextObservationCardinalityNextLoc loc
    increaseObservationCardinalityNextAfterObsNextState
    increaseObservationCardinalityNextObsNextSlotWord
  simp only [valueToWord, bind, Option.bind]
  rw [show EVM.wordOfInt (Int.ofNat obsNext.toNat) = obsNext by
    exact wordOfInt_ofNat_toNat _]
  apply congrArg some
  apply congrArg (fun w : UInt256 =>
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ w)
  apply u256_inj
  rw [ulit_toNat']
  · rfl
  · let bs :=
        ((List.take 27
            (EVM.Word.toBytesLEWithSizeProof
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).1 ++
          List.take 2 (EVM.Word.toBytesLEWithSizeProof obsNext).1) ++
          List.drop (27 + 2)
            (EVM.Word.toBytesLEWithSizeProof
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).1)
    have hlen : bs.length = 32 := by
      simp [bs, List.length_take, List.length_drop,
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).2,
        (EVM.Word.toBytesLEWithSizeProof obsNext).2]
    apply lt_of_lt_of_le (b := 2 ^ (8 * bs.length))
    · simpa [bs] using (EVM.fromBytes'_le (bs := bs))
    · rw [hlen]
      norm_num [UInt256.size]

theorem assignStorageRef_increaseObservationCardinalityNext_obsNext_withGrowLocals
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (L : Store)
    (hL : increaseObservationCardinalityNextGrowLocals σ I
      (increaseObservationCardinalityNextArgWord I) L) :
    assignStorageRef? (config v) { contract := contract v, locals := L } evm .storage
        (slot0F "observationCardinalityNext")
        (increaseObservationCardinalityNextArgValue I) =
      .ok
        ({ contract := contract v, locals := L },
          increaseObservationCardinalityNextAfterObsNextState evm
            (increaseObservationCardinalityNextArgWord I)) := by
  apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "observationCardinalityNext"] })
      (ty := .elem (.int uint16Int))
      (loc := increaseObservationCardinalityNextObservationCardinalityNextLoc)
  · exact hL.slot0_get
  · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
  · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, uint16St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      increaseObservationCardinalityNextObservationCardinalityNextLoc, loc]
  · trivial
  · exact storageLocStore_increaseObservationCardinalityNext_obsNext evm
      (increaseObservationCardinalityNextArgWord I)

theorem increaseObservationCardinalityNextArgWord_lt_twoPow16 (I : ExecutionEnv) :
    (increaseObservationCardinalityNextArgWord I).toNat < EVM.twoPow 16 := by
  have hmask : increaseObservationCardinalityNextUint16Mask = slot0Uint16Mask := by
    native_decide
  simpa [increaseObservationCardinalityNextArgWord, hmask] using
    slot0Uint16Mask_bound (calldataWord I.calldata 4)

theorem increaseObservationCardinalityNextArgWord_le_65535 (I : ExecutionEnv) :
    (increaseObservationCardinalityNextArgWord I).toNat ≤ 65535 := by
  have hlt := increaseObservationCardinalityNextArgWord_lt_twoPow16 I
  norm_num [EVM.twoPow] at hlt ⊢
  omega

theorem evalExpr_increaseObservationCardinalityNext_newLeOld_false
    {v : PoolImmutables} (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (hnewGt : (increaseObservationCardinalityNextOldWord σ I).toNat <
      (increaseObservationCardinalityNextArgWord I).toNat) :
    evalExpr? (config v)
        { contract := contract v, locals := increaseObservationCardinalityNextStoreWithOldNew σ I }
        evm (leE (.var "observationCardinalityNextNew")
          (.var "observationCardinalityNextOld")) =
      .ok (.bool false) := by
  simp only [leE, evalExpr?, evalExpr_increaseObservationCardinalityNext_new_withOldNew,
    evalExpr_increaseObservationCardinalityNext_old_withOldNew, EvalResult.bind, bind,
    evalBinaryOp?]
  simp [not_le.mpr hnewGt]

theorem uniswapV3PoolIncreaseObservationCardinalityNextSourceGrowPrefix
    {v : PoolImmutables} {evm : EVM.State} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (holdNonzero : increaseObservationCardinalityNextOldWord evm.accountMap I ≠ ⟨0⟩)
    (hnewGt : (increaseObservationCardinalityNextOldWord evm.accountMap I).toNat <
      (increaseObservationCardinalityNextArgWord I).toNat) :
    ∃ L',
      ExecBlock (config v)
        { contract := contract v, locals := increaseObservationCardinalityNextStore I } evm
        [ .letDecl "observationCardinalityNextOld" (some uint16)
            (.storage (slot0F "observationCardinalityNext")),
          .letDecl "observationCardinalityNextNew" (some uint16)
            (.var "observationCardinalityNext"),
          .require (gtE (.var "observationCardinalityNextOld") (.intLit 0)),
          Stmt.ite (leE (.var "observationCardinalityNextNew")
              (.var "observationCardinalityNextOld"))
            [ .assign .localVar (varRef "observationCardinalityNextNew")
                (.var "observationCardinalityNextOld") ]
            [ .letDecl "i" (some uint16) (.var "observationCardinalityNextOld"),
              .while (ltE (.var "i") (.var "observationCardinalityNextNew"))
                [ .assign .storage (observationsRawF (.var "i") "blockTimestamp")
                    (.intLit 1),
                  .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ] ] ]
        (.ok { contract := contract v, locals := L' }
          (increaseObservationCardinalityNextGrowLoopSourceState
            ((increaseObservationCardinalityNextArgWord I).toNat -
              (increaseObservationCardinalityNextOldWord evm.accountMap I).toNat)
            evm (increaseObservationCardinalityNextOldWord evm.accountMap I))) ∧
      increaseObservationCardinalityNextGrowLocals evm.accountMap I
        (increaseObservationCardinalityNextArgWord I) L' := by
  have hbranch :
      ∃ L',
        ExecBlock (config v)
          { contract := contract v,
            locals := increaseObservationCardinalityNextStoreWithOldNew evm.accountMap I }
          evm
          [ .letDecl "i" (some uint16) (.var "observationCardinalityNextOld"),
            .while (ltE (.var "i") (.var "observationCardinalityNextNew"))
              [ .assign .storage (observationsRawF (.var "i") "blockTimestamp") (.intLit 1),
                .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ] ]
          (.ok { contract := contract v, locals := L' }
            (increaseObservationCardinalityNextGrowLoopSourceState
              ((increaseObservationCardinalityNextArgWord I).toNat -
                (increaseObservationCardinalityNextOldWord evm.accountMap I).toNat)
              evm (increaseObservationCardinalityNextOldWord evm.accountMap I))) ∧
        increaseObservationCardinalityNextGrowLocals evm.accountMap I
          (increaseObservationCardinalityNextArgWord I) L' := by
    have hinit :=
      increaseObservationCardinalityNextGrowLocals_initial evm.accountMap I
        (increaseObservationCardinalityNextOldWord evm.accountMap I)
    obtain ⟨L', hwhile, hL'⟩ :=
      execStmt_increaseObservationCardinalityNext_growLoop
        (v := v) evm evm.accountMap I
        (increaseObservationCardinalityNextOldWord evm.accountMap I)
        (increaseObservationCardinalityNextGrowStoreWithI evm.accountMap I
          (increaseObservationCardinalityNextOldWord evm.accountMap I))
        hinit (by omega) (increaseObservationCardinalityNextArgWord_le_65535 I)
    exact ⟨L',
      ExecBlock.consNormal
        (ExecStmt.letDecl
          (evalExpr_increaseObservationCardinalityNext_old_withOldNew
            (v := v) evm evm.accountMap I))
        (ExecBlock.consNormal hwhile ExecBlock.nil),
      hL'⟩
  obtain ⟨L', helse, hL'⟩ := hbranch
  refine ⟨L', ?_, hL'⟩
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_increaseObservationCardinalityNext_oldStorage (v := v) evm I howner)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_increaseObservationCardinalityNext_param_withOld
        (v := v) evm evm.accountMap I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_increaseObservationCardinalityNext_oldGtZero_true
        (v := v) evm evm.accountMap I holdNonzero)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.iteFalse
      (evalExpr_increaseObservationCardinalityNext_newLeOld_false
        (v := v) evm evm.accountMap I hnewGt)
      helse)
    ExecBlock.nil

theorem uniswapV3PoolIncreaseObservationCardinalityNextSourceGrowReturns
    {v : PoolImmutables} {evm : EVM.State} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (holdNonzero : increaseObservationCardinalityNextOldWord evm.accountMap I ≠ ⟨0⟩)
    (hnewGt : (increaseObservationCardinalityNextOldWord evm.accountMap I).toNat <
      (increaseObservationCardinalityNextArgWord I).toNat) :
    ∃ L',
      ExecBlock (config v)
        { contract := contract v, locals := increaseObservationCardinalityNextStore I } evm
        [ .letDecl "observationCardinalityNextOld" (some uint16)
            (.storage (slot0F "observationCardinalityNext")),
          .letDecl "observationCardinalityNextNew" (some uint16)
            (.var "observationCardinalityNext"),
          .require (gtE (.var "observationCardinalityNextOld") (.intLit 0)),
          Stmt.ite (leE (.var "observationCardinalityNextNew")
              (.var "observationCardinalityNextOld"))
            [ .assign .localVar (varRef "observationCardinalityNextNew")
                (.var "observationCardinalityNextOld") ]
            [ .letDecl "i" (some uint16) (.var "observationCardinalityNextOld"),
              .while (ltE (.var "i") (.var "observationCardinalityNextNew"))
                [ .assign .storage (observationsRawF (.var "i") "blockTimestamp")
                    (.intLit 1),
                  .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ] ],
          .assign .storage (slot0F "observationCardinalityNext")
            (.var "observationCardinalityNextNew"),
          .assign .storage (slot0F "unlocked") (.boolLit true) ]
        (.ok { contract := contract v, locals := L' }
          (slot0AfterUnlockState
            (increaseObservationCardinalityNextAfterObsNextState
              (increaseObservationCardinalityNextGrowLoopSourceState
                ((increaseObservationCardinalityNextArgWord I).toNat -
                  (increaseObservationCardinalityNextOldWord evm.accountMap I).toNat)
                evm (increaseObservationCardinalityNextOldWord evm.accountMap I))
              (increaseObservationCardinalityNextArgWord I)))) := by
  obtain ⟨Lloop, hprefix, hLloop⟩ :=
    uniswapV3PoolIncreaseObservationCardinalityNextSourceGrowPrefix
      (v := v) (evm := evm) (I := I) howner holdNonzero hnewGt
  let evmLoop :=
    increaseObservationCardinalityNextGrowLoopSourceState
      ((increaseObservationCardinalityNextArgWord I).toNat -
        (increaseObservationCardinalityNextOldWord evm.accountMap I).toNat)
      evm (increaseObservationCardinalityNextOldWord evm.accountMap I)
  have htail :
      ExecBlock (config v) { contract := contract v, locals := Lloop } evmLoop
        [ .assign .storage (slot0F "observationCardinalityNext")
            (.var "observationCardinalityNextNew"),
          .assign .storage (slot0F "unlocked") (.boolLit true) ]
        (.ok { contract := contract v, locals := Lloop }
          (slot0AfterUnlockState
            (increaseObservationCardinalityNextAfterObsNextState evmLoop
              (increaseObservationCardinalityNextArgWord I)))) := by
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_increaseObservationCardinalityNext_new_withGrowLocals
          (v := v) evmLoop evm.accountMap I
          (increaseObservationCardinalityNextArgWord I) Lloop hLloop)
        (assignStorageRef_increaseObservationCardinalityNext_obsNext_withGrowLocals
          (v := v) evmLoop evm.accountMap I Lloop hLloop)) ?_
    exact ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure])
        (assignStorageRef_increaseObservationCardinalityNext_unlocked_true
          (v := v)
          (increaseObservationCardinalityNextAfterObsNextState evmLoop
            (increaseObservationCardinalityNextArgWord I))
          Lloop
          (by
            simpa [Std.HashMap.get?_eq_getElem?] using hLloop.slot0_get)))
      ExecBlock.nil
  refine ⟨Lloop, ?_⟩
  simpa [evmLoop] using execBlock_append hprefix htail

theorem increaseObservationCardinalityNextGrow_i_add_one
    (i : UInt256) (hlt : i.toNat < 65535) :
    UInt256.ofNat (i.toNat + 1) = (⟨1⟩ : UInt256) + i := by
  apply u256_inj
  rw [uadd_toNat]
  have hleft : (UInt256.ofNat (i.toNat + 1)).toNat = i.toNat + 1 := by
    exact ulit_toNat' (i.toNat + 1) (by
      norm_num [UInt256.size]
      omega)
  rw [hleft]
  rw [show (⟨1⟩ : UInt256).toNat = 1 by rfl]
  rw [Nat.mod_eq_of_lt]
  · omega
  · norm_num [UInt256.size]
    omega

def increaseObservationCardinalityNextGrowLoopAccountMap
    (I : ExecutionEnv) : Nat → AccountMap → UInt256 → AccountMap
  | 0, σ, _ => σ
  | n + 1, σ, i =>
      increaseObservationCardinalityNextGrowLoopAccountMap I n
        (sstoreAccountMap I.codeOwner σ
          (increaseObservationCardinalityNextGrowObservationSlot i)
          (increaseObservationCardinalityNextGrowObservationWord σ I i))
        (UInt256.ofNat (i.toNat + 1))

theorem increaseObservationCardinalityNext_uint16Mask_clean
    (w : UInt256) (h : w.toNat < 65536) :
    UInt256.land (⟨65535⟩ : UInt256) w = w := by
  have hmask : (⟨65535⟩ : UInt256) = slot0Uint16Mask := by
    native_decide
  rw [hmask]
  exact slot0Uint16Mask_clean_left (by
    simpa [EVM.twoPow] using h)

theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowLoopRunAux
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {obsNext old arg ret : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hperm : ee.perm = true) (hov : R.length + 15 ≤ 1024) :
    ∀ (n : Nat) (σ : AccountMap) (i : UInt256) (k C : ℕ),
      RD code ee g s0 ⟨16139⟩
        (i :: ⟨0⟩ :: obsNext :: old :: ⟨8⟩ :: ⟨5521⟩ :: ⟨0⟩ :: old :: arg :: ret :: R)
        mem aw rdata (cA, σ) k C →
      i.toNat ≤ obsNext.toNat →
      n = obsNext.toNat - i.toNat →
      obsNext.toNat ≤ 65535 →
      ∃ k' C', RD code ee g s0 ⟨5521⟩
        (obsNext :: ⟨0⟩ :: old :: arg :: ret :: R) mem aw rdata
        (cA, increaseObservationCardinalityNextGrowLoopAccountMap ee n σ i) k' C' := by
  intro n
  induction n with
  | zero =>
      intro σ i k C hrd hle hn _hobsBound
      have hge : obsNext.toNat ≤ i.toNat := by
        omega
      have hiNat : i.toNat = obsNext.toNat := by
        omega
      have hi : i = obsNext := by
        exact u256_inj hiNat
      subst i
      have hdone :
          UInt256.isZero
            (UInt256.lt
              (UInt256.land (⟨65535⟩ : UInt256) obsNext)
              (UInt256.land (⟨65535⟩ : UInt256) obsNext)) ≠ ⟨0⟩ := by
        rw [show UInt256.lt
            (UInt256.land (⟨65535⟩ : UInt256) obsNext)
            (UInt256.land (⟨65535⟩ : UInt256) obsNext) = ⟨0⟩ by
          exact ult_zero (by rfl)]
        native_decide
      obtain ⟨k', C', hrdTail⟩ :=
        uniswapV3PoolIncreaseObservationCardinalityNextGrowLoopExitToTail
          (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
          (R := R) (mem := mem) (aw := aw) (rdata := rdata)
          (acc := (cA, σ)) (i := obsNext) (obsNext := obsNext)
          (old := old) (arg := arg) (ret := ret)
          hpatch hrd hdone (by omega)
      exact ⟨k', C', by
        simpa [increaseObservationCardinalityNextGrowLoopAccountMap] using hrdTail⟩
  | succ n ih =>
      intro σ i k C hrd hle hn hobsBound
      have hlt : i.toNat < obsNext.toNat := by
        omega
      have hiBound : i.toNat < 65535 := by
        omega
      have hiClean :
          UInt256.land (⟨65535⟩ : UInt256) i = i :=
        increaseObservationCardinalityNext_uint16Mask_clean i (by omega)
      have hobsClean :
          UInt256.land (⟨65535⟩ : UInt256) obsNext = obsNext :=
        increaseObservationCardinalityNext_uint16Mask_clean obsNext (by omega)
      have hloop :
          UInt256.isZero
            (UInt256.lt
              (UInt256.land (⟨65535⟩ : UInt256) i)
              (UInt256.land (⟨65535⟩ : UInt256) obsNext)) = ⟨0⟩ := by
        rw [hiClean, hobsClean, ult_one hlt]
        native_decide
      have hincOk :
          UInt256.lt (UInt256.land (⟨65535⟩ : UInt256) i)
              (⟨65535⟩ : UInt256) ≠ ⟨0⟩ := by
        rw [hiClean, ult_one (by
          rw [show (⟨65535⟩ : UInt256).toNat = 65535 by native_decide]
          exact hiBound)]
        native_decide
      obtain ⟨k1, C1, hrd1⟩ :=
        uniswapV3PoolIncreaseObservationCardinalityNextGrowLoopBodyStep
          (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
          (R := R) (mem := mem) (aw := aw) (rdata := rdata) (cA := cA)
          (σ := σ) (i := i) (obsNext := obsNext) (old := old) (arg := arg)
          (ret := ret) hpatch hrd hloop hincOk hperm hov
      let σ1 :=
        sstoreAccountMap ee.codeOwner σ
          (increaseObservationCardinalityNextGrowObservationSlot i)
          (increaseObservationCardinalityNextGrowObservationWord σ ee i)
      let i' : UInt256 := UInt256.ofNat (i.toNat + 1)
      have hi'toNat : i'.toNat = i.toNat + 1 := by
        dsimp [i']
        exact ulit_toNat' (i.toNat + 1) (by
          norm_num [UInt256.size]
          omega)
      have hleNext : i'.toNat ≤ obsNext.toNat := by
        rw [hi'toNat]
        omega
      have hnNext : n = obsNext.toNat - i'.toNat := by
        rw [hi'toNat]
        omega
      have hrd1' : RD code ee g s0 ⟨16139⟩
          (i' :: ⟨0⟩ :: obsNext :: old :: ⟨8⟩ :: ⟨5521⟩ ::
            ⟨0⟩ :: old :: arg :: ret :: R)
          mem aw rdata (cA, σ1) k1 C1 := by
        have hnext := increaseObservationCardinalityNextGrow_i_add_one i hiBound
        simpa [σ1, i', hnext] using hrd1
      obtain ⟨k', C', hrdTail⟩ :=
        ih σ1 i' k1 C1 hrd1' hleNext hnNext hobsBound
      exact ⟨k', C', by
        simpa [increaseObservationCardinalityNextGrowLoopAccountMap, σ1, i'] using hrdTail⟩

theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowLoopRun
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap} {i obsNext old arg ret : UInt256} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨16139⟩
      (i :: ⟨0⟩ :: obsNext :: old :: ⟨8⟩ :: ⟨5521⟩ :: ⟨0⟩ :: old :: arg :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hle : i.toNat ≤ obsNext.toNat)
    (hobsBound : obsNext.toNat ≤ 65535)
    (hperm : ee.perm = true) (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨5521⟩
      (obsNext :: ⟨0⟩ :: old :: arg :: ret :: R) mem aw rdata
      (cA, increaseObservationCardinalityNextGrowLoopAccountMap ee
        (obsNext.toNat - i.toNat) σ i) k' C' := by
  exact uniswapV3PoolIncreaseObservationCardinalityNextGrowLoopRunAux
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0) (R := R)
    (mem := mem) (aw := aw) (rdata := rdata) (cA := cA) (obsNext := obsNext)
    (old := old) (arg := arg) (ret := ret) hpatch hperm hov
    (obsNext.toNat - i.toNat) σ i k C h hle rfl hobsBound

theorem increaseObservationCardinalityNextGrowObservationWord_equiv
    {σ τ : AccountMap} {I : ExecutionEnv} (i : UInt256)
    (hστ : accountMapEquiv σ τ) :
    increaseObservationCardinalityNextGrowObservationWord σ I i =
      increaseObservationCardinalityNextGrowObservationWord τ I i := by
  unfold increaseObservationCardinalityNextGrowObservationWord codeOwnerStorageWord
  rw [accountMapEquiv_storage_findD hστ I.codeOwner
    (increaseObservationCardinalityNextGrowObservationSlot i) ⟨0⟩]

theorem increaseObservationCardinalityNextGrowLoopAccountMap_equiv
    {σ τ : AccountMap} {I : ExecutionEnv} (n : Nat) (i : UInt256)
    (hστ : accountMapEquiv σ τ) :
    accountMapEquiv
      (increaseObservationCardinalityNextGrowLoopAccountMap I n σ i)
      (increaseObservationCardinalityNextGrowLoopAccountMap I n τ i) := by
  induction n generalizing σ τ i with
  | zero =>
      simpa [increaseObservationCardinalityNextGrowLoopAccountMap] using hστ
  | succ n ih =>
      have hword := increaseObservationCardinalityNextGrowObservationWord_equiv
        (I := I) i hστ
      have hstep :
          accountMapEquiv
            (sstoreAccountMap I.codeOwner σ
              (increaseObservationCardinalityNextGrowObservationSlot i)
              (increaseObservationCardinalityNextGrowObservationWord σ I i))
            (sstoreAccountMap I.codeOwner τ
              (increaseObservationCardinalityNextGrowObservationSlot i)
              (increaseObservationCardinalityNextGrowObservationWord τ I i)) := by
        simpa [hword] using
          accountMapEquiv_sstoreAccountMap I.codeOwner
            (increaseObservationCardinalityNextGrowObservationSlot i)
            (increaseObservationCardinalityNextGrowObservationWord σ I i) hστ
      exact ih (UInt256.ofNat (i.toNat + 1)) hstep

theorem increaseObservationCardinalityNextGrowObservationSlot_ne_zero
    (i : UInt256) (hlt : i.toNat < 65535) :
    increaseObservationCardinalityNextGrowObservationSlot i ≠ ⟨0⟩ := by
  have hclean :
      UInt256.land (⟨65535⟩ : UInt256) i = i :=
    increaseObservationCardinalityNext_uint16Mask_clean i (by omega)
  have hslotNat :
      (increaseObservationCardinalityNextGrowObservationSlot i).toNat = i.toNat + 8 := by
    unfold increaseObservationCardinalityNextGrowObservationSlot
    rw [hclean, uadd_toNat]
    rw [show (⟨8⟩ : UInt256).toNat = 8 by rfl]
    rw [Nat.mod_eq_of_lt (by
      norm_num [UInt256.size]
      omega
    )]
  intro hzero
  have hnat := congrArg UInt256.toNat hzero
  rw [hslotNat] at hnat
  norm_num at hnat

theorem increaseObservationCardinalityNextOldWord_sstore_growObservation
    (σ : AccountMap) (I : ExecutionEnv) (i val : UInt256) (hlt : i.toNat < 65535) :
    increaseObservationCardinalityNextOldWord
        (sstoreAccountMap I.codeOwner σ
          (increaseObservationCardinalityNextGrowObservationSlot i) val) I =
      increaseObservationCardinalityNextOldWord σ I := by
  have hslot :
      solcSlotWord
          (sstoreAccountMap I.codeOwner σ
            (increaseObservationCardinalityNextGrowObservationSlot i) val)
          I ⟨0⟩ =
        solcSlotWord σ I ⟨0⟩ := by
    simpa [solcSlotWord] using
      sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨0⟩
        (increaseObservationCardinalityNextGrowObservationSlot i) val
        (Ne.symm (increaseObservationCardinalityNextGrowObservationSlot_ne_zero i hlt))
  simp [increaseObservationCardinalityNextOldWord, slot0ObservationCardinalityNextWord,
    slot0SlotWord, hslot]

theorem increaseObservationCardinalityNextGrowLoopAccountMap_oldWord
    (I : ExecutionEnv) :
    ∀ (n : Nat) (σ : AccountMap) (i : UInt256),
      i.toNat + n ≤ 65535 →
      increaseObservationCardinalityNextOldWord
          (increaseObservationCardinalityNextGrowLoopAccountMap I n σ i) I =
        increaseObservationCardinalityNextOldWord σ I := by
  intro n
  induction n with
  | zero =>
      intro σ i _hbound
      simp [increaseObservationCardinalityNextGrowLoopAccountMap]
  | succ n ih =>
      intro σ i hbound
      have hiBound : i.toNat < 65535 := by omega
      let σ1 :=
        sstoreAccountMap I.codeOwner σ
          (increaseObservationCardinalityNextGrowObservationSlot i)
          (increaseObservationCardinalityNextGrowObservationWord σ I i)
      let i' : UInt256 := UInt256.ofNat (i.toNat + 1)
      have hi'toNat : i'.toNat = i.toNat + 1 := by
        dsimp [i']
        exact ulit_toNat' (i.toNat + 1) (by
          norm_num [UInt256.size]
          omega)
      have hnextBound : i'.toNat + n ≤ 65535 := by
        rw [hi'toNat]
        omega
      have hrec := ih σ1 i' hnextBound
      have hwrite :=
        increaseObservationCardinalityNextOldWord_sstore_growObservation σ I i
          (increaseObservationCardinalityNextGrowObservationWord σ I i) hiBound
      simpa [increaseObservationCardinalityNextGrowLoopAccountMap, σ1, i'] using
        hrec.trans hwrite

theorem increaseObservationCardinalityNextGrowLoopSourceState_executionEnv
    (n : Nat) (evm : EVM.State) (i : UInt256) :
    (increaseObservationCardinalityNextGrowLoopSourceState n evm i).executionEnv =
      evm.executionEnv := by
  induction n generalizing evm i with
  | zero =>
      simp [increaseObservationCardinalityNextGrowLoopSourceState]
  | succ n ih =>
      simp [increaseObservationCardinalityNextGrowLoopSourceState, ih,
        increaseObservationCardinalityNextGrowObservationState, storageStore_executionEnv]

theorem increaseObservationCardinalityNextGrowLoopSourceState_createdAccounts
    (n : Nat) (evm : EVM.State) (i : UInt256) :
    (increaseObservationCardinalityNextGrowLoopSourceState n evm i).createdAccounts =
      evm.createdAccounts := by
  induction n generalizing evm i with
  | zero =>
      simp [increaseObservationCardinalityNextGrowLoopSourceState]
  | succ n ih =>
      simp [increaseObservationCardinalityNextGrowLoopSourceState, ih,
        increaseObservationCardinalityNextGrowObservationState, storageStore_createdAccounts]

theorem increaseObservationCardinalityNextGrowLoopSourceState_accountMap
    (n : Nat) (evm : EVM.State) (I : ExecutionEnv) (i : UInt256)
    (hEnv : evm.executionEnv = I) :
    (increaseObservationCardinalityNextGrowLoopSourceState n evm i).accountMap =
      increaseObservationCardinalityNextGrowLoopAccountMap I n evm.accountMap i := by
  induction n generalizing evm i with
  | zero =>
      simp [increaseObservationCardinalityNextGrowLoopSourceState,
        increaseObservationCardinalityNextGrowLoopAccountMap]
  | succ n ih =>
      have hEnv' :
          (increaseObservationCardinalityNextGrowObservationState evm i).executionEnv = I := by
        simp [increaseObservationCardinalityNextGrowObservationState, storageStore_executionEnv,
          hEnv]
      rw [increaseObservationCardinalityNextGrowLoopSourceState]
      rw [ih (increaseObservationCardinalityNextGrowObservationState evm i)
        (UInt256.ofNat (i.toNat + 1)) hEnv']
      simp [increaseObservationCardinalityNextGrowLoopAccountMap,
        increaseObservationCardinalityNextGrowObservationState, storageStore_accountMap, hEnv]

theorem natLorPackedUint16Byte216 (n field : Nat) (hfield : field < 2 ^ 16) :
    Nat.lor (n % 2 ^ 216 + n / 2 ^ 232 * 2 ^ 232) (field * 2 ^ 216) =
      n % 2 ^ 216 + field * 2 ^ 216 + n / 2 ^ 232 * 2 ^ 232 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((n % 2 ^ 216 + n / 2 ^ 232 * 2 ^ 232) ||| (field * 2 ^ 216)).testBit i =
    (n % 2 ^ 216 + field * 2 ^ 216 + n / 2 ^ 232 * 2 ^ 232).testBit i
  rw [Nat.testBit_or]
  rw [show n % 2 ^ 216 + n / 2 ^ 232 * 2 ^ 232 =
      2 ^ 232 * (n / 2 ^ 232) + n % 2 ^ 216 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ 232)
    (b_lt := lt_trans (Nat.mod_lt _ (show 0 < 2 ^ 216 by norm_num))
      (by norm_num : 2 ^ 216 < 2 ^ 232))]
  rw [show n % 2 ^ 216 + field * 2 ^ 216 + n / 2 ^ 232 * 2 ^ 232 =
      2 ^ 232 * (n / 2 ^ 232) + (2 ^ 216 * field + n % 2 ^ 216) by ring]
  have hmid : 2 ^ 216 * field + n % 2 ^ 216 < 2 ^ 232 := by
    have hlow : n % 2 ^ 216 ≤ 2 ^ 216 - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ (show 0 < 2 ^ 216 by norm_num))
    have hfieldle : field ≤ 2 ^ 16 - 1 := Nat.le_pred_of_lt hfield
    have hmax : 2 ^ 216 * (2 ^ 16 - 1) + (2 ^ 216 - 1) < 2 ^ 232 := by
      norm_num [Nat.pow_add]
    nlinarith
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ 232) (b_lt := hmid)]
  rw [Nat.testBit_two_pow_mul_add (a := field)
    (b_lt := Nat.mod_lt _ (show 0 < 2 ^ 216 by norm_num))]
  rw [show field * 2 ^ 216 = 2 ^ 216 * field + 0 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := field) (b_lt := show 0 < 2 ^ 216 by norm_num)]
  by_cases hi216 : i < 216
  · simp [hi216]
  · have h216le : 216 ≤ i := Nat.le_of_not_gt hi216
    have hlowfalse : (n % 2 ^ 216).testBit i = false := by
      exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (Nat.mod_lt _ (show 0 < 2 ^ 216 by norm_num))
          (Nat.pow_le_pow_right (by norm_num) h216le))
    by_cases hi232 : i < 232
    · simp [hi216, hi232]
      intro hlowtrue
      have hlowfalse' :
          (n % 105312291668557186697918027683670432318895095400549111254310977536).testBit i =
            false := by
        simpa using hlowfalse
      rw [hlowfalse'] at hlowtrue
      cases hlowtrue
    · have hfieldfalse : field.testBit (i - 216) = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hfield (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hi216, hi232]
      intro hfieldtrue
      rw [hfieldfalse] at hfieldtrue
      cases hfieldtrue

theorem increaseObservationCardinalityNextEvmObsNextSlotWord_eq
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {obsNext : UInt256}
    (hAccounts : accountMapEquiv σ evm.accountMap) (hEnv : evm.executionEnv = I)
    (hobsLt : obsNext.toNat < 2 ^ 16) :
    increaseObservationCardinalityNextEvmObsNextSlotWord σ I obsNext =
      increaseObservationCardinalityNextObsNextSlotWord evm obsNext := by
  have hload := increaseObservationCardinalityNextStorageLoad_codeOwner_eq
    (evm := evm) (σ := σ) (I := I) hAccounts hEnv
  have hclearLt :
      (codeOwnerStorageWord I σ ⟨0⟩).toNat % 2 ^ 216 +
          (codeOwnerStorageWord I σ ⟨0⟩).toNat / 2 ^ 232 * 2 ^ 232 <
        UInt256.size := by
    rw [← natLandClearObservationCardinalityNextBytes
      (codeOwnerStorageWord I σ ⟨0⟩).toNat (codeOwnerStorageWord I σ ⟨0⟩).val.isLt]
    exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [UInt256.size])
  have hpackedLt :
      (codeOwnerStorageWord I σ ⟨0⟩).toNat % 2 ^ 216 +
          obsNext.toNat * 2 ^ 216 +
            (codeOwnerStorageWord I σ ⟨0⟩).toNat / 2 ^ 232 * 2 ^ 232 <
        UInt256.size := by
    have hlow : (codeOwnerStorageWord I σ ⟨0⟩).toNat % 2 ^ 216 ≤ 2 ^ 216 - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ (show 0 < 2 ^ 216 by norm_num))
    have hobsLe : obsNext.toNat ≤ 2 ^ 16 - 1 := Nat.le_pred_of_lt hobsLt
    have hhighLt : (codeOwnerStorageWord I σ ⟨0⟩).toNat / 2 ^ 232 < 2 ^ 24 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 232 * 2 ^ 24 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
      change (codeOwnerStorageWord I σ ⟨0⟩).val.val < UInt256.size
      exact (codeOwnerStorageWord I σ ⟨0⟩).val.isLt
    have hhighLe : (codeOwnerStorageWord I σ ⟨0⟩).toNat / 2 ^ 232 ≤ 2 ^ 24 - 1 :=
      Nat.le_pred_of_lt hhighLt
    have hmax :
        (2 ^ 216 - 1) + (2 ^ 16 - 1) * 2 ^ 216 +
            (2 ^ 24 - 1) * 2 ^ 232 <
          UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    nlinarith
  have hmulLt : obsNext.toNat * 2 ^ 216 < UInt256.size := by
    exact lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right hobsLt (by norm_num : 0 < 2 ^ 216))
      (by norm_num [UInt256.size])
  have hmulMod : obsNext.toNat * 2 ^ 216 % UInt256.size =
      obsNext.toNat * 2 ^ 216 :=
    Nat.mod_eq_of_lt hmulLt
  have hsourceWordLt :
      fromBytes'
          ((List.take 27
              (EVM.Word.toBytesLEWithSizeProof (codeOwnerStorageWord I σ ⟨0⟩)).1 ++
            List.take 2 (EVM.Word.toBytesLEWithSizeProof obsNext).1) ++
            List.drop (27 + 2)
              (EVM.Word.toBytesLEWithSizeProof (codeOwnerStorageWord I σ ⟨0⟩)).1) <
        UInt256.size := by
    let bs :=
          ((List.take 27
              (EVM.Word.toBytesLEWithSizeProof (codeOwnerStorageWord I σ ⟨0⟩)).1 ++
            List.take 2 (EVM.Word.toBytesLEWithSizeProof obsNext).1) ++
            List.drop (27 + 2)
              (EVM.Word.toBytesLEWithSizeProof (codeOwnerStorageWord I σ ⟨0⟩)).1)
    have hlen : bs.length = 32 := by
      simp [bs, List.length_take, List.length_drop,
        (EVM.Word.toBytesLEWithSizeProof (codeOwnerStorageWord I σ ⟨0⟩)).2,
        (EVM.Word.toBytesLEWithSizeProof obsNext).2]
    apply lt_of_lt_of_le (b := 2 ^ (8 * bs.length))
    · simpa [bs] using (EVM.fromBytes'_le (bs := bs))
    · rw [hlen]
      norm_num [UInt256.size]
  apply u256_inj
  rw [increaseObservationCardinalityNextEvmObsNextSlotWord,
    increaseObservationCardinalityNextObsNextSlotWord]
  rw [hload]
  rw [u256_lor_toNat, u256_land_toNat, u256_mul_toNat]
  rw [increaseObservationCardinalityNextNoGrowClearMask_toNat]
  rw [natLandClearObservationCardinalityNextBytes]
  rw [Nat.mod_eq_of_lt hclearLt]
  rw [u256_land_toNat]
  rw [show (⟨65535⟩ : UInt256).toNat = 2 ^ 16 - 1 by native_decide]
  rw [nat_land_mask_eq_mod]
  rw [Nat.mod_eq_of_lt hobsLt]
  rw [Nat.mod_eq_of_lt (lt_trans hobsLt (by norm_num [UInt256.size]))]
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨216⟩).toNat = 2 ^ 216 by
    native_decide]
  rw [hmulMod]
  rw [natLorPackedUint16Byte216 _ _ hobsLt]
  rw [Nat.mod_eq_of_lt hpackedLt]
  rw [ulit_toNat' _ hsourceWordLt]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  have hlen27 :
      (List.take 27 (EVM.Word.toBytesLEWithSizeProof (codeOwnerStorageWord I σ ⟨0⟩)).1).length =
        27 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof
      (codeOwnerStorageWord I σ ⟨0⟩)).2]
    norm_num
  have hlen29 :
      (List.take 27 (EVM.Word.toBytesLEWithSizeProof (codeOwnerStorageWord I σ ⟨0⟩)).1 ++
          List.take 2 (EVM.Word.toBytesLEWithSizeProof obsNext).1).length =
        29 := by
    rw [List.length_append, hlen27, List.length_take,
      (EVM.Word.toBytesLEWithSizeProof obsNext).2]
    norm_num
  rw [hlen27, hlen29]
  rw [show 256 ^ (27 : Nat) = 2 ^ 216 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (29 : Nat) = 2 ^ 232 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (2 : Nat) = 2 ^ 16 by norm_num]
  rw [Nat.mod_eq_of_lt hobsLt]
  ring
  exact (codeOwnerStorageWord I σ ⟨0⟩).val.isLt

theorem increaseObservationCardinalityNextFinalGrowAccountMapEquiv
    {evmOwner : EVM.State} {σOwnerEvm : AccountMap} {I : ExecutionEnv}
    {old obsNext : UInt256} (n : Nat)
    (hAccounts : accountMapEquiv σOwnerEvm evmOwner.accountMap)
    (hEnv : evmOwner.executionEnv = I)
    (hobsLt : obsNext.toNat < 2 ^ 16) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (increaseObservationCardinalityNextGrowLoopAccountMap I n σOwnerEvm old)
          ⟨0⟩
          (increaseObservationCardinalityNextEvmObsNextSlotWord
            (increaseObservationCardinalityNextGrowLoopAccountMap I n σOwnerEvm old)
            I obsNext))
        ⟨0⟩
        (increaseObservationCardinalityNextEvmUnlockedTrueSlotWord
          (sstoreAccountMap I.codeOwner
            (increaseObservationCardinalityNextGrowLoopAccountMap I n σOwnerEvm old)
            ⟨0⟩
            (increaseObservationCardinalityNextEvmObsNextSlotWord
              (increaseObservationCardinalityNextGrowLoopAccountMap I n σOwnerEvm old)
              I obsNext)) I))
      (slot0AfterUnlockState
        (increaseObservationCardinalityNextAfterObsNextState
          (increaseObservationCardinalityNextGrowLoopSourceState n evmOwner old)
          obsNext)).accountMap := by
  have hLoopSourceMap :=
    increaseObservationCardinalityNextGrowLoopSourceState_accountMap
      n evmOwner I old hEnv
  have hLoopAccounts :
      accountMapEquiv
        (increaseObservationCardinalityNextGrowLoopAccountMap I n σOwnerEvm old)
        (increaseObservationCardinalityNextGrowLoopSourceState n evmOwner old).accountMap := by
    simpa [hLoopSourceMap] using
      increaseObservationCardinalityNextGrowLoopAccountMap_equiv
        (I := I) n old hAccounts
  have hLoopEnv :
      (increaseObservationCardinalityNextGrowLoopSourceState n evmOwner old).executionEnv = I := by
    rw [increaseObservationCardinalityNextGrowLoopSourceState_executionEnv]
    exact hEnv
  have hfirstWord := increaseObservationCardinalityNextEvmObsNextSlotWord_eq
    (evm := increaseObservationCardinalityNextGrowLoopSourceState n evmOwner old)
    (σ := increaseObservationCardinalityNextGrowLoopAccountMap I n σOwnerEvm old)
    (I := I) (obsNext := obsNext) hLoopAccounts hLoopEnv hobsLt
  have hFirstAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (increaseObservationCardinalityNextGrowLoopAccountMap I n σOwnerEvm old)
          ⟨0⟩
          (increaseObservationCardinalityNextEvmObsNextSlotWord
            (increaseObservationCardinalityNextGrowLoopAccountMap I n σOwnerEvm old)
            I obsNext))
        (increaseObservationCardinalityNextAfterObsNextState
          (increaseObservationCardinalityNextGrowLoopSourceState n evmOwner old)
          obsNext).accountMap := by
    rw [hfirstWord]
    simpa [increaseObservationCardinalityNextAfterObsNextState, storageStore_accountMap,
      hLoopEnv] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
        (increaseObservationCardinalityNextObsNextSlotWord
          (increaseObservationCardinalityNextGrowLoopSourceState n evmOwner old)
          obsNext) hLoopAccounts
  have hFirstEnv :
      (increaseObservationCardinalityNextAfterObsNextState
        (increaseObservationCardinalityNextGrowLoopSourceState n evmOwner old)
        obsNext).executionEnv = I := by
    simp [increaseObservationCardinalityNextAfterObsNextState, storageStore_executionEnv,
      hLoopEnv]
  have hsecondWord := increaseObservationCardinalityNextEvmUnlockedTrueSlotWord_eq
    (evm := increaseObservationCardinalityNextAfterObsNextState
      (increaseObservationCardinalityNextGrowLoopSourceState n evmOwner old) obsNext)
    (σ := sstoreAccountMap I.codeOwner
      (increaseObservationCardinalityNextGrowLoopAccountMap I n σOwnerEvm old)
      ⟨0⟩
      (increaseObservationCardinalityNextEvmObsNextSlotWord
        (increaseObservationCardinalityNextGrowLoopAccountMap I n σOwnerEvm old)
        I obsNext))
    (I := I) hFirstAccounts hFirstEnv
  rw [hsecondWord]
  simpa [slot0AfterUnlockState, storageStore_accountMap, hFirstEnv] using
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
      (slot0UnlockedTrueSlotWord
        (increaseObservationCardinalityNextAfterObsNextState
          (increaseObservationCardinalityNextGrowLoopSourceState n evmOwner old) obsNext))
      hFirstAccounts

theorem uniswapV3PoolIncreaseObservationCardinalityNextGrowBranch
    {v : PoolImmutables} {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ_evm σ_solm σ₀ : AccountMap}
    {A : Substate} {I : ExecutionEnv} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata =
      some (increaseobservationcardinalitynextTransition v))
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode
          (List.map Param.name (increaseobservationcardinalitynextTransition v).params)
          (transitionSignature (increaseobservationcardinalitynextTransition v)).paramTypes
          I.calldata =
        some (increaseObservationCardinalityNextStore I))
    (hsourceLockInit :
      ExecBlock (config v) { contract := contract v, locals := increaseObservationCardinalityNextStore I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.storage (slot0F "unlocked")),
          .assign .storage (slot0F "unlocked") (.boolLit false) ]
        (.ok { contract := contract v, locals := increaseObservationCardinalityNextStore I }
          (initState cA gh bl
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
              (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
            σ₀ (Sat256.ofUInt256 g) A I)))
    (hsourceNoDelegate :
      ExecBlock (config v) { contract := contract v, locals := increaseObservationCardinalityNextStore I }
        (initState cA gh bl
          (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
            (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
          σ₀ (Sat256.ofUInt256 g) A I)
        [ .require (.binary .eq (.env .this) (addrLit v.original)) ]
        (.ok { contract := contract v, locals := increaseObservationCardinalityNextStore I }
          (initState cA gh bl
            (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
              (increaseObservationCardinalityNextLockedSlotWord σ_solm I))
            σ₀ (Sat256.ofUInt256 g) A I)))
    {kNoDelegate CNoDelegate : Nat}
    (hrdNoDelegate :
      RD code I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5493⟩
        [increaseObservationCardinalityNextArgWord I, ⟨857⟩, solcSelectorWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
          (increaseObservationCardinalityNextLockedSlotWord σ_evm I)) kNoDelegate CNoDelegate)
    (hAccountsAfterLock :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
          (increaseObservationCardinalityNextLockedSlotWord σ_evm I))
        (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
          (increaseObservationCardinalityNextLockedSlotWord σ_solm I)))
    (holdNonzeroEvm :
      increaseObservationCardinalityNextOldWord
          (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
            (increaseObservationCardinalityNextLockedSlotWord σ_evm I)) I ≠ ⟨0⟩)
    (holdNonzeroSolm :
      increaseObservationCardinalityNextOldWord
          (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
            (increaseObservationCardinalityNextLockedSlotWord σ_solm I)) I ≠ ⟨0⟩)
    (hnewLeEvm :
      ¬ UInt256.gt (increaseObservationCardinalityNextArgWord I)
          (increaseObservationCardinalityNextOldWord
            (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
              (increaseObservationCardinalityNextLockedSlotWord σ_evm I)) I) = ⟨0⟩)
    (hperm : I.perm = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  let σe := sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
    (increaseObservationCardinalityNextLockedSlotWord σ_evm I)
  let σs := sstoreAccountMap I.codeOwner σ_solm ⟨0⟩
    (increaseObservationCardinalityNextLockedSlotWord σ_solm I)
  let old := increaseObservationCardinalityNextOldWord σe I
  let obsNext := increaseObservationCardinalityNextArgWord I
  have hnewGtNat : old.toNat < obsNext.toNat := by
    by_contra hnot
    have hle : obsNext.toNat ≤ old.toNat := by omega
    exact hnewLeEvm (by simpa [old, obsNext, σe] using ugt_zero hle)
  have holdEq :
      increaseObservationCardinalityNextOldWord σs I = old := by
    simpa [old, σe, σs] using
      increaseObservationCardinalityNextOldWord_transport hAccountsAfterLock
  have hnewGtSolm :
      (increaseObservationCardinalityNextOldWord σs I).toNat < obsNext.toNat := by
    simpa [holdEq] using hnewGtNat
  obtain ⟨_, _, hrd16137⟩ :=
    uniswapV3PoolIncreaseObservationCardinalityNextGrowPrefix
      (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (R := [solcSelectorWord I]) (rdata := ByteArray.empty) (cA := cA)
      (σ := σe) hpatch (by simpa [σe] using hrdNoDelegate)
      (by simpa [old, obsNext, σe] using holdNonzeroEvm)
      (by simpa [old, obsNext, σe] using hnewLeEvm) (by norm_num)
  obtain ⟨_, _, hrd16139⟩ :=
    uniswapV3PoolIncreaseObservationCardinalityNextGrowEnterLoopHeader
      (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (R := [solcSelectorWord I]) (mem := solcFreePtrMem) (aw := UInt256.ofNat 3)
      (rdata := ByteArray.empty) (acc := (cA, σe)) (obsNext := obsNext)
      (old := old) (arg := obsNext) (ret := ⟨857⟩)
      hpatch hrd16137 (by norm_num)
  obtain ⟨k5521, C5521, hrd5521₀⟩ :=
    uniswapV3PoolIncreaseObservationCardinalityNextGrowLoopRun
      (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (R := [solcSelectorWord I]) (mem := solcFreePtrMem) (aw := UInt256.ofNat 3)
      (rdata := ByteArray.empty) (cA := cA) (σ := σe) (i := old)
      (obsNext := obsNext) (old := old) (arg := obsNext) (ret := ⟨857⟩)
      hpatch hrd16139 (by omega) (increaseObservationCardinalityNextArgWord_le_65535 I)
      hperm (by norm_num)
  have holdLoop :
      increaseObservationCardinalityNextOldWord
          (increaseObservationCardinalityNextGrowLoopAccountMap I
            (obsNext.toNat - old.toNat) σe old) I = old := by
    have hobsLe : obsNext.toNat ≤ 65535 := by
      simpa [obsNext] using increaseObservationCardinalityNextArgWord_le_65535 I
    exact increaseObservationCardinalityNextGrowLoopAccountMap_oldWord I
      (obsNext.toNat - old.toNat) σe old (by omega)
  have hrd5521 : RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5521⟩
      [obsNext, ⟨0⟩,
        increaseObservationCardinalityNextOldWord
          (increaseObservationCardinalityNextGrowLoopAccountMap I
            (obsNext.toNat - old.toNat) σe old) I,
        increaseObservationCardinalityNextArgWord I, ⟨857⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, increaseObservationCardinalityNextGrowLoopAccountMap I
        (obsNext.toNat - old.toNat) σe old) k5521 C5521 := by
    simpa [holdLoop, obsNext] using hrd5521₀
  have hchanged :
      UInt256.land
          (increaseObservationCardinalityNextOldWord
            (increaseObservationCardinalityNextGrowLoopAccountMap I
              (obsNext.toNat - old.toNat) σe old) I)
          (⟨65535⟩ : UInt256) ≠
        UInt256.land obsNext (⟨65535⟩ : UInt256) := by
    have holdBound : old.toNat < 65536 := by
      simpa [old, σe, increaseObservationCardinalityNextOldWord] using
        slot0Uint16Mask_bound (UInt256.div (slot0SlotWord σe I) (slot0ShiftBytes 27))
    have holdClean : UInt256.land old (⟨65535⟩ : UInt256) = old := by
      rw [u256_land_comm]
      exact increaseObservationCardinalityNext_uint16Mask_clean old holdBound
    have hnewClean : UInt256.land obsNext (⟨65535⟩ : UInt256) = obsNext := by
      rw [u256_land_comm]
      exact increaseObservationCardinalityNext_uint16Mask_clean obsNext
        (by have h := increaseObservationCardinalityNextArgWord_lt_twoPow16 I
            simpa [obsNext, EVM.twoPow] using h)
    rw [holdLoop, holdClean, hnewClean]
    intro heq
    have hnat := congrArg UInt256.toNat heq
    omega
  have hrdRet :=
    uniswapV3PoolIncreaseObservationCardinalityNextGrowChangedTailReturn
      (v := v) (code := code) (ee := I) (g := Sat256.ofUInt256 g)
      (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (R := [solcSelectorWord I]) (rdata := ByteArray.empty) (obsNext := obsNext)
      (cA := cA) (σ := increaseObservationCardinalityNextGrowLoopAccountMap I
        (obsNext.toNat - old.toNat) σe old)
      hpatch hrd5521 hperm hchanged (by norm_num)
  obtain ⟨Lgrow, hsourceGrow₀⟩ :=
    uniswapV3PoolIncreaseObservationCardinalityNextSourceGrowReturns
      (v := v)
      (evm := initState cA gh bl σs σ₀ (Sat256.ofUInt256 g) A I)
      (I := I) (by simp [initState]) (by simpa [σs] using holdNonzeroSolm)
      (by simpa [σs, obsNext] using hnewGtSolm)
  have hsourceGrow :
      ExecBlock (config v) { contract := contract v, locals := increaseObservationCardinalityNextStore I }
        (initState cA gh bl σs σ₀ (Sat256.ofUInt256 g) A I)
        [ .letDecl "observationCardinalityNextOld" (some uint16)
            (.storage (slot0F "observationCardinalityNext")),
          .letDecl "observationCardinalityNextNew" (some uint16)
            (.var "observationCardinalityNext"),
          .require (gtE (.var "observationCardinalityNextOld") (.intLit 0)),
          Stmt.ite (leE (.var "observationCardinalityNextNew")
              (.var "observationCardinalityNextOld"))
            [ .assign .localVar (varRef "observationCardinalityNextNew")
                (.var "observationCardinalityNextOld") ]
            [ .letDecl "i" (some uint16) (.var "observationCardinalityNextOld"),
              .while (ltE (.var "i") (.var "observationCardinalityNextNew"))
                [ .assign .storage (observationsRawF (.var "i") "blockTimestamp") (.intLit 1),
                  .assign .localVar (varRef "i") (addE (.var "i") (.intLit 1)) ] ],
          .assign .storage (slot0F "observationCardinalityNext")
            (.var "observationCardinalityNextNew"),
          .assign .storage (slot0F "unlocked") (.boolLit true) ]
        (.ok { contract := contract v, locals := Lgrow }
          (slot0AfterUnlockState
            (increaseObservationCardinalityNextAfterObsNextState
              (increaseObservationCardinalityNextGrowLoopSourceState
                (obsNext.toNat - old.toNat)
                (initState cA gh bl σs σ₀ (Sat256.ofUInt256 g) A I) old)
              obsNext))) := by
    simpa [initState, σs, old, obsNext, holdEq] using hsourceGrow₀
  have hsourceSuccess := execBlock_append hsourceNoDelegate hsourceGrow
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (increaseObservationCardinalityNextStore I)
        (increaseobservationcardinalitynextTransition v).body
        (.returned { contract := contract v, locals := Lgrow }
          (slot0AfterUnlockState
            (increaseObservationCardinalityNextAfterObsNextState
              (increaseObservationCardinalityNextGrowLoopSourceState
                (obsNext.toNat - old.toNat)
                (initState cA gh bl σs σ₀ (Sat256.ofUInt256 g) A I) old)
              obsNext))
          none) := by
    refine ExecFuncBody.execBlockOK ?_
    simpa [increaseobservationcardinalitynextTransition, σs] using
      execBlock_append hsourceLockInit hsourceSuccess
  exact hrdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by
      simp [slot0AfterUnlockState, increaseObservationCardinalityNextAfterObsNextState,
        increaseObservationCardinalityNextGrowLoopSourceState_createdAccounts,
        storageStore_createdAccounts, initState])
    (by
      exact increaseObservationCardinalityNextFinalGrowAccountMapEquiv
        (evmOwner := initState cA gh bl σs σ₀ (Sat256.ofUInt256 g) A I)
        (σOwnerEvm := σe) (I := I) (old := old) (obsNext := obsNext)
        (obsNext.toNat - old.toNat) (by simpa [σe, σs, initState] using hAccountsAfterLock)
        (by simp [initState]) (by
          have h := increaseObservationCardinalityNextArgWord_lt_twoPow16 I
          simpa [obsNext, EVM.twoPow] using h))
    (by
      rw [show (increaseobservationcardinalitynextTransition v).returnType = [] from rfl]
      exact returnEquiv.fallthrough rfl rfl (by native_decide))

end Benchmarks.UniswapV3Pool
