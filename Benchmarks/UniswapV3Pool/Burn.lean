import Benchmarks.UniswapV3Pool.Locking
import Benchmarks.UniswapV3Pool.NoDelegateCall
import Benchmarks.UniswapV3Pool.TickSpacing
import Benchmarks.UniswapV3Pool.TicksInt128
import Benchmarks.UniswapV3Pool.Uint128

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev burnTickLowerWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev burnTickUpperWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev burnAmountWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev burnTickLowerCleanWord (I : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨2⟩ (burnTickLowerWord I)

abbrev burnTickUpperCleanWord (I : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨2⟩ (burnTickUpperWord I)

abbrev burnAmountCleanWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (burnAmountWord I) uint128Mask

abbrev burnTickLowerValue (I : ExecutionEnv) : Value :=
  .int (tickSpacingSint24Value (burnTickLowerWord I))

abbrev burnTickUpperValue (I : ExecutionEnv) : Value :=
  .int (tickSpacingSint24Value (burnTickUpperWord I))

abbrev burnAmountValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (UInt256.land (burnAmountWord I) uint128Mask).toNat)

abbrev burnLiquidityDeltaValue (I : ExecutionEnv) : Value :=
  .int (0 - Int.ofNat (burnAmountCleanWord I).toNat)

abbrev burnStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "tickLower" (burnTickLowerValue I))
    |>.insert "tickUpper" (burnTickUpperValue I)
    |>.insert "amount" (burnAmountValue I)

abbrev burnLiquidityDeltaFrame (v : PoolImmutables) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnStore I).insert "liquidityDelta" (burnLiquidityDeltaValue I) }

abbrev burnUint8Mask : UInt256 :=
  UInt256.ofNat (2 ^ 8 - 1)

abbrev burnUnlockedShift : UInt256 :=
  UInt256.shiftLeft ⟨1⟩ ⟨240⟩

abbrev burnUnlockedByte (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land burnUint8Mask (UInt256.div (solcSlotWord σ I ⟨0⟩) burnUnlockedShift)

abbrev burnUnlockedClearMask : UInt256 :=
  UInt256.lnot (UInt256.shiftLeft burnUint8Mask ⟨240⟩)

abbrev burnLockedSlotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land burnUnlockedClearMask (solcSlotWord σ I ⟨0⟩)

abbrev burnUnlockedLoc : StorageLoc :=
  slot0UnlockedLoc

def burnModifyPositionMem0 : ByteArray :=
  (UInt256.toByteArray ((⟨128⟩ : UInt256) + ⟨128⟩)).write 0 solcFreePtrMem
    (⟨64⟩ : UInt256).toNat 32

def burnModifyPositionMem1 (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat I.source.val)).write 0 burnModifyPositionMem0
    (⟨128⟩ : UInt256).toNat 32

def burnModifyPositionMem2 (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))).write 0
    (burnModifyPositionMem1 I) ((⟨128⟩ : UInt256) + ⟨32⟩).toNat 32

def burnModifyPositionMem3 (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))).write 0
    (burnModifyPositionMem2 I) ((⟨128⟩ : UInt256) + ⟨64⟩).toNat 32

def burnModifyPositionMem4 (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray
    (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))).write 0
    (burnModifyPositionMem3 I) (⟨224⟩ : UInt256).toNat 32

private theorem uint128Mask_decode (w : UInt256) :
    (UInt256.land w uint128Mask).toNat = w.toNat % EVM.twoPow 128 := by
  rw [u256_land_toNat, uint128Mask_toNat, nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt (by
    exact lt_trans (Nat.mod_lt _ (by norm_num [EVM.twoPow]))
      (by norm_num [EVM.twoPow, UInt256.size]))

theorem burnUnlockedByte_eq_slot0UnlockedRawWord (σ : AccountMap) (I : ExecutionEnv) :
    burnUnlockedByte σ I = slot0UnlockedRawWord σ I := by
  have hshift : burnUnlockedShift = slot0ShiftBytes 30 := by
    native_decide
  simp [burnUnlockedByte, slot0UnlockedRawWord, burnUnlockedShift, slot0ShiftBytes,
    slot0SlotWord, burnUint8Mask, slot0Uint8Mask, hshift, u256_land_comm]

theorem uniswapV3PoolBurnEvalUnlocked {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) { contract := contract v, locals := burnStore I }
      (initState cA gh bl σ σ₀ g A I) (.storage (slot0F "unlocked")) =
      .ok (wordToElem .bool (burnUnlockedByte σ I)) := by
  rw [evalExpr_storage_scalar
    (t := .bool)
    (slot := slot0F "unlocked")
    (er := { base := "slot0", steps := [.field "unlocked"] })
    (loc := burnUnlockedLoc)
    (hbase := by simp [slot0F, burnStore])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
    (hty := by
      simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, boolSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, burnUnlockedLoc,
        slot0UnlockedLoc, loc])]
  simpa [burnUnlockedByte_eq_slot0UnlockedRawWord] using
    slot0StorageLocLoad_unlocked (initState cA gh bl σ σ₀ g A I)

theorem burnUnlockedByte_wordToElem_false {σ : AccountMap} {I : ExecutionEnv}
    (hzero : burnUnlockedByte σ I = ⟨0⟩) :
    wordToElem .bool (burnUnlockedByte σ I) = .bool false := by
  simp [wordToElem, hzero]

theorem burnUnlockedByte_wordToElem_true {σ : AccountMap} {I : ExecutionEnv}
    (hnz : burnUnlockedByte σ I ≠ ⟨0⟩) :
    wordToElem .bool (burnUnlockedByte σ I) = .bool true := by
  have hbeq : ((burnUnlockedByte σ I).val == 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro hval
    apply hnz
    apply u256_inj
    simpa [UInt256.toNat] using hval
  simp [wordToElem, hbeq]

theorem burnUnlockedByte_transport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    burnUnlockedByte σ_solm I = burnUnlockedByte σ_evm I := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ (⟨0⟩ : UInt256)
  dsimp [burnUnlockedByte, solcSlotWord]
  rw [← hslot]

theorem burnLockedSlotWord_transport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    burnLockedSlotWord σ_solm I = burnLockedSlotWord σ_evm I := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ (⟨0⟩ : UInt256)
  dsimp [burnLockedSlotWord, solcSlotWord]
  rw [← hslot]

theorem uniswapV3PoolBurnSourceLockedReverts {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlocked : burnUnlockedByte σ I = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (burnStore I)
      burnTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [burnTransition, nonpayable, lockPrefix, burnStore] using
    (nonpayableSecondRequireReverts
      (cfg := config v)
      (solm := { contract := contract v, locals := burnStore I })
      (evm := initState cA gh bl σ σ₀ g A I)
      (guard := .storage (slot0F "unlocked"))
      (hwv := by simp [initState, hwv])
      (hguard := by
        rw [uniswapV3PoolBurnEvalUnlocked]
        exact congrArg EvalResult.ok (burnUnlockedByte_wordToElem_false hlocked)))

theorem uniswapV3PoolBurnSourceLockPrefixExact {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hunlocked : burnUnlockedByte σ I ≠ ⟨0⟩) :
    ExecBlock (config v) { contract := contract v, locals := burnStore I }
      (initState cA gh bl σ σ₀ g A I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.storage (slot0F "unlocked")),
        .assign .storage (slot0F "unlocked") (.boolLit false) ]
      (.ok { contract := contract v, locals := burnStore I }
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I))) := by
  refine nonpayableRequireAssignStorageBlock
    (cfg := config v) (solm := { contract := contract v, locals := burnStore I })
    (evm := initState cA gh bl σ σ₀ g A I)
    (evm' := Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
      (burnLockedSlotWord σ I))
    (guard := .storage (slot0F "unlocked")) (rhs := .boolLit false)
    (ref := slot0F "unlocked") (value := .bool false)
    (by simp [initState, hwv]) ?_ ?_ ?_
  · rw [uniswapV3PoolBurnEvalUnlocked]
    exact congrArg EvalResult.ok (burnUnlockedByte_wordToElem_true hunlocked)
  · simp [evalExpr?, pure]
  · apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "unlocked"] })
      (ty := .elem .bool)
      (loc := burnUnlockedLoc)
    · simp [slot0F, burnStore]
    · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
    · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, boolSt]
    · funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, burnUnlockedLoc,
        slot0UnlockedLoc, loc]
    · trivial
    · simpa [initState, burnLockedSlotWord, solcSlotWord, burnUnlockedLoc, slot0UnlockedLoc,
        burnUnlockedClearMask, slot0UnlockedClearMask, u256_land_comm] using
        storageLocStore_slot0Unlocked_false (initState cA gh bl σ σ₀ g A I)

theorem assignStorageRef_burn_unlocked_true
    {v : PoolImmutables} (evm : EVM.State) (L : Store)
    (hbase : "slot0" ∉ L) :
    assignStorageRef? (config v)
        { contract := contract v, locals := L }
        evm .storage (slot0F "unlocked") (.bool true) =
      .ok ({ contract := contract v, locals := L }, slot0AfterUnlockState evm) := by
  apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "unlocked"] })
      (ty := .elem .bool)
      (loc := burnUnlockedLoc)
  · simpa [slot0F] using hbase
  · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
  · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, boolSt]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, burnUnlockedLoc,
      slot0UnlockedLoc, loc]
  · trivial
  · simpa [burnUnlockedLoc, slot0UnlockedLoc] using storageLocStore_slot0Unlocked_true evm

theorem uniswapV3PoolBurnEvalLiquidityDeltaRevert {v : PoolImmutables}
    {evm : EVM.State} {I : ExecutionEnv}
    (hne :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) ≠ burnAmountCleanWord I) :
    evalExpr? (config v) { contract := contract v, locals := burnStore I } evm
      (subE (.intLit 0) (.inRange int128Int (.var "amount"))) = .revert := by
  have hgeNat : EVM.twoPow 127 ≤ (burnAmountCleanWord I).toNat :=
    signextend_fifteen_ne_self_toNat_ge_twoPow127 hne
  have hinRange :
      evalExpr? (config v) { contract := contract v, locals := burnStore I } evm
        (.inRange int128Int (.var "amount")) = .revert := by
    simp [evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, burnStore,
      burnAmountValue, int128Int]
    simpa [EVM.twoPow, burnAmountCleanWord] using hgeNat
  simp [subE, evalExpr?, EvalResult.bind, bind, hinRange]

theorem uniswapV3PoolBurnEvalLiquidityDeltaOk {v : PoolImmutables}
    {evm : EVM.State} {I : ExecutionEnv}
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I) :
    evalExpr? (config v) { contract := contract v, locals := burnStore I } evm
      (subE (.intLit 0) (.inRange int128Int (.var "amount"))) =
      .ok (burnLiquidityDeltaValue I) := by
  have hltNat : (burnAmountCleanWord I).toNat < EVM.twoPow 127 :=
    signextend_fifteen_eq_self_toNat_lt_twoPow127
      (by simpa [burnAmountCleanWord] using uint128Mask_bound (burnAmountWord I))
      hcanon
  have hinRange :
      evalExpr? (config v) { contract := contract v, locals := burnStore I } evm
        (.inRange int128Int (.var "amount")) = .ok (burnAmountValue I) := by
    simp [evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, burnStore,
      burnAmountValue, int128Int]
    simpa [EVM.twoPow, burnAmountCleanWord] using hltNat
  simp [subE, evalExpr?, EvalResult.bind, bind, evalBinaryOp?, burnLiquidityDeltaValue,
    burnAmountValue, hinRange]

theorem uniswapV3PoolBurnSourceThroughLiquidityDelta {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hunlocked : burnUnlockedByte σ I ≠ ⟨0⟩)
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I) :
    ExecBlock (config v) { contract := contract v, locals := burnStore I }
      (initState cA gh bl σ σ₀ g A I)
      (nonpayable ++ lockPrefix ++
        [ .letDecl "liquidityDelta" (some int128)
            (subE (.intLit 0) (.inRange int128Int (.var "amount"))) ])
      (.ok (burnLiquidityDeltaFrame v I)
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I))) := by
  have hprefix := uniswapV3PoolBurnSourceLockPrefixExact (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hwv hunlocked
  have htail :
      ExecBlock (config v) { contract := contract v, locals := burnStore I }
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I))
        [ .letDecl "liquidityDelta" (some int128)
            (subE (.intLit 0) (.inRange int128Int (.var "amount"))) ]
        (.ok (burnLiquidityDeltaFrame v I)
          (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
            (burnLockedSlotWord σ I))) := by
    exact ExecBlock.consNormal
      (ExecStmt.letDecl (uniswapV3PoolBurnEvalLiquidityDeltaOk
        (v := v) (evm := Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
          I.codeOwner ⟨0⟩ (burnLockedSlotWord σ I)) (I := I) hcanon))
      ExecBlock.nil
  simpa [nonpayable, lockPrefix] using execBlock_append hprefix htail

theorem uniswapV3PoolBurnSourceLiquidityDeltaReverts {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hunlocked : burnUnlockedByte σ I ≠ ⟨0⟩)
    (hne :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) ≠ burnAmountCleanWord I) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (burnStore I)
      burnTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hprefix := uniswapV3PoolBurnSourceLockPrefixExact (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hwv hunlocked
  have htail :
      ∀ rest,
        ExecBlock (config v) { contract := contract v, locals := burnStore I }
          (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
            (burnLockedSlotWord σ I))
          (.letDecl "liquidityDelta" (some int128)
            (subE (.intLit 0) (.inRange int128Int (.var "amount"))) :: rest)
          .reverted := by
    intro rest
    exact ExecBlock.consRevert
      (ExecStmt.letDeclRevert (uniswapV3PoolBurnEvalLiquidityDeltaRevert
        (v := v) (evm := Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
          I.codeOwner ⟨0⟩ (burnLockedSlotWord σ I)) (I := I) hne))
  simpa [burnTransition, nonpayable, lockPrefix] using execBlock_append hprefix (htail _)

private def burnStSignextend (s : State) (res : UInt256) (t : List UInt256) : State :=
  { s with
      machineState.stack := res :: t,
      machineState.gasAvailable := s.machineState.gasAvailable.subNat 5
      machineState.pc := s.machineState.pc + ⟨1⟩
      machineState.execLength := s.machineState.execLength + 1 }

private theorem burnSignextendXstep {code : ByteArray} {s : State} {pc a b : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pc)
    (hdec : decode code pc = some (.SIGNEXTEND, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s =
      if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
      else .ok (burnStSignextend s (UInt256.signextend a b) t, .none) := by
  have hdecS : decode s.executionEnv.code s.machineState.pc = some (.SIGNEXTEND, .none) := by
    rw [hcode, hpc]
    exact hdec
  have hstep := step_signextend s hdecS
  have hnoOverflow : ¬ 1024 ≤ t.length := by omega
  simpa [hcode, hstk, GasConstants.Glow, burnStSignextend, hnoOverflow] using hstep

theorem burnRDSignextend {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SIGNEXTEND, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.signextend a b :: t) mem aw rdata acc
      (k + 1) (C + 5) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee,
      hworld⟩
  · exact Or.inl hoog
  · have st := burnSignextendXstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 5
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨burnStSignextend s (UInt256.signextend a b) t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [burnStSignextend]; exact hcode
      · simp only [burnStSignextend]; rw [hpc]
      · rfl
      · simp only [burnStSignextend]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [burnStSignextend]; exact hmem
      · simp only [burnStSignextend]; exact haw
      · simp only [burnStSignextend]; exact hrdata
      · simp only [burnStSignextend]; exact hacc
      · exact hee
      · exact hworld

private theorem uniswapV3PoolPatchPreservesJumpDest9577 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨9577⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched9577 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨9577⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest9577

private theorem uniswapV3PoolPatchPreservesJumpDest9648 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨9648⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched9648 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨9648⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest9648

private theorem uniswapV3PoolPatchPreservesJumpDest9724 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨9724⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched9724 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨9724⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest9724

private theorem uniswapV3PoolPatchPreservesJumpDest11243 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11243⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched11243 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11243⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest11243

private theorem uniswapV3PoolPatchPreservesJumpDest16216 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨16216⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched16216 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨16216⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest16216

private theorem uniswapV3PoolPatchPreservesJumpDest16233 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨16233⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched16233 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨16233⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest16233

private theorem uniswapV3PoolPatchPreservesJumpDest16246 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨16246⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched16246 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨16246⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest16246

private theorem uniswapV3PoolBurnLockPatchDisjoint33 {v : PoolImmutables}
    {pc : UInt256}
    (hlo : 9577 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 10457) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

private theorem uniswapV3PoolBurnLockDecodeEqTemplate {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 9577 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 10457) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 10457 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (uniswapV3PoolBurnLockPatchDisjoint33 (v := v) (pc := pc) hlo hhi)

private theorem uniswapV3PoolBurnReturnShimPatchDisjoint1 {v : PoolImmutables}
    {pc : UInt256}
    (hlo : 11243 ≤ pc.toNat) (hhi : pc.toNat + 1 ≤ 11248) :
    ∀ p ∈ patches v, pc.toNat + 1 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

private theorem uniswapV3PoolBurnSharedPatchDisjoint33 {v : PoolImmutables}
    {pc : UInt256}
    (hlo : 16216 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 16265) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

private theorem uniswapV3PoolBurnSharedDecodeEqTemplate {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 16216 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 16265) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 16265 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (uniswapV3PoolBurnSharedPatchDisjoint33 (v := v) (pc := pc) hlo hhi)

private theorem uniswapV3PoolBurnSharedTailPatchDisjoint33 {v : PoolImmutables}
    {pc : UInt256}
    (hlo : 16233 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 17313) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

private theorem uniswapV3PoolBurnSharedTailDecodeEqTemplate {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 16233 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 17313) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 17313 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (uniswapV3PoolBurnSharedTailPatchDisjoint33 (v := v) (pc := pc) hlo hhi)

private theorem uniswapV3PoolBurnReturnShimDecodeNoArg {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256} {byte : UInt8} {op : Operation}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 11243 ≤ pc.toNat) (hhi : pc.toNat + 1 ≤ 11248)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some byte)
    (hparse : (some byte >>= parseInstr) = some op)
    (harg : argOnNBytesOfInstr op = 0) :
    decode code pc = some (op, .none) := by
  exact uniswapV3PoolDecodePatchedNoArg hpatch
    (by
      have hsize : 11248 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (uniswapV3PoolBurnReturnShimPatchDisjoint1 (v := v) (pc := pc) hlo hhi)
    hgetTemplate hparse harg

private theorem uniswapV3PoolBurnLockedRevertTailWf {v : PoolImmutables}
    {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨9598⟩ ⟨3⟩ ⟨5001035⟩ ⟨232⟩ .PUSH3 3 := by
  dsimp [solcErrorStringRevertTailWf]
  repeat' constructor
  all_goals
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide

private theorem decodeScalarWordWithMode_int24_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 int24 bytes start =
      some
        (.int (tickSpacingSint24Value (ABI.bytesToWord ((bytes.drop start).take 32))),
          start + 32) := by
  simp only [decodeScalarWordWithMode?]
  unfold readWord? readBytes? int24 int24Int
  rw [if_pos hlen]
  simp only [bind, Option.bind]
  unfold decodeABIWord?
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  rfl

private theorem decodeScalarWordWithMode_uint128_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 uint128 bytes start =
      some
        (.int (Int.ofNat
          (UInt256.land (ABI.bytesToWord ((bytes.drop start).take 32)) uint128Mask).toNat),
          start + 32) := by
  simp only [decodeScalarWordWithMode?]
  unfold readWord? readBytes? uint128 uint128Int
  rw [if_pos hlen]
  simp only [bind, Option.bind]
  unfold decodeABIWord?
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  rw [uint128Mask_decode]
  rfl

private theorem decodeScalarWordsWithMode_int24_int24_uint128_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05 [int24, int24, uint128] bytes 0 =
      some
        [ .int (tickSpacingSint24Value (ABI.bytesToWord (bytes.take 32))),
          .int (tickSpacingSint24Value (ABI.bytesToWord ((bytes.drop 32).take 32))),
          .int (Int.ofNat
            (UInt256.land (ABI.bytesToWord ((bytes.drop 64).take 32)) uint128Mask).toNat) ] := by
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_int24_ok (bytes := bytes) (start := 0)
    (by simpa using hlen0)]
  simp only [List.drop_zero]
  rw [decodeScalarWordWithMode_int24_ok (bytes := bytes) (start := 32) hlen32]
  simp only [bind, Option.bind]
  rw [decodeScalarWordWithMode_uint128_ok (bytes := bytes) (start := 64) hlen64]

private theorem decodeScalarWordsWithMode_int24_int24_uint128_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05 [int24, int24, uint128] bytes 0 =
      none := by
  simp only [decodeScalarWordsWithMode?]
  by_cases hlen0 : (bytes.take 32).length = 32
  · rw [decodeScalarWordWithMode_int24_ok (bytes := bytes) (start := 0)
      (by simpa using hlen0)]
    simp only [List.drop_zero]
    by_cases hlen32 : ((bytes.drop 32).take 32).length = 32
    · rw [decodeScalarWordWithMode_int24_ok (bytes := bytes) (start := 32) hlen32]
      simp only [bind, Option.bind]
      have hlen64 : ¬ ((bytes.drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      unfold decodeScalarWordWithMode? readWord? readBytes? uint128 uint128Int
      rw [if_neg hlen64]
      simp only [bind, Option.bind]
    · unfold decodeScalarWordWithMode? readWord? readBytes? int24 int24Int
      rw [if_neg hlen32]
      simp only [bind, Option.bind]
  · unfold decodeScalarWordWithMode? readWord? readBytes? int24 int24Int
    simp only [List.drop_zero]
    rw [if_neg hlen0]
    simp only [bind, Option.bind]

theorem uniswapV3PoolBurnDecodeOk {v : PoolImmutables} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = some (burnStore I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have htake68 : (((I.calldata.toList.drop 4).drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      calldataWord I.calldata 4 :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((I.calldata.toList.drop 36).take 32) =
      calldataWord I.calldata 36 :=
    decode_word_at_eq I.calldata 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((I.calldata.toList.drop 68).take 32) =
      calldataWord I.calldata 68 :=
    decode_word_at_eq I.calldata 68 (by omega) (by norm_num)
  rw [show (config v).abiDecodeMode = DecodeMode.legacySolc05 from rfl]
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := burnTransition.params.map Param.name)
    (types := (transitionSignature burnTransition).paramTypes) (cd := I.calldata)]
  · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
    change (match decodeScalarWordsWithMode? DecodeMode.legacySolc05 [int24, int24, uint128]
        (I.calldata.toList.drop 4) 0 with
      | some values => decodeCalldata.insertValues ["tickLower", "tickUpper", "amount"] values ∅
      | none => none) = some (burnStore I)
    rw [decodeScalarWordsWithMode_int24_int24_uint128_ok
      (bytes := I.calldata.toList.drop 4) htake4 htake36 htake68]
    simp [decodeCalldata.insertValues, burnStore, burnTickLowerValue, burnTickUpperValue,
      burnAmountValue, burnTickLowerWord, burnTickUpperWord, burnAmountWord]
    rw [hword4, hword36, hword68]
  · native_decide

theorem uniswapV3PoolBurnDecodeShort {v : PoolImmutables} {I : ExecutionEnv}
    (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (burnTransition.params.map Param.name)
      (transitionSignature burnTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [show (config v).abiDecodeMode = DecodeMode.legacySolc05 from rfl]
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := burnTransition.params.map Param.name)
    (types := (transitionSignature burnTransition).paramTypes) (cd := I.calldata)]
  · by_cases hsz4 : I.calldata.size < 4
    · rw [if_pos (by rw [htlen]; omega : I.calldata.toList.length < 4)]
    · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
      change (match decodeScalarWordsWithMode? DecodeMode.legacySolc05
          [int24, int24, uint128] (I.calldata.toList.drop 4) 0 with
        | some values => decodeCalldata.insertValues ["tickLower", "tickUpper", "amount"] values ∅
        | none => none) = none
      rw [decodeScalarWordsWithMode_int24_int24_uint128_none_short
        (bytes := I.calldata.toList.drop 4) (by rw [List.length_drop, htlen]; omega)]
  · native_decide

theorem uniswapV3PoolBurnReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 17 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1852⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 17 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0xa3 0x41 0x23 0xa7
        (uniswapV3PoolSelNat 17) (by native_decide) hsel
  have hgt32 : UInt256.gt (armSelNat code ⟨32⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h43 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨43⟩) hpatch h32 hgt32
  have hgt43 : UInt256.gt (armSelNat code ⟨43⟩) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h152 := uniswapV3PoolSelectorSplitTakenTo (next := ⟨152⟩) hpatch h43 hgt43
  have hgt152 : UInt256.gt (armSelNat code ⟨152⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h163 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨163⟩) hpatch h152 hgt152
  have hmiss16 : (uniswapV3PoolSelBytes 16 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h174 := uniswapV3PoolSelectorArmMissToOf (i := 16) (next := ⟨174⟩)
    hpatch hsz hmiss16 h163
  have h1852 := uniswapV3PoolSelectorArmHitTo (i := 17) (target := ⟨1852⟩)
    hpatch hsz hsel h174
  exact ⟨_, _, h1852⟩

theorem uniswapV3PoolDispatch_burn {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 17 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some burnTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl) (hreceive := by rfl)
    (pre := [])
    (ti := burnTransition)
    (post := [collectTransition v, collectprotocolTransition v, factoryTransition v,
      feeTransition v, feegrowthglobal0X128Transition, feegrowthglobal1X128Transition,
      flashTransition v, increaseobservationcardinalitynextTransition v, initializeTransition,
      liquidityTransition, maxliquiditypertickTransition v, mintTransition v,
      observationsTransition, observeTransition v, positionsTransition, protocolfeesTransition,
      setfeeprotocolTransition v, slot0Transition, snapshotcumulativesinsideTransition v,
      swapTransition v, tickbitmapTransition, tickspacingTransition v, ticksTransition,
      token0Transition v, token1Transition v])
    (by simp [contract, transitions])
    (by simp)
    (by rw [selectorOf, burnSelectorBytes]; simpa [uniswapV3PoolSelBytes] using hsel)

theorem uniswapV3PoolBurnEvmDecodeShort {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 17 == I.calldata.extract 0 4) = true)
    (hshort : I.calldata.size < 100) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hreach := uniswapV3PoolBurnReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by
      rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      omega) hsize]
    rw [show (⟨96⟩ : UInt256).toNat = 96 from by decide]
    rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  exact RD.solcExternalStaticArgsShortReverts (need := ⟨96⟩)
    (entry := ⟨1852⟩) (ret := ⟨621⟩) (decoded := ⟨1874⟩) hreach
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    hlt

theorem uniswapV3PoolBurnExternalLenOk {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 17 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨1874⟩
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨621⟩ ::
        [solcSelectorWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hreach := uniswapV3PoolBurnReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
    exact solcDecodeLenCheckOkUnsigned (by
      rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      rw [show (⟨96⟩ : UInt256).toNat = 96 from by decide]
      omega) hsize
  exact RD.solcExternalStaticArgsLenOk (need := ⟨96⟩)
    (entry := ⟨1852⟩) (ret := ⟨621⟩) (decoded := ⟨1874⟩) hreach
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide))
    hlt

theorem uniswapV3PoolBurnDecodedReachTickLower {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {de ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨1874⟩ (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨1883⟩
      (burnTickLowerCleanWord ee :: ⟨2⟩ :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd1875 : RD code ee g s0 ⟨1875⟩ (de :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1) (C + 1) := by
    simpa using h.jumpdest
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1876 : RD code ee g s0 ⟨1876⟩ (⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1) (C + 1 + 2) := by
    simpa using rd1875.pop
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1877 : RD code ee g s0 ⟨1877⟩ (⟨4⟩ :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1) (C + 1 + 2 + 3) := by
    simpa using rd1876.dup1
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1878 : RD code ee g s0 ⟨1878⟩ (burnTickLowerWord ee :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3) := by
    simpa [burnTickLowerWord, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd1877.calldataload
        (by
          rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
          native_decide)
        (by evm_ov)
  have rd1880 : RD code ee g s0 ⟨1880⟩ (⟨2⟩ :: burnTickLowerWord ee :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3 + 3) := by
    simpa using rd1878.push1 ⟨2⟩
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1881 : RD code ee g s0 ⟨1881⟩ (burnTickLowerWord ee :: ⟨2⟩ :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3 + 3 + 3) := by
    simpa using rd1880.swap1
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1882 : RD code ee g s0 ⟨1882⟩
      (⟨2⟩ :: burnTickLowerWord ee :: ⟨2⟩ :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 1 + 2 + 3 + 3 + 3 + 3 + 3) := by
    simpa using rd1881.dup2
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  exact ⟨_, _, by
    simpa [burnTickLowerCleanWord] using
      (burnRDSignextend rd1882
        (by
          rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
          native_decide)
        (by simp only [List.length_cons]; omega))⟩

theorem uniswapV3PoolBurnTickLowerReachTickUpper {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨1883⟩
      (burnTickLowerCleanWord ee :: ⟨2⟩ :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨1892⟩
      (burnTickUpperCleanWord ee :: ⟨4⟩ :: burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd1884 : RD code ee g s0 ⟨1884⟩
      (⟨4⟩ :: ⟨2⟩ :: burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1) (C + 3) := by
    simpa using h.swap2
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1886 : RD code ee g s0 ⟨1886⟩
      (⟨32⟩ :: ⟨4⟩ :: ⟨2⟩ :: burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1) (C + 3 + 3) := by
    simpa using rd1884.push1 ⟨32⟩
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1887 : RD code ee g s0 ⟨1887⟩
      (⟨4⟩ :: ⟨32⟩ :: ⟨4⟩ :: ⟨2⟩ :: burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1) (C + 3 + 3 + 3) := by
    simpa using rd1886.dup2
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1888 : RD code ee g s0 ⟨1888⟩
      (⟨36⟩ :: ⟨4⟩ :: ⟨2⟩ :: burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1) (C + 3 + 3 + 3 + 3) := by
    simpa using rd1887.add
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1889 : RD code ee g s0 ⟨1889⟩
      (burnTickUpperWord ee :: ⟨4⟩ :: ⟨2⟩ :: burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1) (C + 3 + 3 + 3 + 3 + 3) := by
    simpa [burnTickUpperWord, calldataWord,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide] using
      rd1888.calldataload
        (by
          rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
          native_decide)
        (by evm_ov)
  have rd1890 : RD code ee g s0 ⟨1890⟩
      (⟨4⟩ :: burnTickUpperWord ee :: ⟨2⟩ :: burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 3 + 3 + 3 + 3 + 3 + 3) := by
    simpa using rd1889.swap1
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1891 : RD code ee g s0 ⟨1891⟩
      (⟨2⟩ :: burnTickUpperWord ee :: ⟨4⟩ :: burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 3 + 3 + 3 + 3 + 3 + 3 + 3) := by
    simpa using rd1890.swap2
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  exact ⟨_, _, by
    simpa [burnTickUpperCleanWord] using
      (burnRDSignextend rd1891
        (by
          rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
          native_decide)
        (by simp only [List.length_cons]; omega))⟩

theorem uniswapV3PoolBurnTickUpperReachModifyPosition {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨1892⟩
      (burnTickUpperCleanWord ee :: ⟨4⟩ :: burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc k C)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9577⟩
      (burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      mem aw rdata acc k' C' := by
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ⟨1⟩ = uint128Mask := by
    native_decide
  have hamount :
      UInt256.land uint128Mask (burnAmountWord ee) = burnAmountCleanWord ee := by
    rw [burnAmountCleanWord, u256_land_comm]
  have rd1893 : RD code ee g s0 ⟨1893⟩
      (⟨4⟩ :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1) (C + 3) := by
    simpa using h.swap1
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1895 : RD code ee g s0 ⟨1895⟩
      (⟨64⟩ :: ⟨4⟩ :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1) (C + 3 + 3) := by
    simpa using rd1893.push1 ⟨64⟩
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1896 : RD code ee g s0 ⟨1896⟩
      (⟨68⟩ :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1) (C + 3 + 3 + 3) := by
    simpa using rd1895.add
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1897 : RD code ee g s0 ⟨1897⟩
      (burnAmountWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1) (C + 3 + 3 + 3 + 3) := by
    simpa [burnAmountWord, calldataWord,
      show (⟨68⟩ : UInt256).toNat = 68 from by decide] using
      rd1896.calldataload
        (by
          rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
          native_decide)
        (by evm_ov)
  have rd1899 : RD code ee g s0 ⟨1899⟩
      (⟨1⟩ :: burnAmountWord ee :: burnTickUpperCleanWord ee ::
        burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1) (C + 3 + 3 + 3 + 3 + 3) := by
    simpa using rd1897.push1 ⟨1⟩
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1901 : RD code ee g s0 ⟨1901⟩
      (⟨1⟩ :: ⟨1⟩ :: burnAmountWord ee :: burnTickUpperCleanWord ee ::
        burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 3 + 3 + 3 + 3 + 3 + 3) := by
    simpa using rd1899.push1 ⟨1⟩
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1903 : RD code ee g s0 ⟨1903⟩
      (⟨128⟩ :: ⟨1⟩ :: ⟨1⟩ :: burnAmountWord ee :: burnTickUpperCleanWord ee ::
        burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 3 + 3 + 3 + 3 + 3 + 3 + 3) := by
    simpa using rd1901.push1 ⟨128⟩
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by evm_ov)
  have rd1904 : RD code ee g s0 ⟨1904⟩
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ :: ⟨1⟩ :: burnAmountWord ee ::
        burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3) := by
    simpa using rd1903.shl
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by simp only [List.length_cons]; omega)
  have rd1905 : RD code ee g s0 ⟨1905⟩
      (uint128Mask :: burnAmountWord ee :: burnTickUpperCleanWord ee ::
        burnTickLowerCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3) := by
    simpa [hmask] using rd1904.sub
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by simp only [List.length_cons]; omega)
  have rd1906 : RD code ee g s0 ⟨1906⟩
      (burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3) := by
    simpa [hamount] using rd1905.and
      (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
      (by simp only [List.length_cons]; omega)
  have rd1909 := rd1906.push2 ⟨9577⟩
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  exact ⟨_, _, rd1909.jump
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (uniswapV3PoolJumpDestPatched9577 hpatch)
    (by evm_ov)⟩

theorem uniswapV3PoolBurnLockCheck {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {amount upper lower ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨9577⟩ (amount :: upper :: lower :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9597⟩
      (⟨9648⟩ :: burnUnlockedByte σ ee :: ⟨0⟩ :: ⟨0⟩ :: amount :: upper ::
        lower :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd9578 := by
    simpa using h.jumpdest
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  have rd9580 := by
    simpa using rd9578.push1 ⟨0⟩
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  have rd9581 := by
    simpa using rd9580.dup1
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  obtain ⟨_, _, rd9582₀⟩ := rd9581.sload
    (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
    (by evm_ov)
  have rd9582 := by
    simpa [solcSlotWord] using rd9582₀
  have rd9583 := by
    simpa using rd9582.dup2
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  have rd9584 := by
    simpa using rd9583.swap1
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  have rd9586 := by
    simpa using rd9584.push1 ⟨1⟩
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  have rd9588 := by
    simpa using rd9586.push1 ⟨240⟩
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  have rd9589 := by
    simpa [burnUnlockedShift] using rd9588.shl
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by simp only [List.length_cons]; omega)
  have rd9590 := by
    simpa using rd9589.swap1
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  have rd9591 := by
    simpa using rd9590.div
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  have rd9593 := by
    simpa [burnUint8Mask] using rd9591.push1 ⟨255⟩
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  have rd9594 := by
    simpa [burnUnlockedByte] using rd9593.and
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa using rd9594.push2 ⟨9648⟩
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)⟩

theorem uniswapV3PoolBurnLockEnterOk {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {amount upper lower ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨9577⟩ (amount :: upper :: lower :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hunlocked : burnUnlockedByte σ ee ≠ ⟨0⟩)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9662⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: amount :: upper :: lower :: ret :: R)
      mem aw rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ ee)) k' C' := by
  obtain ⟨_, _, rd9597⟩ := uniswapV3PoolBurnLockCheck hpatch h hov
  have rd9648 :=
    rd9597.jumpiT
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      hunlocked
      (uniswapV3PoolJumpDestPatched9648 hpatch)
      (by evm_ov)
  have rd9649 := by
    simpa using rd9648.jumpdest
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  have rd9651 := by
    simpa using rd9649.push1 ⟨0⟩
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  have rd9652 := by
    simpa using rd9651.dup1
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  obtain ⟨_, _, rd9653₀⟩ := rd9652.sload
    (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
    (by evm_ov)
  have rd9653 := by
    simpa [solcSlotWord] using rd9653₀
  have rd9655 := by
    simpa [burnUint8Mask] using rd9653.push1 ⟨255⟩
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  have rd9657 := by
    simpa using rd9655.push1 ⟨240⟩
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  have rd9658 := by
    simpa using rd9657.shl
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by simp only [List.length_cons]; omega)
  have rd9659 := by
    simpa [burnUnlockedClearMask] using rd9658.not
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  have rd9660 := by
    simpa [burnLockedSlotWord] using rd9659.and
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by simp only [List.length_cons]; omega)
  have rd9661 := by
    simpa using rd9660.dup2
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)
  simpa [burnLockedSlotWord, burnUnlockedClearMask, burnUint8Mask, solcSlotWord] using
    rd9661.sstore hperm
      (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)

theorem uniswapV3PoolBurnLockEnterLockedRevert {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {amount upper lower ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨9577⟩ (amount :: upper :: lower :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hlocked : burnUnlockedByte σ ee = ⟨0⟩)
    (hov : R.length + 11 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, rd9597⟩ := uniswapV3PoolBurnLockCheck hpatch h (by omega)
  have rd9598 := rd9597.jumpiNT
    (by rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]; native_decide)
    hlocked
    (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨9598⟩) (len := ⟨3⟩) (rawWord := ⟨5001035⟩) (shift := ⟨232⟩)
    (word := UInt256.shiftLeft ⟨5001035⟩ ⟨232⟩) (op := .PUSH3) (width := 3)
    rd9598
    (uniswapV3PoolBurnLockedRevertTailWf hpatch)
    (by native_decide)
    rfl
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp only [List.length_cons]; omega)

theorem uniswapV3PoolBurnAfterLockWriteOwner {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {amount upper lower ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨9662⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: amount :: upper :: lower :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9675⟩
      (⟨128⟩ :: ⟨64⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: amount :: upper :: lower :: ret :: R)
      (burnModifyPositionMem1 ee) (UInt256.ofNat 5) rdata (cA, σ) k' C' := by
  have hd9662 : decode code ⟨9662⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9664 : decode code ⟨9664⟩ = some (.DUP1, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9665 : decode code ⟨9665⟩ = some (.MLOAD, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9666 : decode code ⟨9666⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9668 : decode code ⟨9668⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9669 : decode code ⟨9669⟩ = some (.ADD, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9670 : decode code ⟨9670⟩ = some (.DUP3, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9671 : decode code ⟨9671⟩ = some (.MSTORE, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9672 : decode code ⟨9672⟩ = some (.CALLER, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9673 : decode code ⟨9673⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9674 : decode code ⟨9674⟩ = some (.MSTORE, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have rd9664 := by
    simpa using h.push1 ⟨64⟩ hd9662
      (by simp only [List.length_cons]; omega)
  have rd9665 := by
    simpa using rd9664.dup1 hd9664
      (by simp only [List.length_cons]; omega)
  have rd9666 := by
    simpa using rd9665.mload 0 ⟨128⟩ (UInt256.ofNat 3) hd9665
      mem_cost
      solcFreePtrMem_mload64
      (by native_decide)
      (by simp only [List.length_cons]; omega)
  have rd9668 := by
    simpa using rd9666.push1 ⟨128⟩ hd9666
      (by simp only [List.length_cons]; omega)
  have rd9669 := by
    simpa using rd9668.dup2 hd9668
      (by simp only [List.length_cons]; omega)
  have rd9670 := by
    simpa using rd9669.add hd9669
      (by simp only [List.length_cons]; omega)
  have rd9671 := by
    simpa using rd9670.dup3 hd9670
      (by simp only [List.length_cons]; omega)
  have rd9672 := by
    simpa [burnModifyPositionMem0] using
      rd9671.mstore 0 burnModifyPositionMem0 (UInt256.ofNat 3)
        hd9671
        mem_cost
        (by rfl)
        (by native_decide)
        (by simp only [List.length_cons]; omega)
  have rd9673 := by
    simpa using rd9672.caller hd9672
      (by simp only [List.length_cons]; omega)
  have rd9674 := by
    simpa using rd9673.dup2 hd9673
      (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [burnModifyPositionMem1] using
      rd9674.mstore 6 (burnModifyPositionMem1 ee) (UInt256.ofNat 5)
        hd9674
        mem_cost
        (by rfl)
        (by native_decide)
        (by simp only [List.length_cons]; omega)⟩

theorem uniswapV3PoolBurnAfterLockWriteTicks {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨9675⟩
      (⟨128⟩ :: ⟨64⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: burnAmountCleanWord ee ::
        burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee :: ret :: R)
      (burnModifyPositionMem1 ee) (UInt256.ofNat 5) rdata (cA, σ) k C)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9695⟩
      (⟨128⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: burnAmountCleanWord ee ::
        burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee :: ret :: R)
      (burnModifyPositionMem3 ee) (UInt256.ofNat 7) rdata (cA, σ) k' C' := by
  have hd9675 : decode code ⟨9675⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9677 : decode code ⟨9677⟩ = some (.DUP9, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9678 : decode code ⟨9678⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9679 : decode code ⟨9679⟩ = some (.SIGNEXTEND, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9680 : decode code ⟨9680⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9682 : decode code ⟨9682⟩ = some (.DUP4, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9683 : decode code ⟨9683⟩ = some (.ADD, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9684 : decode code ⟨9684⟩ = some (.MSTORE, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9685 : decode code ⟨9685⟩ = some (.DUP8, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9686 : decode code ⟨9686⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9687 : decode code ⟨9687⟩ = some (.SIGNEXTEND, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9688 : decode code ⟨9688⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9689 : decode code ⟨9689⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9690 : decode code ⟨9690⟩ = some (.ADD, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9691 : decode code ⟨9691⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9692 : decode code ⟨9692⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9693 : decode code ⟨9693⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9694 : decode code ⟨9694⟩ = some (.MSTORE, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have rd9677 := by
    simpa using h.push1 ⟨2⟩ hd9675
      (by simp only [List.length_cons]; omega)
  have rd9678 := by
    simpa using rd9677.dup9 hd9677
      (by simp only [List.length_cons]; omega)
  have rd9679 := by
    simpa using rd9678.dup2 hd9678
      (by simp only [List.length_cons]; omega)
  have rd9680 := by
    simpa using burnRDSignextend rd9679 hd9679
      (by simp only [List.length_cons]; omega)
  have rd9682 := by
    simpa using rd9680.push1 ⟨32⟩ hd9680
      (by simp only [List.length_cons]; omega)
  have rd9683 := by
    simpa using rd9682.dup4 hd9682
      (by simp only [List.length_cons]; omega)
  have rd9684 := by
    simpa using rd9683.add hd9683
      (by simp only [List.length_cons]; omega)
  have rd9685 := by
    simpa [burnModifyPositionMem2] using
      rd9684.mstore 3 (burnModifyPositionMem2 ee) (UInt256.ofNat 6)
        hd9684
        mem_cost
        (by rfl)
        (by native_decide)
        (by simp only [List.length_cons]; omega)
  have rd9686 := by
    simpa using rd9685.dup8 hd9685
      (by simp only [List.length_cons]; omega)
  have rd9687 := by
    simpa using rd9686.swap1 hd9686
      (by simp only [List.length_cons]; omega)
  have rd9688 := by
    simpa using burnRDSignextend rd9687 hd9687
      (by simp only [List.length_cons]; omega)
  have rd9689 := by
    simpa using rd9688.swap2 hd9688
      (by simp only [List.length_cons]; omega)
  have rd9690 := by
    simpa using rd9689.dup2 hd9689
      (by simp only [List.length_cons]; omega)
  have rd9691 := by
    simpa using rd9690.add hd9690
      (by simp only [List.length_cons]; omega)
  have rd9692 := by
    simpa using rd9691.swap2 hd9691
      (by simp only [List.length_cons]; omega)
  have rd9693 := by
    simpa using rd9692.swap1 hd9692
      (by simp only [List.length_cons]; omega)
  have rd9694 := by
    simpa using rd9693.swap2 hd9693
      (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [burnModifyPositionMem3] using
      rd9694.mstore 3 (burnModifyPositionMem3 ee) (UInt256.ofNat 7)
        hd9694
        mem_cost
        (by rfl)
        (by native_decide)
        (by simp only [List.length_cons]; omega)⟩

theorem uniswapV3PoolBurnPrepareLiquidityDelta {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨9695⟩
      (⟨128⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: burnAmountCleanWord ee ::
        burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee :: ret :: R)
      (burnModifyPositionMem3 ee) (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨16216⟩
      (burnAmountCleanWord ee :: ⟨9724⟩ :: ⟨224⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: burnAmountCleanWord ee ::
        burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee :: ret :: R)
      (burnModifyPositionMem3 ee) (UInt256.ofNat 7) rdata (cA, σ) k' C' := by
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ⟨1⟩ = uint128Mask := by
    native_decide
  have hamount :
      UInt256.land (burnAmountCleanWord ee) uint128Mask = burnAmountCleanWord ee := by
    exact uint128Mask_clean (by
      simpa [burnAmountCleanWord] using uint128Mask_bound (burnAmountWord ee))
  have hd9695 : decode code ⟨9695⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9696 : decode code ⟨9696⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9697 : decode code ⟨9697⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9698 : decode code ⟨9698⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9699 : decode code ⟨9699⟩ = some (.Push .PUSH2, some (⟨9737⟩, 2)) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9702 : decode code ⟨9702⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9703 : decode code ⟨9703⟩ = some (.Push .PUSH1, some (⟨96⟩, 1)) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9705 : decode code ⟨9705⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9706 : decode code ⟨9706⟩ = some (.ADD, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9707 : decode code ⟨9707⟩ = some (.Push .PUSH2, some (⟨9724⟩, 2)) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9710 : decode code ⟨9710⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9712 : decode code ⟨9712⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9714 : decode code ⟨9714⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9716 : decode code ⟨9716⟩ = some (.SHL, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9717 : decode code ⟨9717⟩ = some (.SUB, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9718 : decode code ⟨9718⟩ = some (.DUP11, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9719 : decode code ⟨9719⟩ = some (.AND, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9720 : decode code ⟨9720⟩ = some (.Push .PUSH2, some (⟨16216⟩, 2)) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9723 : decode code ⟨9723⟩ = some (.JUMP, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have rd9696 := by
    simpa using h.dup2 hd9695
      (by simp only [List.length_cons]; omega)
  have rd9697 := by
    simpa using rd9696.swap1 hd9696
      (by simp only [List.length_cons]; omega)
  have rd9698 := by
    simpa using rd9697.dup2 hd9697
      (by simp only [List.length_cons]; omega)
  have rd9699 := by
    simpa using rd9698.swap1 hd9698
      (by simp only [List.length_cons]; omega)
  have rd9702 := by
    simpa using rd9699.push2 ⟨9737⟩ hd9699
      (by simp only [List.length_cons]; omega)
  have rd9703 := by
    simpa using rd9702.swap1 hd9702
      (by simp only [List.length_cons]; omega)
  have rd9705 := by
    simpa using rd9703.push1 ⟨96⟩ hd9703
      (by simp only [List.length_cons]; omega)
  have rd9706 := by
    simpa using rd9705.dup2 hd9705
      (by simp only [List.length_cons]; omega)
  have rd9707 := by
    simpa using rd9706.add hd9706
      (by simp only [List.length_cons]; omega)
  have rd9710 := by
    simpa using rd9707.push2 ⟨9724⟩ hd9707
      (by simp only [List.length_cons]; omega)
  have rd9712 := by
    simpa using rd9710.push1 ⟨1⟩ hd9710
      (by simp only [List.length_cons]; omega)
  have rd9714 := by
    simpa using rd9712.push1 ⟨1⟩ hd9712
      (by simp only [List.length_cons]; omega)
  have rd9716 := by
    simpa using rd9714.push1 ⟨128⟩ hd9714
      (by simp only [List.length_cons]; omega)
  have rd9717 := by
    simpa using rd9716.shl hd9716
      (by simp only [List.length_cons]; omega)
  have rd9718 := by
    simpa [hmask] using rd9717.sub hd9717
      (by simp only [List.length_cons]; omega)
  have rd9719 := by
    simpa using rd9718.dup11 hd9718
      (by simp only [List.length_cons]; omega)
  have rd9720 := by
    simpa [hamount] using rd9719.and hd9719
      (by simp only [List.length_cons]; omega)
  have rd9723 := by
    simpa using rd9720.push2 ⟨16216⟩ hd9720
      (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd9723.jump hd9723 (uniswapV3PoolJumpDestPatched16216 hpatch)
    (by simp only [List.length_cons]; omega)⟩

theorem uniswapV3PoolBurnLiquidityDeltaInt128Ok {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨16216⟩
      (burnAmountCleanWord ee :: ⟨9724⟩ :: ⟨224⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: burnAmountCleanWord ee ::
        burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee :: ret :: R)
      (burnModifyPositionMem3 ee) (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord ee) = burnAmountCleanWord ee)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9724⟩
      (burnAmountCleanWord ee :: ⟨224⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: burnAmountCleanWord ee ::
        burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee :: ret :: R)
      (burnModifyPositionMem3 ee) (UInt256.ofNat 7) rdata (cA, σ) k' C' := by
  have hd16216 : decode code ⟨16216⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16217 : decode code ⟨16217⟩ = some (.DUP1, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16218 : decode code ⟨16218⟩ = some (.Push .PUSH1, some (⟨15⟩, 1)) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16220 : decode code ⟨16220⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16221 : decode code ⟨16221⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16222 : decode code ⟨16222⟩ = some (.SIGNEXTEND, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16223 : decode code ⟨16223⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16224 : decode code ⟨16224⟩ = some (.EQ, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16225 : decode code ⟨16225⟩ = some (.Push .PUSH2, some (⟨11243⟩, 2)) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16228 : decode code ⟨16228⟩ = some (.JUMPI, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd11243 : decode code ⟨11243⟩ = some (.JUMPDEST, .none) := by
    exact uniswapV3PoolBurnReturnShimDecodeNoArg (pc := ⟨11243⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd11244 : decode code ⟨11244⟩ = some (.SWAP2, .none) := by
    exact uniswapV3PoolBurnReturnShimDecodeNoArg (pc := ⟨11244⟩) (byte := 0x91)
      (op := .SWAP2) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd11245 : decode code ⟨11245⟩ = some (.SWAP1, .none) := by
    exact uniswapV3PoolBurnReturnShimDecodeNoArg (pc := ⟨11245⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd11246 : decode code ⟨11246⟩ = some (.POP, .none) := by
    exact uniswapV3PoolBurnReturnShimDecodeNoArg (pc := ⟨11246⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd11247 : decode code ⟨11247⟩ = some (.JUMP, .none) := by
    exact uniswapV3PoolBurnReturnShimDecodeNoArg (pc := ⟨11247⟩) (byte := 0x56)
      (op := .JUMP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hcond :
      UInt256.eq (burnAmountCleanWord ee)
          (UInt256.signextend ⟨15⟩ (burnAmountCleanWord ee)) ≠ ⟨0⟩ := by
    have heq :
        UInt256.eq (burnAmountCleanWord ee)
            (UInt256.signextend ⟨15⟩ (burnAmountCleanWord ee)) = ⟨1⟩ := by
      rw [hcanon, uInt256_eq_self]
    rw [heq]
    native_decide
  have rd16217 := by
    simpa using h.jumpdest hd16216
      (by simp only [List.length_cons]; omega)
  have rd16218 := by
    simpa using rd16217.dup1 hd16217
      (by simp only [List.length_cons]; omega)
  have rd16220 := by
    simpa using rd16218.push1 ⟨15⟩ hd16218
      (by simp only [List.length_cons]; omega)
  have rd16221 := by
    simpa using rd16220.dup2 hd16220
      (by simp only [List.length_cons]; omega)
  have rd16222 := by
    simpa using rd16221.swap1 hd16221
      (by simp only [List.length_cons]; omega)
  have rd16223 := by
    simpa using burnRDSignextend rd16222 hd16222
      (by simp only [List.length_cons]; omega)
  have rd16224 := by
    simpa using rd16223.dup2 hd16223
      (by simp only [List.length_cons]; omega)
  have rd16225 := by
    simpa using rd16224.eq hd16224
      (by simp only [List.length_cons]; omega)
  have rd16228 := by
    simpa using rd16225.push2 ⟨11243⟩ hd16225
      (by simp only [List.length_cons]; omega)
  have rd11243 := rd16228.jumpiT hd16228 hcond
    (uniswapV3PoolJumpDestPatched11243 hpatch)
    (by simp only [List.length_cons]; omega)
  have rd11244 := by
    simpa using rd11243.jumpdest hd11243
      (by simp only [List.length_cons]; omega)
  have rd11245 := by
    simpa using rd11244.swap2 hd11244
      (by simp only [List.length_cons]; omega)
  have rd11246 := by
    simpa using rd11245.swap1 hd11245
      (by simp only [List.length_cons]; omega)
  have rd11247 := by
    simpa using rd11246.pop hd11246
      (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd11247.jump hd11247 (uniswapV3PoolJumpDestPatched9724 hpatch)
    (by simp only [List.length_cons]; omega)⟩

theorem uniswapV3PoolBurnWriteLiquidityDelta {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨9724⟩
      (burnAmountCleanWord ee :: ⟨224⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: burnAmountCleanWord ee ::
        burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee :: ret :: R)
      (burnModifyPositionMem3 ee) (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨16233⟩
      (⟨128⟩ :: ⟨9737⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnModifyPositionMem4 ee) (UInt256.ofNat 8) rdata (cA, σ) k' C' := by
  have hd9724 : decode code ⟨9724⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9725 : decode code ⟨9725⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9727 : decode code ⟨9727⟩ = some (.SUB, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9728 : decode code ⟨9728⟩ = some (.Push .PUSH1, some (⟨15⟩, 1)) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9730 : decode code ⟨9730⟩ = some (.SIGNEXTEND, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9731 : decode code ⟨9731⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9732 : decode code ⟨9732⟩ = some (.MSTORE, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9733 : decode code ⟨9733⟩ = some (.Push .PUSH2, some (⟨16233⟩, 2)) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd9736 : decode code ⟨9736⟩ = some (.JUMP, .none) := by
    rw [uniswapV3PoolBurnLockDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have rd9725 := by
    simpa using h.jumpdest hd9724
      (by simp only [List.length_cons]; omega)
  have rd9727 := by
    simpa using rd9725.push1 ⟨0⟩ hd9725
      (by simp only [List.length_cons]; omega)
  have rd9728 := by
    simpa using rd9727.sub hd9727
      (by simp only [List.length_cons]; omega)
  have rd9730 := by
    simpa using rd9728.push1 ⟨15⟩ hd9728
      (by simp only [List.length_cons]; omega)
  have rd9731 := by
    simpa using burnRDSignextend rd9730 hd9730
      (by simp only [List.length_cons]; omega)
  have rd9732 := by
    simpa using rd9731.swap1 hd9731
      (by simp only [List.length_cons]; omega)
  have rd9733 := by
    simpa [burnModifyPositionMem4] using
      rd9732.mstore 3 (burnModifyPositionMem4 ee) (UInt256.ofNat 8)
        hd9732
        mem_cost
        (by rfl)
        (by native_decide)
        (by simp only [List.length_cons]; omega)
  have rd9736 := by
    simpa using rd9733.push2 ⟨16233⟩ hd9733
      (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd9736.jump hd9736 (uniswapV3PoolJumpDestPatched16233 hpatch)
    (by simp only [List.length_cons]; omega)⟩

theorem uniswapV3PoolBurnNoDelegateCallOk {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨16233⟩
      (⟨128⟩ :: ⟨9737⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnModifyPositionMem4 ee) (UInt256.ofNat 8) rdata (cA, σ) k C)
    (hguard : uniswapV3PoolNoDelegateCallGuard v ee ≠ ⟨0⟩)
    (hov : R.length + 19 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨16246⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnModifyPositionMem4 ee) (UInt256.ofNat 8) rdata (cA, σ) k' C' := by
  have hd16233 : decode code ⟨16233⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnSharedTailDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16234 : decode code ⟨16234⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [uniswapV3PoolBurnSharedTailDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16236 : decode code ⟨16236⟩ = some (.DUP1, .none) := by
    rw [uniswapV3PoolBurnSharedTailDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16237 : decode code ⟨16237⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [uniswapV3PoolBurnSharedTailDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16239 : decode code ⟨16239⟩ = some (.Push .PUSH2, some (⟨16246⟩, 2)) := by
    rw [uniswapV3PoolBurnSharedTailDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16242 : decode code ⟨16242⟩ = some (.Push .PUSH2, some (⟨11248⟩, 2)) := by
    rw [uniswapV3PoolBurnSharedTailDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have hd16245 : decode code ⟨16245⟩ = some (.JUMP, .none) := by
    rw [uniswapV3PoolBurnSharedTailDecodeEqTemplate hpatch (by native_decide)
      (by native_decide)]
    native_decide
  have rd16234 := by
    simpa using h.jumpdest hd16233
      (by simp only [List.length_cons]; omega)
  have rd16236 := by
    simpa using rd16234.push1 ⟨0⟩ hd16234
      (by simp only [List.length_cons]; omega)
  have rd16237 := by
    simpa using rd16236.dup1 hd16236
      (by simp only [List.length_cons]; omega)
  have rd16239 := by
    simpa using rd16237.push1 ⟨0⟩ hd16237
      (by simp only [List.length_cons]; omega)
  have rd16242 := by
    simpa using rd16239.push2 ⟨16246⟩ hd16239
      (by simp only [List.length_cons]; omega)
  have rd16245 := by
    simpa using rd16242.push2 ⟨11248⟩ hd16242
      (by simp only [List.length_cons]; omega)
  have rd11248 := rd16245.jump hd16245 (uniswapV3PoolJumpDestPatched11248 hpatch)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, hrd⟩ :=
    uniswapV3PoolNoDelegateCallReturnOk (v := v) (code := code) (ee := ee) (g := g)
      (s0 := s0)
      (R := ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (mem := burnModifyPositionMem4 ee) (aw := UInt256.ofNat 8) (rdata := rdata)
      (acc := (cA, σ)) hpatch rd11248 hguard
      (uniswapV3PoolJumpDestPatched16246 hpatch)
      (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa using hrd⟩

theorem uniswapV3PoolBurnLiquidityDeltaInt128Revert {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨16216⟩
      (burnAmountCleanWord ee :: ⟨9724⟩ :: ⟨224⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: burnAmountCleanWord ee ::
        burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee :: ret :: R)
      (burnModifyPositionMem3 ee) (UInt256.ofNat 7) rdata (cA, σ) k C)
    (hcheck :
      UInt256.eq (burnAmountCleanWord ee)
        (UInt256.signextend ⟨15⟩ (burnAmountCleanWord ee)) = ⟨0⟩)
    (hov : R.length + 18 ≤ 1024) :
    RDrev code g s0 := by
  have hd16216 : decode code ⟨16216⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16217 : decode code ⟨16217⟩ = some (.DUP1, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16218 : decode code ⟨16218⟩ = some (.Push .PUSH1, some (⟨15⟩, 1)) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16220 : decode code ⟨16220⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16221 : decode code ⟨16221⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16222 : decode code ⟨16222⟩ = some (.SIGNEXTEND, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16223 : decode code ⟨16223⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16224 : decode code ⟨16224⟩ = some (.EQ, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16225 : decode code ⟨16225⟩ = some (.Push .PUSH2, some (⟨11243⟩, 2)) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16228 : decode code ⟨16228⟩ = some (.JUMPI, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16229 : decode code ⟨16229⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16231 : decode code ⟨16231⟩ = some (.DUP1, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have hd16232 : decode code ⟨16232⟩ = some (.REVERT, .none) := by
    rw [uniswapV3PoolBurnSharedDecodeEqTemplate hpatch (by native_decide) (by native_decide)]
    native_decide
  have rd16217 := by
    simpa using h.jumpdest hd16216
      (by simp only [List.length_cons]; omega)
  have rd16218 := by
    simpa using rd16217.dup1 hd16217
      (by simp only [List.length_cons]; omega)
  have rd16220 := by
    simpa using rd16218.push1 ⟨15⟩ hd16218
      (by simp only [List.length_cons]; omega)
  have rd16221 := by
    simpa using rd16220.dup2 hd16220
      (by simp only [List.length_cons]; omega)
  have rd16222 := by
    simpa using rd16221.swap1 hd16221
      (by simp only [List.length_cons]; omega)
  have rd16223 := by
    simpa using burnRDSignextend rd16222 hd16222
      (by simp only [List.length_cons]; omega)
  have rd16224 := by
    simpa using rd16223.dup2 hd16223
      (by simp only [List.length_cons]; omega)
  have rd16225 := by
    simpa using rd16224.eq hd16224
      (by simp only [List.length_cons]; omega)
  have rd16228 := by
    simpa using rd16225.push2 ⟨11243⟩ hd16225
      (by simp only [List.length_cons]; omega)
  have rd16229 := rd16228.jumpiNT hd16228 hcheck
    (by simp only [List.length_cons]; omega)
  have rd16231 := by
    simpa using rd16229.push1 ⟨0⟩ hd16229
      (by simp only [List.length_cons]; omega)
  have rd16232 := by
    simpa using rd16231.dup1 hd16231
      (by simp only [List.length_cons]; omega)
  exact rd16232.rev 0 hd16232 mem_cost
    (by simp only [List.length_cons]; omega)

end Benchmarks.UniswapV3Pool
