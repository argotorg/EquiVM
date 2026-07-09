import Benchmarks.Dss.Flipper.Dispatch
import Benchmarks.Dss.Flipper.BidStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## `tick(uint256)` -/

abbrev tickId (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev tickLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "id" (.int (Int.ofNat (tickId I).toNat))

abbrev tickNow (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

abbrev tickNow48 (I : ExecutionEnv) : UInt256 :=
  UInt256.land (tickNow I) uint48Mask

abbrev tickBidBase (I : ExecutionEnv) : UInt256 :=
  bidBaseOfWord (tickId I)

abbrev tickBidPackedSlot (I : ExecutionEnv) : UInt256 :=
  bidPackedSlotOfWord (tickId I)

abbrev tickBidEvaledRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (.int (Int.ofNat (tickId I).toNat)), .field field] }

abbrev tickEndWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperUint48Offset26Word slot σ I

abbrev tickTicWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperUint48Offset20Word slot σ I

abbrev tickTauWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperUint48Offset6Word ⟨5⟩ σ I

abbrev tickEndNewWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (tickNow48 I + tickTauWord σ I) uint48Mask

abbrev tickEndStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  setUint48Offset26Word (flipperSlotWord (tickBidPackedSlot I) σ I)
    (tickEndNewWord σ I)

abbrev tickLocalsWithEnd (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (tickLocals I).insert "end_" (.int (Int.ofNat (tickEndNewWord σ I).toNat))

noncomputable abbrev tickTicCheckedMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (tickId I) ⟨1⟩
    (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem)

theorem tickBidBase_eq_bidsBase (I : ExecutionEnv) :
    bidsBase (.int (Int.ofNat (tickId I).toNat)) = tickBidBase I := by
  simpa [tickBidBase] using bidsBase_intOfNatWord (tickId I)

theorem tickLocals_get_id (I : ExecutionEnv) :
    (tickLocals I).get? "id" =
      some (.int (Int.ofNat (tickId I).toNat)) := by
  rw [tickLocals, store_get_self]

theorem tickLocals_get_bids (I : ExecutionEnv) :
    (tickLocals I).get? "bids" = none := by
  rw [tickLocals, store_get_ne _ _ (by decide)]
  simp

theorem tickLocals_get_tau (I : ExecutionEnv) :
    (tickLocals I).get? "tau" = none := by
  rw [tickLocals, store_get_ne _ _ (by decide)]
  simp

theorem tickLocals_get_endNew_none (I : ExecutionEnv) :
    (tickLocals I).get? "end_" = none := by
  rw [tickLocals, store_get_ne _ _ (by decide)]
  simp

theorem tickLocalsWithEnd_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (tickLocalsWithEnd σ I).get? "id" =
      some (.int (Int.ofNat (tickId I).toNat)) := by
  rw [tickLocalsWithEnd, store_get_ne _ _ (by decide)]
  exact tickLocals_get_id I

theorem tickLocalsWithEnd_get_bids (σ : AccountMap) (I : ExecutionEnv) :
    (tickLocalsWithEnd σ I).get? "bids" = none := by
  rw [tickLocalsWithEnd, store_get_ne _ _ (by decide)]
  exact tickLocals_get_bids I

theorem tickLocalsWithEnd_get_endNew (σ : AccountMap) (I : ExecutionEnv) :
    (tickLocalsWithEnd σ I).get? "end_" =
      some (.int (Int.ofNat (tickEndNewWord σ I).toNat)) := by
  rw [tickLocalsWithEnd, store_get_self]

theorem tickNow48_bound (I : ExecutionEnv) :
    (tickNow48 I).toNat < 2 ^ 48 := by
  simpa [tickNow48, EVM.twoPow] using uint48Mask_bound (tickNow I)

theorem tickTauWord_bound (σ : AccountMap) (I : ExecutionEnv) :
    (tickTauWord σ I).toNat < 2 ^ 48 := by
  simpa [tickTauWord, EVM.twoPow] using
    uint48Mask_bound (UInt256.div (flipperSlotWord ⟨5⟩ σ I) uint48Divisor)

theorem tickEndNewWord_bound (σ : AccountMap) (I : ExecutionEnv) :
    (tickEndNewWord σ I).toNat < 2 ^ 48 := by
  simpa [tickEndNewWord, EVM.twoPow] using uint48Mask_bound (tickNow48 I + tickTauWord σ I)

theorem tickEndNewWord_toNat (σ : AccountMap) (I : ExecutionEnv) :
    (tickEndNewWord σ I).toNat =
      ((tickNow48 I).toNat + (tickTauWord σ I).toNat) % 2 ^ 48 := by
  rw [tickEndNewWord, uint48Mask_toNat_mod, uadd_toNat]
  have hnow := tickNow48_bound I
  have htau := tickTauWord_bound σ I
  have hsum :
      (tickNow48 I).toNat + (tickTauWord σ I).toNat < UInt256.size := by
    calc
      (tickNow48 I).toNat + (tickTauWord σ I).toNat < 2 ^ 48 + 2 ^ 48 :=
        Nat.add_lt_add hnow htau
      _ = 2 ^ 49 := by norm_num
      _ < UInt256.size := by norm_num [UInt256.size]
  rw [Nat.mod_eq_of_lt hsum]

theorem tickEndNewWord_fullTimestampAdd (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.land (tickNow I + tickTauWord σ I) uint48Mask = tickEndNewWord σ I := by
  apply u256_inj
  rw [uint48Mask_toNat_mod, tickEndNewWord_toNat, uadd_toNat]
  have hdvd : 2 ^ 48 ∣ UInt256.size := by
    norm_num [UInt256.size]
  rw [Nat.mod_mod_of_dvd _ hdvd]
  rw [Nat.add_mod]
  rw [← uint48Mask_toNat_mod (tickNow I)]
  rw [Nat.mod_eq_of_lt (tickTauWord_bound σ I)]

theorem tickEndNewWord_toNat_noOverflow {σ : AccountMap} {I : ExecutionEnv}
    (hfit : (tickNow48 I).toNat + (tickTauWord σ I).toNat < 2 ^ 48) :
    (tickEndNewWord σ I).toNat =
      (tickNow48 I).toNat + (tickTauWord σ I).toNat := by
  rw [tickEndNewWord_toNat]
  exact Nat.mod_eq_of_lt hfit

theorem tickEndNewWord_toNat_overflow {σ : AccountMap} {I : ExecutionEnv}
    (hover : 2 ^ 48 ≤ (tickNow48 I).toNat + (tickTauWord σ I).toNat) :
    (tickEndNewWord σ I).toNat =
      (tickNow48 I).toNat + (tickTauWord σ I).toNat - 2 ^ 48 := by
  rw [tickEndNewWord_toNat]
  have hlt :
      (tickNow48 I).toNat + (tickTauWord σ I).toNat - 2 ^ 48 < 2 ^ 48 := by
    have hnow := tickNow48_bound I
    have htau := tickTauWord_bound σ I
    omega
  rw [Nat.mod_eq_sub_mod hover, Nat.mod_eq_of_lt hlt]

theorem tickEndNewWord_ge_now48_noOverflow {σ : AccountMap} {I : ExecutionEnv}
    (hfit : (tickNow48 I).toNat + (tickTauWord σ I).toNat < 2 ^ 48) :
    (tickNow48 I).toNat ≤ (tickEndNewWord σ I).toNat := by
  rw [tickEndNewWord_toNat_noOverflow hfit]
  omega

theorem tickEndNewWord_lt_now48_overflow {σ : AccountMap} {I : ExecutionEnv}
    (hover : 2 ^ 48 ≤ (tickNow48 I).toNat + (tickTauWord σ I).toNat) :
    (tickEndNewWord σ I).toNat < (tickNow48 I).toNat := by
  rw [tickEndNewWord_toNat_overflow hover]
  have htau := tickTauWord_bound σ I
  omega

theorem evalStorageRef_tickBidField {evm : EVM.State} {I : ExecutionEnv} {field : Ident} :
    evalStorageRef config { contract := contract, locals := tickLocals I } evm
      (bidsF (.var "id") field) = .ok (tickBidEvaledRef I field) := by
  simp [tickBidEvaledRef, tickLocals, bidsF, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind,
    pure, bind]

theorem evalStorageRef_tickTau {evm : EVM.State} {I : ExecutionEnv} :
    evalStorageRef config { contract := contract, locals := tickLocals I } evm tauRef =
      .ok ({ base := "tau", steps := [] } : EvaledStorageRef) := by
  simp [tauRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]

theorem evalStorageRef_tickBidFieldWithEnd {evm : EVM.State} {σ : AccountMap}
    {I : ExecutionEnv} {field : Ident} :
    evalStorageRef config { contract := contract, locals := tickLocalsWithEnd σ I } evm
      (bidsF (.var "id") field) = .ok (tickBidEvaledRef I field) := by
  simp [tickBidEvaledRef, tickLocalsWithEnd, tickLocals, bidsF, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, pure, bind, ← Std.HashMap.get?_eq_getElem?, store_get_ne,
    store_get_self]

theorem evalExpr_tickEnd {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := tickLocals I }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "id") "end")) =
        .ok (.int (Int.ofNat (tickEndWord (tickBidPackedSlot I) σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint48Int)
    (loc := uint48Loc (tickBidPackedSlot I) ⟨26, by decide⟩ (by decide))
    (hbase := tickLocals_get_bids I)
    (her := evalStorageRef_tickBidField (evm := initState cA gh bl σ σ₀ g A I)
      (I := I) (field := "end"))
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, tickBidEvaledRef, contract, storageDecls,
        BidStructTy, uint48St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, tickBidEvaledRef,
        tickBidPackedSlot, bidPackedSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_uint48_offset26 (initState cA gh bl σ σ₀ g A I)
      (tickBidPackedSlot I))

theorem evalExpr_tickTic {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := tickLocals I }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "id") "tic")) =
        .ok (.int (Int.ofNat (tickTicWord (tickBidPackedSlot I) σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint48Int)
    (loc := uint48Loc (tickBidPackedSlot I) ⟨20, by decide⟩ (by decide))
    (hbase := tickLocals_get_bids I)
    (her := evalStorageRef_tickBidField (evm := initState cA gh bl σ σ₀ g A I)
      (I := I) (field := "tic"))
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, tickBidEvaledRef, contract, storageDecls,
        BidStructTy, uint48St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, tickBidEvaledRef,
        tickBidPackedSlot, bidPackedSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_uint48_offset20 (initState cA gh bl σ σ₀ g A I)
      (tickBidPackedSlot I))

theorem evalExpr_tickTau {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := tickLocals I }
      (initState cA gh bl σ σ₀ g A I) (.storage tauRef) =
        .ok (.int (Int.ofNat (tickTauWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint48Int)
    (loc := uint48Loc ⟨5⟩ ⟨6, by decide⟩ (by decide))
    (hbase := tickLocals_get_tau I)
    (her := evalStorageRef_tickTau (evm := initState cA gh bl σ σ₀ g A I) (I := I))
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint48St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_uint48_offset6 (initState cA gh bl σ σ₀ g A I) ⟨5⟩)

theorem evalExpr_tickEndLtTimestamp_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : (tickEndWord (tickBidPackedSlot I) σ I).toNat < (tickNow I).toNat) :
    evalExpr? config { contract := contract, locals := tickLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool true) := by
  have hend := evalExpr_tickEnd (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  simp only [evalExpr?, hend, EvalResult.bind, bind, envValue, pure]
  simp [evalBinaryOp?, tickNow, initState, hlt]

theorem evalExpr_tickEndLtTimestamp_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hge : (tickNow I).toNat ≤ (tickEndWord (tickBidPackedSlot I) σ I).toNat) :
    evalExpr? config { contract := contract, locals := tickLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
        .ok (.bool false) := by
  have hend := evalExpr_tickEnd (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  simp only [evalExpr?, hend, EvalResult.bind, bind, envValue, pure]
  have hnot :
      ¬ (tickEndWord (tickBidPackedSlot I) σ I).toNat <
        (UInt256.ofNat (initState cA gh bl σ σ₀ g A I).executionEnv.header.timestamp).toNat := by
    simpa [tickNow, initState] using not_lt.mpr hge
  simp [evalBinaryOp?, hnot]

theorem evalExpr_tickTicEqZero_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (htic : tickTicWord (tickBidPackedSlot I) σ I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tickLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
        .ok (.bool true) := by
  have hticEval := evalExpr_tickTic (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  simp only [evalExpr?, hticEval, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, htic]

theorem evalExpr_tickTicEqZero_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (htic : tickTicWord (tickBidPackedSlot I) σ I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tickLocals I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
        .ok (.bool false) := by
  have hticEval := evalExpr_tickTic (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  simp only [evalExpr?, hticEval, EvalResult.bind, bind, pure]
  have hzero : ¬ (tickTicWord (tickBidPackedSlot I) σ I).toNat = 0 := by
    intro hz
    exact htic (uint256_toNat_eq_zero hz)
  simp [evalBinaryOp?, hzero]

theorem evalExpr_tickNow48 {evm : EVM.State} {locals : Store} {I : ExecutionEnv}
    (hts : evm.executionEnv.header.timestamp = I.header.timestamp) :
    evalExpr? config { contract := contract, locals := locals } evm now48 =
      .ok (.int (Int.ofNat (tickNow48 I).toNat)) := by
  have hmod :
      (Int.ofNat (tickNow I).toNat) % uint48Modulus =
        Int.ofNat (tickNow48 I).toNat := by
    calc
      (Int.ofNat (tickNow I).toNat) % uint48Modulus =
          Int.ofNat ((tickNow I).toNat % 2 ^ 48) := by
          rw [uint48Modulus]
          exact (Int.natCast_mod (tickNow I).toNat (2 ^ 48)).symm
      _ = Int.ofNat (tickNow48 I).toNat := by
          rw [← uint48Mask_toNat_mod (tickNow I)]
  rw [now48, wrap48]
  simp only [evalExpr?, envValue, hts, EvalResult.bind, bind, pure]
  change evalBinaryOp? .mod (Value.int (Int.ofNat (tickNow I).toNat))
      (Value.int uint48Modulus) =
    .ok (Value.int (Int.ofNat (tickNow48 I).toNat))
  change (if uint48Modulus = 0 then EvalResult.revert else
      .ok (Value.int ((Int.ofNat (tickNow I).toNat) % uint48Modulus))) =
    .ok (Value.int (Int.ofNat (tickNow48 I).toNat))
  rw [if_neg (by norm_num [uint48Modulus]), hmod]

theorem evalExpr_tickEndNew {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := tickLocals I }
      (initState cA gh bl σ σ₀ g A I) (wrap48 (.binary .add now48 (.storage tauRef))) =
        .ok (.int (Int.ofNat (tickEndNewWord σ I).toNat)) := by
  have hnow := evalExpr_tickNow48
    (evm := initState cA gh bl σ σ₀ g A I) (locals := tickLocals I) (I := I) (by rfl)
  have htau := evalExpr_tickTau (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  rw [wrap48]
  simp only [evalExpr?, hnow, htau, EvalResult.bind, bind, pure]
  change (if uint48Modulus = 0 then EvalResult.revert else
      .ok (Value.int (((Int.ofNat (tickNow48 I).toNat) +
        Int.ofNat (tickTauWord σ I).toNat) % uint48Modulus))) =
    .ok (Value.int (Int.ofNat (tickEndNewWord σ I).toNat))
  have hmod :
      ((Int.ofNat (tickNow48 I).toNat) + Int.ofNat (tickTauWord σ I).toNat) %
          uint48Modulus =
        Int.ofNat (tickEndNewWord σ I).toNat := by
    calc
      ((Int.ofNat (tickNow48 I).toNat) + Int.ofNat (tickTauWord σ I).toNat) %
          uint48Modulus =
          Int.ofNat (((tickNow48 I).toNat + (tickTauWord σ I).toNat) % 2 ^ 48) := by
          rw [show (Int.ofNat (tickNow48 I).toNat +
              Int.ofNat (tickTauWord σ I).toNat) =
              Int.ofNat ((tickNow48 I).toNat + (tickTauWord σ I).toNat) by simp]
          rw [uint48Modulus]
          exact (Int.natCast_mod
            ((tickNow48 I).toNat + (tickTauWord σ I).toNat) (2 ^ 48)).symm
      _ = Int.ofNat (tickEndNewWord σ I).toNat := by
          rw [← tickEndNewWord_toNat σ I]
  rw [if_neg (by norm_num [uint48Modulus]), hmod]

theorem evalExpr_tickEndVarWithEnd {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := tickLocalsWithEnd σ I } evm
      (.var "end_") = .ok (.int (Int.ofNat (tickEndNewWord σ I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((tickLocalsWithEnd σ I).get? "end_") =
    .ok (.int (Int.ofNat (tickEndNewWord σ I).toNat))
  rw [tickLocalsWithEnd_get_endNew]
  rfl

theorem evalExpr_tickEndNewGeNow_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hfit : (tickNow48 I).toNat + (tickTauWord σ I).toNat < 2 ^ 48) :
    evalExpr? config { contract := contract, locals := tickLocalsWithEnd σ I }
      (initState cA gh bl σ σ₀ g A I) (.binary .ge (.var "end_") now48) =
        .ok (.bool true) := by
  have hend := evalExpr_tickEndVarWithEnd
    (evm := initState cA gh bl σ σ₀ g A I) (σ := σ) (I := I)
  have hnow :
      evalExpr? config { contract := contract, locals := tickLocalsWithEnd σ I }
        (initState cA gh bl σ σ₀ g A I) now48 =
          .ok (.int (Int.ofNat (tickNow48 I).toNat)) := by
    exact evalExpr_tickNow48 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := tickLocalsWithEnd σ I) (I := I) (by rfl)
  have hgeInt :
      Int.ofNat (tickEndNewWord σ I).toNat ≥ Int.ofNat (tickNow48 I).toNat := by
    exact Int.ofNat_le.mpr (tickEndNewWord_ge_now48_noOverflow hfit)
  simp only [evalExpr?, hend, hnow, EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact tickEndNewWord_ge_now48_noOverflow hfit

theorem evalExpr_tickEndNewGeNow_false {cA gh bl σ σ₀ A I} {g : Sat256}
    (hover : 2 ^ 48 ≤ (tickNow48 I).toNat + (tickTauWord σ I).toNat) :
    evalExpr? config { contract := contract, locals := tickLocalsWithEnd σ I }
      (initState cA gh bl σ σ₀ g A I) (.binary .ge (.var "end_") now48) =
        .ok (.bool false) := by
  have hend := evalExpr_tickEndVarWithEnd
    (evm := initState cA gh bl σ σ₀ g A I) (σ := σ) (I := I)
  have hnow :
      evalExpr? config { contract := contract, locals := tickLocalsWithEnd σ I }
        (initState cA gh bl σ σ₀ g A I) now48 =
          .ok (.int (Int.ofNat (tickNow48 I).toNat)) := by
    exact evalExpr_tickNow48 (evm := initState cA gh bl σ σ₀ g A I)
      (locals := tickLocalsWithEnd σ I) (I := I) (by rfl)
  have hnotInt :
      ¬ Int.ofNat (tickEndNewWord σ I).toNat ≥ Int.ofNat (tickNow48 I).toNat := by
    intro hbad
    exact (not_le.mpr (tickEndNewWord_lt_now48_overflow hover)) (Int.ofNat_le.mp hbad)
  simp only [evalExpr?, hend, hnow, EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact tickEndNewWord_lt_now48_overflow hover

theorem assign_tickEndStorage (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (tickBidPackedSlot I)
      (setUint48Offset26Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (tickBidPackedSlot I))
        (tickEndNewWord σ I))
    assignStorageRef? config { contract := contract, locals := tickLocalsWithEnd σ I } evm
      .storage (bidsF (.var "id") "end")
      (.int (Int.ofNat (tickEndNewWord σ I).toNat)) =
        .ok ({ contract := contract, locals := tickLocalsWithEnd σ I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint48St)
      (er := tickBidEvaledRef I "end")
      (loc := uint48Loc (tickBidPackedSlot I) ⟨26, by decide⟩ (by decide))
      (hbase := tickLocalsWithEnd_get_bids σ I)
      (her := evalStorageRef_tickBidFieldWithEnd (evm := evm) (σ := σ) (I := I)
        (field := "end"))
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, tickBidEvaledRef, contract, storageDecls,
          BidStructTy, uint48St])
      (hloc := by
        funext evm
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, tickBidEvaledRef,
          tickBidPackedSlot, bidPackedSlotOfWord, bidBaseOfWord]
        unfold bidsBase mapSlot solcMappingSlot
        rw [keyValueToWord_uint256_natCast])
  simpa [evm'] using
    flipperStorageLocStore_uint48_offset26 evm (tickBidPackedSlot I) (tickEndNewWord σ I)
      (tickEndNewWord_bound σ I)

-- LIBRARY CANDIDATE: legacy-mode single `uint256` calldata decoding.
theorem flipperDecodeCalldata_legacyUInt256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

-- LIBRARY CANDIDATE: legacy-mode single `uint256` short-calldata failure.
theorem flipperDecodeCalldata_legacyUInt256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
    (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem flipperDecode_tick_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (tickTransition.params.map Param.name)
      (transitionSignature tickTransition).paramTypes I.calldata = some (tickLocals I) := by
  simpa [config, tickTransition, tickLocals, tickId, uint256] using
    (flipperDecodeCalldata_legacyUInt256_ok (cd := I.calldata) (x := "id") hsz36)

theorem flipperDecode_tick_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (tickTransition.params.map Param.name)
      (transitionSignature tickTransition).paramTypes I.calldata = none := by
  simpa [config, tickTransition, uint256] using
    (flipperDecodeCalldata_legacyUInt256_none_short (cd := I.calldata) (x := "id") hsz4
      hshort)

theorem flipperReachTickBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flipperSelBytes 14)) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨938⟩ [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flipperSelWord I = ⟨0xfc7b6aee⟩ :=
    flipperSelWord_eq_of_beq I hsz 0xfc 0x7b 0x6a 0xee ⟨0xfc7b6aee⟩
      (by native_decide) (by simpa [flipperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat flipperBytecode flipperLowSplitPc)
      (flipperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowHighFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowHighFirstArmPc 4))
        (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact flipperReachLowHighBody 4 (by omega) ⟨938⟩ hcode hwv hsz hsize hroot hlow
    heq0 htake (by jump_dest) (by native_decide)

theorem RD.flipperTickDecodeToRoutine {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨960⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = flipperBytecode)
    (hroutine : (D_J code 0).contains ⟨5964⟩ = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨5964⟩
      (calldataWord ee.calldata 4 :: ret :: sel :: R) mem aw rdata acc k' C' := by
  subst hwf
  have rd5964 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw push2 ⟨5964⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) hroutine (by evm_ov)]
  exact ⟨_, _, by simpa [calldataWord] using rd5964⟩

theorem flipperTickX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨938⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5964⟩
        [tickId I, ⟨323⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flipperBytecode) (sel := sel) (entry := ⟨938⟩) (ret := ⟨323⟩)
    (decoded := ⟨960⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.flipperTickDecodeToRoutine
    (code := flipperBytecode) (ret := ⟨323⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [tickId] using hroutine⟩

theorem flipperTickX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨938⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flipperBytecode) (sel := sel) (entry := ⟨938⟩) (ret := ⟨323⟩)
    (decoded := ⟨960⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem flipperTickDecodePushMask5992 :
    decode flipperBytecode (⟨5992⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperTickDecodePushMask6098 :
    decode flipperBytecode (⟨6098⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

abbrev flipperTickBidAlreadyPlacedWord : UInt256 :=
  ⟨31853446598541861569121664937091529620694441758256295719644551114134306947072⟩

theorem flipperTickDecodePushBidAlreadyPlaced6138 :
    decode flipperBytecode (⟨6138⟩ : UInt256) =
      some (.Push .PUSH32, some (flipperTickBidAlreadyPlacedWord, 32)) := by
  native_decide

theorem flipperTickDecodePushMask6204 :
    decode flipperBytecode (⟨6204⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperTickDecodePushMask6237 :
    decode flipperBytecode (⟨6237⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperTickDecodePushMask6276 :
    decode flipperBytecode (⟨6276⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperTickX_endCheckOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hlt : (tickEndWord (tickBidPackedSlot I) σ I).toNat < (tickNow I).toNat)
    (h : RD flipperBytecode I g s0 ⟨5964⟩ [tickId I, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨6072⟩ [tickId I, ret, sel]
      (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd5982 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tickId I) solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (tickId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (tickId I) solcFreePtrMem_size)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k5983, C5983, rd5983raw⟩ := rd5982.sload (by native_decide) (by evm_ov)
  have rd5983 : RD flipperBytecode I g s0 ⟨5983⟩
      [flipperSlotWord (tickBidPackedSlot I) σ I, tickId I, ret, sel]
      (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k5983 C5983 := by
    have hslotAdd :
        ⟨2⟩ + solcMappingSlot ⟨1⟩ (tickId I) =
          solcMappingSlot ⟨1⟩ (tickId I) + ⟨2⟩ := by
      exact u256_add_comm _ _
    simpa [tickBidPackedSlot, bidPackedSlotOfWord, bidBaseOfWord, flipperSlotWord,
      hslotAdd] using
      rd5983raw
  have rd6000 := evm_run rd5983 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTickDecodePushMask5992
      (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov)]
  have hltWord :
      UInt256.lt (tickEndWord (tickBidPackedSlot I) σ I) (tickNow I) = ⟨1⟩ :=
    ult_one hlt
  have hltRaw :
      UInt256.lt
        (UInt256.land uint48Mask
          (UInt256.div (flipperSlotWord (tickBidPackedSlot I) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)))
        (UInt256.ofNat I.header.timestamp) = ⟨1⟩ := by
    simpa [tickEndWord, flipperUint48Offset26Word, tickNow, uint48Divisor26,
      u256_land_comm] using hltWord
  rw [hltRaw] at rd6000
  have rd6001 := rd6000.push2 ⟨6072⟩ (by native_decide) (by evm_ov)
  have rd6072 := rd6001.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact ⟨_, _, rd6072⟩

theorem flipperTickX_notFinished {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hge : (tickNow I).toNat ≤ (tickEndWord (tickBidPackedSlot I) σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨5964⟩ [tickId I, ret, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd5982 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tickId I) solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (tickId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (tickId I) solcFreePtrMem_size)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k5983, C5983, rd5983raw⟩ := rd5982.sload (by native_decide) (by evm_ov)
  have rd5983 : RD flipperBytecode I g s0 ⟨5983⟩
      [flipperSlotWord (tickBidPackedSlot I) σ I, tickId I, ret, sel]
      (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k5983 C5983 := by
    have hslotAdd :
        ⟨2⟩ + solcMappingSlot ⟨1⟩ (tickId I) =
          solcMappingSlot ⟨1⟩ (tickId I) + ⟨2⟩ := by
      exact u256_add_comm _ _
    simpa [tickBidPackedSlot, bidPackedSlotOfWord, bidBaseOfWord, flipperSlotWord,
      hslotAdd] using
      rd5983raw
  have rd6000 := evm_run rd5983 with [
    raw timestamp (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTickDecodePushMask5992
      (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov)]
  have hgeWord :
      UInt256.lt (tickEndWord (tickBidPackedSlot I) σ I) (tickNow I) = ⟨0⟩ :=
    ult_zero hge
  have hgeRaw :
      UInt256.lt
        (UInt256.land uint48Mask
          (UInt256.div (flipperSlotWord (tickBidPackedSlot I) σ I)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)))
        (UInt256.ofNat I.header.timestamp) = ⟨0⟩ := by
    simpa [tickEndWord, flipperUint48Offset26Word, tickNow, uint48Divisor26,
      u256_land_comm] using hgeWord
  rw [hgeRaw] at rd6000
  have rd6001 := rd6000.push2 ⟨6072⟩ (by native_decide) (by evm_ov)
  have rd6005 := rd6001.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨6005⟩) (len := ⟨20⟩)
    (rawWord := (⟨100511754872539569357457718180397213934685919577⟩ : UInt256))
    (shift := ⟨98⟩) (op := .PUSH20) (width := 20)
    (word := UInt256.shiftLeft
      (⟨100511754872539569357457718180397213934685919577⟩ : UInt256) ⟨98⟩)
    rd6005
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) (by rfl)
    (twoWordHashMem_size_96 (tickId I) ⟨1⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (tickId I) ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp)

theorem flipperTickX_ticCheckOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (htic : tickTicWord (tickBidPackedSlot I) σ I = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨6072⟩ [tickId I, ret, sel]
      (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨6187⟩ [tickId I, ret, sel]
      (twoWordHashMem (tickId I) ⟨1⟩
        (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd6090 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tickId I)
        (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (tickId I) ⟨1⟩
        (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (tickId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (tickId I)
        (twoWordHashMem_size_96 (tickId I) ⟨1⟩ solcFreePtrMem_size))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k6091, C6091, rd6091raw⟩ := rd6090.sload (by native_decide) (by evm_ov)
  have rd6091 : RD flipperBytecode I g s0 ⟨6091⟩
      [flipperSlotWord (tickBidPackedSlot I) σ I, tickId I, ret, sel]
      (twoWordHashMem (tickId I) ⟨1⟩
        (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6091 C6091 := by
    have hslotAdd :
        ⟨2⟩ + solcMappingSlot ⟨1⟩ (tickId I) =
          solcMappingSlot ⟨1⟩ (tickId I) + ⟨2⟩ := by
      exact u256_add_comm _ _
    simpa [tickBidPackedSlot, bidPackedSlotOfWord, bidBaseOfWord, flipperSlotWord,
      hslotAdd] using
      rd6091raw
  have rd6106 := evm_run rd6091 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTickDecodePushMask6098
      (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  have hraw :
      UInt256.land uint48Mask
        (UInt256.div (flipperSlotWord (tickBidPackedSlot I) σ I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)) = ⟨0⟩ := by
    simpa [tickTicWord, flipperUint48Offset20Word, uint48Divisor20, u256_land_comm]
      using htic
  rw [hraw] at rd6106
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6106
  have rd6107 := rd6106.push2 ⟨6187⟩ (by native_decide) (by evm_ov)
  have rd6187 := rd6107.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact ⟨_, _, rd6187⟩

theorem flipperTickX_bidAlreadyPlaced {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (htic : tickTicWord (tickBidPackedSlot I) σ I ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨6072⟩ [tickId I, ret, sel]
      (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd6090 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tickId I)
        (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (tickId I) ⟨1⟩
        (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (tickId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (tickId I)
        (twoWordHashMem_size_96 (tickId I) ⟨1⟩ solcFreePtrMem_size))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k6091, C6091, rd6091raw⟩ := rd6090.sload (by native_decide) (by evm_ov)
  have rd6091 : RD flipperBytecode I g s0 ⟨6091⟩
      [flipperSlotWord (tickBidPackedSlot I) σ I, tickId I, ret, sel]
      (twoWordHashMem (tickId I) ⟨1⟩
        (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6091 C6091 := by
    have hslotAdd :
        ⟨2⟩ + solcMappingSlot ⟨1⟩ (tickId I) =
          solcMappingSlot ⟨1⟩ (tickId I) + ⟨2⟩ := by
      exact u256_add_comm _ _
    simpa [tickBidPackedSlot, bidPackedSlotOfWord, bidBaseOfWord, flipperSlotWord,
      hslotAdd] using
      rd6091raw
  have rd6106 := evm_run rd6091 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTickDecodePushMask6098
      (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  let ticRaw :=
    UInt256.land uint48Mask
      (UInt256.div (flipperSlotWord (tickBidPackedSlot I) σ I)
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
  have hrawNe : ticRaw ≠ ⟨0⟩ := by
    intro hbad
    exact htic (by
      simpa [ticRaw, tickTicWord, flipperUint48Offset20Word, uint48Divisor20,
        u256_land_comm] using hbad)
  have hiszero : UInt256.isZero ticRaw = ⟨0⟩ := isZero_eq_zero_of_ne hrawNe
  change RD flipperBytecode I g s0 ⟨6107⟩
    (UInt256.isZero ticRaw :: tickId I :: ret :: sel :: [])
    (twoWordHashMem (tickId I) ⟨1⟩
      (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem))
    (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at rd6106
  rw [hiszero] at rd6106
  have rd6111 := rd6106.push2 ⟨6187⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  let ticMem :=
    twoWordHashMem (tickId I) ⟨1⟩
      (twoWordHashMem (tickId I) ⟨1⟩ solcFreePtrMem)
  have hmem : ticMem.size = 96 := by
    dsimp [ticMem]
    exact twoWordHashMem_size_96 (tickId I) ⟨1⟩
      (twoWordHashMem_size_96 (tickId I) ⟨1⟩ solcFreePtrMem_size)
  have hread64 : ticMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [ticMem]
    exact twoWordHashMem_read64 (tickId I) ⟨1⟩
      (twoWordHashMem_size_96 (tickId I) ⟨1⟩ solcFreePtrMem_size)
      (twoWordHashMem_read64 (tickId I) ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64)
  have rdMload := evm_run rd6111 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 ticMem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 ticMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨26⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 (⟨26⟩ : UInt256) ticMem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst flipperTickBidAlreadyPlacedWord
    (width := 32) (op := .PUSH32) (by decide) flipperTickDecodePushBidAlreadyPlaced6138
    (by evm_ov)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 (⟨26⟩ : UInt256)
        flipperTickBidAlreadyPlacedWord ticMem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide) mem_cost
      (solcErrorStringMem3_mload64 (⟨26⟩ : UInt256) flipperTickBidAlreadyPlacedWord
        hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem flipperTickX_toAdd48 {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (h : RD flipperBytecode I g s0 ⟨6187⟩ [tickId I, ret, sel]
      (tickTicCheckedMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨6272⟩
      [tickTauWord σ I, tickNow I, ⟨6216⟩, tickId I, ret, sel]
      (tickTicCheckedMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd6190 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨k6191, C6191, rd6191raw⟩ := rd6190.sload (by native_decide) (by evm_ov)
  have rd6191 : RD flipperBytecode I g s0 ⟨6191⟩
      [flipperSlotWord ⟨5⟩ σ I, tickId I, ret, sel]
      (tickTicCheckedMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6191 C6191 := by
    simpa [flipperSlotWord] using rd6191raw
  have rd6215 := evm_run rd6191 with [
    raw push2 ⟨6216⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw timestamp (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨48⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTickDecodePushMask6204
      (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push2 ⟨6272⟩ (by native_decide) (by evm_ov)]
  have hraw :
      UInt256.land uint48Mask
        (UInt256.div (flipperSlotWord ⟨5⟩ σ I)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨48⟩)) =
        tickTauWord σ I := by
    have hdiv48 : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨48⟩ = uint48Divisor := by
      native_decide
    simpa [tickTauWord, flipperUint48Offset6Word, hdiv48, u256_land_comm]
  rw [hraw] at rd6215
  exact ⟨_, _, rd6215.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flipperTickX_add48Success {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hfit : (tickNow48 I).toNat + (tickTauWord σ I).toNat < 2 ^ 48)
    (h : RD flipperBytecode I g s0 ⟨6272⟩
      [tickTauWord σ I, tickNow I, ⟨6216⟩, tickId I, ret, sel]
      (tickTicCheckedMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨6216⟩
      [tickNow I + tickTauWord σ I, tickId I, ret, sel]
      (tickTicCheckedMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd6289 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTickDecodePushMask6276
      (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov)]
  have hltWord :
      UInt256.lt (tickEndNewWord σ I) (tickNow48 I) = ⟨0⟩ :=
    ult_zero (tickEndNewWord_ge_now48_noOverflow hfit)
  have hltRaw :
      UInt256.lt
        (UInt256.land (tickNow I + tickTauWord σ I) uint48Mask)
        (UInt256.land (tickNow I) uint48Mask) = ⟨0⟩ := by
    simpa [tickNow48, tickEndNewWord_fullTimestampAdd] using hltWord
  rw [hltRaw] at rd6289
  have rd6290 := rd6289.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6290
  have rd6299 := rd6290.push2 ⟨6299⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd6299 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]⟩

theorem flipperTickX_add48Overflow {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256}
    (hover : 2 ^ 48 ≤ (tickNow48 I).toNat + (tickTauWord σ I).toNat)
    (h : RD flipperBytecode I g s0 ⟨6272⟩
      [tickTauWord σ I, tickNow I, ⟨6216⟩, tickId I, ret, sel]
      (tickTicCheckedMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd6289 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTickDecodePushMask6276
      (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov)]
  have hltWord :
      UInt256.lt (tickEndNewWord σ I) (tickNow48 I) = ⟨1⟩ :=
    ult_one (tickEndNewWord_lt_now48_overflow hover)
  have hltRaw :
      UInt256.lt
        (UInt256.land (tickNow I + tickTauWord σ I) uint48Mask)
        (UInt256.land (tickNow I) uint48Mask) = ⟨1⟩ := by
    simpa [tickNow48, tickEndNewWord_fullTimestampAdd] using hltWord
  rw [hltRaw] at rd6289
  have rd6290 := rd6289.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6290
  have rd6295 := rd6290.push2 ⟨6299⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rd6295 (by native_decide) (by native_decide)
    (by native_decide) (by evm_ov)

theorem flipperTickX_storeEnd {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hperm : I.perm = true)
    (h : RD flipperBytecode I g s0 ⟨6216⟩
      [tickNow I + tickTauWord σ I, tickId I, ⟨323⟩, sel]
      (tickTicCheckedMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flipperBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (tickBidPackedSlot I) (tickEndStoredWord σ I))
      ByteArray.empty := by
  let mem0 := tickTicCheckedMem I
  let mem1 := wordAt0Mem (tickId I) mem0
  let mem2 := twoWordHashMem (tickId I) ⟨1⟩ mem0
  have rd6236 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mstore 0 mem1 (UInt256.ofNat 3) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 mem2 (UInt256.ofNat 3) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (tickId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (tickId I)
        (by
          dsimp [mem0, mem2, tickTicCheckedMem]
          exact twoWordHashMem_size_96 (tickId I) ⟨1⟩
            (twoWordHashMem_size_96 (tickId I) ⟨1⟩ solcFreePtrMem_size)))
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k6237, C6237, rd6237raw⟩ := rd6236.sload (by native_decide) (by evm_ov)
  have rd6237 : RD flipperBytecode I g s0 ⟨6237⟩
      [flipperSlotWord (tickBidPackedSlot I) σ I, tickBidPackedSlot I,
        tickNow I + tickTauWord σ I, ⟨323⟩, sel]
      mem2 (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6237 C6237 := by
    have hslotAdd :
        ⟨2⟩ + solcMappingSlot ⟨1⟩ (tickId I) =
          solcMappingSlot ⟨1⟩ (tickId I) + ⟨2⟩ := by
      exact u256_add_comm _ _
    simpa [mem2, tickBidPackedSlot, bidPackedSlotOfWord, bidBaseOfWord, flipperSlotWord,
      hslotAdd] using rd6237raw
  have rd6270 := evm_run rd6237 with [
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperTickDecodePushMask6237
      (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hdiv26 :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩ = uint48Divisor26 := by
    native_decide
  have hstoredRaw :
      UInt256.lor
        (UInt256.land (flipperSlotWord (tickBidPackedSlot I) σ I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩) ⟨1⟩))
        (UInt256.mul
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)
          (UInt256.land uint48Mask (tickNow I + tickTauWord σ I))) =
        tickEndStoredWord σ I := by
    calc
      UInt256.lor
        (UInt256.land (flipperSlotWord (tickBidPackedSlot I) σ I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩) ⟨1⟩))
        (UInt256.mul
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)
          (UInt256.land uint48Mask (tickNow I + tickTauWord σ I))) =
        UInt256.lor
          (UInt256.land (flipperSlotWord (tickBidPackedSlot I) σ I)
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩) ⟨1⟩))
          (UInt256.mul
            (UInt256.land (tickNow I + tickTauWord σ I) uint48Mask)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)) := by
          rw [u256_land_comm uint48Mask (tickNow I + tickTauWord σ I),
            u256_mul_comm]
      _ =
        setUint48Offset26Word (flipperSlotWord (tickBidPackedSlot I) σ I)
          (UInt256.land (tickNow I + tickTauWord σ I) uint48Mask) := by
          rw [hdiv26]
          exact Benchmarks.Dss.Flipper.setUint48Offset26RuntimeWord
            (flipperSlotWord (tickBidPackedSlot I) σ I) (tickNow I + tickTauWord σ I)
      _ = tickEndStoredWord σ I := by
          rw [tickEndNewWord_fullTimestampAdd]
  rw [hstoredRaw] at rd6270
  obtain ⟨_, _, rd6271⟩ := rd6270.sstore hperm (by native_decide) (by evm_ov)
  have rd323 := rd6271.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd324 := rd323.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd324 (by native_decide) (by evm_ov)

theorem flipperTickSourceBodyNotFinished {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hge : (tickNow I).toNat ≤ (tickEndWord (tickBidPackedSlot I) σ I).toNat) :
    let locals := tickLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tickTransition.body .reverted := by
  intro locals evm0
  have hend :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_tickEndLtTimestamp_false (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hge
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)),
          .require (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)),
          .letDecl "end_" (some uint48) (wrap48 (.binary .add now48 (.storage tauRef))),
          .require (.binary .ge (.var "end_") now48),
          .assign .storage (bidsF (.var "id") "end") (.var "end_") ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hend)
  simpa [ExecTransitionBody, tickTransition, nonpayable, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem flipperTickSourceBodyBidAlreadyPlaced {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlt : (tickEndWord (tickBidPackedSlot I) σ I).toNat < (tickNow I).toNat)
    (htic : tickTicWord (tickBidPackedSlot I) σ I ≠ ⟨0⟩) :
    let locals := tickLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tickTransition.body .reverted := by
  intro locals evm0
  have hend :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_tickEndLtTimestamp_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hlt
  have hticEval :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
          .ok (.bool false) := by
    simpa [locals, evm0] using
      evalExpr_tickTicEqZero_false (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) htic
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)),
          .require (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)),
          .letDecl "end_" (some uint48) (wrap48 (.binary .add now48 (.storage tauRef))),
          .require (.binary .ge (.var "end_") now48),
          .assign .storage (bidsF (.var "id") "end") (.var "end_") ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hend) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hticEval)
  simpa [ExecTransitionBody, tickTransition, nonpayable, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem flipperTickSourceBodyAddOverflow {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlt : (tickEndWord (tickBidPackedSlot I) σ I).toNat < (tickNow I).toNat)
    (htic : tickTicWord (tickBidPackedSlot I) σ I = ⟨0⟩)
    (hover : 2 ^ 48 ≤ (tickNow48 I).toNat + (tickTauWord σ I).toNat) :
    let locals := tickLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tickTransition.body .reverted := by
  intro locals evm0
  have hend :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_tickEndLtTimestamp_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hlt
  have hticEval :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_tickTicEqZero_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) htic
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm0
        (wrap48 (.binary .add now48 (.storage tauRef))) =
          .ok (.int (Int.ofNat (tickEndNewWord σ I).toNat)) := by
    simpa [locals, evm0] using
      evalExpr_tickEndNew (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
  have hge :
      evalExpr? config { contract := contract, locals := tickLocalsWithEnd σ I } evm0
        (.binary .ge (.var "end_") now48) = .ok (.bool false) := by
    simpa [evm0] using
      evalExpr_tickEndNewGeNow_false (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hover
  have htail :
      ExecBlock config { contract := contract, locals := tickLocalsWithEnd σ I } evm0
        [ .require (.binary .ge (.var "end_") now48),
          .assign .storage (bidsF (.var "id") "end") (.var "end_") ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hge)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)),
          .require (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)),
          .letDecl "end_" (some uint48) (wrap48 (.binary .add now48 (.storage tauRef))),
          .require (.binary .ge (.var "end_") now48),
          .assign .storage (bidsF (.var "id") "end") (.var "end_") ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hend) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hticEval) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
    simpa [locals, tickLocalsWithEnd] using htail
  simpa [ExecTransitionBody, tickTransition, nonpayable, checkedAdd48Into, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem flipperTickSourceBodySuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlt : (tickEndWord (tickBidPackedSlot I) σ I).toNat < (tickNow I).toNat)
    (htic : tickTicWord (tickBidPackedSlot I) σ I = ⟨0⟩)
    (hfit : (tickNow48 I).toNat + (tickTauWord σ I).toNat < 2 ^ 48) :
    let locals := tickLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (tickBidPackedSlot I)
      (tickEndStoredWord σ I)
    ExecTransitionBody config contract evm0 locals tickTransition.body
      (.returned { contract := contract, locals := tickLocalsWithEnd σ I } evm1 none) := by
  intro locals evm0 evm1
  have hend :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_tickEndLtTimestamp_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hlt
  have hticEval :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_tickTicEqZero_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) htic
  have hlet :
      evalExpr? config { contract := contract, locals := locals } evm0
        (wrap48 (.binary .add now48 (.storage tauRef))) =
          .ok (.int (Int.ofNat (tickEndNewWord σ I).toNat)) := by
    simpa [locals, evm0] using
      evalExpr_tickEndNew (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
  have hge :
      evalExpr? config { contract := contract, locals := tickLocalsWithEnd σ I } evm0
        (.binary .ge (.var "end_") now48) = .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_tickEndNewGeNow_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfit
  have hassign :
      assignStorageRef? config { contract := contract, locals := tickLocalsWithEnd σ I } evm0
        .storage (bidsF (.var "id") "end")
        (.int (Int.ofNat (tickEndNewWord σ I).toNat)) =
          .ok ({ contract := contract, locals := tickLocalsWithEnd σ I }, evm1) := by
    simpa [evm1, evm0, initState, tickEndStoredWord, flipperSlotWord, Solm.EVM.storageLoad] using
      assign_tickEndStorage evm0 σ I
  have htail :
      ExecBlock config { contract := contract, locals := tickLocalsWithEnd σ I } evm0
        [ .require (.binary .ge (.var "end_") now48),
          .assign .storage (bidsF (.var "id") "end") (.var "end_") ]
        (.ok { contract := contract, locals := tickLocalsWithEnd σ I } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue hge) ?_
    exact ExecBlock.consNormal (ExecStmt.assign (evalExpr_tickEndVarWithEnd (evm := evm0)
      (σ := σ) (I := I)) hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .lt (.storage (bidsF (.var "id") "end")) (.env .timestamp)),
          .require (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0)),
          .letDecl "end_" (some uint48) (wrap48 (.binary .add now48 (.storage tauRef))),
          .require (.binary .ge (.var "end_") now48),
          .assign .storage (bidsF (.var "id") "end") (.var "end_") ]
        (.ok { contract := contract, locals := tickLocalsWithEnd σ I } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hend) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hticEval) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hlet) ?_
    simpa [locals, tickLocalsWithEnd] using htail
  simpa [ExecTransitionBody, tickTransition, nonpayable, checkedAdd48Into, locals, evm0,
    evm1] using ExecFuncBody.execBlockOK hblock

theorem flipperTickBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 14))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 14) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some tickTransition :=
    flipperDispatchTick hsel
  have hreach := flipperReachTickBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · let locals := tickLocals I
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hdecode := flipperDecode_tick_ok (I := I) hsz36
    obtain ⟨_, _, hdecoded⟩ := flipperTickX_decoded (g := Sat256.ofUInt256 g)
      hsz36 hsize hreach
    have hpacked :
        flipperSlotWord (tickBidPackedSlot I) σ_evm I =
          flipperSlotWord (tickBidPackedSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (tickBidPackedSlot I) ⟨0⟩
    have htauSlot : flipperSlotWord ⟨5⟩ σ_evm I = flipperSlotWord ⟨5⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
    have hendEq :
        tickEndWord (tickBidPackedSlot I) σ_evm I =
          tickEndWord (tickBidPackedSlot I) σ_solm I := by
      simp [tickEndWord, flipperUint48Offset26Word, hpacked]
    have hticEq :
        tickTicWord (tickBidPackedSlot I) σ_evm I =
          tickTicWord (tickBidPackedSlot I) σ_solm I := by
      simp [tickTicWord, flipperUint48Offset20Word, hpacked]
    have htauEq : tickTauWord σ_evm I = tickTauWord σ_solm I := by
      simp [tickTauWord, flipperUint48Offset6Word, htauSlot]
    have hendNewEq : tickEndNewWord σ_evm I = tickEndNewWord σ_solm I := by
      simp [tickEndNewWord, htauEq]
    have hstoredEq : tickEndStoredWord σ_evm I = tickEndStoredWord σ_solm I := by
      simp [tickEndStoredWord, hpacked, hendNewEq]
    by_cases hltEvm :
        (tickEndWord (tickBidPackedSlot I) σ_evm I).toNat < (tickNow I).toNat
    · have hltSolm :
          (tickEndWord (tickBidPackedSlot I) σ_solm I).toNat < (tickNow I).toNat := by
        simpa [← hendEq] using hltEvm
      obtain ⟨_, _, rd6072⟩ := flipperTickX_endCheckOk hltEvm hdecoded
      by_cases hticEvm : tickTicWord (tickBidPackedSlot I) σ_evm I = ⟨0⟩
      · have hticSolm : tickTicWord (tickBidPackedSlot I) σ_solm I = ⟨0⟩ := by
          simpa [← hticEq] using hticEvm
        obtain ⟨_, _, rd6187⟩ := flipperTickX_ticCheckOk hticEvm rd6072
        obtain ⟨_, _, rd6272⟩ := flipperTickX_toAdd48 rd6187
        by_cases hfitEvm :
            (tickNow48 I).toNat + (tickTauWord σ_evm I).toNat < 2 ^ 48
        · have hfitSolm :
              (tickNow48 I).toNat + (tickTauWord σ_solm I).toNat < 2 ^ 48 := by
            simpa [← htauEq] using hfitEvm
          obtain ⟨_, _, rd6216⟩ := flipperTickX_add48Success hfitEvm rd6272
          let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (tickBidPackedSlot I)
            (tickEndStoredWord σ_solm I)
          have hbody :
              ExecTransitionBody config contract evm0 locals tickTransition.body
                (.returned { contract := contract, locals := tickLocalsWithEnd σ_solm I }
                  evm1 none) := by
            simpa [evm0, evm1, locals] using
              (flipperTickSourceBodySuccess (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hltSolm hticSolm hfitSolm)
          have hret := flipperTickX_storeEnd hperm rd6216
          exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
            (by simp [evm1, evm0, initState, storageStore_createdAccounts])
            (by
              simpa [evm1, evm0, initState, storageStore_accountMap, hstoredEq] using
                accountMapEquiv_sstoreAccountMap I.codeOwner (tickBidPackedSlot I)
                  (tickEndStoredWord σ_evm I) hAccounts)
            (by
              rw [show tickTransition.returnType = [] by rfl]
              exact returnEquiv.fallthrough rfl (by rfl) (by native_decide))
        · have hoverEvm :
              2 ^ 48 ≤ (tickNow48 I).toNat + (tickTauWord σ_evm I).toNat := by
            omega
          have hoverSolm :
              2 ^ 48 ≤ (tickNow48 I).toNat + (tickTauWord σ_solm I).toNat := by
            simpa [← htauEq] using hoverEvm
          have hbody :
              ExecTransitionBody config contract evm0 locals tickTransition.body .reverted := by
            simpa [evm0, locals] using
              (flipperTickSourceBodyAddOverflow (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hltSolm hticSolm hoverSolm)
          exact (flipperTickX_add48Overflow hoverEvm rd6272)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hticSolm : tickTicWord (tickBidPackedSlot I) σ_solm I ≠ ⟨0⟩ := by
          intro hbad
          exact hticEvm (by simpa [hticEq] using hbad)
        have hbody :
            ExecTransitionBody config contract evm0 locals tickTransition.body .reverted := by
          simpa [evm0, locals] using
            (flipperTickSourceBodyBidAlreadyPlaced (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hltSolm hticSolm)
        exact (flipperTickX_bidAlreadyPlaced hticEvm rd6072)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hgeEvm :
          (tickNow I).toNat ≤ (tickEndWord (tickBidPackedSlot I) σ_evm I).toNat := by
        omega
      have hgeSolm :
          (tickNow I).toNat ≤ (tickEndWord (tickBidPackedSlot I) σ_solm I).toNat := by
        simpa [← hendEq] using hgeEvm
      have hbody :
          ExecTransitionBody config contract evm0 locals tickTransition.body .reverted := by
        simpa [evm0, locals] using
          (flipperTickSourceBodyNotFinished (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hgeSolm)
      exact (flipperTickX_notFinished hgeEvm hdecoded)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hshort : I.calldata.size < 36 := by
      omega
    exact (flipperTickX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hdispatch
        (flipperDecode_tick_none_short hsz4 hshort)

end Benchmarks.Dss.Flipper
