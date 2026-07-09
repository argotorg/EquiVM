import Benchmarks.CompoundIII.CometRewards.RewardConfig
import Benchmarks.CompoundIII.CometRewards.RewardsClaimed
import Benchmarks.CompoundIII.CometRewards.SetRewardConfigWithMultiplier
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.CompoundIII.CometRewards

/-! ## `getRewardOwed(address,address)` ABI and storage setup -/

abbrev getRewardOwedCometWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev getRewardOwedAccountWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev getRewardOwedCometValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (getRewardOwedCometWord I).toNat)

abbrev getRewardOwedAccountValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (getRewardOwedAccountWord I).toNat)

abbrev getRewardOwedStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "comet" (getRewardOwedCometValue I)).insert "account"
    (getRewardOwedAccountValue I)

abbrev getRewardOwedFrame (evm : EVM.State) (I : ExecutionEnv) : Frame :=
  { contract := contract,
    locals := (getRewardOwedStore I).insert "__calldata" (.bytes evm.executionEnv.calldata) }

def getRewardOwedRewardConfigSlotOf (I : ExecutionEnv) : UInt256 :=
  rewardConfigSlot (.address (AccountAddress.ofNat (getRewardOwedCometWord I).toNat))

def getRewardOwedRewardsClaimedSlotOf (I : ExecutionEnv) : UInt256 :=
  rewardsClaimedSlot
    (.address (AccountAddress.ofNat (getRewardOwedCometWord I).toNat))
    (.address (AccountAddress.ofNat (getRewardOwedAccountWord I).toNat))

def getRewardOwedRewardConfigSlot0Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (getRewardOwedRewardConfigSlotOf I) ⟨0⟩)

def getRewardOwedMultiplierWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (getRewardOwedRewardConfigSlotOf I + ⟨1⟩) ⟨0⟩)

def getRewardOwedClaimedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (getRewardOwedRewardsClaimedSlotOf I) ⟨0⟩)

abbrev getRewardOwedTokenWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  rewardConfigTokenFromSlot0 (getRewardOwedRewardConfigSlot0Word σ I)

abbrev getRewardOwedRescaleWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  rewardConfigRescaleFromSlot0 (getRewardOwedRewardConfigSlot0Word σ I)

abbrev getRewardOwedShouldUpscaleRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  rewardConfigShouldUpscaleRawFromSlot0 (getRewardOwedRewardConfigSlot0Word σ I)

abbrev getRewardOwedShouldUpscaleWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  rewardConfigShouldUpscaleFromSlot0 (getRewardOwedRewardConfigSlot0Word σ I)

abbrev getRewardOwedSlot0Load (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (getRewardOwedRewardConfigSlotOf I)

abbrev getRewardOwedMultiplierLoad (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
    (getRewardOwedRewardConfigSlotOf I + ⟨1⟩)

abbrev getRewardOwedClaimedLoad (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (getRewardOwedRewardsClaimedSlotOf I)

abbrev getRewardOwedTokenValueFromSlot0 (slot0 : UInt256) : Value :=
  .address (AccountAddress.ofNat (rewardConfigTokenFromSlot0 slot0).toNat)

abbrev getRewardOwedRescaleValueFromSlot0 (slot0 : UInt256) : Value :=
  .int (Int.ofNat (rewardConfigRescaleFromSlot0 slot0).toNat)

abbrev getRewardOwedShouldUpscaleValueFromSlot0 (slot0 : UInt256) : Value :=
  wordToElem .bool (rewardConfigShouldUpscaleRawFromSlot0 slot0)

abbrev getRewardOwedMultiplierValue (multiplier : UInt256) : Value :=
  .int (Int.ofNat multiplier.toNat)

abbrev getRewardOwedBaseLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (getRewardOwedStore I).insert "__calldata" (.bytes evm.executionEnv.calldata)

abbrev getRewardOwedAfterTokenLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (getRewardOwedBaseLocals evm I).insert "token"
    (getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I))

abbrev getRewardOwedAfterRescaleLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (getRewardOwedAfterTokenLocals evm I).insert "rescaleFactor"
    (getRewardOwedRescaleValueFromSlot0 (getRewardOwedSlot0Load evm I))

abbrev getRewardOwedAfterShouldLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (getRewardOwedAfterRescaleLocals evm I).insert "shouldUpscale"
    (getRewardOwedShouldUpscaleValueFromSlot0 (getRewardOwedSlot0Load evm I))

abbrev getRewardOwedConfigLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (getRewardOwedAfterShouldLocals evm I).insert "multiplier"
    (getRewardOwedMultiplierValue (getRewardOwedMultiplierLoad evm I))

abbrev getRewardOwedAfterAccrueLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (getRewardOwedConfigLocals evm I).insert "_accrued" .unit

abbrev getRewardOwedAfterClaimedLocals
    (evm evmAcc : EVM.State) (I : ExecutionEnv) : Store :=
  (getRewardOwedAfterAccrueLocals evm I).insert "claimed"
    (.int (Int.ofNat (getRewardOwedClaimedLoad evmAcc I).toNat))

abbrev getRewardOwedAfterInternalLocals
    (evm evmAcc : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) : Store :=
  (getRewardOwedAfterClaimedLocals evm evmAcc I).insert "accrued"
    (.int (Int.ofNat accruedNat))

abbrev getRewardOwedOwedNat (evmAcc : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    ℕ :=
  if (getRewardOwedClaimedLoad evmAcc I).toNat < accruedNat then
    accruedNat - (getRewardOwedClaimedLoad evmAcc I).toNat
  else
    0

abbrev getRewardOwedAfterOwedLocals
    (evm evmAcc : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) : Store :=
  (getRewardOwedAfterInternalLocals evm evmAcc I accruedNat).insert "owed"
    (.int (Int.ofNat (getRewardOwedOwedNat evmAcc I accruedNat)))

abbrev getRewardOwedArgs (I : ExecutionEnv) : List Value :=
  [getRewardOwedCometValue I, getRewardOwedAccountValue I]

abbrev getRewardOwedAccrueAccountArgs (I : ExecutionEnv) : List Value :=
  [getRewardOwedAccountValue I]

abbrev getRewardOwedCometTarget (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (getRewardOwedCometWord I).toNat

abbrev getRewardOwedAccrueAccountCallPc : UInt256 := ⟨2450⟩

abbrev getRewardOwedAccrueAccountCallSize : UInt256 := ⟨36⟩

abbrev getRewardOwedBaseTrackingCallPc : UInt256 := ⟨3723⟩

abbrev getRewardOwedBaseTrackingCallSize : UInt256 := ⟨36⟩

abbrev getRewardAccruedArgs (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    List Value :=
  [ getRewardOwedCometValue I,
    getRewardOwedAccountValue I,
    .int (Int.ofNat (rewardConfigRescaleFromSlot0 slot0).toNat),
    wordToElem .bool (rewardConfigShouldUpscaleRawFromSlot0 slot0),
    .int (Int.ofNat multiplier.toNat) ]

abbrev getRewardAccruedStore (I : ExecutionEnv) (slot0 multiplier : UInt256) : Store :=
  (((((∅ : Store).insert "multiplier" (.int (Int.ofNat multiplier.toNat))).insert
    "shouldUpscale" (wordToElem .bool (rewardConfigShouldUpscaleRawFromSlot0 slot0))).insert
    "rescaleFactor" (.int (Int.ofNat (rewardConfigRescaleFromSlot0 slot0).toNat))).insert
    "account" (getRewardOwedAccountValue I)).insert "comet" (getRewardOwedCometValue I)

abbrev getRewardAccruedBaseTrackingArgs (I : ExecutionEnv) : List Value :=
  [getRewardOwedAccountValue I]

abbrev getRewardAccruedAfterBaseLocals
    (I : ExecutionEnv) (slot0 multiplier accrued : UInt256) : Store :=
  (getRewardAccruedStore I slot0 multiplier).insert "accrued"
    (.int (Int.ofNat accrued.toNat))

abbrev getRewardAccruedAfterBaseFrame
    (I : ExecutionEnv) (slot0 multiplier accrued : UInt256) : Frame :=
  { contract := contract, locals := getRewardAccruedAfterBaseLocals I slot0 multiplier accrued }

abbrev getRewardAccruedUpscaledNat (slot0 accrued : UInt256) : ℕ :=
  accrued.toNat * (rewardConfigRescaleFromSlot0 slot0).toNat

abbrev getRewardAccruedDownscaledNat (slot0 accrued : UInt256) : ℕ :=
  accrued.toNat / (rewardConfigRescaleFromSlot0 slot0).toNat

abbrev getRewardAccruedAfterBranchLocals
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accruedNat : ℕ) : Store :=
  (getRewardAccruedStore I slot0 multiplier).insert "accrued"
    (.int (Int.ofNat accruedNat))

abbrev getRewardAccruedAfterBranchFrame
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accruedNat : ℕ) : Frame :=
  { contract := contract, locals := getRewardAccruedAfterBranchLocals I slot0 multiplier accruedNat }

abbrev getRewardAccruedScaledNat (multiplier : UInt256) (accruedNat : ℕ) : ℕ :=
  accruedNat * multiplier.toNat

abbrev getRewardAccruedAfterScaledLocals
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accruedNat : ℕ) : Store :=
  (getRewardAccruedAfterBranchLocals I slot0 multiplier accruedNat).insert "scaled"
    (.int (Int.ofNat (getRewardAccruedScaledNat multiplier accruedNat)))

abbrev getRewardAccruedAfterScaledFrame
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accruedNat : ℕ) : Frame :=
  { contract := contract, locals := getRewardAccruedAfterScaledLocals I slot0 multiplier accruedNat }

abbrev getRewardAccruedReturnNat (multiplier : UInt256) (accruedNat : ℕ) : ℕ :=
  getRewardAccruedScaledNat multiplier accruedNat / factorScale.toNat

theorem getRewardAccruedUpscaledNat_lt_size_of_base64 {slot0 accrued : UInt256}
    (hacc : accrued.toNat < EVM.twoPow 64) :
    getRewardAccruedUpscaledNat slot0 accrued < UInt256.size := by
  have haccLt : accrued.toNat < 2 ^ 64 := by
    simpa [EVM.twoPow] using hacc
  have hresLt : (rewardConfigRescaleFromSlot0 slot0).toNat < 2 ^ 64 := by
    simpa [rewardConfigRescaleFromSlot0, EVM.twoPow] using
      rewardConfigRescaleWord_lt slot0
  have haccLe : accrued.toNat ≤ 2 ^ 64 - 1 := by omega
  have hresLe : (rewardConfigRescaleFromSlot0 slot0).toNat ≤ 2 ^ 64 - 1 := by omega
  have hmul :
      accrued.toNat * (rewardConfigRescaleFromSlot0 slot0).toNat ≤
        (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul haccLe hresLe
  have hbound : (2 ^ 64 - 1) * (2 ^ 64 - 1) < UInt256.size := by
    norm_num [UInt256.size]
  exact lt_of_le_of_lt hmul hbound

theorem u256_land_zero_right (a : UInt256) : UInt256.land a ⟨0⟩ = ⟨0⟩ := by
  apply u256_inj
  rw [u256_land_toNat]
  change Nat.land a.toNat 0 % UInt256.size = 0
  have hland : Nat.land a.toNat 0 = 0 := by
    exact Nat.and_zero a.toNat
  rw [hland]
  rfl

theorem u256_mul_eq_ofNat_of_lt (a b : UInt256)
    (h : a.toNat * b.toNat < UInt256.size) :
    UInt256.mul a b = UInt256.ofNat (a.toNat * b.toNat) := by
  apply u256_inj
  rw [u256_mul_toNat, UInt256.toNat_ofNat_of_lt h, Nat.mod_eq_of_lt h]

theorem checkedMulOverflowFlag_zero (a b : UInt256)
    (h : a.toNat * b.toNat < UInt256.size) :
    UInt256.land
        (UInt256.gt b (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) a))
        (UInt256.isZero (UInt256.isZero a)) = ⟨0⟩ := by
  by_cases ha0 : a = ⟨0⟩
  · have hiz : UInt256.isZero (UInt256.isZero a) = ⟨0⟩ := by
      rw [ha0]
      native_decide
    rw [hiz]
    exact u256_land_zero_right _
  · have hmax : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
      unfold UInt256.lnot
      decide
    have haNatNZ : a.toNat ≠ 0 := by
      intro hz
      exact ha0 (uint256_toNat_eq_zero hz)
    have haPos : 0 < a.toNat := Nat.pos_of_ne_zero haNatNZ
    have hmulLe : b.toNat * a.toNat ≤ UInt256.size - 1 := by
      rw [Nat.mul_comm]
      omega
    have hdivLe :
        b.toNat ≤ (UInt256.size - 1) / a.toNat :=
      (Nat.le_div_iff_mul_le haPos).2 hmulLe
    have hgt :
        UInt256.gt b (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) a) = ⟨0⟩ := by
      apply ugt_zero
      rw [udiv_toNat, hmax]
      exact hdivLe
    rw [hgt, u256_land_comm]
    exact u256_land_zero_right _

theorem checkedMulOverflowFlag_one (a b : UInt256)
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    UInt256.land (UInt256.isZero (UInt256.isZero a))
        (UInt256.gt b (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) a)) = ⟨1⟩ := by
  have hmax : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot
    decide
  have haNZ : a ≠ ⟨0⟩ := by
    intro hzero
    have hto := congrArg UInt256.toNat hzero
    rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl] at hto
    have hprod : a.toNat * b.toNat = 0 := by
      rw [hto]
      exact Nat.zero_mul b.toNat
    have hpos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have haNatNZ : a.toNat ≠ 0 := by
    intro hz
    exact haNZ (uint256_toNat_eq_zero hz)
  have haPos : 0 < a.toNat := Nat.pos_of_ne_zero haNatNZ
  have hgt :
      UInt256.gt b (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) a) = ⟨1⟩ := by
    apply ugt_one
    rw [udiv_toNat, hmax]
    have hltDiv : (UInt256.size - 1) / a.toNat < b.toNat := by
      rw [Nat.div_lt_iff_lt_mul haPos]
      rw [Nat.mul_comm]
      have hpos : 0 < UInt256.size := by norm_num [UInt256.size]
      omega
    exact hltDiv
  have hisz : UInt256.isZero (UInt256.isZero a) = ⟨1⟩ := by
    rw [isZero_eq_zero_of_ne haNZ]
    native_decide
  rw [hisz, hgt]
  native_decide

theorem rewardConfigShouldUpscaleFromSlot0_eq_one_of_raw_ne_zero {slot0 : UInt256}
    (h : rewardConfigShouldUpscaleRawFromSlot0 slot0 ≠ ⟨0⟩) :
    rewardConfigShouldUpscaleFromSlot0 slot0 = ⟨1⟩ := by
  unfold rewardConfigShouldUpscaleFromSlot0
  rw [isZero_eq_zero_of_ne h]
  native_decide

theorem rewardConfigShouldUpscaleFromSlot0_eq_zero_of_raw_zero {slot0 : UInt256}
    (h : rewardConfigShouldUpscaleRawFromSlot0 slot0 = ⟨0⟩) :
    rewardConfigShouldUpscaleFromSlot0 slot0 = ⟨0⟩ := by
  unfold rewardConfigShouldUpscaleFromSlot0
  rw [h]
  native_decide

theorem u256_div_factorScale_ofNat {n : ℕ} (hn : n < UInt256.size) :
    UInt256.div (UInt256.ofNat n) (⟨1000000000000000000⟩ : UInt256) =
      UInt256.ofNat (n / factorScale.toNat) := by
  have hfactor :
      (⟨1000000000000000000⟩ : UInt256).toNat = factorScale.toNat := by
    native_decide
  have hretLt : n / factorScale.toNat < UInt256.size := by
    exact lt_of_le_of_lt (Nat.div_le_self n factorScale.toNat) hn
  apply u256_inj
  rw [udiv_toNat, UInt256.toNat_ofNat_of_lt hn, hfactor,
    UInt256.toNat_ofNat_of_lt hretLt]

theorem u256_div_eq_ofNat (a b : UInt256) :
    UInt256.div a b = UInt256.ofNat (a.toNat / b.toNat) := by
  have hlt : a.toNat / b.toNat < UInt256.size :=
    lt_of_le_of_lt (Nat.div_le_self a.toNat b.toNat) a.val.isLt
  apply u256_inj
  rw [udiv_toNat, UInt256.toNat_ofNat_of_lt hlt]

abbrev getRewardAccruedAfterAssignedLocals
    (I : ExecutionEnv) (slot0 multiplier oldAccrued : UInt256) (accruedNat : ℕ) :
    Store :=
  (getRewardAccruedAfterBaseLocals I slot0 multiplier oldAccrued).insert "accrued"
    (.int (Int.ofNat accruedNat))

abbrev getRewardAccruedAfterAssignedFrame
    (I : ExecutionEnv) (slot0 multiplier oldAccrued : UInt256) (accruedNat : ℕ) :
    Frame :=
  { contract := contract,
    locals := getRewardAccruedAfterAssignedLocals I slot0 multiplier oldAccrued accruedNat }

abbrev getRewardAccruedAfterAssignedScaledLocals
    (I : ExecutionEnv) (slot0 multiplier oldAccrued : UInt256) (accruedNat : ℕ) :
    Store :=
  (getRewardAccruedAfterAssignedLocals I slot0 multiplier oldAccrued accruedNat).insert
    "scaled" (.int (Int.ofNat (getRewardAccruedScaledNat multiplier accruedNat)))

abbrev getRewardAccruedAfterAssignedScaledFrame
    (I : ExecutionEnv) (slot0 multiplier oldAccrued : UInt256) (accruedNat : ℕ) :
    Frame :=
  { contract := contract,
    locals := getRewardAccruedAfterAssignedScaledLocals I slot0 multiplier oldAccrued accruedNat }

theorem getRewardOwedStore_comet (I : ExecutionEnv) :
    (getRewardOwedStore I).get? "comet" = some (getRewardOwedCometValue I) := by
  rw [getRewardOwedStore, store_get_ne _ _ (by decide), store_get_self]

theorem getRewardOwedStore_account (I : ExecutionEnv) :
    (getRewardOwedStore I).get? "account" = some (getRewardOwedAccountValue I) := by
  rw [getRewardOwedStore, store_get_self]

theorem getRewardOwedFrame_comet (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedFrame evm I).locals.get? "comet" = some (getRewardOwedCometValue I) := by
  rw [getRewardOwedFrame]
  rw [store_get_ne _ _ (by decide), getRewardOwedStore_comet]

theorem getRewardOwedFrame_account (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedFrame evm I).locals.get? "account" =
      some (getRewardOwedAccountValue I) := by
  rw [getRewardOwedFrame]
  rw [store_get_ne _ _ (by decide), getRewardOwedStore_account]

theorem getRewardOwedFrame_no_rewardConfig (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedFrame evm I).locals.get? "rewardConfig" = none := by
  rw [getRewardOwedFrame]
  rw [store_get_ne _ _ (by decide)]
  rw [getRewardOwedStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem getRewardOwedFrame_no_rewardsClaimed (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedFrame evm I).locals.get? "rewardsClaimed" = none := by
  rw [getRewardOwedFrame]
  rw [store_get_ne _ _ (by decide)]
  rw [getRewardOwedStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_getRewardOwed_comet_of {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hcomet : locals.get? "comet" = some (getRewardOwedCometValue I)) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "comet") =
      .ok (getRewardOwedCometValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [hcomet]

theorem evalExpr_getRewardOwed_account_of {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (haccount : locals.get? "account" = some (getRewardOwedAccountValue I)) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "account") =
      .ok (getRewardOwedAccountValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [haccount]

theorem evalExprs_getRewardOwed_args_of {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hcomet : locals.get? "comet" = some (getRewardOwedCometValue I))
    (haccount : locals.get? "account" = some (getRewardOwedAccountValue I)) :
    evalExprs? config { contract := contract, locals := locals } evm
      [.var "comet", .var "account"] = .ok (getRewardOwedArgs I) := by
  simp only [getRewardOwedArgs, evalExprs?, evalExpr_getRewardOwed_comet_of evm I hcomet,
    evalExpr_getRewardOwed_account_of evm I haccount, EvalResult.bind, bind]
  rfl

theorem evalExprs_getRewardOwed_accrueAccountArgs_of {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (haccount : locals.get? "account" = some (getRewardOwedAccountValue I)) :
    evalExprs? config { contract := contract, locals := locals } evm [.var "account"] =
      .ok (getRewardOwedAccrueAccountArgs I) := by
  simp only [getRewardOwedAccrueAccountArgs, evalExprs?,
    evalExpr_getRewardOwed_account_of evm I haccount, EvalResult.bind, bind]
  rfl

theorem evalStorageRef_getRewardOwed_rewardConfig_field_of {locals : Store}
    (evm : EVM.State) (I : ExecutionEnv) (field : Ident)
    (hcomet : locals.get? "comet" = some (getRewardOwedCometValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (rewardConfigF (.var "comet") field) =
        .ok { base := "rewardConfig",
              steps := [.mindex (.address (AccountAddress.ofNat
                          (getRewardOwedCometWord I).toNat)), .field field] } := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, rewardConfigF,
    evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
    Std.HashMap.get?_eq_getElem?]
  rw [← Std.HashMap.get?_eq_getElem?, hcomet]

theorem evalExpr_getRewardOwed_token_of {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hcomet : locals.get? "comet" = some (getRewardOwedCometValue I))
    (hbase : locals.get? "rewardConfig" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (rewardConfigF (.var "comet") "token")) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (getRewardOwedRewardConfigSlotOf I))
            solcAddrMask).toNat)) := by
  have her := evalStorageRef_getRewardOwed_rewardConfig_field_of evm I "token" hcomet
  have hty : storageTypeAt? contract.storage
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (getRewardOwedCometWord I).toNat)),
                  .field "token"] } =
      some (.elem .address) := by
    simp [storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (getRewardOwedCometWord I).toNat)),
                  .field "token"] } =
      fun _ => some (fieldLoc (slotAdd (getRewardOwedRewardConfigSlotOf I) 0) 0 20
        (by decide) .address) := by
    rfl
  rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  rw [slotAdd_zero]
  exact cometRewardsStorageLocLoad_address_offset0 evm (getRewardOwedRewardConfigSlotOf I)

theorem evalExpr_getRewardOwed_rescale_of {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hcomet : locals.get? "comet" = some (getRewardOwedCometValue I))
    (hbase : locals.get? "rewardConfig" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (rewardConfigF (.var "comet") "rescaleFactor")) =
        .ok (.int (Int.ofNat
          (UInt256.land
            (UInt256.shiftRight
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                (getRewardOwedRewardConfigSlotOf I))
              ⟨160⟩)
            (UInt256.ofNat (2 ^ 64 - 1))).toNat)) := by
  have her := evalStorageRef_getRewardOwed_rewardConfig_field_of evm I "rescaleFactor" hcomet
  have hty : storageTypeAt? contract.storage
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (getRewardOwedCometWord I).toNat)),
                  .field "rescaleFactor"] } =
      some (.elem (.int uint64Int)) := by
    simp [storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (getRewardOwedCometWord I).toNat)),
                  .field "rescaleFactor"] } =
      fun _ => some (fieldLoc (slotAdd (getRewardOwedRewardConfigSlotOf I) 0) 20 8
        (by decide) (.int uint64Int)) := by
    rfl
  rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  rw [slotAdd_zero]
  exact cometRewardsStorageLocLoad_uint64_offset20 evm (getRewardOwedRewardConfigSlotOf I)

theorem evalExpr_getRewardOwed_shouldUpscale_of {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hcomet : locals.get? "comet" = some (getRewardOwedCometValue I))
    (hbase : locals.get? "rewardConfig" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (rewardConfigF (.var "comet") "shouldUpscale")) =
        .ok (wordToElem .bool
          (UInt256.land
            (UInt256.shiftRight
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                (getRewardOwedRewardConfigSlotOf I))
              ⟨224⟩)
            ⟨255⟩)) := by
  have her := evalStorageRef_getRewardOwed_rewardConfig_field_of evm I "shouldUpscale" hcomet
  have hty : storageTypeAt? contract.storage
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (getRewardOwedCometWord I).toNat)),
                  .field "shouldUpscale"] } =
      some (.elem .bool) := by
    simp [storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (getRewardOwedCometWord I).toNat)),
                  .field "shouldUpscale"] } =
      fun _ => some (fieldLoc (slotAdd (getRewardOwedRewardConfigSlotOf I) 0) 28 1
        (by decide) .bool) := by
    rfl
  rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  rw [slotAdd_zero]
  exact cometRewardsStorageLocLoad_bool_offset28 evm (getRewardOwedRewardConfigSlotOf I)

theorem evalExpr_getRewardOwed_multiplier_of {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hcomet : locals.get? "comet" = some (getRewardOwedCometValue I))
    (hbase : locals.get? "rewardConfig" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (rewardConfigF (.var "comet") "multiplier")) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (getRewardOwedRewardConfigSlotOf I + ⟨1⟩)).toNat)) := by
  have her := evalStorageRef_getRewardOwed_rewardConfig_field_of evm I "multiplier" hcomet
  have hty : storageTypeAt? contract.storage
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (getRewardOwedCometWord I).toNat)),
                  .field "multiplier"] } =
      some (.elem (.int uint256Int)) := by
    simp [storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (getRewardOwedCometWord I).toNat)),
                  .field "multiplier"] } =
      fun _ => some (fieldLoc (slotAdd (getRewardOwedRewardConfigSlotOf I) 1) 0 32
        (by decide) (.int uint256Int)) := by
    rfl
  rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  rw [slotAdd_one]
  rw [cometRewardsStorageLocLoad_uint256]

theorem evalStorageRef_getRewardOwed_rewardsClaimed_of {locals : Store}
    (evm : EVM.State) (I : ExecutionEnv)
    (hcomet : locals.get? "comet" = some (getRewardOwedCometValue I))
    (haccount : locals.get? "account" = some (getRewardOwedAccountValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (rewardsClaimedRef (.var "comet") (.var "account")) =
      .ok { base := "rewardsClaimed",
            steps := [.mindex (.address (AccountAddress.ofNat
                        (getRewardOwedCometWord I).toNat)),
                      .mindex (.address (AccountAddress.ofNat
                        (getRewardOwedAccountWord I).toNat))] } := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, rewardsClaimedRef,
    evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
    Std.HashMap.get?_eq_getElem?]
  rw [← Std.HashMap.get?_eq_getElem?, hcomet]
  rw [← Std.HashMap.get?_eq_getElem?, haccount]

theorem evalExpr_getRewardOwed_claimed_of {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hcomet : locals.get? "comet" = some (getRewardOwedCometValue I))
    (haccount : locals.get? "account" = some (getRewardOwedAccountValue I))
    (hbase : locals.get? "rewardsClaimed" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (rewardsClaimedRef (.var "comet") (.var "account"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (getRewardOwedRewardsClaimedSlotOf I)).toNat)) := by
  have her := evalStorageRef_getRewardOwed_rewardsClaimed_of evm I hcomet haccount
  have hty : storageTypeAt? contract.storage
      { base := "rewardsClaimed",
        steps := [.mindex (.address (AccountAddress.ofNat (getRewardOwedCometWord I).toNat)),
                  .mindex (.address (AccountAddress.ofNat
                    (getRewardOwedAccountWord I).toNat))] } =
      some (.elem (.int uint256Int)) := by
    simp [storageTypeAt?, contract, storageDecls, List.find?, List.foldlM, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "rewardsClaimed",
        steps := [.mindex (.address (AccountAddress.ofNat (getRewardOwedCometWord I).toNat)),
                  .mindex (.address (AccountAddress.ofNat
                    (getRewardOwedAccountWord I).toNat))] } =
      fun _ => some (fieldLoc (getRewardOwedRewardsClaimedSlotOf I) 0 32
        (by decide) (.int uint256Int)) := by
    rfl
  rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  exact cometRewardsStorageLocLoad_uint256 evm (getRewardOwedRewardsClaimedSlotOf I)

theorem getRewardOwedAccountAddress_ofNat_masked_ne_zero_of_ne (w : UInt256)
    (h : UInt256.land w solcAddrMask ≠ ⟨0⟩) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat ≠ AccountAddress.ofNat 0 := by
  intro haddr
  apply h
  apply u256_inj
  have hval := congrArg (fun a : AccountAddress => a.val) haddr
  have hcanon := solcAddrMask_result_canonical w
  have hmod :
      (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
        (UInt256.land w solcAddrMask).toNat := by
    exact Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)
  simp [AccountAddress.ofNat, hmod] at hval
  simpa [UInt256.toNat] using hval

theorem evalExpr_getRewardOwed_zeroAddr_of {locals : Store} (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals } evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption,
    pure, bind]

theorem evalExpr_getRewardOwed_token_ne_zero_true_of {locals : Store}
    (evm : EVM.State) (slot0 : UInt256)
    (htoken :
      locals.get? "token" = some (getRewardOwedTokenValueFromSlot0 slot0))
    (hnz : rewardConfigTokenFromSlot0 slot0 ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.var "token") zeroAddr) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.bind, EvalResult.ofOption, htoken,
    evalExpr_getRewardOwed_zeroAddr_of, bind, evalBinaryOp?]
  have haddr := getRewardOwedAccountAddress_ofNat_masked_ne_zero_of_ne slot0 hnz
  rw [show ((getRewardOwedTokenValueFromSlot0 slot0 : Value) ==
        .address (AccountAddress.ofNat 0)) = false by
    simp [getRewardOwedTokenValueFromSlot0, rewardConfigTokenFromSlot0, BEq.beq, haddr]]
  rfl

theorem evalExpr_getRewardOwed_token_ne_zero_false_of {locals : Store}
    (evm : EVM.State) (slot0 : UInt256)
    (htoken :
      locals.get? "token" = some (getRewardOwedTokenValueFromSlot0 slot0))
    (hz : rewardConfigTokenFromSlot0 slot0 = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.var "token") zeroAddr) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, EvalResult.ofOption, htoken,
    evalExpr_getRewardOwed_zeroAddr_of, bind, evalBinaryOp?]
  simp [getRewardOwedTokenValueFromSlot0, rewardConfigTokenFromSlot0, BEq.beq, hz]

theorem getRewardOwedAfterTokenLocals_comet (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedAfterTokenLocals evm I).get? "comet" =
      some (getRewardOwedCometValue I) := by
  rw [getRewardOwedAfterTokenLocals, getRewardOwedBaseLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), getRewardOwedStore_comet]

theorem getRewardOwedAfterTokenLocals_no_rewardConfig (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedAfterTokenLocals evm I).get? "rewardConfig" = none := by
  rw [getRewardOwedAfterTokenLocals, getRewardOwedBaseLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  rw [getRewardOwedStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem getRewardOwedAfterRescaleLocals_comet (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedAfterRescaleLocals evm I).get? "comet" =
      some (getRewardOwedCometValue I) := by
  rw [getRewardOwedAfterRescaleLocals, store_get_ne _ _ (by decide),
    getRewardOwedAfterTokenLocals_comet]

theorem getRewardOwedAfterRescaleLocals_no_rewardConfig (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedAfterRescaleLocals evm I).get? "rewardConfig" = none := by
  rw [getRewardOwedAfterRescaleLocals, store_get_ne _ _ (by decide),
    getRewardOwedAfterTokenLocals_no_rewardConfig]

theorem getRewardOwedAfterShouldLocals_comet (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedAfterShouldLocals evm I).get? "comet" =
      some (getRewardOwedCometValue I) := by
  rw [getRewardOwedAfterShouldLocals, store_get_ne _ _ (by decide),
    getRewardOwedAfterRescaleLocals_comet]

theorem getRewardOwedAfterShouldLocals_no_rewardConfig (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedAfterShouldLocals evm I).get? "rewardConfig" = none := by
  rw [getRewardOwedAfterShouldLocals, store_get_ne _ _ (by decide),
    getRewardOwedAfterRescaleLocals_no_rewardConfig]

theorem getRewardOwedConfigLocals_comet (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedConfigLocals evm I).get? "comet" =
      some (getRewardOwedCometValue I) := by
  rw [getRewardOwedConfigLocals, getRewardOwedAfterShouldLocals,
    getRewardOwedAfterRescaleLocals, getRewardOwedAfterTokenLocals,
    getRewardOwedBaseLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), getRewardOwedStore_comet]

theorem getRewardOwedConfigLocals_account (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedConfigLocals evm I).get? "account" =
      some (getRewardOwedAccountValue I) := by
  rw [getRewardOwedConfigLocals, getRewardOwedAfterShouldLocals,
    getRewardOwedAfterRescaleLocals, getRewardOwedAfterTokenLocals,
    getRewardOwedBaseLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), getRewardOwedStore_account]

theorem getRewardOwedConfigLocals_token (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedConfigLocals evm I).get? "token" =
      some (getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I)) := by
  rw [getRewardOwedConfigLocals, getRewardOwedAfterShouldLocals,
    getRewardOwedAfterRescaleLocals, getRewardOwedAfterTokenLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem getRewardOwedConfigLocals_rescaleFactor (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedConfigLocals evm I).get? "rescaleFactor" =
      some (getRewardOwedRescaleValueFromSlot0 (getRewardOwedSlot0Load evm I)) := by
  rw [getRewardOwedConfigLocals, getRewardOwedAfterShouldLocals,
    getRewardOwedAfterRescaleLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem getRewardOwedConfigLocals_shouldUpscale (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedConfigLocals evm I).get? "shouldUpscale" =
      some (getRewardOwedShouldUpscaleValueFromSlot0 (getRewardOwedSlot0Load evm I)) := by
  rw [getRewardOwedConfigLocals, getRewardOwedAfterShouldLocals]
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem getRewardOwedConfigLocals_multiplier (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedConfigLocals evm I).get? "multiplier" =
      some (getRewardOwedMultiplierValue (getRewardOwedMultiplierLoad evm I)) := by
  rw [getRewardOwedConfigLocals, store_get_self]

theorem getRewardOwedConfigLocals_no_rewardsClaimed (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedConfigLocals evm I).get? "rewardsClaimed" = none := by
  rw [getRewardOwedConfigLocals, getRewardOwedAfterShouldLocals,
    getRewardOwedAfterRescaleLocals, getRewardOwedAfterTokenLocals,
    getRewardOwedBaseLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  rw [getRewardOwedStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem getRewardOwedAfterAccrueLocals_comet (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedAfterAccrueLocals evm I).get? "comet" =
      some (getRewardOwedCometValue I) := by
  rw [getRewardOwedAfterAccrueLocals, store_get_ne _ _ (by decide),
    getRewardOwedConfigLocals_comet]

theorem getRewardOwedAfterAccrueLocals_account (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedAfterAccrueLocals evm I).get? "account" =
      some (getRewardOwedAccountValue I) := by
  rw [getRewardOwedAfterAccrueLocals, store_get_ne _ _ (by decide),
    getRewardOwedConfigLocals_account]

theorem getRewardOwedAfterAccrueLocals_no_rewardsClaimed
    (evm : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedAfterAccrueLocals evm I).get? "rewardsClaimed" = none := by
  rw [getRewardOwedAfterAccrueLocals, store_get_ne _ _ (by decide),
    getRewardOwedConfigLocals_no_rewardsClaimed]

theorem getRewardOwedAfterClaimedLocals_comet
    (evm evmAcc : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedAfterClaimedLocals evm evmAcc I).get? "comet" =
      some (getRewardOwedCometValue I) := by
  rw [getRewardOwedAfterClaimedLocals, store_get_ne _ _ (by decide),
    getRewardOwedAfterAccrueLocals_comet]

theorem getRewardOwedAfterClaimedLocals_account
    (evm evmAcc : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedAfterClaimedLocals evm evmAcc I).get? "account" =
      some (getRewardOwedAccountValue I) := by
  rw [getRewardOwedAfterClaimedLocals, store_get_ne _ _ (by decide),
    getRewardOwedAfterAccrueLocals_account]

theorem getRewardOwedAfterClaimedLocals_rescaleFactor
    (evm evmAcc : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedAfterClaimedLocals evm evmAcc I).get? "rescaleFactor" =
      some (getRewardOwedRescaleValueFromSlot0 (getRewardOwedSlot0Load evm I)) := by
  rw [getRewardOwedAfterClaimedLocals, getRewardOwedAfterAccrueLocals,
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    getRewardOwedConfigLocals_rescaleFactor]

theorem getRewardOwedAfterClaimedLocals_shouldUpscale
    (evm evmAcc : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedAfterClaimedLocals evm evmAcc I).get? "shouldUpscale" =
      some (getRewardOwedShouldUpscaleValueFromSlot0 (getRewardOwedSlot0Load evm I)) := by
  rw [getRewardOwedAfterClaimedLocals, getRewardOwedAfterAccrueLocals,
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    getRewardOwedConfigLocals_shouldUpscale]

theorem getRewardOwedAfterClaimedLocals_multiplier
    (evm evmAcc : EVM.State) (I : ExecutionEnv) :
    (getRewardOwedAfterClaimedLocals evm evmAcc I).get? "multiplier" =
      some (getRewardOwedMultiplierValue (getRewardOwedMultiplierLoad evm I)) := by
  rw [getRewardOwedAfterClaimedLocals, getRewardOwedAfterAccrueLocals,
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    getRewardOwedConfigLocals_multiplier]

theorem getRewardOwedAfterInternalLocals_token
    (evm evmAcc : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    (getRewardOwedAfterInternalLocals evm evmAcc I accruedNat).get? "token" =
      some (getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I)) := by
  rw [getRewardOwedAfterInternalLocals, getRewardOwedAfterClaimedLocals,
    getRewardOwedAfterAccrueLocals, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    getRewardOwedConfigLocals_token]

theorem getRewardOwedAfterInternalLocals_accrued
    (evm evmAcc : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    (getRewardOwedAfterInternalLocals evm evmAcc I accruedNat).get? "accrued" =
      some (.int (Int.ofNat accruedNat)) := by
  rw [getRewardOwedAfterInternalLocals, store_get_self]

theorem getRewardOwedAfterInternalLocals_claimed
    (evm evmAcc : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    (getRewardOwedAfterInternalLocals evm evmAcc I accruedNat).get? "claimed" =
      some (.int (Int.ofNat (getRewardOwedClaimedLoad evmAcc I).toNat)) := by
  rw [getRewardOwedAfterInternalLocals, store_get_ne _ _ (by decide),
    getRewardOwedAfterClaimedLocals, store_get_self]

theorem getRewardOwedAfterOwedLocals_token
    (evm evmAcc : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    (getRewardOwedAfterOwedLocals evm evmAcc I accruedNat).get? "token" =
      some (getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I)) := by
  rw [getRewardOwedAfterOwedLocals, store_get_ne _ _ (by decide),
    getRewardOwedAfterInternalLocals_token]

theorem getRewardOwedAfterOwedLocals_owed
    (evm evmAcc : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    (getRewardOwedAfterOwedLocals evm evmAcc I accruedNat).get? "owed" =
      some (.int (Int.ofNat (getRewardOwedOwedNat evmAcc I accruedNat))) := by
  rw [getRewardOwedAfterOwedLocals, store_get_self]

theorem getRewardAccruedStore_comet (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (getRewardAccruedStore I slot0 multiplier).get? "comet" =
      some (getRewardOwedCometValue I) := by
  rw [getRewardAccruedStore, store_get_self]

theorem getRewardAccruedStore_account (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (getRewardAccruedStore I slot0 multiplier).get? "account" =
      some (getRewardOwedAccountValue I) := by
  rw [getRewardAccruedStore, store_get_ne _ _ (by decide), store_get_self]

theorem getRewardAccruedStore_rescaleFactor (I : ExecutionEnv)
    (slot0 multiplier : UInt256) :
    (getRewardAccruedStore I slot0 multiplier).get? "rescaleFactor" =
      some (.int (Int.ofNat (rewardConfigRescaleFromSlot0 slot0).toNat)) := by
  rw [getRewardAccruedStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem getRewardAccruedStore_shouldUpscale (I : ExecutionEnv)
    (slot0 multiplier : UInt256) :
    (getRewardAccruedStore I slot0 multiplier).get? "shouldUpscale" =
      some (wordToElem .bool (rewardConfigShouldUpscaleRawFromSlot0 slot0)) := by
  rw [getRewardAccruedStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem getRewardAccruedStore_multiplier (I : ExecutionEnv)
    (slot0 multiplier : UInt256) :
    (getRewardAccruedStore I slot0 multiplier).get? "multiplier" =
      some (.int (Int.ofNat multiplier.toNat)) := by
  rw [getRewardAccruedStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem getRewardAccruedAfterBaseLocals_accrued
    (I : ExecutionEnv) (slot0 multiplier accrued : UInt256) :
    (getRewardAccruedAfterBaseLocals I slot0 multiplier accrued).get? "accrued" =
      some (.int (Int.ofNat accrued.toNat)) := by
  rw [getRewardAccruedAfterBaseLocals, store_get_self]

theorem getRewardAccruedAfterBaseLocals_rescaleFactor
    (I : ExecutionEnv) (slot0 multiplier accrued : UInt256) :
    (getRewardAccruedAfterBaseLocals I slot0 multiplier accrued).get? "rescaleFactor" =
      some (.int (Int.ofNat (rewardConfigRescaleFromSlot0 slot0).toNat)) := by
  rw [getRewardAccruedAfterBaseLocals, store_get_ne _ _ (by decide),
    getRewardAccruedStore_rescaleFactor]

theorem getRewardAccruedAfterBaseLocals_shouldUpscale
    (I : ExecutionEnv) (slot0 multiplier accrued : UInt256) :
    (getRewardAccruedAfterBaseLocals I slot0 multiplier accrued).get? "shouldUpscale" =
      some (wordToElem .bool (rewardConfigShouldUpscaleRawFromSlot0 slot0)) := by
  rw [getRewardAccruedAfterBaseLocals, store_get_ne _ _ (by decide),
    getRewardAccruedStore_shouldUpscale]

theorem getRewardAccruedAfterBaseLocals_multiplier
    (I : ExecutionEnv) (slot0 multiplier accrued : UInt256) :
    (getRewardAccruedAfterBaseLocals I slot0 multiplier accrued).get? "multiplier" =
      some (.int (Int.ofNat multiplier.toNat)) := by
  rw [getRewardAccruedAfterBaseLocals, store_get_ne _ _ (by decide),
    getRewardAccruedStore_multiplier]

theorem getRewardAccruedAfterBranchLocals_accrued
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accruedNat : ℕ) :
    (getRewardAccruedAfterBranchLocals I slot0 multiplier accruedNat).get? "accrued" =
      some (.int (Int.ofNat accruedNat)) := by
  rw [getRewardAccruedAfterBranchLocals, store_get_self]

theorem getRewardAccruedAfterBranchLocals_multiplier
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accruedNat : ℕ) :
    (getRewardAccruedAfterBranchLocals I slot0 multiplier accruedNat).get? "multiplier" =
      some (.int (Int.ofNat multiplier.toNat)) := by
  rw [getRewardAccruedAfterBranchLocals, store_get_ne _ _ (by decide),
    getRewardAccruedStore_multiplier]

theorem getRewardAccruedAfterScaledLocals_scaled
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accruedNat : ℕ) :
    (getRewardAccruedAfterScaledLocals I slot0 multiplier accruedNat).get? "scaled" =
      some (.int (Int.ofNat (getRewardAccruedScaledNat multiplier accruedNat))) := by
  rw [getRewardAccruedAfterScaledLocals, store_get_self]

theorem getRewardAccruedAfterAssignedLocals_accrued
    (I : ExecutionEnv) (slot0 multiplier oldAccrued : UInt256) (accruedNat : ℕ) :
    (getRewardAccruedAfterAssignedLocals I slot0 multiplier oldAccrued accruedNat).get?
      "accrued" = some (.int (Int.ofNat accruedNat)) := by
  rw [getRewardAccruedAfterAssignedLocals, store_get_self]

theorem getRewardAccruedAfterAssignedLocals_multiplier
    (I : ExecutionEnv) (slot0 multiplier oldAccrued : UInt256) (accruedNat : ℕ) :
    (getRewardAccruedAfterAssignedLocals I slot0 multiplier oldAccrued accruedNat).get?
      "multiplier" = some (.int (Int.ofNat multiplier.toNat)) := by
  rw [getRewardAccruedAfterAssignedLocals, store_get_ne _ _ (by decide),
    getRewardAccruedAfterBaseLocals_multiplier]

theorem getRewardAccruedAfterAssignedScaledLocals_scaled
    (I : ExecutionEnv) (slot0 multiplier oldAccrued : UInt256) (accruedNat : ℕ) :
    (getRewardAccruedAfterAssignedScaledLocals I slot0 multiplier oldAccrued accruedNat).get?
      "scaled" =
      some (.int (Int.ofNat (getRewardAccruedScaledNat multiplier accruedNat))) := by
  rw [getRewardAccruedAfterAssignedScaledLocals, store_get_self]

theorem bindParams_getRewardAccrued (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    bindParams? getRewardAccruedFunction.params (getRewardAccruedArgs I slot0 multiplier) =
      some (getRewardAccruedStore I slot0 multiplier) := by
  simp [getRewardAccruedFunction, getRewardAccruedArgs, getRewardAccruedStore, bindParams?]

theorem lookupCallable_getRewardAccrued :
    lookupCallable? contract "getRewardAccrued" =
      some getRewardAccruedFunction.toCallable := by
  rfl

theorem evalExprs_getRewardAccrued_args_of {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv) (slot0 multiplier : UInt256)
    (hcomet : locals.get? "comet" = some (getRewardOwedCometValue I))
    (haccount : locals.get? "account" = some (getRewardOwedAccountValue I))
    (hrescale :
      locals.get? "rescaleFactor" =
        some (.int (Int.ofNat (rewardConfigRescaleFromSlot0 slot0).toNat)))
    (hshould :
      locals.get? "shouldUpscale" =
        some (wordToElem .bool (rewardConfigShouldUpscaleRawFromSlot0 slot0)))
    (hmult : locals.get? "multiplier" = some (.int (Int.ofNat multiplier.toNat))) :
    evalExprs? config { contract := contract, locals := locals } evm
      [.var "comet", .var "account", .var "rescaleFactor",
        .var "shouldUpscale", .var "multiplier"] =
      .ok (getRewardAccruedArgs I slot0 multiplier) := by
  simp only [getRewardAccruedArgs, evalExprs?,
    evalExpr_getRewardOwed_comet_of evm I hcomet,
    evalExpr_getRewardOwed_account_of evm I haccount, EvalResult.bind, bind,
    evalExpr?, EvalResult.ofOption]
  rw [hrescale, hshould, hmult]
  rfl

theorem evalExprs_getRewardAccrued_baseTrackingArgs (evm : EVM.State)
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    evalExprs? config
      { contract := contract, locals := getRewardAccruedStore I slot0 multiplier }
      evm [.var "account"] = .ok (getRewardAccruedBaseTrackingArgs I) := by
  simp only [getRewardAccruedBaseTrackingArgs, evalExprs?,
    evalExpr_getRewardOwed_account_of evm I
      (getRewardAccruedStore_account I slot0 multiplier), EvalResult.bind, bind]
  rfl

theorem evalExpr_getRewardAccrued_shouldUpscale_true (evm : EVM.State)
    (I : ExecutionEnv) (slot0 multiplier accrued : UInt256)
    (htrue : rewardConfigShouldUpscaleRawFromSlot0 slot0 ≠ ⟨0⟩) :
    evalExpr? config (getRewardAccruedAfterBaseFrame I slot0 multiplier accrued) evm
      (.var "shouldUpscale") = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getRewardAccruedAfterBaseLocals_shouldUpscale]
  simp [wordToElem]
  intro hz
  apply htrue
  apply u256_inj
  simpa [UInt256.toNat] using hz

theorem evalExpr_getRewardAccrued_shouldUpscale_false (evm : EVM.State)
    (I : ExecutionEnv) (slot0 multiplier accrued : UInt256)
    (hfalse : rewardConfigShouldUpscaleRawFromSlot0 slot0 = ⟨0⟩) :
    evalExpr? config (getRewardAccruedAfterBaseFrame I slot0 multiplier accrued) evm
      (.var "shouldUpscale") = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getRewardAccruedAfterBaseLocals_shouldUpscale]
  simp [wordToElem, hfalse]

theorem evalExpr_getRewardAccrued_upscaled (evm : EVM.State)
    (I : ExecutionEnv) (slot0 multiplier accrued : UInt256)
    (hup : getRewardAccruedUpscaledNat slot0 accrued < UInt256.size) :
    evalExpr? config (getRewardAccruedAfterBaseFrame I slot0 multiplier accrued) evm
      (u256 (.binary .mul (.var "accrued") (.var "rescaleFactor"))) =
      .ok (.int (Int.ofNat (getRewardAccruedUpscaledNat slot0 accrued))) := by
  simp only [u256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [getRewardAccruedAfterBaseLocals_accrued,
    getRewardAccruedAfterBaseLocals_rescaleFactor]
  simp only [evalBinaryOp?, getRewardAccruedUpscaledNat]
  have hnonneg :
      ¬ (↑accrued.toNat * ↑(rewardConfigRescaleFromSlot0 slot0).toNat : Int) < 0 := by
    rw [show (↑accrued.toNat * ↑(rewardConfigRescaleFromSlot0 slot0).toNat : Int) =
      ↑(accrued.toNat * (rewardConfigRescaleFromSlot0 slot0).toNat) by norm_num]
    omega
  have hltInt :
      ¬ (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) ≤
        (↑accrued.toNat * ↑(rewardConfigRescaleFromSlot0 slot0).toNat : Int) := by
    rw [show (↑accrued.toNat * ↑(rewardConfigRescaleFromSlot0 slot0).toNat : Int) =
      ↑(accrued.toNat * (rewardConfigRescaleFromSlot0 slot0).toNat) by norm_num]
    intro hle
    have hleNat : UInt256.size ≤ accrued.toNat * (rewardConfigRescaleFromSlot0 slot0).toNat := by
      norm_num [UInt256.size]
      exact_mod_cast hle
    exact (Nat.not_le_of_gt hup) hleNat
  simpa [uint256Int, hnonneg, hltInt, pure]

theorem evalExpr_getRewardAccrued_downscaled (evm : EVM.State)
    (I : ExecutionEnv) (slot0 multiplier accrued : UInt256)
    (hrescaleNZ : rewardConfigRescaleFromSlot0 slot0 ≠ ⟨0⟩) :
    evalExpr? config (getRewardAccruedAfterBaseFrame I slot0 multiplier accrued) evm
      (.binary .div (.var "accrued") (.var "rescaleFactor")) =
      .ok (.int (Int.ofNat (getRewardAccruedDownscaledNat slot0 accrued))) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [getRewardAccruedAfterBaseLocals_accrued,
    getRewardAccruedAfterBaseLocals_rescaleFactor]
  have hrescaleNat : (rewardConfigRescaleFromSlot0 slot0).toNat ≠ 0 := by
    intro hz
    apply hrescaleNZ
    apply u256_inj
    simpa [UInt256.toNat] using hz
  have hrescaleInt : ¬ (↑(rewardConfigRescaleFromSlot0 slot0).toNat : Int) = 0 := by
    intro hz
    apply hrescaleNat
    exact_mod_cast hz
  simp only [evalBinaryOp?, getRewardAccruedDownscaledNat]
  by_cases hz : Int.ofNat (rewardConfigRescaleFromSlot0 slot0).toNat = 0
  · exact False.elim (hrescaleInt hz)
  · simp only [hz, ↓reduceIte]
    have hdiv :
        Int.ofNat accrued.toNat / Int.ofNat (rewardConfigRescaleFromSlot0 slot0).toNat =
          Int.ofNat (accrued.toNat / (rewardConfigRescaleFromSlot0 slot0).toNat) :=
      Int.ofNat_ediv_ofNat
    rw [hdiv]

theorem evalExpr_getRewardAccrued_downscaled_revert_zero (evm : EVM.State)
    (I : ExecutionEnv) (slot0 multiplier accrued : UInt256)
    (hrescaleZero : rewardConfigRescaleFromSlot0 slot0 = ⟨0⟩) :
    evalExpr? config (getRewardAccruedAfterBaseFrame I slot0 multiplier accrued) evm
      (.binary .div (.var "accrued") (.var "rescaleFactor")) = .revert := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [getRewardAccruedAfterBaseLocals_accrued,
    getRewardAccruedAfterBaseLocals_rescaleFactor]
  have hrescaleNat : (rewardConfigRescaleFromSlot0 slot0).toNat = 0 := by
    rw [hrescaleZero]
    rfl
  simp [evalBinaryOp?, hrescaleNat]

theorem evalExpr_getRewardAccrued_scaled (evm : EVM.State)
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accruedNat : ℕ)
    (hscaled : getRewardAccruedScaledNat multiplier accruedNat < UInt256.size) :
    evalExpr? config (getRewardAccruedAfterBranchFrame I slot0 multiplier accruedNat) evm
      (u256 (.binary .mul (.var "accrued") (.var "multiplier"))) =
      .ok (.int (Int.ofNat (getRewardAccruedScaledNat multiplier accruedNat))) := by
  simp only [u256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [getRewardAccruedAfterBranchLocals_accrued,
    getRewardAccruedAfterBranchLocals_multiplier]
  simp only [evalBinaryOp?, getRewardAccruedScaledNat]
  have hnonneg : ¬ (↑accruedNat * ↑multiplier.toNat : Int) < 0 := by
    rw [show (↑accruedNat * ↑multiplier.toNat : Int) =
      ↑(accruedNat * multiplier.toNat) by norm_num]
    omega
  have hltInt :
      ¬ (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) ≤
        (↑accruedNat * ↑multiplier.toNat : Int) := by
    rw [show (↑accruedNat * ↑multiplier.toNat : Int) =
      ↑(accruedNat * multiplier.toNat) by norm_num]
    intro hle
    have hleNat : UInt256.size ≤ accruedNat * multiplier.toNat := by
      norm_num [UInt256.size]
      exact_mod_cast hle
    exact (Nat.not_le_of_gt hscaled) hleNat
  simpa [uint256Int, hnonneg, hltInt, pure]

theorem evalExpr_getRewardAccrued_return (evm : EVM.State)
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accruedNat : ℕ) :
    evalExpr? config (getRewardAccruedAfterScaledFrame I slot0 multiplier accruedNat) evm
      (.binary .div (.var "scaled") (.intLit factorScale)) =
      .ok (.int (Int.ofNat (getRewardAccruedReturnNat multiplier accruedNat))) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [getRewardAccruedAfterScaledLocals_scaled]
  simp [evalBinaryOp?, getRewardAccruedReturnNat, factorScale]

theorem evalExpr_getRewardAccrued_scaled_assigned (evm : EVM.State)
    (I : ExecutionEnv) (slot0 multiplier oldAccrued : UInt256) (accruedNat : ℕ)
    (hscaled : getRewardAccruedScaledNat multiplier accruedNat < UInt256.size) :
    evalExpr? config
      (getRewardAccruedAfterAssignedFrame I slot0 multiplier oldAccrued accruedNat) evm
      (u256 (.binary .mul (.var "accrued") (.var "multiplier"))) =
      .ok (.int (Int.ofNat (getRewardAccruedScaledNat multiplier accruedNat))) := by
  simp only [u256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [getRewardAccruedAfterAssignedLocals_accrued,
    getRewardAccruedAfterAssignedLocals_multiplier]
  simp only [evalBinaryOp?, getRewardAccruedScaledNat]
  have hnonneg : ¬ (↑accruedNat * ↑multiplier.toNat : Int) < 0 := by
    rw [show (↑accruedNat * ↑multiplier.toNat : Int) =
      ↑(accruedNat * multiplier.toNat) by norm_num]
    omega
  have hltInt :
      ¬ (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) ≤
        (↑accruedNat * ↑multiplier.toNat : Int) := by
    rw [show (↑accruedNat * ↑multiplier.toNat : Int) =
      ↑(accruedNat * multiplier.toNat) by norm_num]
    intro hle
    have hleNat : UInt256.size ≤ accruedNat * multiplier.toNat := by
      norm_num [UInt256.size]
      exact_mod_cast hle
    exact (Nat.not_le_of_gt hscaled) hleNat
  simpa [uint256Int, hnonneg, hltInt, pure]

theorem evalExpr_getRewardAccrued_scaled_assigned_revert (evm : EVM.State)
    (I : ExecutionEnv) (slot0 multiplier oldAccrued : UInt256) (accruedNat : ℕ)
    (hover : UInt256.size ≤ getRewardAccruedScaledNat multiplier accruedNat) :
    evalExpr? config
      (getRewardAccruedAfterAssignedFrame I slot0 multiplier oldAccrued accruedNat) evm
      (u256 (.binary .mul (.var "accrued") (.var "multiplier"))) = .revert := by
  simp only [u256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [getRewardAccruedAfterAssignedLocals_accrued,
    getRewardAccruedAfterAssignedLocals_multiplier]
  simp only [evalBinaryOp?, getRewardAccruedScaledNat]
  have hnonneg : ¬ (↑accruedNat * ↑multiplier.toNat : Int) < 0 := by
    rw [show (↑accruedNat * ↑multiplier.toNat : Int) =
      ↑(accruedNat * multiplier.toNat) by norm_num]
    omega
  have hgeInt :
      (115792089237316195423570985008687907853269984665640564039457584007913129639936 :
          Int) ≤
        (↑accruedNat * ↑multiplier.toNat : Int) := by
    rw [show (↑accruedNat * ↑multiplier.toNat : Int) =
      ↑(accruedNat * multiplier.toNat) by norm_num]
    norm_num [UInt256.size] at hover ⊢
    exact_mod_cast hover
  simpa [uint256Int, hnonneg, hgeInt, pure]

theorem evalExpr_getRewardAccrued_return_assigned (evm : EVM.State)
    (I : ExecutionEnv) (slot0 multiplier oldAccrued : UInt256) (accruedNat : ℕ) :
    evalExpr? config
      (getRewardAccruedAfterAssignedScaledFrame I slot0 multiplier oldAccrued accruedNat) evm
      (.binary .div (.var "scaled") (.intLit factorScale)) =
      .ok (.int (Int.ofNat (getRewardAccruedReturnNat multiplier accruedNat))) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [getRewardAccruedAfterAssignedScaledLocals_scaled]
  simp [evalBinaryOp?, getRewardAccruedReturnNat, factorScale]

theorem getRewardAccruedBaseTrackingCallSuccess
    (evm evmBase : EVM.State) (I : ExecutionEnv) (slot0 multiplier accrued : UInt256)
    {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (true, evmBase, out) false)
    (hdec : config.externalABI.decode? "baseTrackingAccrued" out =
      some [.int (Int.ofNat accrued.toNat)]) :
    ExecBlock config { contract := contract, locals := getRewardAccruedStore I slot0 multiplier }
      evm
      [ .externalCall (.var "comet") "baseTrackingAccrued" (.intLit 0)
        [.var "account"] "accrued" false]
      (.ok (getRewardAccruedAfterBaseFrame I slot0 multiplier accrued) evmBase) := by
  exact externalCallVarSuccess (cfg := config) (C := contract)
    (evm := evm) (evm' := evmBase) (locals := getRewardAccruedStore I slot0 multiplier)
    (receiver := "comet") (retVar := "accrued") (name := "baseTrackingAccrued")
    (target := getRewardOwedCometTarget I) (sendVal := 0)
    (args := [.var "account"]) (argVals := getRewardAccruedBaseTrackingArgs I)
    (out := out) (perm := false) (value := [.int (Int.ofNat accrued.toNat)])
    (getRewardAccruedStore_comet I slot0 multiplier)
    (evalExprs_getRewardAccrued_baseTrackingArgs evm I slot0 multiplier)
    hcall hdec

theorem assignGetRewardAccrued_upscaled
    (evm : EVM.State) (I : ExecutionEnv) (slot0 multiplier accrued : UInt256) :
    assignStorageRef? config (getRewardAccruedAfterBaseFrame I slot0 multiplier accrued) evm
      .localVar { base := "accrued" }
      (.int (Int.ofNat (getRewardAccruedUpscaledNat slot0 accrued))) =
    .ok (getRewardAccruedAfterAssignedFrame I slot0 multiplier accrued
      (getRewardAccruedUpscaledNat slot0 accrued), evm) := by
  simp [assignStorageRef?, updateLocalPath?, getRewardAccruedAfterBaseFrame,
    getRewardAccruedAfterBaseLocals, getRewardAccruedAfterAssignedFrame,
    getRewardAccruedAfterAssignedLocals, EvalResult.bind, bind, pure]

theorem assignGetRewardAccrued_downscaled
    (evm : EVM.State) (I : ExecutionEnv) (slot0 multiplier accrued : UInt256) :
    assignStorageRef? config (getRewardAccruedAfterBaseFrame I slot0 multiplier accrued) evm
      .localVar { base := "accrued" }
      (.int (Int.ofNat (getRewardAccruedDownscaledNat slot0 accrued))) =
    .ok (getRewardAccruedAfterAssignedFrame I slot0 multiplier accrued
      (getRewardAccruedDownscaledNat slot0 accrued), evm) := by
  simp [assignStorageRef?, updateLocalPath?, getRewardAccruedAfterBaseFrame,
    getRewardAccruedAfterBaseLocals, getRewardAccruedAfterAssignedFrame,
    getRewardAccruedAfterAssignedLocals, EvalResult.bind, bind, pure]

theorem getRewardAccruedBodyReverts_callFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) (slot0 multiplier : UInt256)
    {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (false, evm', out) false) :
    ExecFuncBody config
      { contract := contract, locals := getRewardAccruedStore I slot0 multiplier }
      evm getRewardAccruedFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config
    { contract := contract, locals := getRewardAccruedStore I slot0 multiplier } evm
    [ .externalCall (.var "comet") "baseTrackingAccrued" (.intLit 0)
        [.var "account"] "accrued" false,
      .ite (.var "shouldUpscale")
        [ .assign .localVar { base := "accrued" }
            (u256 (.binary .mul (.var "accrued") (.var "rescaleFactor"))) ]
        [ .assign .localVar { base := "accrued" }
            (.binary .div (.var "accrued") (.var "rescaleFactor")) ],
      .letDecl "scaled" (some uint256)
        (u256 (.binary .mul (.var "accrued") (.var "multiplier"))),
      .return [.binary .div (.var "scaled") (.intLit factorScale)] ] .reverted
  exact ExecBlock.consRevert
    (ExecStmt.externalCallFailure
      (evalExpr_getRewardOwed_comet_of evm I (getRewardAccruedStore_comet I slot0 multiplier))
      (by simp [evalExpr?, pure])
      (evalExprs_getRewardAccrued_baseTrackingArgs evm I slot0 multiplier)
      hcall)

theorem getRewardAccruedBodyReverts_decode
    (evm evm' : EVM.State) (I : ExecutionEnv) (slot0 multiplier : UInt256)
    {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (true, evm', out) false)
    (hdec : config.externalABI.decode? "baseTrackingAccrued" out = none) :
    ExecFuncBody config
      { contract := contract, locals := getRewardAccruedStore I slot0 multiplier }
      evm getRewardAccruedFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config
    { contract := contract, locals := getRewardAccruedStore I slot0 multiplier } evm
    [ .externalCall (.var "comet") "baseTrackingAccrued" (.intLit 0)
        [.var "account"] "accrued" false,
      .ite (.var "shouldUpscale")
        [ .assign .localVar { base := "accrued" }
            (u256 (.binary .mul (.var "accrued") (.var "rescaleFactor"))) ]
        [ .assign .localVar { base := "accrued" }
            (.binary .div (.var "accrued") (.var "rescaleFactor")) ],
      .letDecl "scaled" (some uint256)
        (u256 (.binary .mul (.var "accrued") (.var "multiplier"))),
      .return [.binary .div (.var "scaled") (.intLit factorScale)] ] .reverted
  exact ExecBlock.consRevert
    (ExecStmt.externalCallReturnDecodeRevert
      (evalExpr_getRewardOwed_comet_of evm I (getRewardAccruedStore_comet I slot0 multiplier))
      (by simp [evalExpr?, pure])
      (evalExprs_getRewardAccrued_baseTrackingArgs evm I slot0 multiplier)
      hcall hdec)

theorem getRewardAccruedBodyReturns_upscale
    (evm evmBase : EVM.State) (I : ExecutionEnv) (slot0 multiplier accrued : UInt256)
    {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (true, evmBase, out) false)
    (hdec : config.externalABI.decode? "baseTrackingAccrued" out =
      some [.int (Int.ofNat accrued.toNat)])
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 slot0 ≠ ⟨0⟩)
    (hup : getRewardAccruedUpscaledNat slot0 accrued < UInt256.size)
    (hscaled :
      getRewardAccruedScaledNat multiplier (getRewardAccruedUpscaledNat slot0 accrued) <
        UInt256.size) :
    ExecFuncBody config
      { contract := contract, locals := getRewardAccruedStore I slot0 multiplier }
      evm getRewardAccruedFunction.body
      (.returned
        (getRewardAccruedAfterAssignedScaledFrame I slot0 multiplier accrued
          (getRewardAccruedUpscaledNat slot0 accrued))
        evmBase
        (some [.int (Int.ofNat (getRewardAccruedReturnNat multiplier
          (getRewardAccruedUpscaledNat slot0 accrued)))])) := by
  refine ExecFuncBody.execBlockRet ?_
  change ExecBlock config
    { contract := contract, locals := getRewardAccruedStore I slot0 multiplier } evm
    [ .externalCall (.var "comet") "baseTrackingAccrued" (.intLit 0)
        [.var "account"] "accrued" false,
      .ite (.var "shouldUpscale")
        [ .assign .localVar { base := "accrued" }
            (u256 (.binary .mul (.var "accrued") (.var "rescaleFactor"))) ]
        [ .assign .localVar { base := "accrued" }
            (.binary .div (.var "accrued") (.var "rescaleFactor")) ],
      .letDecl "scaled" (some uint256)
        (u256 (.binary .mul (.var "accrued") (.var "multiplier"))),
      .return [.binary .div (.var "scaled") (.intLit factorScale)] ]
    (.returned
      (getRewardAccruedAfterAssignedScaledFrame I slot0 multiplier accrued
        (getRewardAccruedUpscaledNat slot0 accrued))
      evmBase
      (some [.int (Int.ofNat (getRewardAccruedReturnNat multiplier
        (getRewardAccruedUpscaledNat slot0 accrued)))]))
  have hcallBlock :=
    getRewardAccruedBaseTrackingCallSuccess evm evmBase I slot0 multiplier accrued
      hcall hdec
  have hrest :
      ExecBlock config (getRewardAccruedAfterBaseFrame I slot0 multiplier accrued) evmBase
        [ .ite (.var "shouldUpscale")
            [ .assign .localVar { base := "accrued" }
                (u256 (.binary .mul (.var "accrued") (.var "rescaleFactor"))) ]
            [ .assign .localVar { base := "accrued" }
                (.binary .div (.var "accrued") (.var "rescaleFactor")) ],
          .letDecl "scaled" (some uint256)
            (u256 (.binary .mul (.var "accrued") (.var "multiplier"))),
          .return [.binary .div (.var "scaled") (.intLit factorScale)] ]
        (.returned
          (getRewardAccruedAfterAssignedScaledFrame I slot0 multiplier accrued
            (getRewardAccruedUpscaledNat slot0 accrued))
          evmBase
          (some [.int (Int.ofNat (getRewardAccruedReturnNat multiplier
            (getRewardAccruedUpscaledNat slot0 accrued)))])) := by
    refine ExecBlock.consNormal
      (solm' := getRewardAccruedAfterAssignedFrame I slot0 multiplier accrued
        (getRewardAccruedUpscaledNat slot0 accrued))
      (evm' := evmBase) ?hite ?_
    · refine ExecStmt.iteTrue
        (evalExpr_getRewardAccrued_shouldUpscale_true evmBase I slot0 multiplier accrued
          hshould)
        ?_
      refine ExecBlock.consNormal ?hassign ExecBlock.nil
      exact ExecStmt.assign
        (evalExpr_getRewardAccrued_upscaled evmBase I slot0 multiplier accrued hup)
        (assignGetRewardAccrued_upscaled evmBase I slot0 multiplier accrued)
    refine ExecBlock.consNormal
      (solm' := getRewardAccruedAfterAssignedScaledFrame I slot0 multiplier accrued
        (getRewardAccruedUpscaledNat slot0 accrued))
      (evm' := evmBase) ?hscaledStmt ?_
    · exact ExecStmt.letDecl
        (evalExpr_getRewardAccrued_scaled_assigned evmBase I slot0 multiplier accrued
          (getRewardAccruedUpscaledNat slot0 accrued) hscaled)
    exact ExecBlock.consReturn
      (ExecStmt.return (evalExprs?_singleton
        (evalExpr_getRewardAccrued_return_assigned evmBase I slot0 multiplier accrued
          (getRewardAccruedUpscaledNat slot0 accrued))))
  exact execBlock_append hcallBlock hrest

theorem getRewardAccruedBodyReturns_downscale
    (evm evmBase : EVM.State) (I : ExecutionEnv) (slot0 multiplier accrued : UInt256)
    {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (true, evmBase, out) false)
    (hdec : config.externalABI.decode? "baseTrackingAccrued" out =
      some [.int (Int.ofNat accrued.toNat)])
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 slot0 = ⟨0⟩)
    (hrescaleNZ : rewardConfigRescaleFromSlot0 slot0 ≠ ⟨0⟩)
    (hscaled :
      getRewardAccruedScaledNat multiplier (getRewardAccruedDownscaledNat slot0 accrued) <
        UInt256.size) :
    ExecFuncBody config
      { contract := contract, locals := getRewardAccruedStore I slot0 multiplier }
      evm getRewardAccruedFunction.body
      (.returned
        (getRewardAccruedAfterAssignedScaledFrame I slot0 multiplier accrued
          (getRewardAccruedDownscaledNat slot0 accrued))
        evmBase
        (some [.int (Int.ofNat (getRewardAccruedReturnNat multiplier
          (getRewardAccruedDownscaledNat slot0 accrued)))])) := by
  refine ExecFuncBody.execBlockRet ?_
  change ExecBlock config
    { contract := contract, locals := getRewardAccruedStore I slot0 multiplier } evm
    [ .externalCall (.var "comet") "baseTrackingAccrued" (.intLit 0)
        [.var "account"] "accrued" false,
      .ite (.var "shouldUpscale")
        [ .assign .localVar { base := "accrued" }
            (u256 (.binary .mul (.var "accrued") (.var "rescaleFactor"))) ]
        [ .assign .localVar { base := "accrued" }
            (.binary .div (.var "accrued") (.var "rescaleFactor")) ],
      .letDecl "scaled" (some uint256)
        (u256 (.binary .mul (.var "accrued") (.var "multiplier"))),
      .return [.binary .div (.var "scaled") (.intLit factorScale)] ]
    (.returned
      (getRewardAccruedAfterAssignedScaledFrame I slot0 multiplier accrued
        (getRewardAccruedDownscaledNat slot0 accrued))
      evmBase
      (some [.int (Int.ofNat (getRewardAccruedReturnNat multiplier
        (getRewardAccruedDownscaledNat slot0 accrued)))]))
  have hcallBlock :=
    getRewardAccruedBaseTrackingCallSuccess evm evmBase I slot0 multiplier accrued
      hcall hdec
  have hrest :
      ExecBlock config (getRewardAccruedAfterBaseFrame I slot0 multiplier accrued) evmBase
        [ .ite (.var "shouldUpscale")
            [ .assign .localVar { base := "accrued" }
                (u256 (.binary .mul (.var "accrued") (.var "rescaleFactor"))) ]
            [ .assign .localVar { base := "accrued" }
                (.binary .div (.var "accrued") (.var "rescaleFactor")) ],
          .letDecl "scaled" (some uint256)
            (u256 (.binary .mul (.var "accrued") (.var "multiplier"))),
          .return [.binary .div (.var "scaled") (.intLit factorScale)] ]
        (.returned
          (getRewardAccruedAfterAssignedScaledFrame I slot0 multiplier accrued
            (getRewardAccruedDownscaledNat slot0 accrued))
          evmBase
          (some [.int (Int.ofNat (getRewardAccruedReturnNat multiplier
            (getRewardAccruedDownscaledNat slot0 accrued)))])) := by
    refine ExecBlock.consNormal
      (solm' := getRewardAccruedAfterAssignedFrame I slot0 multiplier accrued
        (getRewardAccruedDownscaledNat slot0 accrued))
      (evm' := evmBase) ?hite ?_
    · refine ExecStmt.iteFalse
        (evalExpr_getRewardAccrued_shouldUpscale_false evmBase I slot0 multiplier accrued
          hshould)
        ?_
      refine ExecBlock.consNormal ?hassign ExecBlock.nil
      exact ExecStmt.assign
        (evalExpr_getRewardAccrued_downscaled evmBase I slot0 multiplier accrued hrescaleNZ)
        (assignGetRewardAccrued_downscaled evmBase I slot0 multiplier accrued)
    refine ExecBlock.consNormal
      (solm' := getRewardAccruedAfterAssignedScaledFrame I slot0 multiplier accrued
        (getRewardAccruedDownscaledNat slot0 accrued))
      (evm' := evmBase) ?hscaledStmt ?_
    · exact ExecStmt.letDecl
        (evalExpr_getRewardAccrued_scaled_assigned evmBase I slot0 multiplier accrued
          (getRewardAccruedDownscaledNat slot0 accrued) hscaled)
    exact ExecBlock.consReturn
      (ExecStmt.return (evalExprs?_singleton
        (evalExpr_getRewardAccrued_return_assigned evmBase I slot0 multiplier accrued
          (getRewardAccruedDownscaledNat slot0 accrued))))
  exact execBlock_append hcallBlock hrest

theorem getRewardAccruedBodyReverts_downscale_zero
    (evm evmBase : EVM.State) (I : ExecutionEnv) (slot0 multiplier accrued : UInt256)
    {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (true, evmBase, out) false)
    (hdec : config.externalABI.decode? "baseTrackingAccrued" out =
      some [.int (Int.ofNat accrued.toNat)])
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 slot0 = ⟨0⟩)
    (hrescaleZero : rewardConfigRescaleFromSlot0 slot0 = ⟨0⟩) :
    ExecFuncBody config
      { contract := contract, locals := getRewardAccruedStore I slot0 multiplier }
      evm getRewardAccruedFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config
    { contract := contract, locals := getRewardAccruedStore I slot0 multiplier } evm
    [ .externalCall (.var "comet") "baseTrackingAccrued" (.intLit 0)
        [.var "account"] "accrued" false,
      .ite (.var "shouldUpscale")
        [ .assign .localVar { base := "accrued" }
            (u256 (.binary .mul (.var "accrued") (.var "rescaleFactor"))) ]
        [ .assign .localVar { base := "accrued" }
            (.binary .div (.var "accrued") (.var "rescaleFactor")) ],
      .letDecl "scaled" (some uint256)
        (u256 (.binary .mul (.var "accrued") (.var "multiplier"))),
      .return [.binary .div (.var "scaled") (.intLit factorScale)] ] .reverted
  have hcallBlock :=
    getRewardAccruedBaseTrackingCallSuccess evm evmBase I slot0 multiplier accrued
      hcall hdec
  have hrest :
      ExecBlock config (getRewardAccruedAfterBaseFrame I slot0 multiplier accrued) evmBase
        [ .ite (.var "shouldUpscale")
            [ .assign .localVar { base := "accrued" }
                (u256 (.binary .mul (.var "accrued") (.var "rescaleFactor"))) ]
            [ .assign .localVar { base := "accrued" }
                (.binary .div (.var "accrued") (.var "rescaleFactor")) ],
          .letDecl "scaled" (some uint256)
            (u256 (.binary .mul (.var "accrued") (.var "multiplier"))),
          .return [.binary .div (.var "scaled") (.intLit factorScale)] ]
        .reverted := by
    refine ExecBlock.consRevert (ExecStmt.iteFalse
      (evalExpr_getRewardAccrued_shouldUpscale_false evmBase I slot0 multiplier accrued
        hshould) ?_)
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert
      (evalExpr_getRewardAccrued_downscaled_revert_zero evmBase I slot0 multiplier
        accrued hrescaleZero))
  exact execBlock_append hcallBlock hrest

theorem getRewardAccruedBodyReverts_upscale_scaledOverflow
    (evm evmBase : EVM.State) (I : ExecutionEnv) (slot0 multiplier accrued : UInt256)
    {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (true, evmBase, out) false)
    (hdec : config.externalABI.decode? "baseTrackingAccrued" out =
      some [.int (Int.ofNat accrued.toNat)])
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 slot0 ≠ ⟨0⟩)
    (hup : getRewardAccruedUpscaledNat slot0 accrued < UInt256.size)
    (hover :
      UInt256.size ≤
        getRewardAccruedScaledNat multiplier (getRewardAccruedUpscaledNat slot0 accrued)) :
    ExecFuncBody config
      { contract := contract, locals := getRewardAccruedStore I slot0 multiplier }
      evm getRewardAccruedFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config
    { contract := contract, locals := getRewardAccruedStore I slot0 multiplier } evm
    [ .externalCall (.var "comet") "baseTrackingAccrued" (.intLit 0)
        [.var "account"] "accrued" false,
      .ite (.var "shouldUpscale")
        [ .assign .localVar { base := "accrued" }
            (u256 (.binary .mul (.var "accrued") (.var "rescaleFactor"))) ]
        [ .assign .localVar { base := "accrued" }
            (.binary .div (.var "accrued") (.var "rescaleFactor")) ],
      .letDecl "scaled" (some uint256)
        (u256 (.binary .mul (.var "accrued") (.var "multiplier"))),
      .return [.binary .div (.var "scaled") (.intLit factorScale)] ] .reverted
  have hcallBlock :=
    getRewardAccruedBaseTrackingCallSuccess evm evmBase I slot0 multiplier accrued
      hcall hdec
  have hrest :
      ExecBlock config (getRewardAccruedAfterBaseFrame I slot0 multiplier accrued) evmBase
        [ .ite (.var "shouldUpscale")
            [ .assign .localVar { base := "accrued" }
                (u256 (.binary .mul (.var "accrued") (.var "rescaleFactor"))) ]
            [ .assign .localVar { base := "accrued" }
                (.binary .div (.var "accrued") (.var "rescaleFactor")) ],
          .letDecl "scaled" (some uint256)
            (u256 (.binary .mul (.var "accrued") (.var "multiplier"))),
          .return [.binary .div (.var "scaled") (.intLit factorScale)] ]
        .reverted := by
    refine ExecBlock.consNormal
      (solm' := getRewardAccruedAfterAssignedFrame I slot0 multiplier accrued
        (getRewardAccruedUpscaledNat slot0 accrued))
      (evm' := evmBase) ?hite ?_
    · refine ExecStmt.iteTrue
        (evalExpr_getRewardAccrued_shouldUpscale_true evmBase I slot0 multiplier accrued
          hshould)
        ?_
      refine ExecBlock.consNormal ?hassign ExecBlock.nil
      exact ExecStmt.assign
        (evalExpr_getRewardAccrued_upscaled evmBase I slot0 multiplier accrued hup)
        (assignGetRewardAccrued_upscaled evmBase I slot0 multiplier accrued)
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert
      (evalExpr_getRewardAccrued_scaled_assigned_revert evmBase I slot0 multiplier accrued
        (getRewardAccruedUpscaledNat slot0 accrued) hover))
  exact execBlock_append hcallBlock hrest

theorem getRewardAccruedBodyReverts_downscale_scaledOverflow
    (evm evmBase : EVM.State) (I : ExecutionEnv) (slot0 multiplier accrued : UInt256)
    {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (true, evmBase, out) false)
    (hdec : config.externalABI.decode? "baseTrackingAccrued" out =
      some [.int (Int.ofNat accrued.toNat)])
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 slot0 = ⟨0⟩)
    (hrescaleNZ : rewardConfigRescaleFromSlot0 slot0 ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤
        getRewardAccruedScaledNat multiplier (getRewardAccruedDownscaledNat slot0 accrued)) :
    ExecFuncBody config
      { contract := contract, locals := getRewardAccruedStore I slot0 multiplier }
      evm getRewardAccruedFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config
    { contract := contract, locals := getRewardAccruedStore I slot0 multiplier } evm
    [ .externalCall (.var "comet") "baseTrackingAccrued" (.intLit 0)
        [.var "account"] "accrued" false,
      .ite (.var "shouldUpscale")
        [ .assign .localVar { base := "accrued" }
            (u256 (.binary .mul (.var "accrued") (.var "rescaleFactor"))) ]
        [ .assign .localVar { base := "accrued" }
            (.binary .div (.var "accrued") (.var "rescaleFactor")) ],
      .letDecl "scaled" (some uint256)
        (u256 (.binary .mul (.var "accrued") (.var "multiplier"))),
      .return [.binary .div (.var "scaled") (.intLit factorScale)] ] .reverted
  have hcallBlock :=
    getRewardAccruedBaseTrackingCallSuccess evm evmBase I slot0 multiplier accrued
      hcall hdec
  have hrest :
      ExecBlock config (getRewardAccruedAfterBaseFrame I slot0 multiplier accrued) evmBase
        [ .ite (.var "shouldUpscale")
            [ .assign .localVar { base := "accrued" }
                (u256 (.binary .mul (.var "accrued") (.var "rescaleFactor"))) ]
            [ .assign .localVar { base := "accrued" }
                (.binary .div (.var "accrued") (.var "rescaleFactor")) ],
          .letDecl "scaled" (some uint256)
            (u256 (.binary .mul (.var "accrued") (.var "multiplier"))),
          .return [.binary .div (.var "scaled") (.intLit factorScale)] ]
        .reverted := by
    refine ExecBlock.consNormal
      (solm' := getRewardAccruedAfterAssignedFrame I slot0 multiplier accrued
        (getRewardAccruedDownscaledNat slot0 accrued))
      (evm' := evmBase) ?hite ?_
    · refine ExecStmt.iteFalse
        (evalExpr_getRewardAccrued_shouldUpscale_false evmBase I slot0 multiplier accrued
          hshould)
        ?_
      refine ExecBlock.consNormal ?hassign ExecBlock.nil
      exact ExecStmt.assign
        (evalExpr_getRewardAccrued_downscaled evmBase I slot0 multiplier accrued hrescaleNZ)
        (assignGetRewardAccrued_downscaled evmBase I slot0 multiplier accrued)
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert
      (evalExpr_getRewardAccrued_scaled_assigned_revert evmBase I slot0 multiplier accrued
        (getRewardAccruedDownscaledNat slot0 accrued) hover))
  exact execBlock_append hcallBlock hrest

theorem evalExpr_getRewardOwed_claimed_afterAccrue
    (evm evmAcc : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := getRewardOwedAfterAccrueLocals evm I } evmAcc
      (.storage (rewardsClaimedRef (.var "comet") (.var "account"))) =
      .ok (.int (Int.ofNat (getRewardOwedClaimedLoad evmAcc I).toNat)) := by
  exact evalExpr_getRewardOwed_claimed_of evmAcc I
    (getRewardOwedAfterAccrueLocals_comet evm I)
    (getRewardOwedAfterAccrueLocals_account evm I)
    (getRewardOwedAfterAccrueLocals_no_rewardsClaimed evm I)

theorem evalExprs_getRewardOwed_getRewardAccruedArgs_afterClaimed
    (evm evmAcc : EVM.State) (I : ExecutionEnv) :
    evalExprs? config
      { contract := contract, locals := getRewardOwedAfterClaimedLocals evm evmAcc I }
      evmAcc
      [.var "comet", .var "account", .var "rescaleFactor",
        .var "shouldUpscale", .var "multiplier"] =
      .ok (getRewardAccruedArgs I (getRewardOwedSlot0Load evm I)
        (getRewardOwedMultiplierLoad evm I)) := by
  exact evalExprs_getRewardAccrued_args_of evmAcc I (getRewardOwedSlot0Load evm I)
    (getRewardOwedMultiplierLoad evm I)
    (getRewardOwedAfterClaimedLocals_comet evm evmAcc I)
    (getRewardOwedAfterClaimedLocals_account evm evmAcc I)
    (getRewardOwedAfterClaimedLocals_rescaleFactor evm evmAcc I)
    (getRewardOwedAfterClaimedLocals_shouldUpscale evm evmAcc I)
    (getRewardOwedAfterClaimedLocals_multiplier evm evmAcc I)

theorem evalExpr_getRewardOwed_owed_at
    (evm evmAcc evmRun : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    evalExpr? config
      { contract := contract, locals := getRewardOwedAfterInternalLocals evm evmAcc I accruedNat }
      evmRun
      (.ite (.binary .gt (.var "accrued") (.var "claimed"))
        (.binary .sub (.var "accrued") (.var "claimed"))
        (.intLit 0)) =
      .ok (.int (Int.ofNat (getRewardOwedOwedNat evmAcc I accruedNat))) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [getRewardOwedAfterInternalLocals_accrued,
    getRewardOwedAfterInternalLocals_claimed]
  by_cases hlt : (getRewardOwedClaimedLoad evmAcc I).toNat < accruedNat
  · have hgtInt : (↑(getRewardOwedClaimedLoad evmAcc I).toNat : Int) < ↑accruedNat := by
      exact_mod_cast hlt
    simp [evalBinaryOp?, hgtInt, getRewardOwedOwedNat, hlt]
    have hsub : (↑accruedNat - ↑(getRewardOwedClaimedLoad evmAcc I).toNat : Int) =
        ↑(accruedNat - (getRewardOwedClaimedLoad evmAcc I).toNat) := by
      omega
    rw [hsub]
  · have hgtFalse : ¬ (↑(getRewardOwedClaimedLoad evmAcc I).toNat : Int) < ↑accruedNat := by
      intro h
      exact hlt (by exact_mod_cast h)
    simp [evalBinaryOp?, hgtFalse, getRewardOwedOwedNat, hlt, pure]

theorem evalExpr_getRewardOwed_owed
    (evm evmAcc : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    evalExpr? config
      { contract := contract, locals := getRewardOwedAfterInternalLocals evm evmAcc I accruedNat }
      evmAcc
      (.ite (.binary .gt (.var "accrued") (.var "claimed"))
        (.binary .sub (.var "accrued") (.var "claimed"))
        (.intLit 0)) =
      .ok (.int (Int.ofNat (getRewardOwedOwedNat evmAcc I accruedNat))) := by
  exact evalExpr_getRewardOwed_owed_at evm evmAcc evmAcc I accruedNat

theorem evalExpr_getRewardOwed_returnTuple_at
    (evm evmAcc evmRun : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    evalExpr? config
      { contract := contract, locals := getRewardOwedAfterOwedLocals evm evmAcc I accruedNat }
      evmRun (.tupleLit [.var "token", .var "owed"]) =
      .ok (.tuple [getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I),
        .int (Int.ofNat (getRewardOwedOwedNat evmAcc I accruedNat))]) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, evalExprList?]
  rw [getRewardOwedAfterOwedLocals_token, getRewardOwedAfterOwedLocals_owed]
  rfl

theorem evalExpr_getRewardOwed_returnTuple
    (evm evmAcc : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    evalExpr? config
      { contract := contract, locals := getRewardOwedAfterOwedLocals evm evmAcc I accruedNat }
      evmAcc (.tupleLit [.var "token", .var "owed"]) =
      .ok (.tuple [getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I),
        .int (Int.ofNat (getRewardOwedOwedNat evmAcc I accruedNat))]) := by
  exact evalExpr_getRewardOwed_returnTuple_at evm evmAcc evmAcc I accruedNat

theorem cometRewardsGetRewardOwedBodyReturns_upscale
    (evm evmAcc evmBase : EVM.State) (I : ExecutionEnv) {accrueOut baseOut : ByteArray}
    {baseAccrued : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hnz : rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evm I) ≠ ⟨0⟩)
    (hguard :
      evalExpr? config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
        (.binary .gt (.extCodeSize (.var "comet")) (.intLit 0)) = .ok (.bool true))
    (hcallAccrue :
      typedCallViaEVM config evm (EVM.address (getRewardOwedCometTarget I))
        "accrueAccount" 0 (getRewardOwedAccrueAccountArgs I)
        (true, evmAcc, accrueOut) true)
    (hdecAccrue : config.externalABI.decode? "accrueAccount" accrueOut = some [])
    (hcallBase :
      typedCallViaEVM config evmAcc (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseTrackingAccrued" baseOut =
      some [.int (Int.ofNat baseAccrued.toNat)])
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 (getRewardOwedSlot0Load evm I) ≠ ⟨0⟩)
    (hup : getRewardAccruedUpscaledNat (getRewardOwedSlot0Load evm I) baseAccrued <
      UInt256.size)
    (hscaled : getRewardAccruedScaledNat (getRewardOwedMultiplierLoad evm I)
      (getRewardAccruedUpscaledNat (getRewardOwedSlot0Load evm I) baseAccrued) <
      UInt256.size) :
    ExecTransitionBody config contract evm (getRewardOwedStore I)
      getRewardOwedTransition.body
      (.returned
        { contract := contract,
          locals := getRewardOwedAfterOwedLocals evm evmAcc I
            (getRewardAccruedReturnNat (getRewardOwedMultiplierLoad evm I)
              (getRewardAccruedUpscaledNat (getRewardOwedSlot0Load evm I) baseAccrued)) }
        evmBase
        (some [.tuple
          [ getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I),
            .int (Int.ofNat (getRewardOwedOwedNat evmAcc I
              (getRewardAccruedReturnNat (getRewardOwedMultiplierLoad evm I)
                (getRewardAccruedUpscaledNat (getRewardOwedSlot0Load evm I)
                  baseAccrued)))) ]])) := by
  refine ExecFuncBody.execBlockRet ?_
  let accruedNat := getRewardAccruedReturnNat (getRewardOwedMultiplierLoad evm I)
    (getRewardAccruedUpscaledNat (getRewardOwedSlot0Load evm I) baseAccrued)
  have hcheckedSmall :
      ExecBlock config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
        (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
          [.var "account"] "_accrued")
        (.ok { contract := contract, locals := getRewardOwedAfterAccrueLocals evm I }
          evmAcc) := by
    simpa [checkedExternalCallStmts, getRewardOwedAfterAccrueLocals, collapseReturns]
      using checkedExternalCallVarSuccess (cfg := config) (C := contract)
        (evm := evm) (evm' := evmAcc) (locals := getRewardOwedConfigLocals evm I)
        (receiver := "comet") (retVar := "_accrued") (name := "accrueAccount")
        (target := getRewardOwedCometTarget I) (sendVal := 0)
        (args := [.var "account"]) (argVals := getRewardOwedAccrueAccountArgs I)
        (out := accrueOut) (perm := true) (value := [])
        hguard (getRewardOwedConfigLocals_comet evm I)
        (evalExprs_getRewardOwed_accrueAccountArgs_of evm I
          (getRewardOwedConfigLocals_account evm I))
        hcallAccrue hdecAccrue
  have hrest :
      ExecBlock config { contract := contract, locals := getRewardOwedAfterAccrueLocals evm I }
        evmAcc
        [ .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "account"))),
          .internalCall "getRewardAccrued"
            [ .var "comet", .var "account", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier" ] "accrued",
          .letDecl "owed" (some uint256)
            (.ite (.binary .gt (.var "accrued") (.var "claimed"))
              (.binary .sub (.var "accrued") (.var "claimed"))
              (.intLit 0)),
          .return [(.tupleLit [.var "token", .var "owed"])] ]
        (.returned
          { contract := contract,
            locals := getRewardOwedAfterOwedLocals evm evmAcc I accruedNat }
          evmBase
          (some [.tuple
            [ getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I),
              .int (Int.ofNat (getRewardOwedOwedNat evmAcc I accruedNat)) ]])) := by
    refine ExecBlock.consNormal
      (solm' := { contract := contract, locals := getRewardOwedAfterClaimedLocals evm evmAcc I })
      (evm' := evmAcc) ?hclaimed ?_
    · exact ExecStmt.letDecl (evalExpr_getRewardOwed_claimed_afterAccrue evm evmAcc I)
    refine ExecBlock.consNormal
      (solm' := { contract := contract, locals := getRewardOwedAfterInternalLocals evm evmAcc I accruedNat })
      (evm' := evmBase) ?hinternal ?_
    · simpa [resumeAfterInternalCall, getRewardOwedAfterInternalLocals, collapseReturns]
        using internalCallFunctionReturn
        (cfg := config)
        (caller := { contract := contract, locals := getRewardOwedAfterClaimedLocals evm evmAcc I })
        (evm := evmAcc) (calleeEvm := evmBase)
        (name := "getRewardAccrued") (retVar := "accrued")
        (args := [.var "comet", .var "account", .var "rescaleFactor",
          .var "shouldUpscale", .var "multiplier"])
        (argVals := getRewardAccruedArgs I (getRewardOwedSlot0Load evm I)
          (getRewardOwedMultiplierLoad evm I))
        (callee := getRewardAccruedFunction)
        (locals := getRewardAccruedStore I (getRewardOwedSlot0Load evm I)
          (getRewardOwedMultiplierLoad evm I))
        (calleeSolm := getRewardAccruedAfterAssignedScaledFrame I
          (getRewardOwedSlot0Load evm I) (getRewardOwedMultiplierLoad evm I) baseAccrued
          (getRewardAccruedUpscaledNat (getRewardOwedSlot0Load evm I) baseAccrued))
        (value := some [.int (Int.ofNat accruedNat)])
        (evalExprs_getRewardOwed_getRewardAccruedArgs_afterClaimed evm evmAcc I)
        lookupCallable_getRewardAccrued
        (bindParams_getRewardAccrued I (getRewardOwedSlot0Load evm I)
          (getRewardOwedMultiplierLoad evm I))
        (by
          dsimp [accruedNat]
          exact getRewardAccruedBodyReturns_upscale evmAcc evmBase I
            (getRewardOwedSlot0Load evm I) (getRewardOwedMultiplierLoad evm I)
            baseAccrued hcallBase hdecBase hshould hup hscaled)
    refine ExecBlock.consNormal
      (solm' := { contract := contract, locals := getRewardOwedAfterOwedLocals evm evmAcc I accruedNat })
      (evm' := evmBase) ?howed ?_
    · exact ExecStmt.letDecl
        (evalExpr_getRewardOwed_owed_at evm evmAcc evmBase I accruedNat)
    exact ExecBlock.consReturn
      (ExecStmt.return (evalExprs?_singleton
        (evalExpr_getRewardOwed_returnTuple_at evm evmAcc evmBase I accruedNat)))
  have htail :
      ExecBlock config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
        (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
          [.var "account"] "_accrued" ++
        [ .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "account"))),
          .internalCall "getRewardAccrued"
            [ .var "comet", .var "account", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier" ] "accrued",
          .letDecl "owed" (some uint256)
            (.ite (.binary .gt (.var "accrued") (.var "claimed"))
              (.binary .sub (.var "accrued") (.var "claimed"))
              (.intLit 0)),
          .return [(.tupleLit [.var "token", .var "owed"])] ])
        (.returned
          { contract := contract,
            locals := getRewardOwedAfterOwedLocals evm evmAcc I accruedNat }
          evmBase
          (some [.tuple
            [ getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I),
              .int (Int.ofNat (getRewardOwedOwedNat evmAcc I accruedNat)) ]])) := by
    exact execBlock_append hcheckedSmall hrest
  have hprefix :
      ABlock config evm { contract := contract, locals := getRewardOwedStore I }
        getRewardOwedTransition.body
        { contract := contract, locals := getRewardOwedConfigLocals evm I }
        (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
          [.var "account"] "_accrued" ++
        [ .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "account"))),
          .internalCall "getRewardAccrued"
            [ .var "comet", .var "account", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier" ] "accrued",
          .letDecl "owed" (some uint256)
            (.ite (.binary .gt (.var "accrued") (.var "claimed"))
              (.binary .sub (.var "accrued") (.var "claimed"))
              (.intLit 0)),
          .return [(.tupleLit [.var "token", .var "owed"])] ]) := by
    simpa [getRewardOwedTransition, externalEntryGuard, nonpayable, calldataSizeGuard,
      checkedExternalCallStmts, getRewardOwedConfigLocals, getRewardOwedAfterShouldLocals,
      getRewardOwedAfterRescaleLocals, getRewardOwedAfterTokenLocals,
      getRewardOwedBaseLocals] using
      (((((((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (getRewardOwedStore I) hsize)).letStep
          (evalExpr_getRewardOwed_token_of evm I (getRewardOwedFrame_comet evm I)
            (getRewardOwedFrame_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_rescale_of evm I
            (getRewardOwedAfterTokenLocals_comet evm I)
            (getRewardOwedAfterTokenLocals_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_shouldUpscale_of evm I
            (getRewardOwedAfterRescaleLocals_comet evm I)
            (getRewardOwedAfterRescaleLocals_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_multiplier_of evm I
            (getRewardOwedAfterShouldLocals_comet evm I)
            (getRewardOwedAfterShouldLocals_no_rewardConfig evm I))).requireStep
            (evalExpr_getRewardOwed_token_ne_zero_true_of evm (getRewardOwedSlot0Load evm I)
              (getRewardOwedConfigLocals_token evm I) hnz)
  exact hprefix.run htail

theorem cometRewardsGetRewardOwedBodyReturns_downscale
    (evm evmAcc evmBase : EVM.State) (I : ExecutionEnv) {accrueOut baseOut : ByteArray}
    {baseAccrued : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hnz : rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evm I) ≠ ⟨0⟩)
    (hguard :
      evalExpr? config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
        (.binary .gt (.extCodeSize (.var "comet")) (.intLit 0)) = .ok (.bool true))
    (hcallAccrue :
      typedCallViaEVM config evm (EVM.address (getRewardOwedCometTarget I))
        "accrueAccount" 0 (getRewardOwedAccrueAccountArgs I)
        (true, evmAcc, accrueOut) true)
    (hdecAccrue : config.externalABI.decode? "accrueAccount" accrueOut = some [])
    (hcallBase :
      typedCallViaEVM config evmAcc (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseTrackingAccrued" baseOut =
      some [.int (Int.ofNat baseAccrued.toNat)])
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 (getRewardOwedSlot0Load evm I) = ⟨0⟩)
    (hrescaleNZ : rewardConfigRescaleFromSlot0 (getRewardOwedSlot0Load evm I) ≠ ⟨0⟩)
    (hscaled : getRewardAccruedScaledNat (getRewardOwedMultiplierLoad evm I)
      (getRewardAccruedDownscaledNat (getRewardOwedSlot0Load evm I) baseAccrued) <
      UInt256.size) :
    ExecTransitionBody config contract evm (getRewardOwedStore I)
      getRewardOwedTransition.body
      (.returned
        { contract := contract,
          locals := getRewardOwedAfterOwedLocals evm evmAcc I
            (getRewardAccruedReturnNat (getRewardOwedMultiplierLoad evm I)
              (getRewardAccruedDownscaledNat (getRewardOwedSlot0Load evm I) baseAccrued)) }
        evmBase
        (some [.tuple
          [ getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I),
            .int (Int.ofNat (getRewardOwedOwedNat evmAcc I
              (getRewardAccruedReturnNat (getRewardOwedMultiplierLoad evm I)
                (getRewardAccruedDownscaledNat (getRewardOwedSlot0Load evm I)
                  baseAccrued)))) ]])) := by
  refine ExecFuncBody.execBlockRet ?_
  let accruedNat := getRewardAccruedReturnNat (getRewardOwedMultiplierLoad evm I)
    (getRewardAccruedDownscaledNat (getRewardOwedSlot0Load evm I) baseAccrued)
  have hcheckedSmall :
      ExecBlock config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
        (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
          [.var "account"] "_accrued")
        (.ok { contract := contract, locals := getRewardOwedAfterAccrueLocals evm I }
          evmAcc) := by
    simpa [checkedExternalCallStmts, getRewardOwedAfterAccrueLocals, collapseReturns]
      using checkedExternalCallVarSuccess (cfg := config) (C := contract)
        (evm := evm) (evm' := evmAcc) (locals := getRewardOwedConfigLocals evm I)
        (receiver := "comet") (retVar := "_accrued") (name := "accrueAccount")
        (target := getRewardOwedCometTarget I) (sendVal := 0)
        (args := [.var "account"]) (argVals := getRewardOwedAccrueAccountArgs I)
        (out := accrueOut) (perm := true) (value := [])
        hguard (getRewardOwedConfigLocals_comet evm I)
        (evalExprs_getRewardOwed_accrueAccountArgs_of evm I
          (getRewardOwedConfigLocals_account evm I))
        hcallAccrue hdecAccrue
  have hrest :
      ExecBlock config { contract := contract, locals := getRewardOwedAfterAccrueLocals evm I }
        evmAcc
        [ .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "account"))),
          .internalCall "getRewardAccrued"
            [ .var "comet", .var "account", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier" ] "accrued",
          .letDecl "owed" (some uint256)
            (.ite (.binary .gt (.var "accrued") (.var "claimed"))
              (.binary .sub (.var "accrued") (.var "claimed"))
              (.intLit 0)),
          .return [(.tupleLit [.var "token", .var "owed"])] ]
        (.returned
          { contract := contract,
            locals := getRewardOwedAfterOwedLocals evm evmAcc I accruedNat }
          evmBase
          (some [.tuple
            [ getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I),
              .int (Int.ofNat (getRewardOwedOwedNat evmAcc I accruedNat)) ]])) := by
    refine ExecBlock.consNormal
      (solm' := { contract := contract, locals := getRewardOwedAfterClaimedLocals evm evmAcc I })
      (evm' := evmAcc) ?hclaimed ?_
    · exact ExecStmt.letDecl (evalExpr_getRewardOwed_claimed_afterAccrue evm evmAcc I)
    refine ExecBlock.consNormal
      (solm' := { contract := contract, locals := getRewardOwedAfterInternalLocals evm evmAcc I accruedNat })
      (evm' := evmBase) ?hinternal ?_
    · simpa [resumeAfterInternalCall, getRewardOwedAfterInternalLocals, collapseReturns]
        using internalCallFunctionReturn
        (cfg := config)
        (caller := { contract := contract, locals := getRewardOwedAfterClaimedLocals evm evmAcc I })
        (evm := evmAcc) (calleeEvm := evmBase)
        (name := "getRewardAccrued") (retVar := "accrued")
        (args := [.var "comet", .var "account", .var "rescaleFactor",
          .var "shouldUpscale", .var "multiplier"])
        (argVals := getRewardAccruedArgs I (getRewardOwedSlot0Load evm I)
          (getRewardOwedMultiplierLoad evm I))
        (callee := getRewardAccruedFunction)
        (locals := getRewardAccruedStore I (getRewardOwedSlot0Load evm I)
          (getRewardOwedMultiplierLoad evm I))
        (calleeSolm := getRewardAccruedAfterAssignedScaledFrame I
          (getRewardOwedSlot0Load evm I) (getRewardOwedMultiplierLoad evm I) baseAccrued
          (getRewardAccruedDownscaledNat (getRewardOwedSlot0Load evm I) baseAccrued))
        (value := some [.int (Int.ofNat accruedNat)])
        (evalExprs_getRewardOwed_getRewardAccruedArgs_afterClaimed evm evmAcc I)
        lookupCallable_getRewardAccrued
        (bindParams_getRewardAccrued I (getRewardOwedSlot0Load evm I)
          (getRewardOwedMultiplierLoad evm I))
        (by
          dsimp [accruedNat]
          exact getRewardAccruedBodyReturns_downscale evmAcc evmBase I
            (getRewardOwedSlot0Load evm I) (getRewardOwedMultiplierLoad evm I)
            baseAccrued hcallBase hdecBase hshould hrescaleNZ hscaled)
    refine ExecBlock.consNormal
      (solm' := { contract := contract, locals := getRewardOwedAfterOwedLocals evm evmAcc I accruedNat })
      (evm' := evmBase) ?howed ?_
    · exact ExecStmt.letDecl
        (evalExpr_getRewardOwed_owed_at evm evmAcc evmBase I accruedNat)
    exact ExecBlock.consReturn
      (ExecStmt.return (evalExprs?_singleton
        (evalExpr_getRewardOwed_returnTuple_at evm evmAcc evmBase I accruedNat)))
  have htail :
      ExecBlock config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
        (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
          [.var "account"] "_accrued" ++
        [ .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "account"))),
          .internalCall "getRewardAccrued"
            [ .var "comet", .var "account", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier" ] "accrued",
          .letDecl "owed" (some uint256)
            (.ite (.binary .gt (.var "accrued") (.var "claimed"))
              (.binary .sub (.var "accrued") (.var "claimed"))
              (.intLit 0)),
          .return [(.tupleLit [.var "token", .var "owed"])] ])
        (.returned
          { contract := contract,
            locals := getRewardOwedAfterOwedLocals evm evmAcc I accruedNat }
          evmBase
          (some [.tuple
            [ getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I),
              .int (Int.ofNat (getRewardOwedOwedNat evmAcc I accruedNat)) ]])) := by
    exact execBlock_append hcheckedSmall hrest
  have hprefix :
      ABlock config evm { contract := contract, locals := getRewardOwedStore I }
        getRewardOwedTransition.body
        { contract := contract, locals := getRewardOwedConfigLocals evm I }
        (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
          [.var "account"] "_accrued" ++
        [ .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "account"))),
          .internalCall "getRewardAccrued"
            [ .var "comet", .var "account", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier" ] "accrued",
          .letDecl "owed" (some uint256)
            (.ite (.binary .gt (.var "accrued") (.var "claimed"))
              (.binary .sub (.var "accrued") (.var "claimed"))
              (.intLit 0)),
          .return [(.tupleLit [.var "token", .var "owed"])] ]) := by
    simpa [getRewardOwedTransition, externalEntryGuard, nonpayable, calldataSizeGuard,
      checkedExternalCallStmts, getRewardOwedConfigLocals, getRewardOwedAfterShouldLocals,
      getRewardOwedAfterRescaleLocals, getRewardOwedAfterTokenLocals,
      getRewardOwedBaseLocals] using
      (((((((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (getRewardOwedStore I) hsize)).letStep
          (evalExpr_getRewardOwed_token_of evm I (getRewardOwedFrame_comet evm I)
            (getRewardOwedFrame_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_rescale_of evm I
            (getRewardOwedAfterTokenLocals_comet evm I)
            (getRewardOwedAfterTokenLocals_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_shouldUpscale_of evm I
            (getRewardOwedAfterRescaleLocals_comet evm I)
            (getRewardOwedAfterRescaleLocals_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_multiplier_of evm I
            (getRewardOwedAfterShouldLocals_comet evm I)
            (getRewardOwedAfterShouldLocals_no_rewardConfig evm I))).requireStep
            (evalExpr_getRewardOwed_token_ne_zero_true_of evm (getRewardOwedSlot0Load evm I)
              (getRewardOwedConfigLocals_token evm I) hnz)
  exact hprefix.run htail

theorem getRewardOwedRewardConfigSlotOf_eq_solc (I : ExecutionEnv)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus) :
    getRewardOwedRewardConfigSlotOf I =
      solcMappingSlot ⟨1⟩ (getRewardOwedCometWord I) := by
  unfold getRewardOwedRewardConfigSlotOf rewardConfigSlot
  rw [keyValueToWord_address_of_canonical _ hcanonComet]
  rfl

theorem getRewardOwedRewardsClaimedSlotOf_eq_solc (I : ExecutionEnv)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (getRewardOwedAccountWord I).toNat < EVM.addressModulus) :
    getRewardOwedRewardsClaimedSlotOf I =
      solcMappingSlot (solcMappingSlot ⟨2⟩ (getRewardOwedCometWord I))
        (getRewardOwedAccountWord I) := by
  unfold getRewardOwedRewardsClaimedSlotOf rewardsClaimedSlot rewardsClaimedCometSlot
  rw [keyValueToWord_address_of_canonical _ hcanonComet,
    keyValueToWord_address_of_canonical _ hcanonAccount]
  rfl

theorem wordAt0Mem_size_of_ge {mem : ByteArray} (word : UInt256)
    (hmem : 32 ≤ mem.size) :
    (wordAt0Mem word mem).size = mem.size := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem wordAt32Mem_size_of_ge {mem : ByteArray} (word : UInt256)
    (hmem : 64 ≤ mem.size) :
    (wordAt32Mem word mem).size = mem.size := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem twoWordHashMem_size_of_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem
  rw [wordAt32Mem_size_of_ge slot (by
    rw [wordAt0Mem_size_of_ge key (by omega)]
    exact hmem)]
  exact wordAt0Mem_size_of_ge key (by omega)

theorem twoWordHashMem_read0_of_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 = UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge key (by omega)]; omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read32_of_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge key (by omega)]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

set_option maxHeartbeats 800000 in
theorem twoWordHashMem_read0_64_of_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [twoWordHashMem_size_of_ge key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [twoWordHashMem_size_of_ge key slot hmem]; omega),
      twoWordHashMem_read0_of_ge key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [twoWordHashMem_size_of_ge key slot hmem]; omega),
      twoWordHashMem_read32_of_ge key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem twoWordHashMem_read64_of_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge key (by omega)]; omega) (by omega)
      (by rw [wordAt0Mem_size_of_ge key (by omega)]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega)
      (by omega) (by omega)]

theorem twoWordHashMem_solcMappingSlot_of_ge (baseSlot key : UInt256)
    {mem : ByteArray} (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_of_ge key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

noncomputable abbrev getRewardOwedAlloc64Mem : ByteArray :=
  writeWord solcFreePtrMem 64 (⟨192⟩ : UInt256)

noncomputable abbrev getRewardOwedConfigZeroMem : ByteArray :=
  writeCascade getRewardOwedAlloc64Mem [(128, (⟨0⟩ : UInt256)), (160, (⟨0⟩ : UInt256))]

noncomputable abbrev getRewardOwedRewardConfigHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (getRewardOwedCometWord I) ⟨1⟩ getRewardOwedConfigZeroMem

noncomputable abbrev getRewardOwedConfigAllocMem (I : ExecutionEnv) : ByteArray :=
  writeWord (getRewardOwedRewardConfigHashMem I) 64 (⟨320⟩ : UInt256)

noncomputable abbrev getRewardOwedConfigTokenMem
    (I : ExecutionEnv) (slot0 : UInt256) : ByteArray :=
  writeWord (getRewardOwedConfigAllocMem I) 192 (rewardConfigTokenFromSlot0 slot0)

noncomputable abbrev getRewardOwedConfigRescaleMem
    (I : ExecutionEnv) (slot0 : UInt256) : ByteArray :=
  writeWord (getRewardOwedConfigTokenMem I slot0) 224 (rewardConfigRescaleFromSlot0 slot0)

noncomputable abbrev getRewardOwedConfigShouldMem
    (I : ExecutionEnv) (slot0 : UInt256) : ByteArray :=
  writeWord (getRewardOwedConfigRescaleMem I slot0) 256
    (rewardConfigShouldUpscaleFromSlot0 slot0)

noncomputable abbrev getRewardOwedConfigMultiplierMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) : ByteArray :=
  writeWord (getRewardOwedConfigShouldMem I slot0) 288 multiplier

noncomputable abbrev getRewardOwedInvalidRewardConfigSelectorMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) : ByteArray :=
  writeWord (getRewardOwedConfigMultiplierMem I slot0 multiplier) 320
    (UInt256.shiftLeft (⟨1311535579⟩ : UInt256) ⟨225⟩)

noncomputable abbrev getRewardOwedInvalidRewardConfigArgMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) : ByteArray :=
  writeWord (getRewardOwedInvalidRewardConfigSelectorMem I slot0 multiplier) 324
    (getRewardOwedCometWord I)

noncomputable abbrev getRewardOwedAccrueAccountSelectorMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) : ByteArray :=
  writeWord (getRewardOwedConfigMultiplierMem I slot0 multiplier) 320
    (UInt256.shiftLeft (⟨3219561613⟩ : UInt256) ⟨224⟩)

noncomputable abbrev getRewardOwedAccrueAccountCalldataMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) : ByteArray :=
  writeWord (getRewardOwedAccrueAccountSelectorMem I slot0 multiplier) 324
    (getRewardOwedAccountWord I)

abbrev getRewardOwedAccrueAccountPostCallTail (I : ExecutionEnv) : List UInt256 :=
  [ ⟨320⟩,
    UInt256.land (getRewardOwedAccountWord I) solcAddrMask,
    getRewardOwedAccountWord I,
    getRewardOwedCometWord I,
    ⟨0⟩,
    UInt256.land (getRewardOwedCometWord I) solcAddrMask,
    solcAddrMask,
    ⟨32⟩,
    ⟨192⟩,
    ⟨64⟩ ]

abbrev getRewardOwedAccrueAccountPostCallStack (z : Bool) (I : ExecutionEnv) :
    List UInt256 :=
  (if z then ⟨1⟩ else ⟨0⟩) :: getRewardOwedAccrueAccountPostCallTail I

noncomputable abbrev getRewardOwedAccrueAccountPostCallMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (out : ByteArray) : ByteArray :=
  out.write 0 (getRewardOwedAccrueAccountCalldataMem I slot0 multiplier) 320
    (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat

abbrev getRewardOwedAccrueAccountPostCallAw : UInt256 :=
  UInt256.ofNat (MachineState.M
    (MachineState.M (UInt256.ofNat 12).toNat (⟨320⟩ : UInt256).toNat
      getRewardOwedAccrueAccountCallSize.toNat)
    (⟨320⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat)

noncomputable abbrev getRewardOwedAccrueAccountAfterAllocMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (out : ByteArray) : ByteArray :=
  writeWord (getRewardOwedAccrueAccountPostCallMem I slot0 multiplier out) 64
    (⟨320⟩ : UInt256)

noncomputable abbrev getRewardOwedClaimedInnerHashMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (out : ByteArray) : ByteArray :=
  twoWordHashMem (UInt256.land (getRewardOwedCometWord I) solcAddrMask) ⟨2⟩
    (getRewardOwedAccrueAccountAfterAllocMem I slot0 multiplier out)

noncomputable abbrev getRewardOwedClaimedOuterHashMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (out : ByteArray) : ByteArray :=
  twoWordHashMem (UInt256.land (getRewardOwedAccountWord I) solcAddrMask)
    (solcMappingSlot ⟨2⟩ (UInt256.land (getRewardOwedCometWord I) solcAddrMask))
    (getRewardOwedClaimedInnerHashMem I slot0 multiplier out)

noncomputable abbrev getRewardOwedBaseTrackingSelectorMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (out : ByteArray) : ByteArray :=
  writeWord (getRewardOwedClaimedOuterHashMem I slot0 multiplier out) 320
    (UInt256.shiftLeft (⟨719776253⟩ : UInt256) ⟨226⟩)

noncomputable abbrev getRewardOwedBaseTrackingCalldataMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (out : ByteArray) : ByteArray :=
  writeWord (getRewardOwedBaseTrackingSelectorMem I slot0 multiplier out) 324
    (getRewardOwedAccountWord I)

abbrev getRewardOwedBaseTrackingPostCallTail (claimed : UInt256) : List UInt256 :=
  [ ⟨192⟩,
    ⟨320⟩,
    ⟨2499⟩,
    claimed,
    ⟨0⟩,
    solcAddrMask,
    ⟨32⟩,
    ⟨192⟩,
    ⟨64⟩ ]

abbrev getRewardOwedBaseTrackingPostCallStack (z : Bool) (claimed : UInt256) :
    List UInt256 :=
  (if z then ⟨1⟩ else ⟨0⟩) :: getRewardOwedBaseTrackingPostCallTail claimed

abbrev getRewardOwedBaseTrackingCallAw : UInt256 :=
  getRewardOwedAccrueAccountPostCallAw

noncomputable abbrev getRewardOwedBaseTrackingPostCallMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accrueOut baseOut : ByteArray) :
    ByteArray :=
  baseOut.write 0 (getRewardOwedBaseTrackingCalldataMem I slot0 multiplier accrueOut) 320
    (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat

abbrev getRewardOwedBaseTrackingPostCallAw : UInt256 :=
  UInt256.ofNat (MachineState.M
    (MachineState.M getRewardOwedBaseTrackingCallAw.toNat
      (⟨320⟩ : UInt256).toNat getRewardOwedBaseTrackingCallSize.toNat)
    (⟨320⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat)

abbrev getRewardOwedBaseTrackingReturnWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

noncomputable abbrev getRewardOwedBaseTrackingPostDecodeMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accrueOut baseOut : ByteArray) :
    ByteArray :=
  writeWord (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut) 64
    (⟨352⟩ : UInt256)

noncomputable abbrev getRewardOwedBaseTrackingPostShortDecodeMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accrueOut baseOut : ByteArray) :
    ByteArray :=
  writeWord (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut) 64
    ((⟨320⟩ : UInt256) +
      UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat baseOut.size + ⟨31⟩))

def getRewardOwedReturnBytes (token owed : UInt256) : ByteArray :=
  UInt256.toByteArray token ++ UInt256.toByteArray owed

abbrev getRewardOwedReturnOwedWord (claimed accrued : UInt256) : UInt256 :=
  if claimed.toNat < accrued.toNat then
    UInt256.ofNat (accrued.toNat - claimed.toNat)
  else
    ⟨0⟩

noncomputable abbrev getRewardOwedReturnAllocMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accrueOut baseOut : ByteArray) :
    ByteArray :=
  writeWord (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut) 64
    (⟨416⟩ : UInt256)

noncomputable abbrev getRewardOwedReturnStructTokenMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accrueOut baseOut : ByteArray) :
    ByteArray :=
  writeWord (getRewardOwedReturnAllocMem I slot0 multiplier accrueOut baseOut) 352
    (rewardConfigTokenFromSlot0 slot0)

noncomputable abbrev getRewardOwedReturnStructOwedMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accrueOut baseOut : ByteArray)
    (owed : UInt256) :
    ByteArray :=
  writeWord (getRewardOwedReturnStructTokenMem I slot0 multiplier accrueOut baseOut) 384 owed

noncomputable abbrev getRewardOwedReturnCopyTokenMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accrueOut baseOut : ByteArray)
    (owed : UInt256) :
    ByteArray :=
  writeWord (getRewardOwedReturnStructOwedMem I slot0 multiplier accrueOut baseOut owed) 416
    (rewardConfigTokenFromSlot0 slot0)

noncomputable abbrev getRewardOwedReturnMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accrueOut baseOut : ByteArray)
    (owed : UInt256) :
    ByteArray :=
  writeWord (getRewardOwedReturnCopyTokenMem I slot0 multiplier accrueOut baseOut owed) 448 owed

theorem getRewardOwedAlloc64Mem_size :
    getRewardOwedAlloc64Mem.size = 96 := by
  simpa [getRewardOwedAlloc64Mem, solcFreePtrMem_size] using
    writeWord_size solcFreePtrMem 64 (⟨192⟩ : UInt256)
      (by rw [solcFreePtrMem_size]; native_decide)

theorem getRewardOwedConfigZeroMem_size :
    getRewardOwedConfigZeroMem.size = 192 := by
  simpa [getRewardOwedConfigZeroMem] using
    writeCascade_size_of_base getRewardOwedAlloc64Mem
      [(128, (⟨0⟩ : UInt256)), (160, (⟨0⟩ : UInt256))]
      getRewardOwedAlloc64Mem_size
      (by
        dsimp [WriteGapsOk]
        constructor
        · native_decide
        constructor
        · native_decide
        · trivial)
      (by native_decide)

theorem getRewardOwedAlloc64Mem_read64 :
    getRewardOwedAlloc64Mem.readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  simpa [getRewardOwedAlloc64Mem] using
    writeWord_read_back solcFreePtrMem 64 (⟨192⟩ : UInt256)
      (by rw [solcFreePtrMem_size]; native_decide)

theorem getRewardOwedConfigZeroMem_read64 :
    getRewardOwedConfigZeroMem.readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  rw [getRewardOwedConfigZeroMem]
  rw [writeCascade_read_preserved_of_base getRewardOwedAlloc64Mem
    [(128, (⟨0⟩ : UInt256)), (160, (⟨0⟩ : UInt256))]
    getRewardOwedAlloc64Mem_size (by
      dsimp [WindowDisjointFromWrites]
      constructor
      · native_decide
      constructor
      · left
        constructor <;> norm_num
      constructor
      · native_decide
      constructor
      · left
        constructor <;> norm_num
      · trivial)]
  exact getRewardOwedAlloc64Mem_read64

theorem getRewardOwedRewardConfigHashMem_keccakSlot (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((getRewardOwedRewardConfigHashMem I).readWithPadding 0 64))) =
      solcMappingSlot ⟨1⟩ (getRewardOwedCometWord I) := by
  unfold getRewardOwedRewardConfigHashMem
  exact twoWordHashMem_solcMappingSlot_of_ge ⟨1⟩ (getRewardOwedCometWord I)
    (by rw [getRewardOwedConfigZeroMem_size]; decide)

theorem getRewardOwedRewardConfigHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (getRewardOwedRewardConfigHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((getRewardOwedRewardConfigHashMem I).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨192⟩ := by
  have hsizeHash : (getRewardOwedRewardConfigHashMem I).size = 192 := by
    unfold getRewardOwedRewardConfigHashMem
    rw [twoWordHashMem_size_of_ge]
    · exact getRewardOwedConfigZeroMem_size
    · rw [getRewardOwedConfigZeroMem_size]
      decide
  have hread :
      (getRewardOwedRewardConfigHashMem I).readWithPadding 64 32 =
        UInt256.toByteArray (⟨192⟩ : UInt256) := by
    unfold getRewardOwedRewardConfigHashMem
    rw [twoWordHashMem_read64_of_ge]
    · exact getRewardOwedConfigZeroMem_read64
    · rw [getRewardOwedConfigZeroMem_size]
      decide
  rw [if_neg]
  · rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hread,
      fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]
  · rw [hsizeHash]
    native_decide

theorem getRewardOwedConfigAllocMem_size (I : ExecutionEnv) :
    (getRewardOwedConfigAllocMem I).size = 192 := by
  have hhash : (getRewardOwedRewardConfigHashMem I).size = 192 := by
    unfold getRewardOwedRewardConfigHashMem
    rw [twoWordHashMem_size_of_ge]
    · exact getRewardOwedConfigZeroMem_size
    · rw [getRewardOwedConfigZeroMem_size]
      decide
  unfold getRewardOwedConfigAllocMem
  rw [writeWord_size]
  · rw [hhash]
    native_decide
  · rw [hhash]
    native_decide

theorem getRewardOwedConfigAllocMem_read64 (I : ExecutionEnv) :
    (getRewardOwedConfigAllocMem I).readWithPadding 64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  have hhash : (getRewardOwedRewardConfigHashMem I).size = 192 := by
    unfold getRewardOwedRewardConfigHashMem
    rw [twoWordHashMem_size_of_ge]
    · exact getRewardOwedConfigZeroMem_size
    · rw [getRewardOwedConfigZeroMem_size]
      decide
  simpa [getRewardOwedConfigAllocMem] using
    writeWord_read_back (getRewardOwedRewardConfigHashMem I) 64 (⟨320⟩ : UInt256)
      (by rw [hhash]; native_decide)

theorem getRewardOwedConfigTokenMem_size (I : ExecutionEnv) (slot0 : UInt256) :
    (getRewardOwedConfigTokenMem I slot0).size = 224 := by
  unfold getRewardOwedConfigTokenMem
  rw [writeWord_size]
  · rw [getRewardOwedConfigAllocMem_size]
    native_decide
  · rw [getRewardOwedConfigAllocMem_size]
    native_decide

theorem getRewardOwedConfigRescaleMem_size (I : ExecutionEnv) (slot0 : UInt256) :
    (getRewardOwedConfigRescaleMem I slot0).size = 256 := by
  unfold getRewardOwedConfigRescaleMem
  rw [writeWord_size]
  · rw [getRewardOwedConfigTokenMem_size]
    native_decide
  · rw [getRewardOwedConfigTokenMem_size]
    native_decide

theorem getRewardOwedConfigShouldMem_size (I : ExecutionEnv) (slot0 : UInt256) :
    (getRewardOwedConfigShouldMem I slot0).size = 288 := by
  unfold getRewardOwedConfigShouldMem
  rw [writeWord_size]
  · rw [getRewardOwedConfigRescaleMem_size]
    native_decide
  · rw [getRewardOwedConfigRescaleMem_size]
    native_decide

theorem getRewardOwedConfigMultiplierMem_size
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (getRewardOwedConfigMultiplierMem I slot0 multiplier).size = 320 := by
  unfold getRewardOwedConfigMultiplierMem
  rw [writeWord_size]
  · rw [getRewardOwedConfigShouldMem_size]
    native_decide
  · rw [getRewardOwedConfigShouldMem_size]
    native_decide

theorem getRewardOwedConfigTokenMem_read64 (I : ExecutionEnv) (slot0 : UInt256) :
    (getRewardOwedConfigTokenMem I slot0).readWithPadding 64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  simpa [getRewardOwedConfigTokenMem] using
    writeWord_read_preserved (getRewardOwedConfigAllocMem I) 192 64
      (rewardConfigTokenFromSlot0 slot0)
      (by rw [getRewardOwedConfigAllocMem_size]; native_decide)
      (by
        left
        rw [getRewardOwedConfigAllocMem_size]
        constructor <;> norm_num)
      |>.trans (getRewardOwedConfigAllocMem_read64 I)

theorem getRewardOwedConfigRescaleMem_read64 (I : ExecutionEnv) (slot0 : UInt256) :
    (getRewardOwedConfigRescaleMem I slot0).readWithPadding 64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  simpa [getRewardOwedConfigRescaleMem] using
    writeWord_read_preserved (getRewardOwedConfigTokenMem I slot0) 224 64
      (rewardConfigRescaleFromSlot0 slot0)
      (by rw [getRewardOwedConfigTokenMem_size]; native_decide)
      (by
        left
        rw [getRewardOwedConfigTokenMem_size]
        constructor <;> norm_num)
      |>.trans (getRewardOwedConfigTokenMem_read64 I slot0)

theorem getRewardOwedConfigShouldMem_read64 (I : ExecutionEnv) (slot0 : UInt256) :
    (getRewardOwedConfigShouldMem I slot0).readWithPadding 64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  simpa [getRewardOwedConfigShouldMem] using
    writeWord_read_preserved (getRewardOwedConfigRescaleMem I slot0) 256 64
      (rewardConfigShouldUpscaleFromSlot0 slot0)
      (by rw [getRewardOwedConfigRescaleMem_size]; native_decide)
      (by
        left
        rw [getRewardOwedConfigRescaleMem_size]
        constructor <;> norm_num)
      |>.trans (getRewardOwedConfigRescaleMem_read64 I slot0)

theorem getRewardOwedConfigMultiplierMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (getRewardOwedConfigMultiplierMem I slot0 multiplier).readWithPadding 64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  simpa [getRewardOwedConfigMultiplierMem] using
    writeWord_read_preserved (getRewardOwedConfigShouldMem I slot0) 288 64 multiplier
      (by rw [getRewardOwedConfigShouldMem_size]; native_decide)
      (by
        left
        rw [getRewardOwedConfigShouldMem_size]
        constructor <;> norm_num)
      |>.trans (getRewardOwedConfigShouldMem_read64 I slot0)

theorem getRewardOwedConfigMultiplierMem_mload64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (getRewardOwedConfigMultiplierMem I slot0 multiplier).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((getRewardOwedConfigMultiplierMem I slot0 multiplier).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ := by
  rw [if_neg]
  · rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      getRewardOwedConfigMultiplierMem_read64,
      fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]
  · rw [getRewardOwedConfigMultiplierMem_size]
    native_decide

theorem getRewardOwedAccrueAccountSelectorMem_size
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (getRewardOwedAccrueAccountSelectorMem I slot0 multiplier).size = 352 := by
  unfold getRewardOwedAccrueAccountSelectorMem
  rw [writeWord_size]
  · rw [getRewardOwedConfigMultiplierMem_size]
    native_decide
  · rw [getRewardOwedConfigMultiplierMem_size]
    native_decide

theorem getRewardOwedAccrueAccountCalldataMem_size
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (getRewardOwedAccrueAccountCalldataMem I slot0 multiplier).size = 356 := by
  unfold getRewardOwedAccrueAccountCalldataMem
  rw [writeWord_size]
  · rw [getRewardOwedAccrueAccountSelectorMem_size]
    native_decide
  · rw [getRewardOwedAccrueAccountSelectorMem_size]
    native_decide

theorem getRewardOwedAccrueAccountCalldataMem_read320_4
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (getRewardOwedAccrueAccountCalldataMem I slot0 multiplier).readWithPadding 320 4 =
      accrueAccountSelector := by
  unfold getRewardOwedAccrueAccountCalldataMem
  unfold Reasoning.Theory.writeWord
  rw [write32_read_below_len _ _ 324 320 4 (by rw [toByteArray_size])
      (by rw [getRewardOwedAccrueAccountSelectorMem_size]; norm_num)
      (by norm_num)
      (by rw [getRewardOwedAccrueAccountSelectorMem_size]; norm_num)
      (by norm_num) (by norm_num)]
  unfold getRewardOwedAccrueAccountSelectorMem
  unfold Reasoning.Theory.writeWord
  rw [write32_read_prefix_len _ _ 320 4 (by rw [toByteArray_size])
      (by rw [getRewardOwedConfigMultiplierMem_size])
      (by norm_num) (by norm_num) (by norm_num)]
  native_decide

theorem getRewardOwedAccrueAccountCalldataMem_read324_32
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (getRewardOwedAccrueAccountCalldataMem I slot0 multiplier).readWithPadding 324 32 =
      UInt256.toByteArray (getRewardOwedAccountWord I) := by
  unfold getRewardOwedAccrueAccountCalldataMem
  unfold Reasoning.Theory.writeWord
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [getRewardOwedAccrueAccountSelectorMem_size]; norm_num)]
  rw [show (UInt256.toByteArray (getRewardOwedAccountWord I)).extract 0 32 =
      UInt256.toByteArray (getRewardOwedAccountWord I) by
    rw [show 32 = (UInt256.toByteArray (getRewardOwedAccountWord I)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem getRewardOwedAccrueAccountCalldataMem_read320_36
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (getRewardOwedAccrueAccountCalldataMem I slot0 multiplier).readWithPadding 320 36 =
      accrueAccountSelector ++ UInt256.toByteArray (getRewardOwedAccountWord I) := by
  rw [byteArray_readWithPadding_split _ 320 4 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by simp [getRewardOwedAccrueAccountCalldataMem_size])]
  rw [getRewardOwedAccrueAccountCalldataMem_read320_4,
    getRewardOwedAccrueAccountCalldataMem_read324_32]

set_option maxHeartbeats 1000000 in
theorem getRewardOwedAccrueAccountCalldataMem_encode_args
    (I : ExecutionEnv)
    (slot0 multiplier : UInt256)
    (hcanonAccount : (getRewardOwedAccountWord I).toNat < EVM.addressModulus) :
    config.externalABI.encode? "accrueAccount" (getRewardOwedAccrueAccountArgs I) =
      some ((getRewardOwedAccrueAccountCalldataMem I slot0 multiplier)
        |>.readWithPadding 320 getRewardOwedAccrueAccountCallSize.toNat) := by
  rw [show getRewardOwedAccrueAccountCallSize.toNat = 36 from rfl]
  rw [getRewardOwedAccrueAccountCalldataMem_read320_36]
  change compoundRewardsExternalABI.encode? "accrueAccount" (getRewardOwedAccrueAccountArgs I) =
    some (accrueAccountSelector ++ UInt256.toByteArray (getRewardOwedAccountWord I))
  have haccountWord :
      EVM.word (AccountAddress.ofNat (getRewardOwedAccountWord I).toNat).val =
        getRewardOwedAccountWord I := by
    change UInt256.ofNat (AccountAddress.ofNat (getRewardOwedAccountWord I).toNat).val =
      getRewardOwedAccountWord I
    have haddr :
        (AccountAddress.ofNat (getRewardOwedAccountWord I).toNat).val =
          (getRewardOwedAccountWord I).toNat := by
      have hcanonAddr : (getRewardOwedAccountWord I).toNat < AccountAddress.size := by
        simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanonAccount
      unfold AccountAddress.ofNat
      exact Nat.mod_eq_of_lt hcanonAddr
    rw [haddr]
    exact u256_ofNat_toNat (getRewardOwedAccountWord I)
  unfold compoundRewardsExternalABI ABI.encodeCallWithSelector? ABI.encodeABIValues?
  simp [getRewardOwedAccrueAccountArgs, getRewardOwedAccountValue, addr,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.encodeABIValuesFrom?, haccountWord,
    word_toBytesBE_toByteArray_eq_toByteArray]

theorem getRewardOwedPostCallLen_le_out_size {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat ≤ out.size := by
  by_cases houtSmall : out.size < 32
  · have hnotle : ¬ (⟨32⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      intro hle
      have hlev : (32 : Nat) ≤ (UInt256.ofNat out.size).toNat := by
        simpa [UInt256.toNat] using hle
      rw [UInt256.toNat_ofNat_of_lt houtSize] at hlev
      omega
    simp [min, hnotle, UInt256.toNat_ofNat_of_lt houtSize]
  · have hle : (⟨32⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      change (⟨32⟩ : UInt256).val ≤ (UInt256.ofNat out.size).val
      change (32 : Nat) ≤ (UInt256.ofNat out.size).toNat
      rw [UInt256.toNat_ofNat_of_lt houtSize]
      omega
    simp [min, hle]
    change (32 : Nat) ≤ out.size
    omega

theorem getRewardOwedAccrueAccountPostCallMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (getRewardOwedAccrueAccountPostCallMem I slot0 multiplier out).readWithPadding
        64 32 =
      UInt256.toByteArray ⟨320⟩ := by
  dsimp [getRewardOwedAccrueAccountPostCallMem]
  have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
    change (0 : Nat) ≤ (UInt256.ofNat out.size).toNat
    exact Nat.zero_le _
  rw [show (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 by
    simp [min, hle]]
  rw [byteArray_write_len_zero]
  unfold getRewardOwedAccrueAccountCalldataMem
  unfold Reasoning.Theory.writeWord
  rw [write32_read_below _ _ 324 64 (by rw [toByteArray_size])
    (by rw [getRewardOwedAccrueAccountSelectorMem_size]; norm_num)
    (by norm_num)]
  unfold getRewardOwedAccrueAccountSelectorMem
  exact (writeWord_read_preserved
    (getRewardOwedConfigMultiplierMem I slot0 multiplier) 320 64
    (UInt256.shiftLeft (⟨3219561613⟩ : UInt256) ⟨224⟩)
    (by rw [getRewardOwedConfigMultiplierMem_size]; native_decide)
    (by
      left
      rw [getRewardOwedConfigMultiplierMem_size]
      constructor <;> norm_num)).trans
    (getRewardOwedConfigMultiplierMem_read64 I slot0 multiplier)

theorem getRewardOwedAccrueAccountPostCallMem_size_ge320
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    320 ≤ (getRewardOwedAccrueAccountPostCallMem I slot0 multiplier out).size := by
  dsimp [getRewardOwedAccrueAccountPostCallMem]
  have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
    change (0 : Nat) ≤ (UInt256.ofNat out.size).toNat
    exact Nat.zero_le _
  rw [show (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 by
    simp [min, hle]]
  rw [byteArray_write_len_zero]
  rw [getRewardOwedAccrueAccountCalldataMem_size]
  norm_num

theorem getRewardOwedAccrueAccountAfterAllocMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (getRewardOwedAccrueAccountAfterAllocMem I slot0 multiplier out).readWithPadding
        64 32 =
      UInt256.toByteArray ⟨320⟩ := by
  unfold getRewardOwedAccrueAccountAfterAllocMem
  exact writeWord_read_back
    (getRewardOwedAccrueAccountPostCallMem I slot0 multiplier out) 64
    (⟨320⟩ : UInt256)
    (by
      have hge := getRewardOwedAccrueAccountPostCallMem_size_ge320
        I slot0 multiplier houtSize
      have hzero :
          64 - (getRewardOwedAccrueAccountPostCallMem I slot0 multiplier out).size = 0 := by
        omega
      rw [hzero]
      native_decide)

theorem getRewardOwedAccrueAccountAfterAllocMem_size_ge320
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    320 ≤ (getRewardOwedAccrueAccountAfterAllocMem I slot0 multiplier out).size := by
  unfold getRewardOwedAccrueAccountAfterAllocMem
  rw [writeWord_size]
  · have hge := getRewardOwedAccrueAccountPostCallMem_size_ge320
      I slot0 multiplier houtSize
    omega
  · have hge := getRewardOwedAccrueAccountPostCallMem_size_ge320
      I slot0 multiplier houtSize
    have hzero :
        64 - (getRewardOwedAccrueAccountPostCallMem I slot0 multiplier out).size = 0 := by
      omega
    rw [hzero]
    native_decide

theorem getRewardOwedClaimedInnerHashMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (getRewardOwedClaimedInnerHashMem I slot0 multiplier out).readWithPadding
        64 32 =
      UInt256.toByteArray ⟨320⟩ := by
  unfold getRewardOwedClaimedInnerHashMem
  rw [twoWordHashMem_read64_of_ge]
  · exact getRewardOwedAccrueAccountAfterAllocMem_read64 I slot0 multiplier houtSize
  · exact le_trans (by norm_num) <|
      getRewardOwedAccrueAccountAfterAllocMem_size_ge320 I slot0 multiplier houtSize

theorem getRewardOwedClaimedInnerHashMem_size_ge320
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    320 ≤ (getRewardOwedClaimedInnerHashMem I slot0 multiplier out).size := by
  unfold getRewardOwedClaimedInnerHashMem
  rw [twoWordHashMem_size_of_ge]
  · exact getRewardOwedAccrueAccountAfterAllocMem_size_ge320 I slot0 multiplier houtSize
  · exact le_trans (by norm_num) <|
      getRewardOwedAccrueAccountAfterAllocMem_size_ge320 I slot0 multiplier houtSize

theorem getRewardOwedClaimedOuterHashMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (getRewardOwedClaimedOuterHashMem I slot0 multiplier out).readWithPadding
        64 32 =
      UInt256.toByteArray ⟨320⟩ := by
  unfold getRewardOwedClaimedOuterHashMem
  rw [twoWordHashMem_read64_of_ge]
  · exact getRewardOwedClaimedInnerHashMem_read64 I slot0 multiplier houtSize
  · exact le_trans (by norm_num) <|
      getRewardOwedClaimedInnerHashMem_size_ge320 I slot0 multiplier houtSize

theorem getRewardOwedClaimedOuterHashMem_size_ge320
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    320 ≤ (getRewardOwedClaimedOuterHashMem I slot0 multiplier out).size := by
  unfold getRewardOwedClaimedOuterHashMem
  rw [twoWordHashMem_size_of_ge]
  · exact getRewardOwedClaimedInnerHashMem_size_ge320 I slot0 multiplier houtSize
  · exact le_trans (by norm_num) <|
      getRewardOwedClaimedInnerHashMem_size_ge320 I slot0 multiplier houtSize

theorem getRewardOwedClaimedOuterHashMem_mload64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (getRewardOwedClaimedOuterHashMem I slot0 multiplier out).size
        ∨ (⟨64⟩ : UInt256) ≥ getRewardOwedBaseTrackingCallAw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((getRewardOwedClaimedOuterHashMem I slot0 multiplier out).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨320⟩ := by
  apply mloadWordValue_of_readWithPadding
  · simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      (lt_of_lt_of_le (by norm_num : 64 < 320) <|
        getRewardOwedClaimedOuterHashMem_size_ge320 I slot0 multiplier houtSize)
  · native_decide
  · exact getRewardOwedClaimedOuterHashMem_read64 I slot0 multiplier houtSize

set_option maxHeartbeats 1000000 in
theorem getRewardOwedClaimedInnerHashMem_keccakSlot
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((getRewardOwedClaimedInnerHashMem I slot0 multiplier out)
          |>.readWithPadding 0 64))) =
      solcMappingSlot ⟨2⟩ (getRewardOwedCometWord I) := by
  unfold getRewardOwedClaimedInnerHashMem
  rw [twoWordHashMem_solcMappingSlot_of_ge]
  · exact congrArg (fun x => solcMappingSlot ⟨2⟩ x)
      (solcAddrMask_clean (by simpa [getRewardOwedCometWord, calldataWord] using hcanonComet))
  · exact le_trans (by norm_num) <|
      getRewardOwedAccrueAccountAfterAllocMem_size_ge320 I slot0 multiplier houtSize

set_option maxHeartbeats 1000000 in
theorem getRewardOwedClaimedOuterHashMem_keccakSlot
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (getRewardOwedAccountWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((getRewardOwedClaimedOuterHashMem I slot0 multiplier out)
          |>.readWithPadding 0 64))) =
      getRewardOwedRewardsClaimedSlotOf I := by
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((getRewardOwedClaimedOuterHashMem I slot0 multiplier out)
            |>.readWithPadding 0 64))) =
        solcMappingSlot
          (solcMappingSlot ⟨2⟩ (UInt256.land (getRewardOwedCometWord I) solcAddrMask))
          (UInt256.land (getRewardOwedAccountWord I) solcAddrMask) := by
    unfold getRewardOwedClaimedOuterHashMem
    exact twoWordHashMem_solcMappingSlot_of_ge
      (solcMappingSlot ⟨2⟩ (UInt256.land (getRewardOwedCometWord I) solcAddrMask))
      (UInt256.land (getRewardOwedAccountWord I) solcAddrMask)
      (le_trans (by norm_num) <|
        getRewardOwedClaimedInnerHashMem_size_ge320 I slot0 multiplier houtSize)
  rw [hhash]
  rw [solcAddrMask_clean
      (by simpa [getRewardOwedCometWord, calldataWord] using hcanonComet)]
  rw [solcAddrMask_clean
      (by simpa [getRewardOwedAccountWord, calldataWord] using hcanonAccount)]
  rw [getRewardOwedRewardsClaimedSlotOf_eq_solc I hcanonComet hcanonAccount]

theorem getRewardOwedBaseTrackingSelectorMem_size_ge352
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    352 ≤ (getRewardOwedBaseTrackingSelectorMem I slot0 multiplier out).size := by
  unfold getRewardOwedBaseTrackingSelectorMem
  have hsize := writeWord_size
    (getRewardOwedClaimedOuterHashMem I slot0 multiplier out) 320
    (UInt256.shiftLeft (⟨719776253⟩ : UInt256) ⟨226⟩)
    (by
      have hge := getRewardOwedClaimedOuterHashMem_size_ge320 I slot0 multiplier houtSize
      have hle : 320 -
          (getRewardOwedClaimedOuterHashMem I slot0 multiplier out).size = 0 := by
        omega
      rw [hle]
      native_decide)
  rw [hsize]
  exact le_max_right _ _

theorem getRewardOwedBaseTrackingCalldataMem_size_ge356
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    356 ≤ (getRewardOwedBaseTrackingCalldataMem I slot0 multiplier out).size := by
  unfold getRewardOwedBaseTrackingCalldataMem
  have hsize := writeWord_size
    (getRewardOwedBaseTrackingSelectorMem I slot0 multiplier out) 324
    (getRewardOwedAccountWord I)
    (by
      have hge := getRewardOwedBaseTrackingSelectorMem_size_ge352
        I slot0 multiplier houtSize
      have hle : 324 -
          (getRewardOwedBaseTrackingSelectorMem I slot0 multiplier out).size = 0 := by
        omega
      rw [hle]
      native_decide)
  rw [hsize]
  have hge := getRewardOwedBaseTrackingSelectorMem_size_ge352
    I slot0 multiplier houtSize
  omega

theorem getRewardOwedBaseTrackingCalldataMem_read320_4
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (getRewardOwedBaseTrackingCalldataMem I slot0 multiplier out).readWithPadding
        320 4 =
      baseTrackingAccruedSelector := by
  unfold getRewardOwedBaseTrackingCalldataMem
  unfold Reasoning.Theory.writeWord
  rw [write32_read_below_len _ _ 324 320 4 (by rw [toByteArray_size])
      (by
        have hge := getRewardOwedBaseTrackingSelectorMem_size_ge352
          I slot0 multiplier houtSize
        omega)
      (by norm_num)
      (by
        have hge := getRewardOwedBaseTrackingSelectorMem_size_ge352
          I slot0 multiplier houtSize
        omega)
      (by norm_num) (by norm_num)]
  unfold getRewardOwedBaseTrackingSelectorMem
  rw [writeWord_read_window
      (getRewardOwedClaimedOuterHashMem I slot0 multiplier out) 320 0 4
      (UInt256.shiftLeft (⟨719776253⟩ : UInt256) ⟨226⟩)
      (by norm_num) (by norm_num) (by norm_num)
      (by
        have hge := getRewardOwedClaimedOuterHashMem_size_ge320
          I slot0 multiplier houtSize
        have hle : 320 -
            (getRewardOwedClaimedOuterHashMem I slot0 multiplier out).size = 0 := by
          omega
        rw [hle]
        native_decide)]
  native_decide

theorem getRewardOwedBaseTrackingCalldataMem_read324_32
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (getRewardOwedBaseTrackingCalldataMem I slot0 multiplier out).readWithPadding
        324 32 =
      UInt256.toByteArray (getRewardOwedAccountWord I) := by
  unfold getRewardOwedBaseTrackingCalldataMem
  unfold Reasoning.Theory.writeWord
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by
        have hge := getRewardOwedBaseTrackingSelectorMem_size_ge352
          I slot0 multiplier houtSize
        omega)]
  exact toByteArray_extract_all (getRewardOwedAccountWord I)

theorem getRewardOwedBaseTrackingCalldataMem_read320_36
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (getRewardOwedBaseTrackingCalldataMem I slot0 multiplier out).readWithPadding
        320 36 =
      baseTrackingAccruedSelector ++ UInt256.toByteArray (getRewardOwedAccountWord I) := by
  rw [byteArray_readWithPadding_split _ 320 4 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by
        exact getRewardOwedBaseTrackingCalldataMem_size_ge356
          I slot0 multiplier houtSize)]
  rw [getRewardOwedBaseTrackingCalldataMem_read320_4 I slot0 multiplier houtSize,
    getRewardOwedBaseTrackingCalldataMem_read324_32 I slot0 multiplier houtSize]

set_option maxHeartbeats 1000000 in
theorem getRewardOwedBaseTrackingCalldataMem_encode_args
    (I : ExecutionEnv)
    (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size)
    (hcanonAccount : (getRewardOwedAccountWord I).toNat < EVM.addressModulus) :
    config.externalABI.encode? "baseTrackingAccrued" (getRewardAccruedBaseTrackingArgs I) =
      some ((getRewardOwedBaseTrackingCalldataMem I slot0 multiplier out)
        |>.readWithPadding 320 getRewardOwedBaseTrackingCallSize.toNat) := by
  rw [show getRewardOwedBaseTrackingCallSize.toNat = 36 from rfl]
  rw [getRewardOwedBaseTrackingCalldataMem_read320_36 I slot0 multiplier houtSize]
  change compoundRewardsExternalABI.encode? "baseTrackingAccrued"
      (getRewardAccruedBaseTrackingArgs I) =
    some (baseTrackingAccruedSelector ++ UInt256.toByteArray (getRewardOwedAccountWord I))
  have haccountWord :
      EVM.word (AccountAddress.ofNat (getRewardOwedAccountWord I).toNat).val =
        getRewardOwedAccountWord I := by
    change UInt256.ofNat (AccountAddress.ofNat (getRewardOwedAccountWord I).toNat).val =
      getRewardOwedAccountWord I
    have haddr :
        (AccountAddress.ofNat (getRewardOwedAccountWord I).toNat).val =
          (getRewardOwedAccountWord I).toNat := by
      have hcanonAddr : (getRewardOwedAccountWord I).toNat < AccountAddress.size := by
        simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanonAccount
      unfold AccountAddress.ofNat
      exact Nat.mod_eq_of_lt hcanonAddr
    rw [haddr]
    exact u256_ofNat_toNat (getRewardOwedAccountWord I)
  unfold compoundRewardsExternalABI ABI.encodeCallWithSelector? ABI.encodeABIValues?
  simp [getRewardAccruedBaseTrackingArgs, getRewardOwedAccountValue, addr,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.encodeABIValuesFrom?, haccountWord,
    word_toBytesBE_toByteArray_eq_toByteArray]

theorem getRewardOwedBaseTrackingSelectorMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (getRewardOwedBaseTrackingSelectorMem I slot0 multiplier out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨320⟩ := by
  unfold getRewardOwedBaseTrackingSelectorMem
  exact (writeWord_read_preserved
    (getRewardOwedClaimedOuterHashMem I slot0 multiplier out) 320 64
    (UInt256.shiftLeft (⟨719776253⟩ : UInt256) ⟨226⟩)
    (by
      have hge := getRewardOwedClaimedOuterHashMem_size_ge320 I slot0 multiplier houtSize
      have hle :
          320 - (getRewardOwedClaimedOuterHashMem I slot0 multiplier out).size = 0 := by
        omega
      rw [hle]
      native_decide)
    (by
      left
      have hge := getRewardOwedClaimedOuterHashMem_size_ge320 I slot0 multiplier houtSize
      constructor <;> omega)).trans
    (getRewardOwedClaimedOuterHashMem_read64 I slot0 multiplier houtSize)

theorem getRewardOwedBaseTrackingCalldataMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (getRewardOwedBaseTrackingCalldataMem I slot0 multiplier out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨320⟩ := by
  unfold getRewardOwedBaseTrackingCalldataMem
  exact (writeWord_read_preserved
    (getRewardOwedBaseTrackingSelectorMem I slot0 multiplier out) 324 64
    (getRewardOwedAccountWord I)
    (by
      have hge := getRewardOwedBaseTrackingSelectorMem_size_ge352 I slot0 multiplier houtSize
      have hle :
          324 - (getRewardOwedBaseTrackingSelectorMem I slot0 multiplier out).size = 0 := by
        omega
      rw [hle]
      native_decide)
    (by
      left
      have hge := getRewardOwedBaseTrackingSelectorMem_size_ge352 I slot0 multiplier houtSize
      constructor <;> omega)).trans
    (getRewardOwedBaseTrackingSelectorMem_read64 I slot0 multiplier houtSize)

theorem getRewardOwedBaseTrackingPostCallMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size) (hbaseSize : baseOut.size < UInt256.size) :
    (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut).readWithPadding
        64 32 =
      UInt256.toByteArray ⟨320⟩ := by
  unfold getRewardOwedBaseTrackingPostCallMem
  by_cases hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat = 0
  · rw [hlen, byteArray_write_len_zero]
    exact getRewardOwedBaseTrackingCalldataMem_read64 I slot0 multiplier haccrueSize
  · have hsrc :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat ≤ baseOut.size :=
      getRewardOwedPostCallLen_le_out_size hbaseSize
    rw [write_read_below_gen_extend baseOut
      (getRewardOwedBaseTrackingCalldataMem I slot0 multiplier accrueOut) 320
      (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat 64
      hlen hsrc
      (by
        have hge := getRewardOwedBaseTrackingCalldataMem_size_ge356
          I slot0 multiplier haccrueSize
        omega)
      (by norm_num)]
    exact getRewardOwedBaseTrackingCalldataMem_read64 I slot0 multiplier haccrueSize

theorem getRewardOwedBaseTrackingPostCallMem_size_ge320
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size) (hbaseSize : baseOut.size < UInt256.size) :
    320 ≤ (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut).size := by
  unfold getRewardOwedBaseTrackingPostCallMem
  by_cases hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat = 0
  · rw [hlen, byteArray_write_len_zero]
    have hge := getRewardOwedBaseTrackingCalldataMem_size_ge356 I slot0 multiplier haccrueSize
    omega
  · have hsrc :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat ≤ baseOut.size :=
      getRewardOwedPostCallLen_le_out_size hbaseSize
    let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat
    let base := getRewardOwedBaseTrackingCalldataMem I slot0 multiplier accrueOut
    have hdest : 320 ≤ base.size := by
      have hge := getRewardOwedBaseTrackingCalldataMem_size_ge356 I slot0 multiplier
        haccrueSize
      simpa [base] using le_trans (by norm_num : 320 ≤ 356) hge
    by_cases hin : 320 + len ≤ base.size
    · rw [write_eq_gen baseOut base 320 len (by simpa [len] using hlen)
        (by simpa [len] using hsrc) hin]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract]
      omega
    · have hext : base.size < 320 + len := Nat.lt_of_not_ge hin
      rw [write_eq_gen_extend baseOut base 320 len (by simpa [len] using hlen)
        (by simpa [len] using hsrc) hdest hext]
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega

theorem getRewardOwedBaseTrackingPostCallMem_mload64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size) (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut).size
        ∨ (⟨64⟩ : UInt256) ≥ getRewardOwedBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut)
          |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨320⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := getRewardOwedBaseTrackingPostCallAw)
    (v := ⟨320⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      have hge := getRewardOwedBaseTrackingPostCallMem_size_ge320
        I slot0 multiplier haccrueSize hbaseSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      exact getRewardOwedBaseTrackingPostCallMem_read64
        I slot0 multiplier haccrueSize hbaseSize)

theorem getRewardOwedBaseTrackingPostCallMem_read320_of_size_ge
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut).readWithPadding
        320 32 =
      baseOut.extract 0 32 := by
  unfold getRewardOwedBaseTrackingPostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := baseOut.size)
      (by decide) hout32 hbaseSize
  rw [hlen]
  exact write32_read_back baseOut
    (getRewardOwedBaseTrackingCalldataMem I slot0 multiplier accrueOut)
    320 hout32
    (by
      have hge := getRewardOwedBaseTrackingCalldataMem_size_ge356
        I slot0 multiplier haccrueSize
      omega)

theorem getRewardOwedBaseTrackingPostCallMem_size_ge352
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    352 ≤ (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut).size := by
  unfold getRewardOwedBaseTrackingPostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := baseOut.size)
      (by decide) hout32 hbaseSize
  rw [hlen]
  rw [write32_eq baseOut
    (getRewardOwedBaseTrackingCalldataMem I slot0 multiplier accrueOut) 320 hout32
    (by
      have hge := getRewardOwedBaseTrackingCalldataMem_size_ge356
        I slot0 multiplier haccrueSize
      omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract]
  have hbase := getRewardOwedBaseTrackingCalldataMem_size_ge356 I slot0 multiplier
    haccrueSize
  omega

theorem getRewardOwedBaseTrackingPostCallMem_mload320_haw :
    ¬ (⟨320⟩ : UInt256) ≥ getRewardOwedBaseTrackingPostCallAw * ⟨32⟩ := by
  native_decide

theorem getRewardOwedBaseTrackingPostCallMem_mload320_of_size_ge
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨320⟩ : UInt256).toNat ≥
          (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut).size
        ∨ (⟨320⟩ : UInt256) ≥ getRewardOwedBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut)
          |>.readWithPadding (⟨320⟩ : UInt256).toNat 32))) =
      getRewardOwedBaseTrackingReturnWord baseOut := by
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut)
    (aw := getRewardOwedBaseTrackingPostCallAw)
    (off := ⟨320⟩)
    (memSize := (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut).size)
    rfl
    (by
      rw [show (⟨320⟩ : UInt256).toNat = 320 from by decide]
      exact lt_of_lt_of_le (by omega)
        (getRewardOwedBaseTrackingPostCallMem_size_ge352
          I slot0 multiplier haccrueSize hout32 hbaseSize))
    getRewardOwedBaseTrackingPostCallMem_mload320_haw
    |>.trans (by
      rw [show (⟨320⟩ : UInt256).toNat = 320 from by decide,
        getRewardOwedBaseTrackingPostCallMem_read320_of_size_ge
          I slot0 multiplier haccrueSize hout32 hbaseSize]
      )

theorem getRewardOwedBaseTrackingPostDecodeMem_read320_of_size_ge
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut).readWithPadding
        320 32 =
      baseOut.extract 0 32 := by
  unfold getRewardOwedBaseTrackingPostDecodeMem
  rw [writeWord_read_preserved]
  · exact getRewardOwedBaseTrackingPostCallMem_read320_of_size_ge
      I slot0 multiplier haccrueSize hout32 hbaseSize
  · have hge := getRewardOwedBaseTrackingPostCallMem_size_ge352
      I slot0 multiplier haccrueSize hout32 hbaseSize
    have hle :
        64 - (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut).size =
          0 := by
      omega
    rw [hle]
    native_decide
  · right
    have hge := getRewardOwedBaseTrackingPostCallMem_size_ge352
      I slot0 multiplier haccrueSize hout32 hbaseSize
    constructor <;> omega

theorem getRewardOwedBaseTrackingPostDecodeMem_mload320_of_size_ge
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨320⟩ : UInt256).toNat ≥
          (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut).size
        ∨ (⟨320⟩ : UInt256) ≥ getRewardOwedBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
          |>.readWithPadding (⟨320⟩ : UInt256).toNat 32))) =
      getRewardOwedBaseTrackingReturnWord baseOut := by
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
    (aw := getRewardOwedBaseTrackingPostCallAw)
    (off := ⟨320⟩)
    (memSize :=
      (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut).size)
    rfl
    (by
      rw [show (⟨320⟩ : UInt256).toNat = 320 from by decide]
      unfold getRewardOwedBaseTrackingPostDecodeMem
      rw [writeWord_size]
      · have hsz := getRewardOwedBaseTrackingPostCallMem_size_ge352
          I slot0 multiplier haccrueSize hout32 hbaseSize
        omega
      · have hsz := getRewardOwedBaseTrackingPostCallMem_size_ge352
          I slot0 multiplier haccrueSize hout32 hbaseSize
        have hle :
            64 -
              (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut).size =
                0 := by
          omega
        rw [hle]
        native_decide)
    getRewardOwedBaseTrackingPostCallMem_mload320_haw
    |>.trans (by
      rw [show (⟨320⟩ : UInt256).toNat = 320 from by decide,
        getRewardOwedBaseTrackingPostDecodeMem_read320_of_size_ge
          I slot0 multiplier haccrueSize hout32 hbaseSize]
      )

theorem getRewardOwedBaseTrackingPostDecodeMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut).readWithPadding
        64 32 =
      UInt256.toByteArray ⟨352⟩ := by
  unfold getRewardOwedBaseTrackingPostDecodeMem
  exact writeWord_read_back
    (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut) 64
    (⟨352⟩ : UInt256)
    (by
      have hge := getRewardOwedBaseTrackingPostCallMem_size_ge352
        I slot0 multiplier haccrueSize hout32 hbaseSize
      have hle :
          64 - (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut).size =
            0 := by
        omega
      rw [hle]
      native_decide)

theorem getRewardOwedBaseTrackingPostDecodeMem_size_ge352
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    352 ≤
      (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut).size := by
  unfold getRewardOwedBaseTrackingPostDecodeMem
  rw [writeWord_size]
  · exact getRewardOwedBaseTrackingPostCallMem_size_ge352
      I slot0 multiplier haccrueSize hout32 hbaseSize
      |>.trans (le_max_left _ _)
  · have hge := getRewardOwedBaseTrackingPostCallMem_size_ge352
      I slot0 multiplier haccrueSize hout32 hbaseSize
    have hle :
        64 - (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut).size =
          0 := by
      omega
    rw [hle]
    native_decide

theorem getRewardOwedBaseTrackingPostDecodeMem_mload64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut).size
        ∨ (⟨64⟩ : UInt256) ≥ getRewardOwedBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
          |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨352⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := getRewardOwedBaseTrackingPostCallAw)
    (v := ⟨352⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      have hge := getRewardOwedBaseTrackingPostDecodeMem_size_ge352
        I slot0 multiplier haccrueSize hout32 hbaseSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      exact getRewardOwedBaseTrackingPostDecodeMem_read64
        I slot0 multiplier haccrueSize hout32 hbaseSize)

theorem twoWordHashMem_read_above64_of_ge {mem : ByteArray} (key slot : UInt256)
    {read : ℕ} (hmem : read + 32 ≤ mem.size) (habove : 64 ≤ read) :
    (twoWordHashMem key slot mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 read (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge key (by omega)]; omega) (by omega)
      (by rw [wordAt0Mem_size_of_ge key (by omega)]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 read (by rw [toByteArray_size])
      (by omega) (by omega) hmem]

theorem getRewardOwedAccrueAccountPostCallMem_read_below320
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {out : ByteArray}
    (houtSize : out.size < UInt256.size) {read : ℕ} (hbelow : read + 32 ≤ 320) :
    (getRewardOwedAccrueAccountPostCallMem I slot0 multiplier out).readWithPadding
        read 32 =
      (getRewardOwedAccrueAccountCalldataMem I slot0 multiplier).readWithPadding read 32 := by
  dsimp [getRewardOwedAccrueAccountPostCallMem]
  have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
    change (0 : Nat) ≤ (UInt256.ofNat out.size).toNat
    exact Nat.zero_le _
  rw [show (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 by
    simp [min, hle]]
  rw [byteArray_write_len_zero]

theorem getRewardOwedBaseTrackingPostCallMem_read_below320
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size) (hbaseSize : baseOut.size < UInt256.size)
    {read : ℕ} (hbelow : read + 32 ≤ 320) :
    (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut).readWithPadding
        read 32 =
      (getRewardOwedBaseTrackingCalldataMem I slot0 multiplier accrueOut).readWithPadding
        read 32 := by
  unfold getRewardOwedBaseTrackingPostCallMem
  by_cases hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat = 0
  · rw [hlen, byteArray_write_len_zero]
  · have hsrc :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat ≤ baseOut.size :=
      getRewardOwedPostCallLen_le_out_size hbaseSize
    rw [write_read_below_gen_extend baseOut
      (getRewardOwedBaseTrackingCalldataMem I slot0 multiplier accrueOut) 320
      (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat read
      hlen hsrc
      (by
        have hge := getRewardOwedBaseTrackingCalldataMem_size_ge356
          I slot0 multiplier haccrueSize
        omega)
      hbelow]

theorem getRewardOwedConfigMultiplierMem_read224
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (getRewardOwedConfigMultiplierMem I slot0 multiplier).readWithPadding 224 32 =
      UInt256.toByteArray (rewardConfigRescaleFromSlot0 slot0) := by
  unfold getRewardOwedConfigMultiplierMem
  rw [writeWord_read_preserved]
  · unfold getRewardOwedConfigShouldMem
    rw [writeWord_read_preserved]
    · unfold getRewardOwedConfigRescaleMem
      exact writeWord_read_back (getRewardOwedConfigTokenMem I slot0) 224
        (rewardConfigRescaleFromSlot0 slot0)
        (by rw [getRewardOwedConfigTokenMem_size]; native_decide)
    · rw [getRewardOwedConfigRescaleMem_size]
      native_decide
    · left
      rw [getRewardOwedConfigRescaleMem_size]
      constructor <;> norm_num
  · rw [getRewardOwedConfigShouldMem_size]
    native_decide
  · left
    rw [getRewardOwedConfigShouldMem_size]
    constructor <;> norm_num

theorem getRewardOwedConfigMultiplierMem_read256
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (getRewardOwedConfigMultiplierMem I slot0 multiplier).readWithPadding 256 32 =
      UInt256.toByteArray (rewardConfigShouldUpscaleFromSlot0 slot0) := by
  unfold getRewardOwedConfigMultiplierMem
  rw [writeWord_read_preserved]
  · unfold getRewardOwedConfigShouldMem
    exact writeWord_read_back (getRewardOwedConfigRescaleMem I slot0) 256
      (rewardConfigShouldUpscaleFromSlot0 slot0)
      (by rw [getRewardOwedConfigRescaleMem_size]; native_decide)
  · rw [getRewardOwedConfigShouldMem_size]
    native_decide
  · left
    rw [getRewardOwedConfigShouldMem_size]
    constructor <;> norm_num

theorem getRewardOwedConfigMultiplierMem_read288
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (getRewardOwedConfigMultiplierMem I slot0 multiplier).readWithPadding 288 32 =
      UInt256.toByteArray multiplier := by
  unfold getRewardOwedConfigMultiplierMem
  exact writeWord_read_back (getRewardOwedConfigShouldMem I slot0) 288 multiplier
    (by rw [getRewardOwedConfigShouldMem_size]; native_decide)

theorem getRewardOwedConfigMultiplierMem_read192
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (getRewardOwedConfigMultiplierMem I slot0 multiplier).readWithPadding 192 32 =
      UInt256.toByteArray (rewardConfigTokenFromSlot0 slot0) := by
  unfold getRewardOwedConfigMultiplierMem
  rw [writeWord_read_preserved]
  · unfold getRewardOwedConfigShouldMem
    rw [writeWord_read_preserved]
    · unfold getRewardOwedConfigRescaleMem
      rw [writeWord_read_preserved]
      · unfold getRewardOwedConfigTokenMem
        exact writeWord_read_back (getRewardOwedConfigAllocMem I) 192
          (rewardConfigTokenFromSlot0 slot0)
          (by rw [getRewardOwedConfigAllocMem_size]; native_decide)
      · rw [getRewardOwedConfigTokenMem_size]
        native_decide
      · left
        rw [getRewardOwedConfigTokenMem_size]
        constructor <;> norm_num
    · rw [getRewardOwedConfigRescaleMem_size]
      native_decide
    · left
      rw [getRewardOwedConfigRescaleMem_size]
      constructor <;> norm_num
  · rw [getRewardOwedConfigShouldMem_size]
    native_decide
  · left
    rw [getRewardOwedConfigShouldMem_size]
    constructor <;> norm_num

theorem getRewardOwedBaseTrackingPostDecodeMem_read_config
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size) (hbaseSize : baseOut.size < UInt256.size)
    {read : ℕ} (hbelow : read + 32 ≤ 320) (habove : 96 ≤ read) {val : UInt256}
    (hcfg :
      (getRewardOwedConfigMultiplierMem I slot0 multiplier).readWithPadding read 32 =
        UInt256.toByteArray val) :
    (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut).readWithPadding
        read 32 =
      UInt256.toByteArray val := by
  unfold getRewardOwedBaseTrackingPostDecodeMem
  rw [writeWord_read_preserved]
  · rw [getRewardOwedBaseTrackingPostCallMem_read_below320
        I slot0 multiplier haccrueSize hbaseSize hbelow]
    unfold getRewardOwedBaseTrackingCalldataMem
    rw [writeWord_read_preserved]
    · unfold getRewardOwedBaseTrackingSelectorMem
      rw [writeWord_read_preserved]
      · unfold getRewardOwedClaimedOuterHashMem
        rw [twoWordHashMem_read_above64_of_ge]
        · unfold getRewardOwedClaimedInnerHashMem
          rw [twoWordHashMem_read_above64_of_ge]
          · unfold getRewardOwedAccrueAccountAfterAllocMem
            rw [writeWord_read_preserved]
            · rw [getRewardOwedAccrueAccountPostCallMem_read_below320
                  I slot0 multiplier haccrueSize hbelow]
              unfold getRewardOwedAccrueAccountCalldataMem
              rw [writeWord_read_preserved]
              · unfold getRewardOwedAccrueAccountSelectorMem
                rw [writeWord_read_preserved]
                · exact hcfg
                · rw [getRewardOwedConfigMultiplierMem_size]
                  native_decide
                · left
                  rw [getRewardOwedConfigMultiplierMem_size]
                  exact ⟨hbelow, hbelow⟩
              · have hge := getRewardOwedAccrueAccountSelectorMem_size
                    I slot0 multiplier
                have hle :
                    324 - (getRewardOwedAccrueAccountSelectorMem I slot0 multiplier).size =
                      0 := by
                  rw [hge]
                rw [hle]
                native_decide
              · left
                have hsz := getRewardOwedAccrueAccountSelectorMem_size I slot0 multiplier
                rw [hsz]
                constructor <;> omega
            · have hge := getRewardOwedAccrueAccountPostCallMem_size_ge320
                  I slot0 multiplier haccrueSize
              have hle :
                  64 - (getRewardOwedAccrueAccountPostCallMem I slot0 multiplier accrueOut).size =
                    0 := by
                omega
              rw [hle]
              native_decide
            · right
              have hge := getRewardOwedAccrueAccountPostCallMem_size_ge320
                    I slot0 multiplier haccrueSize
              constructor <;> omega
          · have hge := getRewardOwedAccrueAccountAfterAllocMem_size_ge320
                I slot0 multiplier haccrueSize
            omega
          · omega
        · have hge := getRewardOwedClaimedInnerHashMem_size_ge320
              I slot0 multiplier haccrueSize
          omega
        · omega
      · have hge := getRewardOwedClaimedOuterHashMem_size_ge320
            I slot0 multiplier haccrueSize
        have hle :
            320 - (getRewardOwedClaimedOuterHashMem I slot0 multiplier accrueOut).size = 0 := by
          omega
        rw [hle]
        native_decide
      · left
        have hge := getRewardOwedClaimedOuterHashMem_size_ge320
            I slot0 multiplier haccrueSize
        constructor <;> omega
    · have hge := getRewardOwedBaseTrackingSelectorMem_size_ge352
          I slot0 multiplier haccrueSize
      have hle :
          324 - (getRewardOwedBaseTrackingSelectorMem I slot0 multiplier accrueOut).size = 0 := by
        omega
      rw [hle]
      native_decide
    · left
      have hge := getRewardOwedBaseTrackingSelectorMem_size_ge352
          I slot0 multiplier haccrueSize
      constructor <;> omega
  · have hge := getRewardOwedBaseTrackingPostCallMem_size_ge320
        I slot0 multiplier haccrueSize hbaseSize
    have hle :
        64 -
          (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut).size = 0 := by
      omega
    rw [hle]
    native_decide
  · right
    have hge := getRewardOwedBaseTrackingPostCallMem_size_ge320
        I slot0 multiplier haccrueSize hbaseSize
    constructor <;> omega

theorem getRewardOwedBaseTrackingPostDecodeMem_read224
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size) (hbaseSize : baseOut.size < UInt256.size) :
    (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut).readWithPadding
        224 32 =
      UInt256.toByteArray (rewardConfigRescaleFromSlot0 slot0) :=
  getRewardOwedBaseTrackingPostDecodeMem_read_config
    I slot0 multiplier haccrueSize hbaseSize (by norm_num) (by norm_num)
    (getRewardOwedConfigMultiplierMem_read224 I slot0 multiplier)

theorem getRewardOwedBaseTrackingPostDecodeMem_read192
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size) (hbaseSize : baseOut.size < UInt256.size) :
    (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut).readWithPadding
        192 32 =
      UInt256.toByteArray (rewardConfigTokenFromSlot0 slot0) :=
  getRewardOwedBaseTrackingPostDecodeMem_read_config
    I slot0 multiplier haccrueSize hbaseSize (by norm_num) (by norm_num)
    (getRewardOwedConfigMultiplierMem_read192 I slot0 multiplier)

theorem getRewardOwedBaseTrackingPostDecodeMem_read256
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size) (hbaseSize : baseOut.size < UInt256.size) :
    (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut).readWithPadding
        256 32 =
      UInt256.toByteArray (rewardConfigShouldUpscaleFromSlot0 slot0) :=
  getRewardOwedBaseTrackingPostDecodeMem_read_config
    I slot0 multiplier haccrueSize hbaseSize (by norm_num) (by norm_num)
    (getRewardOwedConfigMultiplierMem_read256 I slot0 multiplier)

theorem getRewardOwedBaseTrackingPostDecodeMem_read288
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size) (hbaseSize : baseOut.size < UInt256.size) :
    (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut).readWithPadding
        288 32 =
      UInt256.toByteArray multiplier :=
  getRewardOwedBaseTrackingPostDecodeMem_read_config
    I slot0 multiplier haccrueSize hbaseSize (by norm_num) (by norm_num)
    (getRewardOwedConfigMultiplierMem_read288 I slot0 multiplier)

theorem getRewardOwedBaseTrackingPostDecodeMem_mload224
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨224⟩ : UInt256).toNat ≥
          (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut).size
        ∨ (⟨224⟩ : UInt256) ≥ getRewardOwedBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
          |>.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
      rewardConfigRescaleFromSlot0 slot0 := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨224⟩ : UInt256)) (aw := getRewardOwedBaseTrackingPostCallAw)
    (v := rewardConfigRescaleFromSlot0 slot0)
    (by
      rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
      have hge := getRewardOwedBaseTrackingPostDecodeMem_size_ge352
        I slot0 multiplier haccrueSize hout32 hbaseSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
      exact getRewardOwedBaseTrackingPostDecodeMem_read224
        I slot0 multiplier haccrueSize hbaseSize)

theorem getRewardOwedBaseTrackingPostDecodeMem_mload192
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨192⟩ : UInt256).toNat ≥
          (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut).size
        ∨ (⟨192⟩ : UInt256) ≥ getRewardOwedBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
          |>.readWithPadding (⟨192⟩ : UInt256).toNat 32))) =
      rewardConfigTokenFromSlot0 slot0 := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨192⟩ : UInt256)) (aw := getRewardOwedBaseTrackingPostCallAw)
    (v := rewardConfigTokenFromSlot0 slot0)
    (by
      rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]
      have hge := getRewardOwedBaseTrackingPostDecodeMem_size_ge352
        I slot0 multiplier haccrueSize hout32 hbaseSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]
      exact getRewardOwedBaseTrackingPostDecodeMem_read192
        I slot0 multiplier haccrueSize hbaseSize)

theorem getRewardOwedBaseTrackingPostDecodeMem_mload256
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨256⟩ : UInt256).toNat ≥
          (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut).size
        ∨ (⟨256⟩ : UInt256) ≥ getRewardOwedBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
          |>.readWithPadding (⟨256⟩ : UInt256).toNat 32))) =
      rewardConfigShouldUpscaleFromSlot0 slot0 := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨256⟩ : UInt256)) (aw := getRewardOwedBaseTrackingPostCallAw)
    (v := rewardConfigShouldUpscaleFromSlot0 slot0)
    (by
      rw [show (⟨256⟩ : UInt256).toNat = 256 from by decide]
      have hge := getRewardOwedBaseTrackingPostDecodeMem_size_ge352
        I slot0 multiplier haccrueSize hout32 hbaseSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨256⟩ : UInt256).toNat = 256 from by decide]
      exact getRewardOwedBaseTrackingPostDecodeMem_read256
        I slot0 multiplier haccrueSize hbaseSize)

theorem getRewardOwedBaseTrackingPostDecodeMem_mload288
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨288⟩ : UInt256).toNat ≥
          (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut).size
        ∨ (⟨288⟩ : UInt256) ≥ getRewardOwedBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
          |>.readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
      multiplier := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨288⟩ : UInt256)) (aw := getRewardOwedBaseTrackingPostCallAw)
    (v := multiplier)
    (by
      rw [show (⟨288⟩ : UInt256).toNat = 288 from by decide]
      have hge := getRewardOwedBaseTrackingPostDecodeMem_size_ge352
        I slot0 multiplier haccrueSize hout32 hbaseSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨288⟩ : UInt256).toNat = 288 from by decide]
      exact getRewardOwedBaseTrackingPostDecodeMem_read288
        I slot0 multiplier haccrueSize hbaseSize)

theorem rewardConfigTokenFromSlot0_clean (slot0 : UInt256) :
    UInt256.land (rewardConfigTokenFromSlot0 slot0) solcAddrMask =
      rewardConfigTokenFromSlot0 slot0 := by
  simpa [rewardConfigTokenFromSlot0] using
    solcAddrMask_clean (solcAddrMask_result_canonical slot0)

theorem getRewardOwedReturnAllocMem_size_ge352
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    352 ≤ (getRewardOwedReturnAllocMem I slot0 multiplier accrueOut baseOut).size := by
  unfold getRewardOwedReturnAllocMem
  rw [writeWord_size]
  · exact (getRewardOwedBaseTrackingPostDecodeMem_size_ge352
      I slot0 multiplier haccrueSize hout32 hbaseSize).trans (le_max_left _ _)
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by norm_num))

theorem getRewardOwedReturnStructTokenMem_size_ge384
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    384 ≤
      (getRewardOwedReturnStructTokenMem I slot0 multiplier accrueOut baseOut).size := by
  unfold getRewardOwedReturnStructTokenMem
  rw [writeWord_size]
  · omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 352 (by norm_num))

theorem getRewardOwedReturnStructOwedMem_size_ge416
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (owed : UInt256)
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    416 ≤
      (getRewardOwedReturnStructOwedMem I slot0 multiplier accrueOut baseOut owed).size := by
  unfold getRewardOwedReturnStructOwedMem
  rw [writeWord_size]
  · omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 384 (by norm_num))

theorem getRewardOwedReturnCopyTokenMem_size_ge448
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accrueOut baseOut : ByteArray)
    (owed : UInt256) :
    448 ≤ (getRewardOwedReturnCopyTokenMem I slot0 multiplier accrueOut baseOut owed).size := by
  unfold getRewardOwedReturnCopyTokenMem
  rw [writeWord_size]
  · omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 416 (by norm_num))

theorem getRewardOwedReturnMem_size_ge480
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accrueOut baseOut : ByteArray)
    (owed : UInt256) :
    480 ≤ (getRewardOwedReturnMem I slot0 multiplier accrueOut baseOut owed).size := by
  unfold getRewardOwedReturnMem
  rw [writeWord_size]
  · omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 448 (by norm_num))

theorem getRewardOwedReturnAllocMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accrueOut baseOut : ByteArray) :
    (getRewardOwedReturnAllocMem I slot0 multiplier accrueOut baseOut).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨416⟩ : UInt256) := by
  unfold getRewardOwedReturnAllocMem
  exact writeWord_read_back
    (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut) 64
    (⟨416⟩ : UInt256)
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by norm_num)))

theorem getRewardOwedReturnStructTokenMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (getRewardOwedReturnStructTokenMem I slot0 multiplier accrueOut baseOut).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨416⟩ : UInt256) := by
  unfold getRewardOwedReturnStructTokenMem
  rw [writeWord_read_preserved]
  · exact getRewardOwedReturnAllocMem_read64 I slot0 multiplier accrueOut baseOut
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 352 (by norm_num))
  · left
    constructor
    · norm_num
    · have hsz := getRewardOwedReturnAllocMem_size_ge352
        I slot0 multiplier haccrueSize hout32 hbaseSize
      omega

theorem getRewardOwedReturnStructOwedMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (owed : UInt256)
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (getRewardOwedReturnStructOwedMem I slot0 multiplier accrueOut baseOut owed).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨416⟩ : UInt256) := by
  unfold getRewardOwedReturnStructOwedMem
  rw [writeWord_read_preserved]
  · exact getRewardOwedReturnStructTokenMem_read64
      I slot0 multiplier haccrueSize hout32 hbaseSize
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 384 (by norm_num))
  · left
    constructor
    · norm_num
    · have hsz := getRewardOwedReturnStructTokenMem_size_ge384
        I slot0 multiplier haccrueSize hout32 hbaseSize
      omega

theorem getRewardOwedReturnStructOwedMem_mload64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (owed : UInt256)
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (getRewardOwedReturnStructOwedMem I slot0 multiplier accrueOut baseOut owed).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 13 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((getRewardOwedReturnStructOwedMem I slot0 multiplier accrueOut baseOut owed)
          |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨416⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 13) (v := ⟨416⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      have hsz := getRewardOwedReturnStructOwedMem_size_ge416
        I slot0 multiplier owed haccrueSize hout32 hbaseSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      exact getRewardOwedReturnStructOwedMem_read64
        I slot0 multiplier owed haccrueSize hout32 hbaseSize)

theorem getRewardOwedReturnMem_readWord416
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accrueOut baseOut : ByteArray)
    (owed : UInt256) :
    (getRewardOwedReturnMem I slot0 multiplier accrueOut baseOut owed).readWithPadding
        416 32 =
      UInt256.toByteArray (rewardConfigTokenFromSlot0 slot0) := by
  unfold getRewardOwedReturnMem
  rw [writeWord_read_preserved]
  · unfold getRewardOwedReturnCopyTokenMem
    exact writeWord_read_back
      (getRewardOwedReturnStructOwedMem I slot0 multiplier accrueOut baseOut owed) 416
      (rewardConfigTokenFromSlot0 slot0)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 416 (by norm_num)))
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 448 (by norm_num))
  · left
    constructor
    · norm_num
    · exact getRewardOwedReturnCopyTokenMem_size_ge448
        I slot0 multiplier accrueOut baseOut owed

theorem getRewardOwedReturnMem_readWord448
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accrueOut baseOut : ByteArray)
    (owed : UInt256) :
    (getRewardOwedReturnMem I slot0 multiplier accrueOut baseOut owed).readWithPadding
        448 32 =
      UInt256.toByteArray owed := by
  unfold getRewardOwedReturnMem
  exact writeWord_read_back
    (getRewardOwedReturnCopyTokenMem I slot0 multiplier accrueOut baseOut owed) 448 owed
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 448 (by norm_num)))

theorem getRewardOwedReturnStructOwedMem_read384
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accrueOut baseOut : ByteArray)
    (owed : UInt256) :
    (getRewardOwedReturnStructOwedMem I slot0 multiplier accrueOut baseOut owed).readWithPadding
        384 32 =
      UInt256.toByteArray owed := by
  unfold getRewardOwedReturnStructOwedMem
  exact writeWord_read_back
    (getRewardOwedReturnStructTokenMem I slot0 multiplier accrueOut baseOut) 384 owed
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 384 (by norm_num)))

theorem getRewardOwedReturnCopyTokenMem_read384
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (owed : UInt256)
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (getRewardOwedReturnCopyTokenMem I slot0 multiplier accrueOut baseOut owed).readWithPadding
        384 32 =
      UInt256.toByteArray owed := by
  unfold getRewardOwedReturnCopyTokenMem
  rw [writeWord_read_preserved]
  · exact getRewardOwedReturnStructOwedMem_read384
      I slot0 multiplier accrueOut baseOut owed
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 416 (by norm_num))
  · left
    constructor
    · norm_num
    · have hsz := getRewardOwedReturnStructOwedMem_size_ge416
        I slot0 multiplier owed haccrueSize hout32 hbaseSize
      omega

theorem getRewardOwedReturnCopyTokenMem_mload384
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {accrueOut baseOut : ByteArray}
    (owed : UInt256)
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨384⟩ : UInt256).toNat ≥
          (getRewardOwedReturnCopyTokenMem I slot0 multiplier accrueOut baseOut owed).size
        ∨ (⟨384⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((getRewardOwedReturnCopyTokenMem I slot0 multiplier accrueOut baseOut owed)
          |>.readWithPadding (⟨384⟩ : UInt256).toNat 32))) =
      owed := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨384⟩ : UInt256)) (aw := UInt256.ofNat 14) (v := owed)
    (by
      rw [show (⟨384⟩ : UInt256).toNat = 384 from by decide]
      have hsz := getRewardOwedReturnCopyTokenMem_size_ge448
        I slot0 multiplier accrueOut baseOut owed
      omega)
    (by native_decide)
    (by
      rw [show (⟨384⟩ : UInt256).toNat = 384 from by decide]
      exact getRewardOwedReturnCopyTokenMem_read384
        I slot0 multiplier owed haccrueSize hout32 hbaseSize)

theorem getRewardOwedReturnMem_read416
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (accrueOut baseOut : ByteArray)
    (owed : UInt256) :
    (getRewardOwedReturnMem I slot0 multiplier accrueOut baseOut owed).readWithPadding 416 64 =
      getRewardOwedReturnBytes (rewardConfigTokenFromSlot0 slot0) owed := by
  rw [byteArray_readWithPadding_split _ 416 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  · rw [getRewardOwedReturnMem_readWord416, getRewardOwedReturnMem_readWord448]
    rfl
  · exact getRewardOwedReturnMem_size_ge480 I slot0 multiplier accrueOut baseOut owed

theorem getRewardOwedEncodeReturnValue_tuple (slot0 owed : UInt256) :
    encodeReturnValue? (.tuple [addr, uint256])
        (.tuple [getRewardOwedTokenValueFromSlot0 slot0, .int (Int.ofNat owed.toNat)]) =
      some (getRewardOwedReturnBytes (rewardConfigTokenFromSlot0 slot0) owed) := by
  have htoken :
      encodeABIValue? addr (getRewardOwedTokenValueFromSlot0 slot0) =
        some (EVM.Word.toBytesBE (rewardConfigTokenFromSlot0 slot0)) := by
    simpa [addr, getRewardOwedTokenValueFromSlot0, rewardConfigTokenFromSlot0] using
      rewardConfigEncodeABIValue_masked_address slot0
  have hclaimed :
      encodeABIValue? uint256 (.int (Int.ofNat owed.toNat)) =
        some (EVM.Word.toBytesBE owed) := by
    simpa [uint256, uint256Int] using rewardConfigEncodeABIValue_uint256 owed
  have htuple :
      encodeABIValue? (.tuple [addr, uint256])
          (.tuple [getRewardOwedTokenValueFromSlot0 slot0, .int (Int.ofNat owed.toNat)]) =
        some (EVM.Word.toBytesBE (rewardConfigTokenFromSlot0 slot0) ++
          EVM.Word.toBytesBE owed) := by
    simp only [encodeABIValue?]
    simp only [encodeABIValues?, encodeABIValuesFrom?, htoken, hclaimed, bind, Option.bind]
    simp [addr, uint256, uint256Int, abiTupleHeadSize?, staticABIEncodedSize?,
      isDynamicABIType]
  unfold getRewardOwedReturnBytes
  rw [toByteArray_eq_toBytesBE (rewardConfigTokenFromSlot0 slot0),
    toByteArray_eq_toBytesBE owed]
  simp only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?,
    htuple, bind, Option.bind]
  simp [addr, uint256, uint256Int, abiTupleHeadSize?, staticABIEncodedSize?,
    isDynamicABIType]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append]

theorem getRewardOwedSub_eq_ofNat {accrued claimed : UInt256}
    (h : claimed.toNat ≤ accrued.toNat) :
    UInt256.sub accrued claimed =
      UInt256.ofNat (accrued.toNat - claimed.toNat) := by
  apply u256_inj
  rw [usub_toNat (a := accrued) (b := claimed) h]
  rw [UInt256.toNat_ofNat_of_lt]
  exact lt_of_le_of_lt (Nat.sub_le _ _) accrued.val.isLt

theorem getRewardOwedOwedNat_lt (claimed : UInt256) {accruedNat : ℕ}
    (haccrued : accruedNat < UInt256.size) :
    (if claimed.toNat < accruedNat then accruedNat - claimed.toNat else 0) < UInt256.size := by
  by_cases hlt : claimed.toNat < accruedNat
  · simp [hlt]
    exact lt_of_le_of_lt (Nat.sub_le _ _) haccrued
  · simp [hlt, UInt256.size]

theorem getRewardOwedReturnOwedWord_of_ofNat
    (claimed : UInt256) {accruedNat : ℕ} (haccrued : accruedNat < UInt256.size) :
    getRewardOwedReturnOwedWord claimed (UInt256.ofNat accruedNat) =
      UInt256.ofNat
        (if claimed.toNat < accruedNat then accruedNat - claimed.toNat else 0) := by
  unfold getRewardOwedReturnOwedWord
  rw [UInt256.toNat_ofNat_of_lt haccrued]
  by_cases hlt : claimed.toNat < accruedNat
  · simp [hlt]
  · simp [hlt]
    rfl

set_option maxHeartbeats 2000000 in
theorem cometRewardsGetRewardOwedX_return_from2519
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {accrueOut baseOut : ByteArray}
    {owed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2519⟩
      [⟨192⟩, solcAddrMask, ⟨32⟩, owed, ⟨64⟩]
      (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k C)
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (getRewardOwedReturnBytes (rewardConfigTokenFromSlot0 slot0) owed) := by
  have htokenClean := rewardConfigTokenFromSlot0_clean slot0
  have rd2525₀ := evm_run rd with [
    jumpdest,
    raw mload 0 (rewardConfigTokenFromSlot0 slot0)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload192
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    and]
  have rd2525 := rd2525₀
  rw [htokenClean] at rd2525
  have rd2976 := evm_run rd2525 with [
    swap2, dup2, dup5,
    raw mload 0 (⟨352⟩ : UInt256)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload64
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    push2 ⟨2534⟩, dup2, push2 ⟨2976⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩, dup2, add, swap1, dup2, lt,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt, lor,
    push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd2534 := evm_run rd2976 with [
    raw mstore 0
      (getRewardOwedReturnAllocMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold getRewardOwedReturnAllocMem Reasoning.Theory.writeWord
        rfl)
      (by native_decide) (by evm_ov),
    jump (by jump_dest), jumpdest]
  have rd2538 := evm_run rd2534 with [
    dup5, dup2,
    raw mstore 0
      (getRewardOwedReturnStructTokenMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨352⟩ : UInt256).toNat = 352 from by decide]
        unfold getRewardOwedReturnStructTokenMem Reasoning.Theory.writeWord
        rfl)
      (by native_decide) (by evm_ov)]
  have rd2542 := evm_run rd2538 with [
    add, swap1, dup2,
    raw mstore 3
      (getRewardOwedReturnStructOwedMem I slot0 multiplier accrueOut baseOut owed)
      (UInt256.ofNat 13) (by native_decide) mem_cost
      (by
        rw [show ((⟨352⟩ : UInt256) + ⟨32⟩).toNat = 384 from by native_decide]
        unfold getRewardOwedReturnStructOwedMem Reasoning.Theory.writeWord
        rfl)
      (by native_decide) (by evm_ov)]
  have rd2546 := evm_run rd2542 with [
    dup4,
    raw mload 0 (⟨416⟩ : UInt256)
      (UInt256.ofNat 13) (by native_decide) mem_cost
      (getRewardOwedReturnStructOwedMem_mload64
        I slot0 multiplier owed haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    swap3, dup4,
    raw mstore 3
      (getRewardOwedReturnCopyTokenMem I slot0 multiplier accrueOut baseOut owed)
      (UInt256.ofNat 14) (by native_decide) mem_cost
      (by
        rw [show (⟨416⟩ : UInt256).toNat = 416 from by decide]
        unfold getRewardOwedReturnCopyTokenMem Reasoning.Theory.writeWord
        rfl)
      (by native_decide) (by evm_ov)]
  have rd2552 := evm_run rd2546 with [
    raw mload 0 owed
      (UInt256.ofNat 14) (by native_decide) mem_cost
      (by
        rw [show ((⟨352⟩ : UInt256) + ⟨32⟩).toNat = 384 from by native_decide]
        exact getRewardOwedReturnCopyTokenMem_mload384
          I slot0 multiplier owed haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    swap1, dup3, add,
    raw mstore 3
      (getRewardOwedReturnMem I slot0 multiplier accrueOut baseOut owed)
      (UInt256.ofNat 15) (by native_decide) mem_cost
      (by
        rw [show ((⟨416⟩ : UInt256) + ⟨32⟩).toNat = 448 from by native_decide]
        unfold getRewardOwedReturnMem Reasoning.Theory.writeWord
        rfl)
      (by native_decide) (by evm_ov)]
  exact evm_run rd2552 with [
    raw ret 0
      (getRewardOwedReturnBytes (rewardConfigTokenFromSlot0 slot0) owed)
      (by native_decide) mem_cost
      (by
        rw [show (⟨416⟩ : UInt256).toNat = 416 from by decide,
          show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        exact getRewardOwedReturnMem_read416 I slot0 multiplier accrueOut baseOut owed)
      (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem cometRewardsGetRewardOwedX_return_from2499
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {accrueOut baseOut : ByteArray}
    {accrued claimed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2499⟩
      [accrued, claimed, ⟨0⟩, solcAddrMask, ⟨32⟩, ⟨192⟩, ⟨64⟩]
      (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k C)
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (getRewardOwedReturnBytes (rewardConfigTokenFromSlot0 slot0)
        (getRewardOwedReturnOwedWord claimed accrued)) := by
  by_cases hgt : claimed.toNat < accrued.toNat
  · have hgtWord : UInt256.gt accrued claimed = ⟨1⟩ := ugt_one hgt
    have hltWord : UInt256.lt accrued claimed = ⟨0⟩ := ult_zero (le_of_lt hgt)
    have hsubWord :
        UInt256.sub accrued claimed =
          UInt256.ofNat (accrued.toNat - claimed.toNat) :=
      getRewardOwedSub_eq_ofNat (le_of_lt hgt)
    have rd2504₀ := evm_run rd with [jumpdest, dup2, dup2, gt, iszero]
    have rd2504 := rd2504₀
    rw [hgtWord, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd2504
    have rd3241 := evm_run rd2504 with [
      push2 ⟨2553⟩, jumpiNT (by native_decide),
      push2 ⟨2517⟩, swap3, pop, push2 ⟨3241⟩, jump (by jump_dest)]
    have rd3249₀ := evm_run rd3241 with [jumpdest, dup2, dup2, lt]
    have rd3249 := rd3249₀
    rw [hltWord] at rd3249
    have rd2517 := evm_run rd3249 with [
      push2 ⟨3252⟩, jumpiNT (by native_decide),
      sub, swap1, jump (by jump_dest), jumpdest]
    have rd2519 := evm_run rd2517 with [swap3]
    rw [hsubWord] at rd2519
    simpa [getRewardOwedReturnOwedWord, hgt] using
      cometRewardsGetRewardOwedX_return_from2519
        (slot0 := slot0) (multiplier := multiplier)
        (accrueOut := accrueOut) (baseOut := baseOut)
        (owed := UInt256.ofNat (accrued.toNat - claimed.toNat))
        rd2519 haccrueSize hout32 hbaseSize
  · have hle : accrued.toNat ≤ claimed.toNat := by omega
    have hgtWord : UInt256.gt accrued claimed = ⟨0⟩ := ugt_zero hle
    have rd2504₀ := evm_run rd with [jumpdest, dup2, dup2, gt, iszero]
    have rd2504 := rd2504₀
    rw [hgtWord, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd2504
    have rd2519 := evm_run rd2504 with [
      push2 ⟨2553⟩, jumpiT (by native_decide) (by jump_dest),
      jumpdest, pop, pop, swap3, push2 ⟨2519⟩, jump (by jump_dest)]
    simpa [getRewardOwedReturnOwedWord, hgt] using
      cometRewardsGetRewardOwedX_return_from2519
        (slot0 := slot0) (multiplier := multiplier)
        (accrueOut := accrueOut) (baseOut := baseOut)
        (owed := (⟨0⟩ : UInt256))
        rd2519 haccrueSize hout32 hbaseSize

theorem cometRewardsBaseTrackingAccrued_decode_none_short {out : ByteArray}
    (hshort : out.size < 32) :
    config.externalABI.decode? "baseTrackingAccrued" out = none := by
  change compoundRewardsExternalABI.decode? "baseTrackingAccrued" out = none
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [uint64] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_uint64_none_short (returndata := out) hshort)

theorem cometRewardsBaseTrackingAccrued_decode_ok {out : ByteArray}
    (hlo : 32 ≤ out.size) (hhi : out.size < 2 ^ 255)
    (hword : fromByteArrayBigEndian (out.extract 0 32) < EVM.twoPow 64) :
    config.externalABI.decode? "baseTrackingAccrued" out =
      some [.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))] := by
  change compoundRewardsExternalABI.decode? "baseTrackingAccrued" out =
      some [.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))]
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [uint64] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_uint64_ok (returndata := out) hlo hhi hword)

theorem cometRewardsBaseTrackingAccrued_decode_none_noncanon {out : ByteArray}
    (hlo : 32 ≤ out.size) (hhi : out.size < 2 ^ 255)
    (hword : ¬ fromByteArrayBigEndian (out.extract 0 32) < EVM.twoPow 64) :
    config.externalABI.decode? "baseTrackingAccrued" out = none := by
  change compoundRewardsExternalABI.decode? "baseTrackingAccrued" out = none
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [uint64] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_uint64_none_noncanon (returndata := out) hlo hhi hword)

theorem getRewardOwedCometTarget_eq_targetWord (I : ExecutionEnv)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus) :
    EVM.address (getRewardOwedCometTarget I) =
      AccountAddress.ofUInt256 (UInt256.land (getRewardOwedCometWord I) solcAddrMask) := by
  have hclean :
      UInt256.land (getRewardOwedCometWord I) solcAddrMask = getRewardOwedCometWord I := by
    exact solcAddrMask_clean (by simpa [getRewardOwedCometWord, calldataWord] using hcanonComet)
  rw [hclean, accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN, getRewardOwedCometTarget]
  exact Nat.mod_eq_of_lt (AccountAddress.ofNat (getRewardOwedCometWord I).toNat).isLt

set_option maxHeartbeats 1000000 in
theorem evalExpr_getRewardOwed_extCodeSizeGuard_false
    (evm : EVM.State) (I : ExecutionEnv)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (UInt256.land (getRewardOwedCometWord I) solcAddrMask) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
      (.binary .gt (.extCodeSize (.var "comet")) (.intLit 0)) = .ok (.bool false) := by
  have haddr :
      AccountAddress.ofNat (getRewardOwedCometWord I).toNat =
        AccountAddress.ofUInt256 (UInt256.land (getRewardOwedCometWord I) solcAddrMask) := by
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
    congr 1
    exact (solcAddrMask_clean (by simpa [getRewardOwedCometWord, calldataWord] using
      hcanonComet)).symm
  simp only [evalExpr?, EvalResult.bind, bind, EvalResult.ofOption]
  rw [getRewardOwedConfigLocals_comet]
  simp only [getRewardOwedCometValue, haddr, State.lookupAccount]
  have hword :
      EVM.Word.ofNat
          (Option.option 0 (fun acc => acc.code.size)
            (evm.accountMap.find?
              (AccountAddress.ofUInt256
                (UInt256.land (getRewardOwedCometWord I) solcAddrMask)))) =
        (⟨0⟩ : UInt256) := by
    cases hacc : evm.accountMap.find?
        (AccountAddress.ofUInt256 (UInt256.land (getRewardOwedCometWord I) solcAddrMask))
    · decide
    · simpa [Reasoning.Theory.uniswapExtCodeSizeWord, Function.comp, Option.option,
        EVM.Word.ofNat, hacc] using hzero
  rw [hword]
  decide

set_option maxHeartbeats 1000000 in
theorem evalExpr_getRewardOwed_extCodeSizeGuard_true
    (evm : EVM.State) (I : ExecutionEnv)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hnz :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (UInt256.land (getRewardOwedCometWord I) solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
      (.binary .gt (.extCodeSize (.var "comet")) (.intLit 0)) = .ok (.bool true) := by
  have haddr :
      AccountAddress.ofNat (getRewardOwedCometWord I).toNat =
        AccountAddress.ofUInt256 (UInt256.land (getRewardOwedCometWord I) solcAddrMask) := by
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
    congr 1
    exact (solcAddrMask_clean (by simpa [getRewardOwedCometWord, calldataWord] using
      hcanonComet)).symm
  simp only [evalExpr?, EvalResult.bind, bind, EvalResult.ofOption]
  rw [getRewardOwedConfigLocals_comet]
  simp only [getRewardOwedCometValue, haddr, State.lookupAccount]
  let codeWord : UInt256 :=
    EVM.Word.ofNat
      (Option.option 0 (fun acc => acc.code.size)
        (evm.accountMap.find?
          (AccountAddress.ofUInt256
            (UInt256.land (getRewardOwedCometWord I) solcAddrMask))))
  have hwordNZ : codeWord ≠ ⟨0⟩ := by
    cases hacc : evm.accountMap.find?
        (AccountAddress.ofUInt256 (UInt256.land (getRewardOwedCometWord I) solcAddrMask))
    · simpa [codeWord, Reasoning.Theory.uniswapExtCodeSizeWord, Function.comp,
        Option.option, EVM.Word.ofNat, hacc] using hnz
    · simpa [codeWord, Reasoning.Theory.uniswapExtCodeSizeWord, Function.comp,
        Option.option, EVM.Word.ofNat, hacc] using hnz
  have hpos : 0 < codeWord.toNat := by
    by_contra hnot
    have hz : codeWord.toNat = 0 := by omega
    exact hwordNZ (u256_inj hz)
  have hposInt : (0 : Int) < (codeWord.toNat : Int) := by
    exact_mod_cast hpos
  change evalBinaryOp? .gt (.int (Int.ofNat codeWord.toNat)) (.int 0) =
    .ok (.bool true)
  simp [evalBinaryOp?, hposInt]
  exact hpos

theorem cometRewardsDecode_getRewardOwed_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (getRewardOwedAccountWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (getRewardOwedTransition.params.map Param.name)
      (transitionSignature getRewardOwedTransition).paramTypes I.calldata =
        some (getRewardOwedStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "account"] [addr, addr]
    I.calldata = _
  simpa [config, getRewardOwedStore, getRewardOwedCometValue, getRewardOwedAccountValue,
    getRewardOwedCometWord, getRewardOwedAccountWord, calldataWord]
    using decodeCalldata_address_address_ok (cd := I.calldata) (x := "comet")
      (y := "account") hsz68 hbig hcanonComet hcanonAccount

theorem cometRewardsDecode_getRewardOwed_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (getRewardOwedTransition.params.map Param.name)
      (transitionSignature getRewardOwedTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "account"] [addr, addr]
    I.calldata = none
  simpa [config, addr] using decodeCalldata_address_address_none_short
    (cd := I.calldata) (x := "comet") (y := "account") hsz4 hshort

theorem cometRewardsDecode_getRewardOwed_none_noncanon_comet {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncComet : ¬ (getRewardOwedCometWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (getRewardOwedTransition.params.map Param.name)
      (transitionSignature getRewardOwedTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "account"] [addr, addr]
    I.calldata = none
  simpa [config, addr, getRewardOwedCometWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon0
      (cd := I.calldata) (x := "comet") (y := "account") hsz68 hbig hncComet

theorem cometRewardsDecode_getRewardOwed_none_noncanon_account {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hncAccount : ¬ (getRewardOwedAccountWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (getRewardOwedTransition.params.map Param.name)
      (transitionSignature getRewardOwedTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "account"] [addr, addr]
    I.calldata = none
  simpa [config, addr, getRewardOwedCometWord, getRewardOwedAccountWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon1
      (cd := I.calldata) (x := "comet") (y := "account")
      hsz68 hbig hcanonComet hncAccount

theorem cometRewardsDecode_getRewardOwed_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (getRewardOwedTransition.params.map Param.name)
      (transitionSignature getRewardOwedTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "account"] [addr, addr]
    I.calldata = none
  simpa [config, addr] using decodeCalldata_address_address_none_huge
    (cd := I.calldata) (x := "comet") (y := "account") hbig

theorem cometRewardsGetRewardOwedSelector_size {I : ExecutionEnv}
    (hsel : selIs I (cometRewardsSelBytes 3)) :
    4 ≤ I.calldata.size :=
  calldata_size_ge_of_selIs I (cometRewardsSelBytes 3) rfl hsel

theorem cometRewardsDispatch_getRewardOwed {cd : ByteArray}
    (hsel : (cometRewardsSelBytes 3 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some getRewardOwedTransition := by
  have hcd : cd.extract 0 4 = cometRewardsSelBytes 3 :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [claimTransition, claimToTransition])
    (post := [governorTransition, rewardConfigTransition, rewardsClaimedTransition,
      setRewardConfigTransition, setRewardConfigWithMultiplierTransition,
      setRewardsClaimedTransition, transferGovernorTransition, withdrawTokenTransition])
    rfl rfl ?_ (by rw [selectorOf, getRewardOwedSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, claimSelectorBytes, hcd]
    decide
  · rw [selectorOf, claimToSelectorBytes, hcd]
    decide

theorem cometRewardsGetRewardOwedCalldataCheckOk {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨64⟩ = ⟨0⟩ :=
  cometRewardsRewardsClaimedCalldataCheckOk (I := I) hsz68 hsize hhi

theorem cometRewardsGetRewardOwedCalldataCheckShort {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨64⟩ = ⟨1⟩ :=
  cometRewardsRewardsClaimedCalldataCheckShort (I := I) hsz4 hsize hshort

theorem cometRewardsGetRewardOwedCalldataCheckHuge {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨64⟩ = ⟨1⟩ :=
  cometRewardsRewardsClaimedCalldataCheckHuge (I := I) hsize hbig

theorem cometRewardsGetRewardOwedX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsGetRewardOwedCalldataCheckShort (I := I) hsz4 hsize hshort
  obtain ⟨_, _, rd2266⟩ := hreach
  have rd2272 := evm_run rd2266 with [jumpdest, pop, swap3, swap1, swap3, callvalue]
  rw [hwv] at rd2272
  have rd2283 := evm_run rd2272 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    dup3, push1 ⟨3⟩, not, calldatasize, add, slt]
  rw [hslt] at rd2283
  exact evm_run rd2283 with [
    push2 ⟨670⟩, jumpiT (by decide) (by native_decide),
    jumpdest, pop, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsGetRewardOwedX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsGetRewardOwedCalldataCheckHuge (I := I) hsize hbig
  obtain ⟨_, _, rd2266⟩ := hreach
  have rd2272 := evm_run rd2266 with [jumpdest, pop, swap3, swap1, swap3, callvalue]
  rw [hwv] at rd2272
  have rd2283 := evm_run rd2272 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    dup3, push1 ⟨3⟩, not, calldatasize, add, slt]
  rw [hslt] at rd2283
  exact evm_run rd2283 with [
    push2 ⟨670⟩, jumpiT (by decide) (by native_decide),
    jumpdest, pop, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsGetRewardOwedX_dec2831_comet {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2831⟩
      [⟨2298⟩, ⟨224⟩, ⟨4⟩, ⟨0⟩, ⟨255⟩, ⟨64⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt := cometRewardsGetRewardOwedCalldataCheckOk (I := I) hsz68 hsize hhi
  obtain ⟨_, _, rd2266⟩ := hreach
  have rd2272 := evm_run rd2266 with [jumpdest, pop, swap3, swap1, swap3, callvalue]
  rw [hwv] at rd2272
  have rd2283 := evm_run rd2272 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    dup3, push1 ⟨3⟩, not, calldatasize, add, slt]
  rw [hslt] at rd2283
  exact ⟨_, _, evm_run rd2283 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    push1 ⟨255⟩, swap3, swap4, push2 ⟨2298⟩, push2 ⟨2831⟩,
    jump (by native_decide)]⟩

theorem cometRewardsGetRewardOwedX_dec2298_comet {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2298⟩
      [getRewardOwedCometWord I, ⟨224⟩, ⟨4⟩, ⟨0⟩, ⟨255⟩, ⟨64⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2831⟩ :=
    cometRewardsGetRewardOwedX_dec2831_comet (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz68 hsize hhi hreach
  exact ⟨_, _, evm_run rd2831 with [
    jumpdest, push1 ⟨4⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, dup3, sub,
    push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land
            (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
            solcAddrMask =
          uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) := by
        exact solcAddrMask_clean (by
          simpa [getRewardOwedCometWord, calldataWord] using hcanonComet)
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean]
      exact u256_sub_self _),
    jump (by native_decide)]⟩

theorem cometRewardsGetRewardOwedX_dec2853_account {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2853⟩
      [⟨2307⟩, ⟨0⟩, ⟨224⟩, ⟨4⟩, getRewardOwedCometWord I, ⟨255⟩, ⟨64⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2298⟩ :=
    cometRewardsGetRewardOwedX_dec2298_comet (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz68 hsize hhi hcanonComet hreach
  exact ⟨_, _, evm_run rd2298 with [
    jumpdest, swap3, push2 ⟨2307⟩, push2 ⟨2853⟩, jump (by native_decide)]⟩

theorem cometRewardsGetRewardOwedX_dec2307_account {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (getRewardOwedAccountWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2307⟩
      [getRewardOwedAccountWord I, ⟨0⟩, ⟨224⟩, ⟨4⟩, getRewardOwedCometWord I,
        ⟨255⟩, ⟨64⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2853⟩ :=
    cometRewardsGetRewardOwedX_dec2853_account (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz68 hsize hhi hcanonComet hreach
  exact ⟨_, _, evm_run rd2853 with [
    jumpdest, push1 ⟨36⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, dup3, sub,
    push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land
            (uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32))
            solcAddrMask =
          uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32) := by
        exact solcAddrMask_clean (by
          simpa [getRewardOwedAccountWord, calldataWord] using hcanonAccount)
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean]
      exact u256_sub_self _),
    jump (by native_decide)]⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsGetRewardOwedX_noncanon_comet {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (getRewardOwedCometWord I)
      (UInt256.land (getRewardOwedCometWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2831⟩ :=
    cometRewardsGetRewardOwedX_dec2831_comet (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz68 hsize hhi hreach
  exact evm_run rd2831 with [
    jumpdest, push1 ⟨4⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, dup3, sub,
    push2 ⟨1004⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      exact u256_sub_ne_zero_of_ne (by
        intro heq
        have hclean :
            UInt256.eq (getRewardOwedCometWord I)
              (UInt256.land (getRewardOwedCometWord I) solcAddrMask) = ⟨1⟩ := by
          have heq' : getRewardOwedCometWord I =
              UInt256.land (getRewardOwedCometWord I) solcAddrMask := by
            simpa [getRewardOwedCometWord, calldataWord] using heq
          rw [← heq']
          exact uInt256_eq_self _
        rw [hclean] at hnc
        exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hnc))
      (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsGetRewardOwedX_noncanon_account {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (getRewardOwedAccountWord I)
      (UInt256.land (getRewardOwedAccountWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2853⟩ :=
    cometRewardsGetRewardOwedX_dec2853_account (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz68 hsize hhi hcanonComet hreach
  exact evm_run rd2853 with [
    jumpdest, push1 ⟨36⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, dup3, sub,
    push2 ⟨1004⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      exact u256_sub_ne_zero_of_ne (by
        intro heq
        have hclean :
            UInt256.eq (getRewardOwedAccountWord I)
              (UInt256.land (getRewardOwedAccountWord I) solcAddrMask) = ⟨1⟩ := by
          have heq' : getRewardOwedAccountWord I =
              UInt256.land (getRewardOwedAccountWord I) solcAddrMask := by
            simpa [getRewardOwedAccountWord, calldataWord] using heq
          rw [← heq']
          exact uInt256_eq_self _
        rw [hclean] at hnc
        exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hnc))
      (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

end Benchmarks.CompoundIII.CometRewards

theorem Reasoning.Reach.dup12_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP12, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
    (hov : t.length + 13 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
       else .ok
        (stSwap s
          (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t),
          .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP12, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup12 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t).length - 12
        + 13 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem Reasoning.Reach.RD.dup12
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP12, .none)) (hov : t.length + 13 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => Reasoning.Reach.dup12_xstep hc hp hdec hs hov)

namespace Benchmarks.CompoundIII.CometRewards

set_option maxHeartbeats 1000000 in
theorem cometRewardsGetRewardOwedX_configLoaded {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (getRewardOwedAccountWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2410⟩
      [ UInt256.isZero
          (rewardConfigTokenFromSlot0 (getRewardOwedRewardConfigSlot0Word σ I)),
        ⟨4⟩,
        getRewardOwedAccountWord I,
        getRewardOwedCometWord I,
        ⟨0⟩,
        UInt256.land (getRewardOwedCometWord I) solcAddrMask,
        solcAddrMask,
        ⟨32⟩,
        ⟨192⟩,
        ⟨64⟩ ]
      (getRewardOwedConfigMultiplierMem I (getRewardOwedRewardConfigSlot0Word σ I)
        (getRewardOwedMultiplierWord σ I))
      (UInt256.ofNat 10) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2307⟩ :=
    cometRewardsGetRewardOwedX_dec2307_account (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz68 hsize hhi hcanonComet hcanonAccount hreach
  have hslot := getRewardOwedRewardConfigSlotOf_eq_solc I hcanonComet
  let slot0 := getRewardOwedRewardConfigSlot0Word σ I
  let multiplier := getRewardOwedMultiplierWord σ I
  have rd2355 := evm_run rd2307 with [
    jumpdest, swap4, dup7,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap5, push2 ⟨2320⟩, dup7, push2 ⟨2976⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩, dup2, add, swap1, dup2, lt,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt, lor,
    push2 ⟨3003⟩, jumpiNT (by native_decide),
    push1 ⟨64⟩,
    raw mstore 0 getRewardOwedAlloc64Mem (UInt256.ofNat 3) (by decide) mem_cost
      (by unfold getRewardOwedAlloc64Mem Reasoning.Theory.writeWord; rfl)
      (by decide) (by evm_ov),
    jump (by jump_dest),
    jumpdest, dup3, dup7,
    raw mstore 6 (writeCascade getRewardOwedAlloc64Mem [(128, (⟨0⟩ : UInt256))])
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        unfold getRewardOwedAlloc64Mem Reasoning.Theory.writeCascade
          Reasoning.Theory.writeWord
        rfl) (by decide) (by evm_ov),
    dup3, push1 ⟨32⟩, dup1, swap8, add,
    raw mstore 3 getRewardOwedConfigZeroMem (UInt256.ofNat 6) (by decide) mem_cost
      (by
        unfold getRewardOwedConfigZeroMem getRewardOwedAlloc64Mem
        unfold Reasoning.Theory.writeCascade Reasoning.Theory.writeWord
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, dup1, push1 ⟨160⟩, shl, sub, swap5, dup6, dup4, and,
    swap5, dup6, dup6,
    raw mstore 0 (wordAt0Mem (getRewardOwedCometWord I) getRewardOwedConfigZeroMem)
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide, solcAddrMask_clean hcanonComet]
        unfold getRewardOwedConfigZeroMem getRewardOwedAlloc64Mem
        unfold Reasoning.Theory.writeCascade wordAt0Mem Reasoning.Theory.writeWord
        rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, dup9,
    raw mstore 0 (getRewardOwedRewardConfigHashMem I) (UInt256.ofNat 6) (by decide) mem_cost
      (by
        unfold getRewardOwedRewardConfigHashMem getRewardOwedConfigZeroMem
        unfold getRewardOwedAlloc64Mem twoWordHashMem wordAt32Mem wordAt0Mem
        unfold Reasoning.Theory.writeCascade Reasoning.Theory.writeWord
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, dup11, dup7,
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (getRewardOwedCometWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (getRewardOwedRewardConfigHashMem_keccakSlot I) (by decide) (by evm_ov)]
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2355⟩
    [solcMappingSlot ⟨1⟩ (getRewardOwedCometWord I), ⟨1⟩, ⟨224⟩, ⟨4⟩,
      getRewardOwedAccountWord I, getRewardOwedCometWord I, ⟨0⟩,
      UInt256.land (getRewardOwedCometWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩),
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩,
      ⟨32⟩, ⟨255⟩, ⟨64⟩]
    (getRewardOwedRewardConfigHashMem I) (UInt256.ofNat 6) ByteArray.empty
    (cA, σ) _ _ at rd2355
  rw [← hslot] at rd2355
  have rd2356 := Reasoning.Reach.RD.dup12 rd2355 (by native_decide) (by decide)
  have rd2358 := evm_run rd2356 with [
    raw mload 0 ⟨192⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (getRewardOwedRewardConfigHashMem_mload64 I) (by decide) (by evm_ov),
    swap11]
  have rd2359 := Reasoning.Reach.RD.dup12 rd2358 (by native_decide) (by decide)
  have rd2368 := evm_run rd2359 with [
    swap4, push2 ⟨2368⟩, dup6, push2 ⟨3025⟩, jump (by jump_dest),
    jumpdest, push1 ⟨128⟩, dup2, add, swap1, dup2, lt,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt, lor,
    push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩,
    raw mstore 0 (getRewardOwedConfigAllocMem I) (UInt256.ofNat 6) (by decide) mem_cost
      (by
        unfold getRewardOwedConfigAllocMem getRewardOwedRewardConfigHashMem getRewardOwedConfigZeroMem
        unfold getRewardOwedAlloc64Mem twoWordHashMem wordAt32Mem wordAt0Mem
        unfold Reasoning.Theory.writeCascade Reasoning.Theory.writeWord
        rfl)
      (by decide) (by evm_ov),
    jump (by jump_dest), jumpdest]
  have rdAfterSloadPre := evm_run rd2368 with [dup3]
  obtain ⟨_, _, rdAfterSload⟩ := rdAfterSloadPre.sload (by decide) (by evm_ov)
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) _
    (getRewardOwedRewardConfigSlot0Word σ I :: _) (getRewardOwedConfigAllocMem I)
    (UInt256.ofNat 6) ByteArray.empty (cA, σ) _ _ at rdAfterSload
  rw [show getRewardOwedRewardConfigSlot0Word σ I = slot0 from rfl] at rdAfterSload
  have rd2409pre := evm_run rdAfterSload with [
    swap1, dup12, dup3, and, dup1, swap7,
    raw mstore 3 (getRewardOwedConfigTokenMem I slot0) (UInt256.ofNat 7) (by decide) mem_cost
      (by
        unfold getRewardOwedConfigTokenMem getRewardOwedConfigAllocMem
        unfold getRewardOwedRewardConfigHashMem getRewardOwedConfigZeroMem getRewardOwedAlloc64Mem
        unfold twoWordHashMem wordAt32Mem wordAt0Mem Reasoning.Theory.writeCascade
        unfold Reasoning.Theory.writeWord rewardConfigTokenFromSlot0 slot0
        rfl)
      (by decide) (by evm_ov),
    dup14, dup14, dup7, dup1, push1 ⟨64⟩, shl, sub, dup5, push1 ⟨160⟩, shr, and,
    swap2, add,
    raw mstore 3 (getRewardOwedConfigRescaleMem I slot0) (UInt256.ofNat 8) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩ =
          UInt256.ofNat (2 ^ 64 - 1) from by native_decide]
        unfold getRewardOwedConfigRescaleMem getRewardOwedConfigTokenMem getRewardOwedConfigAllocMem
        unfold getRewardOwedRewardConfigHashMem getRewardOwedConfigZeroMem getRewardOwedAlloc64Mem
        unfold twoWordHashMem wordAt32Mem wordAt0Mem Reasoning.Theory.writeCascade
        unfold Reasoning.Theory.writeWord rewardConfigRescaleFromSlot0
        unfold rewardConfigTokenFromSlot0 slot0
        rfl) (by decide) (by evm_ov),
    shr, and, iszero, iszero, dup13, dup13, add,
    raw mstore 3 (getRewardOwedConfigShouldMem I slot0) (UInt256.ofNat 9) (by decide) mem_cost
      (by
        unfold getRewardOwedConfigShouldMem getRewardOwedConfigRescaleMem
        unfold getRewardOwedConfigTokenMem getRewardOwedConfigAllocMem getRewardOwedRewardConfigHashMem
        unfold getRewardOwedConfigZeroMem getRewardOwedAlloc64Mem twoWordHashMem wordAt32Mem wordAt0Mem
        unfold Reasoning.Theory.writeCascade Reasoning.Theory.writeWord
        unfold rewardConfigShouldUpscaleFromSlot0 rewardConfigShouldUpscaleRawFromSlot0
        unfold rewardConfigRescaleFromSlot0 rewardConfigTokenFromSlot0 slot0
        rfl) (by decide) (by evm_ov),
    add]
  obtain ⟨_, _, rdAfterMultiplier⟩ := rd2409pre.sload (by decide) (by evm_ov)
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) _
    (getRewardOwedMultiplierWord σ I :: _) (getRewardOwedConfigShouldMem I slot0)
    (UInt256.ofNat 9) ByteArray.empty (cA, σ) _ _ at rdAfterMultiplier
  rw [show getRewardOwedMultiplierWord σ I = multiplier from rfl] at rdAfterMultiplier
  have rd2409 := evm_run rdAfterMultiplier with [
    push1 ⟨96⟩, dup11, add,
    raw mstore 3 (getRewardOwedConfigMultiplierMem I slot0 multiplier) (UInt256.ofNat 10)
      (by decide) mem_cost
      (by
        unfold getRewardOwedConfigMultiplierMem getRewardOwedConfigShouldMem
        unfold getRewardOwedConfigRescaleMem getRewardOwedConfigTokenMem getRewardOwedConfigAllocMem
        unfold getRewardOwedRewardConfigHashMem getRewardOwedConfigZeroMem getRewardOwedAlloc64Mem
        unfold twoWordHashMem wordAt32Mem wordAt0Mem Reasoning.Theory.writeCascade
        unfold Reasoning.Theory.writeWord
        unfold rewardConfigShouldUpscaleFromSlot0 rewardConfigShouldUpscaleRawFromSlot0
        unfold rewardConfigRescaleFromSlot0 rewardConfigTokenFromSlot0 slot0 multiplier
        rfl)
      (by decide) (by evm_ov),
    iszero]
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  rw [hmask] at rd2409
  exact ⟨_, _, by
    convert rd2409 using 1⟩

theorem cometRewardsGetRewardOwedX_accrueNoCode {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (getRewardOwedAccountWord I).toNat < EVM.addressModulus)
    (hnz : rewardConfigTokenFromSlot0 (getRewardOwedRewardConfigSlot0Word σ I) ≠ ⟨0⟩)
    (hnoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord σ
        (UInt256.land (getRewardOwedCometWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2410⟩ :=
    cometRewardsGetRewardOwedX_configLoaded (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz68 hsize hhi hcanonComet hcanonAccount hreach
  have htokenNZ :
      UInt256.isZero (rewardConfigTokenFromSlot0 (getRewardOwedRewardConfigSlot0Word σ I)) =
        ⟨0⟩ := by
    exact isZero_eq_zero_of_ne hnz
  rw [htokenNZ] at rd2410
  have rd2414 := evm_run rd2410 with [
    push2 ⟨2592⟩, jumpiNT (by decide)]
  have rd2415 := evm_run rd2414 with [dup5]
  obtain ⟨_, _, rd2416⟩ :=
    Reasoning.Reach.RD.uniswapExtcodesize rd2415 (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  rw [hnoCode] at rd2416
  have rd2420 := evm_run rd2416 with [iszero, push2 ⟨797⟩]
  exact evm_run rd2420 with [
    jumpiT (by native_decide) (by jump_dest),
    jumpdest, dup4, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsGetRewardOwedX_call_accrueAccount {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (getRewardOwedAccountWord I).toNat < EVM.addressModulus)
    (hnz : rewardConfigTokenFromSlot0 (getRewardOwedRewardConfigSlot0Word σ I) ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ
        (UInt256.land (getRewardOwedCometWord I) solcAddrMask) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ gasArg k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      getRewardOwedAccrueAccountCallPc
      [ gasArg,
        UInt256.land (getRewardOwedCometWord I) solcAddrMask,
        ⟨0⟩,
        ⟨320⟩,
        getRewardOwedAccrueAccountCallSize,
        ⟨320⟩,
        ⟨0⟩,
        ⟨320⟩,
        UInt256.land (getRewardOwedAccountWord I) solcAddrMask,
        getRewardOwedAccountWord I,
        getRewardOwedCometWord I,
        ⟨0⟩,
        UInt256.land (getRewardOwedCometWord I) solcAddrMask,
        solcAddrMask,
        ⟨32⟩,
        ⟨192⟩,
        ⟨64⟩ ]
      (getRewardOwedAccrueAccountCalldataMem I (getRewardOwedRewardConfigSlot0Word σ I)
        (getRewardOwedMultiplierWord σ I))
      getRewardOwedAccrueAccountPostCallAw ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2410⟩ :=
    cometRewardsGetRewardOwedX_configLoaded (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz68 hsize hhi hcanonComet hcanonAccount hreach
  let slot0 := getRewardOwedRewardConfigSlot0Word σ I
  let multiplier := getRewardOwedMultiplierWord σ I
  have htokenNZ :
      UInt256.isZero (rewardConfigTokenFromSlot0 (getRewardOwedRewardConfigSlot0Word σ I)) =
        ⟨0⟩ := by
    exact isZero_eq_zero_of_ne hnz
  rw [htokenNZ] at rd2410
  have rd2414 := evm_run rd2410 with [
    push2 ⟨2592⟩, jumpiNT (by decide)]
  have rd2415 := evm_run rd2414 with [dup5]
  obtain ⟨_, _, rd2416⟩ :=
    Reasoning.Reach.RD.uniswapExtcodesize rd2415 (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2417 := evm_run rd2416 with [iszero]
  rw [isZero_eq_zero_of_ne hcodeSize] at rd2417
  have rd2421 := evm_run rd2417 with [
    push2 ⟨797⟩, jumpiNT (by decide)]
  have hcleanAccount :
      UInt256.land (getRewardOwedAccountWord I) solcAddrMask =
        getRewardOwedAccountWord I := by
    exact solcAddrMask_clean (by simpa [getRewardOwedAccountWord, calldataWord] using
      hcanonAccount)
  have rd2433 := evm_run rd2421 with [
    dup9,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by decide)
      mem_cost (getRewardOwedConfigMultiplierMem_mload64 I slot0 multiplier)
      (by decide) (by evm_ov),
    push4 ⟨3219561613⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 3 (getRewardOwedAccrueAccountSelectorMem I slot0 multiplier)
      (UInt256.ofNat 11) (by decide) mem_cost
      (by
        unfold getRewardOwedAccrueAccountSelectorMem getRewardOwedConfigMultiplierMem
        unfold getRewardOwedConfigShouldMem getRewardOwedConfigRescaleMem
        unfold getRewardOwedConfigTokenMem getRewardOwedConfigAllocMem
        unfold getRewardOwedRewardConfigHashMem getRewardOwedConfigZeroMem
        unfold getRewardOwedAlloc64Mem twoWordHashMem wordAt32Mem wordAt0Mem
        unfold Reasoning.Theory.writeCascade Reasoning.Theory.writeWord
        unfold rewardConfigShouldUpscaleFromSlot0 rewardConfigShouldUpscaleRawFromSlot0
        unfold rewardConfigRescaleFromSlot0 rewardConfigTokenFromSlot0 slot0 multiplier
        rfl)
      (by decide) (by evm_ov)]
  have rd2442 := evm_run rd2433 with [
    dup3, dup8, and, swap2, dup2, add, dup3, swap1,
    raw mstore 3 (getRewardOwedAccrueAccountCalldataMem I slot0 multiplier)
      getRewardOwedAccrueAccountPostCallAw (by decide) mem_cost
      (by
        rw [show ((⟨320⟩ : UInt256) + ⟨4⟩).toNat = 324 from by native_decide]
        rw [u256_land_comm solcAddrMask (getRewardOwedAccountWord I), hcleanAccount]
        unfold getRewardOwedAccrueAccountCalldataMem getRewardOwedAccrueAccountSelectorMem
        unfold getRewardOwedConfigMultiplierMem getRewardOwedConfigShouldMem
        unfold getRewardOwedConfigRescaleMem getRewardOwedConfigTokenMem
        unfold getRewardOwedConfigAllocMem getRewardOwedRewardConfigHashMem
        unfold getRewardOwedConfigZeroMem getRewardOwedAlloc64Mem twoWordHashMem
        unfold wordAt32Mem wordAt0Mem Reasoning.Theory.writeCascade
        unfold Reasoning.Theory.writeWord rewardConfigShouldUpscaleFromSlot0
        unfold rewardConfigShouldUpscaleRawFromSlot0 rewardConfigRescaleFromSlot0
        unfold rewardConfigTokenFromSlot0 slot0 multiplier
        rfl)
      (by decide) (by evm_ov)]
  obtain ⟨gasArg, rd2450⟩ := evm_run rd2442 with [
    dup5, dup2, push1 ⟨36⟩, dup2, dup4, dup11, gas]
  rw [u256_land_comm solcAddrMask (getRewardOwedAccountWord I)] at rd2450
  exact ⟨gasArg, _, _, by
    convert rd2450 using 1⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsGetRewardOwedX_call_accrueAccount_made
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (getRewardOwedAccountWord I).toNat < EVM.addressModulus)
    (hnz : rewardConfigTokenFromSlot0 (getRewardOwedRewardConfigSlot0Word σ_evm I) ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_evm
        (UInt256.land (getRewardOwedCometWord I) solcAddrMask) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    ∃ cA' σ'_evm σ'_solm A'_solm z out k C,
      typedCallViaEVM config
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (getRewardOwedCometTarget I)) "accrueAccount" 0
        (getRewardOwedAccrueAccountArgs I)
        (z,
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          out) true ∧
      accountMapEquiv σ'_evm σ'_solm ∧
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (getRewardOwedAccrueAccountCallPc + ⟨1⟩)
        (getRewardOwedAccrueAccountPostCallStack z I)
        (getRewardOwedAccrueAccountPostCallMem I
          (getRewardOwedRewardConfigSlot0Word σ_evm I)
          (getRewardOwedMultiplierWord σ_evm I) out)
        getRewardOwedAccrueAccountPostCallAw out (cA', σ'_evm) k C ∧
      out.size < UInt256.size := by
  obtain ⟨gasArg, k0, C0, rd2450⟩ :=
    cometRewardsGetRewardOwedX_call_accrueAccount (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hwv hsz68 hsize hhi hcanonComet hcanonAccount hnz hcodeSize hreach
  have rd2450Call :
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        getRewardOwedAccrueAccountCallPc
        (gasArg :: UInt256.land (getRewardOwedCometWord I) solcAddrMask :: ⟨0⟩ ::
          ⟨320⟩ :: getRewardOwedAccrueAccountCallSize :: ⟨320⟩ :: ⟨0⟩ ::
          getRewardOwedAccrueAccountPostCallTail I)
        (getRewardOwedAccrueAccountCalldataMem I (getRewardOwedRewardConfigSlot0Word σ_evm I)
          (getRewardOwedMultiplierWord σ_evm I))
        getRewardOwedAccrueAccountPostCallAw ByteArray.empty (cA, σ_evm) k0 C0 := by
    simpa [getRewardOwedAccrueAccountPostCallTail] using rd2450
  have hdecCall :
      decode cometRewardsBytecode getRewardOwedAccrueAccountCallPc = some (.CALL, .none) := by
    unfold getRewardOwedAccrueAccountCallPc
    native_decide
  obtain ⟨cA', σ'_evm, z, out, A_in, callGas, k', C', hΘ, rd2451, houtSize⟩ :=
    Reasoning.Reach.RD.call (t := getRewardOwedAccrueAccountPostCallTail I)
      rd2450Call hdecCall hdepth
      (by simp [getRewardOwedAccrueAccountPostCallTail])
  obtain ⟨g'', A'_evm, hΘeq⟩ := hΘ
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hEq
    rw [hEq] at hdepth
    exact absurd hdepth (by decide)
  have hdepthNe :
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.depth ≠
        1024 := by
    simpa [initState] using hdepthNeI
  have htgt := getRewardOwedCometTarget_eq_targetWord I hcanonComet
  have hcd := getRewardOwedAccrueAccountCalldataMem_encode_args I
    (getRewardOwedRewardConfigSlot0Word σ_evm I)
    (getRewardOwedMultiplierWord σ_evm I) hcanonAccount
  have hcallE :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (getRewardOwedCometTarget I)) "accrueAccount" 0
        (getRewardOwedAccrueAccountArgs I)
        (z,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          out) true := by
    refine callCoincides
      (cfg := config)
      (evm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (name := "accrueAccount") (args := getRewardOwedAccrueAccountArgs I)
      (tgt := EVM.address (getRewardOwedCometTarget I))
      (targetWord := UInt256.land (getRewardOwedCometWord I) solcAddrMask)
      (cA' := cA') (σ' := σ'_evm) (A' := A'_evm) (A_in := A_in)
      (z := z) (o := out) (g'' := g'') (callGas := callGas)
      (mem := getRewardOwedAccrueAccountCalldataMem I
        (getRewardOwedRewardConfigSlot0Word σ_evm I)
        (getRewardOwedMultiplierWord σ_evm I))
      (inOff := ⟨320⟩) (inSize := getRewardOwedAccrueAccountCallSize)
      (callPerm := true)
      hdepthNe htgt hcd ?_
    simpa [initState, hperm] using hΘeq
  obtain ⟨σ'_solm, A'_solm, hcallSolm, hPostAccounts⟩ :=
    typedCallViaEVM_initState_accountMapEquiv hcallE hAccounts
  exact ⟨cA', σ'_evm, σ'_solm, A'_solm, z, out, k', C',
    hcallSolm, hPostAccounts, by
      simpa [getRewardOwedAccrueAccountPostCallStack,
        getRewardOwedAccrueAccountPostCallTail, getRewardOwedAccrueAccountPostCallMem,
        getRewardOwedAccrueAccountPostCallAw, getRewardOwedAccrueAccountCallSize]
        using rd2451,
    houtSize⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsGetRewardOwedX_after_accrueAccount_failure
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (getRewardOwedAccrueAccountCallPc + ⟨1⟩)
      (getRewardOwedAccrueAccountPostCallStack false I)
      (getRewardOwedAccrueAccountPostCallMem I slot0 multiplier out)
      getRewardOwedAccrueAccountPostCallAw out acc k C)
    (houtSize : out.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd2451 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2451⟩ (getRewardOwedAccrueAccountPostCallStack false I)
      (getRewardOwedAccrueAccountPostCallMem I slot0 multiplier out)
      getRewardOwedAccrueAccountPostCallAw out acc k C := by
    simpa [getRewardOwedAccrueAccountCallPc] using rd
  have rd2582 := evm_run rd2451 with [
    dup1, iszero, push2 ⟨2582⟩, jumpiT (by native_decide) (by jump_dest)]
  let fp : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥
        (getRewardOwedAccrueAccountPostCallMem I slot0 multiplier out).size
        ∨ (⟨64⟩ : UInt256) ≥ getRewardOwedAccrueAccountPostCallAw * ⟨32⟩ then
      ⟨0⟩
    else
      UInt256.ofNat (fromByteArrayBigEndian
        ((getRewardOwedAccrueAccountPostCallMem I slot0 multiplier out).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtSize
  have rd2583pre := evm_run rd2582 with [jumpdest, dup11]
  have rd2584 := Reasoning.Reach.RD.mload 0 fp getRewardOwedAccrueAccountPostCallAw
    rd2583pre (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        getRewardOwedAccrueAccountPostCallAw, getRewardOwedAccrueAccountCallSize]
      native_decide)
    (by rfl)
    (by native_decide)
    (by simp)
  have rd2587pre := evm_run rd2584 with [returndatasize, dup8, dup3]
  let mem2 : ByteArray :=
    out.write 0 (getRewardOwedAccrueAccountPostCallMem I slot0 multiplier out)
      fp.toNat rdsz.toNat
  let aw2 : UInt256 :=
    UInt256.ofNat (MachineState.M getRewardOwedAccrueAccountPostCallAw.toNat fp.toNat
      rdsz.toNat)
  have rd2588 := Reasoning.Reach.RD.returndatacopy
    (Cₘ aw2 - Cₘ getRewardOwedAccrueAccountPostCallAw) mem2 aw2 rd2587pre
    (by native_decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hrdsz_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2, rdsz])
    (by rfl)
    (by rfl)
    (by simp)
  have rd2590 := evm_run rd2588 with [returndatasize, swap1]
  exact Reasoning.Reach.RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M aw2.toNat fp.toNat rdsz.toNat)) - Cₘ aw2)
    rd2590 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, rdsz])
    (by simp)

set_option maxHeartbeats 1000000 in
theorem cometRewardsGetRewardOwedX_call_baseTrackingAccrued
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {accrueOut : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {k C : ℕ}
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (getRewardOwedAccountWord I).toNat < EVM.addressModulus)
    (houtSize : accrueOut.size < UInt256.size)
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (getRewardOwedAccrueAccountCallPc + ⟨1⟩)
      (getRewardOwedAccrueAccountPostCallStack true I)
      (getRewardOwedAccrueAccountPostCallMem I slot0 multiplier accrueOut)
      getRewardOwedAccrueAccountPostCallAw accrueOut (cA', σ') k C) :
    ∃ gasArg k' C', RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) getRewardOwedBaseTrackingCallPc
      (gasArg :: UInt256.land (getRewardOwedCometWord I) solcAddrMask ::
        ⟨320⟩ :: getRewardOwedBaseTrackingCallSize :: ⟨320⟩ :: ⟨32⟩ ::
        getRewardOwedBaseTrackingPostCallTail (getRewardOwedClaimedWord σ' I))
      (getRewardOwedBaseTrackingCalldataMem I slot0 multiplier accrueOut)
      getRewardOwedBaseTrackingCallAw accrueOut (cA', σ') k' C' := by
  have rd2451 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2451⟩
      [⟨1⟩, ⟨320⟩, UInt256.land (getRewardOwedAccountWord I) solcAddrMask,
        getRewardOwedAccountWord I, getRewardOwedCometWord I, ⟨0⟩,
        UInt256.land (getRewardOwedCometWord I) solcAddrMask, solcAddrMask,
        ⟨32⟩, ⟨192⟩, ⟨64⟩]
      (getRewardOwedAccrueAccountPostCallMem I slot0 multiplier accrueOut)
      getRewardOwedAccrueAccountPostCallAw accrueOut (cA', σ') k C := by
    simpa [getRewardOwedAccrueAccountCallPc,
      getRewardOwedAccrueAccountPostCallStack, getRewardOwedAccrueAccountPostCallTail] using rd
  have rd2466 := evm_run rd2451 with [
    dup1, iszero, push2 ⟨2582⟩, jumpiNT (by native_decide),
    swap1, dup10, swap4, swap3, swap2, push2 ⟨2561⟩,
    jumpiT (by native_decide) (by jump_dest),
    jumpdest, swap5, push2 ⟨2575⟩, push2 ⟨2499⟩, swap6, swap7,
    push2 ⟨3052⟩, jump (by jump_dest)]
  have rd2466' := evm_run rd2466 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup2, gt,
    push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩,
    raw mstore 0 (getRewardOwedAccrueAccountAfterAllocMem I slot0 multiplier accrueOut)
      getRewardOwedAccrueAccountPostCallAw (by native_decide) mem_cost
      (by
        unfold getRewardOwedAccrueAccountAfterAllocMem
        rfl)
      (by native_decide) (by evm_ov),
    jump (by jump_dest), jumpdest, swap5, swap4, push2 ⟨2466⟩,
    jump (by jump_dest)]
  have rd2475pre := evm_run rd2466' with [
    jumpdest, pop, dup5, swap6, push2 ⟨2499⟩, swap5, swap6]
  have rd2476 := evm_run rd2475pre with [
    raw mstore 0
      (wordAt0Mem (UInt256.land (getRewardOwedCometWord I) solcAddrMask)
        (getRewardOwedAccrueAccountAfterAllocMem I slot0 multiplier accrueOut))
      getRewardOwedAccrueAccountPostCallAw (by native_decide) mem_cost
      (by
        unfold wordAt0Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd2480 := evm_run rd2476 with [
    push1 ⟨2⟩, dup9,
    raw mstore 0 (getRewardOwedClaimedInnerHashMem I slot0 multiplier accrueOut)
      getRewardOwedAccrueAccountPostCallAw (by native_decide) mem_cost
      (by
        unfold getRewardOwedClaimedInnerHashMem twoWordHashMem wordAt32Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have hinnerHash :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((getRewardOwedClaimedInnerHashMem I slot0 multiplier accrueOut)
            |>.readWithPadding 0 64))) =
        solcMappingSlot ⟨2⟩ (UInt256.land (getRewardOwedCometWord I) solcAddrMask) := by
    unfold getRewardOwedClaimedInnerHashMem
    exact twoWordHashMem_solcMappingSlot_of_ge ⟨2⟩
      (UInt256.land (getRewardOwedCometWord I) solcAddrMask)
      (le_trans (by norm_num) <|
        getRewardOwedAccrueAccountAfterAllocMem_size_ge320 I slot0 multiplier houtSize)
  have rd2482pre := evm_run rd2480 with [dup10, dup7]
  have rd2483 := rd2482pre.keccak256 0
    (solcMappingSlot ⟨2⟩ (UInt256.land (getRewardOwedCometWord I) solcAddrMask))
    getRewardOwedAccrueAccountPostCallAw (by native_decide) mem_cost
    hinnerHash (by native_decide) (by evm_ov)
  have rd2487 := evm_run rd2483 with [
    swap1, push1 ⟨0⟩,
    raw mstore 0
      (wordAt0Mem (UInt256.land (getRewardOwedAccountWord I) solcAddrMask)
        (getRewardOwedClaimedInnerHashMem I slot0 multiplier accrueOut))
      getRewardOwedAccrueAccountPostCallAw (by native_decide) mem_cost
      (by
        unfold wordAt0Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd2489 := evm_run rd2487 with [
    dup8,
    raw mstore 0 (getRewardOwedClaimedOuterHashMem I slot0 multiplier accrueOut)
      getRewardOwedAccrueAccountPostCallAw (by native_decide) mem_cost
      (by
        unfold getRewardOwedClaimedOuterHashMem twoWordHashMem wordAt32Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have houterHash :=
    getRewardOwedClaimedOuterHashMem_keccakSlot I slot0 multiplier houtSize
      hcanonComet hcanonAccount
  have rd2493pre := (evm_run rd2489 with [dup9, push1 ⟨0⟩]).keccak256 0
    (getRewardOwedRewardsClaimedSlotOf I)
    getRewardOwedAccrueAccountPostCallAw (by native_decide) mem_cost
    houterHash (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2494₀⟩ := rd2493pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2494⟩ : ∃ k1 C1, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2494⟩
      [getRewardOwedClaimedWord σ' I, getRewardOwedAccountWord I, ⟨192⟩,
        ⟨2499⟩, getRewardOwedCometWord I, ⟨0⟩, solcAddrMask, ⟨32⟩,
        ⟨192⟩, ⟨64⟩]
      (getRewardOwedClaimedOuterHashMem I slot0 multiplier accrueOut)
      getRewardOwedAccrueAccountPostCallAw accrueOut (cA', σ') k1 C1 := by
    exact ⟨_, _, by
      simpa [getRewardOwedClaimedWord] using rd2494₀⟩
  have rd3679 := evm_run rd2494 with [
    swap4, push2 ⟨3679⟩, jump (by jump_dest)]
  have hcleanAccount :
      UInt256.land (getRewardOwedAccountWord I) solcAddrMask =
        getRewardOwedAccountWord I := by
    exact solcAddrMask_clean (by simpa [getRewardOwedAccountWord, calldataWord] using
      hcanonAccount)
  have rd3682 := evm_run rd3679 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ getRewardOwedBaseTrackingCallAw (by native_decide)
      mem_cost
      (getRewardOwedClaimedOuterHashMem_mload64 I slot0 multiplier houtSize)
      (by native_decide) (by evm_ov)]
  have rd3692 := evm_run rd3682 with [
    push4 ⟨719776253⟩, push1 ⟨226⟩, shl, dup2,
    raw mstore 0 (getRewardOwedBaseTrackingSelectorMem I slot0 multiplier accrueOut)
      getRewardOwedBaseTrackingCallAw (by native_decide) mem_cost
      (by
        unfold getRewardOwedBaseTrackingSelectorMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3708 := evm_run rd3692 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap3, dup4, and,
    push1 ⟨4⟩, dup3, add,
    raw mstore 0 (getRewardOwedBaseTrackingCalldataMem I slot0 multiplier accrueOut)
      getRewardOwedBaseTrackingCallAw (by native_decide) mem_cost
      (by
        rw [show ((⟨320⟩ : UInt256) + ⟨4⟩).toNat = 324 from by native_decide]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [u256_land_comm solcAddrMask (getRewardOwedAccountWord I), hcleanAccount]
        unfold getRewardOwedBaseTrackingCalldataMem getRewardOwedBaseTrackingSelectorMem
        rfl)
      (by native_decide) (by evm_ov)]
  obtain ⟨gasArg, rd3723⟩ := evm_run rd3708 with [
    swap3, swap2, push1 ⟨32⟩, swap2, dup5, swap2, push1 ⟨36⟩,
    swap2, dup4, swap2, and, gas]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by decide] at rd3723
  rw [u256_land_comm solcAddrMask (getRewardOwedCometWord I)] at rd3723
  exact ⟨gasArg, _, _, by
    simpa [getRewardOwedBaseTrackingCallPc, getRewardOwedBaseTrackingCallSize,
      getRewardOwedBaseTrackingPostCallTail] using rd3723⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsGetRewardOwedX_call_baseTrackingAccrued_made
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {accrueOut : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm σ'_solm : AccountMap}
    {A'_solm : Substate} {k C : ℕ}
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (getRewardOwedAccountWord I).toNat < EVM.addressModulus)
    (hdepth : I.depth.val < 1024)
    (hPostAccounts : accountMapEquiv σ'_evm σ'_solm)
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ_evm σ₀ g A I)
      (getRewardOwedAccrueAccountCallPc + ⟨1⟩)
      (getRewardOwedAccrueAccountPostCallStack true I)
      (getRewardOwedAccrueAccountPostCallMem I slot0 multiplier accrueOut)
      getRewardOwedAccrueAccountPostCallAw accrueOut (cA', σ'_evm) k C)
    (haccrueOutSize : accrueOut.size < UInt256.size) :
    ∃ cA'' σ''_evm σ''_solm A''_solm z baseOut k' C',
      typedCallViaEVM config
        { initState cA gh bl σ_solm σ₀ g A I with
            accountMap := σ'_solm
            substate := A'_solm
            createdAccounts := cA' }
        (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (z,
          { { initState cA gh bl σ_solm σ₀ g A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' } with
              accountMap := σ''_solm
              substate := A''_solm
              createdAccounts := cA'' },
          baseOut) false ∧
      accountMapEquiv σ''_evm σ''_solm ∧
      RD cometRewardsBytecode I g (initState cA gh bl σ_evm σ₀ g A I)
        (getRewardOwedBaseTrackingCallPc + ⟨1⟩)
        (getRewardOwedBaseTrackingPostCallStack z (getRewardOwedClaimedWord σ'_evm I))
        (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut)
        getRewardOwedBaseTrackingPostCallAw baseOut (cA'', σ''_evm) k' C' ∧
      baseOut.size < UInt256.size ∧
      baseOut.size < 2 ^ 255 := by
  obtain ⟨gasArg, k0, C0, rd3723⟩ :=
    cometRewardsGetRewardOwedX_call_baseTrackingAccrued
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (slot0 := slot0) (multiplier := multiplier)
      (accrueOut := accrueOut) (cA' := cA') (σ' := σ'_evm)
      hcanonComet hcanonAccount haccrueOutSize rd
  have rd3723Call :
      RD cometRewardsBytecode I g (initState cA gh bl σ_evm σ₀ g A I)
        getRewardOwedBaseTrackingCallPc
        (gasArg :: UInt256.land (getRewardOwedCometWord I) solcAddrMask ::
          ⟨320⟩ :: getRewardOwedBaseTrackingCallSize :: ⟨320⟩ :: ⟨32⟩ ::
          getRewardOwedBaseTrackingPostCallTail (getRewardOwedClaimedWord σ'_evm I))
        (getRewardOwedBaseTrackingCalldataMem I slot0 multiplier accrueOut)
        getRewardOwedBaseTrackingCallAw accrueOut (cA', σ'_evm) k0 C0 := by
    simpa [getRewardOwedBaseTrackingPostCallTail] using rd3723
  have hdecCall :
      decode cometRewardsBytecode getRewardOwedBaseTrackingCallPc =
        some (.STATICCALL, .none) := by
    unfold getRewardOwedBaseTrackingCallPc
    native_decide
  obtain ⟨cA'', σ''_evm, z, baseOut, A_in, callGas, k', C', hΘ, rd3724,
      _houtSize⟩ :=
    RD.uniswapStaticcall (t :=
        getRewardOwedBaseTrackingPostCallTail (getRewardOwedClaimedWord σ'_evm I))
      rd3723Call hdecCall hdepth
      (by simp [getRewardOwedBaseTrackingPostCallTail])
  obtain ⟨g'', A''_evm, hΘeq⟩ := hΘ
  let evmEBase : EVM.State :=
    { initState cA gh bl σ_evm σ₀ g A I with
        accountMap := σ'_evm
        substate := A'_solm
        createdAccounts := cA' }
  let evmSBase : EVM.State :=
    { initState cA gh bl σ_solm σ₀ g A I with
        accountMap := σ'_solm
        substate := A'_solm
        createdAccounts := cA' }
  have houtSmall : baseOut.size < 2 ^ 138 := by
    exact Theta_returnData_size_lt_2pow138_of_eq
      (blob := I.blobVersionedHashes) (cA := cA')
      (gh := (initState cA gh bl σ_evm σ₀ g A I).genesisBlockHeader)
      (blocks := (initState cA gh bl σ_evm σ₀ g A I).blocks)
      (σ := σ'_evm)
      (σ₀ := (initState cA gh bl σ_evm σ₀ g A I).σ₀)
      (A := A_in)
      (s := AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner))
      (o := I.sender)
      (r := AccountAddress.ofUInt256 (UInt256.land (getRewardOwedCometWord I) solcAddrMask))
      (c := toExecute σ'_evm
        (AccountAddress.ofUInt256 (UInt256.land (getRewardOwedCometWord I) solcAddrMask)))
      (g := callGas) (p := UInt256.ofNat I.gasPrice)
      (v := ⟨0⟩) (v' := ⟨0⟩)
      (d := (getRewardOwedBaseTrackingCalldataMem I slot0 multiplier accrueOut)
        |>.readWithPadding 320 getRewardOwedBaseTrackingCallSize.toNat)
      (e := I.depth + 1) (H := I.header) (w := false)
      hΘeq
      (by exact Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)
  have houtUInt : baseOut.size < UInt256.size := by
    have hsz : UInt256.size = 2 ^ 256 := by decide
    omega
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hEq
    rw [hEq] at hdepth
    exact absurd hdepth (by decide)
  have hdepthNe : evmEBase.executionEnv.depth ≠ 1024 := by
    simpa [evmEBase, initState] using hdepthNeI
  have htgt := getRewardOwedCometTarget_eq_targetWord I hcanonComet
  have hcd := getRewardOwedBaseTrackingCalldataMem_encode_args I slot0 multiplier
    haccrueOutSize hcanonAccount
  have hcallE :
      typedCallViaEVM config evmEBase
        (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (z,
          { evmEBase with
              accountMap := σ''_evm
              substate := A''_evm
              createdAccounts := cA'' },
          baseOut) false := by
    refine callCoincides
      (cfg := config) (evm := evmEBase)
      (name := "baseTrackingAccrued") (args := getRewardAccruedBaseTrackingArgs I)
      (tgt := EVM.address (getRewardOwedCometTarget I))
      (targetWord := UInt256.land (getRewardOwedCometWord I) solcAddrMask)
      (cA' := cA'') (σ' := σ''_evm) (A' := A''_evm) (A_in := A_in)
      (z := z) (o := baseOut) (g'' := g'') (callGas := callGas)
      (mem := getRewardOwedBaseTrackingCalldataMem I slot0 multiplier accrueOut)
      (inOff := ⟨320⟩) (inSize := getRewardOwedBaseTrackingCallSize)
      (callPerm := false)
      hdepthNe htgt hcd ?_
    simpa [evmEBase, initState] using hΘeq
  obtain ⟨σ''_solm, A''_solm, hcallSolm, hPostAccounts'⟩ :=
    typedCallViaEVM_accountMapEquiv
      (evm_solm := evmSBase) hcallE
      (by simpa [evmEBase, evmSBase, initState] using hPostAccounts)
      (by simp [evmEBase, evmSBase, initState])
      (by simp [evmEBase, evmSBase])
      (by simp [evmEBase, evmSBase, initState])
      (by simp [evmEBase, evmSBase, initState])
      (by simp [evmEBase, evmSBase])
      (by simp [evmEBase, evmSBase, initState])
  exact ⟨cA'', σ''_evm, σ''_solm, A''_solm, z, baseOut, k', C',
    by
      simpa [evmSBase, initState] using hcallSolm,
    hPostAccounts',
    by
      simpa [getRewardOwedBaseTrackingPostCallStack,
        getRewardOwedBaseTrackingPostCallTail, getRewardOwedBaseTrackingPostCallMem,
        getRewardOwedBaseTrackingPostCallAw, getRewardOwedBaseTrackingCallSize]
        using rd3724,
    houtUInt,
    by omega⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsGetRewardOwedX_after_baseTracking_failure
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {accrueOut baseOut : ByteArray}
    {claimed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (getRewardOwedBaseTrackingCallPc + ⟨1⟩)
      (getRewardOwedBaseTrackingPostCallStack false claimed)
      (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k C)
    (haccrueSize : accrueOut.size < UInt256.size)
    (hbaseSize : baseOut.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd3724 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3724⟩
      [⟨0⟩, ⟨192⟩, ⟨320⟩, ⟨2499⟩, claimed, ⟨0⟩, solcAddrMask, ⟨32⟩,
        ⟨192⟩, ⟨64⟩]
      (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k C := by
    simpa [getRewardOwedBaseTrackingCallPc, getRewardOwedBaseTrackingPostCallStack,
      getRewardOwedBaseTrackingPostCallTail] using rd
  have rd3876 := evm_run rd3724 with [
    swap2, dup3, iszero, push2 ⟨3876⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd3879 := evm_run rd3876 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨320⟩ getRewardOwedBaseTrackingPostCallAw (by native_decide)
      mem_cost
      (getRewardOwedBaseTrackingPostCallMem_mload64
        I slot0 multiplier haccrueSize hbaseSize)
      (by native_decide) (by evm_ov)]
  let rdsz : UInt256 := UInt256.ofNat baseOut.size
  have hrdsz_toNat : rdsz.toNat = baseOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hbaseSize
  have rd3883pre := evm_run rd3879 with [returndatasize, push1 ⟨0⟩, dup3]
  let mem2 : ByteArray :=
    baseOut.write 0
      (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut)
      320 rdsz.toNat
  let aw2 : UInt256 :=
    UInt256.ofNat (MachineState.M getRewardOwedBaseTrackingPostCallAw.toNat 320 rdsz.toNat)
  have rd3884 := RD.returndatacopy
    (Cₘ aw2 - Cₘ getRewardOwedBaseTrackingPostCallAw) mem2 aw2 rd3883pre
    (by native_decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hrdsz_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2, rdsz]
      change
        Cₘ (UInt256.ofNat
            (MachineState.M getRewardOwedBaseTrackingPostCallAw.toNat 320
              (UInt256.ofNat baseOut.size).toNat)) -
          Cₘ getRewardOwedBaseTrackingPostCallAw =
        Cₘ (UInt256.ofNat
            (MachineState.M getRewardOwedBaseTrackingPostCallAw.toNat 320
              (UInt256.ofNat baseOut.size).toNat)) -
          Cₘ getRewardOwedBaseTrackingPostCallAw
      rfl)
    (by rfl)
    (by rfl)
    (by simp)
  have rd3886 := evm_run rd3884 with [returndatasize, swap1]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M aw2.toNat 320 rdsz.toNat)) - Cₘ aw2)
    rd3886 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, rdsz]
      change
        Cₘ (UInt256.ofNat
            (MachineState.M aw2.toNat 320 (UInt256.ofNat baseOut.size).toNat)) -
          Cₘ aw2 =
        Cₘ (UInt256.ofNat
            (MachineState.M aw2.toNat 320 (UInt256.ofNat baseOut.size).toNat)) -
          Cₘ aw2
      rfl)
    (by simp)

set_option maxHeartbeats 2000000 in
theorem cometRewardsGetRewardOwedX_after_baseTracking_short_revert
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {accrueOut baseOut : ByteArray}
    {claimed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (getRewardOwedBaseTrackingCallPc + ⟨1⟩)
      (getRewardOwedBaseTrackingPostCallStack true claimed)
      (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k C)
    (hshort : baseOut.size < 32) (hbaseSize : baseOut.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let rdsz : UInt256 := UInt256.ofNat baseOut.size
  have hrdsz_toNat : rdsz.toNat = baseOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hbaseSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨1⟩ := by
    apply ugt_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hshort
  have rd3724 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3724⟩
      [⟨1⟩, ⟨192⟩, ⟨320⟩, ⟨2499⟩, claimed, ⟨0⟩, solcAddrMask, ⟨32⟩,
        ⟨192⟩, ⟨64⟩]
      (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k C := by
    simpa [getRewardOwedBaseTrackingCallPc, getRewardOwedBaseTrackingPostCallStack,
      getRewardOwedBaseTrackingPostCallTail] using rd
  have rd3855₀ := evm_run rd3724 with [
    swap2, dup3, iszero, push2 ⟨3876⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap3, push2 ⟨3844⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push2 ⟨3869⟩, swap2, swap3, pop, push1 ⟨32⟩,
    returndatasize, dup2, gt]
  have rd3855 := rd3855₀
  rw [show UInt256.ofNat baseOut.size = rdsz from rfl, hgt] at rd3855
  let rounded : UInt256 :=
    UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat baseOut.size + ⟨31⟩)
  let ptr : UInt256 := (⟨320⟩ : UInt256) + rounded
  have hroundedLe : rounded.toNat ≤ baseOut.size + 31 := by
    unfold rounded
    rw [uland_toNat]
    refine le_trans Nat.and_le_right ?_
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hbaseSize,
      show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    exact Nat.mod_le _ _
  have hptr_toNat : ptr.toNat = 320 + rounded.toNat := by
    unfold ptr
    rw [uadd_toNat, show (⟨320⟩ : UInt256).toNat = 320 from by decide]
    exact Nat.mod_eq_of_lt (by
      have hroundSmall : rounded.toNat < 64 := by omega
      have hsz : UInt256.size = 2 ^ 256 := by decide
      omega)
  have hltPtr : UInt256.lt ptr (⟨320⟩ : UInt256) = ⟨0⟩ := by
    apply ult_zero
    rw [hptr_toNat, show (⟨320⟩ : UInt256).toNat = 320 from by decide]
    omega
  have hmax64 :
      (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩).toNat =
        18446744073709551615 := by
    native_decide
  have hgtPtr :
      UInt256.gt ptr (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    rw [hptr_toNat, hmax64]
    omega
  have hallocOk :
      UInt256.lor (UInt256.lt ptr (⟨320⟩ : UInt256))
        (UInt256.gt ptr (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)) = ⟨0⟩ := by
    rw [hltPtr, hgtPtr]
    native_decide
  have rd3071 := evm_run rd3855 with [
    push2 ⟨734⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, returndatasize, push2 ⟨709⟩, jump (by jump_dest),
    jumpdest, push2 ⟨719⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩,
    jumpiNT (by simpa [ptr, rounded] using hallocOk), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0
      (getRewardOwedBaseTrackingPostShortDecodeMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw
      (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold getRewardOwedBaseTrackingPostShortDecodeMem Reasoning.Theory.writeWord
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3106 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, swap1, push2 ⟨3106⟩,
    jump (by jump_dest)]
  have hlenCheck :
      UInt256.slt (UInt256.sub ((⟨320⟩ : UInt256) + rdsz) ⟨320⟩) ⟨32⟩ =
        ⟨1⟩ := by
    simpa [rdsz] using
      solcReturnStaticLenCheckShort (base := 320) (words := 1) (by simpa using hshort)
        (by norm_num [UInt256.size])
        (by
          have hsz : UInt256.size = 2 ^ 256 := by decide
          omega)
        (by norm_num)
  have rd3114₀ := evm_run rd3106 with [
    jumpdest, swap1, dup2, push1 ⟨32⟩, swap2, sub, slt]
  have rd3114 := rd3114₀
  rw [hlenCheck] at rd3114
  have rd1004 := evm_run rd3114 with [
    push2 ⟨1004⟩, jumpiT (by native_decide) (by jump_dest)]
  exact evm_run rd1004 with [
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem cometRewardsGetRewardOwedX_after_baseTracking_decode_ok
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {accrueOut baseOut : ByteArray}
    {claimed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (getRewardOwedBaseTrackingCallPc + ⟨1⟩)
      (getRewardOwedBaseTrackingPostCallStack true claimed)
      (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k C)
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hbase64 : (getRewardOwedBaseTrackingReturnWord baseOut).toNat < EVM.twoPow 64) :
    ∃ k' C', RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3740⟩
      [⟨192⟩, getRewardOwedBaseTrackingReturnWord baseOut, ⟨2499⟩, claimed,
        ⟨0⟩, solcAddrMask, ⟨32⟩, ⟨192⟩, ⟨64⟩]
      (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k' C' := by
  let baseWord : UInt256 := getRewardOwedBaseTrackingReturnWord baseOut
  have hbase64' : baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  let rdsz : UInt256 := UInt256.ofNat baseOut.size
  have hrdsz_toNat : rdsz.toNat = baseOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hbaseSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hout32
  have rd3724 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3724⟩
      [⟨1⟩, ⟨192⟩, ⟨320⟩, ⟨2499⟩, claimed, ⟨0⟩, solcAddrMask, ⟨32⟩,
        ⟨192⟩, ⟨64⟩]
      (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k C := by
    simpa [getRewardOwedBaseTrackingCallPc, getRewardOwedBaseTrackingPostCallStack,
      getRewardOwedBaseTrackingPostCallTail] using rd
  have rd3855₀ := evm_run rd3724 with [
    swap2, dup3, iszero, push2 ⟨3876⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap3, push2 ⟨3844⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push2 ⟨3869⟩, swap2, swap3, pop, push1 ⟨32⟩,
    returndatasize, dup2, gt]
  have rd3855 := rd3855₀
  rw [show UInt256.ofNat baseOut.size = rdsz from rfl, hgt] at rd3855
  have rd3071 := evm_run rd3855 with [
    push2 ⟨734⟩, jumpiNT (by native_decide),
    push2 ⟨719⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide),
    push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0
      (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw
      (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold getRewardOwedBaseTrackingPostDecodeMem Reasoning.Theory.writeWord
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3106 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, swap1, push2 ⟨3106⟩,
    jump (by jump_dest), jumpdest, swap1, dup2, push1 ⟨32⟩, swap2, sub,
    slt, push2 ⟨1004⟩, jumpiNT (by native_decide)]
  have rd3129 := evm_run rd3106 with [
    raw mload 0 baseWord getRewardOwedBaseTrackingPostCallAw (by native_decide)
      mem_cost
      (by
        simpa [baseWord] using
          getRewardOwedBaseTrackingPostDecodeMem_mload320_of_size_ge
            I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup2, and, dup2, sub]
  have hclean : UInt256.land baseWord uint64Mask = baseWord :=
    uint64Mask_clean hbase64'
  have hcleanExpanded :
      UInt256.land baseWord
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = baseWord := by
    simpa [uint64Mask] using hclean
  have hsub :
      UInt256.sub baseWord
        (UInt256.land baseWord
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) = ⟨0⟩ := by
    rw [hcleanExpanded]
    exact u256_sub_self baseWord
  have rd3129zero := rd3129
  rw [hsub] at rd3129zero
  have rd3869 := evm_run rd3129zero with [
    push2 ⟨1004⟩, jumpiNT (by native_decide), swap1, jump (by jump_dest)]
  have rd3739 := evm_run rd3869 with [
    jumpdest, swap1, codesize, push2 ⟨3738⟩, jump (by jump_dest),
    jumpdest, pop]
  exact ⟨_, _, by
    simpa [baseWord, getRewardOwedBaseTrackingReturnWord] using rd3739⟩

set_option maxHeartbeats 2000000 in
theorem cometRewardsGetRewardOwedX_getRewardAccrued_upscale_success
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {accrueOut baseOut : ByteArray}
    {claimed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3740⟩
      [⟨192⟩, getRewardOwedBaseTrackingReturnWord baseOut, ⟨2499⟩, claimed,
        ⟨0⟩, solcAddrMask, ⟨32⟩, ⟨192⟩, ⟨64⟩]
      (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k C)
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hbase64 : (getRewardOwedBaseTrackingReturnWord baseOut).toNat < EVM.twoPow 64)
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 slot0 ≠ ⟨0⟩)
    (hscaled :
      getRewardAccruedScaledNat multiplier
        (getRewardAccruedUpscaledNat slot0 (getRewardOwedBaseTrackingReturnWord baseOut)) <
          UInt256.size) :
    ∃ k' C', RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2499⟩
      [ UInt256.ofNat
          (getRewardAccruedReturnNat multiplier
            (getRewardAccruedUpscaledNat slot0
              (getRewardOwedBaseTrackingReturnWord baseOut))),
        claimed, ⟨0⟩, solcAddrMask, ⟨32⟩, ⟨192⟩, ⟨64⟩]
      (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k' C' := by
  let baseWord : UInt256 := getRewardOwedBaseTrackingReturnWord baseOut
  let upNat : ℕ := getRewardAccruedUpscaledNat slot0 baseWord
  let scaledNat : ℕ := getRewardAccruedScaledNat multiplier upNat
  have hbase64' : baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  have hup : upNat < UInt256.size := by
    simpa [upNat, baseWord] using
      getRewardAccruedUpscaledNat_lt_size_of_base64
        (slot0 := slot0) (accrued := baseWord) hbase64'
  have hrescale64 : (rewardConfigRescaleFromSlot0 slot0).toNat < EVM.twoPow 64 := by
    simpa [rewardConfigRescaleFromSlot0, EVM.twoPow] using
      rewardConfigRescaleWord_lt slot0
  have hbaseClean :
      UInt256.land baseWord
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = baseWord := by
    simpa [uint64Mask] using uint64Mask_clean hbase64'
  have hbaseCleanLeft :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)
        baseWord = baseWord := by
    rw [u256_land_comm]
    exact hbaseClean
  have hrescaleClean :
      UInt256.land (rewardConfigRescaleFromSlot0 slot0)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) =
        rewardConfigRescaleFromSlot0 slot0 := by
    simpa [uint64Mask] using uint64Mask_clean hrescale64
  have hshouldWord :
      rewardConfigShouldUpscaleFromSlot0 slot0 = ⟨1⟩ :=
    rewardConfigShouldUpscaleFromSlot0_eq_one_of_raw_ne_zero hshould
  have hshouldIsZero :
      UInt256.isZero (rewardConfigShouldUpscaleFromSlot0 slot0) = ⟨0⟩ := by
    rw [hshouldWord]
    native_decide
  have hfirstMulLt :
      baseWord.toNat * (rewardConfigRescaleFromSlot0 slot0).toNat < UInt256.size := by
    simpa [upNat, baseWord, getRewardAccruedUpscaledNat] using hup
  have hfirstFlag :
      UInt256.land
          (UInt256.gt (rewardConfigRescaleFromSlot0 slot0)
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) baseWord))
          (UInt256.isZero (UInt256.isZero baseWord)) = ⟨0⟩ :=
    checkedMulOverflowFlag_zero baseWord (rewardConfigRescaleFromSlot0 slot0) hfirstMulLt
  have hfirstFlagLeft :
      UInt256.land (UInt256.isZero (UInt256.isZero baseWord))
          (UInt256.gt (rewardConfigRescaleFromSlot0 slot0)
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) baseWord)) = ⟨0⟩ := by
    rw [u256_land_comm]
    exact hfirstFlag
  have hfirstMulWord :
      UInt256.mul baseWord (rewardConfigRescaleFromSlot0 slot0) = UInt256.ofNat upNat := by
    simpa [upNat, baseWord, getRewardAccruedUpscaledNat] using
      u256_mul_eq_ofNat_of_lt baseWord (rewardConfigRescaleFromSlot0 slot0) hfirstMulLt
  have hupWordToNat : (UInt256.ofNat upNat).toNat = upNat :=
    UInt256.toNat_ofNat_of_lt hup
  have hsecondMulLt :
      (UInt256.ofNat upNat).toNat * multiplier.toNat < UInt256.size := by
    simpa [hupWordToNat, upNat, baseWord, scaledNat] using hscaled
  have hsecondFlag :
      UInt256.land
          (UInt256.gt multiplier
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat upNat)))
          (UInt256.isZero (UInt256.isZero (UInt256.ofNat upNat))) = ⟨0⟩ :=
    checkedMulOverflowFlag_zero (UInt256.ofNat upNat) multiplier hsecondMulLt
  have hsecondFlagLeft :
      UInt256.land (UInt256.isZero (UInt256.isZero (UInt256.ofNat upNat)))
          (UInt256.gt multiplier
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat upNat))) =
        ⟨0⟩ := by
    rw [u256_land_comm]
    exact hsecondFlag
  have hsecondMulWord :
      UInt256.mul (UInt256.ofNat upNat) multiplier = UInt256.ofNat scaledNat := by
    calc
      UInt256.mul (UInt256.ofNat upNat) multiplier =
          UInt256.ofNat ((UInt256.ofNat upNat).toNat * multiplier.toNat) :=
        u256_mul_eq_ofNat_of_lt (UInt256.ofNat upNat) multiplier hsecondMulLt
      _ = UInt256.ofNat scaledNat := by
        simp [scaledNat, getRewardAccruedScaledNat, hupWordToNat]
  have hdivWord :
      UInt256.div (UInt256.ofNat scaledNat) (⟨1000000000000000000⟩ : UInt256) =
        UInt256.ofNat (getRewardAccruedReturnNat multiplier upNat) := by
    simpa [scaledNat, getRewardAccruedReturnNat] using
      u256_div_factorScale_ofNat (n := scaledNat)
        (by simpa [scaledNat, upNat, baseWord] using hscaled)
  have rd3758 := evm_run rd with [
    push1 ⟨64⟩, dup2, add,
    raw mload 0 (rewardConfigShouldUpscaleFromSlot0 slot0)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload256
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, swap3, dup4, and,
    swap3, swap1, iszero]
  have rd3758' := rd3758
  rw [hbaseCleanLeft, hshouldIsZero] at rd3758'
  have rd3769pre := evm_run rd3758' with [
    push2 ⟨3808⟩, jumpiNT (by native_decide),
    swap1, push1 ⟨96⟩, push2 ⟨3794⟩]
  have rd3769 := rd3769pre.pushConst (⟨1000000000000000000⟩ : UInt256)
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd3671 := evm_run rd3769 with [
    swap5, push2 ⟨3804⟩, swap5, push1 ⟨32⟩, dup6, add,
    raw mload 0 (rewardConfigRescaleFromSlot0 slot0)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload224
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    and, swap1, push2 ⟨3660⟩, jump (by jump_dest),
    jumpdest, dup1, push1 ⟨0⟩, not, div, dup3, gt, dup2, iszero, iszero, and]
  have rd3671' := rd3671
  rw [hrescaleClean, hfirstFlagLeft] at rd3671'
  have rd3794 := evm_run rd3671' with [
    push2 ⟨3252⟩, jumpiNT (by native_decide), mul, swap1, jump (by jump_dest),
    jumpdest]
  have rd3794' := rd3794
  rw [hfirstMulWord] at rd3794'
  have rd3671₂ := evm_run rd3794' with [
    swap2, jumpdest, add,
    raw mload 0 multiplier getRewardOwedBaseTrackingPostCallAw
      (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload288
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    swap1, push2 ⟨3660⟩, jump (by jump_dest),
    jumpdest, dup1, push1 ⟨0⟩, not, div, dup3, gt, dup2, iszero, iszero, and]
  have rd3671₂' := rd3671₂
  rw [hsecondFlagLeft] at rd3671₂'
  have rd3804 := evm_run rd3671₂' with [
    push2 ⟨3252⟩, jumpiNT (by native_decide), mul, swap1, jump (by jump_dest),
    jumpdest]
  have rd3804' := rd3804
  rw [hsecondMulWord] at rd3804'
  have rd2499 := evm_run rd3804' with [
    div, swap1, jump (by jump_dest)]
  rw [hdivWord] at rd2499
  exact ⟨_, _, by
    simpa [baseWord, upNat, scaledNat, getRewardOwedBaseTrackingReturnWord] using rd2499⟩

set_option maxHeartbeats 2000000 in
theorem cometRewardsGetRewardOwedX_getRewardAccrued_downscale_success
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {accrueOut baseOut : ByteArray}
    {claimed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3740⟩
      [⟨192⟩, getRewardOwedBaseTrackingReturnWord baseOut, ⟨2499⟩, claimed,
        ⟨0⟩, solcAddrMask, ⟨32⟩, ⟨192⟩, ⟨64⟩]
      (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k C)
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hbase64 : (getRewardOwedBaseTrackingReturnWord baseOut).toNat < EVM.twoPow 64)
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 slot0 = ⟨0⟩)
    (hrescaleNZ : rewardConfigRescaleFromSlot0 slot0 ≠ ⟨0⟩)
    (hscaled :
      getRewardAccruedScaledNat multiplier
        (getRewardAccruedDownscaledNat slot0 (getRewardOwedBaseTrackingReturnWord baseOut)) <
          UInt256.size) :
    ∃ k' C', RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2499⟩
      [ UInt256.ofNat
          (getRewardAccruedReturnNat multiplier
            (getRewardAccruedDownscaledNat slot0
              (getRewardOwedBaseTrackingReturnWord baseOut))),
        claimed, ⟨0⟩, solcAddrMask, ⟨32⟩, ⟨192⟩, ⟨64⟩]
      (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k' C' := by
  let baseWord : UInt256 := getRewardOwedBaseTrackingReturnWord baseOut
  let downNat : ℕ := getRewardAccruedDownscaledNat slot0 baseWord
  let scaledNat : ℕ := getRewardAccruedScaledNat multiplier downNat
  have hbase64' : baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  have hbaseClean :
      UInt256.land baseWord
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = baseWord := by
    simpa [uint64Mask] using uint64Mask_clean hbase64'
  have hbaseCleanLeft :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)
        baseWord = baseWord := by
    rw [u256_land_comm]
    exact hbaseClean
  have hrescale64 : (rewardConfigRescaleFromSlot0 slot0).toNat < EVM.twoPow 64 := by
    simpa [rewardConfigRescaleFromSlot0, EVM.twoPow] using
      rewardConfigRescaleWord_lt slot0
  have hrescaleClean :
      UInt256.land (rewardConfigRescaleFromSlot0 slot0)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) =
        rewardConfigRescaleFromSlot0 slot0 := by
    simpa [uint64Mask] using uint64Mask_clean hrescale64
  have hshouldWord :
      rewardConfigShouldUpscaleFromSlot0 slot0 = ⟨0⟩ :=
    rewardConfigShouldUpscaleFromSlot0_eq_zero_of_raw_zero hshould
  have hshouldIsZero :
      UInt256.isZero (rewardConfigShouldUpscaleFromSlot0 slot0) = ⟨1⟩ := by
    rw [hshouldWord]
    native_decide
  have hrescaleIsZero : UInt256.isZero (rewardConfigRescaleFromSlot0 slot0) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hrescaleNZ
  have hdownWord :
      UInt256.div baseWord (rewardConfigRescaleFromSlot0 slot0) = UInt256.ofNat downNat := by
    simpa [downNat, baseWord, getRewardAccruedDownscaledNat] using
      u256_div_eq_ofNat baseWord (rewardConfigRescaleFromSlot0 slot0)
  have hdownLt : downNat < UInt256.size := by
    have hle : downNat ≤ baseWord.toNat := by
      simpa [downNat, getRewardAccruedDownscaledNat] using
        Nat.div_le_self baseWord.toNat (rewardConfigRescaleFromSlot0 slot0).toNat
    exact lt_of_le_of_lt hle baseWord.val.isLt
  have hdownWordToNat : (UInt256.ofNat downNat).toNat = downNat :=
    UInt256.toNat_ofNat_of_lt hdownLt
  have hsecondMulLt :
      (UInt256.ofNat downNat).toNat * multiplier.toNat < UInt256.size := by
    simpa [hdownWordToNat, downNat, baseWord, scaledNat] using hscaled
  have hsecondFlag :
      UInt256.land
          (UInt256.gt multiplier
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat downNat)))
          (UInt256.isZero (UInt256.isZero (UInt256.ofNat downNat))) = ⟨0⟩ :=
    checkedMulOverflowFlag_zero (UInt256.ofNat downNat) multiplier hsecondMulLt
  have hsecondFlagLeft :
      UInt256.land (UInt256.isZero (UInt256.isZero (UInt256.ofNat downNat)))
          (UInt256.gt multiplier
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat downNat))) =
        ⟨0⟩ := by
    rw [u256_land_comm]
    exact hsecondFlag
  have hsecondMulWord :
      UInt256.mul (UInt256.ofNat downNat) multiplier = UInt256.ofNat scaledNat := by
    calc
      UInt256.mul (UInt256.ofNat downNat) multiplier =
          UInt256.ofNat ((UInt256.ofNat downNat).toNat * multiplier.toNat) :=
        u256_mul_eq_ofNat_of_lt (UInt256.ofNat downNat) multiplier hsecondMulLt
      _ = UInt256.ofNat scaledNat := by
        simp [scaledNat, getRewardAccruedScaledNat, hdownWordToNat]
  have hdivWord :
      UInt256.div (UInt256.ofNat scaledNat) (⟨1000000000000000000⟩ : UInt256) =
        UInt256.ofNat (getRewardAccruedReturnNat multiplier downNat) := by
    simpa [scaledNat, getRewardAccruedReturnNat] using
      u256_div_factorScale_ofNat (n := scaledNat)
        (by simpa [scaledNat, downNat, baseWord] using hscaled)
  have rd3758 := evm_run rd with [
    push1 ⟨64⟩, dup2, add,
    raw mload 0 (rewardConfigShouldUpscaleFromSlot0 slot0)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload256
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, swap3, dup4, and,
    swap3, swap1, iszero]
  have rd3758' := rd3758
  rw [hbaseCleanLeft, hshouldIsZero] at rd3758'
  have rd3817 := evm_run rd3758' with [
    push2 ⟨3808⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push1 ⟨32⟩, dup3, add,
    raw mload 0 (rewardConfigRescaleFromSlot0 slot0)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload224
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    and, swap1, dup2, iszero]
  have rd3817' := rd3817
  rw [hrescaleClean, hrescaleIsZero] at rd3817'
  have rd3827pre := evm_run rd3817' with [
    push2 ⟨3161⟩, jumpiNT (by native_decide),
    push1 ⟨96⟩, push2 ⟨3804⟩, swap3]
  have rd3828 := rd3827pre.pushConst (⟨1000000000000000000⟩ : UInt256)
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd3796 := evm_run rd3828 with [
    swap5, div, swap2, push2 ⟨3796⟩, jump (by jump_dest), jumpdest]
  have rd3796' := rd3796
  rw [hdownWord] at rd3796'
  have rd3671₂ := evm_run rd3796' with [
    add,
    raw mload 0 multiplier getRewardOwedBaseTrackingPostCallAw
      (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload288
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    swap1, push2 ⟨3660⟩, jump (by jump_dest),
    jumpdest, dup1, push1 ⟨0⟩, not, div, dup3, gt, dup2, iszero, iszero, and]
  have rd3671₂' := rd3671₂
  rw [hsecondFlagLeft] at rd3671₂'
  have rd3804 := evm_run rd3671₂' with [
    push2 ⟨3252⟩, jumpiNT (by native_decide), mul, swap1, jump (by jump_dest),
    jumpdest]
  have rd3804' := rd3804
  rw [hsecondMulWord] at rd3804'
  have rd2499 := evm_run rd3804' with [
    div, swap1, jump (by jump_dest)]
  rw [hdivWord] at rd2499
  exact ⟨_, _, by
    simpa [baseWord, downNat, scaledNat, getRewardOwedBaseTrackingReturnWord] using rd2499⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsGetRewardOwedX_panic12_from3161
    {cA gh bl σ σ₀ A I} {g : Sat256} {mem rdata : ByteArray}
    {stack : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3161⟩
      stack mem getRewardOwedBaseTrackingPostCallAw rdata acc k C)
    (hov : stack.length + 2 ≤ 1024) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        setRewardConfigPanicSelector := by
    rfl
  have rd3172₀ := evm_run rd with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push1 ⟨0⟩]
  have rd3172 := rd3172₀
  rw [hsel] at rd3172
  have rd3173 := evm_run rd3172 with [
    raw mstore 0 (setRewardConfigPanicMem0 mem)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov)]
  have rd3178 := evm_run rd3173 with [
    push1 ⟨18⟩, push1 ⟨4⟩,
    raw mstore 0 (setRewardConfigPanicMem ⟨18⟩ mem)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨36⟩, push1 ⟨0⟩]
  exact evm_run rd3178 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsGetRewardOwedX_panic11_from3252
    {cA gh bl σ σ₀ A I} {g : Sat256} {mem rdata : ByteArray}
    {stack : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3252⟩
      stack mem getRewardOwedBaseTrackingPostCallAw rdata acc k C)
    (hov : stack.length + 2 ≤ 1024) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        setRewardConfigPanicSelector := by
    rfl
  have rd3263₀ := evm_run rd with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push1 ⟨0⟩]
  have rd3263 := rd3263₀
  rw [hsel] at rd3263
  have rd3264 := evm_run rd3263 with [
    raw mstore 0 (setRewardConfigPanicMem0 mem)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov)]
  have rd3269 := evm_run rd3264 with [
    push1 ⟨17⟩, push1 ⟨4⟩,
    raw mstore 0 (setRewardConfigPanicMem ⟨17⟩ mem)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨36⟩, push1 ⟨0⟩]
  exact evm_run rd3269 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem cometRewardsGetRewardOwedX_getRewardAccrued_downscale_zero_revert
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {accrueOut baseOut : ByteArray}
    {claimed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3740⟩
      [⟨192⟩, getRewardOwedBaseTrackingReturnWord baseOut, ⟨2499⟩, claimed,
        ⟨0⟩, solcAddrMask, ⟨32⟩, ⟨192⟩, ⟨64⟩]
      (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k C)
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hbase64 : (getRewardOwedBaseTrackingReturnWord baseOut).toNat < EVM.twoPow 64)
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 slot0 = ⟨0⟩)
    (hrescaleZero : rewardConfigRescaleFromSlot0 slot0 = ⟨0⟩) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let baseWord : UInt256 := getRewardOwedBaseTrackingReturnWord baseOut
  have hbase64' : baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  have hbaseClean :
      UInt256.land baseWord
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = baseWord := by
    simpa [uint64Mask] using uint64Mask_clean hbase64'
  have hbaseCleanLeft :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)
        baseWord = baseWord := by
    rw [u256_land_comm]
    exact hbaseClean
  have hrescaleClean :
      UInt256.land (rewardConfigRescaleFromSlot0 slot0)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) =
        rewardConfigRescaleFromSlot0 slot0 := by
    rw [hrescaleZero]
    native_decide
  have hshouldWord :
      rewardConfigShouldUpscaleFromSlot0 slot0 = ⟨0⟩ :=
    rewardConfigShouldUpscaleFromSlot0_eq_zero_of_raw_zero hshould
  have hshouldIsZero :
      UInt256.isZero (rewardConfigShouldUpscaleFromSlot0 slot0) = ⟨1⟩ := by
    rw [hshouldWord]
    native_decide
  have hrescaleIsZero : UInt256.isZero (rewardConfigRescaleFromSlot0 slot0) = ⟨1⟩ := by
    rw [hrescaleZero]
    native_decide
  have rd3758 := evm_run rd with [
    push1 ⟨64⟩, dup2, add,
    raw mload 0 (rewardConfigShouldUpscaleFromSlot0 slot0)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload256
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, swap3, dup4, and,
    swap3, swap1, iszero]
  have rd3758' := rd3758
  rw [hbaseCleanLeft, hshouldIsZero] at rd3758'
  have rd3817 := evm_run rd3758' with [
    push2 ⟨3808⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push1 ⟨32⟩, dup3, add,
    raw mload 0 (rewardConfigRescaleFromSlot0 slot0)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload224
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    and, swap1, dup2, iszero]
  have rd3817' := rd3817
  rw [hrescaleClean, hrescaleIsZero] at rd3817'
  have rd3161 := evm_run rd3817' with [
    push2 ⟨3161⟩, jumpiT (by native_decide) (by jump_dest)]
  exact cometRewardsGetRewardOwedX_panic12_from3161 rd3161 (by simp)

set_option maxHeartbeats 2000000 in
theorem cometRewardsGetRewardOwedX_getRewardAccrued_upscale_overflow_revert
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {accrueOut baseOut : ByteArray}
    {claimed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3740⟩
      [⟨192⟩, getRewardOwedBaseTrackingReturnWord baseOut, ⟨2499⟩, claimed,
        ⟨0⟩, solcAddrMask, ⟨32⟩, ⟨192⟩, ⟨64⟩]
      (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k C)
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hbase64 : (getRewardOwedBaseTrackingReturnWord baseOut).toNat < EVM.twoPow 64)
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 slot0 ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤ getRewardAccruedScaledNat multiplier
        (getRewardAccruedUpscaledNat slot0 (getRewardOwedBaseTrackingReturnWord baseOut))) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let baseWord : UInt256 := getRewardOwedBaseTrackingReturnWord baseOut
  let upNat : ℕ := getRewardAccruedUpscaledNat slot0 baseWord
  have hbase64' : baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  have hup : upNat < UInt256.size := by
    simpa [upNat, baseWord] using
      getRewardAccruedUpscaledNat_lt_size_of_base64
        (slot0 := slot0) (accrued := baseWord) hbase64'
  have hrescale64 : (rewardConfigRescaleFromSlot0 slot0).toNat < EVM.twoPow 64 := by
    simpa [rewardConfigRescaleFromSlot0, EVM.twoPow] using
      rewardConfigRescaleWord_lt slot0
  have hbaseClean :
      UInt256.land baseWord
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = baseWord := by
    simpa [uint64Mask] using uint64Mask_clean hbase64'
  have hbaseCleanLeft :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)
        baseWord = baseWord := by
    rw [u256_land_comm]
    exact hbaseClean
  have hrescaleClean :
      UInt256.land (rewardConfigRescaleFromSlot0 slot0)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) =
        rewardConfigRescaleFromSlot0 slot0 := by
    simpa [uint64Mask] using uint64Mask_clean hrescale64
  have hshouldWord :
      rewardConfigShouldUpscaleFromSlot0 slot0 = ⟨1⟩ :=
    rewardConfigShouldUpscaleFromSlot0_eq_one_of_raw_ne_zero hshould
  have hshouldIsZero :
      UInt256.isZero (rewardConfigShouldUpscaleFromSlot0 slot0) = ⟨0⟩ := by
    rw [hshouldWord]
    native_decide
  have hfirstMulLt :
      baseWord.toNat * (rewardConfigRescaleFromSlot0 slot0).toNat < UInt256.size := by
    simpa [upNat, baseWord, getRewardAccruedUpscaledNat] using hup
  have hfirstFlag :
      UInt256.land (UInt256.isZero (UInt256.isZero baseWord))
          (UInt256.gt (rewardConfigRescaleFromSlot0 slot0)
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) baseWord)) = ⟨0⟩ := by
    rw [u256_land_comm]
    exact checkedMulOverflowFlag_zero baseWord (rewardConfigRescaleFromSlot0 slot0)
      hfirstMulLt
  have hfirstMulWord :
      UInt256.mul baseWord (rewardConfigRescaleFromSlot0 slot0) = UInt256.ofNat upNat := by
    simpa [upNat, baseWord, getRewardAccruedUpscaledNat] using
      u256_mul_eq_ofNat_of_lt baseWord (rewardConfigRescaleFromSlot0 slot0) hfirstMulLt
  have hupWordToNat : (UInt256.ofNat upNat).toNat = upNat :=
    UInt256.toNat_ofNat_of_lt hup
  have hsecondOver :
      UInt256.size ≤ (UInt256.ofNat upNat).toNat * multiplier.toNat := by
    simpa [hupWordToNat, upNat, baseWord, getRewardAccruedScaledNat] using hover
  have hsecondFlag :
      UInt256.land (UInt256.isZero (UInt256.isZero (UInt256.ofNat upNat)))
          (UInt256.gt multiplier
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat upNat))) =
        ⟨1⟩ :=
    checkedMulOverflowFlag_one (UInt256.ofNat upNat) multiplier hsecondOver
  have rd3758 := evm_run rd with [
    push1 ⟨64⟩, dup2, add,
    raw mload 0 (rewardConfigShouldUpscaleFromSlot0 slot0)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload256
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, swap3, dup4, and,
    swap3, swap1, iszero]
  have rd3758' := rd3758
  rw [hbaseCleanLeft, hshouldIsZero] at rd3758'
  have rd3769pre := evm_run rd3758' with [
    push2 ⟨3808⟩, jumpiNT (by native_decide),
    swap1, push1 ⟨96⟩, push2 ⟨3794⟩]
  have rd3769 := rd3769pre.pushConst (⟨1000000000000000000⟩ : UInt256)
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd3671 := evm_run rd3769 with [
    swap5, push2 ⟨3804⟩, swap5, push1 ⟨32⟩, dup6, add,
    raw mload 0 (rewardConfigRescaleFromSlot0 slot0)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload224
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    and, swap1, push2 ⟨3660⟩, jump (by jump_dest),
    jumpdest, dup1, push1 ⟨0⟩, not, div, dup3, gt, dup2, iszero, iszero, and]
  have rd3671' := rd3671
  rw [hrescaleClean, hfirstFlag] at rd3671'
  have rd3794 := evm_run rd3671' with [
    push2 ⟨3252⟩, jumpiNT (by native_decide), mul, swap1, jump (by jump_dest),
    jumpdest]
  have rd3794' := rd3794
  rw [hfirstMulWord] at rd3794'
  have rd3671₂ := evm_run rd3794' with [
    swap2, jumpdest, add,
    raw mload 0 multiplier getRewardOwedBaseTrackingPostCallAw
      (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload288
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    swap1, push2 ⟨3660⟩, jump (by jump_dest),
    jumpdest, dup1, push1 ⟨0⟩, not, div, dup3, gt, dup2, iszero, iszero, and]
  have rd3671₂' := rd3671₂
  rw [hsecondFlag] at rd3671₂'
  have rd3252 := evm_run rd3671₂' with [
    push2 ⟨3252⟩, jumpiT (by native_decide) (by jump_dest)]
  exact cometRewardsGetRewardOwedX_panic11_from3252 rd3252 (by simp)

set_option maxHeartbeats 2000000 in
theorem cometRewardsGetRewardOwedX_getRewardAccrued_downscale_overflow_revert
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {accrueOut baseOut : ByteArray}
    {claimed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3740⟩
      [⟨192⟩, getRewardOwedBaseTrackingReturnWord baseOut, ⟨2499⟩, claimed,
        ⟨0⟩, solcAddrMask, ⟨32⟩, ⟨192⟩, ⟨64⟩]
      (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k C)
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hbase64 : (getRewardOwedBaseTrackingReturnWord baseOut).toNat < EVM.twoPow 64)
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 slot0 = ⟨0⟩)
    (hrescaleNZ : rewardConfigRescaleFromSlot0 slot0 ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤ getRewardAccruedScaledNat multiplier
        (getRewardAccruedDownscaledNat slot0 (getRewardOwedBaseTrackingReturnWord baseOut))) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let baseWord : UInt256 := getRewardOwedBaseTrackingReturnWord baseOut
  let downNat : ℕ := getRewardAccruedDownscaledNat slot0 baseWord
  have hbase64' : baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  have hbaseClean :
      UInt256.land baseWord
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = baseWord := by
    simpa [uint64Mask] using uint64Mask_clean hbase64'
  have hbaseCleanLeft :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)
        baseWord = baseWord := by
    rw [u256_land_comm]
    exact hbaseClean
  have hrescale64 : (rewardConfigRescaleFromSlot0 slot0).toNat < EVM.twoPow 64 := by
    simpa [rewardConfigRescaleFromSlot0, EVM.twoPow] using
      rewardConfigRescaleWord_lt slot0
  have hrescaleClean :
      UInt256.land (rewardConfigRescaleFromSlot0 slot0)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) =
        rewardConfigRescaleFromSlot0 slot0 := by
    simpa [uint64Mask] using uint64Mask_clean hrescale64
  have hshouldWord :
      rewardConfigShouldUpscaleFromSlot0 slot0 = ⟨0⟩ :=
    rewardConfigShouldUpscaleFromSlot0_eq_zero_of_raw_zero hshould
  have hshouldIsZero :
      UInt256.isZero (rewardConfigShouldUpscaleFromSlot0 slot0) = ⟨1⟩ := by
    rw [hshouldWord]
    native_decide
  have hrescaleIsZero : UInt256.isZero (rewardConfigRescaleFromSlot0 slot0) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hrescaleNZ
  have hdownWord :
      UInt256.div baseWord (rewardConfigRescaleFromSlot0 slot0) = UInt256.ofNat downNat := by
    simpa [downNat, baseWord, getRewardAccruedDownscaledNat] using
      u256_div_eq_ofNat baseWord (rewardConfigRescaleFromSlot0 slot0)
  have hdownLt : downNat < UInt256.size := by
    have hle : downNat ≤ baseWord.toNat := by
      simpa [downNat, getRewardAccruedDownscaledNat] using
        Nat.div_le_self baseWord.toNat (rewardConfigRescaleFromSlot0 slot0).toNat
    exact lt_of_le_of_lt hle baseWord.val.isLt
  have hdownWordToNat : (UInt256.ofNat downNat).toNat = downNat :=
    UInt256.toNat_ofNat_of_lt hdownLt
  have hsecondOver :
      UInt256.size ≤ (UInt256.ofNat downNat).toNat * multiplier.toNat := by
    simpa [hdownWordToNat, downNat, baseWord, getRewardAccruedScaledNat] using hover
  have hsecondFlag :
      UInt256.land (UInt256.isZero (UInt256.isZero (UInt256.ofNat downNat)))
          (UInt256.gt multiplier
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat downNat))) =
        ⟨1⟩ :=
    checkedMulOverflowFlag_one (UInt256.ofNat downNat) multiplier hsecondOver
  have rd3758 := evm_run rd with [
    push1 ⟨64⟩, dup2, add,
    raw mload 0 (rewardConfigShouldUpscaleFromSlot0 slot0)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload256
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, swap3, dup4, and,
    swap3, swap1, iszero]
  have rd3758' := rd3758
  rw [hbaseCleanLeft, hshouldIsZero] at rd3758'
  have rd3817 := evm_run rd3758' with [
    push2 ⟨3808⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push1 ⟨32⟩, dup3, add,
    raw mload 0 (rewardConfigRescaleFromSlot0 slot0)
      getRewardOwedBaseTrackingPostCallAw (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload224
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    and, swap1, dup2, iszero]
  have rd3817' := rd3817
  rw [hrescaleClean, hrescaleIsZero] at rd3817'
  have rd3827pre := evm_run rd3817' with [
    push2 ⟨3161⟩, jumpiNT (by native_decide),
    push1 ⟨96⟩, push2 ⟨3804⟩, swap3]
  have rd3828 := rd3827pre.pushConst (⟨1000000000000000000⟩ : UInt256)
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd3796 := evm_run rd3828 with [
    swap5, div, swap2, push2 ⟨3796⟩, jump (by jump_dest), jumpdest]
  have rd3796' := rd3796
  rw [hdownWord] at rd3796'
  have rd3671₂ := evm_run rd3796' with [
    add,
    raw mload 0 multiplier getRewardOwedBaseTrackingPostCallAw
      (by native_decide) mem_cost
      (getRewardOwedBaseTrackingPostDecodeMem_mload288
        I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    swap1, push2 ⟨3660⟩, jump (by jump_dest),
    jumpdest, dup1, push1 ⟨0⟩, not, div, dup3, gt, dup2, iszero, iszero, and]
  have rd3671₂' := rd3671₂
  rw [hsecondFlag] at rd3671₂'
  have rd3252 := evm_run rd3671₂' with [
    push2 ⟨3252⟩, jumpiT (by native_decide) (by jump_dest)]
  exact cometRewardsGetRewardOwedX_panic11_from3252 rd3252 (by simp)

set_option maxHeartbeats 2000000 in
theorem cometRewardsGetRewardOwedX_after_baseTracking_noncanon_revert
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {accrueOut baseOut : ByteArray}
    {claimed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (getRewardOwedBaseTrackingCallPc + ⟨1⟩)
      (getRewardOwedBaseTrackingPostCallStack true claimed)
      (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k C)
    (haccrueSize : accrueOut.size < UInt256.size)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hbase64 : ¬ (getRewardOwedBaseTrackingReturnWord baseOut).toNat < EVM.twoPow 64) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let baseWord : UInt256 := getRewardOwedBaseTrackingReturnWord baseOut
  have hbase64' : ¬ baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  let rdsz : UInt256 := UInt256.ofNat baseOut.size
  have hrdsz_toNat : rdsz.toNat = baseOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hbaseSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hout32
  have rd3724 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3724⟩
      [⟨1⟩, ⟨192⟩, ⟨320⟩, ⟨2499⟩, claimed, ⟨0⟩, solcAddrMask, ⟨32⟩,
        ⟨192⟩, ⟨64⟩]
      (getRewardOwedBaseTrackingPostCallMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw baseOut acc k C := by
    simpa [getRewardOwedBaseTrackingCallPc, getRewardOwedBaseTrackingPostCallStack,
      getRewardOwedBaseTrackingPostCallTail] using rd
  have rd3855₀ := evm_run rd3724 with [
    swap2, dup3, iszero, push2 ⟨3876⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap3, push2 ⟨3844⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push2 ⟨3869⟩, swap2, swap3, pop, push1 ⟨32⟩,
    returndatasize, dup2, gt]
  have rd3855 := rd3855₀
  rw [show UInt256.ofNat baseOut.size = rdsz from rfl, hgt] at rd3855
  have rd3071 := evm_run rd3855 with [
    push2 ⟨734⟩, jumpiNT (by native_decide),
    push2 ⟨719⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide),
    push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0
      (getRewardOwedBaseTrackingPostDecodeMem I slot0 multiplier accrueOut baseOut)
      getRewardOwedBaseTrackingPostCallAw
      (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold getRewardOwedBaseTrackingPostDecodeMem Reasoning.Theory.writeWord
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3106 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, swap1, push2 ⟨3106⟩,
    jump (by jump_dest), jumpdest, swap1, dup2, push1 ⟨32⟩, swap2, sub,
    slt, push2 ⟨1004⟩, jumpiNT (by native_decide)]
  have rd3129 := evm_run rd3106 with [
    raw mload 0 baseWord getRewardOwedBaseTrackingPostCallAw (by native_decide)
      mem_cost
      (by
        simpa [baseWord] using
          getRewardOwedBaseTrackingPostDecodeMem_mload320_of_size_ge
            I slot0 multiplier haccrueSize hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup2, and, dup2, sub]
  have hnotClean : UInt256.land baseWord uint64Mask ≠ baseWord :=
    uint64Mask_not_clean hbase64'
  have hneq :
      baseWord ≠
        UInt256.land baseWord
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) := by
    intro hEq
    exact hnotClean (by simpa [uint64Mask] using hEq.symm)
  have hsub :
      UInt256.sub baseWord
        (UInt256.land baseWord
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) ≠ ⟨0⟩ :=
    u256_sub_ne_zero_of_ne hneq
  have rd1004 := evm_run rd3129 with [
    push2 ⟨1004⟩, jumpiT hsub (by jump_dest)]
  exact evm_run rd1004 with [
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsGetRewardOwedX_callDepthLimit {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (getRewardOwedAccountWord I).toNat < EVM.addressModulus)
    (hnz : rewardConfigTokenFromSlot0 (getRewardOwedRewardConfigSlot0Word σ I) ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ
        (UInt256.land (getRewardOwedCometWord I) solcAddrMask) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨gasArg, k0, C0, rd2450⟩ :=
    cometRewardsGetRewardOwedX_call_accrueAccount (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hwv hsz68 hsize hhi hcanonComet hcanonAccount hnz hcodeSize hreach
  have rd2450Call :
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        getRewardOwedAccrueAccountCallPc
        (gasArg :: UInt256.land (getRewardOwedCometWord I) solcAddrMask :: ⟨0⟩ ::
          ⟨320⟩ :: getRewardOwedAccrueAccountCallSize :: ⟨320⟩ :: ⟨0⟩ ::
          getRewardOwedAccrueAccountPostCallTail I)
        (getRewardOwedAccrueAccountCalldataMem I (getRewardOwedRewardConfigSlot0Word σ I)
          (getRewardOwedMultiplierWord σ I))
        getRewardOwedAccrueAccountPostCallAw ByteArray.empty (cA, σ) k0 C0 := by
    simpa [getRewardOwedAccrueAccountPostCallTail] using rd2450
  have hdecCall :
      decode cometRewardsBytecode getRewardOwedAccrueAccountCallPc = some (.CALL, .none) := by
    unfold getRewardOwedAccrueAccountCallPc
    native_decide
  have hdepthInit :
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.depth = 1024 := by
    simpa [initState] using hdepth
  obtain ⟨k', C', rdPost₀⟩ :=
    RD.callDepthLimit (t := getRewardOwedAccrueAccountPostCallTail I)
      rd2450Call hdecCall hdepthInit (by simp [getRewardOwedAccrueAccountPostCallTail])
  have rdPost :
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (getRewardOwedAccrueAccountCallPc + ⟨1⟩)
        (getRewardOwedAccrueAccountPostCallStack false I)
        (getRewardOwedAccrueAccountPostCallMem I
          (getRewardOwedRewardConfigSlot0Word σ I) (getRewardOwedMultiplierWord σ I)
          ByteArray.empty)
        getRewardOwedAccrueAccountPostCallAw ByteArray.empty (cA, σ) k' C' := by
    simpa [getRewardOwedAccrueAccountPostCallStack, getRewardOwedAccrueAccountPostCallTail,
      getRewardOwedAccrueAccountPostCallMem, getRewardOwedAccrueAccountPostCallAw,
      getRewardOwedAccrueAccountCallSize] using rdPost₀
  exact cometRewardsGetRewardOwedX_after_accrueAccount_failure
    (slot0 := getRewardOwedRewardConfigSlot0Word σ I)
    (multiplier := getRewardOwedMultiplierWord σ I) rdPost (by simp [UInt256.size])

set_option maxHeartbeats 1000000 in
theorem cometRewardsGetRewardOwedX_tokenZero {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus)
    (hcanonAccount : (getRewardOwedAccountWord I).toNat < EVM.addressModulus)
    (htokenZero : rewardConfigTokenFromSlot0 (getRewardOwedRewardConfigSlot0Word σ I) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2307⟩ :=
    cometRewardsGetRewardOwedX_dec2307_account (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz68 hsize hhi hcanonComet hcanonAccount hreach
  have hslot := getRewardOwedRewardConfigSlotOf_eq_solc I hcanonComet
  let slot0 := getRewardOwedRewardConfigSlot0Word σ I
  let multiplier := getRewardOwedMultiplierWord σ I
  have rd2355 := evm_run rd2307 with [
    jumpdest, swap4, dup7,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap5, push2 ⟨2320⟩, dup7, push2 ⟨2976⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩, dup2, add, swap1, dup2, lt,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt, lor,
    push2 ⟨3003⟩, jumpiNT (by native_decide),
    push1 ⟨64⟩,
    raw mstore 0 getRewardOwedAlloc64Mem (UInt256.ofNat 3) (by decide) mem_cost
      (by unfold getRewardOwedAlloc64Mem Reasoning.Theory.writeWord; rfl)
      (by decide) (by evm_ov),
    jump (by jump_dest),
    jumpdest, dup3, dup7,
    raw mstore 6 (writeCascade getRewardOwedAlloc64Mem [(128, (⟨0⟩ : UInt256))])
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        unfold getRewardOwedAlloc64Mem Reasoning.Theory.writeCascade
          Reasoning.Theory.writeWord
        rfl) (by decide) (by evm_ov),
    dup3, push1 ⟨32⟩, dup1, swap8, add,
    raw mstore 3 getRewardOwedConfigZeroMem (UInt256.ofNat 6) (by decide) mem_cost
      (by
        unfold getRewardOwedConfigZeroMem getRewardOwedAlloc64Mem
        unfold Reasoning.Theory.writeCascade Reasoning.Theory.writeWord
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, dup1, push1 ⟨160⟩, shl, sub, swap5, dup6, dup4, and,
    swap5, dup6, dup6,
    raw mstore 0 (wordAt0Mem (getRewardOwedCometWord I) getRewardOwedConfigZeroMem)
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide, solcAddrMask_clean hcanonComet]
        unfold getRewardOwedConfigZeroMem getRewardOwedAlloc64Mem
        unfold Reasoning.Theory.writeCascade wordAt0Mem Reasoning.Theory.writeWord
        rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, dup9,
    raw mstore 0 (getRewardOwedRewardConfigHashMem I) (UInt256.ofNat 6) (by decide) mem_cost
      (by
        unfold getRewardOwedRewardConfigHashMem getRewardOwedConfigZeroMem
        unfold getRewardOwedAlloc64Mem twoWordHashMem wordAt32Mem wordAt0Mem
        unfold Reasoning.Theory.writeCascade Reasoning.Theory.writeWord
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, dup11, dup7,
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (getRewardOwedCometWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (getRewardOwedRewardConfigHashMem_keccakSlot I) (by decide) (by evm_ov)]
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2355⟩
    [solcMappingSlot ⟨1⟩ (getRewardOwedCometWord I), ⟨1⟩, ⟨224⟩, ⟨4⟩,
      getRewardOwedAccountWord I, getRewardOwedCometWord I, ⟨0⟩,
      UInt256.land (getRewardOwedCometWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩),
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩,
      ⟨32⟩, ⟨255⟩, ⟨64⟩]
    (getRewardOwedRewardConfigHashMem I) (UInt256.ofNat 6) ByteArray.empty
    (cA, σ) _ _ at rd2355
  rw [← hslot] at rd2355
  have rd2356 := Reasoning.Reach.RD.dup12 rd2355 (by native_decide) (by decide)
  have rd2358 := evm_run rd2356 with [
    raw mload 0 ⟨192⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (getRewardOwedRewardConfigHashMem_mload64 I) (by decide) (by evm_ov),
    swap11]
  have rd2359 := Reasoning.Reach.RD.dup12 rd2358 (by native_decide) (by decide)
  have rd2368 := evm_run rd2359 with [
    swap4, push2 ⟨2368⟩, dup6, push2 ⟨3025⟩, jump (by jump_dest),
    jumpdest, push1 ⟨128⟩, dup2, add, swap1, dup2, lt,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt, lor,
    push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩,
    raw mstore 0 (getRewardOwedConfigAllocMem I) (UInt256.ofNat 6) (by decide) mem_cost
      (by
        unfold getRewardOwedConfigAllocMem getRewardOwedRewardConfigHashMem getRewardOwedConfigZeroMem
        unfold getRewardOwedAlloc64Mem twoWordHashMem wordAt32Mem wordAt0Mem
        unfold Reasoning.Theory.writeCascade Reasoning.Theory.writeWord
        rfl)
      (by decide) (by evm_ov),
    jump (by jump_dest), jumpdest]
  have rdAfterSloadPre := evm_run rd2368 with [dup3]
  obtain ⟨_, _, rdAfterSload⟩ := rdAfterSloadPre.sload (by decide) (by evm_ov)
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) _
    (getRewardOwedRewardConfigSlot0Word σ I :: _) (getRewardOwedConfigAllocMem I)
    (UInt256.ofNat 6) ByteArray.empty (cA, σ) _ _ at rdAfterSload
  rw [show getRewardOwedRewardConfigSlot0Word σ I = slot0 from rfl] at rdAfterSload
  have rd2409pre := evm_run rdAfterSload with [
    swap1, dup12, dup3, and, dup1, swap7,
    raw mstore 3 (getRewardOwedConfigTokenMem I slot0) (UInt256.ofNat 7) (by decide) mem_cost
      (by
        unfold getRewardOwedConfigTokenMem getRewardOwedConfigAllocMem
        unfold getRewardOwedRewardConfigHashMem getRewardOwedConfigZeroMem getRewardOwedAlloc64Mem
        unfold twoWordHashMem wordAt32Mem wordAt0Mem Reasoning.Theory.writeCascade
        unfold Reasoning.Theory.writeWord rewardConfigTokenFromSlot0 slot0
        rfl)
      (by decide) (by evm_ov),
    dup14, dup14, dup7, dup1, push1 ⟨64⟩, shl, sub, dup5, push1 ⟨160⟩, shr, and,
    swap2, add,
    raw mstore 3 (getRewardOwedConfigRescaleMem I slot0) (UInt256.ofNat 8) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩ =
          UInt256.ofNat (2 ^ 64 - 1) from by native_decide]
        unfold getRewardOwedConfigRescaleMem getRewardOwedConfigTokenMem getRewardOwedConfigAllocMem
        unfold getRewardOwedRewardConfigHashMem getRewardOwedConfigZeroMem getRewardOwedAlloc64Mem
        unfold twoWordHashMem wordAt32Mem wordAt0Mem Reasoning.Theory.writeCascade
        unfold Reasoning.Theory.writeWord rewardConfigRescaleFromSlot0
        unfold rewardConfigTokenFromSlot0 slot0
        rfl) (by decide) (by evm_ov),
    shr, and, iszero, iszero, dup13, dup13, add,
    raw mstore 3 (getRewardOwedConfigShouldMem I slot0) (UInt256.ofNat 9) (by decide) mem_cost
      (by
        unfold getRewardOwedConfigShouldMem getRewardOwedConfigRescaleMem
        unfold getRewardOwedConfigTokenMem getRewardOwedConfigAllocMem getRewardOwedRewardConfigHashMem
        unfold getRewardOwedConfigZeroMem getRewardOwedAlloc64Mem twoWordHashMem wordAt32Mem wordAt0Mem
        unfold Reasoning.Theory.writeCascade Reasoning.Theory.writeWord
        unfold rewardConfigShouldUpscaleFromSlot0 rewardConfigShouldUpscaleRawFromSlot0
        unfold rewardConfigRescaleFromSlot0 rewardConfigTokenFromSlot0 slot0
        rfl) (by decide) (by evm_ov),
    add]
  obtain ⟨_, _, rdAfterMultiplier⟩ := rd2409pre.sload (by decide) (by evm_ov)
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) _
    (getRewardOwedMultiplierWord σ I :: _) (getRewardOwedConfigShouldMem I slot0)
    (UInt256.ofNat 9) ByteArray.empty (cA, σ) _ _ at rdAfterMultiplier
  rw [show getRewardOwedMultiplierWord σ I = multiplier from rfl] at rdAfterMultiplier
  have rd2409 := evm_run rdAfterMultiplier with [
    push1 ⟨96⟩, dup11, add,
    raw mstore 3 (getRewardOwedConfigMultiplierMem I slot0 multiplier) (UInt256.ofNat 10) (by decide)
      mem_cost
      (by
        unfold getRewardOwedConfigMultiplierMem getRewardOwedConfigShouldMem
        unfold getRewardOwedConfigRescaleMem getRewardOwedConfigTokenMem getRewardOwedConfigAllocMem
        unfold getRewardOwedRewardConfigHashMem getRewardOwedConfigZeroMem getRewardOwedAlloc64Mem
        unfold twoWordHashMem wordAt32Mem wordAt0Mem Reasoning.Theory.writeCascade
        unfold Reasoning.Theory.writeWord
        unfold rewardConfigShouldUpscaleFromSlot0 rewardConfigShouldUpscaleRawFromSlot0
        unfold rewardConfigRescaleFromSlot0 rewardConfigTokenFromSlot0 slot0 multiplier
        rfl)
      (by decide) (by evm_ov),
    iszero]
  have htokenZeroSlot : rewardConfigTokenFromSlot0 slot0 = ⟨0⟩ := by
    simpa [slot0] using htokenZero
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) _
    (UInt256.isZero (rewardConfigTokenFromSlot0 slot0) :: _)
    (getRewardOwedConfigMultiplierMem I slot0 multiplier) (UInt256.ofNat 10)
    ByteArray.empty (cA, σ) _ _ at rd2409
  rw [htokenZeroSlot] at rd2409
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) _
    (⟨1⟩ :: _) (getRewardOwedConfigMultiplierMem I slot0 multiplier)
    (UInt256.ofNat 10) ByteArray.empty (cA, σ) _ _ at rd2409
  have rd2592 := evm_run rd2409 with [
    push2 ⟨2592⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd2614 := evm_run rd2592 with [
    jumpdest, dup9,
    raw mload 0 ⟨320⟩ (UInt256.ofNat 10) (by decide) mem_cost
      (getRewardOwedConfigMultiplierMem_mload64 I slot0 multiplier)
      (by decide) (by evm_ov),
    push4 ⟨1311535579⟩, push1 ⟨225⟩, shl, dup2,
    raw mstore 3 (getRewardOwedInvalidRewardConfigSelectorMem I slot0 multiplier) (UInt256.ofNat 11)
      (by decide) mem_cost
      (by
        unfold getRewardOwedInvalidRewardConfigSelectorMem getRewardOwedConfigMultiplierMem
        unfold getRewardOwedConfigShouldMem getRewardOwedConfigRescaleMem getRewardOwedConfigTokenMem
        unfold getRewardOwedConfigAllocMem getRewardOwedRewardConfigHashMem getRewardOwedConfigZeroMem
        unfold getRewardOwedAlloc64Mem twoWordHashMem wordAt32Mem wordAt0Mem
        unfold Reasoning.Theory.writeCascade Reasoning.Theory.writeWord
        unfold rewardConfigShouldUpscaleFromSlot0 rewardConfigShouldUpscaleRawFromSlot0
        unfold rewardConfigRescaleFromSlot0 rewardConfigTokenFromSlot0 slot0 multiplier
        rfl)
      (by decide) (by evm_ov),
    swap1, dup2, add, dup6, swap1,
    raw mstore 3 (getRewardOwedInvalidRewardConfigArgMem I slot0 multiplier) (UInt256.ofNat 12)
      (by decide) mem_cost
      (by
        unfold getRewardOwedInvalidRewardConfigArgMem getRewardOwedInvalidRewardConfigSelectorMem
        unfold getRewardOwedConfigMultiplierMem getRewardOwedConfigShouldMem getRewardOwedConfigRescaleMem
        unfold getRewardOwedConfigTokenMem getRewardOwedConfigAllocMem getRewardOwedRewardConfigHashMem
        unfold getRewardOwedConfigZeroMem getRewardOwedAlloc64Mem twoWordHashMem wordAt32Mem wordAt0Mem
        unfold Reasoning.Theory.writeCascade Reasoning.Theory.writeWord
        unfold rewardConfigShouldUpscaleFromSlot0 rewardConfigShouldUpscaleRawFromSlot0
        unfold rewardConfigRescaleFromSlot0 rewardConfigTokenFromSlot0 slot0 multiplier
        rw [show ((⟨320⟩ : UInt256) + ⟨4⟩).toNat = 324 from by native_decide]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide, solcAddrMask_clean hcanonComet])
      (by decide) (by evm_ov),
    push1 ⟨36⟩, swap1]
  exact evm_run rd2614 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem cometRewardsGetRewardOwedBodyReverts_tokenZero (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hz : rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evm I) = ⟨0⟩) :
    ExecTransitionBody config contract evm (getRewardOwedStore I)
      getRewardOwedTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [getRewardOwedTransition, externalEntryGuard, nonpayable, calldataSizeGuard,
    checkedExternalCallStmts] using
    (((((((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (getRewardOwedStore I) hsize)).letStep
          (evalExpr_getRewardOwed_token_of evm I (getRewardOwedFrame_comet evm I)
            (getRewardOwedFrame_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_rescale_of evm I
            (getRewardOwedAfterTokenLocals_comet evm I)
            (getRewardOwedAfterTokenLocals_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_shouldUpscale_of evm I
            (getRewardOwedAfterRescaleLocals_comet evm I)
            (getRewardOwedAfterRescaleLocals_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_multiplier_of evm I
            (getRewardOwedAfterShouldLocals_comet evm I)
            (getRewardOwedAfterShouldLocals_no_rewardConfig evm I))).requireRevert
          (evalExpr_getRewardOwed_token_ne_zero_false_of evm (getRewardOwedSlot0Load evm I)
            (getRewardOwedConfigLocals_token evm I) hz)

theorem cometRewardsGetRewardOwedBodyReverts_accrueNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hnz : rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evm I) ≠ ⟨0⟩)
    (hguard :
      evalExpr? config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
        (.binary .gt (.extCodeSize (.var "comet")) (.intLit 0)) = .ok (.bool false)) :
    ExecTransitionBody config contract evm (getRewardOwedStore I)
      getRewardOwedTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hcheckedSmall :
      ExecBlock config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
        (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
          [.var "account"] "_accrued")
        .reverted := by
    exact checkedExternalCallVarNoCode (cfg := config) (C := contract)
      (evm := evm) (locals := getRewardOwedConfigLocals evm I)
      (receiver := "comet") (retVar := "_accrued") (name := "accrueAccount")
      (sendVal := 0) (args := [.var "account"]) (perm := true) hguard
  have hchecked :
      ExecBlock config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
        (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
          [.var "account"] "_accrued" ++
        [ .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "account"))),
          .internalCall "getRewardAccrued"
            [ .var "comet", .var "account", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier" ] "accrued",
          .letDecl "owed" (some uint256)
            (.ite (.binary .gt (.var "accrued") (.var "claimed"))
              (.binary .sub (.var "accrued") (.var "claimed"))
              (.intLit 0)),
          .return [(.tupleLit [.var "token", .var "owed"])] ])
        .reverted := by
    exact execBlock_append_term hcheckedSmall (by intro f e h; cases h)
  have hprefix :
      ABlock config evm { contract := contract, locals := getRewardOwedStore I }
        getRewardOwedTransition.body
        { contract := contract, locals := getRewardOwedConfigLocals evm I }
        (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
          [.var "account"] "_accrued" ++
        [ .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "account"))),
          .internalCall "getRewardAccrued"
            [ .var "comet", .var "account", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier" ] "accrued",
          .letDecl "owed" (some uint256)
            (.ite (.binary .gt (.var "accrued") (.var "claimed"))
              (.binary .sub (.var "accrued") (.var "claimed"))
              (.intLit 0)),
          .return [(.tupleLit [.var "token", .var "owed"])] ]) := by
    simpa [getRewardOwedTransition, externalEntryGuard, nonpayable, calldataSizeGuard,
      checkedExternalCallStmts, getRewardOwedConfigLocals, getRewardOwedAfterShouldLocals,
      getRewardOwedAfterRescaleLocals, getRewardOwedAfterTokenLocals,
      getRewardOwedBaseLocals] using
      (((((((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      change evalExpr? config { contract := contract, locals := getRewardOwedStore I } evm
        (.env .msgData) = .ok (.bytes evm.executionEnv.calldata)
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (getRewardOwedStore I) hsize)).letStep
          (evalExpr_getRewardOwed_token_of evm I (getRewardOwedFrame_comet evm I)
            (getRewardOwedFrame_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_rescale_of evm I
            (getRewardOwedAfterTokenLocals_comet evm I)
            (getRewardOwedAfterTokenLocals_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_shouldUpscale_of evm I
            (getRewardOwedAfterRescaleLocals_comet evm I)
            (getRewardOwedAfterRescaleLocals_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_multiplier_of evm I
            (getRewardOwedAfterShouldLocals_comet evm I)
            (getRewardOwedAfterShouldLocals_no_rewardConfig evm I))).requireStep
            (evalExpr_getRewardOwed_token_ne_zero_true_of evm (getRewardOwedSlot0Load evm I)
              (getRewardOwedConfigLocals_token evm I) hnz)
  exact hprefix.run hchecked

theorem cometRewardsGetRewardOwedBodyReverts_accrueFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hnz : rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evm I) ≠ ⟨0⟩)
    (hguard :
      evalExpr? config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
        (.binary .gt (.extCodeSize (.var "comet")) (.intLit 0)) = .ok (.bool true))
    (hcall :
      typedCallViaEVM config evm (EVM.address (getRewardOwedCometTarget I))
        "accrueAccount" 0 (getRewardOwedAccrueAccountArgs I)
        (false, evm', out) true) :
    ExecTransitionBody config contract evm (getRewardOwedStore I)
      getRewardOwedTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hcheckedSmall :
      ExecBlock config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
        (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
          [.var "account"] "_accrued")
        .reverted := by
    exact checkedExternalCallVarFailure (cfg := config) (C := contract)
      (evm := evm) (evm' := evm') (locals := getRewardOwedConfigLocals evm I)
      (receiver := "comet") (retVar := "_accrued") (name := "accrueAccount")
      (target := getRewardOwedCometTarget I) (sendVal := 0)
      (args := [.var "account"]) (argVals := getRewardOwedAccrueAccountArgs I)
      (out := out) (perm := true)
      hguard (getRewardOwedConfigLocals_comet evm I)
      (evalExprs_getRewardOwed_accrueAccountArgs_of evm I
        (getRewardOwedConfigLocals_account evm I))
      hcall
  have hchecked :
      ExecBlock config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
        (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
          [.var "account"] "_accrued" ++
        [ .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "account"))),
          .internalCall "getRewardAccrued"
            [ .var "comet", .var "account", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier" ] "accrued",
          .letDecl "owed" (some uint256)
            (.ite (.binary .gt (.var "accrued") (.var "claimed"))
              (.binary .sub (.var "accrued") (.var "claimed"))
              (.intLit 0)),
          .return [(.tupleLit [.var "token", .var "owed"])] ])
        .reverted := by
    exact execBlock_append_term hcheckedSmall (by intro f e h; cases h)
  have hprefix :
      ABlock config evm { contract := contract, locals := getRewardOwedStore I }
        getRewardOwedTransition.body
        { contract := contract, locals := getRewardOwedConfigLocals evm I }
        (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
          [.var "account"] "_accrued" ++
        [ .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "account"))),
          .internalCall "getRewardAccrued"
            [ .var "comet", .var "account", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier" ] "accrued",
          .letDecl "owed" (some uint256)
            (.ite (.binary .gt (.var "accrued") (.var "claimed"))
              (.binary .sub (.var "accrued") (.var "claimed"))
              (.intLit 0)),
          .return [(.tupleLit [.var "token", .var "owed"])] ]) := by
    simpa [getRewardOwedTransition, externalEntryGuard, nonpayable, calldataSizeGuard,
      checkedExternalCallStmts, getRewardOwedConfigLocals, getRewardOwedAfterShouldLocals,
      getRewardOwedAfterRescaleLocals, getRewardOwedAfterTokenLocals,
      getRewardOwedBaseLocals] using
      (((((((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      change evalExpr? config { contract := contract, locals := getRewardOwedStore I } evm
        (.env .msgData) = .ok (.bytes evm.executionEnv.calldata)
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (getRewardOwedStore I) hsize)).letStep
          (evalExpr_getRewardOwed_token_of evm I (getRewardOwedFrame_comet evm I)
            (getRewardOwedFrame_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_rescale_of evm I
            (getRewardOwedAfterTokenLocals_comet evm I)
            (getRewardOwedAfterTokenLocals_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_shouldUpscale_of evm I
            (getRewardOwedAfterRescaleLocals_comet evm I)
            (getRewardOwedAfterRescaleLocals_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_multiplier_of evm I
            (getRewardOwedAfterShouldLocals_comet evm I)
            (getRewardOwedAfterShouldLocals_no_rewardConfig evm I))).requireStep
            (evalExpr_getRewardOwed_token_ne_zero_true_of evm (getRewardOwedSlot0Load evm I)
              (getRewardOwedConfigLocals_token evm I) hnz)
  exact hprefix.run hchecked

theorem cometRewardsGetRewardOwedBodyReverts_getRewardAccrued
    (evm evmAcc : EVM.State) (I : ExecutionEnv) {accrueOut : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hnz : rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evm I) ≠ ⟨0⟩)
    (hguard :
      evalExpr? config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
        (.binary .gt (.extCodeSize (.var "comet")) (.intLit 0)) = .ok (.bool true))
    (hcallAccrue :
      typedCallViaEVM config evm (EVM.address (getRewardOwedCometTarget I))
        "accrueAccount" 0 (getRewardOwedAccrueAccountArgs I)
        (true, evmAcc, accrueOut) true)
    (hdecAccrue : config.externalABI.decode? "accrueAccount" accrueOut = some [])
    (hinner :
      ExecFuncBody config
        { contract := contract,
          locals := getRewardAccruedStore I (getRewardOwedSlot0Load evm I)
            (getRewardOwedMultiplierLoad evm I) }
        evmAcc getRewardAccruedFunction.body .reverted) :
    ExecTransitionBody config contract evm (getRewardOwedStore I)
      getRewardOwedTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hcheckedSmall :
      ExecBlock config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
        (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
          [.var "account"] "_accrued")
        (.ok { contract := contract, locals := getRewardOwedAfterAccrueLocals evm I }
          evmAcc) := by
    simpa [checkedExternalCallStmts, getRewardOwedAfterAccrueLocals, collapseReturns]
      using checkedExternalCallVarSuccess (cfg := config) (C := contract)
        (evm := evm) (evm' := evmAcc) (locals := getRewardOwedConfigLocals evm I)
        (receiver := "comet") (retVar := "_accrued") (name := "accrueAccount")
        (target := getRewardOwedCometTarget I) (sendVal := 0)
        (args := [.var "account"]) (argVals := getRewardOwedAccrueAccountArgs I)
        (out := accrueOut) (perm := true) (value := [])
        hguard (getRewardOwedConfigLocals_comet evm I)
        (evalExprs_getRewardOwed_accrueAccountArgs_of evm I
          (getRewardOwedConfigLocals_account evm I))
        hcallAccrue hdecAccrue
  have hrest :
      ExecBlock config { contract := contract, locals := getRewardOwedAfterAccrueLocals evm I }
        evmAcc
        [ .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "account"))),
          .internalCall "getRewardAccrued"
            [ .var "comet", .var "account", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier" ] "accrued",
          .letDecl "owed" (some uint256)
            (.ite (.binary .gt (.var "accrued") (.var "claimed"))
              (.binary .sub (.var "accrued") (.var "claimed"))
              (.intLit 0)),
          .return [(.tupleLit [.var "token", .var "owed"])] ]
        .reverted := by
    refine ExecBlock.consNormal
      (solm' := { contract := contract, locals := getRewardOwedAfterClaimedLocals evm evmAcc I })
      (evm' := evmAcc) ?hclaimed ?_
    · exact ExecStmt.letDecl (evalExpr_getRewardOwed_claimed_afterAccrue evm evmAcc I)
    refine ExecBlock.consRevert ?_
    exact internalCallFunctionRevert
      (cfg := config)
      (caller := { contract := contract, locals := getRewardOwedAfterClaimedLocals evm evmAcc I })
      (evm := evmAcc)
      (name := "getRewardAccrued") (retVar := "accrued")
      (args := [.var "comet", .var "account", .var "rescaleFactor",
        .var "shouldUpscale", .var "multiplier"])
      (argVals := getRewardAccruedArgs I (getRewardOwedSlot0Load evm I)
        (getRewardOwedMultiplierLoad evm I))
      (callee := getRewardAccruedFunction)
      (locals := getRewardAccruedStore I (getRewardOwedSlot0Load evm I)
        (getRewardOwedMultiplierLoad evm I))
      (evalExprs_getRewardOwed_getRewardAccruedArgs_afterClaimed evm evmAcc I)
      lookupCallable_getRewardAccrued
      (bindParams_getRewardAccrued I (getRewardOwedSlot0Load evm I)
        (getRewardOwedMultiplierLoad evm I))
      hinner
  have hchecked :
      ExecBlock config { contract := contract, locals := getRewardOwedConfigLocals evm I } evm
        (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
          [.var "account"] "_accrued" ++
        [ .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "account"))),
          .internalCall "getRewardAccrued"
            [ .var "comet", .var "account", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier" ] "accrued",
          .letDecl "owed" (some uint256)
            (.ite (.binary .gt (.var "accrued") (.var "claimed"))
              (.binary .sub (.var "accrued") (.var "claimed"))
              (.intLit 0)),
          .return [(.tupleLit [.var "token", .var "owed"])] ])
        .reverted := by
    exact execBlock_append hcheckedSmall hrest
  have hprefix :
      ABlock config evm { contract := contract, locals := getRewardOwedStore I }
        getRewardOwedTransition.body
        { contract := contract, locals := getRewardOwedConfigLocals evm I }
        (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
          [.var "account"] "_accrued" ++
        [ .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "account"))),
          .internalCall "getRewardAccrued"
            [ .var "comet", .var "account", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier" ] "accrued",
          .letDecl "owed" (some uint256)
            (.ite (.binary .gt (.var "accrued") (.var "claimed"))
              (.binary .sub (.var "accrued") (.var "claimed"))
              (.intLit 0)),
          .return [(.tupleLit [.var "token", .var "owed"])] ]) := by
    simpa [getRewardOwedTransition, externalEntryGuard, nonpayable, calldataSizeGuard,
      checkedExternalCallStmts, getRewardOwedConfigLocals, getRewardOwedAfterShouldLocals,
      getRewardOwedAfterRescaleLocals, getRewardOwedAfterTokenLocals,
      getRewardOwedBaseLocals] using
      (((((((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      change evalExpr? config { contract := contract, locals := getRewardOwedStore I } evm
        (.env .msgData) = .ok (.bytes evm.executionEnv.calldata)
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (getRewardOwedStore I) hsize)).letStep
          (evalExpr_getRewardOwed_token_of evm I (getRewardOwedFrame_comet evm I)
            (getRewardOwedFrame_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_rescale_of evm I
            (getRewardOwedAfterTokenLocals_comet evm I)
            (getRewardOwedAfterTokenLocals_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_shouldUpscale_of evm I
            (getRewardOwedAfterRescaleLocals_comet evm I)
            (getRewardOwedAfterRescaleLocals_no_rewardConfig evm I))).letStep
          (evalExpr_getRewardOwed_multiplier_of evm I
            (getRewardOwedAfterShouldLocals_comet evm I)
            (getRewardOwedAfterShouldLocals_no_rewardConfig evm I))).requireStep
            (evalExpr_getRewardOwed_token_ne_zero_true_of evm (getRewardOwedSlot0Load evm I)
              (getRewardOwedConfigLocals_token evm I) hnz)
  exact hprefix.run hchecked

set_option maxHeartbeats 10000000 in
/-- `getRewardOwed(address,address)` body, reached at pc 2266. -/
theorem cometRewardsGetRewardOwedBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cometRewardsBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cometRewardsSelBytes 3))
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) getRewardOwedPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz4 := cometRewardsGetRewardOwedSelector_size hsel
  have hd := cometRewardsDispatch_getRewardOwed (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonComet : (getRewardOwedCometWord I).toNat < EVM.addressModulus
      · by_cases hcanonAccount : (getRewardOwedAccountWord I).toNat < EVM.addressModulus
        · have hdec :=
            cometRewardsDecode_getRewardOwed_ok (I := I) hsz68 hhi hcanonComet
              hcanonAccount
          have hslotWord :
              getRewardOwedRewardConfigSlot0Word σ_evm I =
                getRewardOwedRewardConfigSlot0Word σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner
              (getRewardOwedRewardConfigSlotOf I) ⟨0⟩
          have hmulWord :
              getRewardOwedMultiplierWord σ_evm I =
                getRewardOwedMultiplierWord σ_solm I := by
            simpa [getRewardOwedMultiplierWord] using
              accountMapEquiv_storage_findD hAccounts I.codeOwner
                (getRewardOwedRewardConfigSlotOf I + (⟨1⟩ : UInt256)) (⟨0⟩ : UInt256)
          by_cases htokenZero :
              rewardConfigTokenFromSlot0
                (getRewardOwedRewardConfigSlot0Word σ_evm I) = ⟨0⟩
          · let evmSolm : EVM.State :=
              initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
            have htokenZeroSolm :
                rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evmSolm I) = ⟨0⟩ := by
              have hload :
                  getRewardOwedSlot0Load evmSolm I =
                    getRewardOwedRewardConfigSlot0Word σ_solm I := by
                simp [evmSolm, getRewardOwedSlot0Load, getRewardOwedRewardConfigSlot0Word,
                  initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
              rw [hload, ← hslotWord]
              exact htokenZero
            have hbody :
                ExecTransitionBody config contract evmSolm (getRewardOwedStore I)
                  getRewardOwedTransition.body .reverted := by
              exact cometRewardsGetRewardOwedBodyReverts_tokenZero evmSolm I
                (by simp only [evmSolm, initState]; exact hwv)
                (by simp only [evmSolm, initState]; exact hhi)
                htokenZeroSolm
            exact (cometRewardsGetRewardOwedX_tokenZero (g := Sat256.ofUInt256 g)
                hwv hsz68 hsize hhi hcanonComet hcanonAccount htokenZero hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
          · let evmSolm : EVM.State :=
              initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
            by_cases hnoCode :
                Reasoning.Theory.uniswapExtCodeSizeWord σ_evm
                  (UInt256.land (getRewardOwedCometWord I) solcAddrMask) = ⟨0⟩
            · have htokenNZSolm :
                  rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evmSolm I) ≠ ⟨0⟩ := by
                have hload :
                    getRewardOwedSlot0Load evmSolm I =
                      getRewardOwedRewardConfigSlot0Word σ_solm I := by
                  simp [evmSolm, getRewardOwedSlot0Load, getRewardOwedRewardConfigSlot0Word,
                    initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
                rw [hload, ← hslotWord]
                exact htokenZero
              have hnoCodeSolm :
                  Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
                    (UInt256.land (getRewardOwedCometWord I) solcAddrMask) = ⟨0⟩ := by
                rw [← uniswapExtCodeSizeWord_accountMapEquiv hAccounts
                  (UInt256.land (getRewardOwedCometWord I) solcAddrMask)]
                exact hnoCode
              have hguard :
                  evalExpr? config
                    { contract := contract, locals := getRewardOwedConfigLocals evmSolm I } evmSolm
                    (.binary .gt (.extCodeSize (.var "comet")) (.intLit 0)) =
                    .ok (.bool false) := by
                exact evalExpr_getRewardOwed_extCodeSizeGuard_false evmSolm I
                  hcanonComet (by simpa [evmSolm, initState] using hnoCodeSolm)
              have hbody :
                  ExecTransitionBody config contract evmSolm (getRewardOwedStore I)
                    getRewardOwedTransition.body .reverted := by
                exact cometRewardsGetRewardOwedBodyReverts_accrueNoCode evmSolm I
                  (by simp only [evmSolm, initState]; exact hwv)
                  (by simp only [evmSolm, initState]; exact hhi)
                  htokenNZSolm hguard
              exact (cometRewardsGetRewardOwedX_accrueNoCode (g := Sat256.ofUInt256 g)
                  hwv hsz68 hsize hhi hcanonComet hcanonAccount htokenZero hnoCode hreach)
                |>.reEquivExecutionRevert hcode hd hdec hbody
            · have htokenNZSolm :
                  rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evmSolm I) ≠ ⟨0⟩ := by
                have hload :
                    getRewardOwedSlot0Load evmSolm I =
                      getRewardOwedRewardConfigSlot0Word σ_solm I := by
                  simp [evmSolm, getRewardOwedSlot0Load, getRewardOwedRewardConfigSlot0Word,
                    initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
                rw [hload, ← hslotWord]
                exact htokenZero
              have hcodeSizeSolm :
                  Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
                    (UInt256.land (getRewardOwedCometWord I) solcAddrMask) ≠ ⟨0⟩ := by
                intro hz
                exact hnoCode ((uniswapExtCodeSizeWord_accountMapEquiv hAccounts
                  (UInt256.land (getRewardOwedCometWord I) solcAddrMask)).trans hz)
              have hguard :
                  evalExpr? config
                    { contract := contract, locals := getRewardOwedConfigLocals evmSolm I } evmSolm
                    (.binary .gt (.extCodeSize (.var "comet")) (.intLit 0)) =
                    .ok (.bool true) := by
                exact evalExpr_getRewardOwed_extCodeSizeGuard_true evmSolm I
                  hcanonComet (by simpa [evmSolm, initState] using hcodeSizeSolm)
              by_cases hdepth : I.depth.val < 1024
              · obtain ⟨cA', σ'_evm, σ'_solm, A'_solm, z, out, k', C',
                    hcallSolm, hPostAccounts, rdPost, houtSize⟩ :=
                  cometRewardsGetRewardOwedX_call_accrueAccount_made
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hperm hwv hsz68 hsize hhi hcanonComet hcanonAccount htokenZero
                    hnoCode hdepth hreach hAccounts
                cases z
                · have hbody :
                      ExecTransitionBody config contract evmSolm (getRewardOwedStore I)
                        getRewardOwedTransition.body .reverted := by
                    exact cometRewardsGetRewardOwedBodyReverts_accrueFailure evmSolm
                      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                          accountMap := σ'_solm
                          substate := A'_solm
                          createdAccounts := cA' }
                      I
                      (by simp only [evmSolm, initState]; exact hwv)
                      (by simp only [evmSolm, initState]; exact hhi)
                      htokenNZSolm hguard hcallSolm
                  have hrev :
                      RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                    exact cometRewardsGetRewardOwedX_after_accrueAccount_failure
                      (slot0 := getRewardOwedRewardConfigSlot0Word σ_evm I)
                      (multiplier := getRewardOwedMultiplierWord σ_evm I)
                      rdPost houtSize
                  exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                · let evmAcc : EVM.State :=
                    { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σ'_solm
                        substate := A'_solm
                        createdAccounts := cA' }
                  have hdecAccrue :
                      config.externalABI.decode? "accrueAccount" out = some [] := by
                    simp [config, compoundRewardsExternalABI, decodeVoid?]
                  have hclaimedWord :
                      getRewardOwedClaimedWord σ'_evm I =
                        getRewardOwedClaimedWord σ'_solm I :=
                    accountMapEquiv_storage_findD hPostAccounts I.codeOwner
                      (getRewardOwedRewardsClaimedSlotOf I) ⟨0⟩
                  obtain ⟨cA'', σ''_evm, σ''_solm, A''_solm, zBase, baseOut,
                      kBase, CBase, hcallBaseSolm, hBaseAccounts, rdBasePost,
                      hbaseOutSize, hbaseOutHi⟩ :=
                    cometRewardsGetRewardOwedX_call_baseTrackingAccrued_made
                      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := Sat256.ofUInt256 g)
                      (slot0 := getRewardOwedRewardConfigSlot0Word σ_evm I)
                      (multiplier := getRewardOwedMultiplierWord σ_evm I)
                      (accrueOut := out) (cA' := cA') (σ'_evm := σ'_evm)
                      (σ'_solm := σ'_solm) (A'_solm := A'_solm)
                      hcanonComet hcanonAccount hdepth hPostAccounts rdPost houtSize
                  let evmBase : EVM.State :=
                    { evmAcc with
                        accountMap := σ''_solm
                        substate := A''_solm
                        createdAccounts := cA'' }
                  cases zBase
                  · have hinner :
                        ExecFuncBody config
                          { contract := contract,
                            locals := getRewardAccruedStore I
                              (getRewardOwedSlot0Load evmSolm I)
                              (getRewardOwedMultiplierLoad evmSolm I) }
                          evmAcc getRewardAccruedFunction.body .reverted := by
                      exact getRewardAccruedBodyReverts_callFailure evmAcc evmBase I
                        (getRewardOwedSlot0Load evmSolm I)
                        (getRewardOwedMultiplierLoad evmSolm I)
                        (by simpa [evmAcc, evmBase] using hcallBaseSolm)
                    have hbody :
                        ExecTransitionBody config contract evmSolm (getRewardOwedStore I)
                          getRewardOwedTransition.body .reverted := by
                      exact cometRewardsGetRewardOwedBodyReverts_getRewardAccrued
                        evmSolm evmAcc I
                        (by simp only [evmSolm, initState]; exact hwv)
                        (by simp only [evmSolm, initState]; exact hhi)
                        htokenNZSolm hguard
                        (by simpa [evmAcc] using hcallSolm)
                        hdecAccrue hinner
                    have hrev :
                        RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                      exact cometRewardsGetRewardOwedX_after_baseTracking_failure
                        (slot0 := getRewardOwedRewardConfigSlot0Word σ_evm I)
                        (multiplier := getRewardOwedMultiplierWord σ_evm I)
                        rdBasePost houtSize hbaseOutSize
                    exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                  · by_cases hbaseShort : baseOut.size < 32
                    · have hdecBase :=
                        cometRewardsBaseTrackingAccrued_decode_none_short
                          (out := baseOut) hbaseShort
                      have hinner :
                          ExecFuncBody config
                            { contract := contract,
                              locals := getRewardAccruedStore I
                                (getRewardOwedSlot0Load evmSolm I)
                                (getRewardOwedMultiplierLoad evmSolm I) }
                            evmAcc getRewardAccruedFunction.body .reverted := by
                        exact getRewardAccruedBodyReverts_decode evmAcc evmBase I
                          (getRewardOwedSlot0Load evmSolm I)
                          (getRewardOwedMultiplierLoad evmSolm I)
                          (by simpa [evmAcc, evmBase] using hcallBaseSolm)
                          hdecBase
                      have hbody :
                          ExecTransitionBody config contract evmSolm (getRewardOwedStore I)
                            getRewardOwedTransition.body .reverted := by
                        exact cometRewardsGetRewardOwedBodyReverts_getRewardAccrued
                          evmSolm evmAcc I
                          (by simp only [evmSolm, initState]; exact hwv)
                          (by simp only [evmSolm, initState]; exact hhi)
                          htokenNZSolm hguard
                          (by simpa [evmAcc] using hcallSolm)
                          hdecAccrue hinner
                      have hrev :
                          RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                        exact cometRewardsGetRewardOwedX_after_baseTracking_short_revert
                          (slot0 := getRewardOwedRewardConfigSlot0Word σ_evm I)
                          (multiplier := getRewardOwedMultiplierWord σ_evm I)
                          rdBasePost hbaseShort hbaseOutSize
                      exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                    · have hbase32 : 32 ≤ baseOut.size := by omega
                      by_cases hbaseWord :
                          fromByteArrayBigEndian (baseOut.extract 0 32) < EVM.twoPow 64
                      · let baseAccrued : UInt256 := getRewardOwedBaseTrackingReturnWord baseOut
                        let slotE : UInt256 := getRewardOwedRewardConfigSlot0Word σ_evm I
                        let mulE : UInt256 := getRewardOwedMultiplierWord σ_evm I
                        let claimedE : UInt256 := getRewardOwedClaimedWord σ'_evm I
                        have hbaseToNat :
                            baseAccrued.toNat =
                              fromByteArrayBigEndian (baseOut.extract 0 32) := by
                          simpa [baseAccrued, getRewardOwedBaseTrackingReturnWord] using
                            UInt256.toNat_ofNat_of_lt
                              (fromByteArrayBigEndian_extract0_32_lt hbase32)
                        have hbase64 : baseAccrued.toNat < EVM.twoPow 64 := by
                          rw [hbaseToNat]
                          exact hbaseWord
                        have hdecBase :
                            config.externalABI.decode? "baseTrackingAccrued" baseOut =
                              some [.int (Int.ofNat baseAccrued.toNat)] := by
                          have hdecBase0 :=
                            cometRewardsBaseTrackingAccrued_decode_ok
                              (out := baseOut) hbase32 hbaseOutHi hbaseWord
                          simpa [hbaseToNat] using hdecBase0
                        have hslotLoadSolm :
                            getRewardOwedSlot0Load evmSolm I =
                              getRewardOwedRewardConfigSlot0Word σ_solm I := by
                          simp [evmSolm, getRewardOwedSlot0Load,
                            getRewardOwedRewardConfigSlot0Word, initState,
                            Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
                        have hslotLoadEvm :
                            getRewardOwedSlot0Load evmSolm I = slotE := by
                          rw [hslotLoadSolm, ← hslotWord]
                        have hmulLoadSolm :
                            getRewardOwedMultiplierLoad evmSolm I =
                              getRewardOwedMultiplierWord σ_solm I := by
                          simp [evmSolm, getRewardOwedMultiplierLoad,
                            getRewardOwedMultiplierWord, initState,
                            Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
                        have hmulLoadEvm :
                            getRewardOwedMultiplierLoad evmSolm I = mulE := by
                          rw [hmulLoadSolm, ← hmulWord]
                        have hclaimedLoadSolm :
                            getRewardOwedClaimedLoad evmAcc I =
                              getRewardOwedClaimedWord σ'_solm I := by
                          simp [evmAcc, getRewardOwedClaimedLoad,
                            getRewardOwedClaimedWord, initState,
                            Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
                        have hclaimedLoadEvm :
                            getRewardOwedClaimedLoad evmAcc I = claimedE := by
                          rw [hclaimedLoadSolm, ← hclaimedWord]
                        obtain ⟨_, _, rd3740⟩ :=
                          cometRewardsGetRewardOwedX_after_baseTracking_decode_ok
                            (slot0 := slotE) (multiplier := mulE)
                            rdBasePost houtSize hbase32 hbaseOutSize
                            (by simpa [baseAccrued] using hbase64)
                        by_cases hshould :
                            rewardConfigShouldUpscaleRawFromSlot0 slotE ≠ ⟨0⟩
                        · let upNat := getRewardAccruedUpscaledNat slotE baseAccrued
                          let accruedNat := getRewardAccruedReturnNat mulE upNat
                          have hup : upNat < UInt256.size := by
                            simpa [upNat] using
                              getRewardAccruedUpscaledNat_lt_size_of_base64
                                (slot0 := slotE) (accrued := baseAccrued) hbase64
                          by_cases hscaled :
                              getRewardAccruedScaledNat mulE upNat < UInt256.size
                          · have hinner :
                                ExecFuncBody config
                                  { contract := contract,
                                    locals := getRewardAccruedStore I
                                      (getRewardOwedSlot0Load evmSolm I)
                                      (getRewardOwedMultiplierLoad evmSolm I) }
                                  evmAcc getRewardAccruedFunction.body
                                  (.returned
                                    (getRewardAccruedAfterAssignedScaledFrame I
                                      (getRewardOwedSlot0Load evmSolm I)
                                      (getRewardOwedMultiplierLoad evmSolm I)
                                      baseAccrued
                                      (getRewardAccruedUpscaledNat
                                        (getRewardOwedSlot0Load evmSolm I) baseAccrued))
                                    evmBase
                                    (some [.int (Int.ofNat accruedNat)])) := by
                              simpa [hslotLoadEvm, hmulLoadEvm, upNat, accruedNat] using
                                getRewardAccruedBodyReturns_upscale
                                  evmAcc evmBase I slotE mulE baseAccrued
                                  (by simpa [evmAcc, evmBase] using hcallBaseSolm)
                                  hdecBase hshould hup hscaled
                            have hbody :
                                ExecTransitionBody config contract evmSolm (getRewardOwedStore I)
                                  getRewardOwedTransition.body
                                  (.returned
                                    { contract := contract,
                                      locals := getRewardOwedAfterOwedLocals evmSolm evmAcc I
                                        accruedNat }
                                    evmBase
                                    (some [.tuple
                                      [ getRewardOwedTokenValueFromSlot0
                                          (getRewardOwedSlot0Load evmSolm I),
                                        .int (Int.ofNat
                                          (getRewardOwedOwedNat evmAcc I accruedNat)) ]])) := by
                              simpa [hslotLoadEvm, hmulLoadEvm, upNat, accruedNat] using
                                cometRewardsGetRewardOwedBodyReturns_upscale
                                  evmSolm evmAcc evmBase I
                                  (by simp only [evmSolm, initState]; exact hwv)
                                  (by simp only [evmSolm, initState]; exact hhi)
                                  htokenNZSolm hguard
                                  (by simpa [evmAcc] using hcallSolm)
                                  hdecAccrue
                                  (by simpa [evmAcc, evmBase] using hcallBaseSolm)
                                  hdecBase
                                  (by simpa [hslotLoadEvm] using hshould)
                                  (by simpa [hslotLoadEvm, upNat] using hup)
                                  (by simpa [hslotLoadEvm, hmulLoadEvm, upNat] using hscaled)
                            obtain ⟨_, _, rd2499⟩ :=
                              cometRewardsGetRewardOwedX_getRewardAccrued_upscale_success
                                (slot0 := slotE) (multiplier := mulE)
                                rd3740 houtSize hbase32 hbaseOutSize
                                (by simpa [baseAccrued] using hbase64)
                                hshould hscaled
                            have hret :=
                              cometRewardsGetRewardOwedX_return_from2499
                                (slot0 := slotE) (multiplier := mulE)
                                rd2499 houtSize hbase32 hbaseOutSize
                            have haccruedNatLt : accruedNat < UInt256.size := by
                              dsimp [accruedNat, getRewardAccruedReturnNat]
                              exact lt_of_le_of_lt (Nat.div_le_self _ _) hscaled
                            have hOwedNatLt :
                                getRewardOwedOwedNat evmAcc I accruedNat < UInt256.size := by
                              simpa [getRewardOwedOwedNat, hclaimedLoadEvm] using
                                getRewardOwedOwedNat_lt claimedE haccruedNatLt
                            have hOwedWord :
                                getRewardOwedReturnOwedWord claimedE (UInt256.ofNat accruedNat) =
                                  UInt256.ofNat (getRewardOwedOwedNat evmAcc I accruedNat) := by
                              rw [getRewardOwedReturnOwedWord_of_ofNat claimedE haccruedNatLt]
                              simp [getRewardOwedOwedNat, hclaimedLoadEvm]
                            exact hret.reEquivExecutionGenAccountMapEquiv
                              hcode hd hdec hbody rfl hBaseAccounts
                              (returnEquiv.returned rfl (by
                                have henc :=
                                  getRewardOwedEncodeReturnValue_tuple
                                    (getRewardOwedSlot0Load evmSolm I)
                                    (UInt256.ofNat (getRewardOwedOwedNat evmAcc I accruedNat))
                                rw [UInt256.toNat_ofNat_of_lt hOwedNatLt] at henc
                                simpa [getRewardOwedTransition, hslotLoadEvm, slotE, claimedE,
                                  baseAccrued, upNat, accruedNat, hOwedWord] using henc))
                          · have hinner :
                                ExecFuncBody config
                                  { contract := contract,
                                    locals := getRewardAccruedStore I
                                      (getRewardOwedSlot0Load evmSolm I)
                                      (getRewardOwedMultiplierLoad evmSolm I) }
                                  evmAcc getRewardAccruedFunction.body .reverted := by
                              exact getRewardAccruedBodyReverts_upscale_scaledOverflow
                                evmAcc evmBase I
                                (getRewardOwedSlot0Load evmSolm I)
                                (getRewardOwedMultiplierLoad evmSolm I)
                                baseAccrued
                                (by simpa [evmAcc, evmBase] using hcallBaseSolm)
                                hdecBase
                                (by simpa [hslotLoadEvm] using hshould)
                                (by simpa [hslotLoadEvm, upNat] using hup)
                                (by
                                  rw [hslotLoadEvm, hmulLoadEvm]
                                  simpa [upNat] using Nat.le_of_not_gt hscaled)
                            have hbody :
                                ExecTransitionBody config contract evmSolm (getRewardOwedStore I)
                                  getRewardOwedTransition.body .reverted := by
                              exact cometRewardsGetRewardOwedBodyReverts_getRewardAccrued
                                evmSolm evmAcc I
                                (by simp only [evmSolm, initState]; exact hwv)
                                (by simp only [evmSolm, initState]; exact hhi)
                                htokenNZSolm hguard
                                (by simpa [evmAcc] using hcallSolm)
                                hdecAccrue hinner
                            have hrev :
                                RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                              exact
                                cometRewardsGetRewardOwedX_getRewardAccrued_upscale_overflow_revert
                                  (slot0 := slotE) (multiplier := mulE)
                                  rd3740 houtSize hbase32 hbaseOutSize
                                  (by simpa [baseAccrued] using hbase64)
                                  hshould (Nat.le_of_not_gt hscaled)
                            exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                        · have hshouldZero :
                              rewardConfigShouldUpscaleRawFromSlot0 slotE = ⟨0⟩ := by
                            by_contra hz
                            exact hshould hz
                          by_cases hrescaleZero :
                              rewardConfigRescaleFromSlot0 slotE = ⟨0⟩
                          · have hinner :
                                ExecFuncBody config
                                  { contract := contract,
                                    locals := getRewardAccruedStore I
                                      (getRewardOwedSlot0Load evmSolm I)
                                      (getRewardOwedMultiplierLoad evmSolm I) }
                                  evmAcc getRewardAccruedFunction.body .reverted := by
                              exact getRewardAccruedBodyReverts_downscale_zero
                                evmAcc evmBase I
                                (getRewardOwedSlot0Load evmSolm I)
                                (getRewardOwedMultiplierLoad evmSolm I)
                                baseAccrued
                                (by simpa [evmAcc, evmBase] using hcallBaseSolm)
                                hdecBase
                                (by simpa [hslotLoadEvm] using hshouldZero)
                                (by simpa [hslotLoadEvm] using hrescaleZero)
                            have hbody :
                                ExecTransitionBody config contract evmSolm (getRewardOwedStore I)
                                  getRewardOwedTransition.body .reverted := by
                              exact cometRewardsGetRewardOwedBodyReverts_getRewardAccrued
                                evmSolm evmAcc I
                                (by simp only [evmSolm, initState]; exact hwv)
                                (by simp only [evmSolm, initState]; exact hhi)
                                htokenNZSolm hguard
                                (by simpa [evmAcc] using hcallSolm)
                                hdecAccrue hinner
                            have hrev :
                                RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                              exact
                                cometRewardsGetRewardOwedX_getRewardAccrued_downscale_zero_revert
                                  (slot0 := slotE) (multiplier := mulE)
                                  rd3740 houtSize hbase32 hbaseOutSize
                                  (by simpa [baseAccrued] using hbase64)
                                  hshouldZero hrescaleZero
                            exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                          · let downNat := getRewardAccruedDownscaledNat slotE baseAccrued
                            let accruedNat := getRewardAccruedReturnNat mulE downNat
                            by_cases hscaled :
                                getRewardAccruedScaledNat mulE downNat < UInt256.size
                            · have hinner :
                                  ExecFuncBody config
                                    { contract := contract,
                                      locals := getRewardAccruedStore I
                                        (getRewardOwedSlot0Load evmSolm I)
                                        (getRewardOwedMultiplierLoad evmSolm I) }
                                    evmAcc getRewardAccruedFunction.body
                                    (.returned
                                      (getRewardAccruedAfterAssignedScaledFrame I
                                        (getRewardOwedSlot0Load evmSolm I)
                                        (getRewardOwedMultiplierLoad evmSolm I)
                                        baseAccrued
                                        (getRewardAccruedDownscaledNat
                                          (getRewardOwedSlot0Load evmSolm I) baseAccrued))
                                      evmBase
                                      (some [.int (Int.ofNat accruedNat)])) := by
                                simpa [hslotLoadEvm, hmulLoadEvm, downNat, accruedNat] using
                                  getRewardAccruedBodyReturns_downscale
                                    evmAcc evmBase I slotE mulE baseAccrued
                                    (by simpa [evmAcc, evmBase] using hcallBaseSolm)
                                    hdecBase hshouldZero hrescaleZero hscaled
                              have hbody :
                                  ExecTransitionBody config contract evmSolm
                                    (getRewardOwedStore I) getRewardOwedTransition.body
                                    (.returned
                                      { contract := contract,
                                        locals := getRewardOwedAfterOwedLocals evmSolm evmAcc I
                                          accruedNat }
                                      evmBase
                                      (some [.tuple
                                        [ getRewardOwedTokenValueFromSlot0
                                            (getRewardOwedSlot0Load evmSolm I),
                                          .int (Int.ofNat
                                            (getRewardOwedOwedNat evmAcc I accruedNat)) ]])) := by
                                simpa [hslotLoadEvm, hmulLoadEvm, downNat, accruedNat] using
                                  cometRewardsGetRewardOwedBodyReturns_downscale
                                    evmSolm evmAcc evmBase I
                                    (by simp only [evmSolm, initState]; exact hwv)
                                    (by simp only [evmSolm, initState]; exact hhi)
                                    htokenNZSolm hguard
                                    (by simpa [evmAcc] using hcallSolm)
                                    hdecAccrue
                                    (by simpa [evmAcc, evmBase] using hcallBaseSolm)
                                    hdecBase
                                    (by simpa [hslotLoadEvm] using hshouldZero)
                                    (by simpa [hslotLoadEvm] using hrescaleZero)
                                    (by simpa [hslotLoadEvm, hmulLoadEvm, downNat] using hscaled)
                              obtain ⟨_, _, rd2499⟩ :=
                                cometRewardsGetRewardOwedX_getRewardAccrued_downscale_success
                                  (slot0 := slotE) (multiplier := mulE)
                                  rd3740 houtSize hbase32 hbaseOutSize
                                  (by simpa [baseAccrued] using hbase64)
                                  hshouldZero hrescaleZero hscaled
                              have hret :=
                                cometRewardsGetRewardOwedX_return_from2499
                                  (slot0 := slotE) (multiplier := mulE)
                                  rd2499 houtSize hbase32 hbaseOutSize
                              have haccruedNatLt : accruedNat < UInt256.size := by
                                dsimp [accruedNat, getRewardAccruedReturnNat]
                                exact lt_of_le_of_lt (Nat.div_le_self _ _) hscaled
                              have hOwedNatLt :
                                  getRewardOwedOwedNat evmAcc I accruedNat < UInt256.size := by
                                simpa [getRewardOwedOwedNat, hclaimedLoadEvm] using
                                  getRewardOwedOwedNat_lt claimedE haccruedNatLt
                              have hOwedWord :
                                  getRewardOwedReturnOwedWord claimedE
                                      (UInt256.ofNat accruedNat) =
                                    UInt256.ofNat
                                      (getRewardOwedOwedNat evmAcc I accruedNat) := by
                                rw [getRewardOwedReturnOwedWord_of_ofNat claimedE haccruedNatLt]
                                simp [getRewardOwedOwedNat, hclaimedLoadEvm]
                              exact hret.reEquivExecutionGenAccountMapEquiv
                                hcode hd hdec hbody rfl hBaseAccounts
                                (returnEquiv.returned rfl (by
                                  have henc :=
                                    getRewardOwedEncodeReturnValue_tuple
                                      (getRewardOwedSlot0Load evmSolm I)
                                      (UInt256.ofNat (getRewardOwedOwedNat evmAcc I accruedNat))
                                  rw [UInt256.toNat_ofNat_of_lt hOwedNatLt] at henc
                                  simpa [getRewardOwedTransition, hslotLoadEvm, slotE, claimedE,
                                    baseAccrued, downNat, accruedNat, hOwedWord] using henc))
                            · have hinner :
                                  ExecFuncBody config
                                    { contract := contract,
                                      locals := getRewardAccruedStore I
                                        (getRewardOwedSlot0Load evmSolm I)
                                        (getRewardOwedMultiplierLoad evmSolm I) }
                                    evmAcc getRewardAccruedFunction.body .reverted := by
                                exact getRewardAccruedBodyReverts_downscale_scaledOverflow
                                  evmAcc evmBase I
                                  (getRewardOwedSlot0Load evmSolm I)
                                  (getRewardOwedMultiplierLoad evmSolm I)
                                  baseAccrued
                                  (by simpa [evmAcc, evmBase] using hcallBaseSolm)
                                  hdecBase
                                  (by simpa [hslotLoadEvm] using hshouldZero)
                                  (by simpa [hslotLoadEvm] using hrescaleZero)
                                  (by
                                    rw [hslotLoadEvm, hmulLoadEvm]
                                    simpa [downNat] using Nat.le_of_not_gt hscaled)
                              have hbody :
                                  ExecTransitionBody config contract evmSolm
                                    (getRewardOwedStore I)
                                    getRewardOwedTransition.body .reverted := by
                                exact cometRewardsGetRewardOwedBodyReverts_getRewardAccrued
                                  evmSolm evmAcc I
                                  (by simp only [evmSolm, initState]; exact hwv)
                                  (by simp only [evmSolm, initState]; exact hhi)
                                  htokenNZSolm hguard
                                  (by simpa [evmAcc] using hcallSolm)
                                  hdecAccrue hinner
                              have hrev :
                                  RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                                exact
                                  cometRewardsGetRewardOwedX_getRewardAccrued_downscale_overflow_revert
                                    (slot0 := slotE) (multiplier := mulE)
                                    rd3740 houtSize hbase32 hbaseOutSize
                                    (by simpa [baseAccrued] using hbase64)
                                    hshouldZero hrescaleZero (Nat.le_of_not_gt hscaled)
                              exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                      · have hdecBase :=
                          cometRewardsBaseTrackingAccrued_decode_none_noncanon
                            (out := baseOut) hbase32 hbaseOutHi hbaseWord
                        have hinner :
                            ExecFuncBody config
                              { contract := contract,
                                locals := getRewardAccruedStore I
                                  (getRewardOwedSlot0Load evmSolm I)
                                  (getRewardOwedMultiplierLoad evmSolm I) }
                              evmAcc getRewardAccruedFunction.body .reverted := by
                          exact getRewardAccruedBodyReverts_decode evmAcc evmBase I
                            (getRewardOwedSlot0Load evmSolm I)
                            (getRewardOwedMultiplierLoad evmSolm I)
                            (by simpa [evmAcc, evmBase] using hcallBaseSolm)
                            hdecBase
                        have hbody :
                            ExecTransitionBody config contract evmSolm (getRewardOwedStore I)
                              getRewardOwedTransition.body .reverted := by
                          exact cometRewardsGetRewardOwedBodyReverts_getRewardAccrued
                            evmSolm evmAcc I
                            (by simp only [evmSolm, initState]; exact hwv)
                            (by simp only [evmSolm, initState]; exact hhi)
                            htokenNZSolm hguard
                            (by simpa [evmAcc] using hcallSolm)
                            hdecAccrue hinner
                        have hbaseNo :
                            ¬ (getRewardOwedBaseTrackingReturnWord baseOut).toNat <
                              EVM.twoPow 64 := by
                          intro hlt
                          have hto :
                              (getRewardOwedBaseTrackingReturnWord baseOut).toNat =
                                fromByteArrayBigEndian (baseOut.extract 0 32) := by
                            simpa [getRewardOwedBaseTrackingReturnWord] using
                              UInt256.toNat_ofNat_of_lt
                                (fromByteArrayBigEndian_extract0_32_lt hbase32)
                          exact hbaseWord (by rw [← hto]; exact hlt)
                        have hrev :
                            RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
                              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                          exact
                            cometRewardsGetRewardOwedX_after_baseTracking_noncanon_revert
                              (slot0 := getRewardOwedRewardConfigSlot0Word σ_evm I)
                              (multiplier := getRewardOwedMultiplierWord σ_evm I)
                              rdBasePost houtSize hbase32 hbaseOutSize hbaseNo
                        exact hrev.reEquivExecutionRevert hcode hd hdec hbody
              · have hdepth1024 : I.depth = 1024 :=
                  Fin.ext (by
                    have hlt := I.depth.isLt
                    have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hdepth
                    omega)
                let evmInit : EVM.State :=
                  initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                let evmFail : EVM.State :=
                  { evmInit with
                      substate :=
                        (evmInit.addAccessedAccount
                          (EVM.address (getRewardOwedCometTarget I))).substate }
                have hcallS :
                    typedCallViaEVM config evmInit
                      (EVM.address (getRewardOwedCometTarget I)) "accrueAccount" 0
                      (getRewardOwedAccrueAccountArgs I)
                      (false, evmFail, ByteArray.empty) true := by
                  exact callNotMade_depthLimit
                    (cfg := config) (evm := evmInit)
                    (tgt := EVM.address (getRewardOwedCometTarget I))
                    (name := "accrueAccount") (args := getRewardOwedAccrueAccountArgs I)
                    (calldata :=
                      (getRewardOwedAccrueAccountCalldataMem I
                        (getRewardOwedRewardConfigSlot0Word σ_solm I)
                        (getRewardOwedMultiplierWord σ_solm I)).readWithPadding
                          320 getRewardOwedAccrueAccountCallSize.toNat)
                    (callPerm := true)
                    (getRewardOwedAccrueAccountCalldataMem_encode_args I
                      (getRewardOwedRewardConfigSlot0Word σ_solm I)
                      (getRewardOwedMultiplierWord σ_solm I) hcanonAccount)
                    (by simpa [evmInit, initState] using hdepth1024)
                have hbody :
                    ExecTransitionBody config contract
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      (getRewardOwedStore I)
                      getRewardOwedTransition.body .reverted := by
                  exact cometRewardsGetRewardOwedBodyReverts_accrueFailure
                    evmInit evmFail I
                    (by simp only [evmInit, initState]; exact hwv)
                    (by simp only [evmInit, evmSolm]; exact hhi)
                    (by simpa [evmInit, evmSolm] using htokenNZSolm)
                    (by simpa [evmInit, evmSolm] using hguard)
                    hcallS
                exact (cometRewardsGetRewardOwedX_callDepthLimit
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g)
                    hwv hsz68 hsize hhi hcanonComet hcanonAccount htokenZero hnoCode
                    hreach hdepth1024)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hdec := cometRewardsDecode_getRewardOwed_none_noncanon_account
            (I := I) hsz68 hhi hcanonComet hcanonAccount
          have hnc : UInt256.eq (getRewardOwedAccountWord I)
              (UInt256.land (getRewardOwedAccountWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne
              (fun he => hcanonAccount (solcAddrCanonical_of_clean he))
          exact (cometRewardsGetRewardOwedX_noncanon_account (g := Sat256.ofUInt256 g)
              hwv hsz68 hsize hhi hcanonComet hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := cometRewardsDecode_getRewardOwed_none_noncanon_comet
          (I := I) hsz68 hhi hcanonComet
        have hnc : UInt256.eq (getRewardOwedCometWord I)
            (UInt256.land (getRewardOwedCometWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne
            (fun he => hcanonComet (solcAddrCanonical_of_clean he))
        exact (cometRewardsGetRewardOwedX_noncanon_comet (g := Sat256.ofUInt256 g)
            hwv hsz68 hsize hhi hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := cometRewardsDecode_getRewardOwed_none_huge (I := I) hbig
      exact (cometRewardsGetRewardOwedX_hugearg (g := Sat256.ofUInt256 g)
          hwv hsize hbig hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := cometRewardsDecode_getRewardOwed_none_short (I := I) hsz4 hshort
    exact (cometRewardsGetRewardOwedX_shortarg (g := Sat256.ofUInt256 g)
        hwv hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.CompoundIII.CometRewards
