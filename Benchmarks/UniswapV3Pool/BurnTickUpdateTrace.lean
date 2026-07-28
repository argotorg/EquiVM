import Benchmarks.UniswapV3Pool.BurnTickUpdateSource

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

abbrev burnTickUpdateLowerKeyWord (tickLower : UInt256) : UInt256 :=
  UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ tickLower)

abbrev burnTickUpdateLowerBaseSlotWord (tickLower : UInt256) : UInt256 :=
  solcMappingSlot ⟨5⟩ (burnTickUpdateLowerKeyWord tickLower)

abbrev burnTickUpdateLowerLoadedWord (σ : AccountMap) (ee : ExecutionEnv)
    (tickLower : UInt256) : UInt256 :=
  solcSlotWord σ ee (burnTickUpdateLowerBaseSlotWord tickLower)

abbrev burnTickUpdateLowerLiquidityGrossBeforeWordEvm (σ : AccountMap)
    (ee : ExecutionEnv) (tickLower : UInt256) : UInt256 :=
  UInt256.land (burnTickUpdateLowerLoadedWord σ ee tickLower) uint128Mask

noncomputable abbrev burnTickUpdateLowerHashMem
    (tickLower : UInt256) (mem : ByteArray) : ByteArray :=
  twoWordHashMem (burnTickUpdateLowerKeyWord tickLower) ⟨5⟩ mem

theorem burnTickUpdateLowerBaseSlotWord_eq_getLowerBaseSlot (I : ExecutionEnv) :
    burnTickUpdateLowerBaseSlotWord (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)) =
      burnTickGetLowerBaseSlot I := by
  simp [burnTickUpdateLowerBaseSlotWord, burnTickUpdateLowerKeyWord,
    burnTickGetLowerBaseSlot, ticksBase, mapSlot, solcMappingSlot,
    keyValueToWord, wordOfInt_sint24Value_eq_signextend_two,
    signextend_two_tickSpacing_idempotent]

theorem burnTickUpdateLowerLiquidityGrossBeforeWord_transport
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    burnTickUpdateLowerLiquidityGrossBeforeWord σ_solm I =
      burnTickUpdateLowerLiquidityGrossBeforeWordEvm σ_evm I
        (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)) := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner
    (burnTickGetLowerBaseSlot I) (⟨0⟩ : UInt256)
  dsimp [burnTickUpdateLowerLiquidityGrossBeforeWord,
    burnTickUpdateLowerLiquidityGrossBeforeWordEvm, burnTickUpdateLowerLoadedWord,
    solcSlotWord]
  rw [burnTickUpdateLowerBaseSlotWord_eq_getLowerBaseSlot]
  rw [← hslot]

theorem u256_zero_sub_zero_sub {w : UInt256} (hnonzero : w ≠ ⟨0⟩) :
    UInt256.sub ⟨0⟩ (UInt256.sub ⟨0⟩ w) = w := by
  apply u256_inj
  have htoNatNe : w.toNat ≠ 0 := by
    intro h
    exact hnonzero (uint256_toNat_eq_zero h)
  have hpos : 0 < w.toNat := Nat.pos_of_ne_zero htoNatNe
  have hsub : (UInt256.sub (⟨0⟩ : UInt256) w).toNat = UInt256.size - w.toNat := by
    simpa using usub_toNat_underflow (a := (⟨0⟩ : UInt256)) (b := w) hpos
  have hsubPos : 0 < (UInt256.sub (⟨0⟩ : UInt256) w).toNat := by
    rw [hsub]
    have hwlt : w.toNat < UInt256.size := w.val.isLt
    omega
  have hsub2 := usub_toNat_underflow (a := (⟨0⟩ : UInt256))
    (b := UInt256.sub (⟨0⟩ : UInt256) w) hsubPos
  rw [hsub2, hsub]
  change UInt256.size - (UInt256.size - w.toNat) = w.toNat
  have hwlt : w.toNat < UInt256.size := w.val.isLt
  omega

theorem signextend_fifteen_zero_sub_eq_of_lt {w : UInt256}
    (hnonzero : w ≠ ⟨0⟩) (hlt : w.toNat < EVM.twoPow 127) :
    UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ w) = UInt256.sub ⟨0⟩ w := by
  have htoNatNe : w.toNat ≠ 0 := by
    intro h
    exact hnonzero (uint256_toNat_eq_zero h)
  have hpos : 0 < w.toNat := Nat.pos_of_ne_zero htoNatNe
  have hsubNat : (UInt256.sub (⟨0⟩ : UInt256) w).toNat = UInt256.size - w.toNat := by
    simpa using usub_toNat_underflow (a := (⟨0⟩ : UInt256)) (b := w) hpos
  have hposInt : (0 : Int) < (w.toNat : Int) := by exact_mod_cast hpos
  have hneg : -(Int.ofNat w.toNat) < 0 := by
    have : (0 : Int) < Int.ofNat w.toNat := by simpa using hposInt
    omega
  have habs : (-(Int.ofNat w.toNat)).natAbs = w.toNat := by
    rw [Int.natAbs_neg]
    simp
  have hword : UInt256.sub (⟨0⟩ : UInt256) w =
      EVM.wordOfInt (-(Int.ofNat w.toNat)) := by
    apply u256_inj
    rw [hsubNat]
    have hltWord : (-(Int.ofNat w.toNat)).natAbs < EVM.wordModulus := by
      rw [habs]
      rw [show EVM.wordModulus = UInt256.size by native_decide]
      exact w.val.isLt
    rw [wordOfInt_neg_toNat_lt_wordModulus _ hneg hltWord]
    rw [habs]
  rw [hword]
  exact signextend_fifteen_wordOfInt_ticks (-(Int.ofNat w.toNat))
    (by
      norm_num [EVM.twoPow] at hlt ⊢
      omega)
    (by
      norm_num [EVM.twoPow] at hlt ⊢
      omega)

theorem u256_zero_sub_signextend_fifteen_zero_sub {w : UInt256}
    (hnonzero : w ≠ ⟨0⟩) (hlt : w.toNat < EVM.twoPow 127) :
    UInt256.sub ⟨0⟩ (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ w)) = w := by
  rw [signextend_fifteen_zero_sub_eq_of_lt hnonzero hlt]
  exact u256_zero_sub_zero_sub hnonzero

theorem liquidityAddDeltaWrappedSub_lt_iff {x a : Nat}
    (hx : x < 2 ^ (128 : Nat)) (ha0 : 0 < a) (ha : a < 2 ^ (128 : Nat)) :
    liquidityAddDeltaWrappedSub (Int.ofNat x) (0 - Int.ofNat a) < Int.ofNat x ↔
      a ≤ x := by
  unfold liquidityAddDeltaWrappedSub
  have hsimp :
      Int.ofNat x - (0 - (0 - Int.ofNat a)) = Int.ofNat x - Int.ofNat a := by
    ring
  rw [hsimp]
  by_cases hle : a ≤ x
  · have hleInt : Int.ofNat a ≤ Int.ofNat x := Int.ofNat_le.mpr hle
    have hnonneg : 0 ≤ Int.ofNat x - Int.ofNat a := by omega
    have hltm : Int.ofNat x - Int.ofNat a < (2 ^ (128 : Nat) : Int) := by
      have hxInt : Int.ofNat x < (2 ^ (128 : Nat) : Int) := Int.ofNat_lt.mpr hx
      have haNonneg : (0 : Int) ≤ Int.ofNat a := Int.natCast_nonneg a
      omega
    rw [Int.emod_eq_of_lt hnonneg hltm]
    constructor
    · intro _
      exact hle
    · intro _
      have haPosInt : (0 : Int) < Int.ofNat a := Int.ofNat_lt.mpr ha0
      omega
  · have hgt : x < a := Nat.lt_of_not_ge hle
    let m : Int := (2 ^ (128 : Nat) : Int)
    have hmodrewrite : (Int.ofNat x - Int.ofNat a) % m =
        (Int.ofNat x - Int.ofNat a + 1 * m) % m := by
      rw [Int.add_mul_emod_self_right]
    rw [hmodrewrite]
    have hnonneg : 0 ≤ Int.ofNat x - Int.ofNat a + 1 * m := by
      dsimp [m]
      have hxNonneg : (0 : Int) ≤ Int.ofNat x := Int.natCast_nonneg x
      have haLtInt : Int.ofNat a < (2 ^ (128 : Nat) : Int) := Int.ofNat_lt.mpr ha
      omega
    have hltm : Int.ofNat x - Int.ofNat a + 1 * m < m := by
      dsimp [m]
      have hgtInt : Int.ofNat x < Int.ofNat a := Int.ofNat_lt.mpr hgt
      omega
    rw [Int.emod_eq_of_lt hnonneg hltm]
    constructor
    · intro hlt
      dsimp [m] at hlt
      have haLtInt : Int.ofNat a < (2 ^ (128 : Nat) : Int) := Int.ofNat_lt.mpr ha
      omega
    · intro hle'
      exact False.elim (hle hle')

theorem liquidityAddDeltaWrappedSub_eq_of_le {x a : Nat}
    (hx : x < 2 ^ (128 : Nat)) (hle : a ≤ x) :
    liquidityAddDeltaWrappedSub (Int.ofNat x) (0 - Int.ofNat a) =
      Int.ofNat (x - a) := by
  unfold liquidityAddDeltaWrappedSub
  have hsimp :
      Int.ofNat x - (0 - (0 - Int.ofNat a)) = Int.ofNat x - Int.ofNat a := by
    ring
  rw [hsimp]
  have hnonneg : 0 ≤ Int.ofNat x - Int.ofNat a := by
    exact sub_nonneg.mpr (Int.ofNat_le.mpr hle)
  have hltm : Int.ofNat x - Int.ofNat a < (2 ^ (128 : Nat) : Int) := by
    have hxInt : Int.ofNat x < (2 ^ (128 : Nat) : Int) := Int.ofNat_lt.mpr hx
    have haNonneg : (0 : Int) ≤ Int.ofNat a := Int.natCast_nonneg a
    omega
  rw [Int.emod_eq_of_lt hnonneg hltm]
  exact (Int.ofNat_sub hle).symm

theorem uint128Mask_toNat_eq_mod (w : UInt256) :
    (UInt256.land w uint128Mask).toNat = w.toNat % 2 ^ (128 : Nat) := by
  rw [uland_toNat, uint128Mask_toNat]
  change w.toNat.land (2 ^ (128 : Nat) - 1) = w.toNat % 2 ^ (128 : Nat)
  exact nat_land_mask_eq_mod w.toNat 128

theorem uint128Mask_underflow_sub_toNat {x a : UInt256}
    (hx : x.toNat < 2 ^ (128 : Nat)) (hgt : x.toNat < a.toNat)
    (ha : a.toNat < 2 ^ (128 : Nat)) :
    (UInt256.land (UInt256.sub x a) uint128Mask).toNat =
      2 ^ (128 : Nat) + x.toNat - a.toNat := by
  have hsub := usub_toNat_underflow (a := x) (b := a) hgt
  rw [uint128Mask_toNat_eq_mod, hsub]
  have hremLt : 2 ^ (128 : Nat) + x.toNat - a.toNat < 2 ^ (128 : Nat) := by
    omega
  have hrewrite : UInt256.size + x.toNat - a.toNat =
      (2 ^ (128 : Nat) - 1) * 2 ^ (128 : Nat) +
        (2 ^ (128 : Nat) + x.toNat - a.toNat) := by
    norm_num [UInt256.size]
    omega
  rw [hrewrite]
  rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hremLt]

theorem evmUint128SubLtCheck_iff {x a : UInt256}
    (hx : x.toNat < 2 ^ (128 : Nat)) (ha0 : 0 < a.toNat)
    (ha : a.toNat < 2 ^ (128 : Nat)) :
    UInt256.lt (UInt256.land uint128Mask (UInt256.sub x a))
        (UInt256.land uint128Mask x) ≠ ⟨0⟩ ↔
      a.toNat ≤ x.toNat := by
  rw [u256_land_comm uint128Mask (UInt256.sub x a),
    u256_land_comm uint128Mask x, uint128Mask_clean hx]
  by_cases hle : a.toNat ≤ x.toNat
  · have hsub := usub_toNat (a := x) (b := a) hle
    have hsubLt128 : (UInt256.sub x a).toNat < 2 ^ (128 : Nat) := by
      rw [hsub]
      omega
    rw [uint128Mask_clean hsubLt128]
    have hltWords : (UInt256.sub x a).toNat < x.toNat := by
      rw [hsub]
      omega
    rw [ult_one hltWords]
    constructor
    · intro _
      exact hle
    · intro _
      native_decide
  · have hgt : x.toNat < a.toNat := Nat.lt_of_not_ge hle
    have hleft := uint128Mask_underflow_sub_toNat (x := x) (a := a) hx hgt ha
    have hnotLt : x.toNat ≤ (UInt256.land (UInt256.sub x a) uint128Mask).toNat := by
      rw [hleft]
      omega
    rw [ult_zero hnotLt]
    constructor
    · intro hneq
      exact False.elim (hneq rfl)
    · intro hle'
      exact False.elim (hle hle')

theorem burnTickUpdateLowerLiquidityAddDeltaEvmCheck_iff
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcanon : UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩) :
    (burnTickUpdateLowerLiquidityGrossAfterSubInt σ_solm I <
        burnTickUpdateLowerLiquidityGrossBeforeInt σ_solm I) ↔
      UInt256.lt
        (UInt256.land uint128Mask
          (UInt256.sub
            (burnTickUpdateLowerLiquidityGrossBeforeWordEvm σ_evm I
              (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))
            (UInt256.sub ⟨0⟩
              (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))))))
        (UInt256.land uint128Mask
          (burnTickUpdateLowerLiquidityGrossBeforeWordEvm σ_evm I
            (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))) ≠ ⟨0⟩ := by
  let amount := burnAmountCleanWord I
  let x := burnTickUpdateLowerLiquidityGrossBeforeWordEvm σ_evm I
    (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
  have hamountPos : 0 < amount.toNat := by
    have htoNatNe : amount.toNat ≠ 0 := by
      intro h
      exact hnonzero (uint256_toNat_eq_zero h)
    exact Nat.pos_of_ne_zero htoNatNe
  have hamountLt128 : amount.toNat < 2 ^ (128 : Nat) := by
    simpa [amount, burnAmountCleanWord, EVM.twoPow] using
      uint128Mask_bound (burnAmountWord I)
  have hamountLt127 : amount.toNat < EVM.twoPow 127 :=
    signextend_fifteen_eq_self_toNat_lt_twoPow127
      (by simpa [amount, burnAmountCleanWord] using uint128Mask_bound (burnAmountWord I))
      (by simpa [amount] using hcanon)
  have hcancel :
      UInt256.sub ⟨0⟩ (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ amount)) =
        amount :=
    u256_zero_sub_signextend_fifteen_zero_sub (w := amount) hnonzero hamountLt127
  have hx : x.toNat < 2 ^ (128 : Nat) := by
    simpa [x, EVM.twoPow] using
      uint128Mask_bound (burnTickUpdateLowerLoadedWord σ_evm I
        (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))
  have htransport := burnTickUpdateLowerLiquidityGrossBeforeWord_transport
    (σ_evm := σ_evm) (σ_solm := σ_solm) (I := I) hAccounts
  have hsource :
      (burnTickUpdateLowerLiquidityGrossAfterSubInt σ_solm I <
          burnTickUpdateLowerLiquidityGrossBeforeInt σ_solm I) ↔
        amount.toNat ≤ x.toNat := by
    simpa [burnTickUpdateLowerLiquidityGrossAfterSubInt,
      burnTickUpdateLowerLiquidityGrossBeforeInt, burnTickUpdateLowerLiquidityDeltaInt,
      amount, x, htransport] using
      liquidityAddDeltaWrappedSub_lt_iff (x := x.toNat) (a := amount.toNat)
        hx hamountPos hamountLt128
  have hevm :
      UInt256.lt (UInt256.land uint128Mask (UInt256.sub x amount))
          (UInt256.land uint128Mask x) ≠ ⟨0⟩ ↔
        amount.toNat ≤ x.toNat :=
    evmUint128SubLtCheck_iff (x := x) (a := amount) hx hamountPos hamountLt128
  refine hsource.trans ?_
  simpa [x, amount, hcancel] using hevm.symm

theorem burnTickUpdateLowerMaxLiquidityEvmCheck_of_source
    {v : PoolImmutables} {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcanon : UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hdelta :
      burnTickUpdateLowerLiquidityGrossAfterSubInt σ_solm I <
        burnTickUpdateLowerLiquidityGrossBeforeInt σ_solm I)
    (hmax :
      ¬ burnTickUpdateLowerLiquidityGrossAfterSubInt σ_solm I <= v.maxLiquidityPerTick) :
    UInt256.gt
        (UInt256.land uint128Mask
          (UInt256.sub
            (burnTickUpdateLowerLiquidityGrossBeforeWordEvm σ_evm I
              (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))
            (UInt256.sub ⟨0⟩
              (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))))))
        (UInt256.land uint128Mask (EVM.wordOfInt v.maxLiquidityPerTick)) ≠ ⟨0⟩ := by
  let amount := burnAmountCleanWord I
  let x := burnTickUpdateLowerLiquidityGrossBeforeWordEvm σ_evm I
    (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
  let z := UInt256.sub x
    (UInt256.sub ⟨0⟩ (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ amount)))
  have hamountPos : 0 < amount.toNat := by
    have htoNatNe : amount.toNat ≠ 0 := by
      intro h
      exact hnonzero (uint256_toNat_eq_zero h)
    exact Nat.pos_of_ne_zero htoNatNe
  have hamountLt128 : amount.toNat < 2 ^ (128 : Nat) := by
    simpa [amount, burnAmountCleanWord, EVM.twoPow] using
      uint128Mask_bound (burnAmountWord I)
  have hamountLt127 : amount.toNat < EVM.twoPow 127 :=
    signextend_fifteen_eq_self_toNat_lt_twoPow127
      (by simpa [amount, burnAmountCleanWord] using uint128Mask_bound (burnAmountWord I))
      (by simpa [amount] using hcanon)
  have hcancel :
      UInt256.sub ⟨0⟩ (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ amount)) =
        amount :=
    u256_zero_sub_signextend_fifteen_zero_sub (w := amount) hnonzero hamountLt127
  have hx : x.toNat < 2 ^ (128 : Nat) := by
    simpa [x, EVM.twoPow] using
      uint128Mask_bound (burnTickUpdateLowerLoadedWord σ_evm I
        (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)))
  have htransport := burnTickUpdateLowerLiquidityGrossBeforeWord_transport
    (σ_evm := σ_evm) (σ_solm := σ_solm) (I := I) hAccounts
  have hsource :
      (burnTickUpdateLowerLiquidityGrossAfterSubInt σ_solm I <
          burnTickUpdateLowerLiquidityGrossBeforeInt σ_solm I) ↔
        amount.toNat ≤ x.toNat := by
    simpa [burnTickUpdateLowerLiquidityGrossAfterSubInt,
      burnTickUpdateLowerLiquidityGrossBeforeInt, burnTickUpdateLowerLiquidityDeltaInt,
      amount, x, htransport] using
      liquidityAddDeltaWrappedSub_lt_iff (x := x.toNat) (a := amount.toNat)
        hx hamountPos hamountLt128
  have hleAmount : amount.toNat ≤ x.toNat := hsource.mp hdelta
  have hzToNat : z.toNat = x.toNat - amount.toNat := by
    dsimp [z]
    rw [hcancel]
    exact usub_toNat (a := x) (b := amount) hleAmount
  have hafterEq :
      burnTickUpdateLowerLiquidityGrossAfterSubInt σ_solm I =
        Int.ofNat (x.toNat - amount.toNat) := by
    simpa [burnTickUpdateLowerLiquidityGrossAfterSubInt,
      burnTickUpdateLowerLiquidityGrossBeforeInt, burnTickUpdateLowerLiquidityDeltaInt,
      amount, x, htransport] using
      liquidityAddDeltaWrappedSub_eq_of_le (x := x.toNat) (a := amount.toNat) hx hleAmount
  have hafterWord :
      burnTickUpdateLowerLiquidityGrossAfterSubInt σ_solm I = Int.ofNat z.toNat := by
    rw [hafterEq, hzToNat]
  have hzLt128 : z.toNat < EVM.twoPow 128 := by
    rw [hzToNat]
    norm_num [EVM.twoPow] at hx ⊢
    omega
  have hzClean : UInt256.land uint128Mask z = z := uint128Mask_clean_left hzLt128
  have hmaxWordNat :
      (EVM.wordOfInt v.maxLiquidityPerTick).toNat = v.maxLiquidityPerTick.toNat := by
    exact wordOfInt_nonneg_toNat_lt_wordModulus v.maxLiquidityPerTick
      v.maxLiquidityPerTick_nonneg
      (by
        exact lt_trans v.maxLiquidityPerTick_lt
          (by native_decide : (2 ^ (128 : Nat) : Int) < EVM.wordModulus))
  have hmaxWordLt128 :
      (EVM.wordOfInt v.maxLiquidityPerTick).toNat < EVM.twoPow 128 := by
    rw [hmaxWordNat]
    exact (Int.toNat_lt v.maxLiquidityPerTick_nonneg).2
      (by simpa [EVM.twoPow] using v.maxLiquidityPerTick_lt)
  have hmaxClean :
      UInt256.land uint128Mask (EVM.wordOfInt v.maxLiquidityPerTick) =
        EVM.wordOfInt v.maxLiquidityPerTick :=
    uint128Mask_clean_left hmaxWordLt128
  have hmaxLtAfter :
      v.maxLiquidityPerTick < Int.ofNat z.toNat := by
    have hmaxLt :
        v.maxLiquidityPerTick < burnTickUpdateLowerLiquidityGrossAfterSubInt σ_solm I := by
      omega
    simpa [hafterWord] using hmaxLt
  have hmaxNatLt :
      (EVM.wordOfInt v.maxLiquidityPerTick).toNat < z.toNat := by
    rw [hmaxWordNat]
    exact (Int.toNat_lt v.maxLiquidityPerTick_nonneg).2 hmaxLtAfter
  have hgt :
      UInt256.gt z (EVM.wordOfInt v.maxLiquidityPerTick) = ⟨1⟩ :=
    ugt_one hmaxNatLt
  have hgtNe :
      UInt256.gt z (EVM.wordOfInt v.maxLiquidityPerTick) ≠ ⟨0⟩ := by
    rw [hgt]
    decide
  simpa [z, x, amount, hzClean, hmaxClean] using hgtNe

private theorem uniswapV3PoolBurnTickUpdatePatchDisjoint {v : PoolImmutables}
    {pc : UInt256} {n : Nat} (hlo : 20795 ≤ pc.toNat)
    (_hhi : pc.toNat + n ≤ 21285) :
    ∀ p ∈ patches v, pc.toNat + n ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
    List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolBurnTickUpdateDecodeEqTemplate {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 20795 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21285) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 21285 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (uniswapV3PoolBurnTickUpdatePatchDisjoint (v := v) (pc := pc) hlo hhi)

private theorem uniswapV3PoolBurnTickUpdatePatchPreservesJumpDest13807 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨13807⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolBurnJumpDestPatched13807 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨13807⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolBurnTickUpdatePatchPreservesJumpDest13807

private theorem uniswapV3PoolBurnTickUpdatePatchPreservesJumpDest20838 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨20838⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolBurnJumpDestPatched20838 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨20838⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolBurnTickUpdatePatchPreservesJumpDest20838

theorem uniswapV3PoolBurnTickUpdateLowerToLiquidityAddDelta
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {maxLiquidity zero time tick seconds feeGrowthGlobal1 feeGrowthGlobal0
      liquidityDelta slot0Tick tickLower retPc z2 z3 positionBase tickUpper source : UInt256}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨20795⟩
      (maxLiquidity :: zero :: time :: tick :: seconds :: feeGrowthGlobal1 ::
        feeGrowthGlobal0 :: liquidityDelta :: slot0Tick :: tickLower :: ⟨5⟩ ::
        retPc :: seconds :: tick :: time :: z2 :: z3 :: feeGrowthGlobal1 ::
        feeGrowthGlobal0 :: positionBase :: slot0Tick :: liquidityDelta ::
        tickUpper :: tickLower :: source :: R)
      mem (UInt256.ofNat 21) rdata (cA, σ) k C)
    (hmem : 64 ≤ mem.size)
    (hov : R.length + 55 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨13807⟩
      (liquidityDelta ::
        burnTickUpdateLowerLiquidityGrossBeforeWordEvm σ ee tickLower ::
        ⟨20838⟩ :: ⟨0⟩ ::
        burnTickUpdateLowerLiquidityGrossBeforeWordEvm σ ee tickLower ::
        burnTickUpdateLowerBaseSlotWord tickLower :: ⟨0⟩ :: maxLiquidity :: zero ::
        time :: tick :: seconds :: feeGrowthGlobal1 :: feeGrowthGlobal0 ::
        liquidityDelta :: slot0Tick :: tickLower :: ⟨5⟩ :: retPc :: seconds ::
        tick :: time :: z2 :: z3 :: feeGrowthGlobal1 :: feeGrowthGlobal0 ::
        positionBase :: slot0Tick :: liquidityDelta :: tickUpper :: tickLower :: source :: R)
      (burnTickUpdateLowerHashMem tickLower mem) (UInt256.ofNat 21) rdata
      (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 20795 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21285) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnTickUpdateDecodeEqTemplate hpatch hlo hhi
  have rd20796 := by
    simpa using h.jumpdest
      (by rw [hdec ⟨20795⟩ (by native_decide) (by native_decide)]; native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd20798 := evm_run rd20796 with [
    raw push1 ⟨2⟩ (by
      change decode code ⟨20796⟩ = some (.Push .PUSH1, some (⟨2⟩, 1))
      rw [hdec ⟨20796⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw dup11 (by
      change decode code ⟨20798⟩ = some (.DUP11, none)
      rw [hdec ⟨20798⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega),
    raw dup2 (by
      change decode code ⟨20799⟩ = some (.DUP2, none)
      rw [hdec ⟨20799⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov)]
  have rd20801 := by
    simpa using RD.signextend rd20798
      (by
        change decode code ⟨20800⟩ = some (.SIGNEXTEND, none)
        rw [hdec ⟨20800⟩ (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd20802 := evm_run rd20801 with [
    raw swap1 (by
      change decode code ⟨20801⟩ = some (.SWAP1, none)
      rw [hdec ⟨20801⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov)]
  have rd20803 := by
    simpa [burnTickUpdateLowerKeyWord] using RD.signextend rd20802
      (by
        change decode code ⟨20802⟩ = some (.SIGNEXTEND, none)
        rw [hdec ⟨20802⟩ (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd20807 := evm_run rd20803 with [
    raw push1 ⟨0⟩ (by
      change decode code ⟨20803⟩ = some (.Push .PUSH1, some (⟨0⟩, 1))
      rw [hdec ⟨20803⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw swap1 (by
      change decode code ⟨20805⟩ = some (.SWAP1, none)
      rw [hdec ⟨20805⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw dup2 (by
      change decode code ⟨20806⟩ = some (.DUP2, none)
      rw [hdec ⟨20806⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov)]
  have rd20808 := rd20807.mstore 0
    (wordAt0Mem (burnTickUpdateLowerKeyWord tickLower) mem) (UInt256.ofNat 21)
    (by
      change decode code ⟨20807⟩ = some (.MSTORE, none)
      rw [hdec ⟨20807⟩ (by native_decide) (by native_decide)]
      native_decide)
    mem_cost (by rfl) (by native_decide) (by simp only [List.length_cons] at hov ⊢; omega)
  have rd20812 := evm_run rd20808 with [
    raw push1 ⟨32⟩ (by
      change decode code ⟨20808⟩ = some (.Push .PUSH1, some (⟨32⟩, 1))
      rw [hdec ⟨20808⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw dup13 (by
      change decode code ⟨20810⟩ = some (.DUP13, none)
      rw [hdec ⟨20810⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega),
    raw swap1 (by
      change decode code ⟨20811⟩ = some (.SWAP1, none)
      rw [hdec ⟨20811⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov)]
  have rd20813 := rd20812.mstore 0 (burnTickUpdateLowerHashMem tickLower mem)
    (UInt256.ofNat 21)
    (by
      change decode code ⟨20812⟩ = some (.MSTORE, none)
      rw [hdec ⟨20812⟩ (by native_decide) (by native_decide)]
      native_decide)
    mem_cost (by rfl) (by native_decide) (by simp only [List.length_cons] at hov ⊢; omega)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((burnTickUpdateLowerHashMem tickLower mem).readWithPadding 0 64))) =
        burnTickUpdateLowerBaseSlotWord tickLower := by
    exact twoWordHashMem_solcMappingSlot_of_size_ge ⟨5⟩
      (burnTickUpdateLowerKeyWord tickLower) hmem
  have rd20817 := evm_run rd20813 with [
    raw push1 ⟨64⟩ (by
      change decode code ⟨20813⟩ = some (.Push .PUSH1, some (⟨64⟩, 1))
      rw [hdec ⟨20813⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw dup2 (by
      change decode code ⟨20815⟩ = some (.DUP2, none)
      rw [hdec ⟨20815⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov)]
  have rd20817Hash := rd20817.keccak256 0 (burnTickUpdateLowerBaseSlotWord tickLower)
    (UInt256.ofNat 21)
    (by
      change decode code ⟨20816⟩ = some (.KECCAK256, none)
      rw [hdec ⟨20816⟩ (by native_decide) (by native_decide)]
      native_decide)
    mem_cost hslot (by native_decide) (by simp only [List.length_cons] at hov ⊢; omega)
  have rd20818 := evm_run rd20817Hash with [
    raw dup1 (by
      change decode code ⟨20817⟩ = some (.DUP1, none)
      rw [hdec ⟨20817⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rd20819Raw⟩ := rd20818.sload
    (by
      change decode code ⟨20818⟩ = some (.SLOAD, none)
      rw [hdec ⟨20818⟩ (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd20819 := by
    simpa [burnTickUpdateLowerLoadedWord, solcSlotWord] using rd20819Raw
  have rd20838 := evm_run rd20819 with [
    raw push1 ⟨1⟩ (by
      change decode code ⟨20819⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
      rw [hdec ⟨20819⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩ (by
      change decode code ⟨20821⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
      rw [hdec ⟨20821⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw push1 ⟨128⟩ (by
      change decode code ⟨20823⟩ = some (.Push .PUSH1, some (⟨128⟩, 1))
      rw [hdec ⟨20823⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw shl (by
      change decode code ⟨20825⟩ = some (.SHL, none)
      rw [hdec ⟨20825⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw sub (by
      change decode code ⟨20826⟩ = some (.SUB, none)
      rw [hdec ⟨20826⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw and (by
      change decode code ⟨20827⟩ = some (.AND, none)
      rw [hdec ⟨20827⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw dup3 (by
      change decode code ⟨20828⟩ = some (.DUP3, none)
      rw [hdec ⟨20828⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw push2 ⟨20838⟩
      (by
        change decode code ⟨20829⟩ = some (.Push .PUSH2, some (⟨20838⟩, 2))
        rw [hdec ⟨20829⟩ (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3 (by
      change decode code ⟨20832⟩ = some (.DUP3, none)
      rw [hdec ⟨20832⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw dup14 (by
      change decode code ⟨20833⟩ = some (.DUP14, none)
      rw [hdec ⟨20833⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega),
    raw push2 ⟨13807⟩
      (by
        change decode code ⟨20834⟩ = some (.Push .PUSH2, some (⟨13807⟩, 2))
        rw [hdec ⟨20834⟩ (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by
    simpa [burnTickUpdateLowerLiquidityGrossBeforeWordEvm, burnTickUpdateLowerLoadedWord,
      solcSlotWord, uint128Mask, u256_land_comm] using
      rd20838.jump
        (by
          change decode code ⟨20837⟩ = some (.JUMP, none)
          rw [hdec ⟨20837⟩ (by native_decide) (by native_decide)]
          native_decide)
        (uniswapV3PoolBurnJumpDestPatched13807 hpatch)
        (by simp only [List.length_cons] at hov ⊢; omega)⟩

private theorem uniswapV3PoolLiquidityAddDeltaPatchDisjoint {v : PoolImmutables}
    {pc : UInt256} {n : Nat} (hlo : 12989 ≤ pc.toNat)
    (hhi : pc.toNat + n ≤ 13940) :
    ∀ p ∈ patches v, pc.toNat + n ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
    List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolLiquidityAddDeltaDecodeEqTemplate {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 12989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13940) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 13940 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (uniswapV3PoolLiquidityAddDeltaPatchDisjoint (v := v) (pc := pc) hlo hhi)

private theorem uniswapV3PoolBurnPatchPreservesJumpDest13903 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨13903⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolBurnJumpDestPatched13903 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨13903⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolBurnPatchPreservesJumpDest13903

private theorem uniswapV3PoolBurnPatchPreservesJumpDest12989 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12989⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolBurnJumpDestPatched12989 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12989⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolBurnPatchPreservesJumpDest12989

abbrev burnTickUpdateLowerRevertFreePtr : UInt256 :=
  burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256)

def burnTickUpdateLowerLiquidityAddDeltaRevertWord : UInt256 :=
  UInt256.shiftLeft (⟨19539⟩ : UInt256) ⟨240⟩

private theorem burnObserveSingleDecodedMem_read64 (σ : AccountMap)
    (I : ExecutionEnv) (obsWord : UInt256) :
    (burnObserveSingleDecodedMem σ I obsWord).readWithPadding 64 32 =
      UInt256.toByteArray burnTickUpdateLowerRevertFreePtr := by
  unfold burnObserveSingleDecodedMem
  rw [writeWord_read_preserved
    (burnObserveSingleDecodedMem3 σ I obsWord)
    (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)).toNat
    64 (burnObserveSingleDecodedInitializedWord obsWord)
    (by rw [burnObserveSingleDecodedMem3_size σ I obsWord]; native_decide)
    (by rw [burnObserveSingleDecodedMem3_size σ I obsWord]; native_decide)]
  unfold burnObserveSingleDecodedMem3
  rw [writeWord_read_preserved
    (burnObserveSingleDecodedMem2 σ I obsWord)
    (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat
    64 (burnObserveSingleDecodedSecondsWord obsWord)
    (by rw [burnObserveSingleDecodedMem2_size σ I obsWord]; native_decide)
    (by rw [burnObserveSingleDecodedMem2_size σ I obsWord]; native_decide)]
  unfold burnObserveSingleDecodedMem2
  rw [writeWord_read_preserved
    (burnObserveSingleDecodedMem1 σ I obsWord)
    (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat
    64 (burnObserveSingleDecodedTickWord obsWord)
    (by rw [burnObserveSingleDecodedMem1_size σ I obsWord]; native_decide)
    (by rw [burnObserveSingleDecodedMem1_size σ I obsWord]; native_decide)]
  unfold burnObserveSingleDecodedMem1
  rw [writeWord_read_preserved
    (burnObserveSingleAllocMem σ I)
    burnPositionKeyNewFreePtrWord.toNat
    64 (burnObserveSingleDecodedBlockWord obsWord)
    (by rw [burnObserveSingleAllocMem_size σ I]; native_decide)
    (by rw [burnObserveSingleAllocMem_size σ I]; native_decide)]
  unfold burnObserveSingleAllocMem
  simpa [burnTickUpdateLowerRevertFreePtr] using
    writeWord_read_back (burnPositionKeyMappingMem σ I) 64
      (burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256))
      (by rw [burnPositionKeyMappingMem_size σ I]; native_decide)

private theorem burnTickUpdateLowerHashMem_size (σ : AccountMap) (I : ExecutionEnv)
    (obsWord tickLower : UInt256) :
    (burnTickUpdateLowerHashMem tickLower (burnObserveSingleDecodedMem σ I obsWord)).size =
      666 := by
  unfold burnTickUpdateLowerHashMem
  rw [twoWordHashMem_size_of_size_ge]
  · exact burnObserveSingleDecodedMem_size σ I obsWord
  · rw [burnObserveSingleDecodedMem_size σ I obsWord]
    omega

private theorem burnTickUpdateLowerHashMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (obsWord tickLower : UInt256) :
    (burnTickUpdateLowerHashMem tickLower
      (burnObserveSingleDecodedMem σ I obsWord)).readWithPadding 64 32 =
      UInt256.toByteArray burnTickUpdateLowerRevertFreePtr := by
  unfold burnTickUpdateLowerHashMem
  rw [twoWordHashMem_read64_of_size_ge]
  · exact burnObserveSingleDecodedMem_read64 σ I obsWord
  · rw [burnObserveSingleDecodedMem_size σ I obsWord]
    omega

private theorem burnTickUpdateLowerHashMem_mload64 (σ : AccountMap) (I : ExecutionEnv)
    (obsWord tickLower : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (burnTickUpdateLowerHashMem tickLower
            (burnObserveSingleDecodedMem σ I obsWord)).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 21 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((burnTickUpdateLowerHashMem tickLower
              (burnObserveSingleDecodedMem σ I obsWord)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      burnTickUpdateLowerRevertFreePtr := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnTickUpdateLowerHashMem tickLower (burnObserveSingleDecodedMem σ I obsWord))
    (aw := UInt256.ofNat 21) (off := ⟨64⟩) (v := burnTickUpdateLowerRevertFreePtr)
    (by rw [burnTickUpdateLowerHashMem_size σ I obsWord tickLower]; native_decide)
    (by native_decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using burnTickUpdateLowerHashMem_read64 σ I obsWord tickLower)

noncomputable abbrev burnTickUpdateLowerLiquidityAddDeltaRevertMem0
    (σ : AccountMap) (I : ExecutionEnv) (obsWord tickLower : UInt256) : ByteArray :=
  writeWord (burnTickUpdateLowerHashMem tickLower (burnObserveSingleDecodedMem σ I obsWord))
    burnTickUpdateLowerRevertFreePtr.toNat solcErrorStringSelector

noncomputable abbrev burnTickUpdateLowerLiquidityAddDeltaRevertMem1
    (σ : AccountMap) (I : ExecutionEnv) (obsWord tickLower : UInt256) : ByteArray :=
  writeWord (burnTickUpdateLowerLiquidityAddDeltaRevertMem0 σ I obsWord tickLower)
    (burnTickUpdateLowerRevertFreePtr + (⟨4⟩ : UInt256)).toNat (⟨32⟩ : UInt256)

noncomputable abbrev burnTickUpdateLowerLiquidityAddDeltaRevertMem2
    (σ : AccountMap) (I : ExecutionEnv) (obsWord tickLower : UInt256) : ByteArray :=
  writeWord (burnTickUpdateLowerLiquidityAddDeltaRevertMem1 σ I obsWord tickLower)
    (burnTickUpdateLowerRevertFreePtr + (⟨36⟩ : UInt256)).toNat (⟨2⟩ : UInt256)

noncomputable abbrev burnTickUpdateLowerLiquidityAddDeltaRevertMem3
    (σ : AccountMap) (I : ExecutionEnv) (obsWord tickLower : UInt256) : ByteArray :=
  writeWord (burnTickUpdateLowerLiquidityAddDeltaRevertMem2 σ I obsWord tickLower)
    (burnTickUpdateLowerRevertFreePtr + (⟨68⟩ : UInt256)).toNat
    burnTickUpdateLowerLiquidityAddDeltaRevertWord

private theorem burnTickUpdateLowerLiquidityAddDeltaRevertMem0_size
    (σ : AccountMap) (I : ExecutionEnv) (obsWord tickLower : UInt256) :
    (burnTickUpdateLowerLiquidityAddDeltaRevertMem0 σ I obsWord tickLower).size = 698 := by
  unfold burnTickUpdateLowerLiquidityAddDeltaRevertMem0 burnTickUpdateLowerRevertFreePtr
  rw [writeWord_size _ _ _
    (by rw [burnTickUpdateLowerHashMem_size σ I obsWord tickLower]; native_decide)]
  rw [burnTickUpdateLowerHashMem_size σ I obsWord tickLower]
  native_decide

private theorem burnTickUpdateLowerLiquidityAddDeltaRevertMem1_size
    (σ : AccountMap) (I : ExecutionEnv) (obsWord tickLower : UInt256) :
    (burnTickUpdateLowerLiquidityAddDeltaRevertMem1 σ I obsWord tickLower).size = 702 := by
  unfold burnTickUpdateLowerLiquidityAddDeltaRevertMem1 burnTickUpdateLowerRevertFreePtr
  rw [writeWord_size _ _ _
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem0_size σ I obsWord tickLower]
      native_decide)]
  rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem0_size σ I obsWord tickLower]
  native_decide

private theorem burnTickUpdateLowerLiquidityAddDeltaRevertMem2_size
    (σ : AccountMap) (I : ExecutionEnv) (obsWord tickLower : UInt256) :
    (burnTickUpdateLowerLiquidityAddDeltaRevertMem2 σ I obsWord tickLower).size = 734 := by
  unfold burnTickUpdateLowerLiquidityAddDeltaRevertMem2 burnTickUpdateLowerRevertFreePtr
  rw [writeWord_size _ _ _
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem1_size σ I obsWord tickLower]
      native_decide)]
  rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem1_size σ I obsWord tickLower]
  native_decide

private theorem burnTickUpdateLowerLiquidityAddDeltaRevertMem3_size
    (σ : AccountMap) (I : ExecutionEnv) (obsWord tickLower : UInt256) :
    (burnTickUpdateLowerLiquidityAddDeltaRevertMem3 σ I obsWord tickLower).size = 766 := by
  unfold burnTickUpdateLowerLiquidityAddDeltaRevertMem3 burnTickUpdateLowerRevertFreePtr
  rw [writeWord_size _ _ _
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem2_size σ I obsWord tickLower]
      native_decide)]
  rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem2_size σ I obsWord tickLower]
  native_decide

private theorem burnTickUpdateLowerLiquidityAddDeltaRevertMem3_read64
    (σ : AccountMap) (I : ExecutionEnv) (obsWord tickLower : UInt256) :
    (burnTickUpdateLowerLiquidityAddDeltaRevertMem3 σ I obsWord tickLower).readWithPadding
        64 32 =
      UInt256.toByteArray burnTickUpdateLowerRevertFreePtr := by
  unfold burnTickUpdateLowerLiquidityAddDeltaRevertMem3
  rw [writeWord_read_preserved
    (burnTickUpdateLowerLiquidityAddDeltaRevertMem2 σ I obsWord tickLower)
    (burnTickUpdateLowerRevertFreePtr + (⟨68⟩ : UInt256)).toNat
    64 burnTickUpdateLowerLiquidityAddDeltaRevertWord
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem2_size σ I obsWord tickLower]
      native_decide)
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem2_size σ I obsWord tickLower]
      native_decide)]
  unfold burnTickUpdateLowerLiquidityAddDeltaRevertMem2
  rw [writeWord_read_preserved
    (burnTickUpdateLowerLiquidityAddDeltaRevertMem1 σ I obsWord tickLower)
    (burnTickUpdateLowerRevertFreePtr + (⟨36⟩ : UInt256)).toNat
    64 (⟨2⟩ : UInt256)
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem1_size σ I obsWord tickLower]
      native_decide)
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem1_size σ I obsWord tickLower]
      native_decide)]
  unfold burnTickUpdateLowerLiquidityAddDeltaRevertMem1
  rw [writeWord_read_preserved
    (burnTickUpdateLowerLiquidityAddDeltaRevertMem0 σ I obsWord tickLower)
    (burnTickUpdateLowerRevertFreePtr + (⟨4⟩ : UInt256)).toNat
    64 (⟨32⟩ : UInt256)
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem0_size σ I obsWord tickLower]
      native_decide)
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem0_size σ I obsWord tickLower]
      native_decide)]
  unfold burnTickUpdateLowerLiquidityAddDeltaRevertMem0
  rw [writeWord_read_preserved
    (burnTickUpdateLowerHashMem tickLower (burnObserveSingleDecodedMem σ I obsWord))
    burnTickUpdateLowerRevertFreePtr.toNat
    64 solcErrorStringSelector
    (by rw [burnTickUpdateLowerHashMem_size σ I obsWord tickLower]; native_decide)
    (by rw [burnTickUpdateLowerHashMem_size σ I obsWord tickLower]; native_decide)]
  exact burnTickUpdateLowerHashMem_read64 σ I obsWord tickLower

private theorem burnTickUpdateLowerLiquidityAddDeltaRevertMem3_mload64
    (σ : AccountMap) (I : ExecutionEnv) (obsWord tickLower : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (burnTickUpdateLowerLiquidityAddDeltaRevertMem3 σ I obsWord tickLower).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 24 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((burnTickUpdateLowerLiquidityAddDeltaRevertMem3 σ I obsWord tickLower).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      burnTickUpdateLowerRevertFreePtr := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnTickUpdateLowerLiquidityAddDeltaRevertMem3 σ I obsWord tickLower)
    (aw := UInt256.ofNat 24) (off := ⟨64⟩) (v := burnTickUpdateLowerRevertFreePtr)
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem3_size σ I obsWord tickLower]
      native_decide)
    (by native_decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using burnTickUpdateLowerLiquidityAddDeltaRevertMem3_read64 σ I obsWord tickLower)

private theorem uniswapV3PoolLiquidityAddDeltaLsRevertTailWf
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨13854⟩ ⟨2⟩ ⟨19539⟩ ⟨240⟩ .PUSH2 2 := by
  dsimp [solcErrorStringRevertTailWf]
  repeat' constructor
  all_goals
    rw [uniswapV3PoolLiquidityAddDeltaDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide

theorem uniswapV3PoolLiquidityAddDeltaLowerRevertTail
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {obsWord tickLower : UInt256} {stk : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13854⟩ stk
      (burnTickUpdateLowerHashMem tickLower (burnObserveSingleDecodedMem σ ee obsWord))
      (UInt256.ofNat 21) rdata (cA, σ) k C)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases uniswapV3PoolLiquidityAddDeltaLsRevertTailWf hpatch with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 burnTickUpdateLowerRevertFreePtr (UInt256.ofNat 21) hd3
      mem_cost
      (burnTickUpdateLowerHashMem_mload64 σ ee obsWord tickLower)
      (by native_decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 3 (burnTickUpdateLowerLiquidityAddDeltaRevertMem0 σ ee obsWord tickLower)
      (UInt256.ofNat 22) hd12 mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (burnTickUpdateLowerLiquidityAddDeltaRevertMem1 σ ee obsWord tickLower)
      (UInt256.ofNat 22) hd19 mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨2⟩ hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 4 (burnTickUpdateLowerLiquidityAddDeltaRevertMem2 σ ee obsWord tickLower)
      (UInt256.ofNat 23) hd26 mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst (⟨19539⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) hd27
    (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 ⟨240⟩ hdRawOut (by evm_ov),
    raw shl hdShl (by evm_ov)]
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (burnTickUpdateLowerLiquidityAddDeltaRevertMem3 σ ee obsWord tickLower)
      (UInt256.ofNat 24) hdMstore3 mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 burnTickUpdateLowerRevertFreePtr (UInt256.ofNat 24) hdMload
      mem_cost
      (burnTickUpdateLowerLiquidityAddDeltaRevertMem3_mload64 σ ee obsWord tickLower)
      (by native_decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

def burnTickUpdateLowerMaxLiquidityRevertWord : UInt256 :=
  UInt256.shiftLeft (⟨19535⟩ : UInt256) ⟨240⟩

noncomputable abbrev burnTickUpdateLowerMaxLiquidityRevertMem3
    (σ : AccountMap) (I : ExecutionEnv) (obsWord tickLower : UInt256) : ByteArray :=
  writeWord (burnTickUpdateLowerLiquidityAddDeltaRevertMem2 σ I obsWord tickLower)
    (burnTickUpdateLowerRevertFreePtr + (⟨68⟩ : UInt256)).toNat
    burnTickUpdateLowerMaxLiquidityRevertWord

private theorem burnTickUpdateLowerMaxLiquidityRevertMem3_size
    (σ : AccountMap) (I : ExecutionEnv) (obsWord tickLower : UInt256) :
    (burnTickUpdateLowerMaxLiquidityRevertMem3 σ I obsWord tickLower).size = 766 := by
  unfold burnTickUpdateLowerMaxLiquidityRevertMem3 burnTickUpdateLowerRevertFreePtr
  rw [writeWord_size _ _ _
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem2_size σ I obsWord tickLower]
      native_decide)]
  rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem2_size σ I obsWord tickLower]
  native_decide

private theorem burnTickUpdateLowerMaxLiquidityRevertMem3_read64
    (σ : AccountMap) (I : ExecutionEnv) (obsWord tickLower : UInt256) :
    (burnTickUpdateLowerMaxLiquidityRevertMem3 σ I obsWord tickLower).readWithPadding
        64 32 =
      UInt256.toByteArray burnTickUpdateLowerRevertFreePtr := by
  unfold burnTickUpdateLowerMaxLiquidityRevertMem3
  rw [writeWord_read_preserved
    (burnTickUpdateLowerLiquidityAddDeltaRevertMem2 σ I obsWord tickLower)
    (burnTickUpdateLowerRevertFreePtr + (⟨68⟩ : UInt256)).toNat
    64 burnTickUpdateLowerMaxLiquidityRevertWord
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem2_size σ I obsWord tickLower]
      native_decide)
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem2_size σ I obsWord tickLower]
      native_decide)]
  unfold burnTickUpdateLowerLiquidityAddDeltaRevertMem2
  rw [writeWord_read_preserved
    (burnTickUpdateLowerLiquidityAddDeltaRevertMem1 σ I obsWord tickLower)
    (burnTickUpdateLowerRevertFreePtr + (⟨36⟩ : UInt256)).toNat
    64 (⟨2⟩ : UInt256)
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem1_size σ I obsWord tickLower]
      native_decide)
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem1_size σ I obsWord tickLower]
      native_decide)]
  unfold burnTickUpdateLowerLiquidityAddDeltaRevertMem1
  rw [writeWord_read_preserved
    (burnTickUpdateLowerLiquidityAddDeltaRevertMem0 σ I obsWord tickLower)
    (burnTickUpdateLowerRevertFreePtr + (⟨4⟩ : UInt256)).toNat
    64 (⟨32⟩ : UInt256)
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem0_size σ I obsWord tickLower]
      native_decide)
    (by
      rw [burnTickUpdateLowerLiquidityAddDeltaRevertMem0_size σ I obsWord tickLower]
      native_decide)]
  unfold burnTickUpdateLowerLiquidityAddDeltaRevertMem0
  rw [writeWord_read_preserved
    (burnTickUpdateLowerHashMem tickLower (burnObserveSingleDecodedMem σ I obsWord))
    burnTickUpdateLowerRevertFreePtr.toNat
    64 solcErrorStringSelector
    (by rw [burnTickUpdateLowerHashMem_size σ I obsWord tickLower]; native_decide)
    (by rw [burnTickUpdateLowerHashMem_size σ I obsWord tickLower]; native_decide)]
  exact burnTickUpdateLowerHashMem_read64 σ I obsWord tickLower

private theorem burnTickUpdateLowerMaxLiquidityRevertMem3_mload64
    (σ : AccountMap) (I : ExecutionEnv) (obsWord tickLower : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (burnTickUpdateLowerMaxLiquidityRevertMem3 σ I obsWord tickLower).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 24 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((burnTickUpdateLowerMaxLiquidityRevertMem3 σ I obsWord tickLower).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      burnTickUpdateLowerRevertFreePtr := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnTickUpdateLowerMaxLiquidityRevertMem3 σ I obsWord tickLower)
    (aw := UInt256.ofNat 24) (off := ⟨64⟩) (v := burnTickUpdateLowerRevertFreePtr)
    (by
      rw [burnTickUpdateLowerMaxLiquidityRevertMem3_size σ I obsWord tickLower]
      native_decide)
    (by native_decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using burnTickUpdateLowerMaxLiquidityRevertMem3_read64 σ I obsWord tickLower)

private theorem uniswapV3PoolBurnLowerMaxLiquidityRevertTailWf
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨20867⟩ ⟨2⟩ ⟨19535⟩ ⟨240⟩ .PUSH2 2 := by
  dsimp [solcErrorStringRevertTailWf]
  repeat' constructor
  all_goals
    rw [uniswapV3PoolBurnTickUpdateDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide

theorem uniswapV3PoolBurnLowerMaxLiquidityRevertTail
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {obsWord tickLower : UInt256} {stk : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨20867⟩ stk
      (burnTickUpdateLowerHashMem tickLower (burnObserveSingleDecodedMem σ ee obsWord))
      (UInt256.ofNat 21) rdata (cA, σ) k C)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases uniswapV3PoolBurnLowerMaxLiquidityRevertTailWf hpatch with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 burnTickUpdateLowerRevertFreePtr (UInt256.ofNat 21) hd3
      mem_cost
      (burnTickUpdateLowerHashMem_mload64 σ ee obsWord tickLower)
      (by native_decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 3 (burnTickUpdateLowerLiquidityAddDeltaRevertMem0 σ ee obsWord tickLower)
      (UInt256.ofNat 22) hd12 mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (burnTickUpdateLowerLiquidityAddDeltaRevertMem1 σ ee obsWord tickLower)
      (UInt256.ofNat 22) hd19 mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨2⟩ hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 4 (burnTickUpdateLowerLiquidityAddDeltaRevertMem2 σ ee obsWord tickLower)
      (UInt256.ofNat 23) hd26 mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst (⟨19535⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) hd27
    (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 ⟨240⟩ hdRawOut (by evm_ov),
    raw shl hdShl (by evm_ov)]
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (burnTickUpdateLowerMaxLiquidityRevertMem3 σ ee obsWord tickLower)
      (UInt256.ofNat 24) hdMstore3 mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 burnTickUpdateLowerRevertFreePtr (UInt256.ofNat 24) hdMload
      mem_cost
      (burnTickUpdateLowerMaxLiquidityRevertMem3_mload64 σ ee obsWord tickLower)
      (by native_decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

theorem uniswapV3PoolLiquidityAddDeltaNegativeRevert
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {y x ret scratch xCopy obsWord tickLower : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13807⟩ (y :: x :: ret :: scratch :: xCopy :: R)
      (burnTickUpdateLowerHashMem tickLower (burnObserveSingleDecodedMem σ ee obsWord))
      (UInt256.ofNat 21) rdata (cA, σ) k C)
    (hneg :
      UInt256.isZero (UInt256.slt (UInt256.signextend ⟨15⟩ y) ⟨0⟩) = ⟨0⟩)
    (hreq :
      UInt256.lt
        (UInt256.land uint128Mask (UInt256.sub x (UInt256.sub ⟨0⟩ y)))
        (UInt256.land uint128Mask x) = ⟨0⟩)
    (hov : R.length + 20 ≤ 1024) :
    RDrev code g s0 := by
  have hdec (pc : UInt256)
      (hlo : 12989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13940) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolLiquidityAddDeltaDecodeEqTemplate hpatch hlo hhi
  have rd13808 := by
    simpa using h.jumpdest
      (by rw [hdec ⟨13807⟩ (by native_decide) (by native_decide)]; native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd13814 := evm_run rd13808 with [
    raw push1 ⟨0⟩ (by
      change decode code ⟨13808⟩ = some (.Push .PUSH1, some (⟨0⟩, 1))
      rw [hdec ⟨13808⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw dup1 (by
      change decode code ⟨13810⟩ = some (.DUP1, none)
      rw [hdec ⟨13810⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw dup3 (by
      change decode code ⟨13811⟩ = some (.DUP3, none)
      rw [hdec ⟨13811⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨15⟩ (by
      change decode code ⟨13812⟩ = some (.Push .PUSH1, some (⟨15⟩, 1))
      rw [hdec ⟨13812⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov)]
  have rd13815 := by
    simpa using RD.signextend rd13814
      (by
        change decode code ⟨13814⟩ = some (.SIGNEXTEND, none)
        rw [hdec ⟨13814⟩ (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd13820 := evm_run rd13815 with [
    raw slt (by
      change decode code ⟨13815⟩ = some (.SLT, none)
      rw [hdec ⟨13815⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw iszero (by
      change decode code ⟨13816⟩ = some (.ISZERO, none)
      rw [hdec ⟨13816⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push2 ⟨13908⟩ (by
      change decode code ⟨13817⟩ = some (.Push .PUSH2, some (⟨13908⟩, 2))
      rw [hdec ⟨13817⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov)]
  have rd13821 := by
    simpa using rd13820.jumpiNT
      (by
        change decode code ⟨13820⟩ = some (.JUMPI, none)
        rw [hdec ⟨13820⟩ (by native_decide) (by native_decide)]
        native_decide)
      hneg
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd13853 := evm_run rd13821 with [
    raw dup3 (by
      change decode code ⟨13821⟩ = some (.DUP3, none)
      rw [hdec ⟨13821⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      change decode code ⟨13822⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
      rw [hdec ⟨13822⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      change decode code ⟨13824⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
      rw [hdec ⟨13824⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by
      change decode code ⟨13826⟩ = some (.Push .PUSH1, some (⟨128⟩, 1))
      rw [hdec ⟨13826⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw shl (by
      change decode code ⟨13828⟩ = some (.SHL, none)
      rw [hdec ⟨13828⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      change decode code ⟨13829⟩ = some (.SUB, none)
      rw [hdec ⟨13829⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw and (by
      change decode code ⟨13830⟩ = some (.AND, none)
      rw [hdec ⟨13830⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw dup3 (by
      change decode code ⟨13831⟩ = some (.DUP3, none)
      rw [hdec ⟨13831⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by
      change decode code ⟨13832⟩ = some (.Push .PUSH1, some (⟨0⟩, 1))
      rw [hdec ⟨13832⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      change decode code ⟨13834⟩ = some (.SUB, none)
      rw [hdec ⟨13834⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw dup5 (by
      change decode code ⟨13835⟩ = some (.DUP5, none)
      rw [hdec ⟨13835⟩ (by native_decide) (by native_decide)]
      native_decide) (by simp only [List.length_cons] at hov ⊢; omega),
    raw sub (by
      change decode code ⟨13836⟩ = some (.SUB, none)
      rw [hdec ⟨13836⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw swap2 (by
      change decode code ⟨13837⟩ = some (.SWAP2, none)
      rw [hdec ⟨13837⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw pop (by
      change decode code ⟨13838⟩ = some (.POP, none)
      rw [hdec ⟨13838⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw dup2 (by
      change decode code ⟨13839⟩ = some (.DUP2, none)
      rw [hdec ⟨13839⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      change decode code ⟨13840⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
      rw [hdec ⟨13840⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      change decode code ⟨13842⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
      rw [hdec ⟨13842⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by
      change decode code ⟨13844⟩ = some (.Push .PUSH1, some (⟨128⟩, 1))
      rw [hdec ⟨13844⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw shl (by
      change decode code ⟨13846⟩ = some (.SHL, none)
      rw [hdec ⟨13846⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      change decode code ⟨13847⟩ = some (.SUB, none)
      rw [hdec ⟨13847⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw and (by
      change decode code ⟨13848⟩ = some (.AND, none)
      rw [hdec ⟨13848⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw lt (by
      change decode code ⟨13849⟩ = some (.LT, none)
      rw [hdec ⟨13849⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push2 ⟨13903⟩ (by
      change decode code ⟨13850⟩ = some (.Push .PUSH2, some (⟨13903⟩, 2))
      rw [hdec ⟨13850⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov)]
  have hreq' :
      UInt256.lt
        (UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨128⟩).sub ⟨1⟩)
          (UInt256.sub x (UInt256.sub ⟨0⟩ y)))
        (UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨128⟩).sub ⟨1⟩) x) =
        ⟨0⟩ := by
    rw [show ((⟨1⟩ : UInt256).shiftLeft ⟨128⟩).sub ⟨1⟩ = uint128Mask by
      native_decide]
    exact hreq
  have rd13854 := by
    simpa [uint128Mask, u256_land_comm] using rd13853.jumpiNT
      (by
        change decode code ⟨13853⟩ = some (.JUMPI, none)
        rw [hdec ⟨13853⟩ (by native_decide) (by native_decide)]
        native_decide)
      hreq'
      (by simp only [List.length_cons] at hov ⊢; omega)
  exact uniswapV3PoolLiquidityAddDeltaLowerRevertTail
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (obsWord := obsWord) (tickLower := tickLower)
    (rdata := rdata) (cA := cA) (σ := σ)
    hpatch rd13854
    (by simp only [List.length_cons] at hov ⊢; omega)

theorem uniswapV3PoolLiquidityAddDeltaNegativeReturn
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {y x ret scratch xCopy : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13807⟩ (y :: x :: ret :: scratch :: xCopy :: R)
      mem aw rdata (cA, σ) k C)
    (hneg :
      UInt256.isZero (UInt256.slt (UInt256.signextend ⟨15⟩ y) ⟨0⟩) = ⟨0⟩)
    (hreq :
      UInt256.lt
        (UInt256.land uint128Mask (UInt256.sub x (UInt256.sub ⟨0⟩ y)))
        (UInt256.land uint128Mask x) ≠ ⟨0⟩)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.sub x (UInt256.sub ⟨0⟩ y) :: scratch :: xCopy :: R)
      mem aw rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 12989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13940) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolLiquidityAddDeltaDecodeEqTemplate hpatch hlo hhi
  have rd13808 := by
    simpa using h.jumpdest
      (by rw [hdec ⟨13807⟩ (by native_decide) (by native_decide)]; native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd13814 := evm_run rd13808 with [
    raw push1 ⟨0⟩ (by
      change decode code ⟨13808⟩ = some (.Push .PUSH1, some (⟨0⟩, 1))
      rw [hdec ⟨13808⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw dup1 (by
      change decode code ⟨13810⟩ = some (.DUP1, none)
      rw [hdec ⟨13810⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw dup3 (by
      change decode code ⟨13811⟩ = some (.DUP3, none)
      rw [hdec ⟨13811⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨15⟩ (by
      change decode code ⟨13812⟩ = some (.Push .PUSH1, some (⟨15⟩, 1))
      rw [hdec ⟨13812⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov)]
  have rd13815 := by
    simpa using RD.signextend rd13814
      (by
        change decode code ⟨13814⟩ = some (.SIGNEXTEND, none)
        rw [hdec ⟨13814⟩ (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd13820 := evm_run rd13815 with [
    raw slt (by
      change decode code ⟨13815⟩ = some (.SLT, none)
      rw [hdec ⟨13815⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw iszero (by
      change decode code ⟨13816⟩ = some (.ISZERO, none)
      rw [hdec ⟨13816⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push2 ⟨13908⟩ (by
      change decode code ⟨13817⟩ = some (.Push .PUSH2, some (⟨13908⟩, 2))
      rw [hdec ⟨13817⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov)]
  have rd13821 := by
    simpa using rd13820.jumpiNT
      (by
        change decode code ⟨13820⟩ = some (.JUMPI, none)
        rw [hdec ⟨13820⟩ (by native_decide) (by native_decide)]
        native_decide)
      hneg
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd13853 := evm_run rd13821 with [
    raw dup3 (by
      change decode code ⟨13821⟩ = some (.DUP3, none)
      rw [hdec ⟨13821⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      change decode code ⟨13822⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
      rw [hdec ⟨13822⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      change decode code ⟨13824⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
      rw [hdec ⟨13824⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by
      change decode code ⟨13826⟩ = some (.Push .PUSH1, some (⟨128⟩, 1))
      rw [hdec ⟨13826⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw shl (by
      change decode code ⟨13828⟩ = some (.SHL, none)
      rw [hdec ⟨13828⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      change decode code ⟨13829⟩ = some (.SUB, none)
      rw [hdec ⟨13829⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw and (by
      change decode code ⟨13830⟩ = some (.AND, none)
      rw [hdec ⟨13830⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw dup3 (by
      change decode code ⟨13831⟩ = some (.DUP3, none)
      rw [hdec ⟨13831⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by
      change decode code ⟨13832⟩ = some (.Push .PUSH1, some (⟨0⟩, 1))
      rw [hdec ⟨13832⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      change decode code ⟨13834⟩ = some (.SUB, none)
      rw [hdec ⟨13834⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw dup5 (by
      change decode code ⟨13835⟩ = some (.DUP5, none)
      rw [hdec ⟨13835⟩ (by native_decide) (by native_decide)]
      native_decide) (by simp only [List.length_cons] at hov ⊢; omega),
    raw sub (by
      change decode code ⟨13836⟩ = some (.SUB, none)
      rw [hdec ⟨13836⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw swap2 (by
      change decode code ⟨13837⟩ = some (.SWAP2, none)
      rw [hdec ⟨13837⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw pop (by
      change decode code ⟨13838⟩ = some (.POP, none)
      rw [hdec ⟨13838⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw dup2 (by
      change decode code ⟨13839⟩ = some (.DUP2, none)
      rw [hdec ⟨13839⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      change decode code ⟨13840⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
      rw [hdec ⟨13840⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      change decode code ⟨13842⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
      rw [hdec ⟨13842⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by
      change decode code ⟨13844⟩ = some (.Push .PUSH1, some (⟨128⟩, 1))
      rw [hdec ⟨13844⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw shl (by
      change decode code ⟨13846⟩ = some (.SHL, none)
      rw [hdec ⟨13846⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      change decode code ⟨13847⟩ = some (.SUB, none)
      rw [hdec ⟨13847⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw and (by
      change decode code ⟨13848⟩ = some (.AND, none)
      rw [hdec ⟨13848⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw lt (by
      change decode code ⟨13849⟩ = some (.LT, none)
      rw [hdec ⟨13849⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw push2 ⟨13903⟩ (by
      change decode code ⟨13850⟩ = some (.Push .PUSH2, some (⟨13903⟩, 2))
      rw [hdec ⟨13850⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov)]
  have hreq' :
      UInt256.lt
        (UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨128⟩).sub ⟨1⟩)
          (UInt256.sub x (UInt256.sub ⟨0⟩ y)))
        (UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨128⟩).sub ⟨1⟩) x) ≠
        ⟨0⟩ := by
    rw [show ((⟨1⟩ : UInt256).shiftLeft ⟨128⟩).sub ⟨1⟩ = uint128Mask by
      native_decide]
    exact hreq
  have rd13903 := by
    simpa [uint128Mask, u256_land_comm] using rd13853.jumpiT
      (by
        change decode code ⟨13853⟩ = some (.JUMPI, none)
        rw [hdec ⟨13853⟩ (by native_decide) (by native_decide)]
        native_decide)
      hreq'
      (uniswapV3PoolBurnJumpDestPatched13903 hpatch)
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd13904 := by
    simpa using rd13903.jumpdest
      (by
        rw [hdec ⟨13903⟩ (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd13907 := evm_run rd13904 with [
    raw push2 ⟨12989⟩ (by
      change decode code ⟨13904⟩ = some (.Push .PUSH2, some (⟨12989⟩, 2))
      rw [hdec ⟨13904⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov)]
  have rd12989 := by
    simpa using rd13907.jump
      (by
        change decode code ⟨13907⟩ = some (.JUMP, none)
        rw [hdec ⟨13907⟩ (by native_decide) (by native_decide)]
        native_decide)
      (uniswapV3PoolBurnJumpDestPatched12989 hpatch)
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd12990 := by
    simpa using rd12989.jumpdest
      (by
        rw [hdec ⟨12989⟩ (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd12994 := evm_run rd12990 with [
    raw swap3 (by
      change decode code ⟨12990⟩ = some (.SWAP3, none)
      rw [hdec ⟨12990⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw swap2 (by
      change decode code ⟨12991⟩ = some (.SWAP2, none)
      rw [hdec ⟨12991⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw pop (by
      change decode code ⟨12992⟩ = some (.POP, none)
      rw [hdec ⟨12992⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov),
    raw pop (by
      change decode code ⟨12993⟩ = some (.POP, none)
      rw [hdec ⟨12993⟩ (by native_decide) (by native_decide)]
      native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa using rd12994.jump
      (by
        change decode code ⟨12994⟩ = some (.JUMP, none)
        rw [hdec ⟨12994⟩ (by native_decide) (by native_decide)]
        native_decide)
      hret
      (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnLowerMaxLiquidityRevert
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
    {z scratch x base zero maxLiquidity obsWord tickLower : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨20838⟩
      (z :: scratch :: x :: base :: zero :: maxLiquidity :: R)
      (burnTickUpdateLowerHashMem tickLower (burnObserveSingleDecodedMem σ ee obsWord))
      (UInt256.ofNat 21) rdata (cA, σ) k C)
    (hmax :
      UInt256.gt (UInt256.land uint128Mask z)
          (UInt256.land uint128Mask maxLiquidity) ≠ ⟨0⟩)
    (hov : R.length + 16 ≤ 1024) :
    RDrev code g s0 := by
  have hdec (pc : UInt256)
      (hlo : 20795 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21285) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnTickUpdateDecodeEqTemplate hpatch hlo hhi
  have rd20839 := by
    simpa using h.jumpdest
      (by rw [hdec ⟨20838⟩ (by native_decide) (by native_decide)]; native_decide)
      (by simp only [List.length_cons] at hov ⊢; omega)
  have rd20866 := evm_run rd20839 with [
    raw swap1 (by
      change decode code ⟨20839⟩ = some (.SWAP1, none)
      rw [hdec ⟨20839⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw pop (by
      change decode code ⟨20840⟩ = some (.POP, none)
      rw [hdec ⟨20840⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw dup5 (by
      change decode code ⟨20841⟩ = some (.DUP5, none)
      rw [hdec ⟨20841⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by omega),
    raw push1 ⟨1⟩ (by
      change decode code ⟨20842⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
      rw [hdec ⟨20842⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩ (by
      change decode code ⟨20844⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
      rw [hdec ⟨20844⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw push1 ⟨128⟩ (by
      change decode code ⟨20846⟩ = some (.Push .PUSH1, some (⟨128⟩, 1))
      rw [hdec ⟨20846⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw shl (by
      change decode code ⟨20848⟩ = some (.SHL, none)
      rw [hdec ⟨20848⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw sub (by
      change decode code ⟨20849⟩ = some (.SUB, none)
      rw [hdec ⟨20849⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw and (by
      change decode code ⟨20850⟩ = some (.AND, none)
      rw [hdec ⟨20850⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw dup2 (by
      change decode code ⟨20851⟩ = some (.DUP2, none)
      rw [hdec ⟨20851⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩ (by
      change decode code ⟨20852⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
      rw [hdec ⟨20852⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩ (by
      change decode code ⟨20854⟩ = some (.Push .PUSH1, some (⟨1⟩, 1))
      rw [hdec ⟨20854⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw push1 ⟨128⟩ (by
      change decode code ⟨20856⟩ = some (.Push .PUSH1, some (⟨128⟩, 1))
      rw [hdec ⟨20856⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw shl (by
      change decode code ⟨20858⟩ = some (.SHL, none)
      rw [hdec ⟨20858⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw sub (by
      change decode code ⟨20859⟩ = some (.SUB, none)
      rw [hdec ⟨20859⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw and (by
      change decode code ⟨20860⟩ = some (.AND, none)
      rw [hdec ⟨20860⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw gt (by
      change decode code ⟨20861⟩ = some (.GT, none)
      rw [hdec ⟨20861⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw iszero (by
      change decode code ⟨20862⟩ = some (.ISZERO, none)
      rw [hdec ⟨20862⟩ (by native_decide) (by native_decide)]
      native_decide)
      (by evm_ov),
    raw push2 ⟨20916⟩
      (by
        change decode code ⟨20863⟩ = some (.Push .PUSH2, some (⟨20916⟩, 2))
        rw [hdec ⟨20863⟩ (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hcond :
      UInt256.isZero
          (UInt256.gt (UInt256.land uint128Mask z)
            (UInt256.land uint128Mask maxLiquidity)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hmax
  have rd20867 := by
    simpa [uint128Mask, u256_land_comm] using rd20866.jumpiNT
      (by
        change decode code ⟨20866⟩ = some (.JUMPI, none)
        rw [hdec ⟨20866⟩ (by native_decide) (by native_decide)]
        native_decide)
      hcond
      (by simp only [List.length_cons] at hov ⊢; omega)
  exact uniswapV3PoolBurnLowerMaxLiquidityRevertTail
    (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
    (obsWord := obsWord) (tickLower := tickLower) (rdata := rdata)
    (cA := cA) (σ := σ) hpatch rd20867
    (by simp only [List.length_cons] at hov ⊢; omega)

end Benchmarks.UniswapV3Pool
