import Benchmarks.UniswapV3Pool.InitializeGetTickLogCombine
import Benchmarks.UniswapV3Pool.InitializeSourceGetTickPostLog
import Benchmarks.UniswapV3Pool.TickSpacing

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

private theorem nat_land_shifted_uint160_mask (n : Nat) (hn : n < 2 ^ (160 : Nat)) :
    Nat.land (n * 2 ^ (32 : Nat)) ((2 ^ (160 : Nat) - 1) * 2 ^ (32 : Nat)) =
      n * 2 ^ (32 : Nat) := by
  rw [show n * 2 ^ (32 : Nat) = n <<< 32 by rw [Nat.shiftLeft_eq]]
  rw [show (2 ^ (160 : Nat) - 1) * 2 ^ (32 : Nat) =
      (2 ^ (160 : Nat) - 1) <<< 32 by rw [Nat.shiftLeft_eq]]
  apply Nat.eq_of_testBit_eq
  intro i
  change (((n <<< 32) &&& ((2 ^ (160 : Nat) - 1) <<< 32)).testBit i) =
    (n <<< 32).testBit i
  rw [Nat.testBit_and, testBit_shiftLeft, testBit_shiftLeft]
  by_cases hi32 : i < 32
  · simp [hi32]
  · rw [if_neg hi32, if_neg hi32]
    by_cases hi160 : i - 32 < 160
    · have hmask : (2 ^ (160 : Nat) - 1).testBit (i - 32) = true := by
        rw [Nat.testBit_two_pow_sub_one, decide_eq_true hi160]
      rw [hmask, Bool.and_true]
    · have hmask : (2 ^ (160 : Nat) - 1).testBit (i - 32) = false := by
        rw [Nat.testBit_two_pow_sub_one, decide_eq_false hi160]
      have hnbit : n.testBit (i - 32) = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [hmask, hnbit]
      rfl

theorem getTickRatioWord_toNat_eq_source (I : ExecutionEnv) :
    (getTickRatioWord I).toNat = getTickSourceRatioNat I := by
  unfold getTickRatioWord getTickSourceRatioNat getTickRatioMask
  rw [u256_land_toNat]
  have hshift :
      (UInt256.shiftLeft (initializeArgWord I) ⟨32⟩).toNat =
        (initializeArgWord I).toNat * 2 ^ (32 : Nat) := by
    unfold UInt256.shiftLeft
    rw [if_neg (by decide : ¬ (⟨32⟩ : UInt256).val ≥ 256)]
    unfold UInt256.toNat
    rw [Fin.shiftLeft_val]
    change ((initializeArgWord I).toNat <<< 32) % UInt256.size =
      (initializeArgWord I).toNat * 2 ^ (32 : Nat)
    rw [Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt]
    have harg := initializeArgWord_toNat_lt_twoPow160 I
    have hmul := Nat.mul_lt_mul_of_pos_right harg (by norm_num : 0 < 2 ^ (32 : Nat))
    rw [← Nat.pow_add] at hmul
    norm_num [UInt256.size] at hmul ⊢
    exact lt_trans hmul (by norm_num [UInt256.size])
  rw [hshift]
  rw [show (⟨6277101735386680763835789423207666416102355444459739545600⟩ :
      UInt256).toNat = (2 ^ (160 : Nat) - 1) * 2 ^ (32 : Nat) by native_decide]
  rw [nat_land_shifted_uint160_mask]
  rw [show EVM.wordModulus = UInt256.size by native_decide]
  exact initializeArgWord_toNat_lt_twoPow160 I

private theorem shiftRight_toNat_of_lt_256 (w s : UInt256) (hs : s.toNat < 256) :
    (UInt256.shiftRight w s).toNat = w.toNat / 2 ^ s.toNat := by
  unfold UInt256.shiftRight
  rw [if_neg]
  · unfold UInt256.toNat
    rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]
  · exact not_le_of_gt hs

private theorem shiftLeft_toNat_of_lt_256 (w s : UInt256) (hs : s.toNat < 256) :
    (UInt256.shiftLeft w s).toNat = w.toNat * 2 ^ s.toNat % UInt256.size := by
  unfold UInt256.shiftLeft
  rw [if_neg]
  · unfold UInt256.toNat
    rw [Fin.shiftLeft_val, Nat.shiftLeft_eq]
  · exact not_le_of_gt hs

theorem getTickMsbF7Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickMsbF7Word I).toNat = getTickSourceMsbF7Nat I := by
  unfold getTickMsbF7Word getTickSourceMsbF7Nat getTickSourceRatioGt7
  have hthreshold :
      getTickMsbThreshold7.toNat = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF := by
    native_decide
  by_cases hgt : getTickSourceRatioNat I > 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
  · have hgtWord : UInt256.gt (getTickRatioWord I) getTickMsbThreshold7 = ⟨1⟩ := by
      exact ugt_one (by
        rw [getTickRatioWord_toNat_eq_source I, hthreshold]
        exact hgt)
    rw [hgtWord]
    rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨7⟩).toNat = 128 by native_decide]
    rw [decide_eq_true hgt]
    norm_num
  · have hgtWord : UInt256.gt (getTickRatioWord I) getTickMsbThreshold7 = ⟨0⟩ := by
      exact ugt_zero (by
        rw [getTickRatioWord_toNat_eq_source I, hthreshold]
        omega)
    rw [hgtWord]
    rw [show (UInt256.shiftLeft (⟨0⟩ : UInt256) ⟨7⟩).toNat = 0 by native_decide]
    rw [decide_eq_false hgt]
    norm_num

theorem getTickRAfterMsb7Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickRAfterMsb7Word I).toNat = getTickSourceRAfterMsb7Nat I := by
  unfold getTickRAfterMsb7Word getTickSourceRAfterMsb7Nat
  rw [shiftRight_toNat_of_lt_256]
  · rw [getTickRatioWord_toNat_eq_source I, getTickMsbF7Word_toNat_eq_source I]
  · rw [getTickMsbF7Word_toNat_eq_source I]
    unfold getTickSourceMsbF7Nat
    split <;> norm_num

theorem getTickMsbF6Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickMsbF6Word I).toNat = getTickSourceMsbF6Nat I := by
  unfold getTickMsbF6Word getTickSourceMsbF6Nat getTickSourceRAfterMsb7Gt6
  have hthreshold : getTickMsbThreshold6.toNat = 0xFFFFFFFFFFFFFFFF := by
    native_decide
  by_cases hgt : getTickSourceRAfterMsb7Nat I > 0xFFFFFFFFFFFFFFFF
  · have hgtWord : UInt256.gt (getTickRAfterMsb7Word I) getTickMsbThreshold6 = ⟨1⟩ := by
      exact ugt_one (by
        rw [getTickRAfterMsb7Word_toNat_eq_source I, hthreshold]
        exact hgt)
    rw [hgtWord]
    rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨6⟩).toNat = 64 by native_decide]
    rw [decide_eq_true hgt]
    norm_num
  · have hgtWord : UInt256.gt (getTickRAfterMsb7Word I) getTickMsbThreshold6 = ⟨0⟩ := by
      exact ugt_zero (by
        rw [getTickRAfterMsb7Word_toNat_eq_source I, hthreshold]
        omega)
    rw [hgtWord]
    rw [show (UInt256.shiftLeft (⟨0⟩ : UInt256) ⟨6⟩).toNat = 0 by native_decide]
    rw [decide_eq_false hgt]
    norm_num

theorem getTickRAfterMsb6Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickRAfterMsb6Word I).toNat = getTickSourceRAfterMsb6Nat I := by
  unfold getTickRAfterMsb6Word getTickSourceRAfterMsb6Nat
  rw [shiftRight_toNat_of_lt_256]
  · rw [getTickRAfterMsb7Word_toNat_eq_source I, getTickMsbF6Word_toNat_eq_source I]
  · rw [getTickMsbF6Word_toNat_eq_source I]
    unfold getTickSourceMsbF6Nat
    split <;> norm_num

theorem getTickMsbF5Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickMsbF5Word I).toNat = getTickSourceMsbF5Nat I := by
  unfold getTickMsbF5Word getTickSourceMsbF5Nat getTickSourceRAfterMsb6Gt5
  have hthreshold : getTickMsbThreshold5.toNat = 0xFFFFFFFF := by
    native_decide
  by_cases hgt : getTickSourceRAfterMsb6Nat I > 0xFFFFFFFF
  · have hgtWord : UInt256.gt (getTickRAfterMsb6Word I) getTickMsbThreshold5 = ⟨1⟩ := by
      exact ugt_one (by
        rw [getTickRAfterMsb6Word_toNat_eq_source I, hthreshold]
        exact hgt)
    rw [hgtWord]
    rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨5⟩).toNat = 32 by native_decide]
    rw [decide_eq_true hgt]
    norm_num
  · have hgtWord : UInt256.gt (getTickRAfterMsb6Word I) getTickMsbThreshold5 = ⟨0⟩ := by
      exact ugt_zero (by
        rw [getTickRAfterMsb6Word_toNat_eq_source I, hthreshold]
        omega)
    rw [hgtWord]
    rw [show (UInt256.shiftLeft (⟨0⟩ : UInt256) ⟨5⟩).toNat = 0 by native_decide]
    rw [decide_eq_false hgt]
    norm_num

theorem getTickRAfterMsb5Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickRAfterMsb5Word I).toNat = getTickSourceRAfterMsb5Nat I := by
  unfold getTickRAfterMsb5Word getTickSourceRAfterMsb5Nat
  rw [shiftRight_toNat_of_lt_256]
  · rw [getTickRAfterMsb6Word_toNat_eq_source I, getTickMsbF5Word_toNat_eq_source I]
  · rw [getTickMsbF5Word_toNat_eq_source I]
    unfold getTickSourceMsbF5Nat
    split <;> norm_num

theorem getTickMsbF4Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickMsbF4Word I).toNat = getTickSourceMsbF4Nat I := by
  unfold getTickMsbF4Word getTickSourceMsbF4Nat getTickSourceRAfterMsb5Gt4
  have hthreshold : getTickMsbThreshold4.toNat = 0xFFFF := by
    native_decide
  by_cases hgt : getTickSourceRAfterMsb5Nat I > 0xFFFF
  · have hgtWord : UInt256.gt (getTickRAfterMsb5Word I) getTickMsbThreshold4 = ⟨1⟩ := by
      exact ugt_one (by
        rw [getTickRAfterMsb5Word_toNat_eq_source I, hthreshold]
        exact hgt)
    rw [hgtWord]
    rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨4⟩).toNat = 16 by native_decide]
    rw [decide_eq_true hgt]
    norm_num
  · have hgtWord : UInt256.gt (getTickRAfterMsb5Word I) getTickMsbThreshold4 = ⟨0⟩ := by
      exact ugt_zero (by
        rw [getTickRAfterMsb5Word_toNat_eq_source I, hthreshold]
        omega)
    rw [hgtWord]
    rw [show (UInt256.shiftLeft (⟨0⟩ : UInt256) ⟨4⟩).toNat = 0 by native_decide]
    rw [decide_eq_false hgt]
    norm_num

theorem getTickRAfterMsb4Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickRAfterMsb4Word I).toNat = getTickSourceRAfterMsb4Nat I := by
  unfold getTickRAfterMsb4Word getTickSourceRAfterMsb4Nat
  rw [shiftRight_toNat_of_lt_256]
  · rw [getTickRAfterMsb5Word_toNat_eq_source I, getTickMsbF4Word_toNat_eq_source I]
  · rw [getTickMsbF4Word_toNat_eq_source I]
    unfold getTickSourceMsbF4Nat
    split <;> norm_num

theorem getTickMsbF3Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickMsbF3Word I).toNat = getTickSourceMsbF3Nat I := by
  unfold getTickMsbF3Word getTickSourceMsbF3Nat getTickSourceRAfterMsb4Gt3
  have hthreshold : getTickMsbThreshold3.toNat = 0xFF := by
    native_decide
  by_cases hgt : getTickSourceRAfterMsb4Nat I > 0xFF
  · have hgtWord : UInt256.gt (getTickRAfterMsb4Word I) getTickMsbThreshold3 = ⟨1⟩ := by
      exact ugt_one (by
        rw [getTickRAfterMsb4Word_toNat_eq_source I, hthreshold]
        exact hgt)
    rw [hgtWord]
    rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨3⟩).toNat = 8 by native_decide]
    rw [decide_eq_true hgt]
    norm_num
  · have hgtWord : UInt256.gt (getTickRAfterMsb4Word I) getTickMsbThreshold3 = ⟨0⟩ := by
      exact ugt_zero (by
        rw [getTickRAfterMsb4Word_toNat_eq_source I, hthreshold]
        omega)
    rw [hgtWord]
    rw [show (UInt256.shiftLeft (⟨0⟩ : UInt256) ⟨3⟩).toNat = 0 by native_decide]
    rw [decide_eq_false hgt]
    norm_num

theorem getTickRAfterMsb3Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickRAfterMsb3Word I).toNat = getTickSourceRAfterMsb3Nat I := by
  unfold getTickRAfterMsb3Word getTickSourceRAfterMsb3Nat
  rw [shiftRight_toNat_of_lt_256]
  · rw [getTickRAfterMsb4Word_toNat_eq_source I, getTickMsbF3Word_toNat_eq_source I]
  · rw [getTickMsbF3Word_toNat_eq_source I]
    unfold getTickSourceMsbF3Nat
    split <;> norm_num

theorem getTickMsbF2Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickMsbF2Word I).toNat = getTickSourceMsbF2Nat I := by
  unfold getTickMsbF2Word getTickSourceMsbF2Nat getTickSourceRAfterMsb3Gt2
  have hthreshold : getTickMsbThreshold2.toNat = 0xF := by
    native_decide
  by_cases hgt : getTickSourceRAfterMsb3Nat I > 0xF
  · have hgtWord : UInt256.gt (getTickRAfterMsb3Word I) getTickMsbThreshold2 = ⟨1⟩ := by
      exact ugt_one (by
        rw [getTickRAfterMsb3Word_toNat_eq_source I, hthreshold]
        exact hgt)
    rw [hgtWord]
    rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨2⟩).toNat = 4 by native_decide]
    rw [decide_eq_true hgt]
    norm_num
  · have hgtWord : UInt256.gt (getTickRAfterMsb3Word I) getTickMsbThreshold2 = ⟨0⟩ := by
      exact ugt_zero (by
        rw [getTickRAfterMsb3Word_toNat_eq_source I, hthreshold]
        omega)
    rw [hgtWord]
    rw [show (UInt256.shiftLeft (⟨0⟩ : UInt256) ⟨2⟩).toNat = 0 by native_decide]
    rw [decide_eq_false hgt]
    norm_num

theorem getTickRAfterMsb2Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickRAfterMsb2Word I).toNat = getTickSourceRAfterMsb2Nat I := by
  unfold getTickRAfterMsb2Word getTickSourceRAfterMsb2Nat
  rw [shiftRight_toNat_of_lt_256]
  · rw [getTickRAfterMsb3Word_toNat_eq_source I, getTickMsbF2Word_toNat_eq_source I]
  · rw [getTickMsbF2Word_toNat_eq_source I]
    unfold getTickSourceMsbF2Nat
    split <;> norm_num

theorem getTickMsbF1Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickMsbF1Word I).toNat = getTickSourceMsbF1Nat I := by
  unfold getTickMsbF1Word getTickSourceMsbF1Nat getTickSourceRAfterMsb2Gt1
  have hthreshold : getTickMsbThreshold1.toNat = 0x3 := by
    native_decide
  by_cases hgt : getTickSourceRAfterMsb2Nat I > 0x3
  · have hgtWord : UInt256.gt (getTickRAfterMsb2Word I) getTickMsbThreshold1 = ⟨1⟩ := by
      exact ugt_one (by
        rw [getTickRAfterMsb2Word_toNat_eq_source I, hthreshold]
        exact hgt)
    rw [hgtWord]
    rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨1⟩).toNat = 2 by native_decide]
    rw [decide_eq_true hgt]
    norm_num
  · have hgtWord : UInt256.gt (getTickRAfterMsb2Word I) getTickMsbThreshold1 = ⟨0⟩ := by
      exact ugt_zero (by
        rw [getTickRAfterMsb2Word_toNat_eq_source I, hthreshold]
        omega)
    rw [hgtWord]
    rw [show (UInt256.shiftLeft (⟨0⟩ : UInt256) ⟨1⟩).toNat = 0 by native_decide]
    rw [decide_eq_false hgt]
    norm_num

theorem getTickRAfterMsb1Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickRAfterMsb1Word I).toNat = getTickSourceRAfterMsb1Nat I := by
  unfold getTickRAfterMsb1Word getTickSourceRAfterMsb1Nat
  rw [shiftRight_toNat_of_lt_256]
  · rw [getTickRAfterMsb2Word_toNat_eq_source I, getTickMsbF1Word_toNat_eq_source I]
  · rw [getTickMsbF1Word_toNat_eq_source I]
    unfold getTickSourceMsbF1Nat
    split <;> norm_num

theorem getTickMsbF0Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickMsbF0Word I).toNat = getTickSourceMsbF0Nat I := by
  unfold getTickMsbF0Word getTickSourceMsbF0Nat getTickSourceRAfterMsb1Gt0
  by_cases hgt : getTickSourceRAfterMsb1Nat I > 1
  · have hgtWord : UInt256.gt (getTickRAfterMsb1Word I) ⟨1⟩ = ⟨1⟩ := by
      exact ugt_one (by
        rw [getTickRAfterMsb1Word_toNat_eq_source I]
        change 1 < getTickSourceRAfterMsb1Nat I
        exact hgt)
    rw [hgtWord, decide_eq_true hgt]
    rfl
  · have hgtWord : UInt256.gt (getTickRAfterMsb1Word I) ⟨1⟩ = ⟨0⟩ := by
      exact ugt_zero (by
        rw [getTickRAfterMsb1Word_toNat_eq_source I]
        change getTickSourceRAfterMsb1Nat I ≤ 1
        omega)
    rw [hgtWord, decide_eq_false hgt]
    norm_num

private theorem getTickMsbWord_bits_toNat
    (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    (UInt256.lor
      (UInt256.lor
        (UInt256.lor
          (if b2 then (⟨4⟩ : UInt256) else ⟨0⟩)
          (UInt256.lor
            (UInt256.lor
              (if b4 then (⟨16⟩ : UInt256) else ⟨0⟩)
              (UInt256.lor
                (if b5 then (⟨32⟩ : UInt256) else ⟨0⟩)
                (UInt256.lor
                  (if b6 then (⟨64⟩ : UInt256) else ⟨0⟩)
                  (if b7 then (⟨128⟩ : UInt256) else ⟨0⟩))))
            (if b3 then (⟨8⟩ : UInt256) else ⟨0⟩)))
        (if b1 then (⟨2⟩ : UInt256) else ⟨0⟩))
      (if b0 then (⟨1⟩ : UInt256) else ⟨0⟩)).toNat =
      (if b7 then 128 else 0) +
        ((if b6 then 64 else 0) +
          ((if b5 then 32 else 0) +
            ((if b4 then 16 else 0) +
              ((if b3 then 8 else 0) +
                ((if b2 then 4 else 0) +
                  ((if b1 then 2 else 0) + if b0 then 1 else 0)))))) := by
  native_decide +revert

theorem getTickMsbWord_toNat_eq_source (I : ExecutionEnv) :
    (getTickMsbWord I).toNat = getTickSourceMsbAfter0Nat I := by
  have hf7 :
      getTickMsbF7Word I =
        if getTickSourceRatioGt7 I then (⟨128⟩ : UInt256) else ⟨0⟩ := by
    apply u256_inj
    rw [getTickMsbF7Word_toNat_eq_source I]
    unfold getTickSourceMsbF7Nat
    by_cases h : getTickSourceRatioGt7 I <;> (simp [h]; try native_decide)
  have hf6 :
      getTickMsbF6Word I =
        if getTickSourceRAfterMsb7Gt6 I then (⟨64⟩ : UInt256) else ⟨0⟩ := by
    apply u256_inj
    rw [getTickMsbF6Word_toNat_eq_source I]
    unfold getTickSourceMsbF6Nat
    by_cases h : getTickSourceRAfterMsb7Gt6 I <;> (simp [h]; try native_decide)
  have hf5 :
      getTickMsbF5Word I =
        if getTickSourceRAfterMsb6Gt5 I then (⟨32⟩ : UInt256) else ⟨0⟩ := by
    apply u256_inj
    rw [getTickMsbF5Word_toNat_eq_source I]
    unfold getTickSourceMsbF5Nat
    by_cases h : getTickSourceRAfterMsb6Gt5 I <;> (simp [h]; try native_decide)
  have hf4 :
      getTickMsbF4Word I =
        if getTickSourceRAfterMsb5Gt4 I then (⟨16⟩ : UInt256) else ⟨0⟩ := by
    apply u256_inj
    rw [getTickMsbF4Word_toNat_eq_source I]
    unfold getTickSourceMsbF4Nat
    by_cases h : getTickSourceRAfterMsb5Gt4 I <;> (simp [h]; try native_decide)
  have hf3 :
      getTickMsbF3Word I =
        if getTickSourceRAfterMsb4Gt3 I then (⟨8⟩ : UInt256) else ⟨0⟩ := by
    apply u256_inj
    rw [getTickMsbF3Word_toNat_eq_source I]
    unfold getTickSourceMsbF3Nat
    by_cases h : getTickSourceRAfterMsb4Gt3 I <;> (simp [h]; try native_decide)
  have hf2 :
      getTickMsbF2Word I =
        if getTickSourceRAfterMsb3Gt2 I then (⟨4⟩ : UInt256) else ⟨0⟩ := by
    apply u256_inj
    rw [getTickMsbF2Word_toNat_eq_source I]
    unfold getTickSourceMsbF2Nat
    by_cases h : getTickSourceRAfterMsb3Gt2 I <;> (simp [h]; try native_decide)
  have hf1 :
      getTickMsbF1Word I =
        if getTickSourceRAfterMsb2Gt1 I then (⟨2⟩ : UInt256) else ⟨0⟩ := by
    apply u256_inj
    rw [getTickMsbF1Word_toNat_eq_source I]
    unfold getTickSourceMsbF1Nat
    by_cases h : getTickSourceRAfterMsb2Gt1 I <;> (simp [h]; try native_decide)
  have hf0 :
      getTickMsbF0Word I =
        if getTickSourceRAfterMsb1Gt0 I then (⟨1⟩ : UInt256) else ⟨0⟩ := by
    apply u256_inj
    rw [getTickMsbF0Word_toNat_eq_source I]
    unfold getTickSourceMsbF0Nat
    by_cases h : getTickSourceRAfterMsb1Gt0 I <;> (simp [h]; try native_decide)
  unfold getTickMsbWord getTickMsbF1234567Word getTickMsbF234567Word
    getTickMsbF34567Word getTickMsbF4567Word getTickMsbF567Word getTickMsbF67Word
  rw [hf7, hf6, hf5, hf4, hf3, hf2, hf1, hf0]
  simpa [getTickSourceMsbAfter0Nat, getTickSourceMsbAfter1Nat,
    getTickSourceMsbAfter2Nat, getTickSourceMsbAfter3Nat, getTickSourceMsbAfter4Nat,
    getTickSourceMsbAfter5Nat, getTickSourceMsbAfter6Nat, getTickSourceMsbF0Nat,
    getTickSourceMsbF1Nat, getTickSourceMsbF2Nat, getTickSourceMsbF3Nat,
    getTickSourceMsbF4Nat, getTickSourceMsbF5Nat, getTickSourceMsbF6Nat,
    getTickSourceMsbF7Nat, Nat.add_assoc] using
    getTickMsbWord_bits_toNat
      (getTickSourceRAfterMsb1Gt0 I)
      (getTickSourceRAfterMsb2Gt1 I)
      (getTickSourceRAfterMsb3Gt2 I)
      (getTickSourceRAfterMsb4Gt3 I)
      (getTickSourceRAfterMsb5Gt4 I)
      (getTickSourceRAfterMsb6Gt5 I)
      (getTickSourceRAfterMsb7Gt6 I)
      (getTickSourceRatioGt7 I)

theorem getTickRNormalizedWord_toNat_eq_source (I : ExecutionEnv) :
    (getTickRNormalizedWord I).toNat = getTickSourceRNormalizedNat I := by
  have hmsb := getTickMsbWord_toNat_eq_source I
  have hmsbLe := getTickSourceMsbAfter0Nat_le_255 I
  unfold getTickRNormalizedWord getTickSourceRNormalizedNat
  by_cases hge : 128 ≤ getTickSourceMsbAfter0Nat I
  · have hltWord : UInt256.lt (getTickMsbWord I) ⟨128⟩ = ⟨0⟩ := by
      apply ult_zero
      rw [hmsb]
      change 128 ≤ getTickSourceMsbAfter0Nat I
      exact hge
    have hsource : getTickSourceMsbGe128 I = true := by
      unfold getTickSourceMsbGe128
      exact decide_eq_true hge
    simp only [hltWord, hsource, ↓reduceIte]
    unfold getTickRNormalizedHighWord getTickSourceRNormalizedHighNat
    have hsub : (UInt256.sub (getTickMsbWord I) ⟨127⟩).toNat =
        getTickSourceMsbAfter0Nat I - 127 := by
      rw [usub_toNat]
      · rw [hmsb]
        change getTickSourceMsbAfter0Nat I - 127 = getTickSourceMsbAfter0Nat I - 127
        rfl
      · rw [hmsb]
        change 127 ≤ getTickSourceMsbAfter0Nat I
        omega
    rw [shiftRight_toNat_of_lt_256]
    · rw [getTickRatioWord_toNat_eq_source I, hsub]
    · rw [hsub]
      omega
  · have hltNat : getTickSourceMsbAfter0Nat I < 128 := Nat.lt_of_not_ge hge
    have hltWord : UInt256.lt (getTickMsbWord I) ⟨128⟩ = ⟨1⟩ := by
      apply ult_one
      rw [hmsb]
      change getTickSourceMsbAfter0Nat I < 128
      exact hltNat
    have hsource : getTickSourceMsbGe128 I = false := by
      unfold getTickSourceMsbGe128
      exact decide_eq_false hge
    rw [hltWord, hsource]
    rw [if_neg (by native_decide : ¬ ((⟨1⟩ : UInt256) = ⟨0⟩))]
    rw [if_neg (by decide : ¬ (false = true))]
    unfold getTickRNormalizedLowWord getTickSourceRNormalizedLowNat
    have hsub : (UInt256.sub ⟨127⟩ (getTickMsbWord I)).toNat =
        127 - getTickSourceMsbAfter0Nat I := by
      rw [usub_toNat]
      · rw [hmsb]
        change 127 - getTickSourceMsbAfter0Nat I = 127 - getTickSourceMsbAfter0Nat I
        rfl
      · rw [hmsb]
        change getTickSourceMsbAfter0Nat I ≤ 127
        omega
    rw [shiftLeft_toNat_of_lt_256]
    · rw [getTickRatioWord_toNat_eq_source I, hsub]
      rw [show EVM.wordModulus = UInt256.size by native_decide]
    · rw [hsub]
      omega

theorem getTickLogRSquared63Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRSquared63Word I).toNat =
      getTickSourceRNormalizedNat I * getTickSourceRNormalizedNat I := by
  unfold getTickLogRSquared63Word
  rw [u256_mul_toNat]
  rw [getTickRNormalizedWord_toNat_eq_source I]
  rw [Nat.mod_eq_of_lt]
  simpa [EVM.wordModulus] using getTickSourceRNormalizedNat_mul_self_lt_wordModulus I

theorem getTickLogRShifted63Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRShifted63Word I).toNat = getTickSourceLogRShifted63Nat I := by
  unfold getTickLogRShifted63Word getTickSourceLogRShifted63Nat
  rw [shiftRight_toNat_of_lt_256]
  · rw [getTickLogRSquared63Word_toNat_eq_source I]
    change getTickSourceRNormalizedNat I * getTickSourceRNormalizedNat I / 2 ^ (127 : Nat) =
      getTickSourceRNormalizedNat I * getTickSourceRNormalizedNat I / 2 ^ (127 : Nat)
    rfl
  · native_decide

theorem getTickLogF63Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogF63Word I).toNat = getTickSourceLogF63Nat I := by
  unfold getTickLogF63Word getTickSourceLogF63Nat getTickSourceLogRShifted63Nat
  rw [shiftRight_toNat_of_lt_256]
  · rw [getTickLogRSquared63Word_toNat_eq_source I]
    change getTickSourceRNormalizedNat I * getTickSourceRNormalizedNat I / 2 ^ (255 : Nat) =
      getTickSourceRNormalizedNat I * getTickSourceRNormalizedNat I / 2 ^ (127 : Nat) /
        2 ^ (128 : Nat)
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  · native_decide

theorem getTickLogRAfter63Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRAfter63Word I).toNat = getTickSourceLogRAfter63Nat I := by
  unfold getTickLogRAfter63Word getTickSourceLogRAfter63Nat
  rw [shiftRight_toNat_of_lt_256]
  · rw [getTickLogRShifted63Word_toNat_eq_source I, getTickLogF63Word_toNat_eq_source I]
  · rw [getTickLogF63Word_toNat_eq_source I]
    have hle := getTickSourceLogF63Nat_le_1 I
    omega

private theorem getTickLogStepRShiftedWord_toNat_eq_source (r : UInt256) (rn : Nat)
    (hr : r.toNat = rn) (hmul : rn * rn < EVM.wordModulus) :
    (UInt256.shiftRight (UInt256.mul r r) ⟨127⟩).toNat =
      getTickSourceLogStepRShiftedNat rn := by
  unfold getTickSourceLogStepRShiftedNat
  rw [shiftRight_toNat_of_lt_256]
  · rw [u256_mul_toNat, hr]
    rw [Nat.mod_eq_of_lt]
    · change rn * rn / 2 ^ (127 : Nat) = rn * rn / 2 ^ (127 : Nat)
      rfl
    · simpa [EVM.wordModulus] using hmul
  · native_decide

private theorem getTickLogStepFWord_toNat_eq_source (r : UInt256) (rn : Nat)
    (hr : r.toNat = rn) (hmul : rn * rn < EVM.wordModulus) :
    (UInt256.shiftRight (UInt256.mul r r) ⟨255⟩).toNat =
      getTickSourceLogStepFNat rn := by
  unfold getTickSourceLogStepFNat getTickSourceLogStepRShiftedNat
  rw [shiftRight_toNat_of_lt_256]
  · rw [u256_mul_toNat, hr]
    rw [Nat.mod_eq_of_lt]
    · change rn * rn / 2 ^ (255 : Nat) = rn * rn / 2 ^ (127 : Nat) /
        2 ^ (128 : Nat)
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
    · simpa [EVM.wordModulus] using hmul
  · native_decide

private theorem getTickLogStepRAfterWord_toNat_eq_source (r : UInt256) (rn : Nat)
    (hr : r.toNat = rn) (hmul : rn * rn < EVM.wordModulus) :
    (UInt256.shiftRight
        (UInt256.shiftRight (UInt256.mul r r) ⟨127⟩)
        (UInt256.shiftRight (UInt256.mul r r) ⟨255⟩)).toNat =
      getTickSourceLogStepRAfterNat rn := by
  unfold getTickSourceLogStepRAfterNat
  rw [shiftRight_toNat_of_lt_256]
  · rw [getTickLogStepRShiftedWord_toNat_eq_source r rn hr hmul,
      getTickLogStepFWord_toNat_eq_source r rn hr hmul]
  · rw [getTickLogStepFWord_toNat_eq_source r rn hr hmul]
    have hle := getTickSourceLogStepFNat_le_1 rn hmul
    omega

theorem getTickLogRSquared62Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRSquared62Word I).toNat =
      getTickSourceLogRAfter63Nat I * getTickSourceLogRAfter63Nat I := by
  unfold getTickLogRSquared62Word
  rw [u256_mul_toNat, getTickLogRAfter63Word_toNat_eq_source I]
  rw [Nat.mod_eq_of_lt]
  simpa [EVM.wordModulus] using getTickSourceLogRAfter63Nat_mul_self_lt_wordModulus I

theorem getTickLogRShifted62Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRShifted62Word I).toNat = getTickSourceLogRShifted62Nat I := by
  unfold getTickLogRShifted62Word getTickLogRSquared62Word getTickSourceLogRShifted62Nat
  exact getTickLogStepRShiftedWord_toNat_eq_source
    (getTickLogRAfter63Word I)
    (getTickSourceLogRAfter63Nat I)
    (getTickLogRAfter63Word_toNat_eq_source I)
    (getTickSourceLogRAfter63Nat_mul_self_lt_wordModulus I)

theorem getTickLogF62Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogF62Word I).toNat = getTickSourceLogF62Nat I := by
  unfold getTickLogF62Word getTickLogRSquared62Word getTickSourceLogF62Nat
  exact getTickLogStepFWord_toNat_eq_source
    (getTickLogRAfter63Word I)
    (getTickSourceLogRAfter63Nat I)
    (getTickLogRAfter63Word_toNat_eq_source I)
    (getTickSourceLogRAfter63Nat_mul_self_lt_wordModulus I)

theorem getTickLogRAfter62Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRAfter62Word I).toNat = getTickSourceLogRAfter62Nat I := by
  unfold getTickLogRAfter62Word getTickLogRShifted62Word getTickLogF62Word
    getTickLogRSquared62Word getTickSourceLogRAfter62Nat
  exact getTickLogStepRAfterWord_toNat_eq_source
    (getTickLogRAfter63Word I)
    (getTickSourceLogRAfter63Nat I)
    (getTickLogRAfter63Word_toNat_eq_source I)
    (getTickSourceLogRAfter63Nat_mul_self_lt_wordModulus I)

theorem getTickLogRShifted61Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRShifted61Word I).toNat = getTickSourceLogRShifted61Nat I := by
  unfold getTickLogRShifted61Word getTickLogRSquared61Word getTickSourceLogRShifted61Nat
  exact getTickLogStepRShiftedWord_toNat_eq_source
    (getTickLogRAfter62Word I)
    (getTickSourceLogRAfter62Nat I)
    (getTickLogRAfter62Word_toNat_eq_source I)
    (getTickSourceLogRAfter62Nat_mul_self_lt_wordModulus I)

theorem getTickLogF61Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogF61Word I).toNat = getTickSourceLogF61Nat I := by
  unfold getTickLogF61Word getTickLogRSquared61Word getTickSourceLogF61Nat
  exact getTickLogStepFWord_toNat_eq_source
    (getTickLogRAfter62Word I)
    (getTickSourceLogRAfter62Nat I)
    (getTickLogRAfter62Word_toNat_eq_source I)
    (getTickSourceLogRAfter62Nat_mul_self_lt_wordModulus I)

theorem getTickLogRAfter61Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRAfter61Word I).toNat = getTickSourceLogRAfter61Nat I := by
  unfold getTickLogRAfter61Word getTickLogRShifted61Word getTickLogF61Word
    getTickLogRSquared61Word getTickSourceLogRAfter61Nat
  exact getTickLogStepRAfterWord_toNat_eq_source
    (getTickLogRAfter62Word I)
    (getTickSourceLogRAfter62Nat I)
    (getTickLogRAfter62Word_toNat_eq_source I)
    (getTickSourceLogRAfter62Nat_mul_self_lt_wordModulus I)

theorem getTickLogRShifted60Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRShifted60Word I).toNat = getTickSourceLogRShifted60Nat I := by
  unfold getTickLogRShifted60Word getTickLogRSquared60Word getTickSourceLogRShifted60Nat
  exact getTickLogStepRShiftedWord_toNat_eq_source
    (getTickLogRAfter61Word I)
    (getTickSourceLogRAfter61Nat I)
    (getTickLogRAfter61Word_toNat_eq_source I)
    (getTickSourceLogRAfter61Nat_mul_self_lt_wordModulus I)

theorem getTickLogF60Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogF60Word I).toNat = getTickSourceLogF60Nat I := by
  unfold getTickLogF60Word getTickLogRSquared60Word getTickSourceLogF60Nat
  exact getTickLogStepFWord_toNat_eq_source
    (getTickLogRAfter61Word I)
    (getTickSourceLogRAfter61Nat I)
    (getTickLogRAfter61Word_toNat_eq_source I)
    (getTickSourceLogRAfter61Nat_mul_self_lt_wordModulus I)

theorem getTickLogRAfter60Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRAfter60Word I).toNat = getTickSourceLogRAfter60Nat I := by
  unfold getTickLogRAfter60Word getTickLogRShifted60Word getTickLogF60Word
    getTickLogRSquared60Word getTickSourceLogRAfter60Nat
  exact getTickLogStepRAfterWord_toNat_eq_source
    (getTickLogRAfter61Word I)
    (getTickSourceLogRAfter61Nat I)
    (getTickLogRAfter61Word_toNat_eq_source I)
    (getTickSourceLogRAfter61Nat_mul_self_lt_wordModulus I)

theorem getTickLogRAfter59Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRAfter59Word I).toNat = getTickSourceLogRAfter59Nat I := by
  unfold getTickLogRAfter59Word getTickLogRShifted59Word getTickLogF59Word
    getTickLogRSquared59Word getTickSourceLogRAfter59Nat getTickSourceLogRAfterStep
  exact getTickLogStepRAfterWord_toNat_eq_source
    (getTickLogRAfter60Word I)
    (getTickSourceLogRAfter60Nat I)
    (getTickLogRAfter60Word_toNat_eq_source I)
    (getTickSourceLogRAfter60Nat_mul_self_lt_wordModulus I)

theorem getTickLogRAfter58Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRAfter58Word I).toNat = getTickSourceLogRAfter58Nat I := by
  unfold getTickLogRAfter58Word getTickLogRShifted58Word getTickLogF58Word
    getTickLogRSquared58Word getTickSourceLogRAfter58Nat getTickSourceLogRAfterStep
  exact getTickLogStepRAfterWord_toNat_eq_source
    (getTickLogRAfter59Word I)
    (getTickSourceLogRAfter59Nat I)
    (getTickLogRAfter59Word_toNat_eq_source I)
    (getTickSourceLogRAfter59Nat_mul_self_lt_wordModulus I)

theorem getTickLogRAfter57Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRAfter57Word I).toNat = getTickSourceLogRAfter57Nat I := by
  unfold getTickLogRAfter57Word getTickLogRShifted57Word getTickLogF57Word
    getTickLogRSquared57Word getTickSourceLogRAfter57Nat getTickSourceLogRAfterStep
  exact getTickLogStepRAfterWord_toNat_eq_source
    (getTickLogRAfter58Word I)
    (getTickSourceLogRAfter58Nat I)
    (getTickLogRAfter58Word_toNat_eq_source I)
    (getTickSourceLogRAfter58Nat_mul_self_lt_wordModulus I)

theorem getTickLogRAfter56Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRAfter56Word I).toNat = getTickSourceLogRAfter56Nat I := by
  unfold getTickLogRAfter56Word getTickLogRShifted56Word getTickLogF56Word
    getTickLogRSquared56Word getTickSourceLogRAfter56Nat getTickSourceLogRAfterStep
  exact getTickLogStepRAfterWord_toNat_eq_source
    (getTickLogRAfter57Word I)
    (getTickSourceLogRAfter57Nat I)
    (getTickLogRAfter57Word_toNat_eq_source I)
    (getTickSourceLogRAfter57Nat_mul_self_lt_wordModulus I)

theorem getTickLogRAfter55Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRAfter55Word I).toNat = getTickSourceLogRAfter55Nat I := by
  unfold getTickLogRAfter55Word getTickLogRShifted55Word getTickLogF55Word
    getTickLogRSquared55Word getTickSourceLogRAfter55Nat getTickSourceLogRAfterStep
  exact getTickLogStepRAfterWord_toNat_eq_source
    (getTickLogRAfter56Word I)
    (getTickSourceLogRAfter56Nat I)
    (getTickLogRAfter56Word_toNat_eq_source I)
    (getTickSourceLogRAfter56Nat_mul_self_lt_wordModulus I)

theorem getTickLogRAfter54Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRAfter54Word I).toNat = getTickSourceLogRAfter54Nat I := by
  unfold getTickLogRAfter54Word getTickLogRShifted54Word getTickLogF54Word
    getTickLogRSquared54Word getTickSourceLogRAfter54Nat getTickSourceLogRAfterStep
  exact getTickLogStepRAfterWord_toNat_eq_source
    (getTickLogRAfter55Word I)
    (getTickSourceLogRAfter55Nat I)
    (getTickLogRAfter55Word_toNat_eq_source I)
    (getTickSourceLogRAfter55Nat_mul_self_lt_wordModulus I)

theorem getTickLogRAfter53Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRAfter53Word I).toNat = getTickSourceLogRAfter53Nat I := by
  unfold getTickLogRAfter53Word getTickLogRShifted53Word getTickLogF53Word
    getTickLogRSquared53Word getTickSourceLogRAfter53Nat getTickSourceLogRAfterStep
  exact getTickLogStepRAfterWord_toNat_eq_source
    (getTickLogRAfter54Word I)
    (getTickSourceLogRAfter54Nat I)
    (getTickLogRAfter54Word_toNat_eq_source I)
    (getTickSourceLogRAfter54Nat_mul_self_lt_wordModulus I)

theorem getTickLogRAfter52Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRAfter52Word I).toNat = getTickSourceLogRAfter52Nat I := by
  unfold getTickLogRAfter52Word getTickLogRShifted52Word getTickLogF52Word
    getTickLogRSquared52Word getTickSourceLogRAfter52Nat getTickSourceLogRAfterStep
  exact getTickLogStepRAfterWord_toNat_eq_source
    (getTickLogRAfter53Word I)
    (getTickSourceLogRAfter53Nat I)
    (getTickLogRAfter53Word_toNat_eq_source I)
    (getTickSourceLogRAfter53Nat_mul_self_lt_wordModulus I)

theorem getTickLogRAfter51Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRAfter51Word I).toNat = getTickSourceLogRAfter51Nat I := by
  unfold getTickLogRAfter51Word getTickLogRShifted51Word getTickLogF51Word
    getTickLogRSquared51Word getTickSourceLogRAfter51Nat getTickSourceLogRAfterStep
  exact getTickLogStepRAfterWord_toNat_eq_source
    (getTickLogRAfter52Word I)
    (getTickSourceLogRAfter52Nat I)
    (getTickLogRAfter52Word_toNat_eq_source I)
    (getTickSourceLogRAfter52Nat_mul_self_lt_wordModulus I)

theorem getTickLogRShifted50Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRShifted50Word I).toNat = getTickSourceLogRShifted50Nat I := by
  unfold getTickLogRShifted50Word getTickLogRSquared50Word getTickSourceLogRShifted50Nat
  exact getTickLogStepRShiftedWord_toNat_eq_source
    (getTickLogRAfter51Word I)
    (getTickSourceLogRAfter51Nat I)
    (getTickLogRAfter51Word_toNat_eq_source I)
    (getTickSourceLogRAfter51Nat_mul_self_lt_wordModulus I)

private theorem getTickLogRSquaredWord_toNat_eq_source (r : UInt256) (rn : Nat)
    (hr : r.toNat = rn) (hmul : rn * rn < EVM.wordModulus) :
    (UInt256.mul r r).toNat = rn * rn := by
  rw [u256_mul_toNat, hr, Nat.mod_eq_of_lt]
  simpa [EVM.wordModulus] using hmul

theorem getTickLogRSquared61Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRSquared61Word I).toNat =
      getTickSourceLogRAfter62Nat I * getTickSourceLogRAfter62Nat I := by
  unfold getTickLogRSquared61Word
  exact getTickLogRSquaredWord_toNat_eq_source
    (getTickLogRAfter62Word I)
    (getTickSourceLogRAfter62Nat I)
    (getTickLogRAfter62Word_toNat_eq_source I)
    (getTickSourceLogRAfter62Nat_mul_self_lt_wordModulus I)

theorem getTickLogRSquared60Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRSquared60Word I).toNat =
      getTickSourceLogRAfter61Nat I * getTickSourceLogRAfter61Nat I := by
  unfold getTickLogRSquared60Word
  exact getTickLogRSquaredWord_toNat_eq_source
    (getTickLogRAfter61Word I)
    (getTickSourceLogRAfter61Nat I)
    (getTickLogRAfter61Word_toNat_eq_source I)
    (getTickSourceLogRAfter61Nat_mul_self_lt_wordModulus I)

theorem getTickLogRSquared59Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRSquared59Word I).toNat =
      getTickSourceLogRAfter60Nat I * getTickSourceLogRAfter60Nat I := by
  unfold getTickLogRSquared59Word
  exact getTickLogRSquaredWord_toNat_eq_source
    (getTickLogRAfter60Word I)
    (getTickSourceLogRAfter60Nat I)
    (getTickLogRAfter60Word_toNat_eq_source I)
    (getTickSourceLogRAfter60Nat_mul_self_lt_wordModulus I)

theorem getTickLogRSquared58Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRSquared58Word I).toNat =
      getTickSourceLogRAfter59Nat I * getTickSourceLogRAfter59Nat I := by
  unfold getTickLogRSquared58Word
  exact getTickLogRSquaredWord_toNat_eq_source
    (getTickLogRAfter59Word I)
    (getTickSourceLogRAfter59Nat I)
    (getTickLogRAfter59Word_toNat_eq_source I)
    (getTickSourceLogRAfter59Nat_mul_self_lt_wordModulus I)

theorem getTickLogRSquared57Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRSquared57Word I).toNat =
      getTickSourceLogRAfter58Nat I * getTickSourceLogRAfter58Nat I := by
  unfold getTickLogRSquared57Word
  exact getTickLogRSquaredWord_toNat_eq_source
    (getTickLogRAfter58Word I)
    (getTickSourceLogRAfter58Nat I)
    (getTickLogRAfter58Word_toNat_eq_source I)
    (getTickSourceLogRAfter58Nat_mul_self_lt_wordModulus I)

theorem getTickLogRSquared56Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRSquared56Word I).toNat =
      getTickSourceLogRAfter57Nat I * getTickSourceLogRAfter57Nat I := by
  unfold getTickLogRSquared56Word
  exact getTickLogRSquaredWord_toNat_eq_source
    (getTickLogRAfter57Word I)
    (getTickSourceLogRAfter57Nat I)
    (getTickLogRAfter57Word_toNat_eq_source I)
    (getTickSourceLogRAfter57Nat_mul_self_lt_wordModulus I)

theorem getTickLogRSquared55Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRSquared55Word I).toNat =
      getTickSourceLogRAfter56Nat I * getTickSourceLogRAfter56Nat I := by
  unfold getTickLogRSquared55Word
  exact getTickLogRSquaredWord_toNat_eq_source
    (getTickLogRAfter56Word I)
    (getTickSourceLogRAfter56Nat I)
    (getTickLogRAfter56Word_toNat_eq_source I)
    (getTickSourceLogRAfter56Nat_mul_self_lt_wordModulus I)

theorem getTickLogRSquared54Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRSquared54Word I).toNat =
      getTickSourceLogRAfter55Nat I * getTickSourceLogRAfter55Nat I := by
  unfold getTickLogRSquared54Word
  exact getTickLogRSquaredWord_toNat_eq_source
    (getTickLogRAfter55Word I)
    (getTickSourceLogRAfter55Nat I)
    (getTickLogRAfter55Word_toNat_eq_source I)
    (getTickSourceLogRAfter55Nat_mul_self_lt_wordModulus I)

theorem getTickLogRSquared53Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRSquared53Word I).toNat =
      getTickSourceLogRAfter54Nat I * getTickSourceLogRAfter54Nat I := by
  unfold getTickLogRSquared53Word
  exact getTickLogRSquaredWord_toNat_eq_source
    (getTickLogRAfter54Word I)
    (getTickSourceLogRAfter54Nat I)
    (getTickLogRAfter54Word_toNat_eq_source I)
    (getTickSourceLogRAfter54Nat_mul_self_lt_wordModulus I)

theorem getTickLogRSquared52Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRSquared52Word I).toNat =
      getTickSourceLogRAfter53Nat I * getTickSourceLogRAfter53Nat I := by
  unfold getTickLogRSquared52Word
  exact getTickLogRSquaredWord_toNat_eq_source
    (getTickLogRAfter53Word I)
    (getTickSourceLogRAfter53Nat I)
    (getTickLogRAfter53Word_toNat_eq_source I)
    (getTickSourceLogRAfter53Nat_mul_self_lt_wordModulus I)

theorem getTickLogRSquared51Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRSquared51Word I).toNat =
      getTickSourceLogRAfter52Nat I * getTickSourceLogRAfter52Nat I := by
  unfold getTickLogRSquared51Word
  exact getTickLogRSquaredWord_toNat_eq_source
    (getTickLogRAfter52Word I)
    (getTickSourceLogRAfter52Nat I)
    (getTickLogRAfter52Word_toNat_eq_source I)
    (getTickSourceLogRAfter52Nat_mul_self_lt_wordModulus I)

theorem getTickLogRSquared50Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLogRSquared50Word I).toNat =
      getTickSourceLogRAfter51Nat I * getTickSourceLogRAfter51Nat I := by
  unfold getTickLogRSquared50Word
  exact getTickLogRSquaredWord_toNat_eq_source
    (getTickLogRAfter51Word I)
    (getTickSourceLogRAfter51Nat I)
    (getTickLogRAfter51Word_toNat_eq_source I)
    (getTickSourceLogRAfter51Nat_mul_self_lt_wordModulus I)

private theorem nat_div_twoPow255_eq_testBit (n : Nat) (hn : n < 2 ^ (256 : Nat)) :
    n / 2 ^ (255 : Nat) = (n.testBit 255).toNat := by
  by_cases hlt : n < 2 ^ (255 : Nat)
  · have hbit : n.testBit 255 = false := Nat.testBit_lt_two_pow hlt
    have hdiv : n / 2 ^ (255 : Nat) = 0 := Nat.div_eq_of_lt hlt
    rw [hdiv, hbit]
    simp
  · have hge : 2 ^ (255 : Nat) ≤ n := Nat.le_of_not_gt hlt
    have hdiv : n / 2 ^ (255 : Nat) = 1 := by
      apply Nat.div_eq_of_lt_le (k := 1)
      · simpa using hge
      · simpa using hn
    have hbit : n.testBit 255 = true := by
      have hbit0 : (n / 2 ^ (255 : Nat)).testBit 0 = true := by
        rw [hdiv]
        decide
      rw [Nat.testBit_div_two_pow] at hbit0
      simpa using hbit0
    rw [hdiv, hbit]
    simp

private theorem nat_land_shifted_log_bit (n bit : Nat)
    (hbit : bit ≤ 255) (hn : n < 2 ^ (256 : Nat)) :
    Nat.land (n / 2 ^ (255 - bit)) (2 ^ bit) =
      (n / 2 ^ (255 : Nat)) * 2 ^ bit := by
  change (n / 2 ^ (255 - bit) &&& 2 ^ bit) =
    (n / 2 ^ (255 : Nat)) * 2 ^ bit
  rw [Nat.and_two_pow]
  rw [Nat.testBit_div_two_pow]
  rw [show bit + (255 - bit) = 255 by omega]
  rw [nat_div_twoPow255_eq_testBit n hn]

private theorem getTickLog2BitWord_toNat_of_rsq (mask rsq shift : UInt256)
    (rn bit shiftNat : Nat)
    (hmask : mask.toNat = 2 ^ bit)
    (hrsq : rsq.toNat = rn)
    (hshift : shift.toNat = shiftNat)
    (hshiftNat : shiftNat = 255 - bit)
    (hbit : bit ≤ 255)
    (hrn : rn < EVM.wordModulus) :
    (UInt256.land mask (UInt256.shiftRight rsq shift)).toNat =
      (rn / 2 ^ (255 : Nat)) * 2 ^ bit := by
  rw [u256_land_toNat]
  rw [shiftRight_toNat_of_lt_256]
  · rw [hmask, hrsq, hshift, hshiftNat]
    rw [nat_land_comm]
    rw [Nat.mod_eq_of_lt]
    · exact nat_land_shifted_log_bit rn bit hbit (by
        simpa [EVM.wordModulus, EVM.twoPow] using hrn)
    · exact lt_of_le_of_lt (nat_land_le_right _ _) (by
        have hpow : 2 ^ bit ≤ 2 ^ (255 : Nat) :=
          Nat.pow_le_pow_right (by norm_num) hbit
        exact lt_of_le_of_lt hpow (by norm_num [UInt256.size]))
  · rw [hshift, hshiftNat]
    omega

theorem getTickLog2Bit63Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLog2Bit63Word I).toNat = getTickSourceLogF63Nat I * 2 ^ (63 : Nat) := by
  unfold getTickLog2Bit63Word getTickSourceLogF63Nat getTickSourceLogRShifted63Nat
  rw [getTickLog2BitWord_toNat_of_rsq
    getTickLog2Bit63Mask (getTickLogRSquared63Word I) ⟨192⟩
    (getTickSourceRNormalizedNat I * getTickSourceRNormalizedNat I) 63 192
    (by native_decide)
    (getTickLogRSquared63Word_toNat_eq_source I)
    (by native_decide) (by norm_num) (by norm_num)
    (getTickSourceRNormalizedNat_mul_self_lt_wordModulus I)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem getTickLog2Bit62Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLog2Bit62Word I).toNat = getTickSourceLogF62Nat I * 2 ^ (62 : Nat) := by
  unfold getTickLog2Bit62Word getTickSourceLogF62Nat getTickSourceLogRShifted62Nat
  rw [getTickLog2BitWord_toNat_of_rsq
    getTickLog2Bit62Mask (getTickLogRSquared62Word I) ⟨193⟩
    (getTickSourceLogRAfter63Nat I * getTickSourceLogRAfter63Nat I) 62 193
    (by native_decide)
    (getTickLogRSquared62Word_toNat_eq_source I)
    (by native_decide) (by norm_num) (by norm_num)
    (getTickSourceLogRAfter63Nat_mul_self_lt_wordModulus I)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem getTickLog2Bit61Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLog2Bit61Word I).toNat = getTickSourceLogF61Nat I * 2 ^ (61 : Nat) := by
  unfold getTickLog2Bit61Word getTickSourceLogF61Nat getTickSourceLogStepFNat
    getTickSourceLogStepRShiftedNat
  rw [getTickLog2BitWord_toNat_of_rsq
    getTickLog2Bit61Mask (getTickLogRSquared61Word I) ⟨194⟩
    (getTickSourceLogRAfter62Nat I * getTickSourceLogRAfter62Nat I) 61 194
    (by native_decide)
    (getTickLogRSquared61Word_toNat_eq_source I)
    (by native_decide) (by norm_num) (by norm_num)
    (getTickSourceLogRAfter62Nat_mul_self_lt_wordModulus I)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem getTickLog2Bit60Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLog2Bit60Word I).toNat = getTickSourceLogF60Nat I * 2 ^ (60 : Nat) := by
  unfold getTickLog2Bit60Word getTickSourceLogF60Nat getTickSourceLogStepFNat
    getTickSourceLogStepRShiftedNat
  rw [getTickLog2BitWord_toNat_of_rsq
    getTickLog2Bit60Mask (getTickLogRSquared60Word I) ⟨195⟩
    (getTickSourceLogRAfter61Nat I * getTickSourceLogRAfter61Nat I) 60 195
    (by native_decide)
    (getTickLogRSquared60Word_toNat_eq_source I)
    (by native_decide) (by norm_num) (by norm_num)
    (getTickSourceLogRAfter61Nat_mul_self_lt_wordModulus I)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem getTickLog2Bit59Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLog2Bit59Word I).toNat =
      getTickSourceLogStepFNat (getTickSourceLogRAfter60Nat I) * 2 ^ (59 : Nat) := by
  unfold getTickLog2Bit59Word getTickSourceLogStepFNat getTickSourceLogStepRShiftedNat
  rw [getTickLog2BitWord_toNat_of_rsq
    getTickLog2Bit59Mask (getTickLogRSquared59Word I) ⟨196⟩
    (getTickSourceLogRAfter60Nat I * getTickSourceLogRAfter60Nat I) 59 196
    (by native_decide)
    (getTickLogRSquared59Word_toNat_eq_source I)
    (by native_decide) (by norm_num) (by norm_num)
    (getTickSourceLogRAfter60Nat_mul_self_lt_wordModulus I)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem getTickLog2Bit58Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLog2Bit58Word I).toNat =
      getTickSourceLogStepFNat (getTickSourceLogRAfter59Nat I) * 2 ^ (58 : Nat) := by
  unfold getTickLog2Bit58Word getTickSourceLogStepFNat getTickSourceLogStepRShiftedNat
  rw [getTickLog2BitWord_toNat_of_rsq
    getTickLog2Bit58Mask (getTickLogRSquared58Word I) ⟨197⟩
    (getTickSourceLogRAfter59Nat I * getTickSourceLogRAfter59Nat I) 58 197
    (by native_decide)
    (getTickLogRSquared58Word_toNat_eq_source I)
    (by native_decide) (by norm_num) (by norm_num)
    (getTickSourceLogRAfter59Nat_mul_self_lt_wordModulus I)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem getTickLog2Bit57Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLog2Bit57Word I).toNat =
      getTickSourceLogStepFNat (getTickSourceLogRAfter58Nat I) * 2 ^ (57 : Nat) := by
  unfold getTickLog2Bit57Word getTickSourceLogStepFNat getTickSourceLogStepRShiftedNat
  rw [getTickLog2BitWord_toNat_of_rsq
    getTickLog2Bit57Mask (getTickLogRSquared57Word I) ⟨198⟩
    (getTickSourceLogRAfter58Nat I * getTickSourceLogRAfter58Nat I) 57 198
    (by native_decide)
    (getTickLogRSquared57Word_toNat_eq_source I)
    (by native_decide) (by norm_num) (by norm_num)
    (getTickSourceLogRAfter58Nat_mul_self_lt_wordModulus I)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem getTickLog2Bit56Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLog2Bit56Word I).toNat =
      getTickSourceLogStepFNat (getTickSourceLogRAfter57Nat I) * 2 ^ (56 : Nat) := by
  unfold getTickLog2Bit56Word getTickSourceLogStepFNat getTickSourceLogStepRShiftedNat
  rw [getTickLog2BitWord_toNat_of_rsq
    getTickLog2Bit56Mask (getTickLogRSquared56Word I) ⟨199⟩
    (getTickSourceLogRAfter57Nat I * getTickSourceLogRAfter57Nat I) 56 199
    (by native_decide)
    (getTickLogRSquared56Word_toNat_eq_source I)
    (by native_decide) (by norm_num) (by norm_num)
    (getTickSourceLogRAfter57Nat_mul_self_lt_wordModulus I)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem getTickLog2Bit55Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLog2Bit55Word I).toNat =
      getTickSourceLogStepFNat (getTickSourceLogRAfter56Nat I) * 2 ^ (55 : Nat) := by
  unfold getTickLog2Bit55Word getTickSourceLogStepFNat getTickSourceLogStepRShiftedNat
  rw [getTickLog2BitWord_toNat_of_rsq
    getTickLog2Bit55Mask (getTickLogRSquared55Word I) ⟨200⟩
    (getTickSourceLogRAfter56Nat I * getTickSourceLogRAfter56Nat I) 55 200
    (by native_decide)
    (getTickLogRSquared55Word_toNat_eq_source I)
    (by native_decide) (by norm_num) (by norm_num)
    (getTickSourceLogRAfter56Nat_mul_self_lt_wordModulus I)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem getTickLog2Bit54Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLog2Bit54Word I).toNat =
      getTickSourceLogStepFNat (getTickSourceLogRAfter55Nat I) * 2 ^ (54 : Nat) := by
  unfold getTickLog2Bit54Word getTickSourceLogStepFNat getTickSourceLogStepRShiftedNat
  rw [getTickLog2BitWord_toNat_of_rsq
    getTickLog2Bit54Mask (getTickLogRSquared54Word I) ⟨201⟩
    (getTickSourceLogRAfter55Nat I * getTickSourceLogRAfter55Nat I) 54 201
    (by native_decide)
    (getTickLogRSquared54Word_toNat_eq_source I)
    (by native_decide) (by norm_num) (by norm_num)
    (getTickSourceLogRAfter55Nat_mul_self_lt_wordModulus I)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem getTickLog2Bit53Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLog2Bit53Word I).toNat =
      getTickSourceLogStepFNat (getTickSourceLogRAfter54Nat I) * 2 ^ (53 : Nat) := by
  unfold getTickLog2Bit53Word getTickSourceLogStepFNat getTickSourceLogStepRShiftedNat
  rw [getTickLog2BitWord_toNat_of_rsq
    getTickLog2Bit53Mask (getTickLogRSquared53Word I) ⟨202⟩
    (getTickSourceLogRAfter54Nat I * getTickSourceLogRAfter54Nat I) 53 202
    (by native_decide)
    (getTickLogRSquared53Word_toNat_eq_source I)
    (by native_decide) (by norm_num) (by norm_num)
    (getTickSourceLogRAfter54Nat_mul_self_lt_wordModulus I)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem getTickLog2Bit52Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLog2Bit52Word I).toNat =
      getTickSourceLogStepFNat (getTickSourceLogRAfter53Nat I) * 2 ^ (52 : Nat) := by
  unfold getTickLog2Bit52Word getTickSourceLogStepFNat getTickSourceLogStepRShiftedNat
  rw [getTickLog2BitWord_toNat_of_rsq
    getTickLog2Bit52Mask (getTickLogRSquared52Word I) ⟨203⟩
    (getTickSourceLogRAfter53Nat I * getTickSourceLogRAfter53Nat I) 52 203
    (by native_decide)
    (getTickLogRSquared52Word_toNat_eq_source I)
    (by native_decide) (by norm_num) (by norm_num)
    (getTickSourceLogRAfter53Nat_mul_self_lt_wordModulus I)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem getTickLog2Bit51Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLog2Bit51Word I).toNat =
      getTickSourceLogStepFNat (getTickSourceLogRAfter52Nat I) * 2 ^ (51 : Nat) := by
  unfold getTickLog2Bit51Word getTickSourceLogStepFNat getTickSourceLogStepRShiftedNat
  rw [getTickLog2BitWord_toNat_of_rsq
    getTickLog2Bit51Mask (getTickLogRSquared51Word I) ⟨204⟩
    (getTickSourceLogRAfter52Nat I * getTickSourceLogRAfter52Nat I) 51 204
    (by native_decide)
    (getTickLogRSquared51Word_toNat_eq_source I)
    (by native_decide) (by norm_num) (by norm_num)
    (getTickSourceLogRAfter52Nat_mul_self_lt_wordModulus I)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem getTickLog2Bit50Word_toNat_eq_source (I : ExecutionEnv) :
    (getTickLog2Bit50Word I).toNat = getTickSourceLogF50Nat I * 2 ^ (50 : Nat) := by
  unfold getTickLog2Bit50Word getTickSourceLogF50Nat getTickSourceLogStepFNat
    getTickSourceLogStepRShiftedNat
  rw [getTickLog2BitWord_toNat_of_rsq
    getTickLog2Bit50Mask (getTickLogRSquared50Word I) ⟨205⟩
    (getTickSourceLogRAfter51Nat I * getTickSourceLogRAfter51Nat I) 50 205
    (by native_decide)
    (getTickLogRSquared50Word_toNat_eq_source I)
    (by native_decide) (by norm_num) (by norm_num)
    (getTickSourceLogRAfter51Nat_mul_self_lt_wordModulus I)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem getTickLog2BaseWord_eq_source_of_msb_bounds (I : ExecutionEnv)
    (hloMsb : 64 ≤ getTickSourceMsbAfter0Nat I)
    (hhiMsb : getTickSourceMsbAfter0Nat I ≤ 191) :
    getTickLog2BaseWord I = EVM.wordOfInt (getTickSourceLog2BaseInt I) := by
  apply u256_inj
  unfold getTickLog2BaseWord getTickSourceLog2BaseInt
  rw [shiftLeft_toNat_of_lt_256]
  · rw [uadd_toNat, getTickMsbWord_toNat_eq_source I]
    have hlnot : (UInt256.lnot (⟨127⟩ : UInt256)).toNat = UInt256.size - 128 := by
      native_decide
    rw [hlnot]
    by_cases hge128 : 128 ≤ getTickSourceMsbAfter0Nat I
    · have hbaseMod :
          (getTickSourceMsbAfter0Nat I + (UInt256.size - 128)) % UInt256.size =
            getTickSourceMsbAfter0Nat I - 128 := by
        have hsum :
            getTickSourceMsbAfter0Nat I + (UInt256.size - 128) =
              UInt256.size + (getTickSourceMsbAfter0Nat I - 128) := by
          norm_num [UInt256.size]
          omega
        rw [hsum, Nat.add_mod_left]
        rw [Nat.mod_eq_of_lt]
        omega
      rw [hbaseMod]
      have hmulLt : (getTickSourceMsbAfter0Nat I - 128) * 2 ^ (64 : Nat) <
          UInt256.size := by
        have hdiff : getTickSourceMsbAfter0Nat I - 128 ≤ 63 := by omega
        exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hdiff) (by native_decide)
      change (getTickSourceMsbAfter0Nat I - 128) * 2 ^ (64 : Nat) % UInt256.size =
        (EVM.wordOfInt
          (((getTickSourceMsbAfter0Nat I : Int) - 128) * (2 ^ (64 : Nat) : Int))).toNat
      rw [Nat.mod_eq_of_lt hmulLt]
      have hsrcNonneg :
          0 ≤ ((getTickSourceMsbAfter0Nat I : Int) - 128) * (2 ^ (64 : Nat) : Int) := by
        norm_num
        omega
      have hsrcLt :
          ((getTickSourceMsbAfter0Nat I : Int) - 128) * (2 ^ (64 : Nat) : Int) <
            EVM.wordModulus := by
        norm_num [EVM.wordModulus, EVM.twoPow, UInt256.size] at hhiMsb ⊢
        omega
      rw [wordOfInt_nonneg_toNat_lt_wordModulus _ hsrcNonneg hsrcLt]
      have htoNat :
          (((getTickSourceMsbAfter0Nat I : Int) - 128) *
              (2 ^ (64 : Nat) : Int)).toNat =
            (getTickSourceMsbAfter0Nat I - 128) * 2 ^ (64 : Nat) := by
        norm_num
        omega
      rw [htoNat]
    · have hlt128 : getTickSourceMsbAfter0Nat I < 128 := Nat.lt_of_not_ge hge128
      let d := 128 - getTickSourceMsbAfter0Nat I
      have hdPos : 0 < d := by
        dsimp [d]
        omega
      have hdLe : d ≤ 64 := by
        dsimp [d]
        omega
      have hbaseMod :
          (getTickSourceMsbAfter0Nat I + (UInt256.size - 128)) % UInt256.size =
            UInt256.size - d := by
        have hsum :
            getTickSourceMsbAfter0Nat I + (UInt256.size - 128) = UInt256.size - d := by
          dsimp [d]
          norm_num [UInt256.size]
          omega
        rw [hsum]
        rw [Nat.mod_eq_of_lt]
        · exact Nat.sub_lt (by native_decide : 0 < UInt256.size) hdPos
      rw [hbaseMod]
      have hdMulPos : 0 < d * 2 ^ (64 : Nat) := Nat.mul_pos hdPos (by norm_num)
      have hdMulLe : d * 2 ^ (64 : Nat) ≤ UInt256.size := by
        exact le_trans (Nat.mul_le_mul_right _ hdLe) (by native_decide)
      have hshiftMod :
          ((UInt256.size - d) * 2 ^ (64 : Nat)) % UInt256.size =
            UInt256.size - d * 2 ^ (64 : Nat) := by
        have hdecomp :
            (UInt256.size - d) * 2 ^ (64 : Nat) =
              (UInt256.size - d * 2 ^ (64 : Nat)) +
                UInt256.size * (2 ^ (64 : Nat) - 1) := by
          norm_num [UInt256.size] at hdLe ⊢
          omega
        rw [hdecomp, Nat.add_mul_mod_self_left]
        rw [Nat.mod_eq_of_lt]
        omega
      change (UInt256.size - d) * 2 ^ (64 : Nat) % UInt256.size =
        (EVM.wordOfInt
          (((getTickSourceMsbAfter0Nat I : Int) - 128) * (2 ^ (64 : Nat) : Int))).toNat
      rw [hshiftMod]
      have hsrcNeg :
          ((getTickSourceMsbAfter0Nat I : Int) - 128) * (2 ^ (64 : Nat) : Int) < 0 := by
        norm_num
        omega
      have hsrcAbs :
          (((getTickSourceMsbAfter0Nat I : Int) - 128) *
              (2 ^ (64 : Nat) : Int)).natAbs =
            d * 2 ^ (64 : Nat) := by
        dsimp [d]
        omega
      have hsrcAbsLt :
          (((getTickSourceMsbAfter0Nat I : Int) - 128) *
              (2 ^ (64 : Nat) : Int)).natAbs < EVM.wordModulus := by
        rw [hsrcAbs]
        exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hdLe) (by native_decide)
      rw [wordOfInt_neg_toNat_lt_wordModulus _ hsrcNeg hsrcAbsLt]
      rw [hsrcAbs]
  · native_decide

private theorem nat_lor_zero_left (n : Nat) : Nat.lor 0 n = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (0 ||| n).testBit i = n.testBit i
  rw [Nat.testBit_or]
  simp

private theorem nat_lor_bit_low_add (low coeff bit : Nat)
    (hlowMod : low % 2 ^ (bit + 1) = 0)
    (hcoeff : coeff ≤ 1) :
    Nat.lor (coeff * 2 ^ bit) low = low + coeff * 2 ^ bit := by
  rcases Nat.eq_zero_or_pos coeff with hcoeff0 | hcoeffPos
  · subst coeff
    rw [Nat.zero_mul, nat_lor_zero_left]
    omega
  · have hcoeff1 : coeff = 1 := by omega
    subst coeff
    have hlowEq : low = low / 2 ^ (bit + 1) * 2 ^ (bit + 1) := by
      have h := Nat.div_add_mod low (2 ^ (bit + 1))
      rw [hlowMod, add_zero] at h
      rw [Nat.mul_comm] at h
      exact h.symm
    rw [hlowEq]
    rw [nat_lor_shift_add]
    · ring
    · rw [one_mul]
      exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self bit)

private theorem nat_lor_bit_low_high_add (q low coeff bit : Nat)
    (hlow64 : low < 2 ^ (64 : Nat))
    (hlowMod : low % 2 ^ (bit + 1) = 0)
    (hcoeff : coeff ≤ 1)
    (hnewLow : low + coeff * 2 ^ bit < 2 ^ (64 : Nat)) :
    Nat.lor (coeff * 2 ^ bit) (low + q * 2 ^ (64 : Nat)) =
      low + coeff * 2 ^ bit + q * 2 ^ (64 : Nat) := by
  have hprev : low + q * 2 ^ (64 : Nat) = Nat.lor low (q * 2 ^ (64 : Nat)) := by
    rw [nat_lor_shift_add low q 64 hlow64]
  rw [hprev]
  calc
    Nat.lor (coeff * 2 ^ bit) (Nat.lor low (q * 2 ^ (64 : Nat))) =
        Nat.lor (Nat.lor (coeff * 2 ^ bit) low) (q * 2 ^ (64 : Nat)) := by
          exact (Nat.lor_assoc (coeff * 2 ^ bit) low (q * 2 ^ (64 : Nat))).symm
    _ = Nat.lor (low + coeff * 2 ^ bit) (q * 2 ^ (64 : Nat)) := by
          rw [nat_lor_bit_low_add low coeff bit hlowMod hcoeff]
    _ = low + coeff * 2 ^ bit + q * 2 ^ (64 : Nat) := by
          rw [nat_lor_shift_add (low + coeff * 2 ^ bit) q 64 hnewLow]

private theorem getTickLog2AfterStepWord_toNat_of_prev
    (bitWord prev : UInt256) (q bits coeff bit : Nat)
    (hbitWord : bitWord.toNat = coeff * 2 ^ bit)
    (hprev : prev.toNat = bits * 2 ^ (bit + 1) + q * 2 ^ (64 : Nat))
    (hbitsLow : bits * 2 ^ (bit + 1) < 2 ^ (64 : Nat))
    (hcoeff : coeff ≤ 1)
    (hnewLow : (bits * 2 + coeff) * 2 ^ bit < 2 ^ (64 : Nat))
    (hq : q < 2 ^ (192 : Nat)) :
    (UInt256.lor bitWord prev).toNat =
      (bits * 2 + coeff) * 2 ^ bit + q * 2 ^ (64 : Nat) := by
  rw [u256_lor_toNat, hbitWord, hprev]
  have hlowMod : bits * 2 ^ (bit + 1) % 2 ^ (bit + 1) = 0 := by
    exact Nat.mul_mod_left bits (2 ^ (bit + 1))
  have hnewLow' : bits * 2 ^ (bit + 1) + coeff * 2 ^ bit < 2 ^ (64 : Nat) := by
    rw [show bits * 2 ^ (bit + 1) + coeff * 2 ^ bit =
        (bits * 2 + coeff) * 2 ^ bit by
      rw [Nat.pow_succ]
      ring]
    exact hnewLow
  rw [nat_lor_bit_low_high_add q (bits * 2 ^ (bit + 1)) coeff bit hbitsLow
    hlowMod hcoeff hnewLow']
  rw [show bits * 2 ^ (bit + 1) + coeff * 2 ^ bit =
      (bits * 2 + coeff) * 2 ^ bit by
    rw [Nat.pow_succ]
    ring]
  rw [Nat.mod_eq_of_lt]
  have hltQ : q + 1 ≤ 2 ^ (192 : Nat) := Nat.succ_le_iff.mpr hq
  calc
    (bits * 2 + coeff) * 2 ^ bit + q * 2 ^ (64 : Nat)
        < 2 ^ (64 : Nat) + q * 2 ^ (64 : Nat) := by omega
    _ = (q + 1) * 2 ^ (64 : Nat) := by ring
    _ ≤ 2 ^ (192 : Nat) * 2 ^ (64 : Nat) := by
      exact Nat.mul_le_mul_right _ hltQ
    _ = UInt256.size := by native_decide

private def getTickLog2BitsAfter63Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogF63Nat I

private def getTickLog2BitsAfter62Nat (I : ExecutionEnv) : Nat :=
  getTickLog2BitsAfter63Nat I * 2 + getTickSourceLogF62Nat I

private def getTickLog2BitsAfter61Nat (I : ExecutionEnv) : Nat :=
  getTickLog2BitsAfter62Nat I * 2 + getTickSourceLogF61Nat I

private def getTickLog2BitsAfter60Nat (I : ExecutionEnv) : Nat :=
  getTickLog2BitsAfter61Nat I * 2 + getTickSourceLogF60Nat I

private def getTickLog2BitsAfter59Nat (I : ExecutionEnv) : Nat :=
  getTickLog2BitsAfter60Nat I * 2 + getTickSourceLogStepFNat (getTickSourceLogRAfter60Nat I)

private def getTickLog2BitsAfter58Nat (I : ExecutionEnv) : Nat :=
  getTickLog2BitsAfter59Nat I * 2 + getTickSourceLogStepFNat (getTickSourceLogRAfter59Nat I)

private def getTickLog2BitsAfter57Nat (I : ExecutionEnv) : Nat :=
  getTickLog2BitsAfter58Nat I * 2 + getTickSourceLogStepFNat (getTickSourceLogRAfter58Nat I)

private def getTickLog2BitsAfter56Nat (I : ExecutionEnv) : Nat :=
  getTickLog2BitsAfter57Nat I * 2 + getTickSourceLogStepFNat (getTickSourceLogRAfter57Nat I)

private def getTickLog2BitsAfter55Nat (I : ExecutionEnv) : Nat :=
  getTickLog2BitsAfter56Nat I * 2 + getTickSourceLogStepFNat (getTickSourceLogRAfter56Nat I)

private def getTickLog2BitsAfter54Nat (I : ExecutionEnv) : Nat :=
  getTickLog2BitsAfter55Nat I * 2 + getTickSourceLogStepFNat (getTickSourceLogRAfter55Nat I)

private def getTickLog2BitsAfter53Nat (I : ExecutionEnv) : Nat :=
  getTickLog2BitsAfter54Nat I * 2 + getTickSourceLogStepFNat (getTickSourceLogRAfter54Nat I)

private def getTickLog2BitsAfter52Nat (I : ExecutionEnv) : Nat :=
  getTickLog2BitsAfter53Nat I * 2 + getTickSourceLogStepFNat (getTickSourceLogRAfter53Nat I)

private def getTickLog2BitsAfter51Nat (I : ExecutionEnv) : Nat :=
  getTickLog2BitsAfter52Nat I * 2 + getTickSourceLogStepFNat (getTickSourceLogRAfter52Nat I)

def getTickLog2BitsAfter50Nat (I : ExecutionEnv) : Nat :=
  getTickLog2BitsAfter51Nat I * 2 + getTickSourceLogF50Nat I

private theorem getTickLog2BitsAfter63Nat_lt_twoPow1 (I : ExecutionEnv) :
    getTickLog2BitsAfter63Nat I < 2 ^ (1 : Nat) := by
  unfold getTickLog2BitsAfter63Nat
  have hf := getTickSourceLogF63Nat_le_1 I
  omega

private theorem getTickLog2BitsAfter62Nat_lt_twoPow2 (I : ExecutionEnv) :
    getTickLog2BitsAfter62Nat I < 2 ^ (2 : Nat) := by
  unfold getTickLog2BitsAfter62Nat
  have hb := getTickLog2BitsAfter63Nat_lt_twoPow1 I
  have hf := getTickSourceLogF62Nat_le_1 I
  norm_num at hb hf ⊢
  omega

private theorem getTickLog2BitsAfter61Nat_lt_twoPow3 (I : ExecutionEnv) :
    getTickLog2BitsAfter61Nat I < 2 ^ (3 : Nat) := by
  unfold getTickLog2BitsAfter61Nat
  have hb := getTickLog2BitsAfter62Nat_lt_twoPow2 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter62Nat I)
    (getTickSourceLogRAfter62Nat_mul_self_lt_wordModulus I)
  have hf61 : getTickSourceLogF61Nat I ≤ 1 := by
    simpa [getTickSourceLogF61Nat] using hf
  norm_num at hb hf61 ⊢
  omega

private theorem getTickLog2BitsAfter60Nat_lt_twoPow4 (I : ExecutionEnv) :
    getTickLog2BitsAfter60Nat I < 2 ^ (4 : Nat) := by
  unfold getTickLog2BitsAfter60Nat
  have hb := getTickLog2BitsAfter61Nat_lt_twoPow3 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter61Nat I)
    (getTickSourceLogRAfter61Nat_mul_self_lt_wordModulus I)
  have hf60 : getTickSourceLogF60Nat I ≤ 1 := by
    simpa [getTickSourceLogF60Nat] using hf
  norm_num at hb hf60 ⊢
  omega

private theorem getTickLog2BitsAfter59Nat_lt_twoPow5 (I : ExecutionEnv) :
    getTickLog2BitsAfter59Nat I < 2 ^ (5 : Nat) := by
  unfold getTickLog2BitsAfter59Nat
  have hb := getTickLog2BitsAfter60Nat_lt_twoPow4 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter60Nat I)
    (getTickSourceLogRAfter60Nat_mul_self_lt_wordModulus I)
  norm_num at hb hf ⊢
  omega

private theorem getTickLog2BitsAfter58Nat_lt_twoPow6 (I : ExecutionEnv) :
    getTickLog2BitsAfter58Nat I < 2 ^ (6 : Nat) := by
  unfold getTickLog2BitsAfter58Nat
  have hb := getTickLog2BitsAfter59Nat_lt_twoPow5 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter59Nat I)
    (getTickSourceLogRAfter59Nat_mul_self_lt_wordModulus I)
  norm_num at hb hf ⊢
  omega

private theorem getTickLog2BitsAfter57Nat_lt_twoPow7 (I : ExecutionEnv) :
    getTickLog2BitsAfter57Nat I < 2 ^ (7 : Nat) := by
  unfold getTickLog2BitsAfter57Nat
  have hb := getTickLog2BitsAfter58Nat_lt_twoPow6 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter58Nat I)
    (getTickSourceLogRAfter58Nat_mul_self_lt_wordModulus I)
  norm_num at hb hf ⊢
  omega

private theorem getTickLog2BitsAfter56Nat_lt_twoPow8 (I : ExecutionEnv) :
    getTickLog2BitsAfter56Nat I < 2 ^ (8 : Nat) := by
  unfold getTickLog2BitsAfter56Nat
  have hb := getTickLog2BitsAfter57Nat_lt_twoPow7 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter57Nat I)
    (getTickSourceLogRAfter57Nat_mul_self_lt_wordModulus I)
  norm_num at hb hf ⊢
  omega

private theorem getTickLog2BitsAfter55Nat_lt_twoPow9 (I : ExecutionEnv) :
    getTickLog2BitsAfter55Nat I < 2 ^ (9 : Nat) := by
  unfold getTickLog2BitsAfter55Nat
  have hb := getTickLog2BitsAfter56Nat_lt_twoPow8 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter56Nat I)
    (getTickSourceLogRAfter56Nat_mul_self_lt_wordModulus I)
  norm_num at hb hf ⊢
  omega

private theorem getTickLog2BitsAfter54Nat_lt_twoPow10 (I : ExecutionEnv) :
    getTickLog2BitsAfter54Nat I < 2 ^ (10 : Nat) := by
  unfold getTickLog2BitsAfter54Nat
  have hb := getTickLog2BitsAfter55Nat_lt_twoPow9 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter55Nat I)
    (getTickSourceLogRAfter55Nat_mul_self_lt_wordModulus I)
  norm_num at hb hf ⊢
  omega

private theorem getTickLog2BitsAfter53Nat_lt_twoPow11 (I : ExecutionEnv) :
    getTickLog2BitsAfter53Nat I < 2 ^ (11 : Nat) := by
  unfold getTickLog2BitsAfter53Nat
  have hb := getTickLog2BitsAfter54Nat_lt_twoPow10 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter54Nat I)
    (getTickSourceLogRAfter54Nat_mul_self_lt_wordModulus I)
  norm_num at hb hf ⊢
  omega

private theorem getTickLog2BitsAfter52Nat_lt_twoPow12 (I : ExecutionEnv) :
    getTickLog2BitsAfter52Nat I < 2 ^ (12 : Nat) := by
  unfold getTickLog2BitsAfter52Nat
  have hb := getTickLog2BitsAfter53Nat_lt_twoPow11 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter53Nat I)
    (getTickSourceLogRAfter53Nat_mul_self_lt_wordModulus I)
  norm_num at hb hf ⊢
  omega

private theorem getTickLog2BitsAfter51Nat_lt_twoPow13 (I : ExecutionEnv) :
    getTickLog2BitsAfter51Nat I < 2 ^ (13 : Nat) := by
  unfold getTickLog2BitsAfter51Nat
  have hb := getTickLog2BitsAfter52Nat_lt_twoPow12 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter52Nat I)
    (getTickSourceLogRAfter52Nat_mul_self_lt_wordModulus I)
  norm_num at hb hf ⊢
  omega

theorem getTickLog2BitsAfter50Nat_lt_twoPow14 (I : ExecutionEnv) :
    getTickLog2BitsAfter50Nat I < 2 ^ (14 : Nat) := by
  unfold getTickLog2BitsAfter50Nat
  have hb := getTickLog2BitsAfter51Nat_lt_twoPow13 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter51Nat I)
    (getTickSourceLogRAfter51Nat_mul_self_lt_wordModulus I)
  have hf50 : getTickSourceLogF50Nat I ≤ 1 := by
    simpa [getTickSourceLogF50Nat] using hf
  norm_num at hb hf50 ⊢
  omega

private theorem getTickLog2After63Word_toNat_of_base (I : ExecutionEnv) (q : Nat)
    (hbase : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat))
    (hq : q < 2 ^ (192 : Nat)) :
    (getTickLog2After63Word I).toNat =
      getTickLog2BitsAfter63Nat I * 2 ^ (63 : Nat) + q * 2 ^ (64 : Nat) := by
  unfold getTickLog2After63Word
  have hf := getTickSourceLogF63Nat_le_1 I
  simpa [getTickLog2BitsAfter63Nat] using
    getTickLog2AfterStepWord_toNat_of_prev
      (getTickLog2Bit63Word I) (getTickLog2BaseWord I) q 0 (getTickSourceLogF63Nat I) 63
      (getTickLog2Bit63Word_toNat_eq_source I)
      (by simpa using hbase)
      (by norm_num)
      hf
      (by
        norm_num at hf ⊢
        omega)
      hq

private theorem getTickLog2After62Word_toNat_of_base (I : ExecutionEnv) (q : Nat)
    (hbase : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat))
    (hq : q < 2 ^ (192 : Nat)) :
    (getTickLog2After62Word I).toNat =
      getTickLog2BitsAfter62Nat I * 2 ^ (62 : Nat) + q * 2 ^ (64 : Nat) := by
  unfold getTickLog2After62Word
  have hb := getTickLog2BitsAfter63Nat_lt_twoPow1 I
  have hf := getTickSourceLogF62Nat_le_1 I
  simpa [getTickLog2BitsAfter62Nat] using
    getTickLog2AfterStepWord_toNat_of_prev
      (getTickLog2Bit62Word I) (getTickLog2After63Word I) q
      (getTickLog2BitsAfter63Nat I) (getTickSourceLogF62Nat I) 62
      (getTickLog2Bit62Word_toNat_eq_source I)
      (getTickLog2After63Word_toNat_of_base I q hbase hq)
      (by
        norm_num at hb ⊢
        omega)
      hf
      (by
        norm_num at hb hf ⊢
        omega)
      hq

private theorem getTickLog2After61Word_toNat_of_base (I : ExecutionEnv) (q : Nat)
    (hbase : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat))
    (hq : q < 2 ^ (192 : Nat)) :
    (getTickLog2After61Word I).toNat =
      getTickLog2BitsAfter61Nat I * 2 ^ (61 : Nat) + q * 2 ^ (64 : Nat) := by
  unfold getTickLog2After61Word
  have hb := getTickLog2BitsAfter62Nat_lt_twoPow2 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter62Nat I)
    (getTickSourceLogRAfter62Nat_mul_self_lt_wordModulus I)
  have hf61 : getTickSourceLogF61Nat I ≤ 1 := by
    simpa [getTickSourceLogF61Nat] using hf
  simpa [getTickLog2BitsAfter61Nat] using
    getTickLog2AfterStepWord_toNat_of_prev
      (getTickLog2Bit61Word I) (getTickLog2After62Word I) q
      (getTickLog2BitsAfter62Nat I) (getTickSourceLogF61Nat I) 61
      (getTickLog2Bit61Word_toNat_eq_source I)
      (getTickLog2After62Word_toNat_of_base I q hbase hq)
      (by
        norm_num at hb ⊢
        omega)
      hf61
      (by
        norm_num at hb hf61 ⊢
        omega)
      hq

private theorem getTickLog2After60Word_toNat_of_base (I : ExecutionEnv) (q : Nat)
    (hbase : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat))
    (hq : q < 2 ^ (192 : Nat)) :
    (getTickLog2After60Word I).toNat =
      getTickLog2BitsAfter60Nat I * 2 ^ (60 : Nat) + q * 2 ^ (64 : Nat) := by
  unfold getTickLog2After60Word
  have hb := getTickLog2BitsAfter61Nat_lt_twoPow3 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter61Nat I)
    (getTickSourceLogRAfter61Nat_mul_self_lt_wordModulus I)
  have hf60 : getTickSourceLogF60Nat I ≤ 1 := by
    simpa [getTickSourceLogF60Nat] using hf
  simpa [getTickLog2BitsAfter60Nat] using
    getTickLog2AfterStepWord_toNat_of_prev
      (getTickLog2Bit60Word I) (getTickLog2After61Word I) q
      (getTickLog2BitsAfter61Nat I) (getTickSourceLogF60Nat I) 60
      (getTickLog2Bit60Word_toNat_eq_source I)
      (getTickLog2After61Word_toNat_of_base I q hbase hq)
      (by
        norm_num at hb ⊢
        omega)
      hf60
      (by
        norm_num at hb hf60 ⊢
        omega)
      hq

private theorem getTickLog2After59Word_toNat_of_base (I : ExecutionEnv) (q : Nat)
    (hbase : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat))
    (hq : q < 2 ^ (192 : Nat)) :
    (getTickLog2After59Word I).toNat =
      getTickLog2BitsAfter59Nat I * 2 ^ (59 : Nat) + q * 2 ^ (64 : Nat) := by
  unfold getTickLog2After59Word
  have hb := getTickLog2BitsAfter60Nat_lt_twoPow4 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter60Nat I)
    (getTickSourceLogRAfter60Nat_mul_self_lt_wordModulus I)
  simpa [getTickLog2BitsAfter59Nat] using
    getTickLog2AfterStepWord_toNat_of_prev
      (getTickLog2Bit59Word I) (getTickLog2After60Word I) q
      (getTickLog2BitsAfter60Nat I)
      (getTickSourceLogStepFNat (getTickSourceLogRAfter60Nat I)) 59
      (getTickLog2Bit59Word_toNat_eq_source I)
      (getTickLog2After60Word_toNat_of_base I q hbase hq)
      (by
        norm_num at hb ⊢
        omega)
      hf
      (by
        norm_num at hb hf ⊢
        omega)
      hq

private theorem getTickLog2After58Word_toNat_of_base (I : ExecutionEnv) (q : Nat)
    (hbase : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat))
    (hq : q < 2 ^ (192 : Nat)) :
    (getTickLog2After58Word I).toNat =
      getTickLog2BitsAfter58Nat I * 2 ^ (58 : Nat) + q * 2 ^ (64 : Nat) := by
  unfold getTickLog2After58Word
  have hb := getTickLog2BitsAfter59Nat_lt_twoPow5 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter59Nat I)
    (getTickSourceLogRAfter59Nat_mul_self_lt_wordModulus I)
  simpa [getTickLog2BitsAfter58Nat] using
    getTickLog2AfterStepWord_toNat_of_prev
      (getTickLog2Bit58Word I) (getTickLog2After59Word I) q
      (getTickLog2BitsAfter59Nat I)
      (getTickSourceLogStepFNat (getTickSourceLogRAfter59Nat I)) 58
      (getTickLog2Bit58Word_toNat_eq_source I)
      (getTickLog2After59Word_toNat_of_base I q hbase hq)
      (by
        norm_num at hb ⊢
        omega)
      hf
      (by
        norm_num at hb hf ⊢
        omega)
      hq

private theorem getTickLog2After57Word_toNat_of_base (I : ExecutionEnv) (q : Nat)
    (hbase : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat))
    (hq : q < 2 ^ (192 : Nat)) :
    (getTickLog2After57Word I).toNat =
      getTickLog2BitsAfter57Nat I * 2 ^ (57 : Nat) + q * 2 ^ (64 : Nat) := by
  unfold getTickLog2After57Word
  have hb := getTickLog2BitsAfter58Nat_lt_twoPow6 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter58Nat I)
    (getTickSourceLogRAfter58Nat_mul_self_lt_wordModulus I)
  simpa [getTickLog2BitsAfter57Nat] using
    getTickLog2AfterStepWord_toNat_of_prev
      (getTickLog2Bit57Word I) (getTickLog2After58Word I) q
      (getTickLog2BitsAfter58Nat I)
      (getTickSourceLogStepFNat (getTickSourceLogRAfter58Nat I)) 57
      (getTickLog2Bit57Word_toNat_eq_source I)
      (getTickLog2After58Word_toNat_of_base I q hbase hq)
      (by
        norm_num at hb ⊢
        omega)
      hf
      (by
        norm_num at hb hf ⊢
        omega)
      hq

private theorem getTickLog2After56Word_toNat_of_base (I : ExecutionEnv) (q : Nat)
    (hbase : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat))
    (hq : q < 2 ^ (192 : Nat)) :
    (getTickLog2After56Word I).toNat =
      getTickLog2BitsAfter56Nat I * 2 ^ (56 : Nat) + q * 2 ^ (64 : Nat) := by
  unfold getTickLog2After56Word
  have hb := getTickLog2BitsAfter57Nat_lt_twoPow7 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter57Nat I)
    (getTickSourceLogRAfter57Nat_mul_self_lt_wordModulus I)
  simpa [getTickLog2BitsAfter56Nat] using
    getTickLog2AfterStepWord_toNat_of_prev
      (getTickLog2Bit56Word I) (getTickLog2After57Word I) q
      (getTickLog2BitsAfter57Nat I)
      (getTickSourceLogStepFNat (getTickSourceLogRAfter57Nat I)) 56
      (getTickLog2Bit56Word_toNat_eq_source I)
      (getTickLog2After57Word_toNat_of_base I q hbase hq)
      (by
        norm_num at hb ⊢
        omega)
      hf
      (by
        norm_num at hb hf ⊢
        omega)
      hq

private theorem getTickLog2After55Word_toNat_of_base (I : ExecutionEnv) (q : Nat)
    (hbase : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat))
    (hq : q < 2 ^ (192 : Nat)) :
    (getTickLog2After55Word I).toNat =
      getTickLog2BitsAfter55Nat I * 2 ^ (55 : Nat) + q * 2 ^ (64 : Nat) := by
  unfold getTickLog2After55Word
  have hb := getTickLog2BitsAfter56Nat_lt_twoPow8 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter56Nat I)
    (getTickSourceLogRAfter56Nat_mul_self_lt_wordModulus I)
  simpa [getTickLog2BitsAfter55Nat] using
    getTickLog2AfterStepWord_toNat_of_prev
      (getTickLog2Bit55Word I) (getTickLog2After56Word I) q
      (getTickLog2BitsAfter56Nat I)
      (getTickSourceLogStepFNat (getTickSourceLogRAfter56Nat I)) 55
      (getTickLog2Bit55Word_toNat_eq_source I)
      (getTickLog2After56Word_toNat_of_base I q hbase hq)
      (by
        norm_num at hb ⊢
        omega)
      hf
      (by
        norm_num at hb hf ⊢
        omega)
      hq

private theorem getTickLog2After54Word_toNat_of_base (I : ExecutionEnv) (q : Nat)
    (hbase : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat))
    (hq : q < 2 ^ (192 : Nat)) :
    (getTickLog2After54Word I).toNat =
      getTickLog2BitsAfter54Nat I * 2 ^ (54 : Nat) + q * 2 ^ (64 : Nat) := by
  unfold getTickLog2After54Word
  have hb := getTickLog2BitsAfter55Nat_lt_twoPow9 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter55Nat I)
    (getTickSourceLogRAfter55Nat_mul_self_lt_wordModulus I)
  simpa [getTickLog2BitsAfter54Nat] using
    getTickLog2AfterStepWord_toNat_of_prev
      (getTickLog2Bit54Word I) (getTickLog2After55Word I) q
      (getTickLog2BitsAfter55Nat I)
      (getTickSourceLogStepFNat (getTickSourceLogRAfter55Nat I)) 54
      (getTickLog2Bit54Word_toNat_eq_source I)
      (getTickLog2After55Word_toNat_of_base I q hbase hq)
      (by
        norm_num at hb ⊢
        omega)
      hf
      (by
        norm_num at hb hf ⊢
        omega)
      hq

private theorem getTickLog2After53Word_toNat_of_base (I : ExecutionEnv) (q : Nat)
    (hbase : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat))
    (hq : q < 2 ^ (192 : Nat)) :
    (getTickLog2After53Word I).toNat =
      getTickLog2BitsAfter53Nat I * 2 ^ (53 : Nat) + q * 2 ^ (64 : Nat) := by
  unfold getTickLog2After53Word
  have hb := getTickLog2BitsAfter54Nat_lt_twoPow10 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter54Nat I)
    (getTickSourceLogRAfter54Nat_mul_self_lt_wordModulus I)
  simpa [getTickLog2BitsAfter53Nat] using
    getTickLog2AfterStepWord_toNat_of_prev
      (getTickLog2Bit53Word I) (getTickLog2After54Word I) q
      (getTickLog2BitsAfter54Nat I)
      (getTickSourceLogStepFNat (getTickSourceLogRAfter54Nat I)) 53
      (getTickLog2Bit53Word_toNat_eq_source I)
      (getTickLog2After54Word_toNat_of_base I q hbase hq)
      (by
        norm_num at hb ⊢
        omega)
      hf
      (by
        norm_num at hb hf ⊢
        omega)
      hq

private theorem getTickLog2After52Word_toNat_of_base (I : ExecutionEnv) (q : Nat)
    (hbase : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat))
    (hq : q < 2 ^ (192 : Nat)) :
    (getTickLog2After52Word I).toNat =
      getTickLog2BitsAfter52Nat I * 2 ^ (52 : Nat) + q * 2 ^ (64 : Nat) := by
  unfold getTickLog2After52Word
  have hb := getTickLog2BitsAfter53Nat_lt_twoPow11 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter53Nat I)
    (getTickSourceLogRAfter53Nat_mul_self_lt_wordModulus I)
  simpa [getTickLog2BitsAfter52Nat] using
    getTickLog2AfterStepWord_toNat_of_prev
      (getTickLog2Bit52Word I) (getTickLog2After53Word I) q
      (getTickLog2BitsAfter53Nat I)
      (getTickSourceLogStepFNat (getTickSourceLogRAfter53Nat I)) 52
      (getTickLog2Bit52Word_toNat_eq_source I)
      (getTickLog2After53Word_toNat_of_base I q hbase hq)
      (by
        norm_num at hb ⊢
        omega)
      hf
      (by
        norm_num at hb hf ⊢
        omega)
      hq

private theorem getTickLog2After51Word_toNat_of_base (I : ExecutionEnv) (q : Nat)
    (hbase : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat))
    (hq : q < 2 ^ (192 : Nat)) :
    (getTickLog2After51Word I).toNat =
      getTickLog2BitsAfter51Nat I * 2 ^ (51 : Nat) + q * 2 ^ (64 : Nat) := by
  unfold getTickLog2After51Word
  have hb := getTickLog2BitsAfter52Nat_lt_twoPow12 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter52Nat I)
    (getTickSourceLogRAfter52Nat_mul_self_lt_wordModulus I)
  simpa [getTickLog2BitsAfter51Nat] using
    getTickLog2AfterStepWord_toNat_of_prev
      (getTickLog2Bit51Word I) (getTickLog2After52Word I) q
      (getTickLog2BitsAfter52Nat I)
      (getTickSourceLogStepFNat (getTickSourceLogRAfter52Nat I)) 51
      (getTickLog2Bit51Word_toNat_eq_source I)
      (getTickLog2After52Word_toNat_of_base I q hbase hq)
      (by
        norm_num at hb ⊢
        omega)
      hf
      (by
        norm_num at hb hf ⊢
        omega)
      hq

theorem getTickLog2After50Word_toNat_of_base (I : ExecutionEnv) (q : Nat)
    (hbase : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat))
    (hq : q < 2 ^ (192 : Nat)) :
    (getTickLog2After50Word I).toNat =
      getTickLog2BitsAfter50Nat I * 2 ^ (50 : Nat) + q * 2 ^ (64 : Nat) := by
  unfold getTickLog2After50Word
  have hb := getTickLog2BitsAfter51Nat_lt_twoPow13 I
  have hf := getTickSourceLogStepFNat_le_1 (getTickSourceLogRAfter51Nat I)
    (getTickSourceLogRAfter51Nat_mul_self_lt_wordModulus I)
  have hf50 : getTickSourceLogF50Nat I ≤ 1 := by
    simpa [getTickSourceLogF50Nat] using hf
  simpa [getTickLog2BitsAfter50Nat] using
    getTickLog2AfterStepWord_toNat_of_prev
      (getTickLog2Bit50Word I) (getTickLog2After51Word I) q
      (getTickLog2BitsAfter51Nat I) (getTickSourceLogF50Nat I) 50
      (getTickLog2Bit50Word_toNat_eq_source I)
      (getTickLog2After51Word_toNat_of_base I q hbase hq)
      (by
        norm_num at hb ⊢
        omega)
      hf50
      (by
        norm_num at hb hf50 ⊢
        omega)
      hq

theorem getTickSourceLog2After50Int_eq_base_add_bits (I : ExecutionEnv) :
    getTickSourceLog2After50Int I =
      getTickSourceLog2BaseInt I +
        (getTickLog2BitsAfter50Nat I : Int) * (2 ^ (50 : Nat) : Int) := by
  unfold getTickSourceLog2After50Int getTickSourceLog2After51Int
    getTickSourceLog2After52Int getTickSourceLog2After53Int getTickSourceLog2After54Int
    getTickSourceLog2After55Int getTickSourceLog2After56Int getTickSourceLog2After57Int
    getTickSourceLog2After58Int getTickSourceLog2After59Int getTickSourceLog2After60Int
    getTickSourceLog2After61Int getTickSourceLog2After62Int getTickSourceLog2After63Int
    getTickSourceLog2AfterStep getTickSourceLogStepLog2AfterInt
    getTickLog2BitsAfter50Nat getTickLog2BitsAfter51Nat getTickLog2BitsAfter52Nat
    getTickLog2BitsAfter53Nat getTickLog2BitsAfter54Nat getTickLog2BitsAfter55Nat
    getTickLog2BitsAfter56Nat getTickLog2BitsAfter57Nat getTickLog2BitsAfter58Nat
    getTickLog2BitsAfter59Nat getTickLog2BitsAfter60Nat getTickLog2BitsAfter61Nat
    getTickLog2BitsAfter62Nat getTickLog2BitsAfter63Nat getTickSourceLogF61Nat
    getTickSourceLogF60Nat getTickSourceLogF50Nat
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring_nf

end Benchmarks.UniswapV3Pool
