import Benchmarks.UniswapV3Pool.InitializeGetTickWordBridge

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

private theorem getTickLog2LowAfter50Nat_lt_twoPow64 (I : ExecutionEnv) :
    getTickLog2BitsAfter50Nat I * 2 ^ (50 : Nat) < 2 ^ (64 : Nat) := by
  have hb := getTickLog2BitsAfter50Nat_lt_twoPow14 I
  norm_num at hb ⊢
  omega

theorem getTickLog2After50Word_eq_source_of_msb_bounds (I : ExecutionEnv)
    (hloMsb : 64 ≤ getTickSourceMsbAfter0Nat I)
    (hhiMsb : getTickSourceMsbAfter0Nat I ≤ 191) :
    getTickLog2After50Word I = EVM.wordOfInt (getTickSourceLog2After50Int I) := by
  apply u256_inj
  have hbaseWord := getTickLog2BaseWord_eq_source_of_msb_bounds I hloMsb hhiMsb
  have hlowLt := getTickLog2LowAfter50Nat_lt_twoPow64 I
  have hlowIntLt :
      (getTickLog2BitsAfter50Nat I : Int) * (2 ^ (50 : Nat) : Int) <
        (2 ^ (64 : Nat) : Int) := by
    exact_mod_cast hlowLt
  rw [getTickSourceLog2After50Int_eq_base_add_bits I]
  by_cases hge128 : 128 ≤ getTickSourceMsbAfter0Nat I
  · let q := getTickSourceMsbAfter0Nat I - 128
    have hq : q < 2 ^ (192 : Nat) := by
      dsimp [q]
      omega
    have hbaseToNat : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat) := by
      rw [hbaseWord]
      unfold getTickSourceLog2BaseInt
      have hbaseNonneg :
          0 ≤ ((getTickSourceMsbAfter0Nat I : Int) - 128) *
            (2 ^ (64 : Nat) : Int) := by
        norm_num
        omega
      have hbaseLt :
          ((getTickSourceMsbAfter0Nat I : Int) - 128) *
              (2 ^ (64 : Nat) : Int) < EVM.wordModulus := by
        norm_num [EVM.wordModulus, EVM.twoPow] at hhiMsb ⊢
        omega
      rw [wordOfInt_nonneg_toNat_lt_wordModulus _ hbaseNonneg hbaseLt]
      dsimp [q]
      omega
    rw [getTickLog2After50Word_toNat_of_base I q hbaseToNat hq]
    have hsrcNonneg :
        0 ≤ getTickSourceLog2BaseInt I +
          (getTickLog2BitsAfter50Nat I : Int) * (2 ^ (50 : Nat) : Int) := by
      unfold getTickSourceLog2BaseInt
      norm_num
      omega
    have hsrcLt :
        getTickSourceLog2BaseInt I +
            (getTickLog2BitsAfter50Nat I : Int) * (2 ^ (50 : Nat) : Int) <
          EVM.wordModulus := by
      unfold getTickSourceLog2BaseInt
      norm_num [EVM.wordModulus, EVM.twoPow] at hhiMsb hlowIntLt ⊢
      omega
    rw [wordOfInt_nonneg_toNat_lt_wordModulus _ hsrcNonneg hsrcLt]
    dsimp [q]
    unfold getTickSourceLog2BaseInt
    norm_num
    omega
  · have hlt128 : getTickSourceMsbAfter0Nat I < 128 := Nat.lt_of_not_ge hge128
    let d := 128 - getTickSourceMsbAfter0Nat I
    let q := 2 ^ (192 : Nat) - d
    have hdPos : 0 < d := by
      dsimp [d]
      omega
    have hdLe : d ≤ 64 := by
      dsimp [d]
      omega
    have hq : q < 2 ^ (192 : Nat) := by
      dsimp [q]
      omega
    have hbaseToNat : (getTickLog2BaseWord I).toNat = q * 2 ^ (64 : Nat) := by
      rw [hbaseWord]
      unfold getTickSourceLog2BaseInt
      have hbaseNeg :
          ((getTickSourceMsbAfter0Nat I : Int) - 128) *
              (2 ^ (64 : Nat) : Int) < 0 := by
        norm_num
        omega
      have hbaseAbs :
          (((getTickSourceMsbAfter0Nat I : Int) - 128) *
              (2 ^ (64 : Nat) : Int)).natAbs =
            d * 2 ^ (64 : Nat) := by
        dsimp [d]
        omega
      have hbaseAbsLt :
          (((getTickSourceMsbAfter0Nat I : Int) - 128) *
              (2 ^ (64 : Nat) : Int)).natAbs < EVM.wordModulus := by
        rw [hbaseAbs]
        exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hdLe) (by native_decide)
      rw [wordOfInt_neg_toNat_lt_wordModulus _ hbaseNeg hbaseAbsLt]
      rw [hbaseAbs]
      dsimp [q, d]
      norm_num [UInt256.size, EVM.wordModulus, EVM.twoPow]
      omega
    rw [getTickLog2After50Word_toNat_of_base I q hbaseToNat hq]
    have hsrcNeg :
        getTickSourceLog2BaseInt I +
            (getTickLog2BitsAfter50Nat I : Int) * (2 ^ (50 : Nat) : Int) < 0 := by
      unfold getTickSourceLog2BaseInt
      dsimp [d]
      norm_num at hlowIntLt ⊢
      omega
    have hsrcAbs :
        (getTickSourceLog2BaseInt I +
            (getTickLog2BitsAfter50Nat I : Int) * (2 ^ (50 : Nat) : Int)).natAbs =
          d * 2 ^ (64 : Nat) - getTickLog2BitsAfter50Nat I * 2 ^ (50 : Nat) := by
      unfold getTickSourceLog2BaseInt
      dsimp [d]
      norm_num at hlowIntLt ⊢
      omega
    have hsrcAbsLt :
        (getTickSourceLog2BaseInt I +
            (getTickLog2BitsAfter50Nat I : Int) * (2 ^ (50 : Nat) : Int)).natAbs <
          EVM.wordModulus := by
      rw [hsrcAbs]
      exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_le_of_lt
        (Nat.mul_le_mul_right _ hdLe) (by native_decide))
    rw [wordOfInt_neg_toNat_lt_wordModulus _ hsrcNeg hsrcAbsLt]
    rw [hsrcAbs]
    dsimp [q, d]
    norm_num [UInt256.size, EVM.wordModulus, EVM.twoPow] at hlowLt ⊢
    omega

end Benchmarks.UniswapV3Pool
