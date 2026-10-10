import Benchmarks.UniswapV3.Pool.AmountDeltaBounds
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_059
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_060

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def amountDeltaEntry (second : Bool) : Nat := if second then 18002 else 18125

def amountDeltaSortExit (second : Bool) : Nat := if second then 18034 else 18157

def amountDeltaEntryWords (a : AmountDeltaArgs) : List UInt256 :=
  [a.roundUp.toUInt256, a.liquidity, a.sqrtB, a.sqrtA]

def amountDeltaSortedWords (a : AmountDeltaArgs) : List UInt256 :=
  [⟨0⟩, a.roundUp.toUInt256, a.liquidity, amountDeltaUpper a, amountDeltaLower a]

theorem amountDeltaMask160 : UInt256.sub
    (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1) =
    UInt256.ofNat (2 ^ 160 - 1) := by native_decide

def amountDeltaRawLower (a : AmountDeltaArgs) (sqrtARaw sqrtBRaw : UInt256) : UInt256 :=
  if a.sqrtB.toNat < a.sqrtA.toNat then sqrtBRaw else sqrtARaw

def amountDeltaRawUpper (a : AmountDeltaArgs) (sqrtARaw sqrtBRaw : UInt256) : UInt256 :=
  if a.sqrtB.toNat < a.sqrtA.toNat then sqrtARaw else sqrtBRaw

def amountDeltaRawEntryWords (a : AmountDeltaArgs)
    (sqrtARaw sqrtBRaw liquidityRaw : UInt256) : List UInt256 :=
  [a.roundUp.toUInt256, liquidityRaw, sqrtBRaw, sqrtARaw]

def amountDeltaRawSortedWords (a : AmountDeltaArgs)
    (sqrtARaw sqrtBRaw liquidityRaw : UInt256) : List UInt256 :=
  [⟨0⟩, a.roundUp.toUInt256, liquidityRaw, amountDeltaRawUpper a sqrtARaw sqrtBRaw,
    amountDeltaRawLower a sqrtARaw sqrtBRaw]

theorem amountDeltaRawSortedClean (a : AmountDeltaArgs) (sqrtARaw sqrtBRaw : UInt256)
    (hA : UInt256.land sqrtARaw (UInt256.ofNat (2 ^ 160 - 1)) = a.sqrtA)
    (hB : UInt256.land sqrtBRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.sqrtB) :
    UInt256.land (amountDeltaRawLower a sqrtARaw sqrtBRaw) (UInt256.ofNat (2 ^ 160 - 1)) =
      amountDeltaLower a ∧
    UInt256.land (amountDeltaRawUpper a sqrtARaw sqrtBRaw) (UInt256.ofNat (2 ^ 160 - 1)) =
      amountDeltaUpper a := by
  by_cases hs : a.sqrtB.toNat < a.sqrtA.toNat <;>
    simp only [amountDeltaRawLower, amountDeltaRawUpper, amountDeltaLower, amountDeltaUpper,
      hs, if_true, if_false, hA, hB, and_self]

theorem amountDeltaRawSortX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool) (a : AmountDeltaArgs)
    (sqrtARaw sqrtBRaw liquidityRaw : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (amountDeltaEntry second))
      (amountDeltaRawEntryWords a sqrtARaw sqrtBRaw liquidityRaw ++ ret :: R) mem aw rdata σ k C)
    (hA : UInt256.land sqrtARaw (UInt256.ofNat (2 ^ 160 - 1)) = a.sqrtA)
    (hB : UInt256.land sqrtBRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.sqrtB)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat (amountDeltaSortExit second))
      (amountDeltaRawSortedWords a sqrtARaw sqrtBRaw liquidityRaw ++ ret :: R)
      mem aw rdata σ k' C' := by
  have ha : UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 160)) (UInt256.ofNat 1)) sqrtARaw = a.sqrtA := by
    rw [amountDeltaMask160, u256_land_comm, hA]
  have hb : UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 160)) (UInt256.ofNat 1)) sqrtBRaw = a.sqrtB := by
    rw [amountDeltaMask160, u256_land_comm, hB]
  by_cases hs : a.sqrtB.toNat < a.sqrtA.toNat
  · have hc : UInt256.isZero (UInt256.gt
        (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1)) sqrtARaw)
        (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1)) sqrtBRaw)) = UInt256.ofNat 0 := by
      rw [ha, hb, ugt_one hs]
      rfl
    have r1 : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (if second then 18031 else 18154))
        (⟨0⟩ :: a.roundUp.toUInt256 :: liquidityRaw :: sqrtBRaw :: sqrtARaw :: ret :: R)
        mem aw rdata σ (k + 20) (C + 65) := by
      cases second
      · exact uniswapV3Pool_block_18125_fallthrough (immWords := wordsOf (immStore v))
          (by evm_ov) hc rd
      · exact uniswapV3Pool_block_18002_fallthrough (immWords := wordsOf (immStore v))
          (by evm_ov) hc rd
    have r2 : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (amountDeltaSortExit second))
        (⟨0⟩ :: a.roundUp.toUInt256 :: liquidityRaw :: sqrtARaw :: sqrtBRaw :: ret :: R)
        mem aw rdata σ (k + 20 + 3) (C + 65 + 9) := by
      cases second
      · exact uniswapV3Pool_block_18154 (immWords := wordsOf (immStore v)) (by evm_ov) r1
      · exact uniswapV3Pool_block_18031 (immWords := wordsOf (immStore v)) (by evm_ov) r1
    simp only [amountDeltaRawSortedWords, amountDeltaRawUpper, amountDeltaRawLower, if_pos hs,
      List.cons_append, List.nil_append]
    exact ⟨_, _, r2⟩
  · have hc : UInt256.isZero (UInt256.gt
        (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1)) sqrtARaw)
        (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1)) sqrtBRaw)) ≠ UInt256.ofNat 0 := by
      rw [ha, hb, ugt_zero (Nat.le_of_not_gt hs)]
      decide
    have r1 : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (amountDeltaSortExit second))
        (⟨0⟩ :: a.roundUp.toUInt256 :: liquidityRaw :: sqrtBRaw :: sqrtARaw :: ret :: R)
        mem aw rdata σ (k + 20) (C + 65) := by
      cases second
      · exact uniswapV3Pool_block_18125_taken (immWords := wordsOf (immStore v))
          (by evm_ov) hc (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      · exact uniswapV3Pool_block_18002_taken (immWords := wordsOf (immStore v))
          (by evm_ov) hc (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [amountDeltaRawSortedWords, amountDeltaRawUpper, amountDeltaRawLower, if_neg hs,
      List.cons_append, List.nil_append]
    exact ⟨_, _, r1⟩

theorem amountDeltaSortX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool) (a : AmountDeltaArgs)
    (rd : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (amountDeltaEntry second))
      (amountDeltaEntryWords a ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat (amountDeltaSortExit second))
      (amountDeltaSortedWords a ++ ret :: R) mem aw rdata σ k' C' := by
  have hA := u256LandMaskCleanOfToNat (bits := 160) a.sqrtA
    (UInt256.ofNat (2 ^ 160 - 1)) (by decide) hfit.1
  have hB := u256LandMaskCleanOfToNat (bits := 160) a.sqrtB
    (UInt256.ofNat (2 ^ 160 - 1)) (by decide) hfit.2.1
  obtain ⟨kr, Cr, rr⟩ := amountDeltaRawSortX (v := v) second a a.sqrtA a.sqrtB a.liquidity
    rd hA hB hov
  refine ⟨kr, Cr, ?_⟩
  simpa only [amountDeltaRawSortedWords, amountDeltaRawUpper, amountDeltaRawLower,
    amountDeltaSortedWords, amountDeltaUpper, amountDeltaLower] using rr

end Benchmarks.UniswapV3.Pool
