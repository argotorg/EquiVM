import Benchmarks.Morpho.MorphoBlue.LiquidateIncentiveMath
import Benchmarks.Morpho.MorphoBlue.WadDivUpSource
import Benchmarks.Morpho.MorphoBlue.MulDivUpRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: equivalent operand ordering in solc's multiplication check.
theorem checkedMulGuard_alt (x y : UInt256) :
    UInt256.isZero (UInt256.lor (UInt256.isZero x)
      (UInt256.eq y (UInt256.div (UInt256.mul x y) x))) = checkedMulGuard x y := by
  rw [u256_lor_comm, uInt256_eq_comm]
  rfl

theorem liquidationFactor_evm (lltv : UInt256) :
    UInt256.xor liquidationCap (UInt256.mul (UInt256.gt liquidationCap
      (UInt256.div oraclePriceScale (liquidationDenom lltv)))
      (UInt256.xor liquidationCap (UInt256.div oraclePriceScale (liquidationDenom lltv)))) =
      liquidationFactor lltv := by
  rw [minWord_evm, liquidationFactor, wDivDownResult, liquidationWadSquare]

theorem liquidationFactor_evm_alt (lltv : UInt256) :
    UInt256.xor (UInt256.mul (UInt256.xor liquidationCap (UInt256.div oraclePriceScale (liquidationDenom lltv)))
      (UInt256.lt (UInt256.div oraclePriceScale (liquidationDenom lltv)) liquidationCap)) liquidationCap =
      liquidationFactor lltv := by
  rw [minWord_evm_alt, liquidationFactor, wDivDownResult, liquidationWadSquare]

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
  {total lltv : UInt256} {R : List UInt256}

theorem morphoLiquidateWDivReachAdd (hstack : R.length + 14 ≤ 1024)
    (hl : lltv.toNat ≤ wad.toNat)
    (hf : (UInt256.div total oraclePriceScale).toNat * wad.toNat < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1785)
      (total :: liquidationDenom lltv :: R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12651)
      ([UInt256.mul (UInt256.div total oraclePriceScale) wad,
        UInt256.sub (liquidationFactor lltv) (UInt256.ofNat 1), UInt256.ofNat 2004,
        liquidationFactor lltv, UInt256.ofNat 2009, UInt256.ofNat 2055] ++ R) mem aw out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_1785_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 4 ≤ 1024; omega)
    (by rw [checkedMulGuard_alt]; exact checkedMulGuard_ok _ _ hf) h
  have hfactor := liquidationFactor_evm lltv
  dsimp only [liquidationCap, oraclePriceScale] at hfactor
  have rd2 := morphoBlocks.morpho_block_1834_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (by rw [hfactor, wordAddNegOne]; exact checkedSubGuard_ok _ _ (liquidationFactor_positive hl)) rd1
  have rd3 := morphoBlocks.morpho_block_1911 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  dsimp only [morphoBlocks.morpho_block_1911_stack, morphoBlocks.morpho_block_1834_fallthrough_stack] at rd3
  rw [hfactor, wordAddNegOne, u256_mul_comm] at rd3
  exact ⟨_, _, rd3⟩

theorem morphoLiquidateWDivOk (hstack : R.length + 14 ≤ 1024) (hl : lltv.toNat ≤ wad.toNat)
    (hf : MulDivUpFits (UInt256.div total oraclePriceScale) wad (liquidationFactor lltv))
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1785)
      (total :: liquidationDenom lltv :: R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2009)
      (wDivUpResult (UInt256.div total oraclePriceScale) (liquidationFactor lltv) :: UInt256.ofNat 2055 :: R)
      mem aw out σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := morphoLiquidateWDivReachAdd (v := v) hstack hl hf.1 h
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedAddOk (v := v) (by change R.length + 3 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hf.2.2 rd1
  have rd3 := morphoBlocks.morpho_block_2004 (immWords := wordsOf (immStore v))
    (by change R.length + 4 + 1 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact morphoCheckedDivOk (v := v) (by change R.length + 1 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest)
    (fun hz ↦ by have hn := hf.2.1; rw [hz] at hn; contradiction) rd3

theorem morphoLiquidateWDivReverts (hstack : R.length + 14 ≤ 1024) (hl : lltv.toNat ≤ wad.toNat)
    (hf : ¬ MulDivUpFits (UInt256.div total oraclePriceScale) wad (liquidationFactor lltv))
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1785)
      (total :: liquidationDenom lltv :: R) mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  by_cases hp : (UInt256.div total oraclePriceScale).toNat * wad.toNat < UInt256.size
  swap
  · have rd1 := morphoBlocks.morpho_block_1785_taken (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [checkedMulGuard_alt]; change checkedMulGuard (UInt256.div total oraclePriceScale) wad ≠ _
          rw [checkedMulGuard_overflow _ _ (Nat.le_of_not_gt hp)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact morphoBlocks.morpho_block_3277 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 2 ≤ 1024; omega) rd1
  obtain ⟨k1, C1, rd1⟩ := morphoLiquidateWDivReachAdd (v := v) hstack hl hp h
  exact morphoCheckedAddReverts (v := v) (by change R.length + 3 + 6 ≤ 1024; omega)
    (Nat.le_of_not_gt (fun ha ↦ hf ⟨hp, liquidationFactor_positive hl, ha⟩)) rd1

end Reach
end Benchmarks.Morpho.MorphoBlue
