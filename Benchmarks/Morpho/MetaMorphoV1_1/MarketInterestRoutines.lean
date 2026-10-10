import Benchmarks.Morpho.MetaMorphoV1_1.MarketInterestSource
import Benchmarks.Morpho.MetaMorphoV1_1.TaylorRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MarketDecodeRoutines

/-! The active-accrual arithmetic up to its first allocating uint128 cast. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem marketInterestRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {assets rate elapsed feePtr borrowPtr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 17 ≤ 1024)
    (ha : assets.toNat < 2 ^ 128) (hload : memLoad borrowPtr mem = assets)
    (rd : RD (deployedRuntime v) I g s0 ⟨17239⟩
      (⟨17338⟩ :: elapsed :: feePtr :: rate :: borrowPtr :: R) mem aw rdata σ k C) :
    (¬ marketInterestFits assets rate elapsed ∧ RDrev (deployedRuntime v) g s0) ∨
    (marketInterestFits assets rate elapsed ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨19367⟩
        (marketInterest assets rate elapsed :: ⟨17353⟩ :: ⟨17362⟩ :: uint128Mask ::
          borrowPtr :: feePtr :: uint128Mask :: marketInterest assets rate elapsed :: R)
        mem aw' rdata σ k' C') := by
  have hmask := u256LandMaskCleanOfToNat assets uint128Mask (by decide +kernel) ha
  dsimp only [uint128Mask] at hmask
  have h0 := metaMorphoV1_1_block_17239 (immWords := wordsOf (immStore v))
    (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_17239_stack, hload, hmask] at h0
  rcases taylorRoutine v (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h0 with
    ⟨hbad, hrev⟩ | ⟨hfit, k1, C1, h1⟩
  · exact .inl ⟨fun h ↦ hbad h.1, hrev⟩
  have h2 := metaMorphoV1_1_block_17332 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  by_cases hp : assets.toNat * (taylorSum (UInt256.mul rate elapsed)).toNat < UInt256.size
  · obtain ⟨k3, C3, h3⟩ := checkedMulReturn v
      (by simp only [List.length_cons]; omega) hp
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
    have h4 := metaMorphoV1_1_block_17338 (immWords := wordsOf (immStore v))
      (by omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    exact .inr ⟨⟨hfit, hp⟩, _, _, _, h4⟩
  · exact .inl ⟨fun h ↦ hp h.2, checkedMulRevert v
      (by simp only [List.length_cons]; omega) (Nat.le_of_not_lt hp) h2⟩

theorem marketInterestSimulation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem market : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {rate elapsed feePtr borrowPtr : UInt256} {R : List UInt256}
    {frame : Frame} {evm : State}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 17 ≤ 1024)
    (ha : (calldataWord market 64).toNat < 2 ^ 128)
    (hload : memLoad borrowPtr mem = calldataWord market 64)
    (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hr : frame.locals.get? "borrowRate" = some (uint256Value rate))
    (he : frame.locals.get? "elapsed" = some (uint256Value elapsed))
    (rd : RD (deployedRuntime v) I g s0 ⟨17239⟩
      (⟨17338⟩ :: elapsed :: feePtr :: rate :: borrowPtr :: R) mem aw rdata σ k C) :
    (ExecBlock config frame evm (marketAccrualBody.drop 2) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ABlock config evm frame (marketAccrualBody.drop 2)
      (marketInterestFrame frame (calldataWord market 64) rate elapsed)
      (marketAccrualBody.drop 4) ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨19367⟩
        (marketInterest (calldataWord market 64) rate elapsed :: ⟨17353⟩ :: ⟨17362⟩ ::
          uint128Mask :: borrowPtr :: feePtr :: uint128Mask ::
          marketInterest (calldataWord market 64) rate elapsed :: R) mem aw' rdata σ k' C') := by
  rcases marketInterestRoutine v hstack ha hload rd with ⟨hbad, hrev⟩ | ⟨hfit, hdone⟩
  · exact .inl ⟨marketInterestSourceReverts hcontract hm hr he hbad, hrev⟩
  · exact .inr ⟨marketInterestSourcePrefix hcontract hm hr he hfit, hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
