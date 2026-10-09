import Benchmarks.Morpho.MorphoBlue.WithdrawCollateralAccrueRefine
import Benchmarks.Morpho.MorphoBlue.HealthyPriceReach
import Benchmarks.Morpho.MorphoBlue.Uint128Subtraction
import Benchmarks.Morpho.MorphoBlue.PositionPackedWrites
import Benchmarks.Morpho.MorphoBlue.StoreHighStatic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def withdrawCollateralHealthTail (id assets account receiver : UInt256) (R : List UInt256) : List UInt256 :=
  [id, account, receiver, UInt256.ofNat 128, UInt256.ofNat 32, solcAddrMask, receiver,
    assets, UInt256.ofNat 1211, UInt256.ofNat 0] ++ R

def withdrawCollateralUpdateTail (id assets account receiver : UInt256) (R : List UInt256) : List UInt256 :=
  [account, UInt256.ofNat 5693, UInt256.ofNat 5701] ++ withdrawCollateralHealthTail id assets account receiver R

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem out : ByteArray} {aw id assets account receiver : UInt256} {σ : AccountMap}
  {k C : Nat} {R : List UInt256}

theorem morphoWithdrawCollateralReachCast (hstack : R.length + 36 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5630)
      (withdrawCollateralGuardTail id assets account receiver R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([assets, UInt256.ofNat 5644, UInt256.ofNat 64, UInt256.ofNat 5686] ++
        withdrawCollateralGuardTail id assets account receiver R) mem aw out σ k' C' := by
  have rd := morphoBlocks.morpho_block_5630 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 16 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact ⟨_, _, rd⟩

theorem morphoWithdrawCollateralReachSub (hstack : R.length + 36 ≤ 1024)
    (hc : account.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5644)
      ([assets, UInt256.ofNat 64, UInt256.ofNat 5686] ++
        withdrawCollateralGuardTail id assets account receiver R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12846)
      ([positionFieldWord σ ee id account 2, assets, UInt256.ofNat 2278,
        positionSlot id account + UInt256.ofNat 1, UInt256.ofNat 5686] ++
        withdrawCollateralUpdateTail id assets account receiver R)
      (supplyPositionMem id account mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_5644_packed (immWords := wordsOf (immStore v))
    (by change R.length + 4 + 15 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_5644_stack, morphoBlocks.morpho_block_5644_memory] at rd1
  rw [solcAddrMask_clean hc] at rd1
  let m1 := twoWordHashMem id (UInt256.ofNat 2) mem
  have hh1 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1 = solcMappingSlot ⟨2⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  let m2 := twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1) m1
  have hm2 : m2 = supplyPositionMem id account mem := by dsimp only [m2]; rw [hh1]; rfl
  change RD _ _ _ _ _
    ([UInt256.shiftRight (solcSlotWordAt
      (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1) σ ee)
      (UInt256.ofNat 128), assets, UInt256.ofNat 2278,
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1, UInt256.ofNat 5686] ++
      withdrawCollateralUpdateTail id assets account receiver R) m2 _ _ _ _ _ at rd1
  rw [hm2, supplyPositionMem_hash] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
