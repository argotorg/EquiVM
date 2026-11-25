import Benchmarks.Midnight.LiquidateStorageGas

variable {fork : Ethereum.Fork}

/-! The final packed continuous-fee write in the liquidation bad-debt branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateFeeStore {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root amount : UInt256} {σ : AccountMap}
    {k C credit : Nat} {R : List UInt256} (hstack : R.length + 7 ≤ 1024)
    (hp : I.perm = true) (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨7735⟩ (amount :: ⟨7768⟩ :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', TransferBudget root credit mem aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨7768⟩ R mem aw' rdata
        (storeHigh128Accounts σ I (memLoad (UInt256.ofNat 672) mem + ⟨1⟩) amount) k' C' := by
  obtain ⟨k', C', hb', rd'⟩ := liquidate_block_7735_budget hstack hp (by jump_dest) hb rd
  refine ⟨_, k', C', hb', ?_⟩
  simpa only [midnightBlocks.midnight_block_7735_stack, uint128Mask_computed,
    shiftLeft128_highMask, storeHigh128Accounts, setUint128HighWord] using rd'

end Benchmarks.Midnight
