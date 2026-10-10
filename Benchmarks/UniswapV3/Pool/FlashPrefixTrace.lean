import Benchmarks.UniswapV3.Pool.FlashPrefix
import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.Calls
import Benchmarks.UniswapV3.Pool.Routines
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_022
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_023

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem flashLockStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨6508⟩ R mem aw rdata σ k C)
    (hperm : ee.perm = false) (hov : R.length + 4 ≤ 1024) :
    RDstatic (deployedRuntime v) g s0 := by
  have rdLoad := evm_run rd with [
    raw jumpdest (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨6508⟩ : UInt256), (UInt8.ofNat 91), .JUMPDEST, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw push1 (UInt256.ofNat 0) (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨6509⟩ : UInt256), (UInt8.ofNat 96), .Push .PUSH1, some ((UInt256.ofNat 0), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw dup1 (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨6511⟩ : UInt256), (UInt8.ofNat 128), .DUP1, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)]
  obtain ⟨_, _, rdLoaded⟩ :=
    RD.sload rdLoad (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨6512⟩ : UInt256), (UInt8.ofNat 84), .SLOAD, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rdStore := evm_run rdLoaded with [
    raw push1 (UInt256.ofNat 255) (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨6513⟩ : UInt256), (UInt8.ofNat 96), .Push .PUSH1, some ((UInt256.ofNat 255), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw push1 (UInt256.ofNat 240) (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨6515⟩ : UInt256), (UInt8.ofNat 96), .Push .PUSH1, some ((UInt256.ofNat 240), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw shl (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨6517⟩ : UInt256), (UInt8.ofNat 27), .SHL, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw not (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨6518⟩ : UInt256), (UInt8.ofNat 25), .NOT, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw and (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨6519⟩ : UInt256), (UInt8.ofNat 22), .AND, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw swap1 (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨6520⟩ : UInt256), (UInt8.ofNat 144), .SWAP1, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)]
  exact rdStore.sstoreStatic hperm (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨6521⟩ : UInt256), (UInt8.ofNat 85), .SSTORE, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)


theorem flashReadLockX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨6440⟩ R mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ slot0FieldWord 30 1 σ ee = ⟨0⟩) ∨
      (slot0FieldWord 30 1 σ ee ≠ ⟨0⟩ ∧
        ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨6508⟩ R mem aw rdata σ k' C') := by
  have hfield : UInt256.land (UInt256.ofNat 255)
      (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
        (fun ac ↦ ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))) =
      slot0FieldWord 30 1 σ ee := (slot0FieldWord_unlocked_evm σ ee).symm
  by_cases hlocked : slot0FieldWord 30 1 σ ee = ⟨0⟩
  · obtain ⟨_, _, rdFail⟩ := uniswapV3Pool_block_6440_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) (by rw [hfield]; exact hlocked) rd
    exact Or.inl ⟨uniswapV3Pool_block_6458 (immWords := wordsOf (immStore v)) hov rdFail, hlocked⟩
  · exact Or.inr ⟨hlocked, uniswapV3Pool_block_6440_taken (immWords := wordsOf (immStore v))
      (by omega) (by rw [hfield]; exact hlocked)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩

theorem flashLockX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨6508⟩ R mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true) (hov : R.length + 4 ≤ 1024) :
    SourceState s0 ee (storeSlot0Unlocked evm false).accountMap (storeSlot0Unlocked evm false) ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11248⟩ (⟨6529⟩ :: R) mem aw rdata
        (storeSlot0Unlocked evm false).accountMap k' C' := by
  have hmap := storeSlot0Unlocked_accountMap evm false
  rw [slot0UnlockedWord_false, hs.env, ← hs.accounts] at hmap
  change (storeSlot0Unlocked evm false).accountMap =
    sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0)
      (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240)))
        (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac ↦ ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))) at hmap
  refine ⟨⟨(storeSlot0Unlocked_originalAccounts evm false).trans hs.world,
    (storeSlot0Unlocked_executionEnv evm false).trans hs.env, rfl⟩, ?_⟩
  obtain ⟨k', C', rd'⟩ := uniswapV3Pool_block_6508 (immWords := wordsOf (immStore v)) hov hperm
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  rw [← hmap] at rd'
  exact ⟨k', C', rd'⟩

theorem flashReadLiquidityX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨6529⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ (poolLiquidityWord σ ee).toNat = 0) ∨
      (0 < (poolLiquidityWord σ ee).toNat ∧
        ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨6595⟩ (poolLiquidityWord σ ee :: R)
          mem aw rdata σ k' C') := by
  have hfield : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))
      (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
        (fun ac ↦ ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) = poolLiquidityWord σ ee := by
    rw [solcMask128, u256_land_comm]
    rfl
  by_cases hz : poolLiquidityWord σ ee = ⟨0⟩
  · obtain ⟨_, _, rdBad⟩ := uniswapV3Pool_block_6529_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) (by rw [hfield]; exact hz) rd
    exact Or.inl ⟨uniswapV3Pool_block_6547 (immWords := wordsOf (immStore v))
      (by simpa only [uniswapV3Pool_block_6529_fallthrough_stack, List.length_cons] using hov) rdBad,
      congrArg UInt256.toNat hz⟩
  · obtain ⟨k', C', rd'⟩ := uniswapV3Pool_block_6529_taken
      (immWords := wordsOf (immStore v)) (by omega) (by rw [hfield]; exact hz)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    refine Or.inr ⟨Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h)), k', C', ?_⟩
    simpa only [uniswapV3Pool_block_6529_taken_stack, hfield] using rd'

end Benchmarks.UniswapV3.Pool
