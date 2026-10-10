import Benchmarks.UniswapV4PoolManager.PoolSwapPreludeMemory
import Benchmarks.UniswapV4PoolManager.PoolSwapLPSelectSource
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_053
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.WordBoolean

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapResultLoadTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id state params ret packed protocol amount inv : UInt256} {p : PoolSwapParamsWords}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024) (hI : evm.executionEnv = I)
    (hs : memLoad params mem = p.amountSpecified)
    (ho : memLoad (params+UInt256.ofNat 128)
      (poolSwapResultInitMem mem state packed (poolLiquidityWord evm id)) = p.lpFeeOverride)
    (h : RD (deployedRuntime v) I g s0 ⟨18842⟩
      ([ret, params, state+UInt256.ofNat 32, state+UInt256.ofNat 64, state, protocol, amount, inv,
        packed, poolSlot id, state]++R) mem aw rdata evm.accountMap k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 (if lpFeeIsOverride p.lpFeeOverride then ⟨18928⟩ else ⟨22246⟩)
      ([p.lpFeeOverride, slot0SqrtPriceWord packed, ret, params, p.amountSpecified, ⟨0⟩, state, protocol, amount,
        inv, packed, poolSlot id, state]++R)
      (poolSwapResultInitMem mem state packed (poolLiquidityWord evm id)) (poolSwapResultInitAW aw state params)
      rdata evm.accountMap k' C' := by
  have hliq : UInt256.land (evm.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac => ac.storage.getD (poolSlot id+UInt256.ofNat 3) ⟨0⟩))
      (UInt256.ofNat 340282366920938463463374607431768211455) = poolLiquidityWord evm id :=
    congrArg (fun word => UInt256.land word (UInt256.ofNat 340282366920938463463374607431768211455))
      (storageLoad_codeOwner_eq_solcSlotWordAt evm I (poolSlot id+UInt256.ofNat 3) (by rw [hI])).symm
  have hprice : UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) packed =
      slot0SqrtPriceWord packed := u256_land_comm _ _
  have hoRaw : memLoad (params+UInt256.ofNat 128)
      (poolManagerBlocks.poolManager_block_18842_taken_memory (ee := I) (mem := mem) (σ := evm.accountMap)
        (x2 := state+UInt256.ofNat 32) (x3 := state+UInt256.ofNat 64) (x4 := state)
        (x8 := packed) (x9 := poolSlot id)) = p.lpFeeOverride := by
    simpa only [poolManagerBlocks.poolManager_block_18842_taken_memory, hliq, hprice] using ho
  dsimp only [poolManagerBlocks.poolManager_block_18842_taken_memory] at hoRaw
  simp only [hliq, hprice] at hoRaw
  have htest : UInt256.isZero (UInt256.isZero (UInt256.land p.lpFeeOverride (UInt256.ofNat 4194304))) =
      UInt256.fromBool (lpFeeIsOverride p.lpFeeOverride) := wordNonzeroBool _
  apply RD_retainCost (h := h)
  intro budget start hin
  cases he : lpFeeIsOverride p.lpFeeOverride
  · obtain ⟨k', C', rd⟩ := poolManagerBlocks.poolManager_block_18842_taken
      (by change R.length+1+15 ≤ 1024; omega)
      (by rw [hliq, hprice, hoRaw, htest, he]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) hin
    simp only [poolManagerBlocks.poolManager_block_18842_taken_stack, hoRaw, hs, hprice,
      poolManagerBlocks.poolManager_block_18842_taken_memory, hliq] at rd
    exact ⟨k', C', rd⟩
  · obtain ⟨k', C', rd⟩ := poolManagerBlocks.poolManager_block_18842_fallthrough
      (by change R.length+1+15 ≤ 1024; omega) (by rw [hliq, hprice, hoRaw, htest, he]; rfl) hin
    simp only [poolManagerBlocks.poolManager_block_18842_fallthrough_stack, hoRaw, hs, hprice,
      poolManagerBlocks.poolManager_block_18842_fallthrough_memory, hliq] at rd
    exact ⟨k', C', rd⟩

end Benchmarks.UniswapV4PoolManager
