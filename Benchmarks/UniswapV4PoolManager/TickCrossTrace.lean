import Benchmarks.UniswapV4PoolManager.TickCrossStorageTrace
import Benchmarks.UniswapV4PoolManager.ReachCost
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_057

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickCrossTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick growth0 growth1 step state : UInt256}
    {x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 direction : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hI : evm.executionEnv = I)
    (hperm : I.perm = true) (htick : memLoad (step+UInt256.ofNat 32) mem = tick)
    (h : RD (deployedRuntime v) I g s0 ⟨20029⟩
      ([step, UInt256.ofNat 32, poolSlot id, UInt256.ofNat 4, growth1, growth0, state,
        x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, direction] ++ R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0
      (if direction = ⟨0⟩ then ⟨20104⟩ else ⟨20082⟩)
      ([state, tickCrossNet evm id (EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)) growth0 growth1,
        x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, direction] ++ R)
      (tickCrossMemory mem id tick)
      (M (M (M (M aw (step+UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩)
        ⟨0⟩ (UInt256.ofNat 64)) rdata
      (tickCrossPost evm id (EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)) growth0 growth1).accountMap k' C' := by
  have hhash := tickCrossMemory_hash_compiled mem id tick
  have haccounts := tickCrossPost_accounts hI id (EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)) growth0 growth1
  have hnet := tickCrossNet_compiled hI id (EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)) growth0 growth1
  apply RD_retainCost ?_ h
  intro budget start rd
  by_cases hd : direction = ⟨0⟩
  · rw [if_pos hd]
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_20029_taken hstack hperm
      (by rw [hd]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd
    dsimp only [poolManagerBlocks.poolManager_block_20029_taken_stack,
      poolManagerBlocks.poolManager_block_20029_taken_memory] at rd1
    rw [htick, hhash, signextend24_idempotent] at rd1
    change RD (deployedRuntime v) I budget start ⟨20104⟩
      ([state, UInt256.sar (UInt256.ofNat 128) (solcSlotWordAt
          (tickSlot id (EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)))
          (tickCrossAccounts evm.accountMap I id (EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)) growth0 growth1) I),
        x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, direction] ++ R)
      (tickCrossMemory mem id tick) _ rdata
      (tickCrossAccounts evm.accountMap I id (EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)) growth0 growth1) k1 C1 at rd1
    rw [hnet, ← haccounts] at rd1
    exact ⟨k1, C1, rd1⟩
  · rw [if_neg hd]
    obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_20029_fallthrough hstack hperm
      (isZero_eq_zero_of_ne hd) rd
    dsimp only [poolManagerBlocks.poolManager_block_20029_fallthrough_stack,
      poolManagerBlocks.poolManager_block_20029_fallthrough_memory] at rd1
    rw [htick, hhash, signextend24_idempotent] at rd1
    change RD (deployedRuntime v) I budget start ⟨20082⟩
      ([state, UInt256.sar (UInt256.ofNat 128) (solcSlotWordAt
          (tickSlot id (EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)))
          (tickCrossAccounts evm.accountMap I id (EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)) growth0 growth1) I),
        x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, direction] ++ R)
      (tickCrossMemory mem id tick) _ rdata
      (tickCrossAccounts evm.accountMap I id (EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)) growth0 growth1) k1 C1 at rd1
    rw [hnet, ← haccounts] at rd1
    exact ⟨k1, C1, rd1⟩

end Benchmarks.UniswapV4PoolManager
