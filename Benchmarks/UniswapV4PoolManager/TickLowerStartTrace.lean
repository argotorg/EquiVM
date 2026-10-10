import Benchmarks.UniswapV4PoolManager.PoolUpdateTickSource
import Benchmarks.UniswapV4PoolManager.TransientTrace
import Benchmarks.UniswapV4PoolManager.Signed128Range
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_020
import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickLowerLiquidityTail (id tick packed x0 x1 x2 x3 x4 x5 x6 : UInt256) (delta : Int)
    (R : List UInt256) : List UInt256 :=
  ⟨2^128-1⟩ :: packed :: ⟨7038⟩ :: tickSlot id (EVM.signed tick) :: tickGrossWord packed :: tick ::
    (poolSlot id+⟨4⟩) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: EVM.wordOfInt delta :: tick :: R

theorem tickLowerStartExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 x1 x2 x3 x4 x5 x6 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+20 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (ht : int24Canonical tick)
    (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6949⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: EVM.wordOfInt delta :: tick :: R)
      mem aw rdata evm.accountMap k C) :
    let packed := tickFieldWord evm id (EVM.signed tick) .liquidityPacked
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨17774⟩
      (tickGrossWord packed :: EVM.wordOfInt delta :: ⟨7009⟩ ::
        tickLowerLiquidityTail id tick packed x0 x1 x2 x3 x4 x5 x6 delta R)
      (twoWordHashMem tick (poolSlot id+⟨4⟩) mem) (M aw (UInt256.ofNat 128) ⟨32⟩) rdata evm.accountMap k' C' := by
  have ht' : UInt256.signextend (UInt256.ofNat 2) tick = tick := (signextend24_eq_iff tick).mpr ht
  have hd' : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt delta) = EVM.wordOfInt delta :=
    signextend128_wordOfInt hd.1 hd.2
  obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_6949 hstack
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_6949_stack, poolManagerBlocks.poolManager_block_6949_memory,
    ht', hd', hm] at rd1
  have hhash : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      ((poolSlot id+UInt256.ofNat 4).toByteArray.write 0
        (tick.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) =
      tickSlot id (EVM.signed tick) := by
    change keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem tick (poolSlot id+⟨4⟩) mem) = _
    rw [mappingMemory_slot_any]
    simp only [tickSlot, wordOfInt_signed]
  rw [hhash] at rd1
  have hload : solcSlotWordAt (tickSlot id (EVM.signed tick)) evm.accountMap I =
      tickFieldWord evm id (EVM.signed tick) .liquidityPacked :=
    (storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])).symm
  dsimp only [solcSlotWordAt, solcSlotWord] at hload
  rw [hload] at rd1
  have h5 : 5 ≤ (M aw (UInt256.ofNat 128) ⟨32⟩).toNat :=
    memoryWords_ge_span aw (UInt256.ofNat 128) ⟨32⟩ (by decide)
  have h0 : M (M aw (UInt256.ofNat 128) ⟨32⟩) ⟨0⟩ ⟨32⟩ = M aw (UInt256.ofNat 128) ⟨32⟩ :=
    memoryWords_eq_self (by change 0+32 ≤ _*32; omega)
  have h32 : M (M aw (UInt256.ofNat 128) ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩ = M aw (UInt256.ofNat 128) ⟨32⟩ :=
    memoryWords_eq_self (by change 32+32 ≤ _*32; omega)
  have h64 : M (M aw (UInt256.ofNat 128) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64) = M aw (UInt256.ofNat 128) ⟨32⟩ :=
    memoryWords_eq_self (by change 0+64 ≤ _*32; omega)
  rw [h0, h32, h64] at rd1
  exact ⟨k1, C1, rd1⟩

theorem tickLowerStartTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 x1 x2 x3 x4 x5 x6 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+20 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (ht : int24Canonical tick)
    (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6949⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: EVM.wordOfInt delta :: tick :: R)
      mem aw rdata evm.accountMap k C) :
    let packed := tickFieldWord evm id (EVM.signed tick) .liquidityPacked
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨17774⟩
      (tickGrossWord packed :: EVM.wordOfInt delta :: ⟨7009⟩ ::
        tickLowerLiquidityTail id tick packed x0 x1 x2 x3 x4 x5 x6 delta R)
      (twoWordHashMem tick (poolSlot id+⟨4⟩) mem) aw' rdata evm.accountMap k' C' := by
  obtain ⟨k', C', hr⟩ := tickLowerStartExactTrace v hstack hI hm ht hd h
  exact ⟨_, k', C', hr⟩

end Benchmarks.UniswapV4PoolManager
