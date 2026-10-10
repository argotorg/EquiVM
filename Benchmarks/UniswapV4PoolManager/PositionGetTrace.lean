import Benchmarks.UniswapV4PoolManager.PositionGetSource
import Benchmarks.UniswapV4PoolManager.PositionGetMemory
import Benchmarks.UniswapV4PoolManager.PositionGetCostBlock

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def positionGetOutputStack (evm : State) (id : UInt256) (owner : AccountAddress)
    (lower upper salt delta x0 x1 x2 x3 x4 x5 fee0 x9 fee1 : UInt256) (R : List UInt256) : List UInt256 :=
  let key := positionKey owner lower upper salt
  fee0 :: upper :: delta :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: positionSlot id key ::
    positionLiquidityWord evm id key :: lower :: x9 :: fee1 :: R

open poolManagerBlocks in
theorem positionGetCostTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free id params lower upper salt delta x0 x1 x2 x3 x4 x5 fee0 x9 fee1 : UInt256}
    {owner : AccountAddress} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) (hfl : 160 ≤ free.toNat)
    (hfh : free.toNat+64 < UInt256.size)
    (ha : UInt256.land (memLoad params mem) solcAddrMask = accountWord owner)
    (hs : memLoad (params+UInt256.ofNat 160) mem = salt)
    (h : RD (deployedRuntime v) I g s0 ⟨5802⟩
      (params :: delta :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: upper :: fee0 :: lower :: x9 :: fee1 :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', Cₘ (positionGetActiveWords aw params free)+C ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ⟨5915⟩
      (positionGetOutputStack evm id owner lower upper salt delta x0 x1 x2 x3 x4 x5 fee0 x9 fee1 R)
      (positionGetMemory mem free id owner lower upper salt) (positionGetActiveWords aw params free) rdata evm.accountMap k' C' := by
  obtain ⟨k1, C1, hcost, rd1⟩ := positionGetCostBlock (by simp only [List.length_cons]; omega) h
  rw [hfree] at hcost
  have ha' : UInt256.land (memLoad params mem)
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = accountWord owner := ha
  simp only [poolManager_block_5802_stack, poolManager_block_5802_memory, hfree, hs, ha'] at rd1
  rw [positionKeyMemory_compiled mem free owner lower upper salt (by omega),
    positionKeyMemory_hash mem free owner lower upper salt (by omega),
    positionKeyCleanMemory_compiled mem free owner lower upper salt hfh] at rd1
  have hpool := positionKeyScratch_load_pool (free := free) (id := id)
    (lower := lower) (upper := upper) (salt := salt) owner hm hmem hfl
  rw [hpool] at rd1
  have hhash : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      ((poolSlot id+UInt256.ofNat 6).toByteArray.write 0
        ((positionKey owner lower upper salt).toByteArray.write 0
          (positionKeyCleanMemory mem free.toNat owner lower upper salt) (⟨0⟩ : UInt256).toNat 32)
        (UInt256.ofNat 32).toNat 32) = positionSlot id (positionKey owner lower upper salt) := by
    change keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (positionKey owner lower upper salt) (poolSlot id+⟨6⟩)
      (positionKeyCleanMemory mem free.toNat owner lower upper salt)) = _
    exact mappingMemory_slot_any _ _ _
  rw [hhash] at rd1
  have hload : solcSlotWordAt (positionSlot id (positionKey owner lower upper salt)) evm.accountMap I =
      positionPackedWord evm id (positionKey owner lower upper salt) :=
    (storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])).symm
  dsimp only [solcSlotWordAt, solcSlotWord] at hload
  rw [hload] at rd1
  exact ⟨k1, C1, hcost, rd1⟩

theorem positionGetTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free id params lower upper salt delta x0 x1 x2 x3 x4 x5 fee0 x9 fee1 : UInt256}
    {owner : AccountAddress} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) (hfl : 160 ≤ free.toNat)
    (hfh : free.toNat+64 < UInt256.size)
    (ha : UInt256.land (memLoad params mem) solcAddrMask = accountWord owner)
    (hs : memLoad (params+UInt256.ofNat 160) mem = salt)
    (h : RD (deployedRuntime v) I g s0 ⟨5802⟩
      (params :: delta :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: upper :: fee0 :: lower :: x9 :: fee1 :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨5915⟩
      (positionGetOutputStack evm id owner lower upper salt delta x0 x1 x2 x3 x4 x5 fee0 x9 fee1 R)
      (positionGetMemory mem free id owner lower upper salt) aw' rdata evm.accountMap k' C' := by
  obtain ⟨k', C', _, hr⟩ := positionGetCostTrace v hstack hI hm hmem hfree hfl hfh ha hs h
  exact ⟨_, k', C', hr⟩

end Benchmarks.UniswapV4PoolManager
