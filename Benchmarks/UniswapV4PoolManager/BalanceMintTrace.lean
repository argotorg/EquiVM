import Benchmarks.UniswapV4PoolManager.BalanceMint
import Benchmarks.UniswapV4PoolManager.MappingMemory
import Benchmarks.UniswapV4PoolManager.StorageStaticTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_005
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_006
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_030

/-! The balance-credit and event tail reached by `mint`. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def balanceMintStack (receiver id amount : UInt256) (R : List UInt256) : List UInt256 :=
  receiver :: solcAddrMask :: ⟨1005⟩ :: transferEventTopic :: ⟨0⟩ :: amount :: id :: R

theorem balanceMintLoadTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {receiver id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 11 ≤ 1024) (hmem : mem.size = 96) (hc : receiver.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) I g s0 ⟨10850⟩ (balanceMintStack receiver id amount R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12282⟩
      (solcSlotWordAt (balanceSlot receiver id) σ I :: amount :: ⟨607⟩ :: balanceSlot receiver id ::
        amount :: ⟨1005⟩ :: transferEventTopic :: ⟨0⟩ :: receiver :: id :: R)
      (nestedMappingMemory receiver id ⟨4⟩ mem) aw' rdata σ k' C' := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12282) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  obtain ⟨k', C', hnext⟩ := poolManagerBlocks.poolManager_block_10850 (R := R) hstack hj h
  let masked := UInt256.land receiver solcAddrMask
  let nextMem := nestedMappingMemory masked id ⟨4⟩ mem
  change RD (deployedRuntime v) I g s0 ⟨12282⟩
    (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ nextMem) σ I :: amount :: ⟨607⟩ ::
      keccakWord ⟨0⟩ ⟨64⟩ nextMem :: amount :: ⟨1005⟩ :: transferEventTopic :: ⟨0⟩ :: masked :: id :: R)
    nextMem _ rdata σ k' C' at hnext
  have hm : masked = receiver := solcAddrMask_clean hc
  dsimp only [nextMem] at hnext
  rw [hm, nestedMappingMemory_slot _ _ _ hmem] at hnext
  exact ⟨_, _, _, hnext⟩

open poolManagerBlocks in
theorem balanceCreditStaticTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {value slot : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 2 ≤ 1024) (hp : I.perm = false)
    (h : RD (deployedRuntime v) I g s0 ⟨607⟩ (value :: slot :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  exact swappedStoreStatic hstack hp
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨607⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64))
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨608⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64))
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨609⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) h

theorem balanceMintReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {value slot receiver id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 10 ≤ 1024) (hp : I.perm = true)
    (h : RD (deployedRuntime v) I g s0 ⟨607⟩
      (value :: slot :: amount :: ⟨1005⟩ :: transferEventTopic :: ⟨0⟩ :: receiver :: id :: R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 (sstoreAccountMap I.codeOwner σ slot value) .empty := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 1005) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  obtain ⟨k', C', hlog⟩ := poolManagerBlocks.poolManager_block_607
    (R := transferEventTopic :: ⟨0⟩ :: receiver :: id :: R)
    (by simp only [List.length_cons]; omega) hp hj h
  exact poolManagerBlocks.poolManager_block_1005 (by change R.length + 7 ≤ 1024; omega) hp hlog

theorem balanceMintTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw : UInt256} {k C : Nat} {receiver id amount : UInt256} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 11 ≤ 1024) (hmem : mem.size = 96)
    (hI : evm.executionEnv = I) (hc : receiver.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) I g s0 ⟨10850⟩ (balanceMintStack receiver id amount R) mem aw rdata evm.accountMap k C) :
    if (balanceWord evm receiver id).toNat + amount.toNat < UInt256.size then
      if I.perm = false then RDstatic (deployedRuntime v) g s0 else
      RDret (deployedRuntime v) g s0 (balanceMintPost evm receiver id amount).accountMap .empty
    else RDrev (deployedRuntime v) g s0 := by
  generalize hbalance : balanceWord evm receiver id = balance at ⊢
  obtain ⟨aw', k', C', hadd⟩ := balanceMintLoadTrace v hstack hmem hc h
  have hread : balanceWord evm receiver id = solcSlotWordAt (balanceSlot receiver id) evm.accountMap I :=
    storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])
  rw [← hread, hbalance] at hadd
  by_cases hfit : balance.toNat + amount.toNat < UInt256.size
  · rw [if_pos hfit]
    have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 607) = true := by
      rw [deployedRuntime_jumps]; jump_dest
    obtain ⟨k'', C'', hstore⟩ := checkedAddPass v (by simp only [List.length_cons]; omega) hfit hj hadd
    by_cases hp : I.perm = false
    · rw [if_pos hp]
      exact balanceCreditStaticTrace v (by simp only [List.length_cons]; omega) hp hstore
    · rw [if_neg hp]
      have hret := balanceMintReturnTrace v (by omega) (Bool.eq_true_of_not_eq_false hp) hstore
      have hmap : (balanceMintPost evm receiver id amount).accountMap =
          sstoreAccountMap I.codeOwner evm.accountMap (balanceSlot receiver id) (balance + amount) := by
        rw [balanceMintPost, balancePost, storageStore_accountMap, hI, hbalance]
      rw [hmap]
      exact hret
  · rw [if_neg hfit]
    exact checkedAddReverts v (by simp only [List.length_cons]; omega) (Nat.le_of_not_gt hfit) hadd

end Benchmarks.UniswapV4PoolManager
