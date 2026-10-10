import Benchmarks.UniswapV4PoolManager.ProtocolFeesUpdateSource
import Benchmarks.UniswapV4PoolManager.ProtocolFeesUpdateStatic
import Benchmarks.UniswapV4PoolManager.MappingScratchMemory
import Benchmarks.UniswapV4PoolManager.TransientTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def protocolFeesUpdateMemory (mem : ByteArray) (currency : AccountAddress) : ByteArray :=
  twoWordHashMem (accountWord currency) ⟨1⟩ mem

def protocolFeesUpdateAW (aw : UInt256) : UInt256 :=
  M (M (M aw ⟨0⟩ ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64)

theorem protocolFeesUpdateTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw amount : UInt256} {currency : AccountAddress}
    {x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 : UInt256}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+18 ≤ 1024) (hI : evm.executionEnv = I) (hperm : I.perm = true)
    (h : RD (deployedRuntime v) I g s0 ⟨2003⟩
      ([accountWord currency, amount, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11,
        x12, x13, x14, UInt256.ofNat 32, x16]++R) mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨1766⟩
      ([x16, x16, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14,
        UInt256.ofNat 32, x16]++R)
      (protocolFeesUpdateMemory mem currency) (protocolFeesUpdateAW aw) rdata
      (protocolFeesUpdatePost evm currency amount).accountMap k' C' := by
  have hclean : UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975)
      (accountWord currency) = accountWord currency := by
    rw [u256_land_comm]
    exact solcAddrMask_clean (accountWord_canonical currency)
  have hslot : keccakWord ⟨0⟩ (UInt256.ofNat 64) (protocolFeesUpdateMemory mem currency) =
      protocolFeesSlot currency := mappingMemory_slot_any _ _ _
  have hread : (evm.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac => ac.storage.getD (protocolFeesSlot currency) ⟨0⟩)) = protocolFeesWord evm currency :=
    (storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])).symm
  obtain ⟨k', C', rd⟩ := poolManagerBlocks.poolManager_block_2003 hstack hperm
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_2003_stack,
    poolManagerBlocks.poolManager_block_2003_memory, hclean] at rd
  change RD _ _ _ _ ⟨1766⟩ _ (protocolFeesUpdateMemory mem currency) _ _
    (sstoreAccountMap I.codeOwner evm.accountMap
      (keccakWord ⟨0⟩ (UInt256.ofNat 64) (protocolFeesUpdateMemory mem currency))
      ((evm.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD
        (keccakWord ⟨0⟩ (UInt256.ofNat 64) (protocolFeesUpdateMemory mem currency)) ⟨0⟩))+amount)) _ _ at rd
  rw [hslot, hread] at rd
  refine ⟨k', C', ?_⟩
  rw [protocolFeesUpdatePost, protocolFeesPost, storageStore_accountMap, hI]
  exact rd

end Benchmarks.UniswapV4PoolManager
