import Benchmarks.Morpho.MetaMorphoV1_1.SetAllocatorGuards

/-! Successful storage update for allocator permissions. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

theorem allocatorStore_bytecode (old flag : UInt256) (hflag : flag = ⟨0⟩ ∨ flag = ⟨1⟩) :
    UInt256.lor (UInt256.land flag (UInt256.ofNat 255))
      (UInt256.land old (UInt256.lnot (UInt256.ofNat 255))) = setBoolOffset0Word old flag := by
  rw [u256_lor_comm, setBoolOffset0Word, (boolWordClean_iff flag).mpr hflag]
  congr 1
  rcases hflag with h | h <;> rw [h] <;> decide

set_option maxRecDepth 2000 in
theorem setAllocatorStoreReturn {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    {addr : AccountAddress} {flag : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hflag : flag = ⟨0⟩ ∨ flag = ⟨1⟩) (hperm : evm.executionEnv.perm = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨3637⟩
      (flag :: UInt256.ofNat addr.val :: R) mem aw rdata evm.accountMap k C) :
    RDret (deployedRuntime v) g s0 (setAllocatorState evm addr flag).accountMap
      ByteArray.empty := by
  have hret := metaMorphoV1_1_block_3637 (immWords := wordsOf (immStore v)) hstack hperm rd
  have hk : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      ((UInt256.ofNat 11).toByteArray.write 0
        ((UInt256.ofNat addr.val).toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32)
        (UInt256.ofNat 32).toNat 32) = allocatorSlot addr :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  rw [hk, allocatorStore_bytecode _ flag hflag] at hret
  simpa only [setAllocatorState, storageStore_accountMap] using hret

end Benchmarks.Morpho.MetaMorphoV1_1
