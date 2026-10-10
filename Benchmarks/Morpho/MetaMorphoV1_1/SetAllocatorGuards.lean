import Benchmarks.Morpho.MetaMorphoV1_1.SetAllocatorEntry
import Benchmarks.Morpho.MetaMorphoV1_1.SetAllocatorSource
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_010

/-! The allocator mapping read and unchanged-value guard in the runtime. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

def setAllocatorScratch (addr : AccountAddress) : ByteArray :=
  twoWordHashMem (UInt256.ofNat addr.val) ⟨11⟩ solcFreePtrMem

theorem allocatorBoolWord_bytecode (evm : EVM.State) (addr : AccountAddress) :
    UInt256.isZero (UInt256.isZero (UInt256.land (UInt256.ofNat 255)
      (codeOwnerStorageWord evm.executionEnv evm.accountMap
        (keccakWord ⟨0⟩ (UInt256.ofNat 64)
          (twoWordHashMem (UInt256.land (UInt256.sub
              (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
            (UInt256.ofNat addr.val)) (UInt256.ofNat 11) solcFreePtrMem))))) =
      allocatorBoolWord evm addr := by
  change UInt256.isZero (UInt256.isZero (UInt256.land ⟨255⟩
    (codeOwnerStorageWord evm.executionEnv evm.accountMap
      (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem
        (UInt256.land solcAddrMask (UInt256.ofNat addr.val)) ⟨11⟩ solcFreePtrMem))))) = _
  rw [solcAddrMask_clean_left (w := UInt256.ofNat addr.val) (addressWord_val_canonical addr),
    mappingScratchHash, u256_land_comm]
  rfl

set_option maxRecDepth 2000 in
theorem setAllocatorReachStore {evm : EVM.State} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    {addr : AccountAddress} {flag : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hne : allocatorBoolWord evm addr ≠ flag)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨3599⟩
      (UInt256.ofNat addr.val :: flag :: R) solcFreePtrMem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨3637⟩
      (flag :: UInt256.ofNat addr.val :: R) (setAllocatorScratch addr) aw' rdata
      evm.accountMap k' C' := by
  obtain ⟨aw', k', C', r1⟩ := metaMorphoV1_1_block_3599_fallthrough_packed
    (immWords := wordsOf (immStore v)) hstack (by
      have hc := u256_eq_of_ne (Ne.symm hne)
      rw [← allocatorBoolWord_bytecode evm addr] at hc
      exact hc) rd
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := by decide
  simp only [metaMorphoV1_1_block_3599_fallthrough_stack,
    metaMorphoV1_1_block_3599_fallthrough_memory, hm,
    solcAddrMask_clean_left (w := UInt256.ofNat addr.val) (addressWord_val_canonical addr)] at r1
  exact ⟨aw', k', C', r1⟩

set_option maxRecDepth 2000 in
theorem setAllocatorRevertUnchanged {evm : EVM.State} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {k C : Nat} {R : List UInt256}
    {addr : AccountAddress} {flag : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (heq : allocatorBoolWord evm addr = flag)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨3599⟩
      (UInt256.ofNat addr.val :: flag :: R) solcFreePtrMem aw rdata evm.accountMap k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, r1⟩ := metaMorphoV1_1_block_3599_taken
    (immWords := wordsOf (immStore v)) hstack (by
      have hc : UInt256.eq flag (allocatorBoolWord evm addr) ≠ ⟨0⟩ := by
        rw [heq, u256_eq_refl]
        decide
      rw [← allocatorBoolWord_bytecode evm addr] at hc
      exact hc) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_1143 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_3599_taken_stack, List.length]; omega) r1

end Benchmarks.Morpho.MetaMorphoV1_1
