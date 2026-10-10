import Benchmarks.Morpho.MetaMorphoV1_1.SpendAllowanceGuards

/-! The finite allowance write and the shared return to the caller. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem spendAllowanceStoreMemory (mem : ByteArray) (owner spender : AccountAddress) :
    metaMorphoV1_1_block_12614_memory (mem := mem)
      (x0 := UInt256.ofNat owner.toNat) (x1 := UInt256.ofNat spender.toNat) =
      approvalScratchMem mem owner spender := by
  have hs : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (UInt256.ofNat spender.toNat) = UInt256.ofNat spender.toNat :=
    solcAddrMask_clean_left (addressWord_val_canonical spender)
  simp only [metaMorphoV1_1_block_12614_memory, hs]
  change twoWordHashMem (UInt256.ofNat spender.toNat)
    (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨1⟩ mem))
    (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨1⟩ mem) = _
  have hh : keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨1⟩ mem) =
      solcMappingSlot ⟨1⟩ (UInt256.ofNat owner.toNat) :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  rw [hh]
  rfl

theorem spendAllowanceStoreReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender : AccountAddress} {value allowed ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024) (hperm : I.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12614⟩
      (UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value :: allowed :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R
      (approvalScratchMem mem owner spender) aw' rdata
      (sstoreAccountMap I.codeOwner σ (approvalSlot owner spender) (UInt256.sub allowed value))
      k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12614_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hperm
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  change RD (deployedRuntime v) I g s0 ⟨12579⟩ (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ret :: R)
    (metaMorphoV1_1_block_12614_memory (mem := mem)
      (x0 := UInt256.ofNat owner.toNat) (x1 := UInt256.ofNat spender.toNat)) aw1 rdata
    (sstoreAccountMap I.codeOwner σ
      (keccakWord ⟨0⟩ ⟨64⟩ (metaMorphoV1_1_block_12614_memory (mem := mem)
        (x0 := UInt256.ofNat owner.toNat) (x1 := UInt256.ofNat spender.toNat)))
      (UInt256.sub allowed value)) k1 C1 at h1
  rw [spendAllowanceStoreMemory, allowanceScratchHash] at h1
  exact metaMorphoV1_1_block_12579_packed (immWords := wordsOf (immStore v))
    (by omega) hret h1

end Benchmarks.Morpho.MetaMorphoV1_1
