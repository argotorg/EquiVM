import Benchmarks.Morpho.MetaMorphoV1_1.SpendAllowanceCalls
import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_062

/-! Nested allowance lookup and the unlimited-allowance branch. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem allowanceAddOne_ne_zero {word : UInt256} (h : word ≠ unlimitedAllowance) :
    word + ⟨1⟩ ≠ ⟨0⟩ := by
  have hmax : word.toNat ≠ UInt256.size - 1 := by
    intro heq
    apply h
    apply u256_inj
    rw [unlimitedAllowance, u256_lnot_zero_toNat, heq]
  have hfit : word.toNat + 1 < UInt256.size := by
    have hlt := word.val.isLt
    change word.toNat < UInt256.size at hlt
    omega
  intro hz
  have hn := congrArg UInt256.toNat hz
  rw [add1_toNat hfit] at hn
  change word.toNat + 1 = 0 at hn
  omega

theorem allowanceScratchHash (mem : ByteArray) (owner spender : AccountAddress) :
    keccakWord ⟨0⟩ ⟨64⟩ (approvalScratchMem mem owner spender) = approvalSlot owner spender :=
  twoWordHashMem_solcMappingSlot_any _ _ _

theorem spendAllowanceLookupMemory (mem : ByteArray) (owner spender : AccountAddress) :
    metaMorphoV1_1_block_12530_taken_memory (mem := mem)
      (x0 := UInt256.ofNat owner.toNat) (x1 := UInt256.ofNat spender.toNat) =
      approvalScratchMem mem owner spender := by
  have ho : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (UInt256.ofNat owner.toNat) = UInt256.ofNat owner.toNat :=
    solcAddrMask_clean_left (addressWord_val_canonical owner)
  have hs : UInt256.land (UInt256.ofNat spender.toNat)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = UInt256.ofNat spender.toNat :=
    solcAddrMask_clean (addressWord_val_canonical spender)
  simp only [metaMorphoV1_1_block_12530_taken_memory, ho, hs]
  change twoWordHashMem (UInt256.ofNat spender.toNat)
    (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨1⟩ mem))
    (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨1⟩ mem) = _
  have hh : keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨1⟩ mem) =
      solcMappingSlot ⟨1⟩ (UInt256.ofNat owner.toNat) :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  rw [hh]
  rfl

theorem spendAllowanceLookupStack (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (owner spender : AccountAddress) (value : UInt256) (R : List UInt256) :
    metaMorphoV1_1_block_12530_taken_stack (ee := I) (σ := σ) (mem := mem)
      (x0 := UInt256.ofNat owner.toNat) (x1 := UInt256.ofNat spender.toNat) (x2 := value)
      (R := R) =
      UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value ::
        codeOwnerStorageWord I σ (approvalSlot owner spender) :: R := by
  have ho : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (UInt256.ofNat owner.toNat) = UInt256.ofNat owner.toNat :=
    solcAddrMask_clean_left (addressWord_val_canonical owner)
  change _ :: _ :: value :: codeOwnerStorageWord I σ (keccakWord ⟨0⟩ ⟨64⟩
    (metaMorphoV1_1_block_12530_taken_memory (mem := mem)
      (x0 := UInt256.ofNat owner.toNat) (x1 := UInt256.ofNat spender.toNat))) :: R = _
  rw [spendAllowanceLookupMemory, allowanceScratchHash, ho]

theorem spendAllowanceLookup {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender : AccountAddress} {value : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨12530⟩
      (UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0
      (if codeOwnerStorageWord I σ (approvalSlot owner spender) = unlimitedAllowance
        then ⟨12579⟩ else ⟨12585⟩)
      (UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value ::
        codeOwnerStorageWord I σ (approvalSlot owner spender) :: R)
      (approvalScratchMem mem owner spender) aw' rdata σ k' C' := by
  by_cases hmax : codeOwnerStorageWord I σ (approvalSlot owner spender) = unlimitedAllowance
  · rw [if_pos hmax]
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12530_fallthrough_packed
      (immWords := wordsOf (immStore v)) hstack (by
        change codeOwnerStorageWord I σ (keccakWord ⟨0⟩ ⟨64⟩
          (metaMorphoV1_1_block_12530_taken_memory (mem := mem)
            (x0 := UInt256.ofNat owner.toNat) (x1 := UInt256.ofNat spender.toNat))) + ⟨1⟩ = ⟨0⟩
        rw [spendAllowanceLookupMemory, allowanceScratchHash, hmax]
        decide) rd
    change RD (deployedRuntime v) I g s0 ⟨12579⟩
      (metaMorphoV1_1_block_12530_taken_stack (ee := I) (σ := σ) (mem := mem)
        (x0 := UInt256.ofNat owner.toNat) (x1 := UInt256.ofNat spender.toNat) (x2 := value)
        (R := R))
      (metaMorphoV1_1_block_12530_taken_memory (mem := mem)
        (x0 := UInt256.ofNat owner.toNat) (x1 := UInt256.ofNat spender.toNat))
      aw1 rdata σ k1 C1 at h1
    rw [spendAllowanceLookupStack, spendAllowanceLookupMemory] at h1
    exact ⟨aw1, k1, C1, h1⟩
  · rw [if_neg hmax]
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12530_taken_packed
      (immWords := wordsOf (immStore v)) hstack (by
        change codeOwnerStorageWord I σ (keccakWord ⟨0⟩ ⟨64⟩
          (metaMorphoV1_1_block_12530_taken_memory (mem := mem)
            (x0 := UInt256.ofNat owner.toNat) (x1 := UInt256.ofNat spender.toNat))) + ⟨1⟩ ≠ ⟨0⟩
        rw [spendAllowanceLookupMemory, allowanceScratchHash]
        exact allowanceAddOne_ne_zero hmax)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    rw [spendAllowanceLookupStack, spendAllowanceLookupMemory] at h1
    exact ⟨aw1, k1, C1, h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
