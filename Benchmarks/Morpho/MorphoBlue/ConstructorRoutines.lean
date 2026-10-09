import Benchmarks.Morpho.MorphoBlue.ConstructorReturnMemory
import Benchmarks.Morpho.MorphoBlue.CreationBlocks_001
import Benchmarks.Morpho.MorphoBlue.CreationBlocks_002

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def constructorOwnerStack (w : UInt256) : List UInt256 :=
  [UInt256.ofNat 256, UInt256.ofNat 192, UInt256.lnot (UInt256.ofNat 31), UInt256.ofNat 32,
    UInt256.ofNat 64, w, UInt256.ofNat (2 ^ 64 - 1)]

theorem morphoConstructorReachOwner {σ σ₀ A I} {g : Sat256} (w : UInt256)
    (hcode : I.code = morphoCreationBytecode ++ w.toByteArray) (hc : w.toNat < EVM.addressModulus)
    (hcv : I.weiValue = ⟨0⟩) :
    ∃ aw k C, RD (morphoCreationBytecode ++ w.toByteArray) I g (initState σ σ₀ g A I)
      (UInt256.ofNat 114) (constructorOwnerStack w) (constructorDecodedMem w) aw ByteArray.empty σ k C := by
  have rd0 := RD.initState (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
  have rd1 := morphoCreationBlocks.morphoCreation_block_0_fallthrough (by simp) hcv rd0
  have rd2 := morphoCreationBlocks.morphoCreation_block_8_fallthrough
    (by simp [morphoCreationBlocks.morphoCreation_block_0_fallthrough_stack])
    (by rw [constructorCodeSize]; decide) rd1
  simp only [morphoCreationBlocks.morphoCreation_block_8_fallthrough_stack, constructorCodeSize] at rd2
  change RD _ _ _ _ _ [UInt256.ofNat 32, UInt256.ofNat 16055, UInt256.ofNat 160,
    UInt256.ofNat 192, UInt256.lnot (UInt256.ofNat 31), UInt256.ofNat (2 ^ 64 - 1)] _ _ _ _ _ _ at rd2
  have rd3 := morphoCreationBlocks.morphoCreation_block_52_fallthrough (by simp) (by decide) rd2
  change RD _ _ _ _ _ [UInt256.ofNat 160, UInt256.ofNat 32, UInt256.ofNat 64,
    UInt256.lnot (UInt256.ofNat 31), UInt256.ofNat (2 ^ 64 - 1)]
    ((morphoCreationBytecode ++ w.toByteArray).write 16055 constructorFreeMem 160 32) _ _ _ _ _ at rd3
  rw [constructorArgumentCopy] at rd3
  have hm := constructorDecodedMemory w
  have rd4 := morphoCreationBlocks.morphoCreation_block_76_fallthrough (by simp) (by
    change UInt256.sub (memLoad (UInt256.ofNat 160) (constructorDecodedMem w))
      (UInt256.land (memLoad (UInt256.ofNat 160) (constructorDecodedMem w)) solcAddrMask) = ⟨0⟩
    rw [hm.2.2, solcAddrMask_clean hc, u256_sub_self]) rd3
  change RD _ _ _ _ _ [UInt256.lnot (UInt256.ofNat 31), UInt256.ofNat 32, UInt256.ofNat 64,
    UInt256.land (memLoad (UInt256.ofNat 160) (constructorDecodedMem w)) solcAddrMask,
    UInt256.ofNat (2 ^ 64 - 1)] (constructorDecodedMem w) _ _ _ _ _ at rd4
  rw [hm.2.2, solcAddrMask_clean hc] at rd4
  have rd5 := morphoCreationBlocks.morphoCreation_block_97_fallthrough (by simp)
    (by rw [hm.2.1]; decide) rd4
  simp only [morphoCreationBlocks.morphoCreation_block_97_fallthrough_stack, hm.2.1] at rd5
  exact ⟨_, _, _, rd5⟩

theorem morphoConstructorReachHash {tail : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} (w : UInt256) (hw : w ≠ ⟨0⟩)
    (h : RD (morphoCreationBytecode ++ tail) I g s0 (UInt256.ofNat 114) (constructorOwnerStack w)
      (constructorDecodedMem w) aw rdata σ k C) :
    ∃ aw' k' C', RD (morphoCreationBytecode ++ tail) I g s0 (UInt256.ofNat 222)
      [UInt256.ofNat 64, UInt256.ofNat 256, UInt256.ofNat 288, w, UInt256.ofNat 384]
      (constructorDomainMem w I) aw' rdata σ k' C' := by
  have rd1 := morphoCreationBlocks.morphoCreation_block_114_fallthrough (by simp)
    (isZero_eq_zero_of_ne hw) h
  have hm : morphoCreationBlocks.morphoCreation_block_114_fallthrough_memory
      (mem := constructorDecodedMem w) (x0 := UInt256.ofNat 256) (x1 := UInt256.ofNat 192)
      (x3 := UInt256.ofNat 32) (x4 := UInt256.ofNat 64) = constructorOwnerMem w := by
    rw [constructorOwnerMem, morphoErrorMem, (constructorDecodedMemory w).2.1]
    rfl
  change RD _ _ _ _ _ [UInt256.ofNat 192, UInt256.lnot (UInt256.ofNat 31), UInt256.ofNat 32,
    UInt256.ofNat 64, w, UInt256.ofNat (2 ^ 64 - 1)] _ _ _ _ _ _ at rd1
  rw [hm] at rd1
  have hf := (constructorOwnerMemory w).2.1
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoCreationBlocks.morphoCreation_block_147_fallthrough_packed
    (by simp) (by rw [hf]; decide) rd1
  simp only [morphoCreationBlocks.morphoCreation_block_147_fallthrough_stack,
    morphoCreationBlocks.morphoCreation_block_147_fallthrough_memory, hf] at rd2
  exact ⟨aw2, k2, C2, rd2⟩

theorem morphoConstructorFinish {tail : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} (w : UInt256)
    (hc : w.toNat < EVM.addressModulus) (hp : I.perm = true)
    (h : RD (morphoCreationBytecode ++ tail) I g s0 (UInt256.ofNat 222)
      [UInt256.ofNat 64, UInt256.ofNat 256, UInt256.ofNat 288, w, UInt256.ofNat 384]
      (constructorDomainMem w I) aw rdata σ k C) :
    RDret (morphoCreationBytecode ++ tail) g s0
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ (setAddressOffset0Word (solcSlotWordAt ⟨0⟩ σ I) w))
      (immutableLayout.runtime morphoBytecode (fun _ => morphoDomainSeparator I)) := by
  have hr := morphoCreationBlocks.morphoCreation_block_222 (by simp) hp h
  have hm := constructorPreparedMemory w I
  change RDret _ _ _ (sstoreAccountMap I.codeOwner σ ⟨0⟩
    (UInt256.lor w (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWordAt ⟨0⟩ σ I))))
    ((writeWord (writeWord (constructorCopiedMem
      (writeWord (constructorPreparedMem w I) 128
        (keccakWord (UInt256.ofNat 288) (memLoad (UInt256.ofNat 256) (constructorPreparedMem w I))
          (constructorPreparedMem w I))) tail) 6666
      (memLoad (UInt256.ofNat 128) (constructorCopiedMem
        (writeWord (constructorPreparedMem w I) 128
          (keccakWord (UInt256.ofNat 288) (memLoad (UInt256.ofNat 256) (constructorPreparedMem w I))
            (constructorPreparedMem w I))) tail))) 9785
      (memLoad (UInt256.ofNat 128) (constructorCopiedMem
        (writeWord (constructorPreparedMem w I) 128
          (keccakWord (UInt256.ofNat 288) (memLoad (UInt256.ofNat 256) (constructorPreparedMem w I))
            (constructorPreparedMem w I))) tail))).readWithPadding 384 15623) at hr
  rw [hm.2.1, hm.2.2] at hr
  have hret := constructorPatchedReturn _ tail _ (constructorPatchMemory w I).1 (constructorPatchMemory w I).2
  simp only [constructorPatchMem] at hret
  rw [hret] at hr
  have hs : UInt256.lor w (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWordAt ⟨0⟩ σ I)) =
      setAddressOffset0Word (solcSlotWordAt ⟨0⟩ σ I) w := by
    rw [setAddressOffset0Word, solcAddrMask_clean hc]
    rw [u256_lor_comm w, u256_land_comm]
  rwa [hs] at hr

end Benchmarks.Morpho.MorphoBlue
