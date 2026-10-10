import Benchmarks.Morpho.MetaMorphoV1_1.EcrecoverCall
import Benchmarks.Morpho.MetaMorphoV1_1.ECDSATryReturn
import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_086
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_018

/-! Recovery's s check, precompile input setup, and returned signer/error tuple. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem ecdsaHalfOrder_word : (UInt256.ofNat ecdsaHalfOrder).toNat = ecdsaHalfOrder := by
  decide +kernel

theorem ecdsaTryHighReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {hash sigV sigR sigS ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hhigh : ecdsaHalfOrder < sigS.toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨19083⟩ (hash :: sigV :: sigR :: sigS :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret (sigS :: ⟨3⟩ :: ⟨0⟩ :: R)
      mem aw rdata σ k' C' := by
  have r1 := metaMorphoV1_1_block_19083_taken (immWords := wordsOf (immStore v))
    (by simpa only [List.length_cons] using hstack)
    (by change UInt256.gt sigS (UInt256.ofNat ecdsaHalfOrder) ≠ ⟨0⟩
        rw [ugt_one (a := sigS) (b := UInt256.ofNat ecdsaHalfOrder)
          (by rw [ecdsaHalfOrder_word]; exact hhigh)]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact RD.pack (metaMorphoV1_1_block_19202 (immWords := wordsOf (immStore v))
    (by omega) hret r1)

theorem ecdsaTryCallSetup {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {hash sigV sigR sigS : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (free : Nat) (hstack : R.length + 10 ≤ 1024)
    (hfit : free + 128 < UInt256.size) (hv : sigV.toNat < 256)
    (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hlow : ¬ ecdsaHalfOrder < sigS.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨19083⟩ (hash :: sigV :: sigR :: sigS :: R)
      mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) I g s0 ⟨19163⟩
      (gasArg :: ⟨1⟩ :: UInt256.ofNat free :: ⟨128⟩ :: ⟨0⟩ :: ⟨32⟩ :: R)
      (ecrecoverCallMemory mem free hash sigV sigR sigS) aw' rdata σ k' C' := by
  have hf : free < UInt256.size := by omega
  have hclean : UInt256.land sigV (UInt256.ofNat 255) = sigV := lowByteClean hv
  have hadd (n : Nat) (hn : n ≤ 128) :
      (UInt256.ofNat free + UInt256.ofNat n).toNat = free + n := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt (by omega)]
  have hm : metaMorphoV1_1_block_19125_memory
      (mem := mem) (x0 := sigV) (x1 := sigR) (x2 := hash) (x3 := sigS) =
      ecrecoverCallMemory mem free hash sigV sigR sigS := by
    simp only [metaMorphoV1_1_block_19125_memory, hfree,
      UInt256.toNat_ofNat_of_lt hf, hadd 32 (by omega), hadd 64 (by omega),
      hadd 96 (by omega), hclean, ecrecoverCallMemory, wordSequenceMemory,
      Reasoning.Theory.writeWord, Nat.add_assoc]
    rfl
  have r1 := metaMorphoV1_1_block_19083_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (ugt_zero (a := sigS) (b := UInt256.ofNat ecdsaHalfOrder)
      (by rw [ecdsaHalfOrder_word]; exact Nat.le_of_not_gt hlow)) rd
  obtain ⟨aw', k', C', r2⟩ := metaMorphoV1_1_block_19125_packed
    (immWords := wordsOf (immStore v)) hstack r1
  rw [hm] at r2
  exact ⟨_, aw', k', C', by
    simpa only [metaMorphoV1_1_block_19125_stack, hfree] using r2⟩

theorem ecdsaTryCallFailure {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hout : out.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨19164⟩ (⟨0⟩ :: R) mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := metaMorphoV1_1_block_19164_taken (immWords := wordsOf (immStore v))
    (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_2921 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_19164_taken_stack]; omega)
    (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
        rw [UInt256.toNat_ofNat_of_lt hout, Nat.zero_add]) r1

theorem ecdsaTrySignerReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {signer : AccountAddress} {ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hword : memLoad ⟨0⟩ mem = UInt256.ofNat signer.toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨19164⟩ (⟨1⟩ :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
      (⟨0⟩ :: ecdsaRecoveryError signer :: UInt256.ofNat signer.toNat :: R)
      mem aw' out σ k' C' := by
  have r1 := metaMorphoV1_1_block_19164_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by decide) rd
  have hm : UInt256.land (memLoad ⟨0⟩ mem) solcAddrMask = UInt256.ofNat signer.toNat := by
    rw [hword]
    exact solcAddrMask_clean (addressWord_val_canonical signer)
  by_cases hzero : signer = AccountAddress.ofNat 0
  · have r2 := metaMorphoV1_1_block_19169_taken (immWords := wordsOf (immStore v))
      (R := ret :: R) (by simpa only [List.length_cons] using hstack)
      (by change UInt256.isZero (UInt256.land (memLoad ⟨0⟩ mem) solcAddrMask) ≠ ⟨0⟩
          rw [hm, hzero]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨k3, C3, r3⟩ := RD.pack (metaMorphoV1_1_block_19192
      (immWords := wordsOf (immStore v)) (by omega) hret r2)
    exact ⟨_, k3, C3, by
      simpa only [metaMorphoV1_1_block_19192_stack, ecdsaRecoveryError, if_pos hzero, hzero]
        using r3⟩
  · have r2 := metaMorphoV1_1_block_19169_fallthrough (immWords := wordsOf (immStore v))
      (R := ret :: R) (by simpa only [List.length_cons] using hstack)
      (by change UInt256.isZero (UInt256.land (memLoad ⟨0⟩ mem) solcAddrMask) = ⟨0⟩
          rw [hm]; exact isZero_eq_zero_of_ne (approvalAddressWord_ne_zero hzero)) r1
    obtain ⟨k3, C3, r3⟩ := RD.pack (metaMorphoV1_1_block_19186
      (immWords := wordsOf (immStore v)) (by omega) hret r2)
    exact ⟨_, k3, C3, by
      simpa only [metaMorphoV1_1_block_19186_stack, hword, ecdsaRecoveryError, if_neg hzero]
        using r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1
