import Benchmarks.Morpho.MetaMorphoV1_1.SkimSource
import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_017
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_018
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-! Skim entry guards, canonical address decoding, and the stored recipient check. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem skimRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024) (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨2710⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h := metaMorphoV1_1_block_2710_taken (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) h

theorem skimRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024) (hwv : I.weiValue = ⟨0⟩)
    (hbad : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨2710⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_2710_fallthrough (immWords := wordsOf (immStore v))
    (by omega) hwv rd
  have h2 := metaMorphoV1_1_block_2716_taken (immWords := wordsOf (immStore v)) hstack hbad
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) h2

theorem skimReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024) (hwv : I.weiValue = ⟨0⟩)
    (hlen : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨2710⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨11163⟩ (⟨2735⟩ :: R)
      mem aw rdata σ k' C' := by
  have h1 := metaMorphoV1_1_block_2710_fallthrough (immWords := wordsOf (immStore v))
    (by omega) hwv rd
  have h2 := metaMorphoV1_1_block_2716_fallthrough (immWords := wordsOf (immStore v))
    hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_32 hlen hhi hsize) h1
  have h3 := metaMorphoV1_1_block_2728 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  exact ⟨_, _, h3⟩

theorem skimRecipientWord (evm : State) :
    UInt256.ofNat (skimRecipientAddress evm).toNat = UInt256.land solcAddrMask
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨19⟩) := by
  change EVM.word (AccountAddress.ofNat (UInt256.land _ solcAddrMask).toNat).val = _
  rw [word_of_addressOfNat_eq_mask, solcAddrMask_clean (solcAddrMask_result_canonical _),
    u256_land_comm]

theorem skimRecipientWord_nonzero (evm : State)
    (hne : skimRecipientAddress evm ≠ ⟨0, by decide⟩) :
    UInt256.ofNat (skimRecipientAddress evm).toNat ≠ ⟨0⟩ := by
  intro hw
  apply hne
  have h := congrArg (fun w : UInt256 ↦ AccountAddress.ofNat w.toNat) hw
  change AccountAddress.ofNat (EVM.word (skimRecipientAddress evm).val).toNat =
    (⟨0, by decide⟩ : AccountAddress) at h
  rw [accountAddress_of_word_val] at h
  exact h

theorem skimReachBalance {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {token : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hs : SourceState s0 I σ evm) (hne : skimRecipientAddress evm ≠ ⟨0, by decide⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨2735⟩ (token :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨2755⟩
      (token :: UInt256.ofNat (skimRecipientAddress evm).toNat :: R) mem aw' rdata σ k' C' := by
  have hw : UInt256.land solcAddrMask (codeOwnerStorageWord I σ ⟨19⟩) =
      UInt256.ofNat (skimRecipientAddress evm).toNat := by
    rw [skimRecipientWord]
    rw [hs.storageRead]
  obtain ⟨aw', k', C', h⟩ := metaMorphoV1_1_block_2735_fallthrough_packed
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.isZero (UInt256.land solcAddrMask (codeOwnerStorageWord I σ ⟨19⟩)) = ⟨0⟩
      rw [hw]
      exact isZero_eq_zero_of_ne (skimRecipientWord_nonzero evm hne)) rd
  refine ⟨aw', k', C', ?_⟩
  change RD (deployedRuntime v) I g s0 ⟨2755⟩
    (token :: UInt256.land solcAddrMask (codeOwnerStorageWord I σ ⟨19⟩) :: R)
    mem aw' rdata σ k' C' at h
  rwa [hw] at h

theorem skimRevertRecipient {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {token : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hs : SourceState s0 I σ evm) (heq : skimRecipientAddress evm = ⟨0, by decide⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨2735⟩ (token :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hw : UInt256.land solcAddrMask (codeOwnerStorageWord I σ ⟨19⟩) = ⟨0⟩ := by
    have h := skimRecipientWord evm
    rw [heq, hs.storageRead] at h
    exact h.symm
  obtain ⟨_, _, _, h⟩ := metaMorphoV1_1_block_2735_taken_packed
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.isZero (UInt256.land solcAddrMask (codeOwnerStorageWord I σ ⟨19⟩)) ≠ ⟨0⟩
      rw [hw]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_2932 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_2735_taken_stack, List.length_cons]; omega) h

end Benchmarks.Morpho.MetaMorphoV1_1
