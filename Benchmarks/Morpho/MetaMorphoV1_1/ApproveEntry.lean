import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_053
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_023

/-! Calldata guards and return encoding for public approval. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem approveReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨10846⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11163⟩
      (⟨10874⟩ :: ⟨4161⟩ :: R) mem aw' rdata σ k' C' := by
  have h1 := metaMorphoV1_1_block_10846_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have h2 := metaMorphoV1_1_block_10852_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨64⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_64 hsz hhi hsize) h1
  exact metaMorphoV1_1_block_10864_packed (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

theorem approveRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨10846⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_10846_taken (immWords := wordsOf (immStore v))
    hstack hwv (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack h1

theorem approveRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨64⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨10846⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_10846_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have h2 := metaMorphoV1_1_block_10852_taken (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) h2

theorem approveRevertNoncanonical {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨10846⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, _, h1⟩ := approveReachDecoder v (by omega) hwv hsz hhi hsize rd
  exact decodeAddressAt4Revert v (by simp only [List.length_cons]; omega) hnc h1

theorem approveReachFunction {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨10846⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨16692⟩
      (UInt256.ofNat I.source.toNat ::
        UInt256.ofNat (AccountAddress.ofNat (calldataWord I.calldata 4).toNat).toNat ::
        calldataWord I.calldata 36 :: ⟨4161⟩ :: R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := approveReachDecoder v (by omega) hwv hsz hhi hsize rd
  obtain ⟨k2, C2, h2⟩ := decodeAddressAt4 v (by simp only [List.length_cons]; omega)
    hcanon (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  have heq : UInt256.ofNat (AccountAddress.ofNat (calldataWord I.calldata 4).toNat).toNat =
      calldataWord I.calldata 4 := by
    simpa only [keyValueToWord_address, Fin.toNat] using
      keyValueToWord_address_of_canonical _ hcanon
  rw [heq]
  exact metaMorphoV1_1_block_10874_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

theorem approveEncodeReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨4161⟩ R mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (UInt256.ofNat 1).toByteArray := by
  have h := metaMorphoV1_1_block_4161 (immWords := wordsOf (immStore v)) hstack rd
  change RDret _ _ _ _ ((writeWord mem (memLoad ⟨64⟩ mem).toNat ⟨1⟩).readWithPadding
    (memLoad ⟨64⟩ mem).toNat 32) at h
  rw [writeWord_sparse_read_back] at h
  exact h

end Benchmarks.Morpho.MetaMorphoV1_1
