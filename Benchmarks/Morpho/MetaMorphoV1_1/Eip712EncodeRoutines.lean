import Benchmarks.Morpho.MetaMorphoV1_1.Eip712FinishRoutines

/-! Composition of the two string encoders and the final domain return. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000
set_option autoImplicit false

theorem eip712EncodeReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (name version : ByteArray)
    (namePtr versionPtr arrayPtr out : Nat)
    (hstack : R.length + 14 ≤ 1024)
    (hname : name.size < 2 ^ 255) (hversion : version.size < 2 ^ 255)
    (hfit : out + 320 + paddedSize name.size + paddedSize version.size < UInt256.size)
    (hnameLo : 96 ≤ namePtr) (hversionLo : 96 ≤ versionPtr) (harrayLo : 96 ≤ arrayPtr)
    (hnameBelow : namePtr + 32 + paddedSize name.size ≤ out)
    (hversionBelow : versionPtr + 32 + paddedSize version.size ≤ out)
    (harrayBelow : arrayPtr + 32 ≤ out) (hmem : out ≤ mem.size)
    (hnameBuffer : StringBuffer mem namePtr name)
    (hversionBuffer : StringBuffer mem versionPtr version)
    (harray : memLoad (UInt256.ofNat arrayPtr) mem = ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨11086⟩
      (UInt256.ofNat namePtr :: UInt256.ofNat (out + 224) :: ⟨5104⟩ ::
        UInt256.ofNat versionPtr :: ⟨5118⟩ :: ⟨32⟩ :: UInt256.ofNat arrayPtr ::
        UInt256.ofNat out :: UInt256.ofNat out :: R)
      (eip712StartMemory mem out) aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (eip712ReturnBytes I name version) := by
  have hnfit : name.size < UInt256.size := lt_trans hname (by decide)
  have hvfit : version.size < UInt256.size := lt_trans hversion (by decide)
  have hn := UInt256.toNat_ofNat_of_lt hnfit
  have hv := UInt256.toNat_ofNat_of_lt hvfit
  have hnstart := eip712StartMemory_buffer hnameBuffer hnameLo (by omega) hnameBelow
  have hvstart := eip712StartMemory_buffer hversionBuffer hversionLo (by omega) hversionBelow
  obtain ⟨hnamePrefix, hnameSize, hnameHead, hnameData⟩ := eip712NameMemory_facts
    mem name namePtr out (by omega) hnfit hnstart hnameBelow
  have hvbefore := hvstart.preserve hnamePrefix hversionLo (by omega) hversionBelow
  obtain ⟨hfinalSize, hfinalHead, hfinalData⟩ := eip712VersionMemory_facts
    mem name version namePtr versionPtr out (by omega) hvfit hvbefore hversionBelow
    hnameSize hnameHead hnameData
  have hvdata : versionPtr + 32 + (UInt256.ofNat version.size).toNat ≤
      (eip712NameMemory mem namePtr out name).size := by
    rw [hv]
    have := hvbefore.size
    have : version.size ≤ paddedSize version.size := by unfold paddedSize; omega
    omega
  have hfinalPrefix : MemoryPrefix mem
      (eip712VersionMemory mem namePtr versionPtr out name version) out :=
    ((eip712StartMemory_prefix mem out).trans hnamePrefix).trans
      ((stringPayloadMemory_prefix _ (versionPtr + 32) (out + 256 + paddedSize name.size)
        (UInt256.ofNat version.size) hvdata).mono (by omega))
  have hfinalArray : memLoad (UInt256.ofNat arrayPtr)
      (eip712VersionMemory mem namePtr versionPtr out name version) = ⟨0⟩ :=
    (hfinalPrefix.load_preserved harrayLo harrayBelow (by omega) (by omega)).trans harray
  obtain ⟨aw1, k1, C1, h1⟩ := stringEncoderRoutine v namePtr (out + 224)
    (UInt256.ofNat name.size) (by simp only [List.length_cons]; omega)
    (by rw [hn]; exact hname) (by omega) (by rw [hn]; omega) hnstart.length
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  simp only [hn] at h1
  change RD _ I g s0 ⟨5104⟩
    (UInt256.ofNat (out + 256 + paddedSize name.size) :: UInt256.ofNat versionPtr ::
      ⟨5118⟩ :: ⟨32⟩ :: UInt256.ofNat arrayPtr :: UInt256.ofNat out :: UInt256.ofNat out :: R)
    (stringPayloadMemory (eip712StartMemory mem out) (namePtr + 32) (out + 224)
      (UInt256.ofNat name.size)) aw1 rdata σ k1 C1 at h1
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_5104_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  have hdiff : UInt256.sub (UInt256.ofNat (out + 256 + paddedSize name.size))
      (UInt256.ofNat out) = UInt256.ofNat (256 + paddedSize name.size) := by
    rw [ofNat_sub_words (by omega) (by omega)]
    congr 1
    omega
  have h64 : (UInt256.ofNat out + UInt256.ofNat 64).toNat = out + 64 := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt (by omega)]
  simp only [metaMorphoV1_1_block_5104_stack, metaMorphoV1_1_block_5104_memory,
    hdiff, h64] at h2
  change RD _ I g s0 ⟨11086⟩
    (UInt256.ofNat versionPtr :: UInt256.ofNat (out + 256 + paddedSize name.size) ::
      ⟨5118⟩ :: ⟨32⟩ :: UInt256.ofNat arrayPtr :: UInt256.ofNat out :: UInt256.ofNat out :: R)
    (eip712NameMemory mem namePtr out name) aw2 rdata σ k2 C2 at h2
  obtain ⟨aw3, k3, C3, h3⟩ := stringEncoderRoutine v versionPtr
    (out + 256 + paddedSize name.size) (UInt256.ofNat version.size)
    (by simp only [List.length_cons]; omega) (by rw [hv]; exact hversion) (by omega)
    (by rw [hv]; omega) hvbefore.length
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
  simp only [hv] at h3
  rw [show out + 256 + paddedSize name.size + 32 + paddedSize version.size =
    out + 288 + paddedSize name.size + paddedSize version.size by omega] at h3
  exact eip712FinishReturn v name version arrayPtr out (by omega) hfit harrayBelow
    hfinalArray hfinalSize hfinalHead hfinalData h3

end Benchmarks.Morpho.MetaMorphoV1_1
