import Benchmarks.Morpho.MetaMorphoV1_1.Eip712EncodeMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_028

/-! Final scalar fields and the zero-length extensions loop of `eip712Domain`. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000
set_option autoImplicit false

theorem eip712FinishReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (name version : ByteArray) (arrayPtr out : Nat)
    (hstack : R.length + 10 ≤ 1024)
    (hfit : out + 320 + paddedSize name.size + paddedSize version.size < UInt256.size)
    (harray : arrayPtr + 32 ≤ out)
    (hload : memLoad (UInt256.ofNat arrayPtr) mem = ⟨0⟩)
    (hmem : out + 288 + paddedSize name.size + paddedSize version.size ≤ mem.size)
    (hhead : mem.readWithPadding out 96 = wordBytes (eip712HeadPrefixWords name))
    (htail : mem.readWithPadding (out + 224)
      (64 + paddedSize name.size + paddedSize version.size) =
        stringPayloadBytes name ++ stringPayloadBytes version)
    (rd : RD (deployedRuntime v) I g s0 ⟨5118⟩
      (UInt256.ofNat (out + 288 + paddedSize name.size + paddedSize version.size) ::
        ⟨32⟩ :: UInt256.ofNat arrayPtr :: UInt256.ofNat out :: UInt256.ofNat out :: R)
      mem aw rdata σ k C) : RDret (deployedRuntime v) g s0 σ (eip712ReturnBytes I name version) :=
    by
  have hadd (n : Nat) (hn : out + n < UInt256.size) :
      (UInt256.ofNat out + UInt256.ofNat n).toNat = out + n := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt hn]
  have hsub : UInt256.sub
      (UInt256.ofNat (out + 288 + paddedSize name.size + paddedSize version.size))
      (UInt256.ofNat out) =
      UInt256.ofNat (288 + paddedSize name.size + paddedSize version.size) := by
    rw [ofNat_sub_words (by omega) (by omega)]
    congr 1
    omega
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_5118_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) rd
  simp only [metaMorphoV1_1_block_5118_stack, metaMorphoV1_1_block_5118_memory, hsub,
    hadd 96 (by omega), hadd 128 (by omega), hadd 160 (by omega), hadd 192 (by omega),
    UInt256.toNat_ofNat_of_lt (show
      out + 288 + paddedSize name.size + paddedSize version.size < UInt256.size by omega)] at h1
  change RD _ I g s0 ⟨5158⟩
    (⟨0⟩ :: ⟨32⟩ :: memLoad (UInt256.ofNat arrayPtr)
      (wordSequenceMemory mem (out + 96) (eip712HeadSuffixWords I name version)) ::
      (UInt256.ofNat arrayPtr + UInt256.ofNat 32) ::
      (UInt256.ofNat (out + 288 + paddedSize name.size + paddedSize version.size) +
        UInt256.ofNat 32) :: UInt256.ofNat out :: UInt256.ofNat out :: R)
    (writeWord (wordSequenceMemory mem (out + 96) (eip712HeadSuffixWords I name version))
      (out + 288 + paddedSize name.size + paddedSize version.size)
      (memLoad (UInt256.ofNat arrayPtr)
        (wordSequenceMemory mem (out + 96) (eip712HeadSuffixWords I name version))))
    aw1 rdata σ k1 C1 at h1
  have hz := (wordSequenceMemory_load_below (eip712HeadSuffixWords I name version)
    (by omega : arrayPtr + 32 ≤ mem.size) (by omega : arrayPtr + 32 ≤ out + 96)
    (by omega : arrayPtr < UInt256.size)).trans hload
  rw [hz, ofNat_add_words, ofNat_add_words] at h1
  have h2 := metaMorphoV1_1_block_5158_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by decide) h1
  have h3 := metaMorphoV1_1_block_5166 (immWords := wordsOf (immStore v)) (by omega) h2
  have hdiff : (UInt256.sub
      (UInt256.ofNat (out + 288 + paddedSize name.size + paddedSize version.size + 32))
      (UInt256.ofNat out)).toNat = 320 + paddedSize name.size + paddedSize version.size := by
    rw [usub_ofNat_lit_toNat (by omega) (by omega)]
    omega
  have hread := eip712FinishMemory_read I mem name version out hmem hhead htail
  simp only [eip712FinishMemory] at hread
  simpa only [UInt256.toNat_ofNat_of_lt (show out < UInt256.size by omega), hdiff,
    hread] using h3

end Benchmarks.Morpho.MetaMorphoV1_1
