import Benchmarks.Morpho.MetaMorphoV1_1.StringCopyMemory
import Benchmarks.Morpho.MetaMorphoV1_1.StringStorageHash
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_025

/-! Routing either metadata getter into short copying or its storage-word loop. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem stringCopyShortStart {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {header len : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 7 ≤ 1024)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringCopyPC symbol)
      (len :: header :: ⟨0⟩ :: ⟨128⟩ :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨4753⟩
      (header :: UInt256.land header ⟨1⟩ :: len :: ⟨0⟩ :: ⟨128⟩ :: R)
      (Reasoning.Theory.writeWord mem 128 len) aw' rdata σ k' C' := by
  have hc : UInt256.isZero (UInt256.land header (UInt256.ofNat 1)) ≠ UInt256.ofNat 0 := by
    change UInt256.isZero (UInt256.land header ⟨1⟩) ≠ ⟨0⟩
    rw [hflag]
    decide
  cases symbol with
  | false =>
      exact metaMorphoV1_1_block_10916_taken_packed (immWords := wordsOf (immStore v))
        hstack hc (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  | true =>
      exact metaMorphoV1_1_block_4619_taken_packed (immWords := wordsOf (immStore v))
        hstack hc (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

theorem stringCopyLongStart {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {header len : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 7 ≤ 1024)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (stringCopyPC symbol)
      (len :: header :: ⟨0⟩ :: ⟨128⟩ :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (stringCopyLoopPC symbol)
      (len :: ⟨0⟩ :: ⟨128⟩ :: solidityBytesDataBaseSlot (stringViewSlot symbol) :: R)
      (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem 128 len)
        0 (stringViewSlot symbol)) aw' rdata σ k' C' := by
  have hc : UInt256.eq (UInt256.ofNat 1) (UInt256.land header (UInt256.ofNat 1)) ≠
      UInt256.ofNat 0 := by
    change UInt256.eq ⟨1⟩ (UInt256.land header ⟨1⟩) ≠ ⟨0⟩
    rw [land_one_eq_one_of_ne_zero hflag]
    decide
  have hfirst : ∃ aw1 k1 C1, RD (deployedRuntime v) I g s0
      (if symbol then ⟨4635⟩ else ⟨10932⟩)
      (header :: UInt256.land header ⟨1⟩ :: len :: ⟨0⟩ :: ⟨128⟩ :: R)
      (Reasoning.Theory.writeWord mem 128 len) aw1 rdata σ k1 C1 := by
    cases symbol with
    | false =>
        exact metaMorphoV1_1_block_10916_fallthrough_packed
          (immWords := wordsOf (immStore v)) hstack (isZero_eq_zero_of_ne hflag) rd
    | true =>
        exact metaMorphoV1_1_block_4619_fallthrough_packed
          (immWords := wordsOf (immStore v)) hstack (isZero_eq_zero_of_ne hflag) rd
  obtain ⟨aw1, k1, C1, h1⟩ := hfirst
  have hsecond : ∃ aw2 k2 C2, RD (deployedRuntime v) I g s0
      (if symbol then ⟨4659⟩ else ⟨10955⟩) (len :: ⟨0⟩ :: ⟨128⟩ :: R)
      (Reasoning.Theory.writeWord mem 128 len) aw2 rdata σ k2 C2 := by
    cases symbol with
    | false =>
        exact metaMorphoV1_1_block_10932_taken_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) hc
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    | true =>
        exact metaMorphoV1_1_block_4635_taken_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) hc
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  obtain ⟨aw2, k2, C2, h2⟩ := hsecond
  cases symbol with
  | false =>
      obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_10955_packed
        (immWords := wordsOf (immStore v)) (by omega) h2
      have hhash : (UInt256.ofNat
          80167465652159884487584418398737133515478493586045375474096367959472086682926) =
          solidityBytesDataBaseSlot ⟨24⟩ := stringStorageHash_eq false
      exact ⟨aw3, k3, C3, by
        simpa only [metaMorphoV1_1_block_10955_stack, hhash] using h3⟩
  | true =>
      obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_4659_packed
        (immWords := wordsOf (immStore v)) (by omega) h2
      have hhash : (UInt256.ofNat
          67072331549493647622825787457569556318728415786901242217649037894484240406165) =
          solidityBytesDataBaseSlot ⟨25⟩ := stringStorageHash_eq true
      exact ⟨aw3, k3, C3, by
        simpa only [metaMorphoV1_1_block_4659_stack, hhash] using h3⟩

theorem stringCopyLongFinish {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {len off ptr slot : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 (stringCopyLoopExitPC symbol)
      (len :: off :: ptr :: slot :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨4643⟩
      (UInt256.ofNat 2379 :: (UInt256.ofNat 32 + (ptr + off)) :: ptr :: R)
      mem aw' rdata σ k' C' := by
  cases symbol with
  | false =>
      exact metaMorphoV1_1_block_11007_packed (immWords := wordsOf (immStore v)) hstack
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  | true =>
      exact metaMorphoV1_1_block_4711_packed (immWords := wordsOf (immStore v)) hstack
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

end Benchmarks.Morpho.MetaMorphoV1_1
