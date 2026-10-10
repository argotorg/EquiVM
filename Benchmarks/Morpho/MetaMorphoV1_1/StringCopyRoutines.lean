import Benchmarks.Morpho.MetaMorphoV1_1.StringCopySetup

/-! Both metadata getters' storage copying up to the shared allocator. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem stringCopyToAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {header : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (symbol : Bool) (hstack : R.length + 10 ≤ 1024)
    (hvalid : storageStringValid header)
    (rd : RD (deployedRuntime v) I g s0 (stringCopyPC symbol)
      ([storageStringLength header, header, ⟨0⟩, ⟨128⟩] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11329⟩
      (stringAllocationStack (storageStringLength header) R)
      (stringCopyMemory I σ mem (stringViewSlot symbol) header (storageStringLength header))
      aw' rdata σ k' C' := by
  change RD _ I g s0 (stringCopyPC symbol)
    (storageStringLength header :: header :: ⟨0⟩ :: ⟨128⟩ :: R) mem aw rdata σ k C at rd
  have hlen := storageStringLength_lt header
  have hcopy : ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨4643⟩
      ([⟨2379⟩, stringCopyEnd (storageStringLength header), ⟨128⟩] ++ R)
      (stringCopyMemory I σ mem (stringViewSlot symbol) header (storageStringLength header))
      aw' rdata σ k' C' := by
    by_cases hflag : UInt256.land header ⟨1⟩ = ⟨0⟩
    · obtain ⟨aw1, k1, C1, h1⟩ := stringCopyShortStart v symbol (by omega) hflag rd
      obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_4753_packed
        (immWords := wordsOf (immStore v)) (by omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      change RD _ I g s0 ⟨4643⟩
        (UInt256.ofNat 2379 :: (UInt256.ofNat 32 + (UInt256.ofNat 128 +
          UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (storageStringLength header)))
            (UInt256.ofNat 5))) :: UInt256.ofNat 128 :: R)
        (shortStringCopyMemory mem header (storageStringLength header)) aw2 rdata σ k2 C2 at h2
      refine ⟨aw2, k2, C2, ?_⟩
      simpa only [shortStringEnd _ (storageStringShortLength header hvalid hflag),
        stringCopyMemory, if_pos hflag] using h2
    · obtain ⟨aw3, k3, C3, h3⟩ := stringCopyLongStart v symbol (by omega) hflag rd
      obtain ⟨aw4, k4, C4, h4⟩ := stringCopyLoop v symbol
        (stringWordCount (storageStringLength header)) 0 hstack
        (by unfold stringWordCount; omega)
        (by intro i hi; unfold stringWordCount at hi; omega)
        (by change 128 + 0 + 32 * ((_ + 31) / 32) + 32 < 2 ^ 256; omega) h3
      obtain ⟨aw5, k5, C5, h5⟩ := stringCopyLongFinish v symbol (by omega) h4
      have hend : UInt256.ofNat 32 + (UInt256.ofNat 128 +
          UInt256.ofNat (0 + 32 * stringWordCount (storageStringLength header))) =
          stringCopyEnd (storageStringLength header) := by
        rw [ofNat_add_words, ofNat_add_words]
        congr 1
        omega
      change RD _ I g s0 ⟨4643⟩
        (UInt256.ofNat 2379 :: (UInt256.ofNat 32 + (UInt256.ofNat 128 +
          UInt256.ofNat (0 + 32 * stringWordCount (storageStringLength header)))) ::
          UInt256.ofNat 128 :: R)
        (longStringCopyMemory I σ mem (stringViewSlot symbol) (storageStringLength header))
        aw5 rdata σ k5 C5 at h5
      refine ⟨aw5, k5, C5, ?_⟩
      simpa only [hend, stringCopyMemory, if_neg hflag] using h5
  obtain ⟨aw1, k1, C1, h1⟩ := hcopy
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_4643_packed
    (immWords := wordsOf (immStore v)) (by simpa using (show R.length + 9 ≤ 1024 by omega))
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  refine ⟨aw2, k2, C2, ?_⟩
  simpa only [metaMorphoV1_1_block_4643_stack, stringCopySize_sub _ hlen,
    stringAllocationStack] using h2

end Benchmarks.Morpho.MetaMorphoV1_1
