import Benchmarks.Morpho.MetaMorphoV1_1.FallbackStringMemory

/-! Header decoding and the short/long branches of the generic storage-string copier. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem fallbackStringReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {base ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨11857⟩ (base :: ptr :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11801⟩
      (codeOwnerStorageWord I σ base :: ⟨11872⟩ :: base :: ptr ::
        codeOwnerStorageWord I σ base :: ret :: ⟨0⟩ :: R) mem aw' rdata σ k' C' := by
  exact metaMorphoV1_1_block_11857_packed (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

theorem storageStringBaseHash (mem : ByteArray) (base : UInt256) :
    keccakWord ⟨0⟩ ⟨32⟩ (writeWord mem 0 base) = solidityBytesDataBaseSlot base := by
  unfold keccakWord
  change UInt256.ofNat (fromByteArrayBigEndian
    (KEC ((writeWord mem 0 base).readWithPadding 0 32))) = _
  rw [writeWord_sparse_read_back, solidityBytesDataBaseSlot, uInt256OfByteArray_eq]

theorem fallbackStringLongStart {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {base ptr ret header len : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨11872⟩
      (len :: base :: ptr :: header :: ret :: ⟨0⟩ :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11914⟩
      (solidityBytesDataBaseSlot base :: ptr :: ⟨0⟩ :: len :: ret :: R)
      (writeWord (writeWord mem ptr.toNat len) 0 base) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_11872_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (isZero_eq_zero_of_ne hflag) rd
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_11888_taken_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) (by
      change UInt256.eq ⟨1⟩ (UInt256.land header ⟨1⟩) ≠ ⟨0⟩
      rw [land_one_eq_one_of_ne_zero hflag]
      decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_11900_packed
    (immWords := wordsOf (immStore v)) (by omega) h2
  refine ⟨aw3, k3, C3, ?_⟩
  change RD _ _ _ _ _
    (keccakWord ⟨0⟩ ⟨32⟩ (writeWord (writeWord mem ptr.toNat len) 0 base) ::
      ptr :: ⟨0⟩ :: len :: ret :: R) _ _ _ _ _ _ at h3
  rw [storageStringBaseHash] at h3
  exact h3

theorem fallbackStringShortReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {base ret header : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (free : Nat) (hstack : R.length + 9 ≤ 1024)
    (hfit : free + 64 < UInt256.size)
    (hvalid : storageStringValid header) (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11872⟩
      (storageStringLength header :: base :: UInt256.ofNat free :: header :: ret :: ⟨0⟩ :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
      (UInt256.ofNat (free + 32 + 32 * stringWordCount (storageStringLength header)) :: R)
      (fallbackStringMemory I σ mem base header free) aw' rdata σ k' C' := by
  have hl := storageStringShortLength header hvalid hflag
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_11872_taken_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by change UInt256.isZero (UInt256.land header ⟨1⟩) ≠ ⟨0⟩; rw [hflag]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_11957_packed
    (immWords := wordsOf (immStore v)) (by omega) hret h1
  have hf : (UInt256.ofNat free).toNat = free := UInt256.toNat_ofNat_of_lt (by omega)
  have ha : (UInt256.ofNat free + UInt256.ofNat 32).toNat = free + 32 := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt (by omega)]
  have hend : (UInt256.shiftLeft
      (UInt256.isZero (UInt256.isZero (storageStringLength header))) (UInt256.ofNat 5) +
      UInt256.ofNat free) + UInt256.ofNat 32 =
      UInt256.ofNat (free + 32 + 32 * stringWordCount (storageStringLength header)) := by
    by_cases hz : storageStringLength header = ⟨0⟩
    · rw [hz]
      change (⟨0⟩ : UInt256) + UInt256.ofNat free + UInt256.ofNat 32 = _
      rw [u256_zero_add, ofNat_add_words]
      rfl
    · have hn : (storageStringLength header).toNat ≠ 0 :=
        fun h ↦ hz (uint256_toNat_eq_zero h)
      have hc : stringWordCount (storageStringLength header) = 1 := by
        unfold stringWordCount
        omega
      rw [isZero_eq_zero_of_ne hz, hc]
      change (UInt256.ofNat 32 + UInt256.ofNat free) + UInt256.ofNat 32 = _
      rw [ofNat_add_words, ofNat_add_words]
      congr 1
      omega
  refine ⟨aw2, k2, C2, ?_⟩
  simpa only [metaMorphoV1_1_block_11957_stack, metaMorphoV1_1_block_11957_memory,
    metaMorphoV1_1_block_11872_taken_memory, hf, ha, hend,
    fallbackStringMemory, if_pos hflag] using h2

end Benchmarks.Morpho.MetaMorphoV1_1
