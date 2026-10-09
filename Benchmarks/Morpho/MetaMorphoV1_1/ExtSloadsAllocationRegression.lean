import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsCall
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_017

/-! Symbolic boundary checks for the return-buffer allocation limit.

The large buffer is a mathematical value; these proofs never evaluate or allocate it.
This file checks the decoder/allocator boundary, not an end-to-end transaction counterexample.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsAllocationRegression

set_option autoImplicit false

private theorem readNatPrefix (word : UInt256) (tail : ByteArray) :
    readNat? (word.toByteArray ++ tail).toList 0 = some word.toNat := by
  have hlen : word.toByteArray.toList.length = 32 := by
    rw [byteArray_toList_eq, Array.length_toList]
    exact toByteArray_size word
  have htake : ((word.toByteArray ++ tail).toList.drop 0).take 32 =
      word.toByteArray.toList := by
    rw [List.drop_zero, byteArray_toList_append,
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  simp only [readNat?, readWord?, readBytes?, htake, hlen, ↓reduceIte,
    bind, Option.bind]
  congr 1
  change (UInt256.ofNat
    (fromByteArrayBigEndian (ByteArray.mk word.toByteArray.toList.toArray))).toNat = _
  have hba : ByteArray.mk word.toByteArray.toList.toArray = word.toByteArray := by
    apply ByteArray.ext
    rw [byteArray_toList_eq]
  rw [hba, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

private theorem readNat_drop (bytes : List UInt8) (off : Nat) :
    readNat? (bytes.drop off) 0 = readNat? bytes off := by
  simp only [readNat?, readWord?, readBytes?, List.drop_zero]

private theorem sourceAcceptsOfReads (out : ByteArray)
    (hsize : out.toList.length < 2 ^ 255) (hmin : 96 ≤ out.toList.length)
    (hoff : readNat? out.toList 0 = some 32)
    (hlen : readNat? out.toList 32 = some 1) :
    ∃ values, config.externalABI.decode? "extSloads" out =
      some [.array values] ∧ values.length = 1 := by
  obtain ⟨values, hvalues, hlength⟩ := decodeABIValue_dynamicArray_bytes32_exists
    hlen (by decide) (by omega)
  refine ⟨values, ?_, hlength⟩
  change (ABI.decodeReturnValues? [.dynamicArray abiBytes32] out).bind
    (fun values => some values) = _
  suffices h : ABI.decodeReturnValues? [.dynamicArray abiBytes32] out =
      some [.array values] by rw [h]; rfl
  unfold ABI.decodeReturnValues?
  rw [if_neg (by simp only [List.isEmpty_cons]; omega)]
  simp only [abiTupleHeadSize?, isDynamicABIType, bind, Option.bind,
    decodeABIValues?, Nat.zero_add, hoff, solcMaxLen,
    show ¬ solcMaxU64 < 32 from by decide, ↓reduceIte, hvalues]

def oversizedReturn : ByteArray :=
  (⟨32⟩ : UInt256).toByteArray ++
    ((⟨1⟩ : UInt256).toByteArray ++ ByteArray.zeroes (2 ^ 64 - 64))

theorem oversizedReturn_size : oversizedReturn.size = 2 ^ 64 := by
  simp only [oversizedReturn, ByteArray.size_append, toByteArray_size, ByteArray_zeroes_size]
  norm_num

set_option maxRecDepth 2000 in
theorem oversizedReturn_sourceAccepts :
    ∃ values, config.externalABI.decode? "extSloads" oversizedReturn =
      some [.array values] ∧ values.length = 1 := by
  have hlist : oversizedReturn.toList.length = 2 ^ 64 := by
    rw [byteArray_toList_eq, Array.length_toList]
    exact oversizedReturn_size
  have hoff : readNat? oversizedReturn.toList 0 = some 32 :=
    readNatPrefix ⟨32⟩ _
  have hdrop : oversizedReturn.toList.drop 32 =
      ((⟨1⟩ : UInt256).toByteArray ++ ByteArray.zeroes (2 ^ 64 - 64)).toList := by
    change (((⟨32⟩ : UInt256).toByteArray ++ _).toList.drop 32) = _
    rw [byteArray_toList_append, List.drop_append_of_le_length]
    · have h32 : (⟨32⟩ : UInt256).toByteArray.toList.length = 32 := by
        rw [byteArray_toList_eq, Array.length_toList]
        exact toByteArray_size _
      rw [List.drop_eq_nil_of_le (by omega), List.nil_append]
    · rw [byteArray_toList_eq, Array.length_toList]
      exact (toByteArray_size _).ge
  have hlen : readNat? oversizedReturn.toList 32 = some 1 := by
    rw [← readNat_drop]
    rw [hdrop]
    exact readNatPrefix ⟨1⟩ _
  exact sourceAcceptsOfReads oversizedReturn (by rw [hlist]; norm_num)
    (by rw [hlist]; norm_num) hoff hlen

theorem oversizedReturn_allocatorRejects :
    UInt256.lor
      (UInt256.gt ((⟨512⟩ : UInt256) +
        UInt256.land (UInt256.ofNat oversizedReturn.size + ⟨31⟩) (UInt256.lnot ⟨31⟩))
        (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨64⟩) ⟨1⟩))
      (UInt256.lt ((⟨512⟩ : UInt256) +
        UInt256.land (UInt256.ofNat oversizedReturn.size + ⟨31⟩) (UInt256.lnot ⟨31⟩))
        ⟨512⟩) = ⟨1⟩ := by
  rw [oversizedReturn_size]
  decide +kernel

/-- The existing gas-derived bound on opaque return data does not exclude this buffer. -/
theorem oversizedReturn_withinGasDerivedBound :
    oversizedReturn.size ≤ Ethereum.EVM.maxReturnDataSizeByGas := by
  rw [oversizedReturn_size]
  norm_num [Ethereum.EVM.maxReturnDataSizeByGas, Ethereum.EVM.maxReturnDataWordsByGas]

/-- Expanding EVM memory for this return is affordable with a permitted 256-bit gas budget. -/
theorem oversizedReturn_memoryGasFits :
    memExpansionCost ⟨2⟩ ⟨0⟩ (UInt256.ofNat (2 ^ 64)) < 2 ^ 120 ∧
      2 ^ 120 < UInt256.size := by
  decide +kernel

attribute [local irreducible] metaMorphoV1_1Bytecode oversizedReturn

set_option maxRecDepth 2000 in
/-- A successful call returning this buffer reaches the compiler's allocation panic.
The hypothesis is the actual post-call RD state, not a claim that this state is reachable. -/
theorem oversizedReturn_evmReverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨14211⟩ (⟨1⟩ :: ⟨512⟩ :: R)
      mem aw oversizedReturn σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hbranch := metaMorphoV1_1Blocks.metaMorphoV1_1_block_14211_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by decide) rd
  have hcopy := metaMorphoV1_1Blocks.metaMorphoV1_1_block_14217_taken
    (immWords := wordsOf (immStore v)) (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hbranch
  change RD _ _ _ _ _ (⟨512⟩ :: ⟨0⟩ :: ⟨14232⟩ :: R) _ _ _ _ _ _ at hcopy
  have halloc := metaMorphoV1_1Blocks.metaMorphoV1_1_block_14236
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [oversizedReturn_size]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hcopy
  change RD _ _ _ _ _ (⟨512⟩ :: UInt256.ofNat oversizedReturn.size :: ⟨9439⟩ ::
    UInt256.ofNat oversizedReturn.size :: ⟨512⟩ :: ⟨14256⟩ :: ⟨14232⟩ :: R)
    _ _ _ _ _ _ at halloc
  have hpanic := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11329_taken
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by
      intro h
      exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
        (oversizedReturn_allocatorRejects.symm.trans h))
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) halloc
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_2690
    (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_11329_taken_stack,
      List.length_cons]; omega) hpanic

end Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsAllocationRegression
