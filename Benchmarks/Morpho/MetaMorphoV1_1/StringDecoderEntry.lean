import Benchmarks.Morpho.MetaMorphoV1_1.StringCalldata
import Benchmarks.Morpho.MetaMorphoV1_1.CalldataBytesRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.Decode

/-! Offset and length-word validation in the shared single-string ABI decoder. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

structure StringCalldataHeader (cd : ByteArray) : Prop where
  head : 36 ≤ cd.size
  size : cd.size < 2 ^ 255
  offset : (calldataWord cd 4).toNat < 2 ^ 64
  lengthWord : (calldataWord cd 4).toNat + 36 ≤ cd.size

theorem stringDecoderPrefix {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables) (param : Ident)
    (hstack : R.length + 7 ≤ 1024) (h4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨11698⟩
      (UInt256.ofNat I.calldata.size :: ret :: R) mem aw out σ k C) :
    (decodeCalldata [param] [.string] I.calldata = none ∧ RDrev (deployedRuntime v) g s0) ∨
    (StringCalldataHeader I.calldata ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨11644⟩
        (calldataStringStart I.calldata :: calldataStringLength I.calldata ::
          UInt256.ofNat I.calldata.size :: ⟨11757⟩ :: ret :: R) mem aw' out σ k' C') := by
  by_cases hhead : 36 ≤ I.calldata.size
  case neg =>
    have h1 := metaMorphoV1_1_block_11698_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by
        change UInt256.slt (UInt256.ofNat I.calldata.size + UInt256.lnot ⟨3⟩) ⟨32⟩ ≠ ⟨0⟩
        rw [u256_add_comm, calldataNot3_eq_sub h4 hsize,
          solcDecodeLenCheckShort_4_32 h4 (by omega) hsize]
        decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨decodeCalldataStringShort I.calldata param (by omega),
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) h1⟩
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  case neg =>
    have h1 := metaMorphoV1_1_block_11698_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by
        change UInt256.slt (UInt256.ofNat I.calldata.size + UInt256.lnot ⟨3⟩) ⟨32⟩ ≠ ⟨0⟩
        rw [u256_add_comm, calldataNot3_eq_sub h4 hsize,
          solcDecodeLenCheckHuge_4_32 (Nat.le_of_not_gt hhi) hsize]
        decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨decodeCalldata_string_none_huge (by omega),
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) h1⟩
  have h1 := metaMorphoV1_1_block_11698_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by
      change UInt256.slt (UInt256.ofNat I.calldata.size + UInt256.lnot ⟨3⟩) ⟨32⟩ = ⟨0⟩
      rw [u256_add_comm, calldataNot3_eq_sub h4 hsize]
      exact solcDecodeLenCheckOk_4_32 hhead hhi hsize) rd
  by_cases hoff : (calldataWord I.calldata 4).toNat < 2 ^ 64
  case neg =>
    have h2 := metaMorphoV1_1_block_11711_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by
        rw [ugt_one (by change 2 ^ 64 - 1 < (calldataWord I.calldata 4).toNat; omega)]
        decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    exact .inl ⟨decodeCalldata_string_none_offset_huge hhead (by unfold solcMaxU64; omega),
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by
        simp only [metaMorphoV1_1_block_11711_taken_stack, List.length_cons]; omega) h2⟩
  have h2 := metaMorphoV1_1_block_11711_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (ugt_zero (by change (calldataWord I.calldata 4).toNat ≤ 2 ^ 64 - 1; omega)) h1
  simp only [metaMorphoV1_1_block_11711_fallthrough_stack] at h2
  have hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat := by
    unfold solcMaxU64; omega
  have h35 : calldataWord I.calldata 4 + UInt256.ofNat 35 =
      ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩ := by
    rw [u256_add_comm (⟨4⟩ : UInt256), u256_add_assoc]
    rfl
  by_cases hsign : I.calldata.size < 2 ^ 255
  case neg =>
    have h3 := metaMorphoV1_1_block_11729_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by
        change UInt256.isZero (UInt256.slt (calldataWord I.calldata 4 + _) _) ≠ _
        rw [h35, calldataStart_slt_zero_of_size_high I.calldata hoffMax hsize hsign]
        decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    exact .inl ⟨decodeCalldata_string_none_total_huge (by omega),
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) h3⟩
  by_cases hword : (calldataWord I.calldata 4).toNat + 36 ≤ I.calldata.size
  case neg =>
    have h3 := metaMorphoV1_1_block_11729_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by
        change UInt256.isZero (UInt256.slt (calldataWord I.calldata 4 + _) _) ≠ _
        rw [h35, slt_lit_zero hsign (by
          rw [calldataStartPlus31_toNat I.calldata hoffMax]; omega) (by
          rw [calldataStartPlus31_toNat I.calldata hoffMax]; omega)]
        decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    exact .inl ⟨decodeCalldata_string_none_length_short hhead hhi (by omega),
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) h3⟩
  have h3 := metaMorphoV1_1_block_11729_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by
      change UInt256.isZero (UInt256.slt (calldataWord I.calldata 4 + _) _) = _
      rw [h35, calldataStart_slt_one I.calldata hoffMax (by omega) hsign]
      decide) h2
  obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_11740_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
  have hload : uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32) =
      calldataWord I.calldata 4 := rfl
  have hlen : uInt256OfByteArray (I.calldata.readBytes
      (UInt256.ofNat 4 + calldataWord I.calldata 4).toNat 32) =
      calldataStringLength I.calldata := calldataLengthWord_eq_abi I.calldata hoffMax
  simp only [metaMorphoV1_1_block_11740_stack, hload, hlen] at h4
  exact .inr ⟨⟨hhead, hsign, hoff, hword⟩, aw4, k4, C4, h4⟩

end Benchmarks.Morpho.MetaMorphoV1_1
