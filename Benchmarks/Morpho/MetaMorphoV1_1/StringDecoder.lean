import Benchmarks.Morpho.MetaMorphoV1_1.StringDecoderEntry
import Benchmarks.Morpho.MetaMorphoV1_1.CalldataBytesMemory

/-! Complete single-string decoding, with source decode and allocator outcomes. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 600000

theorem stringDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables) (param : Ident)
    (hstack : R.length + 12 ≤ 1024) (h4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hptr : ptr.toNat < 2 ^ 64)
    (hlo : 96 ≤ ptr.toNat) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11698⟩
      (UInt256.ofNat I.calldata.size :: ret :: R) mem aw out σ k C) :
    (decodeCalldata [param] [.string] I.calldata = none ∧ RDrev (deployedRuntime v) g s0) ∨
    (decodeCalldata [param] [.string] I.calldata =
        some ((∅ : Store).insert param (.bytes (calldataStringBytes I.calldata))) ∧
      (calldataStringBytes I.calldata).size < 2 ^ 64 ∧
      ((¬ allocationFits ptr (UInt256.ofNat (32 + (calldataStringBytes I.calldata).size)) ∧
          RDrev (deployedRuntime v) g s0) ∨
        (allocationFits ptr (UInt256.ofNat (32 + (calldataStringBytes I.calldata).size)) ∧
          ∃ mem' aw' k' C', StringBuffer mem' ptr.toNat (calldataStringBytes I.calldata) ∧
            memLoad ⟨64⟩ mem' =
              nextCursor ptr (UInt256.ofNat (32 + (calldataStringBytes I.calldata).size)) ∧
            RD (deployedRuntime v) I g s0 ret (ptr :: R) mem' aw' out σ k' C'))) := by
  rcases stringDecoderPrefix v param (by omega) h4 hsize rd with hbad | ⟨hh, aw1, k1, C1, h1⟩
  · exact .inl hbad
  have hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat := by
    have := hh.offset
    unfold solcMaxU64; omega
  by_cases hl : (calldataStringLength I.calldata).toNat < 2 ^ 64
  case neg =>
    exact .inl ⟨decodeCalldata_string_none_length_huge hh.head
        (by have := hh.size; omega) hoffMax (by have := hh.lengthWord; omega)
        (by change solcMaxU64 < (calldataStringLength I.calldata).toNat
            unfold solcMaxU64; omega),
      calldataBytesLengthRevert v (by simp only [List.length_cons]; omega) (by omega) h1⟩
  have hsum : (calldataStringStart I.calldata + calldataStringLength I.calldata).toNat =
      (calldataWord I.calldata 4).toNat + 36 + (calldataStringLength I.calldata).toNat := by
    rw [uadd_toNat, calldataStringStart_toNat I.calldata hh.offset]
    exact Nat.mod_eq_of_lt (by have := hh.offset; change _ < 2 ^ 256; omega)
  have htotal : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    UInt256.toNat_ofNat_of_lt hsize
  by_cases hp : (calldataWord I.calldata 4).toNat + 36 +
      (calldataStringLength I.calldata).toNat ≤ I.calldata.size
  case neg =>
    have hdec : decodeCalldata [param] [.string] I.calldata = none := by
      apply decodeCalldata_string_none_payload_short hh.head (by have := hh.size; omega)
        hoffMax (by have := hh.lengthWord; omega)
        (by change ¬ solcMaxU64 < (calldataStringLength I.calldata).toNat
            unfold solcMaxU64; omega)
      simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
      change min (calldataStringLength I.calldata).toNat
        (I.calldata.size - 4 - ((calldataWord I.calldata 4).toNat + 32)) ≠
          (calldataStringLength I.calldata).toNat
      have := hh.lengthWord
      omega
    rcases calldataBytesAllocation v (by simp only [List.length_cons]; omega) hl hfree h1
        with ⟨_, hrev⟩ | ⟨_, aw2, k2, C2, h2⟩
    · exact .inl ⟨hdec, hrev⟩
    · exact .inl ⟨hdec, calldataBytesCopyRevert v
        (by simp only [List.length_cons]; omega) (by rw [hsum, htotal]; omega) h2⟩
  have hbytes := calldataStringBytes_size I.calldata hp
  have hdec := decodeCalldataString I.calldata param hh.head hh.size hh.offset hp hl
  refine .inr ⟨hdec, by simpa only [hbytes] using hl, ?_⟩
  rcases calldataBytesAllocation v (by simp only [List.length_cons]; omega) hl hfree h1
      with ⟨hfit, hrev⟩ | ⟨hfit, aw2, k2, C2, h2⟩
  · exact .inl ⟨by simpa only [hbytes] using hfit, hrev⟩
  · refine .inr ⟨by simpa only [hbytes] using hfit, ?_⟩
    obtain ⟨aw3, k3, C3, h3⟩ := calldataBytesCopyReturn v
      (by simp only [List.length_cons]; omega) (by rw [hsum, htotal]; exact hp)
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
    obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_11757_packed
      (immWords := wordsOf (immStore v)) (by omega) hret h3
    have hsrc : (calldataStringStart I.calldata).toNat +
        (calldataStringLength I.calldata).toNat ≤ I.calldata.size := by
      rwa [calldataStringStart_toNat I.calldata hh.offset]
    have hpayload : calldataStringBytes I.calldata = I.calldata.extract
        (calldataStringStart I.calldata).toNat
        ((calldataStringStart I.calldata).toNat + (calldataStringLength I.calldata).toNat) := by
      rw [calldataStringStart_toNat I.calldata hh.offset]
      rfl
    refine ⟨_, aw4, k4, C4, ?_, ?_, h4⟩
    · rw [hpayload]
      exact calldataBytesMemory_buffer mem I.calldata ptr _ _ hptr hl hlo hsrc
    · rw [hbytes, nextCursor_bytesAlloc]
      exact calldataBytesMemory_free mem I.calldata ptr _ _ hptr hl hlo hsrc

end Benchmarks.Morpho.MetaMorphoV1_1
