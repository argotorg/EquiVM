import Benchmarks.Morpho.MetaMorphoV1_1.StringEncoderMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_055
import Benchmarks.EAS.Attester.WordHelpers

/-! The shared dynamic-string encoder, independent of its source and destination pointers. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000
set_option autoImplicit false

theorem stringEncoderRoundedSize (len : UInt256) (hlen : len.toNat < 2 ^ 255) :
    UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (UInt256.ofNat 31 + len) =
      UInt256.ofNat (ABI.paddedSize len.toNat) := by
  rw [u256_land_comm, u256_add_comm]
  change roundedSize len = _
  apply u256_inj
  rw [roundedSize_toNat, Nat.mod_eq_of_lt (show len.toNat + 31 < UInt256.size by
    change _ < 2 ^ 256; omega), UInt256.toNat_ofNat_of_lt (by
      change 32 * ((len.toNat + 31) / 32) < 2 ^ 256; omega)]
  exact Nat.mul_comm _ _

theorem stringEncoderRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (src dest : Nat) (len : UInt256)
    (hstack : R.length + 8 ≤ 1024) (hlen : len.toNat < 2 ^ 255)
    (hsrc : src + 32 < UInt256.size)
    (hfit : dest + 32 + paddedSize len.toNat + 32 < UInt256.size)
    (hload : memLoad (UInt256.ofNat src) mem = len)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11086⟩
      (UInt256.ofNat src :: UInt256.ofNat dest :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
      (UInt256.ofNat (dest + 32 + paddedSize len.toNat) :: R)
      (stringPayloadMemory mem (src + 32) dest len) aw' rdata σ k' C' := by
  have hp : len.toNat ≤ paddedSize len.toNat := by unfold paddedSize; omega
  obtain ⟨aw', k', C', h⟩ := metaMorphoV1_1_block_11086_packed
    (immWords := wordsOf (immStore v)) hstack hret rd
  have hzero : UInt256.ofNat 32 + (len + UInt256.ofNat dest) =
      UInt256.ofNat (dest + 32 + len.toNat) := by
    nth_rw 1 [← u256_ofNat_toNat len]
    rw [ofNat_add_words, ofNat_add_words]
    congr 1
    omega
  have hend : (UInt256.ofNat (paddedSize len.toNat) + UInt256.ofNat dest) +
      UInt256.ofNat 32 = UInt256.ofNat (dest + 32 + paddedSize len.toNat) := by
    rw [ofNat_add_words, ofNat_add_words]
    congr 1
    omega
  have hsource : (UInt256.ofNat 32 + UInt256.ofNat src).toNat = src + 32 := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt (by omega)]
    omega
  have hdest : (UInt256.ofNat dest + UInt256.ofNat 32).toNat = dest + 32 := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt (by omega)]
  refine ⟨aw', k', C', ?_⟩
  simpa only [metaMorphoV1_1_block_11086_stack, metaMorphoV1_1_block_11086_memory,
    hload, stringEncoderRoundedSize len hlen, hzero, hend, hsource, hdest,
    UInt256.toNat_ofNat_of_lt (show dest < UInt256.size by omega),
    UInt256.toNat_ofNat_of_lt (show dest + 32 + len.toNat < UInt256.size by omega),
    stringPayloadMemory, stringPayloadCopy, Reasoning.Theory.writeWord] using h

end Benchmarks.Morpho.MetaMorphoV1_1
