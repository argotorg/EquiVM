import Benchmarks.Morpho.MetaMorphoV1_1.DecimalScale
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_068

/-! The compiler's decimal exponentiation routine and its overflow branch. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem decimalScaleReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {offset ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (ho : offset.toNat ≤ 77) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨14402⟩
      ([offset, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (decimalScale offset :: R)
      mem aw' rdata σ k' C' := by
  have hm : UInt256.land (UInt256.ofNat 255) offset = offset := by
    rw [u256_land_comm]
    exact lowByteClean (by omega)
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_14402_fallthrough_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [hm]; exact ugt_zero ho) rd
  change RD _ _ _ _ _ (UInt256.land (UInt256.ofNat 255) offset :: ret :: R) _ _ _ _ _ _ at h1
  rw [hm] at h1
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_14414_packed
    (immWords := wordsOf (immStore v)) (by omega) hret h1
  change RD _ _ _ _ _ (UInt256.exp ⟨10⟩ offset :: R) _ _ _ _ _ _ at h2
  rw [decimalScale_exp ho] at h2
  exact ⟨aw2, k2, C2, h2⟩

theorem decimalScaleRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {offset : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (ho : offset.toNat < 256) (hbad : 77 < offset.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨14402⟩
      (offset :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hm : UInt256.land (UInt256.ofNat 255) offset = offset := by
    rw [u256_land_comm]
    exact lowByteClean ho
  have hg : UInt256.gt offset (UInt256.ofNat 77) = ⟨1⟩ := ugt_one hbad
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_14402_taken_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [hm, hg]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_9453 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 2 ≤ 1024; omega) h1

end Benchmarks.Morpho.MetaMorphoV1_1
