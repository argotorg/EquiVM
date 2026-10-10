import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsDecodedMemory

/-! Complete dynamic-array decoding, including every header, allocation, and payload failure. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem extSloadsDecodeReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C base : Nat} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 12 ≤ 1024)
    (hbound : base + out.size ≤ 2 ^ 200) (hlo : 96 ≤ base)
    (hmem : base + out.size ≤ mem.size) (hsep : base + out.size ≤ ptr.toNat)
    (hptr : memLoad ⟨64⟩ mem = ptr)
    (hread : ∀ off, off + 32 ≤ out.size →
      memLoad (UInt256.ofNat (base + off)) mem = calldataWord out off)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13221⟩
      (UInt256.ofNat base :: UInt256.ofNat (base + out.size) :: ret :: R) mem aw out σ k C) :
    ((¬ extSloadsReturnChecks out ∨ ¬ allocationFits ptr (extSloadsArraySize out)) ∧
      RDrev (deployedRuntime v) g s0) ∨
      (extSloadsReturnChecks out ∧ allocationFits ptr (extSloadsArraySize out) ∧
        ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (ptr :: R)
          (extSloadsDecodedMem mem ptr out) aw' out σ k' C') := by
  rcases extSloadsDecodeHeader v (by simp only [List.length_cons]; omega)
      hbound hread rd with ⟨hbad, hrev⟩ | ⟨hheader, aw1, k1, C1, h1⟩
  · exact .inl ⟨.inl (fun hc => hbad (extSloadsReturnChecks_header hc)), hrev⟩
  rcases extSloadsDecodeAllocation v (by simp only [List.length_cons]; omega)
      hbound hheader hptr h1 with ⟨hbad, hrev⟩ | ⟨hcheck, hfit, aw2, k2, C2, h2⟩
  · exact .inl ⟨hbad, hrev⟩
  have h3 := metaMorphoV1_1_block_13309 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) h2
  have halloc := extSloadsArrayBound hcheck.length hfit
  have hptr32 : ptr.toNat + 32 < UInt256.size := by change _ < 2 ^ 256; omega
  have hp : ptr + ⟨32⟩ = UInt256.ofNat (ptr.toNat + 32) := by
    apply u256_inj
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from rfl,
      Nat.mod_eq_of_lt hptr32, UInt256.toNat_ofNat_of_lt hptr32]
  simp only [metaMorphoV1_1_block_13309_stack, hp, ofNat_add_words,
    show 32 + (base + extSloadsReturnOffset out) =
      base + extSloadsReturnOffset out + 32 from by omega,
    show base + extSloadsReturnOffset out + 32 * extSloadsReturnCount out + 32 =
      base + extSloadsReturnOffset out + 32 + 32 * (extSloadsReturnWords out).length from by
        rw [extSloadsReturnWords_length]; omega] at h3
  have hcopyread : ∀ i (hi : i < (extSloadsReturnWords out).length),
      memLoad (UInt256.ofNat (base + extSloadsReturnOffset out + 32 + 32 * i))
        (extSloadsArrayHeaderMem mem ptr out) = (extSloadsReturnWords out)[i] := by
    intro i hi
    rw [extSloadsReturnWords_get out i hi]
    have hi' : i < extSloadsReturnCount out := by rwa [extSloadsReturnWords_length] at hi
    have hin : extSloadsReturnOffset out + 32 + 32 * i + 32 ≤ out.size := by
      have hb := hcheck.data
      change extSloadsReturnOffset out + 32 + 32 * extSloadsReturnCount out ≤ out.size at hb
      omega
    have he : base + extSloadsReturnOffset out + 32 + 32 * i =
        base + (extSloadsReturnOffset out + 32 + 32 * i) := by omega
    rw [he]
    exact extSloadsArrayHeaderMem_load hlo hmem hsep hin (hread _ hin)
  have hdata := hcheck.data
  change extSloadsReturnOffset out + 32 + 32 * extSloadsReturnCount out ≤ out.size at hdata
  obtain ⟨aw3, k3, C3, hdone⟩ := extSloadsCopyLoop v (extSloadsReturnWords out)
    (by omega)
    (by rw [extSloadsReturnWords_length]
        simp only [extSloadsArrayHeaderMem, writeWord_sparse_size]; omega)
    (by rw [extSloadsReturnWords_length]; omega)
    (by rw [extSloadsReturnWords_length]; change _ < 2 ^ 256; omega)
    hcopyread hret h3
  exact .inr ⟨hcheck, hfit, aw3, k3, C3, hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
