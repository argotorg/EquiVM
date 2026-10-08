import Benchmarks.EAS.Attester.MultiAttestCallTrace
import Benchmarks.EAS.Attester.WordArrayEncodeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem multiAttestCallBounds {cd : ByteArray} (hc : MultiHeadChecks cd)
    (hshape : BatchShape cd) (hrows : BatchRowsValid cd) :
    multiAttestBuiltFree cd < 2 ^ 138 ∧
      multiAttestEncodedEnd cd - multiAttestBuiltFree cd ≤ maxReturnDataSizeByGas := by
  have hn := uint64Bound_of_isZero_gt hc.first.length
  change arrayCount cd 4 ≤ solcMaxU64 at hn
  have hf := (multiAttestBuiltMemory_bounds hc hshape hrows).2.1
  have he := attestRequestsEncodedEnd_upper
    (dst := multiAttestBuiltFree cd + 4 + 64 + 32 * arrayCount cd 4)
    (counts := multiAttestCounts cd) (i := 0) (remaining := arrayCount cd 4) (cap := solcMaxU64)
    (by intro j hj hj'
        exact uint64Bound_of_isZero_gt (hrows j (by rw [hshape.2]; omega)).1.length)
  change multiAttestEncodedEnd cd ≤ _ at he
  norm_num only [solcMaxU64, maxReturnDataSizeByGas, maxReturnDataWordsByGas] at hn hf he ⊢
  constructor <;> omega

theorem multiAttestReachReturnDecoder {words : String → UInt256} {I g s0 σ k C aw out R}
    {a b c : UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1787⟩
      ([⟨1⟩, a, b, c] ++ R) (multiAttestEncodedMemory I.calldata) aw out σ k C)
    (hstack : R.length + 6 ≤ 1024) (hc : MultiHeadChecks I.calldata)
    (hshape : BatchShape I.calldata) (hrows : BatchRowsValid I.calldata)
    (hout : out.size < 2 ^ 138) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3547⟩
      ([UInt256.ofNat (multiAttestBuiltFree I.calldata),
        UInt256.ofNat (multiAttestBuiltFree I.calldata + out.size), ⟨1873⟩] ++ R)
      (returnArrayInputMemory (multiAttestEncodedMemory I.calldata)
        (multiAttestBuiltFree I.calldata) out) aw' out σ k' C' := by
  have hfree := (multiAttestCallBounds hc hshape hrows).1
  have hfp := multiAttestEncodedMemory_freePtr hc hshape hrows
  have h1 := attesterRuntime_block_1787_taken
    (by simp only [List.append, List.length_cons]; omega) (by decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  obtain ⟨aw2, k2, C2, h2⟩ := attesterRuntime_block_1803_packed
    (by simp only [List.append]; omega)
    (by rw [show (UInt256.ofNat 0).toNat = 0 from rfl, Nat.zero_add,
          ulit_toNat' out.size (by change out.size < 2 ^ 256; omega)])
    (by rw [attesterRuntime_validJumps]; native_decide) h1
  refine ⟨aw2, k2, C2, ?_⟩
  simpa only [attesterRuntime_block_1803_stack, hfp, ofNat_add_words,
    returnArrayInputMemory_summary (out := out) hfp (by omega), List.append] using h2

theorem multiAttestReturnDecoded {words : String → UInt256} {I g s0 σ k C aw out R}
    {base : Nat} {mem : ByteArray}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨121⟩
      (UInt256.ofNat (returnArrayFree base out) :: R)
      (returnArrayDecodedMemory mem base out) aw out σ k C)
    (hstack : R.length + 10 ≤ 1024) (hlo : 96 ≤ base) (hc : ReturnArrayChecks out)
    (hcap : returnArrayEnd base out ≤ solcMaxU64) :
    RDret (immutableLayout.runtime attesterBytecode words) g s0 σ
      (wordBytes ([UInt256.ofNat 32, UInt256.ofNat (returnArrayCount out)] ++
        wordArrayWords (returnArrayWords out) 0 (returnArrayCount out))) := by
  have hb := (returnArrayFree_bounds base out).1
  have hf : returnArrayEnd base out + 64 + 32 * returnArrayCount out < UInt256.size := by
    have hn := hc.length
    change returnArrayCount out ≤ 18446744073709551615 at hn
    change returnArrayEnd base out ≤ 18446744073709551615 at hcap
    change _ < 2 ^ 256; omega
  apply wordArrayReturn (dst := returnArrayEnd base out) h hstack (by omega)
  · rw [returnArrayDecodedMemory, wordArrayMemory_size _ _ _ _ (by omega)]
    exact Nat.le_max_right _ _
  · exact le_refl _
  · exact hf
  · exact wordArrayMemory_freePtr _ _ _ _ (by omega)
  · exact wordArrayMemory_length _ _ _ _ (by omega) (by unfold returnArrayEnd at hf; omega)
  · intro j hj
    exact wordArrayMemory_data _ _ _ _ hj (by change returnArrayEnd base out < _; omega)

end Benchmarks.EAS.Attester
