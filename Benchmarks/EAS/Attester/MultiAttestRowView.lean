import Benchmarks.EAS.Attester.NestedDecodeTrace
import Benchmarks.EAS.Attester.WordHelpers

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem multiAttestRowView {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {n i : Nat} {base secondData schemaData : UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1109⟩
      ([UInt256.ofNat i, base, UInt256.ofNat n, ⟨96⟩, UInt256.ofNat n, secondData,
        UInt256.ofNat n, schemaData] ++ R) mem aw out σ k C)
    (hstack : R.length + 19 ≤ 1024) (hi : i < n) (hn : n < UInt256.size) :
    ((¬ NestedHeadChecks I.calldata secondData (rowEntry secondData i) ∨
        rowLength I.calldata secondData i = ⟨0⟩) ∧
      RDrev (immutableLayout.runtime attesterBytecode words) g s0) ∨
    (NestedHeadChecks I.calldata secondData (rowEntry secondData i) ∧
      rowLength I.calldata secondData i ≠ ⟨0⟩ ∧ ∃ aw' k' C',
      RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1221⟩
        ([rowLength I.calldata secondData i, rowLength I.calldata secondData i,
          rowData I.calldata secondData i, UInt256.ofNat i, base, UInt256.ofNat n, ⟨96⟩,
          UInt256.ofNat n, secondData, UInt256.ofNat n, schemaData] ++ R)
        mem aw' out σ k' C') := by
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat n) = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' _ (by omega), ulit_toNat' _ hn]; exact hi)
  have h' := attesterRuntime_block_1109_fallthrough
    (R := ⟨96⟩ :: UInt256.ofNat n :: secondData :: UInt256.ofNat n :: schemaData :: R)
    (by simp only [List.length_cons]; omega) (by rw [hlt]; rfl) h
  have h'' := attesterRuntime_block_1118_taken
    (R := UInt256.ofNat n :: schemaData :: R)
    (by simp only [List.length_cons]; omega) (by rw [hlt]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h'
  have h''' := attesterRuntime_block_1138
    (by simp only [List.length_cons]; omega)
    (by rw [attesterRuntime_validJumps]; native_decide) h''
  rcases attesterNestedView h''' (by simp only [List.length_cons]; omega)
      (by rw [attesterRuntime_validJumps]; native_decide) with ⟨hbad, hrev⟩ | ⟨hgood, k', C', hv⟩
  · exact .inl ⟨.inl hbad, hrev⟩
  by_cases hz : rowLength I.calldata secondData i = ⟨0⟩
  · have hr := attesterRuntime_block_1156_fallthrough
      (x0 := rowLength I.calldata secondData i)
      (by simp only [List.length_cons]; omega) (by rw [hz]; rfl) hv
    exact .inl ⟨.inr hz, attesterRuntime_block_1172
      (by simp only [attesterRuntime_block_1156_fallthrough_stack, List.length_cons]; omega) hr⟩
  have hr := attesterRuntime_block_1156_taken (x0 := rowLength I.calldata secondData i)
    (by simp only [List.length_cons]; omega) (u256_zero_sub_ne_zero hz)
    (by rw [attesterRuntime_validJumps]; native_decide) hv
  exact .inr ⟨hgood, hz, _, _, _, hr⟩

end Benchmarks.EAS.Attester
