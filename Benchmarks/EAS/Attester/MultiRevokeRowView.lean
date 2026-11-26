import Benchmarks.EAS.Attester.NestedDecodeTrace
import Benchmarks.EAS.Attester.WordHelpers

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem multiRevokeRowView {words : String → UInt256} {I g s0 σ mem aw out k C R}
    {n i : Nat} {base secondData schemaData : UInt256}
    (h : RD fork (immutableLayout.runtime attesterBytecode words) I g s0 ⟨367⟩
      ([UInt256.ofNat i, base, UInt256.ofNat n, UInt256.ofNat n, secondData,
        UInt256.ofNat n, schemaData] ++ R) mem aw out σ k C)
    (hstack : R.length + 18 ≤ 1024) (hi : i < n) (hn : n < UInt256.size) :
    ((¬ NestedHeadChecks I.calldata secondData (rowEntry secondData i) ∨
        rowLength I.calldata secondData i = ⟨0⟩) ∧
      RDrev fork (immutableLayout.runtime attesterBytecode words) g s0) ∨
    (NestedHeadChecks I.calldata secondData (rowEntry secondData i) ∧
      rowLength I.calldata secondData i ≠ ⟨0⟩ ∧ ∃ aw' k' C',
      RD fork (immutableLayout.runtime attesterBytecode words) I g s0 ⟨479⟩
        ([rowLength I.calldata secondData i, rowLength I.calldata secondData i,
          rowData I.calldata secondData i, UInt256.ofNat i, base, UInt256.ofNat n,
          UInt256.ofNat n, secondData, UInt256.ofNat n, schemaData] ++ R)
        mem aw' out σ k' C') := by
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat n) = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' _ (by omega), ulit_toNat' _ hn]; exact hi)
  have h' := attesterRuntime_block_367_fallthrough
    (R := UInt256.ofNat n :: secondData :: UInt256.ofNat n :: schemaData :: R)
    (by simp only [List.length_cons]; omega) (by rw [hlt]; rfl) h
  have h'' := attesterRuntime_block_376_taken
    (R := UInt256.ofNat n :: schemaData :: R)
    (by simp only [List.length_cons]; omega) (by rw [hlt]; decide)
    h'
  have h''' := attesterRuntime_block_396
    (by simp only [List.length_cons]; omega)
    h''
  rcases attesterNestedView h''' (by simp only [List.length_cons]; omega)
      (by exact attesterJumpdest _ rfl rfl) with ⟨hbad, hrev⟩ | ⟨hgood, k', C', hv⟩
  · exact .inl ⟨.inl hbad, hrev⟩
  by_cases hz : rowLength I.calldata secondData i = ⟨0⟩
  · have hr := attesterRuntime_block_414_fallthrough
      (x0 := rowLength I.calldata secondData i)
      (by simp only [List.length_cons]; omega) (by rw [hz]; rfl) hv
    exact .inl ⟨.inr hz, attesterRuntime_block_430
      (by simp only [attesterRuntime_block_414_fallthrough_stack, List.length_cons]; omega) hr⟩
  have hr := attesterRuntime_block_414_taken (x0 := rowLength I.calldata secondData i)
    (by simp only [List.length_cons]; omega) (u256_zero_sub_ne_zero hz)
    hv
  exact .inr ⟨hgood, hz, _, _, _, hr⟩

end Benchmarks.EAS.Attester
