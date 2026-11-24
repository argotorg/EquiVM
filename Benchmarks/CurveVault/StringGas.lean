import Benchmarks.CurveVault.Common

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: a padded read has exactly its requested length.
theorem readWithPadding_size (mem : ByteArray) (offset length : Nat) :
    (mem.readWithPadding offset length).size = length := by
  unfold ByteArray.readWithPadding
  rw [ByteArray.size_append, ByteArray_zeroes_size]
  have hread := Ethereum.EVM.ByteArray.readWithoutPadding_size_le mem offset length
  omega

-- LIBRARY CANDIDATE: oversized return data rules out the successful RDret branch.
theorem rdret_outOfGas_of_large_output {code : ByteArray} {g : Sat256} {s0 : State}
    {σ : AccountMap} {out : ByteArray}
    (hpaid : memoryPaidByGas s0) (hlarge : maxReturnDataSizeByGas < out.size)
    (h : RDret fork code g s0 σ out) :
    X fork (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass := by
  rcases h with hoog | ⟨state, hsuccess, _⟩
  · exact hoog
  · have hbound := X_success_output_size_le_maxReturnDataSizeByGas hpaid hsuccess
    omega

-- LIBRARY CANDIDATE: initial empty memory has already been paid for by any UInt256 gas budget.
theorem initState_memoryPaidByGas (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    memoryPaidByGas (initState σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hzero : (default : State).machineState.activeWords.toNat = 0 := rfl
  simp only [memoryPaidByGas, initState, Cₘ, hzero, Nat.mul_zero, Nat.zero_div,
    Nat.add_zero, Nat.zero_add, Sat256.ofUInt256_toNat]
  exact g.val.isLt

end Benchmarks.CurveVault
