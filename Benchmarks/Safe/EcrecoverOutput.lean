import Benchmarks.Safe.RawStaticCall
import Benchmarks.Safe.Memory
import Reasoning.WordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: ECRECOVER either has no result or returns a canonical address word.
def EcrecoverOutput (out : ByteArray) : Prop :=
  out = ByteArray.empty ∨ (out.size = 32 ∧ (calldataWord out 0).toNat < EVM.addressModulus)

theorem ecrecoverHashOutput (bytes : ByteArray) :
    EcrecoverOutput (ByteArray.zeroes 12 ++ (KEC bytes).extract 12 32) := by
  have ht : ((KEC bytes).extract 12 32).size = 20 := by
    rw [ByteArray.size_extract, keccak_size]
    rfl
  have hs : (ByteArray.zeroes 12 ++ (KEC bytes).extract 12 32).size = 32 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size, ht]
  refine Or.inr ⟨hs, ?_⟩
  have hw := calldataWord_bytes (out := ByteArray.zeroes 12 ++ (KEC bytes).extract 12 32)
    (by omega)
  have he : (ByteArray.zeroes 12 ++ (KEC bytes).extract 12 32).extract 0 32 =
      ByteArray.zeroes 12 ++ (KEC bytes).extract 12 32 := by
    conv_lhs => arg 3; rw [← hs]
    exact byteArray_extract_self _
  rw [he] at hw
  rw [← fromByteArrayBigEndian_toByteArray, hw, fromByteArrayBigEndian_append,
    show fromByteArrayBigEndian (ByteArray.zeroes 12) = 0 from by decide +kernel,
    Nat.zero_mul, Nat.zero_add]
  have hb := fromByteArrayBigEndian_lt ((KEC bytes).extract 12 32)
  simpa only [ht] using hb

theorem precompileEcrecoverOutput (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) : EcrecoverOutput (Ξ_ECREC σ g A I).2.2.2 := by
  unfold Ξ_ECREC
  dsimp only
  split
  · exact Or.inl rfl
  · dsimp only
    split
    · exact Or.inl rfl
    · split
      · exact ecrecoverHashOutput _
      · exact Or.inl rfl

theorem thetaEcrecoverOutput (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : Fin 1025)
    (H : BlockHeader) (blob : List ByteArray) (blocks : ProcessedBlocks) (w : Bool) :
    EcrecoverOutput (Θ σ σ₀ A s o r (.Precompiled 1) g p v v' d e H blob blocks w).2.2.2.2 := by
  unfold Θ
  dsimp only
  exact precompileEcrecoverOutput _ _ _ _

theorem callEcrecoverOutput {evm evm' : EVM.State} {d out : ByteArray} {z perm : Bool}
    (hc : callViaEVM evm (AccountAddress.ofNat 1) 0 d (z, evm', out) perm) :
    EcrecoverOutput out := by
  cases hc with
  | callNotMade => exact Or.inl rfl
  | callMade hvalue hcall hevm hbal hdepth =>
      obtain ⟨gas, A, hΘ⟩ := hcall
      have hto : toExecute evm.accountMap (AccountAddress.ofNat 1) = .Precompiled 1 := rfl
      rw [hto, hvalue] at hΘ
      have hs := thetaEcrecoverOutput evm.accountMap evm.σ₀ A evm.executionEnv.codeOwner
        evm.executionEnv.sender (AccountAddress.ofNat 1) gas (.ofNat evm.executionEnv.gasPrice)
        (EVM.wordOfInt 0) (EVM.wordOfInt 0) d (evm.executionEnv.depth + 1) evm.executionEnv.header
        evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks (perm && evm.executionEnv.perm)
      rw [← hΘ] at hs
      exact hs

end Benchmarks.Safe
