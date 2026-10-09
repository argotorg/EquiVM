import Benchmarks.Morpho.MorphoBlue.AuthorizationSigRecoveryCall
import Benchmarks.Morpho.MorphoBlue.WordCallOutputMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def authorizationRecoveredMem (v : MorphoImmutables) (a : AuthorizationWords)
    (cd out : ByteArray) : ByteArray :=
  callOutputMem (authorizationRecoveryMem v a cd) out (UInt256.ofNat 0) (UInt256.ofNat 32)

theorem authorizationRecoveryMem_free (v : MorphoImmutables) (a : AuthorizationWords) (cd : ByteArray) :
    memLoad (UInt256.ofNat 64) (authorizationRecoveryMem v a cd) = UInt256.ofNat 768 := by
  have hp := authorizationDigestReadyMem_properties v a
  let m := writeCascade (authorizationDigestReadyMem v a)
    (returnWordWrites 768 (authorizationRecoveryWords v a cd))
  have hg : 768 - (authorizationDigestReadyMem v a).size < USize.size := by
    rw [hp.1]; exact lt_usize _ (by decide)
  have hs : m.size = 896 := by
    dsimp only [m]
    rw [writeReturnWords_size _ _ _ (by simp [authorizationRecoveryWords]) hg, hp.1]; rfl
  have hg0 : 0 - m.size < USize.size := by simpa only [Nat.zero_sub] using USize.size_pos
  rw [authorizationRecoveryMem, memLoad_writeWord_disjoint m 0 _ _ hg0
    (by rw [hs]; decide) (Or.inr (by decide)), memLoad_writeReturnWords_below _ _ _ _ hg
    (by rw [hp.1]; decide) (by decide)]
  have hp0 := authorizationDigestMem_properties v a
  exact memLoad_writeWord_self_of_offset _ 64 _ (UInt256.ofNat 64)
    (by rw [hp0.1]; exact USize.size_pos) rfl

theorem authorizationRecoveredMem_properties (v : MorphoImmutables) (a : AuthorizationWords)
    (cd out : ByteArray) (ho : EcrecoverOutput out) :
    (authorizationRecoveredMem v a cd out).size = 896 ∧
      a.InMemory (authorizationRecoveredMem v a cd out) ∧
      memLoad (UInt256.ofNat 0) (authorizationRecoveredMem v a cd out) = ecrecoverWord out ∧
      memLoad (UInt256.ofNat 64) (authorizationRecoveredMem v a cd out) = UInt256.ofNat 768 := by
  have hp := authorizationRecoveryMem_properties v a cd
  have hf := authorizationRecoveryMem_free v a cd
  rcases ho.size with hz | h32
  · have he := byteArray_eq_empty_of_size_eq_zero out hz
    rw [authorizationRecoveredMem, he, callOutput32_empty]
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hf⟩
  · rw [authorizationRecoveredMem, callOutput32_word _ _ _ h32, show (UInt256.ofNat 0).toNat = 0 from rfl]
    have hg : 0 - (authorizationRecoveryMem v a cd).size < USize.size :=
      by simpa only [Nat.zero_sub] using USize.size_pos
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [writeWord_size _ _ _ hg, hp.1]; rfl
    · exact hp.2.1.prefix (memoryPrefix_sparse_writeWord _ 0 288 _ (Or.inr (by decide))) le_rfl (by omega)
    · simp only [ecrecoverWord, h32, show (32 : Nat) ≠ 0 by decide, ↓reduceIte]
      exact memLoad_writeWord_self_of_offset _ 0 _ (UInt256.ofNat 0) hg rfl
    · rw [memLoad_writeWord_disjoint _ 0 _ _ hg (by rw [hp.1]; decide)
        (Or.inr (by decide)), hf]

end Benchmarks.Morpho.MorphoBlue
