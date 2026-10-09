import Benchmarks.Morpho.MorphoBlue.AuthorizationSigSignatureDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def authorizationRecoveryWords (v : MorphoImmutables) (a : AuthorizationWords)
    (cd : ByteArray) : List UInt256 :=
  [authorizationDigest v a, signatureRecoveryWord cd, calldataWord cd 196, calldataWord cd 228]

def authorizationRecoveryMem (v : MorphoImmutables) (a : AuthorizationWords)
    (cd : ByteArray) : ByteArray :=
  writeWord (writeCascade (authorizationDigestReadyMem v a)
    (returnWordWrites 768 (authorizationRecoveryWords v a cd))) 0 (UInt256.ofNat 0)

def authorizationRecoveryTail (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat 224, solcAddrMask, UInt256.ofNat 128, UInt256.ofNat 32,
    UInt256.ofNat 160, UInt256.ofNat 192, UInt256.ofNat 0] ++ R

theorem authorizationRecoveryMem_eq (v : MorphoImmutables) (a : AuthorizationWords)
    (ee : ExecutionEnv) :
    morphoBlocks.morpho_block_6372_memory (ee := ee) (mem := authorizationDigestReadyMem v a)
      (x0 := UInt256.ofNat 416) (x1 := UInt256.ofNat 768) (x2 := authorizationDigest v a)
      (x3 := UInt256.ofNat 0) (x4 := signatureRecoveryWord ee.calldata) =
      authorizationRecoveryMem v a ee.calldata := by
  simp only [morphoBlocks.morpho_block_6372_memory,
    show (UInt256.ofNat 416 + UInt256.ofNat 384).toNat = 800 by decide,
    show (UInt256.ofNat 416 + UInt256.ofNat 416).toNat = 832 by decide,
    show (UInt256.ofNat 416 + UInt256.ofNat 448).toNat = 864 by decide]
  rfl

theorem morphoAuthorizationRecoveryInput {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords) (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6372)
      (authorizationSignatureStack v a ee.calldata R) (authorizationDigestReadyMem v a) aw out σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6409)
      ([gasArg, UInt256.ofNat 1, UInt256.ofNat 768, UInt256.ofNat 128,
        UInt256.ofNat 0, UInt256.ofNat 32] ++ authorizationRecoveryTail R)
      (authorizationRecoveryMem v a ee.calldata) aw' out σ k' C' := by
  have r := morphoBlocks.morpho_block_6372 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 12 ≤ 1024; omega) h
  rw [authorizationRecoveryMem_eq v a ee] at r
  exact ⟨_, _, _, _, r⟩

theorem authorizationRecoveryMem_properties (v : MorphoImmutables) (a : AuthorizationWords)
    (cd : ByteArray) :
    (authorizationRecoveryMem v a cd).size = 896 ∧
      a.InMemory (authorizationRecoveryMem v a cd) ∧
      memLoad (UInt256.ofNat 0) (authorizationRecoveryMem v a cd) = UInt256.ofNat 0 ∧
      (authorizationRecoveryMem v a cd).readWithPadding 768 128 =
        returnWordBytes (authorizationRecoveryWords v a cd) := by
  have hp := authorizationDigestReadyMem_properties v a
  let m := writeCascade (authorizationDigestReadyMem v a)
    (returnWordWrites 768 (authorizationRecoveryWords v a cd))
  have hg : 768 - (authorizationDigestReadyMem v a).size < USize.size := by
    rw [hp.1]; exact lt_usize _ (by decide)
  have hs : m.size = 896 := by
    dsimp only [m]
    rw [writeReturnWords_size _ _ _ (by simp [authorizationRecoveryWords]) hg, hp.1]; rfl
  have hg0 : 0 - m.size < USize.size := by simpa only [Nat.zero_sub] using USize.size_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [authorizationRecoveryMem, writeWord_size _ _ _ hg0, hs]; rfl
  · exact (hp.2.1.words (by omega) _ _ (by decide)).prefix
      (memoryPrefix_sparse_writeWord m 0 288 _ (Or.inr (by decide))) le_rfl
      (by change 288 ≤ m.size; omega)
  · exact memLoad_writeWord_self_of_offset m 0 _ (UInt256.ofNat 0) hg0 rfl
  · rw [authorizationRecoveryMem, writeWord_read_preserved_len m 0 768 128 _ hg0
      (Or.inr ⟨by decide, by rw [hs]⟩) (by decide) (by decide)]
    exact readReturnWords (authorizationRecoveryWords v a cd) (authorizationDigestReadyMem v a) 768 hg

end Benchmarks.Morpho.MorphoBlue
