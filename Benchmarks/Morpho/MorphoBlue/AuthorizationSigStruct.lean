import Benchmarks.Morpho.MorphoBlue.AuthorizationSigHashSource
import Benchmarks.Morpho.MorphoBlue.SafeTransferCallMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem AuthorizationWords.InMemory.words {a : AuthorizationWords} {mem : ByteArray}
    (ha : a.InMemory mem) (hs : 288 ≤ mem.size) (ws : List UInt256) (off : Nat)
    (ho : 288 ≤ off) : a.InMemory (writeCascade mem (returnWordWrites off ws)) :=
  ha.prefix (writeReturnWords_prefix ws mem off 288 ho) le_rfl hs

def authorizationStructMem (a : AuthorizationWords) : ByteArray :=
  writeWord (writeCascade (authorizationCheckedMem a) (returnWordWrites 448 a.structWords))
    416 (UInt256.ofNat 192)

def authorizationStructStack (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat 448, UInt256.ofNat 256, UInt256.ofNat 18446744073709551615,
    UInt256.ofNat 640, UInt256.ofNat 416, UInt256.ofNat 224, solcAddrMask,
    UInt256.ofNat 128, UInt256.ofNat 32, UInt256.ofNat 160, UInt256.ofNat 192, UInt256.ofNat 0] ++ R

theorem authorizationStructMem_eq (a : AuthorizationWords) (hc : a.Canonical) :
    morphoBlocks.morpho_block_6120_fallthrough_memory
      (mem := authorizationCheckedMem a) (x1 := UInt256.ofNat 256)
      (x2 := UInt256.ofNat 224) (x3 := solcAddrMask) (x4 := UInt256.ofNat 128)
      (x5 := UInt256.ofNat 32) (x6 := UInt256.ofNat 160) (x7 := UInt256.ofNat 192) =
      authorizationStructMem a := by
  have hp := authorizationCheckedMem_properties a
  have h1 := (hp.2.2.1.words (by omega) [authorizationTypeHash] 448 (by decide)) ⟨0, by decide⟩
  have h2 := (hp.2.2.1.words (by omega) [authorizationTypeHash, a.authorizer]
    448 (by decide)) ⟨1, by decide⟩
  have h3 := (hp.2.2.1.words (by omega) [authorizationTypeHash, a.authorizer, a.authorized]
    448 (by decide)) ⟨2, by decide⟩
  have h4 := (hp.2.2.1.words (by omega)
    [authorizationTypeHash, a.authorizer, a.authorized, a.enabled] 448 (by decide)) ⟨3, by decide⟩
  have h5 := (hp.2.2.1.words (by omega)
    [authorizationTypeHash, a.authorizer, a.authorized, a.enabled, a.nonce]
    448 (by decide)) ⟨4, by decide⟩
  dsimp only [returnWordWrites, writeCascade_cons, writeCascade_nil,
    AuthorizationWords.toList, Reasoning.Theory.writeWord, authorizationTypeHash] at h1 h2 h3 h4 h5
  simp at h1 h2 h3 h4 h5
  have he : UInt256.isZero (UInt256.isZero a.enabled) = a.enabled := (boolWordClean_iff _).mpr hc.2.2
  have hma := solcAddrMask_clean hc.1
  have hmb := solcAddrMask_clean hc.2.1
  simp only [morphoBlocks.morpho_block_6120_fallthrough_memory, hp.2.1]
  simp only [show (UInt256.ofNat 416 + UInt256.ofNat 32).toNat = 448 by decide,
    show (UInt256.ofNat 416 + UInt256.ofNat 64).toNat = 480 by decide,
    show (UInt256.ofNat 416 + UInt256.ofNat 96).toNat = 512 by decide,
    show (UInt256.ofNat 416 + UInt256.ofNat 128).toNat = 544 by decide,
    show (UInt256.ofNat 416 + UInt256.ofNat 160).toNat = 576 by decide,
    show (UInt256.ofNat 416 + UInt256.ofNat 192).toNat = 608 by decide]
  rw [h1, hma, h2, hmb, h3, he, h4, h5]
  rfl


theorem morphoAuthorizationStruct {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords) (hc : a.Canonical)
    (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6120)
      (authorizationHashTail R) (authorizationCheckedMem a) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6234)
      (authorizationStructStack R) (authorizationStructMem a) aw' out σ k' C' := by
  have hf := (authorizationCheckedMem_properties a).2.1
  have r := morphoBlocks.morpho_block_6120_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 14 ≤ 1024; omega) (by rw [hf]; decide) h
  dsimp only [morphoBlocks.morpho_block_6120_fallthrough_stack] at r
  rw [hf, authorizationStructMem_eq a hc] at r
  rw [show UInt256.ofNat 416 + UInt256.ofNat 32 = UInt256.ofNat 448 by decide,
    show UInt256.ofNat 416 + UInt256.ofNat 224 = UInt256.ofNat 640 by decide] at r
  exact ⟨_, _, _, r⟩


theorem authorizationStructMem_properties (a : AuthorizationWords) :
    (authorizationStructMem a).size = 640 ∧
      a.InMemory (authorizationStructMem a) ∧
      memLoad (UInt256.ofNat 416) (authorizationStructMem a) = UInt256.ofNat 192 ∧
      (authorizationStructMem a).readWithPadding 448 192 = returnWordBytes a.structWords := by
  have hp := authorizationCheckedMem_properties a
  let m := writeCascade (authorizationCheckedMem a) (returnWordWrites 448 a.structWords)
  have hg : 448 - (authorizationCheckedMem a).size < USize.size := by
    rw [hp.1]; exact lt_usize _ (by decide)
  have hs : m.size = 640 := by
    dsimp only [m]
    rw [writeReturnWords_size _ _ _ (by simp [AuthorizationWords.structWords]) hg, hp.1]
    rfl
  have hgm : 416 - m.size < USize.size := by rw [hs]; exact USize.size_pos
  have hsize : (authorizationStructMem a).size = 640 := by
    rw [authorizationStructMem, writeWord_size _ _ _ hgm, hs]; rfl
  refine ⟨hsize, ?_, ?_, ?_⟩
  · exact (hp.2.2.1.words (by omega) _ _ (by decide)).prefix
      (memoryPrefix_sparse_writeWord m 416 288 _ (Or.inl (by decide))) le_rfl (by change 288 ≤ m.size; omega)
  · exact memLoad_writeWord_self_of_offset m 416 _ (UInt256.ofNat 416) hgm rfl
  · rw [authorizationStructMem, writeWord_read_preserved_len m 416 448 192 _ hgm
      (Or.inr ⟨by decide, by rw [hs]⟩) (by decide) (by decide)]
    exact readReturnWords a.structWords (authorizationCheckedMem a) 448 hg

def authorizationStructReadyMem (a : AuthorizationWords) : ByteArray :=
  writeWord (authorizationStructMem a) 64 (UInt256.ofNat 640)

theorem authorizationStructReadyMem_properties (a : AuthorizationWords) :
    (authorizationStructReadyMem a).size = 640 ∧
      a.InMemory (authorizationStructReadyMem a) ∧
      memLoad (UInt256.ofNat 416) (authorizationStructReadyMem a) = UInt256.ofNat 192 ∧
      keccakWord (UInt256.ofNat 448) (UInt256.ofNat 192) (authorizationStructReadyMem a) =
        a.structHash := by
  have hp := authorizationStructMem_properties a
  have hg : 64 - (authorizationStructMem a).size < USize.size := by
    rw [hp.1]; exact USize.size_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [authorizationStructReadyMem, writeWord_size _ _ _ hg, hp.1]; rfl
  · exact hp.2.1.prefix
      (memoryPrefix_sparse_writeWord _ 64 288 _ (Or.inr (by decide))) le_rfl (by omega)
  · rw [authorizationStructReadyMem, memLoad_writeWord_disjoint _ _ _ _ hg
      (by rw [hp.1]; decide) (Or.inr (by decide)), hp.2.2.1]
  · change UInt256.ofNat (fromByteArrayBigEndian (KEC ((writeWord (authorizationStructMem a) 64 (UInt256.ofNat 640)).readWithPadding
      448 192))) = a.structHash
    rw [writeWord_read_preserved_len _ 64 448 192 _ hg
      (Or.inr ⟨by decide, by rw [hp.1]⟩) (by decide) (by decide), hp.2.2.2]
    exact (uInt256OfByteArray_eq _).symm

end Benchmarks.Morpho.MorphoBlue
