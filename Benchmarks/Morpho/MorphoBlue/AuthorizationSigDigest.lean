import Benchmarks.Morpho.MorphoBlue.AuthorizationSigStruct
import Benchmarks.Morpho.MorphoBlue.WordPrefixMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def authorizationDigestPrefix : UInt256 :=
  UInt256.ofNat 11309588061646438093662687302255421419811724423900836950936401294474059186176

def authorizationDigestPayloadMem (v : MorphoImmutables) (a : AuthorizationWords) : ByteArray :=
  writeCascade (writeWord (authorizationStructReadyMem a) 672 authorizationDigestPrefix)
    (returnWordWrites 674 [v.DOMAIN_SEPARATOR, a.structHash])

def authorizationDigestMem (v : MorphoImmutables) (a : AuthorizationWords) : ByteArray :=
  writeWord (authorizationDigestPayloadMem v a) 640 (UInt256.ofNat 66)

def authorizationDigestStack (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat 672, UInt256.ofNat 768, UInt256.ofNat 640, UInt256.ofNat 416,
    UInt256.ofNat 224, solcAddrMask, UInt256.ofNat 128, UInt256.ofNat 32,
    UInt256.ofNat 160, UInt256.ofNat 192, UInt256.ofNat 0] ++ R

theorem authorizationDigestMem_eq (v : MorphoImmutables) (a : AuthorizationWords) :
    morphoBlocks.morpho_block_6234_fallthrough_memory
      (immWords := wordsOf (immStore v)) (mem := authorizationStructMem a)
      (x0 := UInt256.ofNat 448) (x1 := UInt256.ofNat 256)
      (x3 := UInt256.ofNat 640) (x4 := UInt256.ofNat 416) = authorizationDigestMem v a := by
  have hp := authorizationStructReadyMem_properties a
  have hl : memLoad (UInt256.ofNat 416)
      ((UInt256.ofNat 640).toByteArray.write 0 (authorizationStructMem a) 64 32) =
      UInt256.ofNat 192 := hp.2.2.1
  have hk : keccakWord (UInt256.ofNat 448) (UInt256.ofNat 192)
      ((UInt256.ofNat 640).toByteArray.write 0 (authorizationStructMem a) 64 32) =
      a.structHash := hp.2.2.2
  simp only [morphoBlocks.morpho_block_6234_fallthrough_memory,
    show (UInt256.ofNat 64).toNat = 64 from rfl]
  rw [hl, hk]
  rw [show (UInt256.ofNat 416 + UInt256.ofNat 256).toNat = 672 by decide,
    show (UInt256.ofNat 416 + UInt256.ofNat 258).toNat = 674 by decide,
    show (UInt256.ofNat 416 + UInt256.ofNat 290).toNat = 706 by decide]
  rw [wordsOf_immStore_DOMAIN_SEPARATOR]
  rfl

theorem morphoAuthorizationDigest {v : MorphoImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords) (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6234)
      (authorizationStructStack R) (authorizationStructMem a) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6347)
      (authorizationDigestStack R) (authorizationDigestMem v a) aw' out σ k' C' := by
  have r := morphoBlocks.morpho_block_6234_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 7 + 8 ≤ 1024; omega) (by decide) h
  dsimp only [morphoBlocks.morpho_block_6234_fallthrough_stack] at r
  rw [authorizationDigestMem_eq v a,
    show UInt256.ofNat 416 + UInt256.ofNat 256 = UInt256.ofNat 672 by decide,
    show UInt256.ofNat 416 + UInt256.ofNat 352 = UInt256.ofNat 768 by decide] at r
  exact ⟨_, _, _, r⟩


theorem authorizationDigestPayloadMem_properties (v : MorphoImmutables) (a : AuthorizationWords) :
    (authorizationDigestPayloadMem v a).size = 738 ∧
      a.InMemory (authorizationDigestPayloadMem v a) ∧
      (authorizationDigestPayloadMem v a).readWithPadding 672 66 = authorizationDigestBytes v a := by
  have hp := authorizationStructReadyMem_properties a
  have hg : 672 - (authorizationStructReadyMem a).size < USize.size := by
    rw [hp.1]; exact lt_usize _ (by decide)
  have hs : (writeWord (authorizationStructReadyMem a) 672 authorizationDigestPrefix).size = 704 := by
    rw [writeWord_size _ _ _ hg, hp.1]; rfl
  have hg1 : 674 - (writeWord (authorizationStructReadyMem a) 672 authorizationDigestPrefix).size <
      USize.size := by rw [hs]; exact USize.size_pos
  refine ⟨?_, ?_, ?_⟩
  · rw [authorizationDigestPayloadMem, writeReturnWords_size _ _ _ (by simp) hg1, hs]; rfl
  · exact (hp.2.1.prefix
      (memoryPrefix_sparse_writeWord _ 672 288 _ (Or.inl (by decide))) le_rfl (by omega)).words
        (by rw [hs]; decide) _ 674 (by decide)
  · have hr := wordPrefixMem_read authorizationDigestPrefix [v.DOMAIN_SEPARATOR, a.structHash]
      (authorizationStructReadyMem a) 672 2 (by simp) (by decide) (by decide) hg
    have hb : authorizationDigestPrefix.toByteArray.extract 0 2 = (⟨#[25, 1]⟩ : ByteArray) :=
      by native_decide
    simpa only [hb, returnWordBytes, ByteArray.append_empty, ByteArray.append_assoc,
      authorizationDigestBytes] using hr

theorem authorizationDigestMem_properties (v : MorphoImmutables) (a : AuthorizationWords) :
    (authorizationDigestMem v a).size = 738 ∧
      a.InMemory (authorizationDigestMem v a) ∧
      memLoad (UInt256.ofNat 640) (authorizationDigestMem v a) = UInt256.ofNat 66 ∧
      (authorizationDigestMem v a).readWithPadding 672 66 = authorizationDigestBytes v a := by
  have hp := authorizationDigestPayloadMem_properties v a
  have hg : 640 - (authorizationDigestPayloadMem v a).size < USize.size := by
    rw [hp.1]; exact USize.size_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [authorizationDigestMem, writeWord_size _ _ _ hg, hp.1]; rfl
  · exact hp.2.1.prefix
      (memoryPrefix_sparse_writeWord _ 640 288 _ (Or.inl (by decide))) le_rfl (by omega)
  · exact memLoad_writeWord_self_of_offset _ 640 _ (UInt256.ofNat 640) hg rfl
  · rw [authorizationDigestMem, writeWord_read_preserved_len _ 640 672 66 _ hg
      (Or.inr ⟨by decide, by rw [hp.1]⟩) (by decide) (by decide), hp.2.2]

def authorizationDigestReadyMem (v : MorphoImmutables) (a : AuthorizationWords) : ByteArray :=
  writeWord (authorizationDigestMem v a) 64 (UInt256.ofNat 768)

theorem authorizationDigestReadyMem_properties (v : MorphoImmutables) (a : AuthorizationWords) :
    (authorizationDigestReadyMem v a).size = 738 ∧
      a.InMemory (authorizationDigestReadyMem v a) ∧
      memLoad (UInt256.ofNat 640) (authorizationDigestReadyMem v a) = UInt256.ofNat 66 ∧
      keccakWord (UInt256.ofNat 672) (UInt256.ofNat 66) (authorizationDigestReadyMem v a) =
        authorizationDigest v a := by
  have hp := authorizationDigestMem_properties v a
  have hg : 64 - (authorizationDigestMem v a).size < USize.size := by
    rw [hp.1]; exact USize.size_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [authorizationDigestReadyMem, writeWord_size _ _ _ hg, hp.1]; rfl
  · exact hp.2.1.prefix
      (memoryPrefix_sparse_writeWord _ 64 288 _ (Or.inr (by decide))) le_rfl (by omega)
  · rw [authorizationDigestReadyMem, memLoad_writeWord_disjoint _ _ _ _ hg
      (by rw [hp.1]; decide) (Or.inr (by decide)), hp.2.2.1]
  · change UInt256.ofNat (fromByteArrayBigEndian (KEC
      ((writeWord (authorizationDigestMem v a) 64 (UInt256.ofNat 768)).readWithPadding 672 66))) = _
    rw [writeWord_read_preserved_len _ 64 672 66 _ hg
      (Or.inr ⟨by decide, by rw [hp.1]⟩) (by decide) (by decide), hp.2.2.2]
    exact (uInt256OfByteArray_eq _).symm

end Benchmarks.Morpho.MorphoBlue
