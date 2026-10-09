import Benchmarks.Morpho.MorphoBlue.ConstructorSource
import Benchmarks.Morpho.MorphoBlue.MarketParamsMemory
import Benchmarks.Morpho.MorphoBlue.ErrorMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: a word patch in the right component commutes with a memory prefix.
theorem writeWord_append_right (pref suffix : ByteArray) (off : Nat) (w : UInt256)
    (hoff : off ≤ suffix.size) :
    writeWord (pref ++ suffix) (pref.size + off) w = pref ++ writeWord suffix off w := by
  rw [Reasoning.Theory.writeWord, write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [ByteArray.size_append]; omega),
    Reasoning.Theory.writeWord, write32_eq _ _ _ (by rw [toByteArray_size]) hoff,
    extract_append_span _ _ _ _ (by omega) (by omega), byteArray_extract_self,
    extract_append_right_window _ _ _ _ (by omega), ByteArray.size_append]
  simp only [Nat.add_sub_cancel_left, Nat.add_assoc, ByteArray.append_assoc]

def constructorFreeMem : ByteArray := writeWord ByteArray.empty 64 (UInt256.ofNat 192)
def constructorDecodedMem (w : UInt256) : ByteArray := writeWord constructorFreeMem 160 w

theorem constructorDecodedMemory (w : UInt256) :
    (constructorDecodedMem w).size = 192 ∧
    memLoad (UInt256.ofNat 64) (constructorDecodedMem w) = UInt256.ofNat 192 ∧
    memLoad (UInt256.ofNat 160) (constructorDecodedMem w) = w := by
  have hs : constructorFreeMem.size = 96 := by native_decide
  have hg : 160 - constructorFreeMem.size < USize.size := by rw [hs]; exact lt_usize _ (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [constructorDecodedMem, writeWord_size _ _ _ hg, hs]; rfl
  · rw [constructorDecodedMem, memLoad_writeWord_disjoint _ _ _ _ hg (by rw [hs]; decide) (by left; decide)]
    native_decide
  · exact memLoad_writeWord_self _ w (UInt256.ofNat 160) hg

theorem constructorCodeSize (w : UInt256) :
    (morphoCreationBytecode ++ w.toByteArray).size = 16087 := by
  rw [ByteArray.size_append, toByteArray_size]
  native_decide

theorem constructorArgumentCopy (w : UInt256) :
    (morphoCreationBytecode ++ w.toByteArray).write 16055 constructorFreeMem 160 32 = constructorDecodedMem w := by
  have hs : constructorFreeMem.size = 96 := by native_decide
  have hc : morphoCreationBytecode.size = 16055 := by native_decide
  rw [write_from_gap_eq _ _ _ _ _ (by decide) (by rw [constructorCodeSize])
    (by rw [hs]; decide) (by rw [hs]; exact lt_usize _ (by decide))]
  rw [extract_append_right' _ _ _ _ hc.symm (by rw [hc, toByteArray_size])]
  exact (toByteArray_write_eq w constructorFreeMem 160 (by rw [hs]; decide)
    (by rw [hs]; exact lt_usize _ (by decide))).symm

def constructorOwnerMessage : UInt256 := UInt256.shiftLeft (UInt256.ofNat 37879813105686071716916589427) (UInt256.ofNat 160)
def constructorOwnerMem (w : UInt256) : ByteArray := morphoErrorMem (UInt256.ofNat 12) constructorOwnerMessage (constructorDecodedMem w)

theorem constructorOwnerMemory (w : UInt256) :
    (constructorOwnerMem w).size = 256 ∧
    memLoad (UInt256.ofNat 64) (constructorOwnerMem w) = UInt256.ofNat 256 ∧
    morphoErrorLength (constructorOwnerMem w) (UInt256.ofNat 192) = UInt256.ofNat 12 := by
  have hd := constructorDecodedMemory w
  exact morphoErrorMem_properties _ _ _ _ hd.1 hd.2.1 (by decide) (by decide)

def constructorDomainMem (w : UInt256) (I : ExecutionEnv) : ByteArray :=
  writeWord (writeCascade (constructorOwnerMem w) (returnWordWrites 288 (morphoDomainWords I))) 256 (UInt256.ofNat 96)

theorem constructorDomainMemory (w : UInt256) (I : ExecutionEnv) :
    (constructorDomainMem w I).size = 384 ∧
    memLoad (UInt256.ofNat 64) (constructorDomainMem w I) = UInt256.ofNat 256 ∧
    memLoad (UInt256.ofNat 256) (constructorDomainMem w I) = UInt256.ofNat 96 ∧
    keccakWord (UInt256.ofNat 288) (UInt256.ofNat 96) (constructorDomainMem w I) = morphoDomainSeparator I := by
  let mem := writeCascade (constructorOwnerMem w) (returnWordWrites 288 (morphoDomainWords I))
  have hb := constructorOwnerMemory w
  have hs : mem.size = 384 := by
    dsimp only [mem]
    rw [writeCascade_size]
    · simp only [morphoDomainWords, returnWordWrites, writeCascadeSize, hb.1]; rfl
    · simp only [morphoDomainWords, returnWordWrites, WriteGapsOk, hb.1]
      exact ⟨lt_usize _ (by decide), lt_usize _ (by decide), lt_usize _ (by decide), True.intro⟩
  have hg : 256 - mem.size < USize.size := by rw [hs]; exact lt_usize _ (by decide)
  have hr : mem.readWithPadding 288 96 = returnWordBytes (morphoDomainWords I) :=
    readReturnWords_after_gap _ _ _ 288 (by rw [hb.1]; decide) (by rw [hb.1]; exact lt_usize _ (by decide))
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (writeWord mem 256 _).size = _
    rw [writeWord_size _ _ _ hg, hs]; rfl
  · change memLoad (UInt256.ofNat 64) (writeWord mem 256 _) = _
    rw [memLoad_writeWord_disjoint _ _ _ _ hg (by rw [hs]; decide) (by left; decide)]
    have hp : mem.readWithPadding 64 32 = (constructorOwnerMem w).readWithPadding 64 32 := by
      apply writeCascade_read_preserved
      simp only [morphoDomainWords, returnWordWrites, WindowDisjointFromWrites, hb.1]
      have hz : 32 < USize.size := lt_usize _ (by decide)
      norm_num; omega
    have heq : memLoad (UInt256.ofNat 64) mem = memLoad (UInt256.ofNat 64) (constructorOwnerMem w) := by
      simp only [memLoad, show (UInt256.ofNat 64).toNat = 64 from rfl, hs, hb.1, hp]
      rfl
    exact heq.trans hb.2.1
  · exact memLoad_writeWord_self mem _ (UInt256.ofNat 256) hg
  · change UInt256.ofNat (fromByteArrayBigEndian (KEC ((writeWord mem 256 _).readWithPadding 288 96))) = _
    rw [writeWord_read_preserved_len_of_disjoint hg (by right; rw [hs]; decide) (by decide) (by decide), hr,
      keccakSlot_eq]
    rfl

end Benchmarks.Morpho.MorphoBlue
