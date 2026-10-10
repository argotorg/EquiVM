import Benchmarks.Morpho.MetaMorphoV1_1.Eip712ReturnMemory
import Benchmarks.Morpho.MetaMorphoV1_1.StringEncoderRoutines

/-! The two encoded strings and the first three words of the domain return header. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000
set_option autoImplicit false

def eip712StartMemory (mem : ByteArray) (out : Nat) : ByteArray :=
  writeWord (writeWord mem out eip712FieldsWord) (out + 32) ⟨224⟩

def eip712NameMemory (mem : ByteArray) (namePtr out : Nat) (name : ByteArray) : ByteArray :=
  writeWord (stringPayloadMemory (eip712StartMemory mem out) (namePtr + 32) (out + 224)
    (UInt256.ofNat name.size)) (out + 64) (UInt256.ofNat (256 + paddedSize name.size))

def eip712VersionMemory (mem : ByteArray) (namePtr versionPtr out : Nat)
    (name version : ByteArray) : ByteArray :=
  stringPayloadMemory (eip712NameMemory mem namePtr out name) (versionPtr + 32)
    (out + 256 + paddedSize name.size) (UInt256.ofNat version.size)

theorem eip712StartMemory_size (mem : ByteArray) (out : Nat) :
    (eip712StartMemory mem out).size = max mem.size (out + 64) := by
  simp only [eip712StartMemory, writeWord_sparse_size]
  omega

theorem eip712StartMemory_prefix (mem : ByteArray) (out : Nat) :
    MemoryPrefix mem (eip712StartMemory mem out) out :=
  wordSequenceMemory_prefix mem out [eip712FieldsWord, ⟨224⟩]

theorem eip712StartMemory_buffer {mem bytes : ByteArray} {ptr out : Nat}
    (buffer : StringBuffer mem ptr bytes) (hlo : 96 ≤ ptr) (hptr : ptr < UInt256.size)
    (hbelow : ptr + 32 + paddedSize bytes.size ≤ out) :
    StringBuffer (eip712StartMemory mem out) ptr bytes :=
  buffer.preserve (eip712StartMemory_prefix mem out) hlo hptr hbelow

theorem eip712NameMemory_facts (mem name : ByteArray) (namePtr out : Nat)
    (hout : 96 ≤ out) (hname : name.size < UInt256.size)
    (buffer : StringBuffer (eip712StartMemory mem out) namePtr name)
    (hbelow : namePtr + 32 + paddedSize name.size ≤ out) :
    MemoryPrefix (eip712StartMemory mem out) (eip712NameMemory mem namePtr out name) out ∧
    out + 256 + paddedSize name.size ≤ (eip712NameMemory mem namePtr out name).size ∧
    (eip712NameMemory mem namePtr out name).readWithPadding out 96 =
      wordBytes (eip712HeadPrefixWords name) ∧
    (eip712NameMemory mem namePtr out name).readWithPadding (out + 224)
      (32 + paddedSize name.size) = stringPayloadBytes name := by
  have hn := UInt256.toNat_ofNat_of_lt hname
  have hcover : name.size ≤ paddedSize name.size := by unfold paddedSize; omega
  have hpad : paddedSize name.size ≤ name.size + 31 := by unfold paddedSize; omega
  have hdata : namePtr + 32 + (UInt256.ofNat name.size).toNat ≤
      (eip712StartMemory mem out).size := by rw [hn]; have := buffer.size; omega
  let copied := stringPayloadMemory (eip712StartMemory mem out) (namePtr + 32) (out + 224)
    (UInt256.ofNat name.size)
  have hsize : copied.size = max (eip712StartMemory mem out).size (out + 288 + name.size) := by
    dsimp only [copied]
    rw [stringPayloadMemory_size _ _ _ _ hdata, hn]
    congr 1
    omega
  have hp := stringPayloadMemory_prefix (eip712StartMemory mem out) (namePtr + 32)
    (out + 224) (UInt256.ofNat name.size) hdata
  refine ⟨(hp.mono (by omega)).trans
    (memoryPrefix_sparse_writeWord _ (out + 64) out _ (.inl (by omega))), ?_, ?_, ?_⟩
  · change _ ≤ (writeWord copied (out + 64) _).size
    rw [writeWord_sparse_size, hsize]
    omega
  · have hfirst : copied.readWithPadding out 64 =
        wordBytes [eip712FieldsWord, ⟨224⟩] := by
      rw [memoryPrefix_read_words hp 2 out hout (by omega)
        (by rw [eip712StartMemory_size]; omega)]
      exact wordSequenceMemory_read mem out [eip712FieldsWord, ⟨224⟩]
    change (writeWord copied (out + 64) _).readWithPadding out 96 = _
    rw [show 96 = 64 + 32 by omega, readWithPadding_split _ _ _ _ (by
      rw [writeWord_sparse_size]; omega),
      writeWord_sparse_read_preserved_unbounded _ _ _ _ _ (by rw [hsize]; omega)
        (.inl (le_refl _)), hfirst, writeWord_sparse_read_back]
    simp only [eip712HeadPrefixWords, wordBytes, ByteArray.append_empty, ByteArray.append_assoc]
  · change (writeWord copied (out + 64) _).readWithPadding _ _ = _
    rw [writeWord_sparse_read_preserved_unbounded _ _ _ _ _ (by rw [hsize]; omega)
      (.inr (by omega))]
    have hr := stringPayloadMemory_read (eip712StartMemory mem out) name (namePtr + 32)
      (out + 224) (UInt256.ofNat name.size) hn.symm hdata (by rw [hn]; omega)
      (by rw [hn]; exact buffer.data)
    simpa only [hn] using hr

theorem eip712VersionMemory_facts (mem name version : ByteArray) (namePtr versionPtr out : Nat)
    (hout : 96 ≤ out) (hversion : version.size < UInt256.size)
    (buffer : StringBuffer (eip712NameMemory mem namePtr out name) versionPtr version)
    (hbelow : versionPtr + 32 + paddedSize version.size ≤ out)
    (hsize : out + 256 + paddedSize name.size ≤ (eip712NameMemory mem namePtr out name).size)
    (hhead : (eip712NameMemory mem namePtr out name).readWithPadding out 96 =
      wordBytes (eip712HeadPrefixWords name))
    (hname : (eip712NameMemory mem namePtr out name).readWithPadding (out + 224)
      (32 + paddedSize name.size) = stringPayloadBytes name) :
    out + 288 + paddedSize name.size + paddedSize version.size ≤
      (eip712VersionMemory mem namePtr versionPtr out name version).size ∧
    (eip712VersionMemory mem namePtr versionPtr out name version).readWithPadding out 96 =
      wordBytes (eip712HeadPrefixWords name) ∧
    (eip712VersionMemory mem namePtr versionPtr out name version).readWithPadding (out + 224)
      (64 + paddedSize name.size + paddedSize version.size) =
        stringPayloadBytes name ++ stringPayloadBytes version := by
  have hv := UInt256.toNat_ofNat_of_lt hversion
  have hcover : version.size ≤ paddedSize version.size := by unfold paddedSize; omega
  have hpad : paddedSize version.size ≤ version.size + 31 := by unfold paddedSize; omega
  have hdata : versionPtr + 32 + (UInt256.ofNat version.size).toNat ≤
      (eip712NameMemory mem namePtr out name).size := by rw [hv]; have := buffer.size; omega
  have hs : (eip712VersionMemory mem namePtr versionPtr out name version).size =
      max (eip712NameMemory mem namePtr out name).size
        (out + 320 + paddedSize name.size + version.size) := by
    rw [eip712VersionMemory, stringPayloadMemory_size _ _ _ _ hdata, hv]
    congr 1
    omega
  have hp := stringPayloadMemory_prefix (eip712NameMemory mem namePtr out name)
    (versionPtr + 32) (out + 256 + paddedSize name.size) (UInt256.ofNat version.size) hdata
  have hcopy : (eip712VersionMemory mem namePtr versionPtr out name version).readWithPadding
      (out + 256 + paddedSize name.size) (32 + paddedSize version.size) =
      stringPayloadBytes version := by
    have hr := stringPayloadMemory_read (eip712NameMemory mem namePtr out name) version
      (versionPtr + 32) (out + 256 + paddedSize name.size) (UInt256.ofNat version.size)
      hv.symm hdata (by rw [hv]; omega)
      (by rw [hv]; exact buffer.data)
    simpa only [hv] using hr
  have hkeep : (eip712VersionMemory mem namePtr versionPtr out name version).readWithPadding
      (out + 224) (32 + paddedSize name.size) = stringPayloadBytes name := by
    have he : 32 * (1 + (name.size + 31) / 32) = 32 + paddedSize name.size := by
      unfold paddedSize
      omega
    have hr := memoryPrefix_read_words hp (1 + (name.size + 31) / 32) (out + 224)
      (by omega) (by rw [he]; omega) (by rw [he]; omega)
    rw [he] at hr
    exact hr.trans hname
  refine ⟨by rw [hs]; omega, ?_, ?_⟩
  · exact (memoryPrefix_read_words hp 3 out hout (by omega) (by omega)).trans hhead
  · rw [show 64 + paddedSize name.size + paddedSize version.size =
      (32 + paddedSize name.size) + (32 + paddedSize version.size) by omega,
      readWithPadding_split _ _ _ _ (by rw [hs]; omega), hkeep,
      show out + 224 + (32 + paddedSize name.size) = out + 256 + paddedSize name.size by omega,
      hcopy]

end Benchmarks.Morpho.MetaMorphoV1_1
