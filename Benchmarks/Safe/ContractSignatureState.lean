import Benchmarks.Safe.ContractSignatureTrace
import Benchmarks.Safe.BytesMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def contractSignatureFinalMemory (mem : ByteArray) (ptr len : Nat) (hash : UInt256)
    (words : List UInt256) (out : ByteArray) : ByteArray :=
  signatureReturnMemory (contractSignatureCallMemory mem ptr len hash words)
    (contractSignatureCallEnd ptr len) out

def contractSignatureNext (ptr len : Nat) (out : ByteArray) : Nat :=
  if out.size = 0 then contractSignatureCallEnd ptr len
  else contractSignatureCallEnd ptr len + 32 + ABI.paddedSize out.size

theorem contractSignatureFinalMemory_free (mem out : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (contractSignatureFinalMemory mem ptr len hash words out) =
      UInt256.ofNat (contractSignatureNext ptr len out) := by
  unfold contractSignatureFinalMemory signatureReturnMemory contractSignatureNext
  split
  · exact contractSignatureCallMemory_free _ _ _ _ _ hn hp
  · exact returnDataMemory_free _ _ _ (by dsimp [contractSignatureCallEnd]; omega)

theorem contractSignatureFinalMemory_preserved (mem out : ByteArray) (ptr len off count : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hin : off + count ≤ mem.size) (hl : 96 ≤ off) (hh : off + count ≤ ptr) :
    (contractSignatureFinalMemory mem ptr len hash words out).readWithPadding off count =
      mem.readWithPadding off count := by
  unfold contractSignatureFinalMemory signatureReturnMemory
  split
  · exact contractSignatureCallMemory_preserved _ _ _ _ _ _ _ hn hin hl hh
  · rw [returnDataMemory_preserved _ _ _ _ _ (by
      rw [contractSignatureCallMemory_size _ _ _ _ _ hn]; omega) hl
      (by dsimp [contractSignatureCallEnd]; omega)]
    exact contractSignatureCallMemory_preserved _ _ _ _ _ _ _ hn hin hl hh

theorem contractSignatureFinalMemory_size_le (mem out : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) (hl : len < 2 ^ 64) (ho : out.size < 2 ^ 138) :
    mem.size ≤ (contractSignatureFinalMemory mem ptr len hash words out).size ∧
      (contractSignatureFinalMemory mem ptr len hash words out).size ≤
        max mem.size (ptr + 2 ^ 140) := by
  unfold contractSignatureFinalMemory signatureReturnMemory
  split
  · rw [contractSignatureCallMemory_size _ _ _ _ _ hn]
    dsimp [contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize]
    omega
  · rw [returnDataMemory_size _ _ _ (by dsimp [contractSignatureCallEnd]; omega),
      contractSignatureCallMemory_size _ _ _ _ _ hn]
    dsimp [contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize]
    omega

theorem contractSignatureNext_bounds (ptr len : Nat) (out : ByteArray)
    (hl : len < 2 ^ 64) (ho : out.size < 2 ^ 138) :
    ptr ≤ contractSignatureNext ptr len out ∧ contractSignatureNext ptr len out ≤ ptr + 2 ^ 140 :=
      by
  unfold contractSignatureNext
  split <;> dsimp [contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize] <;> omega

theorem contractSignatureFinalMemory_bytes {mem out bytes : ByteArray} {ptr len src : Nat}
    {hash : UInt256} {words : List UInt256} (hn : words.length = (len + 31) / 32)
    (hbytes : BytesMemory mem src bytes) (hs : 96 ≤ src) (ha : src + 32 + bytes.size ≤ ptr)
    (hb : src < UInt256.size) :
    BytesMemory (contractSignatureFinalMemory mem ptr len hash words out) src bytes := by
  refine ⟨?_, ?_, ?_⟩
  · rw [memLoadReadWord, ulit_toNat' src hb,
      contractSignatureFinalMemory_preserved _ _ _ _ _ _ _ _ hn (by
        have := hbytes.available; omega) hs (by omega),
      ← ulit_toNat' src hb, ← memLoadReadWord, hbytes.length]
  · rw [contractSignatureFinalMemory_preserved _ _ _ _ _ _ _ _ hn (by
      have := hbytes.available; omega) (by omega) ha, hbytes.payload]
  · have hh : mem.size ≤ (contractSignatureFinalMemory mem ptr len hash words out).size := by
      unfold contractSignatureFinalMemory signatureReturnMemory
      split
      · rw [contractSignatureCallMemory_size _ _ _ _ _ hn]; omega
      · rw [returnDataMemory_size _ _ _ (by dsimp [contractSignatureCallEnd]; omega),
          contractSignatureCallMemory_size _ _ _ _ _ hn]; omega
    have := hbytes.available
    omega

end Benchmarks.Safe
