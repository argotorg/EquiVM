import Benchmarks.Safe.SignatureP256Pieces
import Benchmarks.Safe.P256Memory
import Benchmarks.Safe.BytesMemoryPreserved

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem signatureP256Reads {p : SignatureInput} {mem : ByteArray} {src : Nat} {off : UInt256}
    (hm : BytesMemory mem src p.signatures) (ho : off.toNat + 128 ≤ p.signatures.size)
    (hb : src + 32 + p.signatures.size < UInt256.size) :
    memLoad ((UInt256.ofNat src + off) + UInt256.ofNat 32) mem =
        (signatureP256Input p off).r ∧
      memLoad ((UInt256.ofNat src + off) + UInt256.ofNat 64) mem =
        (signatureP256Input p off).s ∧
      memLoad ((UInt256.ofNat src + off) + UInt256.ofNat 96) mem =
        (signatureP256Input p off).qx ∧
      memLoad ((UInt256.ofNat src + off) + UInt256.ofNat 128) mem =
        (signatureP256Input p off).qy ∧
      keccakWord ((UInt256.ofNat src + off) + UInt256.ofNat 96) (UInt256.ofNat 64) mem =
        signatureP256Signer (signatureP256Input p off) := by
  have hbase : (UInt256.ofNat src + off).toNat = src + off.toNat := by
    have hsrc : (UInt256.ofNat src).toNat = src := ulit_toNat' _ (by omega)
    simpa only [hsrc] using addWord_toNat (UInt256.ofNat src) off (by rw [hsrc]; omega)
  have hadd (j : Nat) (hj : j ≤ 128) :
      ((UInt256.ofNat src + off) + UInt256.ofNat j).toNat = src + off.toNat + j := by
    rw [uadd_word_ofNat_toNat _ _ (by rw [hbase]; omega), hbase]
  have hload (j : Nat) (hj : j ≤ 96) :
      memLoad ((UInt256.ofNat src + off) + UInt256.ofNat (j + 32)) mem =
        calldataWord p.signatures (off.toNat + j) := by
    have ha : (UInt256.ofNat src + off) + UInt256.ofNat (j + 32) =
        UInt256.ofNat (src + 32 + (off.toNat + j)) := by
      apply u256_inj
      rw [hadd _ (by omega), ulit_toNat' _ (by omega)]
      omega
    rw [ha]
    exact hm.word (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.zero_add, Nat.add_zero] using hload 0 (by decide)
  · exact hload 32 (by decide)
  · exact hload 64 (by decide)
  · exact hload 96 (by decide)
  have hread (j : Nat) (hj : j ≤ 96) :
      mem.readWithPadding (src + 32 + (off.toNat + j)) 32 =
        (calldataWord p.signatures (off.toNat + j)).toByteArray := by
    rw [calldataWord_bytes_at (by omega)]
    simpa only [Nat.add_sub_cancel_left] using
      hm.slice (start := off.toNat + j) (finish := off.toNat + j + 32) (by omega) (by omega)
  have hpair : mem.readWithPadding (src + 32 + (off.toNat + 64)) 64 =
      wordBytes [(signatureP256Input p off).qx, (signatureP256Input p off).qy] := by
    rw [show 64 = 32 + 32 from rfl, byteArray_readWithPadding_split_unbounded _ _ _ _
      (by decide) (by decide) (by have := hm.available; omega), hread 64 (by decide),
      show src + 32 + (off.toNat + 64) + 32 = src + 32 + (off.toNat + 96) by omega,
      hread 96 (by decide)]
    simp only [wordBytes, ByteArray.append_empty, signatureP256Input]
  simp only [keccakWord, signatureP256Signer, uInt256OfByteArray_eq]
  rw [hadd 96 (by decide), show (UInt256.ofNat 64).toNat = 64 from rfl,
    show src + off.toNat + 96 = src + 32 + (off.toNat + 64) by omega, hpair]

theorem p256OutputMemory_size (mem out : ByteArray) (ptr : Nat) (input : P256Input) :
    (p256OutputMemory mem ptr input out).size = max mem.size (ptr + 160) := by
  by_cases hz : out.size = 0
  · simp only [p256OutputMemory, hz, Nat.min_zero, byteArray_write_zero_length,
    p256InputMemory_size]
  rw [p256OutputMemory, copyWindow_size _ _ _ _ _ (by omega) (by omega)
    (Nat.zero_le _), p256InputMemory_size]
  omega

theorem p256OutputMemory_bytes {mem out bytes : ByteArray} {ptr src : Nat}
    {input : P256Input} (hm : BytesMemory mem src bytes) (hs : 32 ≤ src)
    (ha : src + 32 + bytes.size ≤ ptr) (hb : src < UInt256.size) :
    BytesMemory (p256OutputMemory mem ptr input out) src bytes := by
  apply hm.preserved hb (p256OutputMemory_lower _ _ _ _)
  intro off count hlo hin
  exact p256OutputMemory_readBelow _ _ _ _ _ _ (by have := hm.available; omega)
    (by omega) (by omega)

theorem p256OutputMemory_zeroSlot {mem out : ByteArray} {ptr : Nat} {input : P256Input}
    (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr) (hz : memLoad ⟨96⟩ mem = ⟨0⟩) :
    memLoad ⟨96⟩ (p256OutputMemory mem ptr input out) = ⟨0⟩ := by
  rw [memLoadReadWord, show (⟨96⟩ : UInt256).toNat = 96 from rfl,
    p256OutputMemory_readBelow _ _ _ _ _ _ hm (by decide) hp,
    ← show (⟨96⟩ : UInt256).toNat = 96 from rfl, ← memLoadReadWord, hz]

end Benchmarks.Safe
