import Benchmarks.Safe.SignaturePiece
import Benchmarks.Safe.Blocks.Runtime_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem signaturePieceReads {mem bytes : ByteArray} {src i : Nat}
    (hm : BytesMemory mem src bytes) (hin : 65 * i + 65 ≤ bytes.size)
    (hb : src + 64 + bytes.size < UInt256.size) :
    memLoad ((UInt256.ofNat src + UInt256.mul (UInt256.ofNat i) (UInt256.ofNat 65)) +
      UInt256.ofNat 32) mem = signatureR bytes i ∧
    memLoad ((UInt256.ofNat src + UInt256.mul (UInt256.ofNat i) (UInt256.ofNat 65)) +
      UInt256.ofNat 64) mem = signatureS bytes i ∧
    UInt256.byteAt ⟨0⟩ (memLoad ((UInt256.ofNat src +
      UInt256.mul (UInt256.ofNat i) (UInt256.ofNat 65)) + UInt256.ofNat 96) mem) =
        signatureV bytes i := by
  have hi : i < UInt256.size := by omega
  have hmul : (UInt256.mul (UInt256.ofNat i) (UInt256.ofNat 65)).toNat = 65 * i := by
    rw [u256_mul_toNat, ulit_toNat' i hi]
    change i * 65 % UInt256.size = 65 * i
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have haddr (j : Nat) (hj32 : 32 ≤ j) (hj : j ≤ 96) :
      (UInt256.ofNat src + UInt256.mul (UInt256.ofNat i) (UInt256.ofNat 65)) + UInt256.ofNat j =
        UInt256.ofNat (src + 32 + (65 * i + j - 32)) := by
    apply u256_inj
    rw [uadd_toNat, uadd_toNat, ulit_toNat' src (by omega), hmul,
      ulit_toNat' j (by omega)]
    rw [Nat.mod_eq_of_lt (by omega : src + 65 * i < UInt256.size)]
    change (src + 65 * i + j) % UInt256.size =
      (src + 32 + (65 * i + j - 32)) % UInt256.size
    congr 1
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [haddr 32 (by decide) (by decide)]
    simpa only [Nat.add_sub_cancel] using hm.word
      (by omega : 65 * i + 32 ≤ bytes.size) (by omega)
  · rw [haddr 64 (by decide) (by decide)]
    have he : 65 * i + 64 - 32 = 65 * i + 32 := by omega
    rw [he]
    exact hm.word (by omega) (by omega)
  · rw [haddr 96 (by decide) (by decide)]
    have he : 65 * i + 96 - 32 = 65 * i + 64 := by omega
    rw [he, hm.byte (by omega) (by omega)]
    rfl

theorem safeSignatureSplit {I g s0 σ k C aw mem rdata src i} {bytes : ByteArray}
    {oldS oldR oldV current last required : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨2011⟩
      (UInt256.ofNat i :: oldS :: oldR :: oldV :: current :: last :: required ::
        UInt256.ofNat src :: R) mem aw rdata σ k C)
    (hm : BytesMemory mem src bytes) (hin : 65 * i + 65 ≤ bytes.size)
    (hb : src + 64 + bytes.size < UInt256.size) (hov : R.length + 13 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0
      (if signatureV bytes i = ⟨0⟩ then ⟨2052⟩ else ⟨2108⟩)
      (UInt256.ofNat i :: signatureS bytes i :: signatureR bytes i :: signatureV bytes i ::
        current :: last :: required :: UInt256.ofNat src :: R) mem aw' rdata σ k' C' := by
  obtain ⟨hr, hs, hv⟩ := signaturePieceReads hm hin hb
  by_cases hz : signatureV bytes i = ⟨0⟩
  · obtain ⟨aw', k', C', h₂⟩ := safeRuntime_block_2011_fallthrough_packed hov
      (by rw [hv, hz]; decide) h
    refine ⟨aw', k', C', ?_⟩
    simpa only [if_pos hz, safeRuntime_block_2011_fallthrough_stack, hr, hs, hv] using h₂
  · obtain ⟨aw', k', C', h₂⟩ := safeRuntime_block_2011_taken_packed hov
      (by rw [hv]; exact u256_zero_sub_ne_zero hz) (by jump_dest) h
    refine ⟨aw', k', C', ?_⟩
    simpa only [if_neg hz, safeRuntime_block_2011_taken_stack, hr, hs, hv] using h₂

end Benchmarks.Safe
