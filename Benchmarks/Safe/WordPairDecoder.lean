import Benchmarks.Safe.Calldata
import Benchmarks.Safe.Decoders
import Benchmarks.Safe.Blocks.Runtime_043

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: the modern ABI decoder for two unrestricted uint256 words.
theorem decodeWordPairGuard {cd : ByteArray} {x y : Solm.Ident} (hlong : 4 ≤ cd.size) :
    decodeCalldata [x, y] [abiUInt256, abiUInt256] cd =
      if 2 ^ 255 ≤ cd.size - 4 then none
      else if cd.size - 4 < 64 then none
      else (do
        let (values, _) ← decodeABIValues? [abiUInt256, abiUInt256]
          (cd.toList.drop 4) 0 0 64 64
        decodeCalldata.insertValues [x, y] values ∅) :=
  decodeStaticCalldata hlong (by decide) (by decide)
    (by simp [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType,
      abiUInt256, bind, Option.bind])

theorem decodeWordPair {cd : ByteArray} {x y : Solm.Ident}
    (hlen : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4) :
    decodeCalldata [x, y] [abiUInt256, abiUInt256] cd =
      some (((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))).insert
        y (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  rw [decodeWordPairGuard (by omega), if_neg (by omega), if_neg (by omega)]
  have hlist : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlist]; omega
  have htake36 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlist]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq_any cd 4 (by omega)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq_any cd 36 hlen
  simp only [decodeABIValues?, isDynamicABIType, Bool.false_eq_true, if_false,
    staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  rw [decodeABIValue_uint256_ok (start := 0) (by simpa using htake4),
    decodeABIValue_uint256_ok (start := 32) htake36]
  simp [decodeCalldata.insertValues, hword4, hword36, List.drop_drop]

theorem decodeWordPairShort {cd : ByteArray} {x y : Solm.Ident}
    (hlong : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [abiUInt256, abiUInt256] cd = none := by
  rw [decodeWordPairGuard hlong, if_neg (by omega), if_pos (by omega)]

theorem decodeWordPairHuge {cd : ByteArray} {x y : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y] [abiUInt256, abiUInt256] cd = none := by
  rw [decodeWordPairGuard (by omega), if_pos (by omega)]

theorem safeDecodeWordPair {I g s0 σ k C aw mem rdata} {head stop ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9844⟩ (head :: stop :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 64) = ⟨0⟩)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret
      (calldataWord I.calldata (head + UInt256.ofNat 32).toNat ::
        calldataWord I.calldata head.toNat :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_9844_taken (by simp; omega) (by rw [hlen]; decide)
    (by jump_dest) h
  have h₂ := safeRuntime_block_9861 (by simp; omega) hret h₁
  exact ⟨_, _, h₂⟩

theorem safeDecodeWordPairRevert {I g s0 σ k C aw mem rdata} {head stop : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9844⟩ (head :: stop :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hlen : UInt256.slt (UInt256.sub stop head) (UInt256.ofNat 64) = ⟨1⟩) :
    RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_9844_fallthrough hov (by rw [hlen]; decide) h
  exact safeRuntime_block_9858
    (by simp only [safeRuntime_block_9844_fallthrough_stack, List.length_cons]; omega) h₁

end Benchmarks.Safe
