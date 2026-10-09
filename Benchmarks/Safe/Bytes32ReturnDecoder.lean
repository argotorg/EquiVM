import Benchmarks.Safe.Memory
import Benchmarks.Safe.Blocks.Runtime_051
import Reasoning.ABIComposite
import Reasoning.WordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeBytes32DecoderShort {I g s0 σ k C aw mem rdata} {start ret : UInt256}
    {len : Nat} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11787⟩
      (start :: (start + UInt256.ofNat len) :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : len < 32) : RDrev safeBytecode g s0 := by
  have hlt : UInt256.slt (UInt256.ofNat len) (UInt256.ofNat 32) = ⟨1⟩ := by
    apply slt_lit_one_low (by decide)
    rw [ulit_toNat' len (by change len < 2 ^ 256; omega)]
    exact hl
  have hr := safeRuntime_block_11787_fallthrough (by simp; omega)
    (by rw [word_add_sub_left, hlt]; decide) h
  exact safeRuntime_block_11800 (by
    simp only [safeRuntime_block_11787_fallthrough_stack, List.length_cons]; omega) hr

theorem safeBytes32DecoderValid {I g s0 σ k C aw mem rdata} {start ret : UInt256}
    {len : Nat} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11787⟩
      (start :: (start + UInt256.ofNat len) :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : 32 ≤ len) (hb : len < 2 ^ 255)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret (memLoad start mem :: R) mem aw' rdata σ k' C' := by
  have hlt : UInt256.slt (UInt256.ofNat len) (UInt256.ofNat 32) = ⟨0⟩ := by
    apply slt_lit_zero (by decide)
    · rw [ulit_toNat' len (by change len < 2 ^ 256; omega)]; exact hl
    · rw [ulit_toNat' len (by change len < 2 ^ 256; omega)]; exact hb
  have hr := safeRuntime_block_11787_taken (by simp; omega)
    (by rw [word_add_sub_left, hlt]; decide) (by jump_dest) h
  exact safeRuntime_block_11803_packed (by omega) hret hr

-- GENERALIZES decodeReturnValue_bytes32_ok to the modern decoder's signed-size guard.
theorem decodeBytes32ReturnLong {out : ByteArray} (hl : 32 ≤ out.size) (hb : out.size < 2 ^ 255) :
    ABI.decodeReturnValueWithMode? .modern abiBytes32 out =
      some (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE (calldataWord out 0))) := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hw : EVM.Word.toBytesBE (calldataWord out 0) = out.toList.take 32 := by
    have hh := congrArg ByteArray.toList (calldataWord_bytes hl)
    rw [word_toBytesBE_eq_toByteArray_toList]
    simpa only [byteArray_toList_eq,
      ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
      List.drop_zero, Nat.sub_zero] using hh
  rw [hw]
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue? ABI.decodeReturnValues?
  rw [if_neg (by omega)]
  rw [show abiTupleHeadSize? [abiBytes32] = some 32 by
    simp [abiTupleHeadSize?, abiBytes32, isDynamicABIType, staticABIEncodedSize?]]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_ok (mode := .modern) (by rw [List.length_take, hlen]; omega)]

theorem decodeBytes32ReturnShort {out : ByteArray} (hl : out.size < 32) :
    ABI.decodeReturnValueWithMode? .modern abiBytes32 out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue? ABI.decodeReturnValues?
  rw [if_neg (by omega)]
  rw [show abiTupleHeadSize? [abiBytes32] = some 32 by
    simp [abiTupleHeadSize?, abiBytes32, isDynamicABIType, staticABIEncodedSize?]]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_none_short (mode := .modern) (by rw [hlen]; omega)]

end Benchmarks.Safe
