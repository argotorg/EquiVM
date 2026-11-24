import Benchmarks.Safe.ViaIR.Memory
import Benchmarks.Safe.ViaIR.Blocks.Runtime_001
import Benchmarks.Safe.ViaIR.Blocks.Runtime_045
import Reasoning.ABIComposite
import Reasoning.WordArithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeBytes32DecoderShort {I g s0 σ k C aw mem rdata} {start : UInt256}
    {len : Nat} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10041⟩
      (UInt256.ofNat len :: start :: ⟨32⟩ :: start :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : len < 32) : RDrev fork safeBytecode g s0 := by
  have hlt : UInt256.slt (UInt256.ofNat len) (UInt256.ofNat 32) = ⟨1⟩ := by
    apply slt_lit_one_low (by decide)
    rw [ulit_toNat' len (by change len < 2 ^ 256; omega)]
    exact hl
  have hr := safeRuntime_block_10041_taken (by simp; omega)
    (by
      rw [word_add_sub_left]
      change UInt256.slt (UInt256.ofNat len) (UInt256.ofNat 32) ≠ ⟨0⟩
      rw [hlt]; decide) (by jump_dest) h
  exact safeRuntime_block_111 (by
    simp only [safeRuntime_block_10041_taken_stack, List.length_cons]; omega) hr

theorem safeBytes32DecoderValid {I g s0 σ k C aw mem rdata} {start : UInt256}
    {len : Nat} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10041⟩
      (UInt256.ofNat len :: start :: ⟨32⟩ :: start :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hl : 32 ≤ len) (hb : len < 2 ^ 255) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨10003⟩ (⟨0⟩ :: memLoad start mem :: R)
      mem aw' rdata σ k' C' := by
  have hlt : UInt256.slt (UInt256.ofNat len) (UInt256.ofNat 32) = ⟨0⟩ := by
    apply slt_lit_zero (by decide)
    · rw [ulit_toNat' len (by change len < 2 ^ 256; omega)]; exact hl
    · rw [ulit_toNat' len (by change len < 2 ^ 256; omega)]; exact hb
  have hr := safeRuntime_block_10041_fallthrough (by simp; omega)
    (by rw [word_add_sub_left]; exact hlt) h
  exact safeRuntime_block_10050_packed (by omega) (by jump_dest) hr

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

end Benchmarks.Safe.ViaIR
