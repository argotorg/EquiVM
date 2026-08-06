import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words0
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words1
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words2
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words3
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words7

/-!
# BLAKE2F zero-round output-word bridge: staged output words

`bytecodeOutputBytes` computes output words after earlier output slots have already been written.
The word-specific files prove the semantic value of each word at the memory stage where it matters
for later words 4--7.  This module supplies the missing preservation facts for the earlier staged
words, and the final-flag-memory preservation facts for words 0--5.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputWordsMem0_read_below_output_slots {mem : ByteArray}
    (hmem : mem.size = 1984) {read : Nat}
    (hread : read + 32 ≤ 1984) (hbelow : read + 32 ≤ 1216) :
    (outputWordsMem0 mem).readWithPadding read 32 = mem.readWithPadding read 32 := by
  unfold outputWordsMem0 outputWord0Mem
  exact toByteArray_write_read_below_of_gap
    (outputWord0 mem) mem 1216 read
    (by rw [hmem]; exact hread)
    hbelow
    (by rw [hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputWordsMem0_read_above_output_slots {mem : ByteArray}
    (hmem : mem.size = 1984) {read : Nat}
    (habove : 1216 + 32 ≤ read) (hin : read + 32 ≤ 1984) :
    (outputWordsMem0 mem).readWithPadding read 32 = mem.readWithPadding read 32 := by
  unfold outputWordsMem0 outputWord0Mem
  exact write32_read_above_len
    (UInt256.toByteArray (outputWord0 mem)) mem 1216 read 32
    (by rw [toByteArray_size])
    (by rw [hmem]; decide)
    habove
    (by rw [hmem]; exact hin)
    (by decide) (by decide)

theorem outputWordsMem1_read_below_output_slots {mem : ByteArray}
    (hmem : mem.size = 1984) {read : Nat}
    (hread : read + 32 ≤ 1984) (hbelow : read + 32 ≤ 1216) :
    (outputWordsMem1 mem).readWithPadding read 32 = mem.readWithPadding read 32 := by
  unfold outputWordsMem1 outputWord1Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord1 (outputWordsMem0 mem)) (outputWordsMem0 mem) 1248 read
    (by rw [outputWordsMem0_size hmem]; exact hread)
    (by omega)
    (by rw [outputWordsMem0_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem0_read_below_output_slots hmem hread hbelow

theorem outputWordsMem1_read_above_output_slots {mem : ByteArray}
    (hmem : mem.size = 1984) {read : Nat}
    (habove : 1248 + 32 ≤ read) (hin : read + 32 ≤ 1984) :
    (outputWordsMem1 mem).readWithPadding read 32 = mem.readWithPadding read 32 := by
  unfold outputWordsMem1 outputWord1Mem
  rw [write32_read_above_len
    (UInt256.toByteArray (outputWord1 (outputWordsMem0 mem))) (outputWordsMem0 mem)
    1248 read 32
    (by rw [toByteArray_size])
    (by rw [outputWordsMem0_size hmem]; decide)
    habove
    (by rw [outputWordsMem0_size hmem]; exact hin)
    (by decide) (by decide)]
  exact outputWordsMem0_read_above_output_slots hmem (by omega) hin

theorem outputWordsMem2_read_below_output_slots {mem : ByteArray}
    (hmem : mem.size = 1984) {read : Nat}
    (hread : read + 32 ≤ 1984) (hbelow : read + 32 ≤ 1216) :
    (outputWordsMem2 mem).readWithPadding read 32 = mem.readWithPadding read 32 := by
  unfold outputWordsMem2 outputWord2Mem
  rw [toByteArray_write_read_below_of_gap
    (outputWord2 (outputWordsMem1 mem)) (outputWordsMem1 mem) 1280 read
    (by rw [outputWordsMem1_size hmem]; exact hread)
    (by omega)
    (by rw [outputWordsMem1_size hmem]; change 0 < USize.size; exact lt_usize 0 (by norm_num))]
  exact outputWordsMem1_read_below_output_slots hmem hread hbelow

theorem outputWordsMem2_read_above_output_slots {mem : ByteArray}
    (hmem : mem.size = 1984) {read : Nat}
    (habove : 1280 + 32 ≤ read) (hin : read + 32 ≤ 1984) :
    (outputWordsMem2 mem).readWithPadding read 32 = mem.readWithPadding read 32 := by
  unfold outputWordsMem2 outputWord2Mem
  rw [write32_read_above_len
    (UInt256.toByteArray (outputWord2 (outputWordsMem1 mem))) (outputWordsMem1 mem)
    1280 read 32
    (by rw [toByteArray_size])
    (by rw [outputWordsMem1_size hmem]; decide)
    habove
    (by rw [outputWordsMem1_size hmem]; exact hin)
    (by decide) (by decide)]
  exact outputWordsMem1_read_above_output_slots hmem (by omega) hin

theorem outputWord1_outputWordsMem0_eq {mem : ByteArray} (hmem : mem.size = 1984) :
    outputWord1 (outputWordsMem0 mem) = outputWord1 mem := by
  unfold outputWord1 outputH1LoadWord outputV1LoadWord outputV9LoadWord
  rw [outputWordsMem0_read_below_output_slots hmem (by decide) (by decide)]
  rw [outputWordsMem0_read_above_output_slots hmem (by decide) (by decide)]
  rw [outputWordsMem0_read_above_output_slots hmem (by decide) (by decide)]

theorem outputWord2_outputWordsMem1_eq {mem : ByteArray} (hmem : mem.size = 1984) :
    outputWord2 (outputWordsMem1 mem) = outputWord2 mem := by
  unfold outputWord2 outputH2LoadWord outputV2LoadWord outputV10LoadWord
  rw [outputWordsMem1_read_below_output_slots hmem (by decide) (by decide)]
  rw [outputWordsMem1_read_above_output_slots hmem (by decide) (by decide)]
  rw [outputWordsMem1_read_above_output_slots hmem (by decide) (by decide)]

theorem outputWord3_outputWordsMem2_eq {mem : ByteArray} (hmem : mem.size = 1984) :
    outputWord3 (outputWordsMem2 mem) = outputWord3 mem := by
  unfold outputWord3 outputH3LoadWord outputV3LoadWord outputV11LoadWord
  rw [outputWordsMem2_read_below_output_slots hmem (by decide) (by decide)]
  rw [outputWordsMem2_read_above_output_slots hmem (by decide) (by decide)]
  rw [outputWordsMem2_read_above_output_slots hmem (by decide) (by decide)]

theorem outputWord4_outputWordsMem3_eq {mem : ByteArray} (hmem : mem.size = 1984) :
    outputWord4 (outputWordsMem3 mem) = outputWord4 mem := by
  unfold outputWord4 outputH4LoadWord outputV4LoadWord outputV12LoadWord
  rw [outputWordsMem3_read_below_output_slots hmem (by decide) (by decide)]
  rw [outputWordsMem3_read_above_output_slots hmem (by decide) (by decide)]
  rw [outputWordsMem3_read_above_output_slots hmem (by decide) (by decide)]

theorem outputWord5_outputWordsMem4_eq {mem : ByteArray} (hmem : mem.size = 1984) :
    outputWord5 (outputWordsMem4 mem) = outputWord5 mem := by
  unfold outputWord5 outputH5LoadWord outputV5LoadWord outputV13LoadWord
  rw [outputWordsMem4_read_below_output_slots hmem (by decide) (by decide)]
  rw [outputWordsMem4_read_above_output_slots hmem (by decide) (by decide)]
  rw [outputWordsMem4_read_above_output_slots hmem (by decide) (by decide)]

theorem v14FinalFlagMem_read_below_flag_slot
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) {read : Nat}
    (hread : read + 32 ≤ 1984) (hbelow : read + 32 ≤ 1920) :
    (v14FinalFlagMem I).readWithPadding read 32 =
      (v13MixedMem I).readWithPadding read 32 := by
  unfold v14FinalFlagMem
  exact toByteArray_write_read_below_of_gap
    (UInt256.ofNat 16175846103906665108) (v13MixedMem I) 1920 read
    (by rw [v13MixedMem_size I hlen]; exact hread)
    hbelow
    (by rw [v13MixedMem_size I hlen]; change 0 < USize.size; exact lt_usize 0 (by norm_num))

theorem outputWord0_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord0 (v14FinalFlagMem I) = UInt256.ofNat 7640891576956012808 := by
  unfold outputWord0 outputH0LoadWord outputV0LoadWord outputV8LoadWord
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  exact outputWord0_v13MixedMem I hlen

theorem outputWord1_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord1 (v14FinalFlagMem I) = UInt256.ofNat 13503953896175478587 := by
  unfold outputWord1 outputH1LoadWord outputV1LoadWord outputV9LoadWord
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  exact outputWord1_v13MixedMem I hlen

theorem outputWord2_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord2 (v14FinalFlagMem I) = UInt256.ofNat 4354685564936845355 := by
  unfold outputWord2 outputH2LoadWord outputV2LoadWord outputV10LoadWord
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  exact outputWord2_v13MixedMem I hlen

theorem outputWord3_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord3 (v14FinalFlagMem I) = UInt256.ofNat 11912009170470909681 := by
  unfold outputWord3 outputH3LoadWord outputV3LoadWord outputV11LoadWord
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  exact outputWord3_v13MixedMem I hlen

theorem outputWord4_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord4 (v14FinalFlagMem I) =
      UInt256.land (v12MixedWord I) ⟨18446744073709551615⟩ := by
  have hbase :
      outputWord4 (v13MixedMem I) =
        UInt256.land (v12MixedWord I) ⟨18446744073709551615⟩ := by
    rw [← outputWord4_outputWordsMem3_eq (v13MixedMem_size I hlen)]
    exact outputWord4_outputWordsMem3_v13MixedMem I hlen
  unfold outputWord4 outputH4LoadWord outputV4LoadWord outputV12LoadWord
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  exact hbase

theorem outputWord5_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord5 (v14FinalFlagMem I) =
      UInt256.land (v13MixedWord I) ⟨18446744073709551615⟩ := by
  have hbase :
      outputWord5 (v13MixedMem I) =
        UInt256.land (v13MixedWord I) ⟨18446744073709551615⟩ := by
    rw [← outputWord5_outputWordsMem4_eq (v13MixedMem_size I hlen)]
    exact outputWord5_outputWordsMem4_v13MixedMem I hlen
  unfold outputWord5 outputH5LoadWord outputV5LoadWord outputV13LoadWord
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  rw [v14FinalFlagMem_read_below_flag_slot I hlen (by decide) (by decide)]
  exact hbase

theorem outputWord1_outputWordsMem0_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord1 (outputWordsMem0 (v13MixedMem I)) =
      UInt256.ofNat 13503953896175478587 := by
  rw [outputWord1_outputWordsMem0_eq (v13MixedMem_size I hlen)]
  exact outputWord1_v13MixedMem I hlen

theorem outputWord2_outputWordsMem1_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord2 (outputWordsMem1 (v13MixedMem I)) =
      UInt256.ofNat 4354685564936845355 := by
  rw [outputWord2_outputWordsMem1_eq (v13MixedMem_size I hlen)]
  exact outputWord2_v13MixedMem I hlen

theorem outputWord3_outputWordsMem2_v13MixedMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord3 (outputWordsMem2 (v13MixedMem I)) =
      UInt256.ofNat 11912009170470909681 := by
  rw [outputWord3_outputWordsMem2_eq (v13MixedMem_size I hlen)]
  exact outputWord3_v13MixedMem I hlen

theorem outputWord1_outputWordsMem0_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord1 (outputWordsMem0 (v14FinalFlagMem I)) =
      UInt256.ofNat 13503953896175478587 := by
  rw [outputWord1_outputWordsMem0_eq (v14FinalFlagMem_size I hlen)]
  exact outputWord1_v14FinalFlagMem I hlen

theorem outputWord2_outputWordsMem1_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord2 (outputWordsMem1 (v14FinalFlagMem I)) =
      UInt256.ofNat 4354685564936845355 := by
  rw [outputWord2_outputWordsMem1_eq (v14FinalFlagMem_size I hlen)]
  exact outputWord2_v14FinalFlagMem I hlen

theorem outputWord3_outputWordsMem2_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord3 (outputWordsMem2 (v14FinalFlagMem I)) =
      UInt256.ofNat 11912009170470909681 := by
  rw [outputWord3_outputWordsMem2_eq (v14FinalFlagMem_size I hlen)]
  exact outputWord3_v14FinalFlagMem I hlen

theorem outputWord4_outputWordsMem3_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord4 (outputWordsMem3 (v14FinalFlagMem I)) =
      UInt256.land (v12MixedWord I) ⟨18446744073709551615⟩ := by
  rw [outputWord4_outputWordsMem3_eq (v14FinalFlagMem_size I hlen)]
  exact outputWord4_v14FinalFlagMem I hlen

theorem outputWord5_outputWordsMem4_v14FinalFlagMem
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    outputWord5 (outputWordsMem4 (v14FinalFlagMem I)) =
      UInt256.land (v13MixedWord I) ⟨18446744073709551615⟩ := by
  rw [outputWord5_outputWordsMem4_eq (v14FinalFlagMem_size I hlen)]
  exact outputWord5_v14FinalFlagMem I hlen

end Blake2f
