import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ReturnSlice.Words4To7

/-!
# BLAKE2F fallback return-slice bridge

This module proves that the terminal return buffer is the concatenation of the bytecode output
words exposed by `OutputBridge.Slots`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputWordsMem_v13MixedMem_size
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem (v13MixedMem I)).size = 1984 := by
  unfold outputWordsMem
  exact outputWord7Mem_size
    (outputWord6Mem_size
      (outputWord5Mem_size
        (outputWord4Mem_size
          (outputWord3Mem_size
            (outputWord2Mem_size
              (outputWord1Mem_size (outputWord0Mem_size (v13MixedMem_size I hlen))))))))

theorem outputWordsMem_v14FinalFlagMem_size
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    (outputWordsMem (v14FinalFlagMem I)).size = 1984 := by
  unfold outputWordsMem
  exact outputWord7Mem_size
    (outputWord6Mem_size
      (outputWord5Mem_size
        (outputWord4Mem_size
          (outputWord3Mem_size
            (outputWord2Mem_size
              (outputWord1Mem_size (outputWord0Mem_size (v14FinalFlagMem_size I hlen))))))))

theorem zeroRoundsZeroFlagRetSlice_flat
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    ((returnLoopWord7Mem I
        (outputWordsMem (v13MixedMem I))).readWithPadding 2016 64) =
      returnWordBytes (returnLoopWord0 I (outputWordsMem (v13MixedMem I))) ++
      returnWordBytes (returnLoopWord1 I (outputWordsMem (v13MixedMem I))) ++
      returnWordBytes (returnLoopWord2 I (outputWordsMem (v13MixedMem I))) ++
      returnWordBytes (returnLoopWord3 I (outputWordsMem (v13MixedMem I))) ++
      returnWordBytes (returnLoopWord4 I (outputWordsMem (v13MixedMem I))) ++
      returnWordBytes (returnLoopWord5 I (outputWordsMem (v13MixedMem I))) ++
      returnWordBytes (returnLoopWord6 I (outputWordsMem (v13MixedMem I))) ++
      returnWordBytes (returnLoopWord7 I (outputWordsMem (v13MixedMem I))) := by
  exact returnLoopWord7Mem_read2016_64_flat I hlen
    (outputWordsMem_v13MixedMem_size I hlen)

theorem zeroRoundsOneFlagRetSlice_flat
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    ((returnLoopWord7Mem I
        (outputWordsMem (v14FinalFlagMem I))).readWithPadding 2016 64) =
      returnWordBytes (returnLoopWord0 I (outputWordsMem (v14FinalFlagMem I))) ++
      returnWordBytes (returnLoopWord1 I (outputWordsMem (v14FinalFlagMem I))) ++
      returnWordBytes (returnLoopWord2 I (outputWordsMem (v14FinalFlagMem I))) ++
      returnWordBytes (returnLoopWord3 I (outputWordsMem (v14FinalFlagMem I))) ++
      returnWordBytes (returnLoopWord4 I (outputWordsMem (v14FinalFlagMem I))) ++
      returnWordBytes (returnLoopWord5 I (outputWordsMem (v14FinalFlagMem I))) ++
      returnWordBytes (returnLoopWord6 I (outputWordsMem (v14FinalFlagMem I))) ++
      returnWordBytes (returnLoopWord7 I (outputWordsMem (v14FinalFlagMem I))) := by
  exact returnLoopWord7Mem_read2016_64_flat I hlen
    (outputWordsMem_v14FinalFlagMem_size I hlen)

theorem zeroRoundsRetSlice_eq_bytecodeOutputBytes
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    ((returnLoopWord7Mem I (outputWordsMem mem)).readWithPadding 2016 64) =
      bytecodeOutputBytes mem := by
  rw [returnLoopWord7Mem_read2016_64_flat I hlen (outputWordsMem_size hmem)]
  unfold bytecodeOutputBytes
  unfold returnLoopWord0 outputReturnWord0
  rw [returnLoopLoadWord0_outputWordsMem I hlen hmem]
  unfold returnLoopWord1 outputReturnWord1
  rw [returnLoopLoadWord1_outputWordsMem I hlen hmem]
  unfold returnLoopWord2 outputReturnWord2
  rw [returnLoopLoadWord2_outputWordsMem I hlen hmem]
  unfold returnLoopWord3 outputReturnWord3
  rw [returnLoopLoadWord3_outputWordsMem I hlen hmem]
  unfold returnLoopWord4 outputReturnWord4
  rw [returnLoopLoadWord4_outputWordsMem I hlen hmem]
  unfold returnLoopWord5 outputReturnWord5
  rw [returnLoopLoadWord5_outputWordsMem I hlen hmem]
  unfold returnLoopWord6 outputReturnWord6
  rw [returnLoopLoadWord6_outputWordsMem I hlen hmem]
  unfold returnLoopWord7 outputReturnWord7
  rw [returnLoopLoadWord7_outputWordsMem I hlen hmem]

theorem zeroRoundsZeroFlagRetSlice_eq_bytecodeOutputBytes
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    ((returnLoopWord7Mem I
        (outputWordsMem (v13MixedMem I))).readWithPadding 2016 64) =
      bytecodeOutputBytes (v13MixedMem I) := by
  exact zeroRoundsRetSlice_eq_bytecodeOutputBytes I hlen (v13MixedMem_size I hlen)

theorem zeroRoundsOneFlagRetSlice_eq_bytecodeOutputBytes
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    ((returnLoopWord7Mem I
        (outputWordsMem (v14FinalFlagMem I))).readWithPadding 2016 64) =
      bytecodeOutputBytes (v14FinalFlagMem I) := by
  exact zeroRoundsRetSlice_eq_bytecodeOutputBytes I hlen (v14FinalFlagMem_size I hlen)

end Blake2f
