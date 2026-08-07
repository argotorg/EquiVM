import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopReturnFinal
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ByteOrder
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ParserValues
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Staged
import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords.Words7

/-!
# BLAKE2F positive-round output/model bridge

This file closes the functional bridge left by `LoopReturnFinal`: from the arbitrary-round final
memory invariant at index `Model.rounds calldata`, the bytecode output-word expression is exactly
the trusted pure model output.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

private theorem memorySlotStoresU64.word
    {mem : ByteArray} {off : Nat} {w : UInt64}
    (h : memorySlotStoresU64 mem off w) :
    memoryWord mem off = UInt256.ofNat w.toNat := by
  simpa [memorySlotStoresU64, u64AsWord] using h

theorem outputWord6_outputWordsMem5_eq {mem : ByteArray} (hmem : mem.size = 1984) :
    outputWord6 (outputWordsMem5 mem) = outputWord6 mem := by
  unfold outputWord6 outputH6LoadWord outputV6LoadWord outputV14LoadWord
  rw [outputWordsMem5_read_below_output_slots hmem (by decide) (by decide)]
  rw [outputWordsMem5_read_above_output_slots hmem (by decide) (by decide)]
  rw [outputWordsMem5_read_above_output_slots hmem (by decide) (by decide)]

theorem outputWord7_outputWordsMem6_eq {mem : ByteArray} (hmem : mem.size = 1984) :
    outputWord7 (outputWordsMem6 mem) = outputWord7 mem := by
  unfold outputWord7 outputH7LoadWord outputV7LoadWord outputV15LoadWord
  rw [outputWordsMem6_read_below_output_slots hmem (by decide) (by decide)]
  rw [outputWordsMem6_read_above_output_slots hmem (by decide) (by decide)]
  rw [outputWordsMem6_read_above_output_slots hmem (by decide) (by decide)]

private theorem outputWord0_eq_modelWord
    {mem : ByteArray} {h v : Array UInt64}
    (hH : memoryRepresentsH mem h)
    (hV : memoryRepresentsVector mem v) :
    outputWord0 mem =
      UInt256.ofNat ((h[0]! ^^^ v[0]! ^^^ v[8]!).toNat) := by
  have hh :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 384 32)) =
        UInt256.ofNat (h[0]!).toNat := by
    simpa [memoryWord, hSlotOffset, hBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hH.2 0 (by decide))
  have hv0 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32)) =
        UInt256.ofNat (v[0]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 0 (by decide))
  have hv8 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1728 32)) =
        UInt256.ofNat (v[8]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 8 (by decide))
  unfold outputWord0 outputH0LoadWord outputV0LoadWord outputV8LoadWord
  rw [hh, hv0, hv8]
  simpa
    using show
      UInt256.land
        (UInt256.xor
          (UInt256.xor
            (UInt256.land (UInt256.ofNat (h[0]!).toNat) ⟨18446744073709551615⟩)
            (UInt256.ofNat (v[0]!).toNat))
          (UInt256.ofNat (v[8]!).toNat))
        ⟨18446744073709551615⟩ =
          UInt256.ofNat ((h[0]! ^^^ v[0]! ^^^ v[8]!).toNat) by
      rw [land_u64_mask, u256_xor_u64, u256_xor_u64, land_u64_mask]

private theorem outputWord1_eq_modelWord
    {mem : ByteArray} {h v : Array UInt64}
    (hH : memoryRepresentsH mem h)
    (hV : memoryRepresentsVector mem v) :
    outputWord1 mem =
      UInt256.ofNat ((h[1]! ^^^ v[1]! ^^^ v[9]!).toNat) := by
  have hh :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 416 32)) =
        UInt256.ofNat (h[1]!).toNat := by
    simpa [memoryWord, hSlotOffset, hBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hH.2 1 (by decide))
  have hv1 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1504 32)) =
        UInt256.ofNat (v[1]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 1 (by decide))
  have hv9 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1760 32)) =
        UInt256.ofNat (v[9]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 9 (by decide))
  unfold outputWord1 outputH1LoadWord outputV1LoadWord outputV9LoadWord
  rw [hh, hv1, hv9]
  simpa
    using show
      UInt256.land
        (UInt256.xor
          (UInt256.xor
            (UInt256.land (UInt256.ofNat (h[1]!).toNat) ⟨18446744073709551615⟩)
            (UInt256.ofNat (v[1]!).toNat))
          (UInt256.ofNat (v[9]!).toNat))
        ⟨18446744073709551615⟩ =
          UInt256.ofNat ((h[1]! ^^^ v[1]! ^^^ v[9]!).toNat) by
      rw [land_u64_mask, u256_xor_u64, u256_xor_u64, land_u64_mask]

private theorem outputWord2_eq_modelWord
    {mem : ByteArray} {h v : Array UInt64}
    (hH : memoryRepresentsH mem h)
    (hV : memoryRepresentsVector mem v) :
    outputWord2 mem =
      UInt256.ofNat ((h[2]! ^^^ v[2]! ^^^ v[10]!).toNat) := by
  have hh :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 448 32)) =
        UInt256.ofNat (h[2]!).toNat := by
    simpa [memoryWord, hSlotOffset, hBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hH.2 2 (by decide))
  have hv2 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1536 32)) =
        UInt256.ofNat (v[2]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 2 (by decide))
  have hv10 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1792 32)) =
        UInt256.ofNat (v[10]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 10 (by decide))
  unfold outputWord2 outputH2LoadWord outputV2LoadWord outputV10LoadWord
  rw [hh, hv2, hv10]
  simpa
    using show
      UInt256.land
        (UInt256.xor
          (UInt256.xor
            (UInt256.land (UInt256.ofNat (h[2]!).toNat) ⟨18446744073709551615⟩)
            (UInt256.ofNat (v[2]!).toNat))
          (UInt256.ofNat (v[10]!).toNat))
        ⟨18446744073709551615⟩ =
          UInt256.ofNat ((h[2]! ^^^ v[2]! ^^^ v[10]!).toNat) by
      rw [land_u64_mask, u256_xor_u64, u256_xor_u64, land_u64_mask]

private theorem outputWord3_eq_modelWord
    {mem : ByteArray} {h v : Array UInt64}
    (hH : memoryRepresentsH mem h)
    (hV : memoryRepresentsVector mem v) :
    outputWord3 mem =
      UInt256.ofNat ((h[3]! ^^^ v[3]! ^^^ v[11]!).toNat) := by
  have hh :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 480 32)) =
        UInt256.ofNat (h[3]!).toNat := by
    simpa [memoryWord, hSlotOffset, hBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hH.2 3 (by decide))
  have hv3 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1568 32)) =
        UInt256.ofNat (v[3]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 3 (by decide))
  have hv11 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1824 32)) =
        UInt256.ofNat (v[11]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 11 (by decide))
  unfold outputWord3 outputH3LoadWord outputV3LoadWord outputV11LoadWord
  rw [hh, hv3, hv11]
  simpa
    using show
      UInt256.land
        (UInt256.xor
          (UInt256.xor
            (UInt256.land (UInt256.ofNat (h[3]!).toNat) ⟨18446744073709551615⟩)
            (UInt256.ofNat (v[3]!).toNat))
          (UInt256.ofNat (v[11]!).toNat))
        ⟨18446744073709551615⟩ =
          UInt256.ofNat ((h[3]! ^^^ v[3]! ^^^ v[11]!).toNat) by
      rw [land_u64_mask, u256_xor_u64, u256_xor_u64, land_u64_mask]

private theorem outputWord4_eq_modelWord
    {mem : ByteArray} {h v : Array UInt64}
    (hH : memoryRepresentsH mem h)
    (hV : memoryRepresentsVector mem v) :
    outputWord4 mem =
      UInt256.ofNat ((h[4]! ^^^ v[4]! ^^^ v[12]!).toNat) := by
  have hh :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 512 32)) =
        UInt256.ofNat (h[4]!).toNat := by
    simpa [memoryWord, hSlotOffset, hBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hH.2 4 (by decide))
  have hv4 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1600 32)) =
        UInt256.ofNat (v[4]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 4 (by decide))
  have hv12 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1856 32)) =
        UInt256.ofNat (v[12]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 12 (by decide))
  unfold outputWord4 outputH4LoadWord outputV4LoadWord outputV12LoadWord
  rw [hh, hv4, hv12]
  simpa
    using show
      UInt256.land
        (UInt256.xor
          (UInt256.xor
            (UInt256.land (UInt256.ofNat (h[4]!).toNat) ⟨18446744073709551615⟩)
            (UInt256.ofNat (v[4]!).toNat))
          (UInt256.ofNat (v[12]!).toNat))
        ⟨18446744073709551615⟩ =
          UInt256.ofNat ((h[4]! ^^^ v[4]! ^^^ v[12]!).toNat) by
      rw [land_u64_mask, u256_xor_u64, u256_xor_u64, land_u64_mask]

private theorem outputWord5_eq_modelWord
    {mem : ByteArray} {h v : Array UInt64}
    (hH : memoryRepresentsH mem h)
    (hV : memoryRepresentsVector mem v) :
    outputWord5 mem =
      UInt256.ofNat ((h[5]! ^^^ v[5]! ^^^ v[13]!).toNat) := by
  have hh :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 544 32)) =
        UInt256.ofNat (h[5]!).toNat := by
    simpa [memoryWord, hSlotOffset, hBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hH.2 5 (by decide))
  have hv5 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32)) =
        UInt256.ofNat (v[5]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 5 (by decide))
  have hv13 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1888 32)) =
        UInt256.ofNat (v[13]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 13 (by decide))
  unfold outputWord5 outputH5LoadWord outputV5LoadWord outputV13LoadWord
  rw [hh, hv5, hv13]
  simpa
    using show
      UInt256.land
        (UInt256.xor
          (UInt256.xor
            (UInt256.land (UInt256.ofNat (h[5]!).toNat) ⟨18446744073709551615⟩)
            (UInt256.ofNat (v[5]!).toNat))
          (UInt256.ofNat (v[13]!).toNat))
        ⟨18446744073709551615⟩ =
          UInt256.ofNat ((h[5]! ^^^ v[5]! ^^^ v[13]!).toNat) by
      rw [land_u64_mask, u256_xor_u64, u256_xor_u64, land_u64_mask]

private theorem outputWord6_eq_modelWord
    {mem : ByteArray} {h v : Array UInt64}
    (hH : memoryRepresentsH mem h)
    (hV : memoryRepresentsVector mem v) :
    outputWord6 mem =
      UInt256.ofNat ((h[6]! ^^^ v[6]! ^^^ v[14]!).toNat) := by
  have hh :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 576 32)) =
        UInt256.ofNat (h[6]!).toNat := by
    simpa [memoryWord, hSlotOffset, hBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hH.2 6 (by decide))
  have hv6 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1664 32)) =
        UInt256.ofNat (v[6]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 6 (by decide))
  have hv14 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1920 32)) =
        UInt256.ofNat (v[14]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 14 (by decide))
  unfold outputWord6 outputH6LoadWord outputV6LoadWord outputV14LoadWord
  rw [hh, hv6, hv14]
  simpa
    using show
      UInt256.land
        (UInt256.xor
          (UInt256.xor
            (UInt256.land (UInt256.ofNat (h[6]!).toNat) ⟨18446744073709551615⟩)
            (UInt256.ofNat (v[6]!).toNat))
          (UInt256.ofNat (v[14]!).toNat))
        ⟨18446744073709551615⟩ =
          UInt256.ofNat ((h[6]! ^^^ v[6]! ^^^ v[14]!).toNat) by
      rw [land_u64_mask, u256_xor_u64, u256_xor_u64, land_u64_mask]

private theorem outputWord7_eq_modelWord
    {mem : ByteArray} {h v : Array UInt64}
    (hH : memoryRepresentsH mem h)
    (hV : memoryRepresentsVector mem v) :
    outputWord7 mem =
      UInt256.ofNat ((h[7]! ^^^ v[7]! ^^^ v[15]!).toNat) := by
  have hh :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 608 32)) =
        UInt256.ofNat (h[7]!).toNat := by
    simpa [memoryWord, hSlotOffset, hBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hH.2 7 (by decide))
  have hv7 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1696 32)) =
        UInt256.ofNat (v[7]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 7 (by decide))
  have hv15 :
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32)) =
        UInt256.ofNat (v[15]!).toNat := by
    simpa [memoryWord, vSlotOffset, vBaseOffset, wordBytes] using
      memorySlotStoresU64.word (hV.2 15 (by decide))
  unfold outputWord7 outputH7LoadWord outputV7LoadWord outputV15LoadWord
  rw [hh, hv7, hv15]
  simpa
    using show
      UInt256.land
        (UInt256.xor
          (UInt256.xor
            (UInt256.land (UInt256.ofNat (h[7]!).toNat) ⟨18446744073709551615⟩)
            (UInt256.ofNat (v[7]!).toNat))
          (UInt256.ofNat (v[15]!).toNat))
        ⟨18446744073709551615⟩ =
          UInt256.ofNat ((h[7]! ^^^ v[7]! ^^^ v[15]!).toNat) by
      rw [land_u64_mask, u256_xor_u64, u256_xor_u64, land_u64_mask]

theorem compressBytesLoop_eq_modelWordChunks (input : ByteArray) (rounds : Nat) :
    Model.compressBytesLoop input rounds =
      modelWordChunk ((Model.compressLoop rounds (Model.parsedH input) (Model.parsedM input)
        (Model.parsedT0 input) (Model.parsedT1 input) (Model.parsedFinalFlag input))[0]!) ++
      modelWordChunk ((Model.compressLoop rounds (Model.parsedH input) (Model.parsedM input)
        (Model.parsedT0 input) (Model.parsedT1 input) (Model.parsedFinalFlag input))[1]!) ++
      modelWordChunk ((Model.compressLoop rounds (Model.parsedH input) (Model.parsedM input)
        (Model.parsedT0 input) (Model.parsedT1 input) (Model.parsedFinalFlag input))[2]!) ++
      modelWordChunk ((Model.compressLoop rounds (Model.parsedH input) (Model.parsedM input)
        (Model.parsedT0 input) (Model.parsedT1 input) (Model.parsedFinalFlag input))[3]!) ++
      modelWordChunk ((Model.compressLoop rounds (Model.parsedH input) (Model.parsedM input)
        (Model.parsedT0 input) (Model.parsedT1 input) (Model.parsedFinalFlag input))[4]!) ++
      modelWordChunk ((Model.compressLoop rounds (Model.parsedH input) (Model.parsedM input)
        (Model.parsedT0 input) (Model.parsedT1 input) (Model.parsedFinalFlag input))[5]!) ++
      modelWordChunk ((Model.compressLoop rounds (Model.parsedH input) (Model.parsedM input)
        (Model.parsedT0 input) (Model.parsedT1 input) (Model.parsedFinalFlag input))[6]!) ++
      modelWordChunk ((Model.compressLoop rounds (Model.parsedH input) (Model.parsedM input)
        (Model.parsedT0 input) (Model.parsedT1 input) (Model.parsedFinalFlag input))[7]!) := by
  unfold Model.compressBytesLoop
  simp [List.range', model_writeLE64_append]

theorem positiveRoundBytecodeOutput_eq_modelOutput
    (ctx : BytecodeContext) {mem : ByteArray}
    (hinv : positiveRoundInvariantContextRead64 ctx
      (Model.rounds ctx.executionEnv.calldata) mem) :
    bytecodeOutputBytes mem = output ctx := by
  let input := ctx.executionEnv.calldata
  let rounds := Model.rounds input
  let h := Model.parsedH input
  let v := positiveRoundModelState input rounds
  have hmodel :
      positiveRoundHeaderInvariant ctx.executionEnv rounds mem := by
    simpa [input, rounds] using
      positiveRoundInvariantContext.model
        (positiveRoundInvariantContextRead64.invariant hinv)
  have hmem : mem.size = 1984 :=
    positiveRoundHeaderInvariant.mem_size hmodel
  have hH : memoryRepresentsH mem h := by
    simpa [input, h] using positiveRoundHeaderInvariant.representsH hmodel
  have hV : memoryRepresentsVector mem v := by
    simpa [input, rounds, v, positiveRoundModelState] using
      positiveRoundHeaderInvariant.representsVector hmodel
  have hw0 := outputWord0_eq_modelWord (mem := mem)
    (h := h) (v := v) hH hV
  have hw1 := outputWord1_eq_modelWord (mem := mem)
    (h := h) (v := v) hH hV
  have hw2 := outputWord2_eq_modelWord (mem := mem)
    (h := h) (v := v) hH hV
  have hw3 := outputWord3_eq_modelWord (mem := mem)
    (h := h) (v := v) hH hV
  have hw4 := outputWord4_eq_modelWord (mem := mem)
    (h := h) (v := v) hH hV
  have hw5 := outputWord5_eq_modelWord (mem := mem)
    (h := h) (v := v) hH hV
  have hw6 := outputWord6_eq_modelWord (mem := mem)
    (h := h) (v := v) hH hV
  have hw7 := outputWord7_eq_modelWord (mem := mem)
    (h := h) (v := v) hH hV
  have hcompress :
      Model.compressLoop rounds (Model.parsedH input) (Model.parsedM input)
          (Model.parsedT0 input) (Model.parsedT1 input) (Model.parsedFinalFlag input) =
        Model.finalize h v := by
    simp [Model.compressLoop, positiveRoundModelState, h, v, input, rounds]
  unfold output
  rw [Model.output_eq_compressBytesLoop]
  rw [compressBytesLoop_eq_modelWordChunks]
  rw [hcompress]
  unfold Model.finalize
  simp [List.range']
  unfold bytecodeOutputBytes outputReturnWord0 outputReturnWord1 outputReturnWord2
    outputReturnWord3 outputReturnWord4 outputReturnWord5 outputReturnWord6 outputReturnWord7
  rw [outputWord1_outputWordsMem0_eq hmem]
  rw [outputWord2_outputWordsMem1_eq hmem]
  rw [outputWord3_outputWordsMem2_eq hmem]
  rw [outputWord4_outputWordsMem3_eq hmem]
  rw [outputWord5_outputWordsMem4_eq hmem]
  rw [outputWord6_outputWordsMem5_eq hmem]
  rw [outputWord7_outputWordsMem6_eq hmem]
  change
    bytecodeWordChunk (outputWord0 mem) ++
    bytecodeWordChunk (outputWord1 mem) ++
    bytecodeWordChunk (outputWord2 mem) ++
    bytecodeWordChunk (outputWord3 mem) ++
    bytecodeWordChunk (outputWord4 mem) ++
    bytecodeWordChunk (outputWord5 mem) ++
    bytecodeWordChunk (outputWord6 mem) ++
    bytecodeWordChunk (outputWord7 mem) =
      modelWordChunk ((h[0]! ^^^ v[0]! ^^^ v[8]!)) ++
      modelWordChunk ((h[1]! ^^^ v[1]! ^^^ v[9]!)) ++
      modelWordChunk ((h[2]! ^^^ v[2]! ^^^ v[10]!)) ++
      modelWordChunk ((h[3]! ^^^ v[3]! ^^^ v[11]!)) ++
      modelWordChunk ((h[4]! ^^^ v[4]! ^^^ v[12]!)) ++
      modelWordChunk ((h[5]! ^^^ v[5]! ^^^ v[13]!)) ++
      modelWordChunk ((h[6]! ^^^ v[6]! ^^^ v[14]!)) ++
      modelWordChunk ((h[7]! ^^^ v[7]! ^^^ v[15]!))
  rw [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7]
  repeat rw [bytecodeWordChunk_of_u64]

theorem positiveRoundValidTrace :
    ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = runtimeBytecode →
      accepts ctx →
      valid ctx →
      0 < Model.rounds ctx.executionEnv.calldata →
      RDxRet runtimeBytecode ctx.gas ctx.initialState
        (ctx.createdAccounts, ctx.accountMap)
        (output ctx) (positiveRoundGasCost ctx) := by
  apply positiveRoundValidTrace_of_bytecodeOutputBridge
  intro ctx _hcode _haccepts _hvalid _hrounds memFinal hinvFinal
  exact positiveRoundBytecodeOutput_eq_modelOutput ctx hinvFinal

end Blake2f
