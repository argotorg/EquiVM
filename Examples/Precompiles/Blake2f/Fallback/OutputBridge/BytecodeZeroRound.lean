import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ModelZeroRound

/-!
# BLAKE2F zero-round bytecode-output normal forms

This module rewrites the compact bytecode output expression through the eight staged output-word
bridge lemmas.  The remaining difference from the trusted-model normal forms is byte-order/parser
bridging for the symbolic `t0`/`t1` words.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

def bytecodeZeroFlag0Bytes (I : ExecutionEnv) : ByteArray :=
  returnWordBytes (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat 7640891576956012808)) ⟨192⟩) ++
  returnWordBytes (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat 13503953896175478587)) ⟨192⟩) ++
  returnWordBytes (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat 4354685564936845355)) ⟨192⟩) ++
  returnWordBytes (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat 11912009170470909681)) ⟨192⟩) ++
  returnWordBytes (UInt256.shiftLeft
    (evmSwap64 (UInt256.land (v12MixedWord I) ⟨18446744073709551615⟩)) ⟨192⟩) ++
  returnWordBytes (UInt256.shiftLeft
    (evmSwap64 (UInt256.land (v13MixedWord I) ⟨18446744073709551615⟩)) ⟨192⟩) ++
  returnWordBytes (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat 2270897969802886507)) ⟨192⟩) ++
  returnWordBytes (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat 6620516959819538809)) ⟨192⟩)

def bytecodeZeroFlag1Bytes (I : ExecutionEnv) : ByteArray :=
  returnWordBytes (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat 7640891576956012808)) ⟨192⟩) ++
  returnWordBytes (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat 13503953896175478587)) ⟨192⟩) ++
  returnWordBytes (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat 4354685564936845355)) ⟨192⟩) ++
  returnWordBytes (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat 11912009170470909681)) ⟨192⟩) ++
  returnWordBytes (UInt256.shiftLeft
    (evmSwap64 (UInt256.land (v12MixedWord I) ⟨18446744073709551615⟩)) ⟨192⟩) ++
  returnWordBytes (UInt256.shiftLeft
    (evmSwap64 (UInt256.land (v13MixedWord I) ⟨18446744073709551615⟩)) ⟨192⟩) ++
  returnWordBytes (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat 16175846103906665108)) ⟨192⟩) ++
  returnWordBytes (UInt256.shiftLeft (evmSwap64 (UInt256.ofNat 6620516959819538809)) ⟨192⟩)

theorem bytecodeOutputBytes_v13MixedMem_norm
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    bytecodeOutputBytes (v13MixedMem I) = bytecodeZeroFlag0Bytes I := by
  unfold bytecodeOutputBytes bytecodeZeroFlag0Bytes
  unfold outputReturnWord0 outputReturnWord1 outputReturnWord2 outputReturnWord3
    outputReturnWord4 outputReturnWord5 outputReturnWord6 outputReturnWord7
  rw [outputWord0_v13MixedMem I hlen]
  rw [outputWord1_outputWordsMem0_v13MixedMem I hlen]
  rw [outputWord2_outputWordsMem1_v13MixedMem I hlen]
  rw [outputWord3_outputWordsMem2_v13MixedMem I hlen]
  rw [outputWord4_outputWordsMem3_v13MixedMem I hlen]
  rw [outputWord5_outputWordsMem4_v13MixedMem I hlen]
  rw [outputWord6_outputWordsMem5_v13MixedMem I hlen]
  rw [outputWord7_outputWordsMem6_v13MixedMem I hlen]

theorem bytecodeOutputBytes_v14FinalFlagMem_norm
    (I : ExecutionEnv) (hlen : I.calldata.size = 213) :
    bytecodeOutputBytes (v14FinalFlagMem I) = bytecodeZeroFlag1Bytes I := by
  unfold bytecodeOutputBytes bytecodeZeroFlag1Bytes
  unfold outputReturnWord0 outputReturnWord1 outputReturnWord2 outputReturnWord3
    outputReturnWord4 outputReturnWord5 outputReturnWord6 outputReturnWord7
  rw [outputWord0_v14FinalFlagMem I hlen]
  rw [outputWord1_outputWordsMem0_v14FinalFlagMem I hlen]
  rw [outputWord2_outputWordsMem1_v14FinalFlagMem I hlen]
  rw [outputWord3_outputWordsMem2_v14FinalFlagMem I hlen]
  rw [outputWord4_outputWordsMem3_v14FinalFlagMem I hlen]
  rw [outputWord5_outputWordsMem4_v14FinalFlagMem I hlen]
  rw [outputWord6_outputWordsMem5_v14FinalFlagMem I hlen]
  rw [outputWord7_outputWordsMem6_v14FinalFlagMem I hlen]

end Blake2f
