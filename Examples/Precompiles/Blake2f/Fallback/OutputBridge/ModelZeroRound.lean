import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ZeroRoundWords

/-!
# BLAKE2F zero-round trusted-model output normal forms

This module normalizes the pure trusted `Model.output` for the zero-round branch.  It is deliberately
separate from the bytecode readback proofs: these facts are only about the pure Lean model copied
from `evm-semantics`.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

def modelZeroFlag0Bytes (input : ByteArray) : ByteArray :=
  ((((((((ByteArray.empty
    |> (fun acc => Model.writeLE64 acc (UInt64.ofNat 7640891576956012808)))
    |> (fun acc => Model.writeLE64 acc (UInt64.ofNat 13503953896175478587)))
    |> (fun acc => Model.writeLE64 acc (UInt64.ofNat 4354685564936845355)))
    |> (fun acc => Model.writeLE64 acc (UInt64.ofNat 11912009170470909681)))
    |> (fun acc => Model.writeLE64 acc ((UInt64.ofNat 5840696475078001361) ^^^
      Model.readLE64 input 196)))
    |> (fun acc => Model.writeLE64 acc ((UInt64.ofNat 11170449401992604703) ^^^
      Model.readLE64 input 204)))
    |> (fun acc => Model.writeLE64 acc (UInt64.ofNat 2270897969802886507)))
    |> (fun acc => Model.writeLE64 acc (UInt64.ofNat 6620516959819538809)))

def modelZeroFlag1Bytes (input : ByteArray) : ByteArray :=
  ((((((((ByteArray.empty
    |> (fun acc => Model.writeLE64 acc (UInt64.ofNat 7640891576956012808)))
    |> (fun acc => Model.writeLE64 acc (UInt64.ofNat 13503953896175478587)))
    |> (fun acc => Model.writeLE64 acc (UInt64.ofNat 4354685564936845355)))
    |> (fun acc => Model.writeLE64 acc (UInt64.ofNat 11912009170470909681)))
    |> (fun acc => Model.writeLE64 acc ((UInt64.ofNat 5840696475078001361) ^^^
      Model.readLE64 input 196)))
    |> (fun acc => Model.writeLE64 acc ((UInt64.ofNat 11170449401992604703) ^^^
      Model.readLE64 input 204)))
    |> (fun acc => Model.writeLE64 acc (UInt64.ofNat 16175846103906665108)))
    |> (fun acc => Model.writeLE64 acc (UInt64.ofNat 6620516959819538809)))

theorem iv6_xor_finalFlag_const :
    ((2270897969802886507 : UInt64) ^^^ (18446744073709551615 : UInt64)) =
      (16175846103906665108 : UInt64) := by
  native_decide

theorem model_output_zero_flag0_norm
    (input : ByteArray) (hrounds : Model.rounds input = 0) (hbyte : input[212]! = 0) :
    Model.output input = modelZeroFlag0Bytes input := by
  rw [modelOutput_eq_compressBytes_zero_of_rounds_zero input hrounds]
  unfold modelZeroFlag0Bytes
  simp [Model.compressBytes, Model.compress, Model.IV, List.range'_succ, hbyte]

theorem model_output_zero_flag1_norm
    (input : ByteArray) (hrounds : Model.rounds input = 0) (hbyte : input[212]! = 1) :
    Model.output input = modelZeroFlag1Bytes input := by
  rw [modelOutput_eq_compressBytes_zero_of_rounds_zero input hrounds]
  unfold modelZeroFlag1Bytes
  simp [Model.compressBytes, Model.compress, Model.IV, List.range'_succ, hbyte,
    iv6_xor_finalFlag_const]

end Blake2f
