import Benchmarks.Midnight.CalldataDynamicValues

/-! The four external arguments of Midnight's flash loan. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def flashLoanArguments (tokens assets : List UInt256) (callback : AccountAddress)
    (data : ByteArray) : Store :=
  ((((∅ : Store).insert "tokens" (.array (addressWordArrayValues tokens))).insert
    "assets" (.array (wordArrayValues assets))).insert "callback" (.address callback)).insert
    "data" (.bytes data)

def decodeFlashLoanArguments (bytes : ByteArray) : Option Store := do
  let tokens ← decodeCalldataAddressWords bytes 4
  let assets ← decodeCalldataArrayWords bytes 36
  if (calldataWord bytes 68).toNat < EVM.addressModulus then
    let data ← decodeCalldataBytes bytes 100
    some (flashLoanArguments tokens assets (AccountAddress.ofNat (calldataWord bytes 68).toNat) data)
  else none

theorem midnightDecodeFlashLoan_none_check {bytes : ByteArray}
    (h4 : 4 ≤ bytes.size) (hcheck : solcSLT (solcSub bytes.size 4) 128 = true) :
    config.externalABI.decodeCalldata? ["tokens", "assets", "callback", "data"]
      [.dynamicArray Model.addr, .dynamicArray Model.u256, Model.addr, .bytes] bytes = none := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hhead : abiTupleHeadSize?
      [.dynamicArray Model.addr, .dynamicArray Model.u256, Model.addr, .bytes] = some 128 := by
    simp [abiTupleHeadSize?, Model.addr, staticABIEncodedSize?, isDynamicABIType]
  change Model.decodeCalldata _ _ bytes = _
  simp only [Model.decodeCalldata, decodeCalldataWithMode, decodeCalldata, hl,
    show ¬ bytes.size < 4 from by omega, if_false, Model.calldataMode, List.any_cons,
    List.any_nil, isDynamicABIType, Bool.true_or, decodeArgs?, List.isEmpty_cons,
    Bool.false_eq_true, hhead, bind, Option.bind, hcheck, if_true, ite_self]

theorem decodeSolcFlashLoan {bytes : ByteArray}
    (h132 : 132 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 128 = false) :
    decodeCalldataWithMode Model.calldataMode ["tokens", "assets", "callback", "data"]
      [.dynamicArray Model.addr, .dynamicArray Model.u256, Model.addr, .bytes] bytes =
      decodeFlashLoanArguments bytes := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hhead : abiTupleHeadSize?
      [.dynamicArray Model.addr, .dynamicArray Model.u256, Model.addr, .bytes] = some 128 := by
    simp [abiTupleHeadSize?, Model.addr, staticABIEncodedSize?, isDynamicABIType]
  simp only [decodeCalldataWithMode, decodeCalldata, hl, show ¬ bytes.size < 4 from by omega,
    if_false, Model.calldataMode, List.any_cons, List.any_nil, isDynamicABIType, Bool.true_or,
    decodeArgs?, List.isEmpty_cons, Bool.false_eq_true, hhead, bind, Option.bind, hcheck, ite_self]
  have hbe : (0xac9650d8 == (bytesToWord (bytes.toList.take 4)).toNat) = false :=
    beq_eq_false_iff_ne.mpr hselector
  have hp : ((([(0xac9650d8, [{ materialize := [] }])] : List (Nat × List CalldataPlan)).find?
      (fun entry ↦ entry.1 == (bytesToWord (bytes.toList.take 4)).toNat)).map Prod.snd).getD [] =
      [] := by simp [List.find?, hbe]
  rw [hp, solcDecodeFields_addressArray (cursor := 0) (by omega) hsize]
  simp only [Nat.add_zero]
  rw [solcDecodeFields_u256Array (cursor := 32) (by omega) hsize]
  simp only [Nat.reduceAdd]
  rw [solcDecodeFields_word Model.addr (base := 4) (cursor := 64) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_address]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_bytes (cursor := 96) (by omega) hsize]
  simp only [Nat.reduceAdd]
  unfold decodeFlashLoanArguments
  cases decodeCalldataAddressWords bytes 4 with
  | none => rfl
  | some tokens =>
    cases decodeCalldataArrayWords bytes 36 with
    | none => rfl
    | some assets =>
      by_cases hc : (calldataWord bytes 68).toNat < EVM.addressModulus
      · cases decodeCalldataBytes bytes 100 <;>
          simp only [hc, if_true, decodeFields?] <;> rfl
      · simp only [hc, if_false]
        rfl

theorem midnightDecodeFlashLoan {bytes : ByteArray}
    (h132 : 132 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 128 = false) :
    config.externalABI.decodeCalldata? ["tokens", "assets", "callback", "data"]
      [.dynamicArray Model.addr, .dynamicArray Model.u256, Model.addr, .bytes] bytes =
      decodeFlashLoanArguments bytes := by
  change Model.decodeCalldata _ _ bytes = _
  unfold Model.decodeCalldata
  rw [decodeSolcFlashLoan h132 hsize hselector hcheck]
  unfold decodeFlashLoanArguments
  cases decodeCalldataAddressWords bytes 4 with
  | none => rfl
  | some tokens =>
    cases decodeCalldataArrayWords bytes 36 with
    | none => rfl
    | some assets =>
      by_cases hc : (calldataWord bytes 68).toNat < EVM.addressModulus
      · simp only [hc, if_true]
        cases decodeCalldataBytes bytes 100 with
        | none => rfl
        | some data =>
          simp [flashLoanArguments, Model.inputSizesFit]
      · simp only [hc, if_false]
        rfl

end Benchmarks.Midnight
