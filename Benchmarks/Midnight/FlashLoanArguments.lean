import Benchmarks.Midnight.FlashLoanDecode
import Benchmarks.Midnight.CalldataArgumentSlice

/-! The decoded flash-loan arguments and the bytecode's calldata references. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def calldataArgumentWords (bytes : ByteArray) (slot : Nat) : List UInt256 :=
  calldataArrayWords bytes (calldataArgumentLength bytes slot).toNat
    (calldataArgumentPointer bytes slot).toNat

def calldataArgumentBytes (bytes : ByteArray) (slot : Nat) : ByteArray :=
  bytes.extract (calldataArgumentPointer bytes slot).toNat
    ((calldataArgumentPointer bytes slot).toNat + (calldataArgumentLength bytes slot).toNat)

theorem decodeFlashLoanArguments_invalid {bytes : ByteArray}
    (hb : (¬ CalldataArgumentValid false bytes 4) ∨
      (¬ CalldataArgumentValid false bytes 36) ∨
      (¬ (calldataWord bytes 68).toNat < EVM.addressModulus) ∨
      (¬ CalldataArgumentValid true bytes 100)) :
    decodeFlashLoanArguments bytes = none := by
  unfold decodeFlashLoanArguments
  rcases hb with ht | ha | hc | hd
  · have hn : decodeCalldataAddressWords bytes 4 = none := by
      unfold decodeCalldataAddressWords
      rw [decodeCalldataArrayWords_invalid ht]
      rfl
    rw [hn]
    rfl
  · rw [decodeCalldataArrayWords_invalid ha]
    cases decodeCalldataAddressWords bytes 4 <;> rfl
  · simp only [hc, if_false]
    cases decodeCalldataAddressWords bytes 4 <;>
      cases decodeCalldataArrayWords bytes 36 <;> rfl
  · rw [decodeCalldataBytes_invalid hd]
    cases decodeCalldataAddressWords bytes 4 <;>
      cases decodeCalldataArrayWords bytes 36 <;>
      simp only [bind, Option.bind, ite_self]

theorem decodeFlashLoanArguments_valid {bytes : ByteArray}
    (ht : CalldataArgumentValid false bytes 4)
    (ha : CalldataArgumentValid false bytes 36)
    (hc : (calldataWord bytes 68).toNat < EVM.addressModulus)
    (hd : CalldataArgumentValid true bytes 100) :
    decodeFlashLoanArguments bytes =
      if CanonicalAddressWords (calldataArgumentWords bytes 4) then
        some (flashLoanArguments (calldataArgumentWords bytes 4)
          (calldataArgumentWords bytes 36)
          (AccountAddress.ofNat (calldataWord bytes 68).toNat) (calldataArgumentBytes bytes 100))
      else none := by
  unfold decodeFlashLoanArguments decodeCalldataAddressWords
  rw [decodeCalldataArrayWords_valid ht, decodeCalldataArrayWords_valid ha,
    decodeCalldataBytes_valid hd]
  by_cases ht' : CanonicalAddressWords (calldataArgumentWords bytes 4)
  · simp only [calldataArgumentWords] at ht'
    simp only [calldataArgumentWords, ht', hc, if_true, bind, Option.bind]
    rfl
  · simp only [calldataArgumentWords] at ht'
    simp only [calldataArgumentWords, ht', if_false, bind, Option.bind]

theorem calldataArgumentWords_length (bytes : ByteArray) (slot : Nat) :
    (calldataArgumentWords bytes slot).length = (calldataArgumentLength bytes slot).toNat :=
  calldataArrayWords_length _ _ _

end Benchmarks.Midnight
