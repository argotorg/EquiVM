import Benchmarks.Midnight.TakeDecode

/-! Failure and success rules for take's complete materialized argument decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem decodeTakeArguments_none_of_invalid {bytes : ByteArray}
    (h : ∀ offer ratifierData data,
      decodeCalldataOffer bytes 4 = some offer →
      decodeCalldataBytes bytes 36 = some ratifierData →
      TakeScalarsValid bytes → decodeCalldataBytes bytes 196 = some data →
      ¬ takeInputSize offer ratifierData data < 2^64) : decodeTakeArguments bytes = none := by
  unfold decodeTakeArguments
  cases ho : decodeCalldataOffer bytes 4 with
  | none => rfl
  | some offer =>
    cases hr : decodeCalldataBytes bytes 36 with
    | none => rfl
    | some ratifierData =>
      dsimp only [bind, Option.bind]
      by_cases hv : TakeScalarsValid bytes
      · rw [if_pos hv]
        cases hd : decodeCalldataBytes bytes 196 with
        | none => rfl
        | some data =>
          dsimp only [bind, Option.bind]
          rw [if_neg (h offer ratifierData data ho hr hv hd)]
      · rw [if_neg hv]

theorem decodeTakeArguments_none_offer {bytes : ByteArray}
    (h : decodeCalldataOffer bytes 4 = none) : decodeTakeArguments bytes = none := by
  apply decodeTakeArguments_none_of_invalid
  intro offer _ _ ho
  rw [h] at ho
  cases ho

theorem decodeTakeArguments_none_ratifier {bytes : ByteArray}
    (h : decodeCalldataBytes bytes 36 = none) : decodeTakeArguments bytes = none := by
  apply decodeTakeArguments_none_of_invalid
  intro _ _ _ _ hr
  rw [h] at hr
  cases hr

theorem decodeTakeArguments_none_scalars {bytes : ByteArray}
    (h : ¬ TakeScalarsValid bytes) : decodeTakeArguments bytes = none := by
  apply decodeTakeArguments_none_of_invalid
  intro _ _ _ _ _ hv
  exact False.elim (h hv)

theorem decodeTakeArguments_none_data {bytes : ByteArray}
    (h : decodeCalldataBytes bytes 196 = none) : decodeTakeArguments bytes = none := by
  apply decodeTakeArguments_none_of_invalid
  intro _ _ _ _ _ _ hd
  rw [h] at hd
  cases hd

theorem decodeTakeArguments_some {bytes ratifierData data : ByteArray} {offer : OfferData}
    (ho : decodeCalldataOffer bytes 4 = some offer)
    (hr : decodeCalldataBytes bytes 36 = some ratifierData) (hv : TakeScalarsValid bytes)
    (hd : decodeCalldataBytes bytes 196 = some data)
    (hfit : takeInputSize offer ratifierData data < 2^64) :
    decodeTakeArguments bytes = some (takeArguments offer ratifierData (calldataWord bytes 68)
      (AccountAddress.ofNat (calldataWord bytes 100).toNat)
      (AccountAddress.ofNat (calldataWord bytes 132).toNat)
      (AccountAddress.ofNat (calldataWord bytes 164).toNat) data) := by
  unfold decodeTakeArguments
  rw [ho]
  dsimp only [bind, Option.bind]
  rw [hr]
  dsimp only [bind, Option.bind]
  rw [if_pos hv, hd]
  dsimp only [bind, Option.bind]
  rw [if_pos hfit]
  rfl

end Benchmarks.Midnight
