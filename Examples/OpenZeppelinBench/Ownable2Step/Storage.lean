import Examples.OpenZeppelinBench.Ownable2Step.Common
import Reasoning.Memory
import Reasoning.Storage
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Ownable2Step

/-!
# Ownable2StepBench storage helpers

The contract has two scalar `address` slots.  The helper below proves the byte-level load/store
round trip for a Solidity `address` stored at offset 0 in a 32-byte EVM storage word.
-/


theorem ownable2StepSetAddressWord_eq (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    ownable2StepSetAddressWord old addr =
      UInt256.ofNat (addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160) := by
  simpa [ownable2StepSetAddressWord, setAddressOffset0Word] using
    setAddressOffset0Word_eq old addr hcanon

theorem ownable2StepSetAddressWord_toNat (old addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    (ownable2StepSetAddressWord old addr).toNat =
      addr.toNat + (old.toNat / 2 ^ 160) * 2 ^ 160 := by
  simpa [ownable2StepSetAddressWord, setAddressOffset0Word] using
    setAddressOffset0Word_toNat old addr hcanon


end OpenZeppelinBench.Ownable2Step
