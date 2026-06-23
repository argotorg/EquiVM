import Examples.OpenZeppelinBench.ERC6909.Approve
import Examples.OpenZeppelinBench.ERC6909.BalanceOf
import Examples.OpenZeppelinBench.ERC6909.IsOperator
import Examples.OpenZeppelinBench.ERC6909.Storage
import Examples.OpenZeppelinBench.ERC6909.Transfer
import Examples.OpenZeppelinBench.Pausable.Storage
import Reasoning.Refinement
import Reasoning.SolmBody
import Reasoning.SolcDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace OpenZeppelinBench.ERC6909

/-! ## `transferFrom(address,address,uint256,uint256)` body slice

This file keeps the source-side state threading explicit.  In particular, the sender balance is read
after the optional allowance update, matching the spec's assignment order and avoiding any storage
non-collision assumption between the allowance and balance slots.
-/

/-- The raw ABI word for `transferFrom`'s `sender` argument. -/
abbrev transferFromSenderWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

/-- The raw ABI word for `transferFrom`'s `receiver` argument. -/
abbrev transferFromReceiverWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

/-- The raw ABI word for `transferFrom`'s `id` argument. -/
abbrev transferFromIdWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨64⟩ : UInt256).toNat 32)

/-- The raw ABI word for `transferFrom`'s `amount` argument. -/
abbrev transferFromAmountWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨96⟩ : UInt256).toNat 32)

abbrev transferFromSenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferFromSenderWord I).toNat)

abbrev transferFromReceiverValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferFromReceiverWord I).toNat)

abbrev transferFromIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromIdWord I).toNat)

abbrev transferFromAmountValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromAmountWord I).toNat)

def transferFromStore (I : ExecutionEnv) : Store :=
  ((((∅ : Store).insert "sender" (transferFromSenderValue I)).insert "receiver"
    (transferFromReceiverValue I)).insert "id" (transferFromIdValue I)).insert "amount"
    (transferFromAmountValue I)

/-! ### ABI decoding -/

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeScalarWords_address_address_uint256_uint256_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hcanon32 : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat <
      EVM.addressModulus) :
    decodeScalarWords? [addr, addr, uint256, uint256] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat)] := by
  change decodeScalarWords? [.elem .address, .elem .address, abiUInt256, abiUInt256]
      bytes 0 =
    some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
      .address (Ethereum.AccountAddress.ofNat
        (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
      .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
      .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat)]
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_ok (start := 32) hlen32 hcanon32]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_uint256_ok (start := 64) hlen64]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_uint256_ok (start := 96) hlen96]
  rfl

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeScalarWords_address_address_uint256_uint256_none_noncanon0 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc0 : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr, uint256, uint256] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, .elem .address, abiUInt256, abiUInt256]
    bytes 0 = none
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc0)]
  simp only [Option.bind, bind]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeScalarWords_address_address_uint256_uint256_none_noncanon1 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hnc32 : ¬ (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr, uint256, uint256] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, .elem .address, abiUInt256, abiUInt256]
    bytes 0 = none
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_none_noncanon (start := 32) hlen32 hnc32]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeScalarWords_address_address_uint256_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 128) :
    decodeScalarWords? [addr, addr, uint256, uint256] bytes 0 = none := by
  change decodeScalarWords? [.elem .address, .elem .address, abiUInt256, abiUInt256]
    bytes 0 = none
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    rw [decodeScalarWord_address_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    by_cases h64 : bytes.length < 64
    · have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
      · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]
        rw [decodeScalarWord_address_none_short (start := 32) htake32n]
      · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
          (by simpa using hcanon0)]
        simp only [Option.bind, bind]
    · have htake32 : ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      by_cases h96 : bytes.length < 96
      · have htake64n : ¬ ((bytes.drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
        · by_cases hcanon32 :
            (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus
          · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
              (by simpa using hcanon0)]
            simp only [Option.bind, bind]
            rw [decodeScalarWord_address_ok (start := 32) htake32 hcanon32]
            simp only [Option.bind, bind]
            rw [decodeScalarWord_uint256_none_short (start := 64) htake64n]
          · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
              (by simpa using hcanon0)]
            simp only [Option.bind, bind]
            rw [decodeScalarWord_address_none_noncanon (start := 32) htake32 hcanon32]
        · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
            (by simpa using hcanon0)]
          simp only [Option.bind, bind]
      · have htake64 : ((bytes.drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        have htake96n : ¬ ((bytes.drop 96).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        by_cases hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
        · by_cases hcanon32 :
            (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus
          · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
              (by simpa using hcanon0)]
            simp only [Option.bind, bind]
            rw [decodeScalarWord_address_ok (start := 32) htake32 hcanon32]
            simp only [Option.bind, bind]
            rw [decodeScalarWord_uint256_ok (start := 64) htake64]
            simp only [Option.bind, bind]
            rw [decodeScalarWord_uint256_none_short (start := 96) htake96n]
          · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
              (by simpa using hcanon0)]
            simp only [Option.bind, bind]
            rw [decodeScalarWord_address_none_noncanon (start := 32) htake32 hcanon32]
        · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
            (by simpa using hcanon0)]
          simp only [Option.bind, bind]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeCalldata_address_address_uint256_uint256_ok {cd : ByteArray}
    {x y z w : Solm.Ident} (hsz132 : 132 ≤ cd.size)
    (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z, w] [addr, addr, uint256, uint256] cd =
      some (((((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))).insert w
        (.int (Int.ofNat (calldataWord cd 100).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake100 : ((cd.toList.drop 100).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have hword100 : ABI.bytesToWord ((cd.toList.drop 100).take 32) = calldataWord cd 100 :=
    decode_word_at_eq cd 100 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  have htake68' : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68
  have htake100' : ((cd.toList.drop 4).drop 96 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake100
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z, w])
    (types := [addr, addr, uint256, uint256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_uint256_ok (bytes := cd.toList.drop 4)
    htake4 htake36' htake68' htake100'
    (by rw [hword4]; exact hcanon0)
    (by
      rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
          calldataWord cd 36 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hcanon1)]
  change decodeCalldata.insertValues [x, y, z, w]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 96).take 32)).toNat)] ∅ =
    some (((((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat))).insert w
      (.int (Int.ofNat (calldataWord cd 100).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4, hword36, hword68, hword100]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeCalldata_address_address_uint256_uint256_none_noncanon0 {cd : ByteArray}
    {x y z w : Solm.Ident} (hsz132 : 132 ≤ cd.size)
    (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z, w] [addr, addr, uint256, uint256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z, w])
    (types := [addr, addr, uint256, uint256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_uint256_none_noncanon0
    (bytes := cd.toList.drop 4) htake4 (by rw [hword4]; exact hnc0)]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeCalldata_address_address_uint256_uint256_none_noncanon1 {cd : ByteArray}
    {x y z w : Solm.Ident} (hsz132 : 132 ≤ cd.size)
    (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z, w] [addr, addr, uint256, uint256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z, w])
    (types := [addr, addr, uint256, uint256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_uint256_none_noncanon1
    (bytes := cd.toList.drop 4) htake4 htake36'
    (by rw [hword4]; exact hcanon0)
    (by
      rw [show ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
          calldataWord cd 36 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hnc1)]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeCalldata_address_address_uint256_uint256_none_short {cd : ByteArray}
    {x y z w : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 132) :
    decodeCalldata [x, y, z, w] [addr, addr, uint256, uint256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z, w])
    (types := [addr, addr, uint256, uint256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_address_uint256_uint256_none_short
    (bytes := cd.toList.drop 4) (by rw [List.length_drop, htlen]; omega)]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeCalldata_address_address_uint256_uint256_none_huge {cd : ByteArray}
    {x y z w : Solm.Ident} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z, w] [addr, addr, uint256, uint256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z, w])
    (types := [addr, addr, uint256, uint256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

theorem erc6909Decode_transferFrom_ok {I : ExecutionEnv}
    (hsz132 : 132 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (transferFromStore I) := by
  show decodeCalldata ["sender", "receiver", "id", "amount"]
      [addr, addr, uint256, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, transferFromStore, transferFromSenderValue,
    transferFromReceiverValue, transferFromIdValue, transferFromAmountValue,
    transferFromSenderWord, transferFromReceiverWord, transferFromIdWord,
    transferFromAmountWord, calldataWord]
    using decodeCalldata_address_address_uint256_uint256_ok
      (cd := I.calldata) (x := "sender") (y := "receiver") (z := "id") (w := "amount")
      hsz132 hbig hcanonSender hcanonReceiver

theorem erc6909Decode_transferFrom_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 132) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["sender", "receiver", "id", "amount"]
      [addr, addr, uint256, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_address_address_uint256_uint256_none_short
      (cd := I.calldata) (x := "sender") (y := "receiver") (z := "id") (w := "amount")
      hsz4 hshort

theorem erc6909Decode_transferFrom_none_noncanon_sender {I : ExecutionEnv}
    (hsz132 : 132 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (transferFromSenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["sender", "receiver", "id", "amount"]
      [addr, addr, uint256, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, transferFromSenderWord]
    using decodeCalldata_address_address_uint256_uint256_none_noncanon0
      (cd := I.calldata) (x := "sender") (y := "receiver") (z := "id") (w := "amount")
      hsz132 hbig hnc

theorem erc6909Decode_transferFrom_none_noncanon_receiver {I : ExecutionEnv}
    (hsz132 : 132 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (transferFromReceiverWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["sender", "receiver", "id", "amount"]
      [addr, addr, uint256, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, transferFromSenderWord,
    transferFromReceiverWord]
    using decodeCalldata_address_address_uint256_uint256_none_noncanon1
      (cd := I.calldata) (x := "sender") (y := "receiver") (z := "id") (w := "amount")
      hsz132 hbig hcanonSender hnc

theorem erc6909Decode_transferFrom_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["sender", "receiver", "id", "amount"]
      [addr, addr, uint256, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_address_address_uint256_uint256_none_huge
      (cd := I.calldata) (x := "sender") (y := "receiver") (z := "id") (w := "amount")
      hbig

def transferFromOperatorSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  operatorApprovalSlot (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
    (.address evm.executionEnv.source)

def transferFromAllowanceSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
    (.address evm.executionEnv.source) (.int (Int.ofNat (transferFromIdWord I).toNat))

def transferFromInvalidSenderSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨0x01486a41⟩ ⟨231⟩

def transferFromInvalidReceiverSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨0x0b8bbd61⟩ ⟨228⟩

def transferFromSenderBalanceSlot (I : ExecutionEnv) : UInt256 :=
  balanceSlot (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
    (.int (Int.ofNat (transferFromIdWord I).toNat))

def transferFromReceiverBalanceSlot (I : ExecutionEnv) : UInt256 :=
  balanceSlot (.address (AccountAddress.ofNat (transferFromReceiverWord I).toNat))
    (.int (Int.ofNat (transferFromIdWord I).toNat))

theorem transferFromSenderBalanceKeccakSlot (I : ExecutionEnv)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus) :
    transferOuterSlot (transferFromSenderWord I) (transferFromIdWord I) =
      transferFromSenderBalanceSlot I := by
  rw [transferOuterKeccakSlot _ _ hcanonSender]
  rfl

theorem transferFromReceiverBalanceKeccakSlot (I : ExecutionEnv)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus) :
    transferOuterSlot (transferFromReceiverWord I) (transferFromIdWord I) =
      transferFromReceiverBalanceSlot I := by
  rw [transferOuterKeccakSlot _ _ hcanonReceiver]
  rfl

abbrev transferFromCallerWord (I : ExecutionEnv) : UInt256 :=
  approveOwnerWord I

theorem transferFromCallerWord_toNat (I : ExecutionEnv) :
    (transferFromCallerWord I).toNat = I.source.val :=
  approveOwnerWord_toNat I

theorem transferFromCallerWord_canonical (I : ExecutionEnv) :
    (transferFromCallerWord I).toNat < EVM.addressModulus :=
  approveOwnerWord_canonical I

theorem transferFromCaller_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (transferFromCallerWord I).toNat = I.source :=
  approveOwner_ofNat I

def transferFromOperatorSlotI (I : ExecutionEnv) : UInt256 :=
  operatorApprovalSlot (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
    (.address I.source)

def transferFromAllowanceSlotI (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
    (.address I.source) (.int (Int.ofNat (transferFromIdWord I).toNat))

theorem transferFromOperatorKeccakSlot (I : ExecutionEnv)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        ((ffi.KEC ((isOperatorOuterHashMem (transferFromSenderWord I)
          (transferFromCallerWord I)).readWithPadding 0 64)))) =
      transferFromOperatorSlotI I := by
  have hcallerKey : keyValueToWord (.address I.source) = transferFromCallerWord I := by
    rw [← transferFromCaller_ofNat I]
    exact erc6909KeyValueToWord_address_of_canonical _
      (transferFromCallerWord_canonical I)
  have hinner :
      isOperatorInnerSlot (transferFromSenderWord I) =
        mapSlot (transferFromSenderWord I) ⟨1⟩ := by
    unfold isOperatorInnerSlot mapSlot
    rw [isOperatorInnerHashMem_read0_64]
    exact mappingSlot_single (transferFromSenderWord I) ⟨1⟩
  unfold transferFromOperatorSlotI operatorApprovalSlot mapSlot
  rw [isOperatorOuterHashMem_read0_64, hinner,
    erc6909KeyValueToWord_address_of_canonical _ hcanonSender, hcallerKey]
  exact mappingSlot_single (transferFromCallerWord I)
    (mapSlot (transferFromSenderWord I) ⟨1⟩)

theorem transferFromAllowanceKeccakSlot (I : ExecutionEnv)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        ((ffi.KEC ((approveIdHashMem (transferFromSenderWord I)
          (transferFromCallerWord I) (transferFromIdWord I)).readWithPadding 0 64)))) =
      transferFromAllowanceSlotI I := by
  have hcallerKey : keyValueToWord (.address I.source) = transferFromCallerWord I := by
    rw [← transferFromCaller_ofNat I]
    exact erc6909ApproveKeyValueToWord_address_of_canonical _
      (transferFromCallerWord_canonical I)
  have hownerSlot :
      approveOwnerSlot (transferFromSenderWord I) =
        mapSlot (transferFromSenderWord I) ⟨2⟩ := by
    unfold approveOwnerSlot mapSlot
    rw [approveOwnerHashMem_read0_64]
    exact mappingSlot_single (transferFromSenderWord I) ⟨2⟩
  have hspenderSlot :
      approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I) =
        mapSlot (transferFromCallerWord I) (mapSlot (transferFromSenderWord I) ⟨2⟩) := by
    unfold approveSpenderSlot mapSlot
    rw [approveSpenderHashMem_read0_64, hownerSlot]
    exact mappingSlot_single (transferFromCallerWord I)
      (mapSlot (transferFromSenderWord I) ⟨2⟩)
  unfold transferFromAllowanceSlotI allowanceSlot mapSlot
  rw [approveIdHashMem_read0_64, hspenderSlot,
    erc6909ApproveKeyValueToWord_address_of_canonical _ hcanonSender, hcallerKey]
  rw [show keyValueToWord (.int (Int.ofNat (transferFromIdWord I).toNat)) =
      transferFromIdWord I from erc6909WordOfInt_ofNat_toNat (transferFromIdWord I)]
  exact mappingSlot_single (transferFromIdWord I)
    (mapSlot (transferFromCallerWord I) (mapSlot (transferFromSenderWord I) ⟨2⟩))

theorem uint256_lnot_zero_max :
    UInt256.lnot (⟨0⟩ : UInt256) = UInt256.ofNat (UInt256.size - 1) := by
  decide

theorem transferFromOperatorSlot_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    transferFromOperatorSlot (initState cA gh bl σ σ₀ g A I) I =
      transferFromOperatorSlotI I := by
  simp [transferFromOperatorSlot, transferFromOperatorSlotI, initState]

theorem transferFromAllowanceSlot_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    transferFromAllowanceSlot (initState cA gh bl σ σ₀ g A I) I =
      transferFromAllowanceSlotI I := by
  simp [transferFromAllowanceSlot, transferFromAllowanceSlotI, initState]

def transferFromOperatorWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromOperatorSlot evm I))
    ⟨255⟩

abbrev transferFromOperatorValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  wordToElem .bool (transferFromOperatorWord evm I)

def transferFromCurrentAllowanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromAllowanceSlot evm I)

abbrev transferFromCurrentAllowanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromCurrentAllowanceWord evm I).toNat)

@[irreducible] def transferFromStoreCurrentAllowance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferFromStore I).insert "currentAllowance" (transferFromCurrentAllowanceValue evm I)

def transferFromAllowanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((transferFromCurrentAllowanceWord evm I).toNat - (transferFromAmountWord I).toNat)

def transferFromAfterAllowanceState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (transferFromAllowanceSlot evm I)
    (transferFromAllowanceDebitWord evm I)

theorem transferFromAfterAllowance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromAfterAllowanceState evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp only [transferFromAfterAllowanceState, Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? evm.executionEnv.codeOwner with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

def transferFromSenderBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromSenderBalanceSlot I)

abbrev transferFromSenderBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromSenderBalanceWord evm I).toNat)

def transferFromStoreFromBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferFromStoreCurrentAllowance evm I).insert "fromBalance"
    (transferFromSenderBalanceValue (transferFromAfterAllowanceState evm I) I)

def transferFromSenderDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat -
      (transferFromAmountWord I).toNat)

def transferFromAfterSenderBalanceState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferFromAfterAllowanceState evm I) evm.executionEnv.codeOwner
    (transferFromSenderBalanceSlot I) (transferFromSenderDebitWord evm I)

theorem transferFromAfterSenderBalance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromAfterSenderBalanceState evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp only [transferFromAfterSenderBalanceState, Solm.EVM.storageStore, State.lookupAccount]
  cases (transferFromAfterAllowanceState evm I).accountMap.find? evm.executionEnv.codeOwner with
  | none => exact transferFromAfterAllowance_codeOwner evm I
  | some acc =>
      simp only [Option.option, State.setAccount, Account.updateStorage,
        transferFromAfterAllowance_codeOwner]

def transferFromReceiverBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (transferFromAfterSenderBalanceState evm I) evm.executionEnv.codeOwner
    (transferFromReceiverBalanceSlot I)

abbrev transferFromReceiverBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromReceiverBalanceWord evm I).toNat)

def transferFromStoreToBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferFromStoreFromBalance evm I).insert "toBalance" (transferFromReceiverBalanceValue evm I)

def transferFromReceiverCreditNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (transferFromReceiverBalanceWord evm I).toNat + (transferFromAmountWord I).toNat

def transferFromReceiverCreditWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (transferFromReceiverCreditNat evm I)

abbrev transferFromReceiverCreditValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromReceiverCreditNat evm I))

def transferFromPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferFromAfterSenderBalanceState evm I) evm.executionEnv.codeOwner
    (transferFromReceiverBalanceSlot I) (transferFromReceiverCreditWord evm I)

def transferFromTailStoreFromBalance (locals : Store) (evm : EVM.State)
    (I : ExecutionEnv) : Store :=
  locals.insert "fromBalance" (transferFromSenderBalanceValue evm I)

def transferFromTailSenderDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((transferFromSenderBalanceWord evm I).toNat - (transferFromAmountWord I).toNat)

def transferFromTailAfterSenderBalanceState (evm : EVM.State) (I : ExecutionEnv) :
    EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (transferFromSenderBalanceSlot I) (transferFromTailSenderDebitWord evm I)

theorem transferFromTailAfterSenderBalance_codeOwner (evm : EVM.State)
    (I : ExecutionEnv) :
    (transferFromTailAfterSenderBalanceState evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp only [transferFromTailAfterSenderBalanceState, Solm.EVM.storageStore,
    State.lookupAccount]
  cases evm.accountMap.find? evm.executionEnv.codeOwner with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

def transferFromTailReceiverBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (transferFromTailAfterSenderBalanceState evm I)
    evm.executionEnv.codeOwner (transferFromReceiverBalanceSlot I)

abbrev transferFromTailReceiverBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromTailReceiverBalanceWord evm I).toNat)

def transferFromTailStoreToBalance (locals : Store) (evm : EVM.State)
    (I : ExecutionEnv) : Store :=
  (transferFromTailStoreFromBalance locals evm I).insert "toBalance"
    (transferFromTailReceiverBalanceValue evm I)

def transferFromTailReceiverCreditNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (transferFromTailReceiverBalanceWord evm I).toNat + (transferFromAmountWord I).toNat

def transferFromTailReceiverCreditWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (transferFromTailReceiverCreditNat evm I)

abbrev transferFromTailReceiverCreditValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromTailReceiverCreditNat evm I))

def transferFromTailPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferFromTailAfterSenderBalanceState evm I)
    evm.executionEnv.codeOwner (transferFromReceiverBalanceSlot I)
    (transferFromTailReceiverCreditWord evm I)

theorem transferFromReceiverCreditWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromReceiverCreditNat evm I < UInt256.size) :
    (transferFromReceiverCreditWord evm I).toNat = transferFromReceiverCreditNat evm I := by
  unfold transferFromReceiverCreditWord
  exact ulit_toNat' _ hfit

theorem transferFromTailReceiverCreditWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    (transferFromTailReceiverCreditWord evm I).toNat =
      transferFromTailReceiverCreditNat evm I := by
  unfold transferFromTailReceiverCreditWord
  exact ulit_toNat' _ hfit

theorem transferFromStore_sender (I : ExecutionEnv) :
    (transferFromStore I).get? "sender" = some (transferFromSenderValue I) := by
  rw [transferFromStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem transferFromStore_receiver (I : ExecutionEnv) :
    (transferFromStore I).get? "receiver" = some (transferFromReceiverValue I) := by
  rw [transferFromStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem transferFromStore_id (I : ExecutionEnv) :
    (transferFromStore I).get? "id" = some (transferFromIdValue I) := by
  rw [transferFromStore, store_get_ne _ _ (by decide), store_get_self]

theorem transferFromStore_amount (I : ExecutionEnv) :
    (transferFromStore I).get? "amount" = some (transferFromAmountValue I) := by
  rw [transferFromStore, store_get_self]

theorem transferFromStoreCurrentAllowance_currentAllowance (evm : EVM.State)
    (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "currentAllowance" =
      some (transferFromCurrentAllowanceValue evm I) := by
  rw [transferFromStoreCurrentAllowance, store_get_self]

theorem transferFromStoreCurrentAllowance_sender (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "sender" =
      some (transferFromSenderValue I) := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_sender]

theorem transferFromStoreCurrentAllowance_receiver (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "receiver" =
      some (transferFromReceiverValue I) := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_receiver]

theorem transferFromStoreCurrentAllowance_id (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "id" =
      some (transferFromIdValue I) := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_id]

theorem transferFromStoreCurrentAllowance_amount (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreCurrentAllowance evm I).get? "amount" =
      some (transferFromAmountValue I) := by
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_amount]

theorem transferFromStoreFromBalance_fromBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "fromBalance" =
      some (transferFromSenderBalanceValue (transferFromAfterAllowanceState evm I) I) := by
  rw [transferFromStoreFromBalance, store_get_self]

theorem transferFromStoreFromBalance_sender (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "sender" =
      some (transferFromSenderValue I) := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_sender]

theorem transferFromStoreFromBalance_receiver (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "receiver" =
      some (transferFromReceiverValue I) := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_receiver]

theorem transferFromStoreFromBalance_amount (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreFromBalance evm I).get? "amount" =
      some (transferFromAmountValue I) := by
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance_amount]

theorem transferFromStoreToBalance_toBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalance evm I).get? "toBalance" =
      some (transferFromReceiverBalanceValue evm I) := by
  rw [transferFromStoreToBalance, store_get_self]

theorem transferFromStoreToBalance_amount (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalance evm I).get? "amount" =
      some (transferFromAmountValue I) := by
  rw [transferFromStoreToBalance, store_get_ne _ _ (by decide),
    transferFromStoreFromBalance_amount]

theorem transferFromStoreToBalance_receiver (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromStoreToBalance evm I).get? "receiver" =
      some (transferFromReceiverValue I) := by
  rw [transferFromStoreToBalance, store_get_ne _ _ (by decide),
    transferFromStoreFromBalance_receiver]

def transferFromOperatorEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_operatorApprovals",
    steps := [.mindex (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat)),
      .mindex (.address evm.executionEnv.source)] }

def transferFromAllowanceEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_allowances",
    steps := [.mindex (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat)),
      .mindex (.address evm.executionEnv.source),
      .mindex (.int (Int.ofNat (transferFromIdWord I).toNat))] }

def transferFromSenderBalanceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_balances",
    steps := [.mindex (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat)),
      .mindex (.int (Int.ofNat (transferFromIdWord I).toNat))] }

def transferFromReceiverBalanceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_balances",
    steps := [.mindex (.address (AccountAddress.ofNat (transferFromReceiverWord I).toNat)),
      .mindex (.int (Int.ofNat (transferFromIdWord I).toNat))] }

theorem evalExpr_transferFrom_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.var "sender") = .ok (transferFromSenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStore_sender]

theorem evalExpr_transferFrom_id (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.var "id") = .ok (transferFromIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStore_id]

theorem evalExpr_transferFrom_sender_currentAllowance (evm evm' : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (.var "sender") = .ok (transferFromSenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreCurrentAllowance_sender]

theorem evalExpr_transferFrom_id_currentAllowance (evm evm' : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (.var "id") = .ok (transferFromIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_id]

theorem evalExpr_transferFrom_sender_fromBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "sender") = .ok (transferFromSenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance_sender]

theorem evalExpr_transferFrom_receiver_fromBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "receiver") = .ok (transferFromReceiverValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance_receiver]

theorem evalExpr_transferFrom_id_fromBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "id") = .ok (transferFromIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_id]

theorem evalExpr_transferFrom_receiver_toBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreToBalance evm I } evm'
      (.var "receiver") = .ok (transferFromReceiverValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreToBalance_receiver]

theorem evalExpr_transferFrom_id_toBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreToBalance evm I } evm'
      (.var "id") = .ok (transferFromIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreToBalance, store_get_ne _ _ (by decide),
    transferFromStoreFromBalance, store_get_ne _ _ (by decide),
    transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide), transferFromStore_id]

theorem evalExpr_transferFrom_amount_currentAllowance (evm evm' : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (.var "amount") = .ok (transferFromAmountValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreCurrentAllowance_amount]

theorem evalExpr_transferFrom_amount_fromBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I } evm'
      (.var "amount") = .ok (transferFromAmountValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStoreFromBalance_amount]

theorem evalExpr_transferFrom_tail_sender_fromBalance (locals : Store)
    (evm evm' : EVM.State) (I : ExecutionEnv)
    (hget : locals.get? "sender" = some (transferFromSenderValue I)) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I } evm'
      (.var "sender") = .ok (transferFromSenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hget]

theorem evalExpr_transferFrom_tail_receiver_fromBalance (locals : Store)
    (evm evm' : EVM.State) (I : ExecutionEnv)
    (hget : locals.get? "receiver" = some (transferFromReceiverValue I)) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I } evm'
      (.var "receiver") = .ok (transferFromReceiverValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hget]

theorem evalExpr_transferFrom_tail_id_fromBalance (locals : Store)
    (evm evm' : EVM.State) (I : ExecutionEnv)
    (hget : locals.get? "id" = some (transferFromIdValue I)) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I } evm'
      (.var "id") = .ok (transferFromIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hget]

theorem evalExpr_transferFrom_tail_amount_fromBalance (locals : Store)
    (evm evm' : EVM.State) (I : ExecutionEnv)
    (hget : locals.get? "amount" = some (transferFromAmountValue I)) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I } evm'
      (.var "amount") = .ok (transferFromAmountValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hget]

theorem evalExpr_transferFrom_tail_receiver_toBalance (locals : Store)
    (evm evm' : EVM.State) (I : ExecutionEnv)
    (hget : locals.get? "receiver" = some (transferFromReceiverValue I)) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreToBalance locals evm I } evm'
      (.var "receiver") = .ok (transferFromReceiverValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromTailStoreToBalance, store_get_ne _ _ (by decide),
    transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hget]

theorem evalExpr_transferFrom_tail_id_toBalance (locals : Store)
    (evm evm' : EVM.State) (I : ExecutionEnv)
    (hget : locals.get? "id" = some (transferFromIdValue I)) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreToBalance locals evm I } evm'
      (.var "id") = .ok (transferFromIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromTailStoreToBalance, store_get_ne _ _ (by decide),
    transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hget]

theorem evalExpr_transferFrom_tail_amount_toBalance (locals : Store)
    (evm evm' : EVM.State) (I : ExecutionEnv)
    (hget : locals.get? "amount" = some (transferFromAmountValue I)) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreToBalance locals evm I } evm'
      (.var "amount") = .ok (transferFromAmountValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromTailStoreToBalance, store_get_ne _ _ (by decide),
    transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hget]

theorem evalExpr_transferFrom_sender_nonzero_true_of_get (evm : EVM.State)
    (locals : Store) (I : ExecutionEnv)
    (hget : locals.get? "sender" = some (transferFromSenderValue I))
    (hnz : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.var "sender") zeroAddr) = .ok (.bool true) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [hget]
  have hne : ((transferFromSenderValue I : Value) == .address zeroAccountAddress) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    simp only [transferFromSenderValue, Value.address.injEq] at h
    exact hnz h
  simp [evalBinaryOp?, transferFromSenderValue, hne]

theorem evalExpr_transferFrom_sender_nonzero_false_of_get (evm : EVM.State)
    (locals : Store) (I : ExecutionEnv)
    (hget : locals.get? "sender" = some (transferFromSenderValue I))
    (hz : AccountAddress.ofNat (transferFromSenderWord I).toNat = zeroAccountAddress) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.var "sender") zeroAddr) = .ok (.bool false) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [hget]
  simp [evalBinaryOp?, transferFromSenderValue, zeroAccountAddress, hz]

theorem evalExpr_transferFrom_receiver_nonzero_true_of_get (evm : EVM.State)
    (locals : Store) (I : ExecutionEnv)
    (hget : locals.get? "receiver" = some (transferFromReceiverValue I))
    (hnz : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.var "receiver") zeroAddr) = .ok (.bool true) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [hget]
  have hne :
      ((transferFromReceiverValue I : Value) == .address zeroAccountAddress) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    simp only [transferFromReceiverValue, Value.address.injEq] at h
    exact hnz h
  simp [evalBinaryOp?, transferFromReceiverValue, hne]

theorem evalExpr_transferFrom_receiver_nonzero_false_of_get (evm : EVM.State)
    (locals : Store) (I : ExecutionEnv)
    (hget : locals.get? "receiver" = some (transferFromReceiverValue I))
    (hz : AccountAddress.ofNat (transferFromReceiverWord I).toNat = zeroAccountAddress) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.var "receiver") zeroAddr) = .ok (.bool false) := by
  simp only [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  rw [hget]
  simp [evalBinaryOp?, transferFromReceiverValue, zeroAccountAddress, hz]

theorem evalStorageRef_transferFrom_operator (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStore I } evm
      (operatorApprovalRef (.var "sender") sender) =
        .ok (transferFromOperatorEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, operatorApprovalRef, sender, envValue,
    evalExpr_transferFrom_sender, transferFromOperatorEvaledRef, transferFromSenderValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_transferFrom_operator (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.storage (operatorApprovalRef (.var "sender") sender)) =
        .ok (transferFromOperatorValue evm I) := by
  rw [evalExpr_storage_scalar (t := .bool) (loc := boolLoc (transferFromOperatorSlot evm I))
    (hbase := by simp [transferFromStore, operatorApprovalRef])
    (her := evalStorageRef_transferFrom_operator evm I)
    (hty := by
      simp [storageTypeAt?, transferFromOperatorEvaledRef, contract, storageDecls, boolSt,
        storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromOperatorEvaledRef,
      transferFromOperatorSlot])]
  simp [transferFromOperatorValue, transferFromOperatorWord, erc6909StorageLocLoad_bool_offset0]

theorem evalExpr_transferFrom_env_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_transferFrom_sender_ne_env_false (evm : EVM.State) (I : ExecutionEnv)
    (hsource : evm.executionEnv.source = I.source)
    (haddr : AccountAddress.ofNat (transferFromSenderWord I).toNat = I.source) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .ne (.var "sender") sender) = .ok (.bool false) := by
  rw [evalExpr?]
  rw [evalExpr_transferFrom_sender]
  have hcaller :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm sender =
        .ok (.address I.source) := by
    simpa [hsource] using evalExpr_transferFrom_env_sender evm I
  rw [hcaller]
  simp only [EvalResult.bind, bind]
  change evalBinaryOp? .ne (transferFromSenderValue I) (.address I.source) =
    .ok (.bool false)
  simp [evalBinaryOp?, transferFromSenderValue, haddr]

theorem evalExpr_transferFrom_sender_ne_env_true (evm : EVM.State) (I : ExecutionEnv)
    (hsource : evm.executionEnv.source = I.source)
    (hne : ((transferFromSenderValue I : Value) == .address I.source) = false) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .ne (.var "sender") sender) = .ok (.bool true) := by
  rw [evalExpr?]
  rw [evalExpr_transferFrom_sender]
  have hcaller :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm sender =
        .ok (.address I.source) := by
    simpa [hsource] using evalExpr_transferFrom_env_sender evm I
  rw [hcaller]
  simp only [EvalResult.bind, bind]
  simp [evalBinaryOp?, hne]

theorem evalExpr_transferFrom_operator_not_true (evm : EVM.State) (I : ExecutionEnv)
    (hop : transferFromOperatorWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.unary .not (.storage (operatorApprovalRef (.var "sender") sender))) =
        .ok (.bool true) := by
  rw [evalExpr?]
  rw [evalExpr_transferFrom_operator]
  have hval : ((transferFromOperatorWord evm I).val == 0) = true := by
    rw [hop]
    rfl
  simp only [EvalResult.bind, bind, EvalResult.ofOption]
  simp [evalUnaryOp?, transferFromOperatorValue, wordToElem, hval]

theorem evalExpr_transferFrom_operator_not_false (evm : EVM.State) (I : ExecutionEnv)
    (hop : transferFromOperatorWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.unary .not (.storage (operatorApprovalRef (.var "sender") sender))) =
        .ok (.bool false) := by
  rw [evalExpr?]
  rw [evalExpr_transferFrom_operator]
  have hval : ((transferFromOperatorWord evm I).val == 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro hv
    apply hop
    apply u256_inj
    change (transferFromOperatorWord evm I).val.val = 0
    exact congrArg Fin.val hv
  simp only [EvalResult.bind, bind, EvalResult.ofOption]
  simp [evalUnaryOp?, transferFromOperatorValue, wordToElem, hval]

theorem evalExpr_transferFrom_allowance_gate_false_sender (evm : EVM.State)
    (I : ExecutionEnv) (hsource : evm.executionEnv.source = I.source)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .and
        (.binary .ne (.var "sender") sender)
        (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
        .ok (.bool false) := by
  have haddr : AccountAddress.ofNat (transferFromSenderWord I).toNat = I.source := by
    rw [hsenderCaller]
    exact transferFromCaller_ofNat I
  have hleft :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .ne (.var "sender") sender) = .ok (.bool false) := by
    exact evalExpr_transferFrom_sender_ne_env_false evm I hsource haddr
  rw [evalExpr?]
  by_cases hop : transferFromOperatorWord evm I = ⟨0⟩
  · have hright := evalExpr_transferFrom_operator_not_true evm I hop
    rw [hleft, hright]
    simp [EvalResult.bind, bind, pure, evalBinaryOp?]
  · have hright := evalExpr_transferFrom_operator_not_false evm I hop
    rw [hleft, hright]
    simp [EvalResult.bind, bind, pure, evalBinaryOp?]

theorem evalExpr_transferFrom_allowance_gate_true (evm : EVM.State)
    (I : ExecutionEnv) (hsource : evm.executionEnv.source = I.source)
    (hsenderNe : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ I.source)
    (hop : transferFromOperatorWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .and
        (.binary .ne (.var "sender") sender)
        (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
        .ok (.bool true) := by
  have hne : ((transferFromSenderValue I : Value) == .address I.source) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    simp only [transferFromSenderValue, Value.address.injEq] at h
    exact hsenderNe h
  have hleft :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .ne (.var "sender") sender) = .ok (.bool true) := by
    exact evalExpr_transferFrom_sender_ne_env_true evm I hsource hne
  have hright := evalExpr_transferFrom_operator_not_true evm I hop
  rw [evalExpr?]
  rw [hleft, hright]
  simp [EvalResult.bind, bind, pure, evalBinaryOp?]

theorem evalExpr_transferFrom_allowance_gate_false_operator (evm : EVM.State)
    (I : ExecutionEnv) (hsource : evm.executionEnv.source = I.source)
    (hsenderNe : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ I.source)
    (hop : transferFromOperatorWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .and
        (.binary .ne (.var "sender") sender)
        (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
        .ok (.bool false) := by
  have hne : ((transferFromSenderValue I : Value) == .address I.source) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    simp only [transferFromSenderValue, Value.address.injEq] at h
    exact hsenderNe h
  have hleft :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .ne (.var "sender") sender) = .ok (.bool true) := by
    exact evalExpr_transferFrom_sender_ne_env_true evm I hsource hne
  have hright := evalExpr_transferFrom_operator_not_false evm I hop
  rw [evalExpr?]
  rw [hleft, hright]
  simp [EvalResult.bind, bind, pure, evalBinaryOp?]

theorem evalStorageRef_transferFrom_allowance_currentAllowance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (allowanceRef (.var "sender") sender (.var "id")) =
        .ok (transferFromAllowanceEvaledRef evm' I) := by
  simp [evalStorageRef, evalStorageRefStep, allowanceRef, sender, envValue,
    evalExpr_transferFrom_sender_currentAllowance, evalExpr_transferFrom_id_currentAllowance,
    transferFromAllowanceEvaledRef, transferFromSenderValue, transferFromIdValue, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalStorageRef_transferFrom_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStore I } evm
      (allowanceRef (.var "sender") sender (.var "id")) =
        .ok (transferFromAllowanceEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, allowanceRef, sender, envValue,
    evalExpr_transferFrom_sender, evalExpr_transferFrom_id, transferFromAllowanceEvaledRef,
    transferFromSenderValue, transferFromIdValue, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_transferFrom_currentAllowance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.storage (allowanceRef (.var "sender") sender (.var "id"))) =
        .ok (transferFromCurrentAllowanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferFromAllowanceSlot evm I))
    (hbase := by simp [allowanceRef, transferFromStore])
    (her := evalStorageRef_transferFrom_allowance evm I)
    (hty := by
      simp [storageTypeAt?, transferFromAllowanceEvaledRef, contract, storageDecls, uint256St,
        storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromAllowanceEvaledRef,
      transferFromAllowanceSlot])]
  simp [transferFromCurrentAllowanceValue, transferFromCurrentAllowanceWord,
    erc6909StorageLocLoad_uint256]

theorem transferFromAssignAllowance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      .storage (allowanceRef (.var "sender") sender (.var "id"))
      (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromStoreCurrentAllowance evm I },
          transferFromAfterAllowanceState evm I) := by
  simp only [allowanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferFromAllowanceSlot evm I))
      (hbase := by simp [allowanceRef, transferFromStoreCurrentAllowance, transferFromStore])
      (her := evalStorageRef_transferFrom_allowance_currentAllowance evm evm I)
      (hty := by
        simp [storageTypeAt?, transferFromAllowanceEvaledRef, contract, storageDecls, uint256St,
          storageTypeStep?])
      (hloc := by
        simp [config, storageLayout, transferFromAllowanceEvaledRef, transferFromAllowanceSlot])
  rw [erc6909StorageLocStore_uint256]
  simp [transferFromAfterAllowanceState, transferFromAllowanceSlot]

theorem evalExpr_transferFrom_allowance_ge_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .ge (.var "currentAllowance") (.var "amount")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreCurrentAllowance_currentAllowance,
    transferFromStoreCurrentAllowance_amount]
  simp [evalBinaryOp?]
  exact henough

theorem evalExpr_transferFrom_allowance_ge_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromCurrentAllowanceWord evm I).toNat <
      (transferFromAmountWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .ge (.var "currentAllowance") (.var "amount")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreCurrentAllowance_currentAllowance,
    transferFromStoreCurrentAllowance_amount]
  simp [evalBinaryOp?]
  omega

theorem evalExpr_transferFrom_allowance_lt_max_true (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromCurrentAllowanceWord evm I).toNat < UInt256.size - 1) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool true) := by
  have hlt' : (transferFromCurrentAllowanceWord evm I).toNat < 2 ^ 256 - 1 := by
    simpa [UInt256.size] using hlt
  simp only [maxUint256Lit, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreCurrentAllowance_currentAllowance]
  simp [evalBinaryOp?, transferFromCurrentAllowanceValue, maxUint256, UInt256.size]
  omega

theorem evalExpr_transferFrom_allowance_lt_max_false (evm : EVM.State) (I : ExecutionEnv)
    (hge : UInt256.size - 1 ≤ (transferFromCurrentAllowanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool false) := by
  have hge' : 2 ^ 256 - 1 ≤ (transferFromCurrentAllowanceWord evm I).toNat := by
    simpa [UInt256.size] using hge
  simp only [maxUint256Lit, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreCurrentAllowance_currentAllowance]
  simp [evalBinaryOp?, transferFromCurrentAllowanceValue, maxUint256, UInt256.size]
  omega

theorem evalExpr_transferFrom_allowance_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .sub (.var "currentAllowance") (.var "amount")) =
        .ok (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromCurrentAllowanceWord evm I).toNat -
          Int.ofNat (transferFromAmountWord I).toNat =
        Int.ofNat
          ((transferFromCurrentAllowanceWord evm I).toNat - (transferFromAmountWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromAllowanceDebitWord evm I).toNat =
      (transferFromCurrentAllowanceWord evm I).toNat - (transferFromAmountWord I).toNat := by
    unfold transferFromAllowanceDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le (transferFromCurrentAllowanceWord evm I).toNat (transferFromAmountWord I).toNat)
      (transferFromCurrentAllowanceWord evm I).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreCurrentAllowance_currentAllowance,
    transferFromStoreCurrentAllowance_amount]
  simp [evalBinaryOp?, htoNat]
  exact hsub

theorem evalStorageRef_transferFrom_sender_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromStoreFromBalance evm I } evm'
      (balanceRef (.var "sender") (.var "id")) =
        .ok (transferFromSenderBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef, evalExpr_transferFrom_sender_fromBalance,
    evalExpr_transferFrom_id_fromBalance,
    transferFromSenderBalanceEvaledRef, transferFromSenderValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem transferFromAssignSenderBalance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config
      { contract := contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterAllowanceState evm I) .storage (balanceRef (.var "sender") (.var "id"))
      (.int (Int.ofNat (transferFromSenderDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromStoreFromBalance evm I },
          transferFromAfterSenderBalanceState evm I) := by
  simp only [balanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferFromSenderBalanceSlot I))
      (hbase := by simp [balanceRef, transferFromStoreFromBalance, transferFromStoreCurrentAllowance,
        transferFromStore])
      (her := evalStorageRef_transferFrom_sender_balance_fromBalance evm
        (transferFromAfterAllowanceState evm I) I)
      (hty := by
        simp [storageTypeAt?, transferFromSenderBalanceEvaledRef, contract, storageDecls,
          uint256St, storageTypeStep?])
      (hloc := by simp [config, storageLayout, transferFromSenderBalanceEvaledRef,
        transferFromSenderBalanceSlot])
  rw [erc6909StorageLocStore_uint256]
  simp [transferFromAfterSenderBalanceState, transferFromSenderBalanceSlot,
    transferFromAfterAllowance_codeOwner]

theorem evalStorageRef_transferFrom_sender_balance_currentAllowance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm'
      (balanceRef (.var "sender") (.var "id")) =
        .ok (transferFromSenderBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef,
    evalExpr_transferFrom_sender_currentAllowance, evalExpr_transferFrom_id_currentAllowance,
    transferFromSenderBalanceEvaledRef, transferFromSenderValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_transferFrom_sender_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
      (transferFromAfterAllowanceState evm I) (.storage (balanceRef (.var "sender") (.var "id"))) =
        .ok (transferFromSenderBalanceValue (transferFromAfterAllowanceState evm I) I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferFromSenderBalanceSlot I))
    (hbase := by simp [balanceRef, transferFromStoreCurrentAllowance, transferFromStore])
    (her := evalStorageRef_transferFrom_sender_balance_currentAllowance evm
      (transferFromAfterAllowanceState evm I) I)
    (hty := by
      simp [storageTypeAt?, transferFromSenderBalanceEvaledRef, contract, storageDecls, uint256St,
        storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromSenderBalanceEvaledRef,
      transferFromSenderBalanceSlot])]
  simp [transferFromSenderBalanceValue, transferFromSenderBalanceWord,
    erc6909StorageLocLoad_uint256, transferFromAfterAllowance_codeOwner]

theorem evalExpr_transferFrom_sender_balance_ge_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterAllowanceState evm I)
      (.binary .ge (.var "fromBalance") (.var "amount")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreFromBalance_fromBalance, transferFromStoreFromBalance_amount]
  simp [evalBinaryOp?]
  exact henough

theorem evalExpr_transferFrom_sender_balance_ge_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat <
      (transferFromAmountWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterAllowanceState evm I)
      (.binary .ge (.var "fromBalance") (.var "amount")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreFromBalance_fromBalance, transferFromStoreFromBalance_amount]
  simp [evalBinaryOp?]
  omega

theorem evalExpr_transferFrom_sender_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterAllowanceState evm I)
      (.binary .sub (.var "fromBalance") (.var "amount")) =
        .ok (.int (Int.ofNat (transferFromSenderDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat -
          Int.ofNat (transferFromAmountWord I).toNat =
        Int.ofNat
          ((transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat -
            (transferFromAmountWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromSenderDebitWord evm I).toNat =
      (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat -
        (transferFromAmountWord I).toNat := by
    unfold transferFromSenderDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le
        (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat
        (transferFromAmountWord I).toNat)
      (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferFromStoreFromBalance_fromBalance, transferFromStoreFromBalance_amount]
  simp [evalBinaryOp?, htoNat]
  exact hsub

theorem evalStorageRef_transferFrom_receiver_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromStoreFromBalance evm I } evm'
      (balanceRef (.var "receiver") (.var "id")) =
        .ok (transferFromReceiverBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef, evalExpr_transferFrom_receiver_fromBalance,
    evalExpr_transferFrom_id_fromBalance, transferFromReceiverBalanceEvaledRef,
    transferFromReceiverValue, transferFromIdValue, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure]

theorem evalExpr_transferFrom_receiver_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreFromBalance evm I }
      (transferFromAfterSenderBalanceState evm I)
      (.storage (balanceRef (.var "receiver") (.var "id"))) =
        .ok (transferFromReceiverBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferFromReceiverBalanceSlot I))
    (hbase := by simp [balanceRef, transferFromStoreFromBalance, transferFromStoreCurrentAllowance,
      transferFromStore])
    (her := evalStorageRef_transferFrom_receiver_balance_fromBalance evm
      (transferFromAfterSenderBalanceState evm I) I)
    (hty := by
      simp [storageTypeAt?, transferFromReceiverBalanceEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromReceiverBalanceEvaledRef,
      transferFromReceiverBalanceSlot])]
  simp [transferFromReceiverBalanceValue, transferFromReceiverBalanceWord,
    erc6909StorageLocLoad_uint256, transferFromAfterSenderBalance_codeOwner]

theorem evalExpr_transferFrom_receiver_credit (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromReceiverCreditNat evm I < UInt256.size) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreToBalance evm I }
      (transferFromAfterSenderBalanceState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))) =
        .ok (transferFromReceiverCreditValue evm I) := by
  have hlt : ¬ Int.ofNat (transferFromReceiverCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreToBalance_toBalance, transferFromStoreToBalance_amount]
  simp [evalBinaryOp?, transferFromReceiverCreditValue, transferFromReceiverCreditNat, uint256Int]
  constructor
  · omega
  · have hfitNat :
        (transferFromReceiverBalanceWord evm I).toNat + (transferFromAmountWord I).toNat <
          2 ^ 256 := by
      simpa [transferFromReceiverCreditNat, UInt256.size] using hfit
    omega

theorem evalExpr_transferFrom_receiver_credit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ transferFromReceiverCreditNat evm I) :
    evalExpr? config
      { contract := contract, locals := transferFromStoreToBalance evm I }
      (transferFromAfterSenderBalanceState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))) = .revert := by
  have hge : Int.ofNat (transferFromReceiverCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferFromStoreToBalance_toBalance, transferFromStoreToBalance_amount]
  simp [evalBinaryOp?, transferFromReceiverBalanceValue, transferFromAmountValue,
    transferFromReceiverCreditValue, transferFromReceiverCreditNat, uint256Int]
  intro _
  simpa [transferFromReceiverCreditNat] using hge

theorem evalStorageRef_transferFrom_receiver_balance_toBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromStoreToBalance evm I } evm'
      (balanceRef (.var "receiver") (.var "id")) =
        .ok (transferFromReceiverBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef, evalExpr_transferFrom_receiver_toBalance,
    evalExpr_transferFrom_id_toBalance, transferFromReceiverBalanceEvaledRef,
    transferFromReceiverValue, transferFromIdValue, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure]

theorem transferFromAssignReceiverBalance (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromReceiverCreditNat evm I < UInt256.size) :
    assignStorageRef? config
      { contract := contract, locals := transferFromStoreToBalance evm I }
      (transferFromAfterSenderBalanceState evm I) .storage
      (balanceRef (.var "receiver") (.var "id")) (transferFromReceiverCreditValue evm I) =
        .ok ({ contract := contract, locals := transferFromStoreToBalance evm I },
          transferFromPostState evm I) := by
  simp only [balanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferFromReceiverBalanceSlot I))
      (hbase := by simp [balanceRef, transferFromStoreToBalance, transferFromStoreFromBalance,
        transferFromStoreCurrentAllowance, transferFromStore])
      (her := evalStorageRef_transferFrom_receiver_balance_toBalance evm
        (transferFromAfterSenderBalanceState evm I) I)
      (hty := by
        simp [storageTypeAt?, transferFromReceiverBalanceEvaledRef, contract, storageDecls,
          uint256St, storageTypeStep?])
      (hloc := by simp [config, storageLayout, transferFromReceiverBalanceEvaledRef,
        transferFromReceiverBalanceSlot])
  rw [← transferFromReceiverCreditWord_toNat evm I hfit]
  rw [erc6909StorageLocStore_uint256]
  simp [transferFromPostState, transferFromReceiverBalanceSlot,
    transferFromAfterSenderBalance_codeOwner]

theorem evalStorageRef_transferFrom_tail_sender_balance (evm evm' : EVM.State)
    (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStore I } evm'
      (balanceRef (.var "sender") (.var "id")) =
        .ok (transferFromSenderBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef, evalExpr_transferFrom_sender,
    evalExpr_transferFrom_id, transferFromSenderBalanceEvaledRef, transferFromSenderValue,
    transferFromIdValue, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_transferFrom_tail_sender_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.storage (balanceRef (.var "sender") (.var "id"))) =
        .ok (transferFromSenderBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferFromSenderBalanceSlot I))
    (hbase := by simp [balanceRef, transferFromStore])
    (her := evalStorageRef_transferFrom_tail_sender_balance evm evm I)
    (hty := by
      simp [storageTypeAt?, transferFromSenderBalanceEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromSenderBalanceEvaledRef,
      transferFromSenderBalanceSlot])]
  simp [transferFromSenderBalanceValue, transferFromSenderBalanceWord,
    erc6909StorageLocLoad_uint256]

theorem evalStorageRef_transferFrom_tail_sender_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I }
      evm' (balanceRef (.var "sender") (.var "id")) =
        .ok (transferFromSenderBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef,
    evalExpr_transferFrom_tail_sender_fromBalance (transferFromStore I) evm evm' I
      (transferFromStore_sender I),
    evalExpr_transferFrom_tail_id_fromBalance (transferFromStore I) evm evm' I
      (transferFromStore_id I),
    transferFromSenderBalanceEvaledRef, transferFromSenderValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalStorageRef_transferFrom_tail_sender_balance_fromBalance_of_get
    (locals : Store) (evm evm' : EVM.State) (I : ExecutionEnv)
    (hsender : locals.get? "sender" = some (transferFromSenderValue I))
    (hid : locals.get? "id" = some (transferFromIdValue I)) :
    evalStorageRef config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I }
      evm' (balanceRef (.var "sender") (.var "id")) =
        .ok (transferFromSenderBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef,
    evalExpr_transferFrom_tail_sender_fromBalance locals evm evm' I hsender,
    evalExpr_transferFrom_tail_id_fromBalance locals evm evm' I hid,
    transferFromSenderBalanceEvaledRef, transferFromSenderValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem transferFromTailAssignSenderBalance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config
      { contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I }
      evm .storage (balanceRef (.var "sender") (.var "id"))
      (.int (Int.ofNat (transferFromTailSenderDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I },
          transferFromTailAfterSenderBalanceState evm I) := by
  simp only [balanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferFromSenderBalanceSlot I))
      (hbase := by simp [balanceRef, transferFromTailStoreFromBalance, transferFromStore])
      (her := evalStorageRef_transferFrom_tail_sender_balance_fromBalance evm evm I)
      (hty := by
        simp [storageTypeAt?, transferFromSenderBalanceEvaledRef, contract, storageDecls,
          uint256St, storageTypeStep?])
      (hloc := by simp [config, storageLayout, transferFromSenderBalanceEvaledRef,
        transferFromSenderBalanceSlot])
  rw [erc6909StorageLocStore_uint256]
  simp [transferFromTailAfterSenderBalanceState, transferFromSenderBalanceSlot]

theorem transferFromTailAssignSenderBalance_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hsender : locals.get? "sender" = some (transferFromSenderValue I))
    (hid : locals.get? "id" = some (transferFromIdValue I))
    (hbase : "_balances" ∉ locals) :
    assignStorageRef? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I }
      evm .storage (balanceRef (.var "sender") (.var "id"))
      (.int (Int.ofNat (transferFromTailSenderDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromTailStoreFromBalance locals evm I },
          transferFromTailAfterSenderBalanceState evm I) := by
  simp only [balanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferFromSenderBalanceSlot I))
      (hbase := by simp [balanceRef, transferFromTailStoreFromBalance, hbase])
      (her := evalStorageRef_transferFrom_tail_sender_balance_fromBalance_of_get
        locals evm evm I hsender hid)
      (hty := by
        simp [storageTypeAt?, transferFromSenderBalanceEvaledRef, contract, storageDecls,
          uint256St, storageTypeStep?])
      (hloc := by simp [config, storageLayout, transferFromSenderBalanceEvaledRef,
        transferFromSenderBalanceSlot])
  rw [erc6909StorageLocStore_uint256]
  simp [transferFromTailAfterSenderBalanceState, transferFromSenderBalanceSlot]

theorem evalExpr_transferFrom_tail_sender_balance_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hsender : locals.get? "sender" = some (transferFromSenderValue I))
    (hid : locals.get? "id" = some (transferFromIdValue I))
    (hbase : "_balances" ∉ locals) :
    evalExpr? config
      { contract := contract, locals := locals } evm
      (.storage (balanceRef (.var "sender") (.var "id"))) =
        .ok (transferFromSenderBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferFromSenderBalanceSlot I))
    (hbase := by simp [balanceRef, hbase])
    (her := by
      change evalStorageRef config { contract := contract, locals := locals } evm
        (balanceRef (.var "sender") (.var "id")) =
          .ok (transferFromSenderBalanceEvaledRef I)
      simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, balanceRef, evalExpr?,
        EvalResult.bind, EvalResult.ofOption, bind, pure]
      rw [hsender, hid]
      simp [transferFromSenderBalanceEvaledRef, transferFromSenderValue, transferFromIdValue,
        valueToKey?])
    (hty := by
      simp [storageTypeAt?, transferFromSenderBalanceEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromSenderBalanceEvaledRef,
      transferFromSenderBalanceSlot])]
  simp [transferFromSenderBalanceValue, transferFromSenderBalanceWord,
    erc6909StorageLocLoad_uint256]

theorem evalExpr_transferFrom_tail_sender_balance_ge_true (evm : EVM.State)
    (I : ExecutionEnv)
    (henough : (transferFromAmountWord I).toNat ≤ (transferFromSenderBalanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I }
      evm (.binary .ge (.var "fromBalance") (.var "amount")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [show (transferFromTailStoreFromBalance (transferFromStore I) evm I).get?
        "fromBalance" = some (transferFromSenderBalanceValue evm I) by
      rw [transferFromTailStoreFromBalance, store_get_self]]
  rw [show (transferFromTailStoreFromBalance (transferFromStore I) evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide),
        transferFromStore_amount]]
  simp [evalBinaryOp?]
  exact henough

theorem evalExpr_transferFrom_tail_sender_balance_ge_true_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hamount : locals.get? "amount" = some (transferFromAmountValue I))
    (henough : (transferFromAmountWord I).toNat ≤ (transferFromSenderBalanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I }
      evm (.binary .ge (.var "fromBalance") (.var "amount")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [show (transferFromTailStoreFromBalance locals evm I).get?
        "fromBalance" = some (transferFromSenderBalanceValue evm I) by
      rw [transferFromTailStoreFromBalance, store_get_self]]
  rw [show (transferFromTailStoreFromBalance locals evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hamount]]
  simp [evalBinaryOp?]
  exact henough

theorem evalExpr_transferFrom_tail_sender_balance_ge_false (evm : EVM.State)
    (I : ExecutionEnv)
    (hlt : (transferFromSenderBalanceWord evm I).toNat < (transferFromAmountWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I }
      evm (.binary .ge (.var "fromBalance") (.var "amount")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [show (transferFromTailStoreFromBalance (transferFromStore I) evm I).get?
        "fromBalance" = some (transferFromSenderBalanceValue evm I) by
      rw [transferFromTailStoreFromBalance, store_get_self]]
  rw [show (transferFromTailStoreFromBalance (transferFromStore I) evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide),
        transferFromStore_amount]]
  simp [evalBinaryOp?]
  omega

theorem evalExpr_transferFrom_tail_sender_balance_ge_false_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hamount : locals.get? "amount" = some (transferFromAmountValue I))
    (hlt : (transferFromSenderBalanceWord evm I).toNat < (transferFromAmountWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I }
      evm (.binary .ge (.var "fromBalance") (.var "amount")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [show (transferFromTailStoreFromBalance locals evm I).get?
        "fromBalance" = some (transferFromSenderBalanceValue evm I) by
      rw [transferFromTailStoreFromBalance, store_get_self]]
  rw [show (transferFromTailStoreFromBalance locals evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hamount]]
  simp [evalBinaryOp?]
  omega

theorem evalExpr_transferFrom_tail_sender_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromAmountWord I).toNat ≤ (transferFromSenderBalanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I }
      evm (.binary .sub (.var "fromBalance") (.var "amount")) =
        .ok (.int (Int.ofNat (transferFromTailSenderDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromSenderBalanceWord evm I).toNat -
          Int.ofNat (transferFromAmountWord I).toNat =
        Int.ofNat ((transferFromSenderBalanceWord evm I).toNat -
          (transferFromAmountWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromTailSenderDebitWord evm I).toNat =
      (transferFromSenderBalanceWord evm I).toNat - (transferFromAmountWord I).toNat := by
    unfold transferFromTailSenderDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le (transferFromSenderBalanceWord evm I).toNat (transferFromAmountWord I).toNat)
      (transferFromSenderBalanceWord evm I).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [show (transferFromTailStoreFromBalance (transferFromStore I) evm I).get?
        "fromBalance" = some (transferFromSenderBalanceValue evm I) by
      rw [transferFromTailStoreFromBalance, store_get_self]]
  rw [show (transferFromTailStoreFromBalance (transferFromStore I) evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide),
        transferFromStore_amount]]
  simp [evalBinaryOp?, htoNat]
  exact hsub

theorem evalExpr_transferFrom_tail_sender_debit_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hamount : locals.get? "amount" = some (transferFromAmountValue I))
    (henough : (transferFromAmountWord I).toNat ≤ (transferFromSenderBalanceWord evm I).toNat) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I }
      evm (.binary .sub (.var "fromBalance") (.var "amount")) =
        .ok (.int (Int.ofNat (transferFromTailSenderDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromSenderBalanceWord evm I).toNat -
          Int.ofNat (transferFromAmountWord I).toNat =
        Int.ofNat ((transferFromSenderBalanceWord evm I).toNat -
          (transferFromAmountWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromTailSenderDebitWord evm I).toNat =
      (transferFromSenderBalanceWord evm I).toNat - (transferFromAmountWord I).toNat := by
    unfold transferFromTailSenderDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le (transferFromSenderBalanceWord evm I).toNat (transferFromAmountWord I).toNat)
      (transferFromSenderBalanceWord evm I).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [show (transferFromTailStoreFromBalance locals evm I).get?
        "fromBalance" = some (transferFromSenderBalanceValue evm I) by
      rw [transferFromTailStoreFromBalance, store_get_self]]
  rw [show (transferFromTailStoreFromBalance locals evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hamount]]
  simp [evalBinaryOp?, htoNat]
  exact hsub

theorem evalStorageRef_transferFrom_tail_receiver_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I }
      evm' (balanceRef (.var "receiver") (.var "id")) =
        .ok (transferFromReceiverBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef,
    evalExpr_transferFrom_tail_receiver_fromBalance (transferFromStore I) evm evm' I
      (transferFromStore_receiver I),
    evalExpr_transferFrom_tail_id_fromBalance (transferFromStore I) evm evm' I
      (transferFromStore_id I),
    transferFromReceiverBalanceEvaledRef, transferFromReceiverValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalStorageRef_transferFrom_tail_receiver_balance_fromBalance_of_get
    (locals : Store) (evm evm' : EVM.State) (I : ExecutionEnv)
    (hreceiver : locals.get? "receiver" = some (transferFromReceiverValue I))
    (hid : locals.get? "id" = some (transferFromIdValue I)) :
    evalStorageRef config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I }
      evm' (balanceRef (.var "receiver") (.var "id")) =
        .ok (transferFromReceiverBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef,
    evalExpr_transferFrom_tail_receiver_fromBalance locals evm evm' I hreceiver,
    evalExpr_transferFrom_tail_id_fromBalance locals evm evm' I hid,
    transferFromReceiverBalanceEvaledRef, transferFromReceiverValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_transferFrom_tail_receiver_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance (transferFromStore I) evm I }
      (transferFromTailAfterSenderBalanceState evm I)
      (.storage (balanceRef (.var "receiver") (.var "id"))) =
        .ok (transferFromTailReceiverBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferFromReceiverBalanceSlot I))
    (hbase := by simp [balanceRef, transferFromTailStoreFromBalance, transferFromStore])
    (her := evalStorageRef_transferFrom_tail_receiver_balance_fromBalance evm
      (transferFromTailAfterSenderBalanceState evm I) I)
    (hty := by
      simp [storageTypeAt?, transferFromReceiverBalanceEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromReceiverBalanceEvaledRef,
      transferFromReceiverBalanceSlot])]
  simp [transferFromTailReceiverBalanceValue, transferFromTailReceiverBalanceWord,
    erc6909StorageLocLoad_uint256, transferFromTailAfterSenderBalance_codeOwner]

theorem evalExpr_transferFrom_tail_receiver_balance_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hreceiver : locals.get? "receiver" = some (transferFromReceiverValue I))
    (hid : locals.get? "id" = some (transferFromIdValue I))
    (hbase : "_balances" ∉ locals) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreFromBalance locals evm I }
      (transferFromTailAfterSenderBalanceState evm I)
      (.storage (balanceRef (.var "receiver") (.var "id"))) =
        .ok (transferFromTailReceiverBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (loc := wordLoc (transferFromReceiverBalanceSlot I))
    (hbase := by simp [balanceRef, transferFromTailStoreFromBalance, hbase])
    (her := evalStorageRef_transferFrom_tail_receiver_balance_fromBalance_of_get locals evm
      (transferFromTailAfterSenderBalanceState evm I) I hreceiver hid)
    (hty := by
      simp [storageTypeAt?, transferFromReceiverBalanceEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
    (hloc := by simp [config, storageLayout, transferFromReceiverBalanceEvaledRef,
      transferFromReceiverBalanceSlot])]
  simp [transferFromTailReceiverBalanceValue, transferFromTailReceiverBalanceWord,
    erc6909StorageLocLoad_uint256, transferFromTailAfterSenderBalance_codeOwner]

theorem evalExpr_transferFrom_tail_receiver_credit (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreToBalance (transferFromStore I) evm I }
      (transferFromTailAfterSenderBalanceState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))) =
        .ok (transferFromTailReceiverCreditValue evm I) := by
  have hlt : ¬ Int.ofNat (transferFromTailReceiverCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [show (transferFromTailStoreToBalance (transferFromStore I) evm I).get?
        "toBalance" = some (transferFromTailReceiverBalanceValue evm I) by
      rw [transferFromTailStoreToBalance, store_get_self]]
  rw [show (transferFromTailStoreToBalance (transferFromStore I) evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreToBalance, store_get_ne _ _ (by decide),
        transferFromTailStoreFromBalance, store_get_ne _ _ (by decide),
        transferFromStore_amount]]
  simp [evalBinaryOp?, transferFromTailReceiverCreditValue,
    transferFromTailReceiverCreditNat, uint256Int]
  constructor
  · omega
  · have hfitNat :
        (transferFromTailReceiverBalanceWord evm I).toNat +
            (transferFromAmountWord I).toNat < 2 ^ 256 := by
      simpa [transferFromTailReceiverCreditNat, UInt256.size] using hfit
    omega

theorem evalExpr_transferFrom_tail_receiver_credit_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hamount : locals.get? "amount" = some (transferFromAmountValue I))
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreToBalance locals evm I }
      (transferFromTailAfterSenderBalanceState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))) =
        .ok (transferFromTailReceiverCreditValue evm I) := by
  have hlt : ¬ Int.ofNat (transferFromTailReceiverCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [show (transferFromTailStoreToBalance locals evm I).get?
        "toBalance" = some (transferFromTailReceiverBalanceValue evm I) by
      rw [transferFromTailStoreToBalance, store_get_self]]
  rw [show (transferFromTailStoreToBalance locals evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreToBalance, store_get_ne _ _ (by decide),
        transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hamount]]
  simp [evalBinaryOp?, transferFromTailReceiverCreditValue,
    transferFromTailReceiverCreditNat, uint256Int]
  constructor
  · omega
  · have hfitNat :
        (transferFromTailReceiverBalanceWord evm I).toNat +
            (transferFromAmountWord I).toNat < 2 ^ 256 := by
      simpa [transferFromTailReceiverCreditNat, UInt256.size] using hfit
    omega

theorem evalExpr_transferFrom_tail_receiver_credit_revert (evm : EVM.State)
    (I : ExecutionEnv) (hover : UInt256.size ≤ transferFromTailReceiverCreditNat evm I) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreToBalance (transferFromStore I) evm I }
      (transferFromTailAfterSenderBalanceState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))) = .revert := by
  have hge : Int.ofNat (transferFromTailReceiverCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [show (transferFromTailStoreToBalance (transferFromStore I) evm I).get?
        "toBalance" = some (transferFromTailReceiverBalanceValue evm I) by
      rw [transferFromTailStoreToBalance, store_get_self]]
  rw [show (transferFromTailStoreToBalance (transferFromStore I) evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreToBalance, store_get_ne _ _ (by decide),
        transferFromTailStoreFromBalance, store_get_ne _ _ (by decide),
        transferFromStore_amount]]
  simp [evalBinaryOp?, transferFromTailReceiverBalanceValue, transferFromAmountValue,
    transferFromTailReceiverCreditValue, transferFromTailReceiverCreditNat, uint256Int]
  intro _
  simpa [transferFromTailReceiverCreditNat] using hge

theorem evalExpr_transferFrom_tail_receiver_credit_revert_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hamount : locals.get? "amount" = some (transferFromAmountValue I))
    (hover : UInt256.size ≤ transferFromTailReceiverCreditNat evm I) :
    evalExpr? config
      { contract := contract, locals := transferFromTailStoreToBalance locals evm I }
      (transferFromTailAfterSenderBalanceState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))) = .revert := by
  have hge : Int.ofNat (transferFromTailReceiverCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [show (transferFromTailStoreToBalance locals evm I).get?
        "toBalance" = some (transferFromTailReceiverBalanceValue evm I) by
      rw [transferFromTailStoreToBalance, store_get_self]]
  rw [show (transferFromTailStoreToBalance locals evm I).get?
        "amount" = some (transferFromAmountValue I) by
      rw [transferFromTailStoreToBalance, store_get_ne _ _ (by decide),
        transferFromTailStoreFromBalance, store_get_ne _ _ (by decide), hamount]]
  simp [evalBinaryOp?, transferFromTailReceiverBalanceValue, transferFromAmountValue,
    transferFromTailReceiverCreditValue, transferFromTailReceiverCreditNat, uint256Int]
  intro _
  simpa [transferFromTailReceiverCreditNat] using hge

theorem evalStorageRef_transferFrom_tail_receiver_balance_toBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config
      { contract := contract, locals := transferFromTailStoreToBalance (transferFromStore I) evm I }
      evm' (balanceRef (.var "receiver") (.var "id")) =
        .ok (transferFromReceiverBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef,
    evalExpr_transferFrom_tail_receiver_toBalance (transferFromStore I) evm evm' I
      (transferFromStore_receiver I),
    evalExpr_transferFrom_tail_id_toBalance (transferFromStore I) evm evm' I
      (transferFromStore_id I),
    transferFromReceiverBalanceEvaledRef, transferFromReceiverValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalStorageRef_transferFrom_tail_receiver_balance_toBalance_of_get
    (locals : Store) (evm evm' : EVM.State) (I : ExecutionEnv)
    (hreceiver : locals.get? "receiver" = some (transferFromReceiverValue I))
    (hid : locals.get? "id" = some (transferFromIdValue I)) :
    evalStorageRef config
      { contract := contract, locals := transferFromTailStoreToBalance locals evm I }
      evm' (balanceRef (.var "receiver") (.var "id")) =
        .ok (transferFromReceiverBalanceEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceRef,
    evalExpr_transferFrom_tail_receiver_toBalance locals evm evm' I hreceiver,
    evalExpr_transferFrom_tail_id_toBalance locals evm evm' I hid,
    transferFromReceiverBalanceEvaledRef, transferFromReceiverValue, transferFromIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem transferFromTailAssignReceiverBalance (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    assignStorageRef? config
      { contract := contract, locals := transferFromTailStoreToBalance (transferFromStore I) evm I }
      (transferFromTailAfterSenderBalanceState evm I) .storage
      (balanceRef (.var "receiver") (.var "id"))
      (transferFromTailReceiverCreditValue evm I) =
        .ok ({ contract := contract, locals := transferFromTailStoreToBalance (transferFromStore I) evm I },
          transferFromTailPostState evm I) := by
  simp only [balanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferFromReceiverBalanceSlot I))
      (hbase := by simp [balanceRef, transferFromTailStoreToBalance,
        transferFromTailStoreFromBalance, transferFromStore])
      (her := evalStorageRef_transferFrom_tail_receiver_balance_toBalance evm
        (transferFromTailAfterSenderBalanceState evm I) I)
      (hty := by
        simp [storageTypeAt?, transferFromReceiverBalanceEvaledRef, contract, storageDecls,
          uint256St, storageTypeStep?])
      (hloc := by simp [config, storageLayout, transferFromReceiverBalanceEvaledRef,
        transferFromReceiverBalanceSlot])
  rw [← transferFromTailReceiverCreditWord_toNat evm I hfit]
  rw [erc6909StorageLocStore_uint256]
  simp [transferFromTailPostState, transferFromReceiverBalanceSlot,
    transferFromTailAfterSenderBalance_codeOwner]

theorem transferFromTailAssignReceiverBalance_of_get (locals : Store)
    (evm : EVM.State) (I : ExecutionEnv)
    (hreceiver : locals.get? "receiver" = some (transferFromReceiverValue I))
    (hid : locals.get? "id" = some (transferFromIdValue I))
    (hbase : "_balances" ∉ locals)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    assignStorageRef? config
      { contract := contract, locals := transferFromTailStoreToBalance locals evm I }
      (transferFromTailAfterSenderBalanceState evm I) .storage
      (balanceRef (.var "receiver") (.var "id"))
      (transferFromTailReceiverCreditValue evm I) =
        .ok ({ contract := contract, locals := transferFromTailStoreToBalance locals evm I },
          transferFromTailPostState evm I) := by
  simp only [balanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (loc := wordLoc (transferFromReceiverBalanceSlot I))
      (hbase := by
        simp [balanceRef, transferFromTailStoreToBalance, transferFromTailStoreFromBalance,
          hbase])
      (her := evalStorageRef_transferFrom_tail_receiver_balance_toBalance_of_get locals evm
        (transferFromTailAfterSenderBalanceState evm I) I hreceiver hid)
      (hty := by
        simp [storageTypeAt?, transferFromReceiverBalanceEvaledRef, contract, storageDecls,
          uint256St, storageTypeStep?])
      (hloc := by simp [config, storageLayout, transferFromReceiverBalanceEvaledRef,
        transferFromReceiverBalanceSlot])
  rw [← transferFromTailReceiverCreditWord_toNat evm I hfit]
  rw [erc6909StorageLocStore_uint256]
  simp [transferFromTailPostState, transferFromReceiverBalanceSlot,
    transferFromTailAfterSenderBalance_codeOwner]

abbrev transferFromTailReceiverBody : List Stmt :=
  [ .letDecl "toBalance" (some uint256)
      (.storage (balanceRef (.var "receiver") (.var "id"))),
    .assign .storage (balanceRef (.var "receiver") (.var "id"))
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))),
    .return (.boolLit true) ]

abbrev transferFromAfterAllowanceBody : List Stmt :=
  [ .require (.binary .ne (.var "sender") zeroAddr),
    .require (.binary .ne (.var "receiver") zeroAddr),
    .letDecl "fromBalance" (some uint256)
      (.storage (balanceRef (.var "sender") (.var "id"))),
    .require (.binary .ge (.var "fromBalance") (.var "amount")),
    .assign .storage (balanceRef (.var "sender") (.var "id"))
      (.binary .sub (.var "fromBalance") (.var "amount")),
    .letDecl "toBalance" (some uint256)
      (.storage (balanceRef (.var "receiver") (.var "id"))),
    .assign .storage (balanceRef (.var "receiver") (.var "id"))
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "amount"))),
    .return (.boolLit true) ]

theorem erc6909TransferFromAllowanceMaxPrefixBlock (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool false))
    {result : ExecResult}
    (htail :
      ExecBlock config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        evm transferFromAfterAllowanceBody result) :
    ExecBlock config { contract := contract, locals := transferFromStore I }
      evm transferFromTransition.body result := by
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        evm)
      hallowanceGate ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
    rw [transferFromStoreCurrentAllowance] at hallowanceMax ⊢
    let currentFrame : Frame :=
      { contract := contract,
        locals := (transferFromStore I).insert "currentAllowance"
          (transferFromCurrentAllowanceValue evm I) }
    refine ExecBlock.consNormal
      (ExecStmt.iteFalse
        (result := .ok currentFrame evm)
        hallowanceMax ?_) ?_
    · exact ExecBlock.nil
    · exact ExecBlock.nil
  simpa [transferFromAfterAllowanceBody] using htail

theorem erc6909TransferFromTailReceiverCoreCurrentAllowance
    (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    ExecBlock config
      { contract := contract,
        locals := transferFromTailStoreFromBalance (transferFromStoreCurrentAllowance evm I)
          evm I }
      (transferFromTailAfterSenderBalanceState evm I)
      transferFromTailReceiverBody
      (.returned
        { contract := contract,
          locals := transferFromTailStoreToBalance (transferFromStoreCurrentAllowance evm I)
            evm I }
        (transferFromTailPostState evm I) (some (.bool true))) := by
  have hbase : "_balances" ∉ transferFromStoreCurrentAllowance evm I := by
    simp [transferFromStoreCurrentAllowance, transferFromStore]
  dsimp [transferFromTailReceiverBody]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_transferFrom_tail_receiver_balance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_receiver evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFrom_tail_receiver_credit_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_amount evm I) hfit)
      (transferFromTailAssignReceiverBalance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_receiver evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

set_option maxHeartbeats 50000000 in
theorem erc6909TransferFromAfterAllowanceCore (evm : EVM.State) (I : ExecutionEnv)
    (hsenderNonzero :
      evalExpr? config { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        evm (.binary .ne (.var "sender") zeroAddr) = .ok (.bool true))
    (hreceiverNonzero :
      evalExpr? config { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        evm (.binary .ne (.var "receiver") zeroAddr) = .ok (.bool true))
    (hbalanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord evm I).toNat)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    ExecBlock config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
      evm transferFromAfterAllowanceBody
      (.returned
        { contract := contract,
          locals := transferFromTailStoreToBalance (transferFromStoreCurrentAllowance evm I)
            evm I }
        (transferFromTailPostState evm I) (some (.bool true))) := by
  dsimp [transferFromAfterAllowanceBody]
  refine ExecBlock.consNormal (ExecStmt.requireTrue hsenderNonzero) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreceiverNonzero) ?_
  have hbase : "_balances" ∉ transferFromStoreCurrentAllowance evm I := by
    simp [transferFromStoreCurrentAllowance, transferFromStore]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_transferFrom_tail_sender_balance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_sender evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_tail_sender_balance_ge_true_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_amount evm I) hbalanceEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFrom_tail_sender_debit_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_amount evm I) hbalanceEnough)
      (transferFromTailAssignSenderBalance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_sender evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase)) ?_
  change ExecBlock config
    { contract := contract,
      locals := transferFromTailStoreFromBalance (transferFromStoreCurrentAllowance evm I)
        evm I }
    (transferFromTailAfterSenderBalanceState evm I)
    transferFromTailReceiverBody
    (.returned
      { contract := contract,
        locals := transferFromTailStoreToBalance (transferFromStoreCurrentAllowance evm I)
          evm I }
      (transferFromTailPostState evm I) (some (.bool true)))
  exact erc6909TransferFromTailReceiverCoreCurrentAllowance evm I hfit

theorem erc6909TransferFromAfterAllowanceReverts_sender_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hz : AccountAddress.ofNat (transferFromSenderWord I).toNat = zeroAccountAddress) :
    ExecBlock config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
      evm transferFromAfterAllowanceBody .reverted := by
  dsimp [transferFromAfterAllowanceBody]
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFrom_sender_nonzero_false_of_get evm
        (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hz))

theorem erc6909TransferFromAfterAllowanceReverts_receiver_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hz : AccountAddress.ofNat (transferFromReceiverWord I).toNat = zeroAccountAddress) :
    ExecBlock config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
      evm transferFromAfterAllowanceBody .reverted := by
  dsimp [transferFromAfterAllowanceBody]
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get evm
        (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hsender)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFrom_receiver_nonzero_false_of_get evm
        (transferFromStoreCurrentAllowance evm I) I
        (by
          rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
            transferFromStore_receiver])
        hz))

set_option maxHeartbeats 50000000 in
theorem erc6909TransferFromAfterAllowanceReverts_insufficient_balance
    (evm : EVM.State) (I : ExecutionEnv)
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (hlt : (transferFromSenderBalanceWord evm I).toNat < (transferFromAmountWord I).toNat) :
    ExecBlock config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
      evm transferFromAfterAllowanceBody .reverted := by
  dsimp [transferFromAfterAllowanceBody]
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get evm
        (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hsender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_receiver_nonzero_true_of_get evm
        (transferFromStoreCurrentAllowance evm I) I
        (by
          rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
            transferFromStore_receiver])
        hreceiver)) ?_
  have hbase : "_balances" ∉ transferFromStoreCurrentAllowance evm I := by
    simp [transferFromStoreCurrentAllowance, transferFromStore]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_transferFrom_tail_sender_balance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_sender evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFrom_tail_sender_balance_ge_false_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_amount evm I) hlt))

set_option maxHeartbeats 50000000 in
theorem erc6909TransferFromAfterAllowanceReverts_overflow
    (evm : EVM.State) (I : ExecutionEnv)
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (henough : (transferFromAmountWord I).toNat ≤ (transferFromSenderBalanceWord evm I).toNat)
    (hover : UInt256.size ≤ transferFromTailReceiverCreditNat evm I) :
    ExecBlock config
      { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
      evm transferFromAfterAllowanceBody .reverted := by
  dsimp [transferFromAfterAllowanceBody]
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get evm
        (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hsender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_receiver_nonzero_true_of_get evm
        (transferFromStoreCurrentAllowance evm I) I
        (by
          rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
            transferFromStore_receiver])
        hreceiver)) ?_
  have hbase : "_balances" ∉ transferFromStoreCurrentAllowance evm I := by
    simp [transferFromStoreCurrentAllowance, transferFromStore]
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_transferFrom_tail_sender_balance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_sender evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_tail_sender_balance_ge_true_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_amount evm I) henough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFrom_tail_sender_debit_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_amount evm I) henough)
      (transferFromTailAssignSenderBalance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_sender evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl
      (evalExpr_transferFrom_tail_receiver_balance_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_receiver evm I)
        (transferFromStoreCurrentAllowance_id evm I) hbase)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert
      (evalExpr_transferFrom_tail_receiver_credit_revert_of_get
        (transferFromStoreCurrentAllowance evm I) evm I
        (transferFromStoreCurrentAllowance_amount evm I) hover))

/-- Source-side core for the allowance-debit success path of
`transferFrom(address,address,uint256,uint256)`.

The hypotheses name the branch guards that the EVM body at pc 388 must establish on this path.  The
state threading below is deliberately explicit: the sender balance is read from
`transferFromAfterAllowanceState`, after the allowance write.
-/
theorem erc6909TransferFromBodyCoreAllowanceDebit (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceNotMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool true))
    (hallowanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hsenderNonzero :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        (transferFromAfterAllowanceState evm I)
        (.binary .ne (.var "sender") zeroAddr) = .ok (.bool true))
    (hreceiverNonzero :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        (transferFromAfterAllowanceState evm I)
        (.binary .ne (.var "receiver") zeroAddr) = .ok (.bool true))
    (hbalanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat)
    (hfit : transferFromReceiverCreditNat evm I < UInt256.size) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body
      (.returned { contract := contract, locals := transferFromStoreToBalance evm I }
        (transferFromPostState evm I) (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        (transferFromAfterAllowanceState evm I))
      hallowanceGate ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
    rw [transferFromStoreCurrentAllowance] at hallowanceNotMax hsenderNonzero hreceiverNonzero ⊢
    let currentFrame : Frame :=
      { contract := contract,
        locals := (transferFromStore I).insert "currentAllowance"
          (transferFromCurrentAllowanceValue evm I) }
    refine ExecBlock.consNormal
      (ExecStmt.iteTrue
        (result := .ok currentFrame (transferFromAfterAllowanceState evm I))
        hallowanceNotMax ?_) ?_
    · refine ExecBlock.consNormal
        (ExecStmt.requireTrue
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_ge_true evm I hallowanceEnough)) ?_
      refine ExecBlock.consNormal
        (ExecStmt.assign
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_debit evm I hallowanceEnough)
          (by
            simpa [transferFromStoreCurrentAllowance] using
              transferFromAssignAllowance evm I)) ?_
      exact ExecBlock.nil
    · exact ExecBlock.nil
  refine ExecBlock.consNormal (ExecStmt.requireTrue hsenderNonzero) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreceiverNonzero) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_sender_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_balance_ge_true evm I hbalanceEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_sender_debit evm I hbalanceEnough)
      (transferFromAssignSenderBalance evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_receiver_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_receiver_credit evm I hfit)
      (transferFromAssignReceiverBalance evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

set_option maxHeartbeats 12000000 in
theorem erc6909TransferFromBodyCoreAllowanceMax (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool false))
    (hsenderNonzero :
      evalExpr? config { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        evm (.binary .ne (.var "sender") zeroAddr) = .ok (.bool true))
    (hreceiverNonzero :
      evalExpr? config { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        evm (.binary .ne (.var "receiver") zeroAddr) = .ok (.bool true))
    (hbalanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord evm I).toNat)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    ∃ cs, ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body
      (.returned cs (transferFromTailPostState evm I) (some (.bool true))) := by
  let cs : Frame :=
    { contract := contract
      locals := transferFromTailStoreToBalance (transferFromStoreCurrentAllowance evm I) evm I }
  refine ⟨cs, ExecFuncBody.execBlockRet ?_⟩
  exact erc6909TransferFromAllowanceMaxPrefixBlock evm I hwv hallowanceGate hallowanceMax
    (erc6909TransferFromAfterAllowanceCore evm I hsenderNonzero hreceiverNonzero
      hbalanceEnough hfit)

theorem erc6909TransferFromBodyRevertsAllowanceMax_sender_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
      (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool false))
    (hz : AccountAddress.ofNat (transferFromSenderWord I).toNat = zeroAccountAddress) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact erc6909TransferFromAllowanceMaxPrefixBlock evm I hwv hallowanceGate hallowanceMax
    (erc6909TransferFromAfterAllowanceReverts_sender_zero evm I hz)

theorem erc6909TransferFromBodyRevertsAllowanceMax_receiver_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool false))
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hz : AccountAddress.ofNat (transferFromReceiverWord I).toNat = zeroAccountAddress) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact erc6909TransferFromAllowanceMaxPrefixBlock evm I hwv hallowanceGate hallowanceMax
    (erc6909TransferFromAfterAllowanceReverts_receiver_zero evm I hsender hz)

set_option maxHeartbeats 12000000 in
theorem erc6909TransferFromBodyRevertsAllowanceMax_insufficient_balance
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool false))
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (hlt : (transferFromSenderBalanceWord evm I).toNat < (transferFromAmountWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact erc6909TransferFromAllowanceMaxPrefixBlock evm I hwv hallowanceGate hallowanceMax
    (erc6909TransferFromAfterAllowanceReverts_insufficient_balance evm I hsender hreceiver hlt)

set_option maxHeartbeats 12000000 in
theorem erc6909TransferFromBodyRevertsAllowanceMax_overflow
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool false))
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (henough : (transferFromAmountWord I).toNat ≤ (transferFromSenderBalanceWord evm I).toNat)
    (hover : UInt256.size ≤ transferFromTailReceiverCreditNat evm I) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  exact erc6909TransferFromAllowanceMaxPrefixBlock evm I hwv hallowanceGate hallowanceMax
    (erc6909TransferFromAfterAllowanceReverts_overflow evm I hsender hreceiver henough hover)

theorem erc6909TransferFromBodyCoreNoAllowance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool false))
    (hsenderNonzero :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .ne (.var "sender") zeroAddr) = .ok (.bool true))
    (hreceiverNonzero :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .ne (.var "receiver") zeroAddr) = .ok (.bool true))
    (hbalanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord evm I).toNat)
    (hfit : transferFromTailReceiverCreditNat evm I < UInt256.size) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body
      (.returned { contract := contract, locals := transferFromTailStoreToBalance (transferFromStore I) evm I }
        (transferFromTailPostState evm I) (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (result := .ok
      ({ contract := contract, locals := transferFromStore I } : Frame) evm)
      hallowanceGate ?_) ?_
  · exact ExecBlock.nil
  refine ExecBlock.consNormal (ExecStmt.requireTrue hsenderNonzero) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreceiverNonzero) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_tail_sender_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_tail_sender_balance_ge_true evm I hbalanceEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_tail_sender_debit evm I hbalanceEnough)
      (transferFromTailAssignSenderBalance evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_tail_receiver_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_tail_receiver_credit evm I hfit)
      (transferFromTailAssignReceiverBalance evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem erc6909TransferFromBodyRevertsAllowance_insufficient
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceNotMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool true))
    (hlt : (transferFromCurrentAllowanceWord evm I).toNat <
      (transferFromAmountWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.iteTrue hallowanceGate ?_
  · refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
    rw [transferFromStoreCurrentAllowance] at hallowanceNotMax
    let currentFrame : Frame :=
      { contract := contract,
        locals := (transferFromStore I).insert "currentAllowance"
          (transferFromCurrentAllowanceValue evm I) }
    change ExecBlock config currentFrame evm
      [ .ite (.binary .lt (.var "currentAllowance") maxUint256Lit)
          [ .require (.binary .ge (.var "currentAllowance") (.var "amount")),
            .assign .storage (allowanceRef (.var "sender") sender (.var "id"))
              (.binary .sub (.var "currentAllowance") (.var "amount")) ]
          [] ]
      .reverted
    refine ExecBlock.consRevert ?_
    refine ExecStmt.iteTrue (result := .reverted) hallowanceNotMax ?_
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (by
          simpa [transferFromStoreCurrentAllowance] using
            evalExpr_transferFrom_allowance_ge_false evm I hlt))

theorem erc6909TransferFromBodyRevertsAllowance_sender_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceNotMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool true))
    (hallowanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hz : AccountAddress.ofNat (transferFromSenderWord I).toNat = zeroAccountAddress) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        (transferFromAfterAllowanceState evm I))
      hallowanceGate ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
    rw [transferFromStoreCurrentAllowance] at hallowanceNotMax ⊢
    let currentFrame : Frame :=
      { contract := contract,
        locals := (transferFromStore I).insert "currentAllowance"
          (transferFromCurrentAllowanceValue evm I) }
    refine ExecBlock.consNormal
      (ExecStmt.iteTrue
        (result := .ok currentFrame (transferFromAfterAllowanceState evm I))
        hallowanceNotMax ?_) ?_
    · refine ExecBlock.consNormal
        (ExecStmt.requireTrue
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_ge_true evm I hallowanceEnough)) ?_
      refine ExecBlock.consNormal
        (ExecStmt.assign
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_debit evm I hallowanceEnough)
          (by
            simpa [transferFromStoreCurrentAllowance] using
              transferFromAssignAllowance evm I)) ?_
      exact ExecBlock.nil
    · exact ExecBlock.nil
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFrom_sender_nonzero_false_of_get
        (transferFromAfterAllowanceState evm I) (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hz))

theorem erc6909TransferFromBodyRevertsAllowance_receiver_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceNotMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool true))
    (hallowanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hz : AccountAddress.ofNat (transferFromReceiverWord I).toNat = zeroAccountAddress) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        (transferFromAfterAllowanceState evm I))
      hallowanceGate ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
    rw [transferFromStoreCurrentAllowance] at hallowanceNotMax ⊢
    let currentFrame : Frame :=
      { contract := contract,
        locals := (transferFromStore I).insert "currentAllowance"
          (transferFromCurrentAllowanceValue evm I) }
    refine ExecBlock.consNormal
      (ExecStmt.iteTrue
        (result := .ok currentFrame (transferFromAfterAllowanceState evm I))
        hallowanceNotMax ?_) ?_
    · refine ExecBlock.consNormal
        (ExecStmt.requireTrue
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_ge_true evm I hallowanceEnough)) ?_
      refine ExecBlock.consNormal
        (ExecStmt.assign
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_debit evm I hallowanceEnough)
          (by
            simpa [transferFromStoreCurrentAllowance] using
              transferFromAssignAllowance evm I)) ?_
      exact ExecBlock.nil
    · exact ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get
        (transferFromAfterAllowanceState evm I) (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hsender)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFrom_receiver_nonzero_false_of_get
        (transferFromAfterAllowanceState evm I) (transferFromStoreCurrentAllowance evm I) I
        (by
          rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
            transferFromStore_receiver])
        hz))

theorem erc6909TransferFromBodyRevertsAllowance_insufficient_balance
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceNotMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool true))
    (hallowanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (hlt : (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat <
      (transferFromAmountWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        (transferFromAfterAllowanceState evm I))
      hallowanceGate ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
    rw [transferFromStoreCurrentAllowance] at hallowanceNotMax ⊢
    let currentFrame : Frame :=
      { contract := contract,
        locals := (transferFromStore I).insert "currentAllowance"
          (transferFromCurrentAllowanceValue evm I) }
    refine ExecBlock.consNormal
      (ExecStmt.iteTrue
        (result := .ok currentFrame (transferFromAfterAllowanceState evm I))
        hallowanceNotMax ?_) ?_
    · refine ExecBlock.consNormal
        (ExecStmt.requireTrue
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_ge_true evm I hallowanceEnough)) ?_
      refine ExecBlock.consNormal
        (ExecStmt.assign
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_debit evm I hallowanceEnough)
          (by
            simpa [transferFromStoreCurrentAllowance] using
              transferFromAssignAllowance evm I)) ?_
      exact ExecBlock.nil
    · exact ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get
        (transferFromAfterAllowanceState evm I) (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hsender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_receiver_nonzero_true_of_get
        (transferFromAfterAllowanceState evm I) (transferFromStoreCurrentAllowance evm I) I
        (by
          rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
            transferFromStore_receiver])
        hreceiver)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_sender_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transferFrom_sender_balance_ge_false evm I hlt))

theorem erc6909TransferFromBodyRevertsAllowance_overflow
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool true))
    (hallowanceNotMax :
      evalExpr? config
        { contract := contract, locals := transferFromStoreCurrentAllowance evm I } evm
        (.binary .lt (.var "currentAllowance") maxUint256Lit) = .ok (.bool true))
    (hallowanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord evm I).toNat)
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (hbalanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (transferFromAfterAllowanceState evm I) I).toNat)
    (hover : UInt256.size ≤ transferFromReceiverCreditNat evm I) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
        (transferFromAfterAllowanceState evm I))
      hallowanceGate ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_transferFrom_currentAllowance evm I)) ?_
    rw [transferFromStoreCurrentAllowance] at hallowanceNotMax ⊢
    let currentFrame : Frame :=
      { contract := contract,
        locals := (transferFromStore I).insert "currentAllowance"
          (transferFromCurrentAllowanceValue evm I) }
    refine ExecBlock.consNormal
      (ExecStmt.iteTrue
        (result := .ok currentFrame (transferFromAfterAllowanceState evm I))
        hallowanceNotMax ?_) ?_
    · refine ExecBlock.consNormal
        (ExecStmt.requireTrue
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_ge_true evm I hallowanceEnough)) ?_
      refine ExecBlock.consNormal
        (ExecStmt.assign
          (by
            simpa [transferFromStoreCurrentAllowance] using
              evalExpr_transferFrom_allowance_debit evm I hallowanceEnough)
          (by
            simpa [transferFromStoreCurrentAllowance] using
              transferFromAssignAllowance evm I)) ?_
      exact ExecBlock.nil
    · exact ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get
        (transferFromAfterAllowanceState evm I) (transferFromStoreCurrentAllowance evm I) I
        (transferFromStoreCurrentAllowance_sender evm I) hsender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_receiver_nonzero_true_of_get
        (transferFromAfterAllowanceState evm I) (transferFromStoreCurrentAllowance evm I) I
        (by
          rw [transferFromStoreCurrentAllowance, store_get_ne _ _ (by decide),
            transferFromStore_receiver])
        hreceiver)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_sender_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_balance_ge_true evm I hbalanceEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_sender_debit evm I hbalanceEnough)
      (transferFromAssignSenderBalance evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_receiver_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert (evalExpr_transferFrom_receiver_credit_revert evm I hover))

theorem erc6909TransferFromBodyRevertsNoAllowance_sender_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool false))
    (hz : AccountAddress.ofNat (transferFromSenderWord I).toNat = zeroAccountAddress) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (result := .ok
      ({ contract := contract, locals := transferFromStore I } : Frame) evm)
      hallowanceGate ?_) ?_
  · exact ExecBlock.nil
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFrom_sender_nonzero_false_of_get evm (transferFromStore I) I
        (transferFromStore_sender I) hz))

theorem erc6909TransferFromBodyRevertsNoAllowance_receiver_zero
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool false))
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hz : AccountAddress.ofNat (transferFromReceiverWord I).toNat = zeroAccountAddress) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (result := .ok
      ({ contract := contract, locals := transferFromStore I } : Frame) evm)
      hallowanceGate ?_) ?_
  · exact ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get evm (transferFromStore I) I
        (transferFromStore_sender I) hsender)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFrom_receiver_nonzero_false_of_get evm (transferFromStore I) I
        (transferFromStore_receiver I) hz))

theorem erc6909TransferFromBodyRevertsNoAllowance_insufficient
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool false))
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (hlt : (transferFromSenderBalanceWord evm I).toNat < (transferFromAmountWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (result := .ok
      ({ contract := contract, locals := transferFromStore I } : Frame) evm)
      hallowanceGate ?_) ?_
  · exact ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get evm (transferFromStore I) I
        (transferFromStore_sender I) hsender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_receiver_nonzero_true_of_get evm (transferFromStore I) I
        (transferFromStore_receiver I) hreceiver)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_tail_sender_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transferFrom_tail_sender_balance_ge_false evm I hlt))

theorem erc6909TransferFromBodyRevertsNoAllowance_overflow
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hallowanceGate :
      evalExpr? config { contract := contract, locals := transferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "sender") sender)
          (.unary .not (.storage (operatorApprovalRef (.var "sender") sender)))) =
          .ok (.bool false))
    (hsender : AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ zeroAccountAddress)
    (hreceiver : AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠ zeroAccountAddress)
    (henough : (transferFromAmountWord I).toNat ≤ (transferFromSenderBalanceWord evm I).toNat)
    (hover : UInt256.size ≤ transferFromTailReceiverCreditNat evm I) :
    ExecTransitionBody config contract evm (transferFromStore I)
      transferFromTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [transferFromTransition]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (result := .ok
      ({ contract := contract, locals := transferFromStore I } : Frame) evm)
      hallowanceGate ?_) ?_
  · exact ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_sender_nonzero_true_of_get evm (transferFromStore I) I
        (transferFromStore_sender I) hsender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_receiver_nonzero_true_of_get evm (transferFromStore I) I
        (transferFromStore_receiver I) hreceiver)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_tail_sender_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_tail_sender_balance_ge_true evm I henough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_tail_sender_debit evm I henough)
      (transferFromTailAssignSenderBalance evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transferFrom_tail_receiver_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert
      (evalExpr_transferFrom_tail_receiver_credit_revert evm I hover))

/-! ## Generic scratch-memory helpers for `transferFrom` EVM tails -/

theorem erc6909ScratchMem_mload64 {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ base.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian (base.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [hbase]; decide) (by decide) hread64

noncomputable def solcReturnBaseMem (base : ByteArray) (selector : UInt256) : ByteArray :=
  (UInt256.toByteArray selector).write 0 base 128 32

noncomputable def approveErrorBaseMem (base : ByteArray) (selector arg : UInt256) : ByteArray :=
  (UInt256.toByteArray arg).write 0 (solcReturnBaseMem base selector) 132 32

theorem solcReturnBaseMem_size {base : ByteArray} (selector : UInt256)
    (hbase : base.size = 96) :
    (solcReturnBaseMem base selector).size = 160 := by
  unfold solcReturnBaseMem
  rw [toByteArray_write_eq _ _ _ (by rw [hbase]; omega)
      (by rw [hbase]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, hbase, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem solcReturnBaseMem_read64 {base : ByteArray} (selector : UInt256)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcReturnBaseMem base selector).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcReturnBaseMem
  rw [toByteArray_write_eq _ _ _ (by rw [hbase]; omega)
      (by rw [hbase]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hbase, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, hbase, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [hbase]),
    ← readWithPadding_eq_extract _ 64 (by rw [hbase])]
  exact hread64

theorem approveErrorBaseMem_size {base : ByteArray} (selector arg : UInt256)
    (hbase : base.size = 96) :
    (approveErrorBaseMem base selector arg).size = 164 := by
  unfold approveErrorBaseMem
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [solcReturnBaseMem_size selector hbase]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, solcReturnBaseMem_size selector hbase,
    toByteArray_size]
  omega

theorem approveErrorBaseMem_read64 {base : ByteArray} (selector arg : UInt256)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (approveErrorBaseMem base selector arg).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold approveErrorBaseMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [solcReturnBaseMem_size selector hbase]; omega) (by omega),
    solcReturnBaseMem_read64 selector hbase hread64]

theorem approveErrorBaseMem_mload64 {base : ByteArray} (selector arg : UInt256)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (approveErrorBaseMem base selector arg).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((approveErrorBaseMem base selector arg).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [approveErrorBaseMem_size selector arg hbase]; decide)
    (by decide) (approveErrorBaseMem_read64 selector arg hbase hread64)

noncomputable def transferInsufficientBalanceSelectorBaseMem
    (base : ByteArray) : ByteArray :=
  (UInt256.toByteArray transferInsufficientBalanceSelectorWord).write 0 base 128 32

noncomputable def transferInsufficientBalanceSenderBaseMem
    (base : ByteArray) (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray owner).write 0
    (transferInsufficientBalanceSelectorBaseMem base) 132 32

noncomputable def transferInsufficientBalanceBalanceBaseMem
    (base : ByteArray) (owner balance : UInt256) : ByteArray :=
  (UInt256.toByteArray balance).write 0
    (transferInsufficientBalanceSenderBaseMem base owner) 164 32

noncomputable def transferInsufficientBalanceAmountBaseMem
    (base : ByteArray) (owner balance amount : UInt256) : ByteArray :=
  (UInt256.toByteArray amount).write 0
    (transferInsufficientBalanceBalanceBaseMem base owner balance) 196 32

noncomputable def transferInsufficientBalanceIdBaseMem
    (base : ByteArray) (owner id balance amount : UInt256) : ByteArray :=
  (UInt256.toByteArray id).write 0
    (transferInsufficientBalanceAmountBaseMem base owner balance amount) 228 32

theorem transferInsufficientBalanceSelectorBaseMem_size {base : ByteArray}
    (hbase : base.size = 96) :
    (transferInsufficientBalanceSelectorBaseMem base).size = 160 := by
  unfold transferInsufficientBalanceSelectorBaseMem
  rw [toByteArray_write_eq _ _ _ (by rw [hbase]; omega)
      (by rw [hbase]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, hbase, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem transferInsufficientBalanceSenderBaseMem_size {base : ByteArray}
    (owner : UInt256) (hbase : base.size = 96) :
    (transferInsufficientBalanceSenderBaseMem base owner).size = 164 := by
  unfold transferInsufficientBalanceSenderBaseMem
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceSelectorBaseMem_size hbase]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferInsufficientBalanceSelectorBaseMem_size hbase, toByteArray_size]
  omega

theorem transferInsufficientBalanceBalanceBaseMem_size {base : ByteArray}
    (owner balance : UInt256) (hbase : base.size = 96) :
    (transferInsufficientBalanceBalanceBaseMem base owner balance).size = 196 := by
  unfold transferInsufficientBalanceBalanceBaseMem
  rw [write32_eq _ _ 164 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceSenderBaseMem_size owner hbase]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferInsufficientBalanceSenderBaseMem_size owner hbase, toByteArray_size]
  omega

theorem transferInsufficientBalanceAmountBaseMem_size {base : ByteArray}
    (owner balance amount : UInt256) (hbase : base.size = 96) :
    (transferInsufficientBalanceAmountBaseMem base owner balance amount).size = 228 := by
  unfold transferInsufficientBalanceAmountBaseMem
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceBalanceBaseMem_size owner balance hbase]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferInsufficientBalanceBalanceBaseMem_size owner balance hbase, toByteArray_size]
  omega

theorem transferInsufficientBalanceIdBaseMem_size {base : ByteArray}
    (owner id balance amount : UInt256) (hbase : base.size = 96) :
    (transferInsufficientBalanceIdBaseMem base owner id balance amount).size = 260 := by
  unfold transferInsufficientBalanceIdBaseMem
  rw [write32_eq _ _ 228 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceAmountBaseMem_size owner balance amount hbase]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferInsufficientBalanceAmountBaseMem_size owner balance amount hbase,
    toByteArray_size]
  omega

theorem transferInsufficientBalanceSelectorBaseMem_read64 {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferInsufficientBalanceSelectorBaseMem base).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientBalanceSelectorBaseMem
  rw [toByteArray_write_eq _ _ _ (by rw [hbase]; omega)
      (by rw [hbase]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hbase, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, hbase, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [hbase]),
    ← readWithPadding_eq_extract _ 64 (by rw [hbase])]
  exact hread64

theorem transferInsufficientBalanceSenderBaseMem_read64 {base : ByteArray}
    (owner : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferInsufficientBalanceSenderBaseMem base owner).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientBalanceSenderBaseMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceSelectorBaseMem_size hbase]; omega) (by omega),
    transferInsufficientBalanceSelectorBaseMem_read64 hbase hread64]

theorem transferInsufficientBalanceBalanceBaseMem_read64 {base : ByteArray}
    (owner balance : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferInsufficientBalanceBalanceBaseMem base owner balance).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientBalanceBalanceBaseMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceSenderBaseMem_size owner hbase]) (by omega),
    transferInsufficientBalanceSenderBaseMem_read64 owner hbase hread64]

theorem transferInsufficientBalanceAmountBaseMem_read64 {base : ByteArray}
    (owner balance amount : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferInsufficientBalanceAmountBaseMem base owner balance amount).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientBalanceAmountBaseMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceBalanceBaseMem_size owner balance hbase])
      (by omega),
    transferInsufficientBalanceBalanceBaseMem_read64 owner balance hbase hread64]

theorem transferInsufficientBalanceIdBaseMem_read64 {base : ByteArray}
    (owner id balance amount : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferInsufficientBalanceIdBaseMem base owner id balance amount).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientBalanceIdBaseMem
  rw [write32_read_below _ _ 228 64 (by rw [toByteArray_size])
      (by rw [transferInsufficientBalanceAmountBaseMem_size owner balance amount hbase])
      (by omega),
    transferInsufficientBalanceAmountBaseMem_read64 owner balance amount hbase hread64]

theorem transferInsufficientBalanceIdBaseMem_mload64 {base : ByteArray}
    (owner id balance amount : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (transferInsufficientBalanceIdBaseMem base owner id balance amount).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferInsufficientBalanceIdBaseMem base owner id balance amount).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [transferInsufficientBalanceIdBaseMem_size owner id balance amount hbase]; decide)
    (by decide) (transferInsufficientBalanceIdBaseMem_read64 owner id balance amount hbase hread64)

def transferFromInsufficientAllowanceSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨0x2c51fead⟩ ⟨225⟩

noncomputable def transferFromInsufficientAllowanceSelectorBaseMem
    (base : ByteArray) : ByteArray :=
  (UInt256.toByteArray transferFromInsufficientAllowanceSelectorWord).write 0 base 128 32

noncomputable def transferFromInsufficientAllowanceSenderBaseMem
    (base : ByteArray) (sender : UInt256) : ByteArray :=
  (UInt256.toByteArray sender).write 0
    (transferFromInsufficientAllowanceSelectorBaseMem base) 132 32

noncomputable def transferFromInsufficientAllowanceAllowanceBaseMem
    (base : ByteArray) (sender allowance : UInt256) : ByteArray :=
  (UInt256.toByteArray allowance).write 0
    (transferFromInsufficientAllowanceSenderBaseMem base sender) 164 32

noncomputable def transferFromInsufficientAllowanceAmountBaseMem
    (base : ByteArray) (sender allowance amount : UInt256) : ByteArray :=
  (UInt256.toByteArray amount).write 0
    (transferFromInsufficientAllowanceAllowanceBaseMem base sender allowance) 196 32

noncomputable def transferFromInsufficientAllowanceIdBaseMem
    (base : ByteArray) (sender id allowance amount : UInt256) : ByteArray :=
  (UInt256.toByteArray id).write 0
    (transferFromInsufficientAllowanceAmountBaseMem base sender allowance amount) 228 32

theorem transferFromInsufficientAllowanceSelectorBaseMem_size {base : ByteArray}
    (hbase : base.size = 96) :
    (transferFromInsufficientAllowanceSelectorBaseMem base).size = 160 := by
  unfold transferFromInsufficientAllowanceSelectorBaseMem
  rw [toByteArray_write_eq _ _ _ (by rw [hbase]; omega)
      (by rw [hbase]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, hbase, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem transferFromInsufficientAllowanceSenderBaseMem_size {base : ByteArray}
    (sender : UInt256) (hbase : base.size = 96) :
    (transferFromInsufficientAllowanceSenderBaseMem base sender).size = 164 := by
  unfold transferFromInsufficientAllowanceSenderBaseMem
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceSelectorBaseMem_size hbase]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromInsufficientAllowanceSelectorBaseMem_size hbase, toByteArray_size]
  omega

theorem transferFromInsufficientAllowanceAllowanceBaseMem_size {base : ByteArray}
    (sender allowance : UInt256) (hbase : base.size = 96) :
    (transferFromInsufficientAllowanceAllowanceBaseMem base sender allowance).size = 196 := by
  unfold transferFromInsufficientAllowanceAllowanceBaseMem
  rw [write32_eq _ _ 164 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceSenderBaseMem_size sender hbase]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromInsufficientAllowanceSenderBaseMem_size sender hbase, toByteArray_size]
  omega

theorem transferFromInsufficientAllowanceAmountBaseMem_size {base : ByteArray}
    (sender allowance amount : UInt256) (hbase : base.size = 96) :
    (transferFromInsufficientAllowanceAmountBaseMem base sender allowance amount).size = 228 := by
  unfold transferFromInsufficientAllowanceAmountBaseMem
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceAllowanceBaseMem_size sender allowance hbase]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromInsufficientAllowanceAllowanceBaseMem_size sender allowance hbase,
    toByteArray_size]
  omega

theorem transferFromInsufficientAllowanceIdBaseMem_size {base : ByteArray}
    (sender id allowance amount : UInt256) (hbase : base.size = 96) :
    (transferFromInsufficientAllowanceIdBaseMem base sender id allowance amount).size = 260 := by
  unfold transferFromInsufficientAllowanceIdBaseMem
  rw [write32_eq _ _ 228 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceAmountBaseMem_size sender allowance amount hbase]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    transferFromInsufficientAllowanceAmountBaseMem_size sender allowance amount hbase,
    toByteArray_size]
  omega

theorem transferFromInsufficientAllowanceSelectorBaseMem_read64 {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferFromInsufficientAllowanceSelectorBaseMem base).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromInsufficientAllowanceSelectorBaseMem
  rw [toByteArray_write_eq _ _ _ (by rw [hbase]; omega)
      (by rw [hbase]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hbase, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, hbase, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [hbase]),
    ← readWithPadding_eq_extract _ 64 (by rw [hbase])]
  exact hread64

theorem transferFromInsufficientAllowanceSenderBaseMem_read64 {base : ByteArray}
    (sender : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferFromInsufficientAllowanceSenderBaseMem base sender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromInsufficientAllowanceSenderBaseMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceSelectorBaseMem_size hbase]; omega) (by omega),
    transferFromInsufficientAllowanceSelectorBaseMem_read64 hbase hread64]

theorem transferFromInsufficientAllowanceAllowanceBaseMem_read64 {base : ByteArray}
    (sender allowance : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferFromInsufficientAllowanceAllowanceBaseMem base sender allowance).readWithPadding
        64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromInsufficientAllowanceAllowanceBaseMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceSenderBaseMem_size sender hbase])
      (by omega),
    transferFromInsufficientAllowanceSenderBaseMem_read64 sender hbase hread64]

theorem transferFromInsufficientAllowanceAmountBaseMem_read64 {base : ByteArray}
    (sender allowance amount : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferFromInsufficientAllowanceAmountBaseMem base sender allowance amount).readWithPadding
        64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromInsufficientAllowanceAmountBaseMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceAllowanceBaseMem_size sender allowance hbase])
      (by omega),
    transferFromInsufficientAllowanceAllowanceBaseMem_read64 sender allowance hbase hread64]

theorem transferFromInsufficientAllowanceIdBaseMem_read64 {base : ByteArray}
    (sender id allowance amount : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferFromInsufficientAllowanceIdBaseMem base sender id allowance amount).readWithPadding
        64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromInsufficientAllowanceIdBaseMem
  rw [write32_read_below _ _ 228 64 (by rw [toByteArray_size])
      (by rw [transferFromInsufficientAllowanceAmountBaseMem_size sender allowance amount hbase])
      (by omega),
    transferFromInsufficientAllowanceAmountBaseMem_read64 sender allowance amount hbase hread64]

theorem transferFromInsufficientAllowanceIdBaseMem_mload64 {base : ByteArray}
    (sender id allowance amount : UInt256) (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (transferFromInsufficientAllowanceIdBaseMem base sender id allowance amount).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferFromInsufficientAllowanceIdBaseMem base sender id allowance amount).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [transferFromInsufficientAllowanceIdBaseMem_size sender id allowance amount hbase]; decide)
    (by decide)
    (transferFromInsufficientAllowanceIdBaseMem_read64 sender id allowance amount hbase hread64)

/-! ## EVM ABI decode trace for `transferFrom(address,address,uint256,uint256)` -/

-- PROMOTE -> Common.lean / Reasoning.Stepping: generic `SWAP7` xstep.
theorem erc6909Swap7_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP7, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: t)
    (hov : t.length + 8 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (h :: b :: c :: d :: e :: f :: gg :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP7, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap7 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: t).length - 8 + 8 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Common.lean / Reasoning.Reach: generic `RD.swap7`.
theorem RD.erc6909Swap7 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {a b c d e f gg h : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: h :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP7, .none)) (hov : t.length + 8 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (h :: b :: c :: d :: e :: f :: gg :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => erc6909Swap7_xstep hc hp hdec hs hov)

theorem erc6909TransferFromX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1954⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨402⟩, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨193⟩, push2 ⟨402⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1954⟩, jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_dec1629_sender {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1629⟩
      [⟨4⟩, ⟨1982⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨402⟩, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨0⟩ := by
    simpa using solcCalldataStaticLenCheckOk (words := 4) hsz132 hszhi hsize
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push0, push0, push1 ⟨128⟩, dup6, dup8, sub, slt, iszero,
    push2 ⟨1973⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push2 ⟨1982⟩, dup6, push2 ⟨1629⟩, jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_dec1982 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1982⟩
      [transferFromSenderWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨402⟩, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_dec1629_sender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hreach
  simpa [transferFromSenderWord, calldataWord] using
    RD.erc6909DecodeAddrOk rd hcanonSender (by jump_dest) (by evm_ov)

theorem erc6909TransferFromX_dec1629_receiver {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1629⟩
      [⟨4⟩ + ⟨32⟩, ⟨1996⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, transferFromSenderWord I,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨402⟩, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_dec1982 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap4, pop, push2 ⟨1996⟩, push1 ⟨32⟩, dup7, add,
    push2 ⟨1629⟩, jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_dec1996 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1996⟩
      [transferFromReceiverWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, transferFromSenderWord I,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨402⟩, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_dec1629_receiver (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hreach
  simpa [transferFromReceiverWord, calldataWord] using
    RD.erc6909DecodeAddrOk rd hcanonReceiver (by jump_dest) (by evm_ov)

theorem erc6909TransferFromX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨556⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_dec1996 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hcanonReceiver hreach
  have rd1997 := evm_run rd with [jumpdest, swap4]
  have rd1998 := RD.erc6909Swap7 rd1997 (by decide) (by evm_ov)
  have rd1999 := evm_run rd1998 with [swap4]
  have rd2000 := RD.erc6909Swap6 rd1999 (by decide) (by evm_ov)
  have rd402 := evm_run rd2000 with [
    pop, pop, pop, pop, push1 ⟨64⟩, dup3, add, calldataload, swap2,
    push1 ⟨96⟩, add, calldataload, swap1, jump (by jump_dest) ]
  have rd556 := evm_run rd402 with [jumpdest, push2 ⟨556⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [transferFromIdWord, transferFromAmountWord, calldataWord] using rd556⟩

theorem erc6909TransferFromX_skipCaller_toUpdate {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd556⟩ := erc6909TransferFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hcanonReceiver hreach
  have hsenderClean :
      UInt256.land (transferFromSenderWord I) solcAddrMask = transferFromSenderWord I :=
    solcAddrMask_clean hcanonSender
  exact ⟨_, _, by
    simpa [transferFromCallerWord] using evm_run rd556 with [
      jumpdest, push0, caller, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
      dup7, and, dup2, eq, dup1, iszero, swap1, push2 ⟨620⟩,
      jumpiT (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [hsenderClean, hsenderCaller]
        rw [transferFromCallerWord, approveOwnerWord, uInt256_eq_self]
        exact one_ne_zero_uint)
        (by jump_dest),
      jumpdest, iszero, push2 ⟨637⟩,
      jumpiT (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [hsenderClean, hsenderCaller]
        rw [transferFromCallerWord, approveOwnerWord, uInt256_eq_self]
        decide)
        (by jump_dest),
      jumpdest, push2 ⟨649⟩, dup7, dup7, dup7, dup7, push2 ⟨661⟩,
      jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_skipCaller_toUpdateHelper {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_skipCaller_toUpdate (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderCaller hreach
  exact ⟨_, _, evm_run rd661 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨707⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      exact hsenderNZ)
      (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push2 ⟨748⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonReceiver]
      exact hreceiverNZ)
      (by jump_dest),
    jumpdest, push2 ⟨760⟩, dup5, dup5, dup5, dup5, push2 ⟨1323⟩,
    jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_skipCaller_revert_sender_zero {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderZero : transferFromSenderWord I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_skipCaller_toUpdate (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderCaller hreach
  have rd676 := evm_run rd661 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨707⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [hsenderZero]
      decide) ]
  exact evm_run rd676 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x01486a41⟩, push1 ⟨231⟩, shl, dup2,
    raw mstore 6 (solcReturnMem transferFromInvalidSenderSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorMem transferFromInvalidSenderSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add,
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorMem_mload64 transferFromInvalidSenderSelectorWord ⟨0⟩)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_skipCaller_revert_receiver_zero {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverZero : transferFromReceiverWord I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_skipCaller_toUpdate (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderCaller hreach
  have rd722 := evm_run rd661 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨707⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      exact hsenderNZ)
      (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push2 ⟨748⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [hreceiverZero]
      decide) ]
  exact evm_run rd722 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x0b8bbd61⟩, push1 ⟨228⟩, shl, dup2,
    raw mstore 6 (solcReturnMem transferFromInvalidReceiverSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorMem transferFromInvalidReceiverSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorMem_mload64 transferFromInvalidReceiverSelectorWord ⟨0⟩)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_skipCaller_afterLoad {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1373⟩
      [transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromSenderWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_skipCaller_toUpdateHelper
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ hreach
  have hslot := transferFromSenderBalanceKeccakSlot I hcanonSender
  have hcallerWord : UInt256.ofNat ↑I.source = transferFromSenderWord I := by
    simpa [transferFromCallerWord, approveOwnerWord] using hsenderCaller.symm
  have rd1340 := evm_run rd1323 with [
    jumpdest, caller, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and,
    iszero, push2 ⟨1476⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      exact isZero_eq_zero_of_ne hsenderNZ) ]
  have rd1372 := evm_run rd1340 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and, push0, swap1, dup2,
    raw mstore 0 (approveWordAt0Mem (transferFromSenderWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (transferInnerHashMem (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup7, dup5,
    raw mstore 0 (approveWordAt0Mem (transferFromIdWord I)
        (transferInnerHashMem (transferFromSenderWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw keccak256 0 (transferOuterSlot (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  obtain ⟨k1, C1, rd1373₀⟩ := rd1372.sload (by decide) (by evm_ov)
  exact ⟨k1, C1, by
    simpa [transferFromSenderBalanceWord, transferFromSenderBalanceSlot,
      hslot, hcallerWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using rd1373₀⟩

theorem erc6909TransferFromX_skipCaller_afterRequire {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1437⟩
      [transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromSenderWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1373⟩ := erc6909TransferFromX_skipCaller_afterLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ hreach
  have hlt : UInt256.lt
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I)
      (transferFromAmountWord I) = ⟨0⟩ := ult_zero henough
  exact ⟨_, _, evm_run rd1373 with [
    dup3, dup2, lt, iszero, push2 ⟨1437⟩,
    jumpiT (by rw [hlt]; decide) (by jump_dest) ]⟩

theorem erc6909TransferFromX_skipCaller_insufficientTail {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (rd1373 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1373⟩
      [transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromSenderWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hltw : UInt256.lt
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I)
      (transferFromAmountWord I) = ⟨1⟩ := ult_one hlt
  have rd1381 := evm_run rd1373 with [
    dup3, dup2, lt, iszero, push2 ⟨1437⟩,
    jumpiNT (by rw [hltw]; decide) ]
  exact evm_run rd1381 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      (transferOuterHashMem_mload64 (transferFromSenderWord I) (transferFromIdWord I))
      (by decide) (by evm_ov),
    push4 ⟨0x02c6d3fb⟩, push1 ⟨230⟩, shl, dup2,
    raw mstore 6 (transferInsufficientBalanceSelectorMem (transferFromSenderWord I)
        (transferFromIdWord I))
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup8, and,
    push1 ⟨4⟩, dup3, add,
    raw mstore 3 (transferInsufficientBalanceSenderMem (transferFromSenderWord I)
        (transferFromIdWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, dup2, add, dup3, swap1,
    raw mstore 3 (transferInsufficientBalanceBalanceMem (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.ofNat 7) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨68⟩, dup2, add, dup5, swap1,
    raw mstore 3 (transferInsufficientBalanceAmountMem (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, dup2, add, dup6, swap1,
    raw mstore 3 (transferInsufficientBalanceIdMem (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 9) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨132⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide) mem_cost
      (transferInsufficientBalanceIdMem_mload64 (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromAmountWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_skipCaller_insufficient {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1373⟩ := erc6909TransferFromX_skipCaller_afterLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ hreach
  exact erc6909TransferFromX_skipCaller_insufficientTail hcanonSender hlt rd1373

theorem erc6909TransferFromX_skipCaller_afterDebit {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1476⟩
      [transferFromSenderWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd1437⟩ := erc6909TransferFromX_skipCaller_afterRequire
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ henough hreach
  have hslot := transferFromSenderBalanceKeccakSlot I hcanonSender
  have rd1451 := evm_run rd1437 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and,
    push0, swap1, dup2,
    raw mstore 0 (approveWordAt0Mem (transferFromSenderWord I)
        (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1456 := evm_run rd1451 with [
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩
        (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1461 := evm_run rd1456 with [
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferInnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩
                    (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
                  ).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((transferInnerHashMem (transferFromSenderWord I)).readWithPadding 0 64)))
        rw [approveTwoWordHashMem_read0_64 (transferFromSenderWord I) ⟨0⟩
          (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I)),
          transferInnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1468 := evm_run rd1461 with [
    dup8, dup5,
    raw mstore 0 (approveWordAt0Mem (transferFromIdWord I)
        (approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩
          (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0
      (transferMapScratchMem
        (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1470 := evm_run rd1468 with [
    swap1,
    raw keccak256 0 (transferOuterSlot (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferOuterSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferMapScratchMem
                    (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
                    (transferFromSenderWord I) (transferFromIdWord I)).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I)
                  ).readWithPadding 0 64)))
        rw [transferMapScratchMem_read0_64 (transferFromSenderWord I) (transferFromIdWord I)
          (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I)),
          transferOuterHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have hdebit :
      UInt256.sub
          (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I)
          (transferFromAmountWord I) =
        transferFromTailSenderDebitWord (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [usub_toNat henough]
    unfold transferFromTailSenderDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le
        (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat
        (transferFromAmountWord I).toNat)
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).val.isLt)]
  have rd1475₀ := evm_run rd1470 with [
    swap1, dup4, swap1, sub, swap1 ]
  have rd1475 := rd1475₀
  rw [hdebit, hslot] at rd1475
  obtain ⟨_, _, rd1476⟩ := rd1475.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, rd1476⟩

theorem erc6909TransferFromX_skipCaller_toCheckedAdd {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2017⟩
      [transferFromTailReceiverBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromAmountWord I, ⟨1539⟩, ⟨0⟩, transferFromReceiverBalanceSlot I,
        transferFromAmountWord I, transferFromSenderWord I, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨760⟩, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨649⟩,
        transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem
          (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
          (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd1476⟩ := erc6909TransferFromX_skipCaller_afterDebit
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hperm hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ henough hreach
  let debitMem :=
    transferMapScratchMem (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (transferFromSenderWord I) (transferFromIdWord I)
  have hdebitMemSize : debitMem.size = 96 := by
    dsimp [debitMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I)
      (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I))
  have hdebitMemRead64 :
      debitMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [debitMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I))
      (transferOuterHashMem_read64 (transferFromSenderWord I) (transferFromIdWord I))
  have hslot := transferFromReceiverBalanceKeccakSlot I hcanonReceiver
  have rd1492 := evm_run rd1476 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    iszero, push2 ⟨1545⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonReceiver]
      exact isZero_eq_zero_of_ne hreceiverNZ) ]
  have rd1505 := evm_run rd1492 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and, push0, swap1,
    dup2,
    raw mstore 0 (approveWordAt0Mem (transferFromReceiverWord I) debitMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonReceiver]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1510 := evm_run rd1505 with [
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (approveTwoWordHashMem (transferFromReceiverWord I) ⟨0⟩ debitMem)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1515 := evm_run rd1510 with [
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferFromReceiverWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferInnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((approveTwoWordHashMem (transferFromReceiverWord I) ⟨0⟩ debitMem
                  ).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferInnerHashMem (transferFromReceiverWord I)).readWithPadding 0 64)))
        rw [approveTwoWordHashMem_read0_64 (transferFromReceiverWord I) ⟨0⟩
          hdebitMemSize, transferInnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1522 := evm_run rd1515 with [
    dup7, dup5,
    raw mstore 0 (approveWordAt0Mem (transferFromIdWord I)
        (approveTwoWordHashMem (transferFromReceiverWord I) ⟨0⟩ debitMem))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (transferMapScratchMem debitMem (transferFromReceiverWord I)
        (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup2 ]
  have rd1524 := evm_run rd1522 with [
    raw keccak256 0 (transferOuterSlot (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferOuterSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferMapScratchMem debitMem (transferFromReceiverWord I)
                    (transferFromIdWord I)).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferOuterHashMem (transferFromReceiverWord I) (transferFromIdWord I)
                  ).readWithPadding 0 64)))
        rw [transferMapScratchMem_read0_64 (transferFromReceiverWord I)
          (transferFromIdWord I) hdebitMemSize, transferOuterHashMem_read0_64])
      (by decide) (by evm_ov),
    dup1 ]
  obtain ⟨k1, C1, rd1526₀⟩ := rd1524.sload (by decide) (by evm_ov)
  have rd1526 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1526⟩
      [transferFromTailReceiverBalanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromReceiverBalanceSlot I, ⟨0⟩, transferFromSenderWord I,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      (transferMapScratchMem debitMem (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σ σ₀ g A I) I)) k1 C1 := by
    simpa [transferFromTailReceiverBalanceWord, transferFromTailAfterSenderBalanceState,
      transferFromSenderBalanceSlot, hslot, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, storageStore_accountMap, debitMem]
      using rd1526₀
  exact ⟨_, _, evm_run rd1526 with [
    dup5, swap3, swap1, push2 ⟨1539⟩, swap1, dup5, swap1, push2 ⟨2017⟩,
    jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_skipCaller_afterCredit {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hfit : transferFromTailReceiverCreditNat (initState cA gh bl σ σ₀ g A I) I <
      UInt256.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1545⟩
      [transferFromSenderWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem
          (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
          (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromSenderBalanceSlot I)
          (transferFromTailSenderDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferFromReceiverBalanceSlot I)
        (transferFromTailReceiverCreditWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd2017⟩ := erc6909TransferFromX_skipCaller_toCheckedAdd
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hperm hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ henough hreach
  obtain ⟨_, _, rd1539₀⟩ := erc6909RoutineCheckedAdd rd2017
    (by simpa [transferFromTailReceiverCreditNat] using hfit)
    (by jump_dest) (by evm_ov)
  have hnew :
      transferFromTailReceiverBalanceWord (initState cA gh bl σ σ₀ g A I) I +
          transferFromAmountWord I =
        transferFromTailReceiverCreditWord (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt (by
      simpa [transferFromTailReceiverCreditNat] using hfit)]
    unfold transferFromTailReceiverCreditWord
    rw [ulit_toNat' _ hfit]
    rfl
  have rd1539 := rd1539₀
  rw [hnew] at rd1539
  have rd1542 := evm_run rd1539 with [
    jumpdest, swap1, swap2 ]
  obtain ⟨_, _, rd1543⟩ := rd1542.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1543 with [ pop, pop ]⟩

theorem erc6909TransferFromX_skipCaller_overflow {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hover : UInt256.size ≤
      transferFromTailReceiverCreditNat (initState cA gh bl σ σ₀ g A I) I)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2017⟩ := erc6909TransferFromX_skipCaller_toCheckedAdd
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hperm hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ henough hreach
  exact erc6909RoutineCheckedAdd_overflow rd2017
    (by simpa [transferFromTailReceiverCreditNat] using hover) (by evm_ov)

theorem erc6909TransferFromX_skipCaller_success {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderCaller : transferFromSenderWord I = transferFromCallerWord I)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hfit : transferFromTailReceiverCreditNat (initState cA gh bl σ σ₀ g A I) I <
      UInt256.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromSenderBalanceSlot I)
          (transferFromTailSenderDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferFromReceiverBalanceSlot I)
        (transferFromTailReceiverCreditWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd1545⟩ := erc6909TransferFromX_skipCaller_afterCredit
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hperm hcanonSender hcanonReceiver
    hsenderCaller hsenderNZ hreceiverNZ henough hfit hreach
  let debitMem :=
    transferMapScratchMem (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (transferFromSenderWord I) (transferFromIdWord I)
  let creditMem := transferMapScratchMem debitMem (transferFromReceiverWord I)
    (transferFromIdWord I)
  have hdebitMemSize : debitMem.size = 96 := by
    dsimp [debitMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I)
      (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I))
  have hdebitMemRead64 :
      debitMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [debitMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I))
      (transferOuterHashMem_read64 (transferFromSenderWord I) (transferFromIdWord I))
  have hcreditMemSize : creditMem.size = 96 := by
    dsimp [creditMem]
    exact transferMapScratchMem_size (transferFromReceiverWord I) (transferFromIdWord I)
      hdebitMemSize
  have hcreditMemRead64 :
      creditMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [creditMem]
    exact transferMapScratchMem_read64 (transferFromReceiverWord I) (transferFromIdWord I)
      hdebitMemSize hdebitMemRead64
  have rd1563 := evm_run rd1545 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (transferMapScratchMem_mload64 (transferFromReceiverWord I) (transferFromIdWord I)
        hdebitMemSize hdebitMemRead64)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, dup2, and, dup3,
    raw mstore 6 (transferEventFromBaseMem creditMem (transferFromSenderWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        change (UInt256.toByteArray (UInt256.land solcAddrMask (transferFromSenderWord I))).write 0
          creditMem 128 32 = transferEventFromBaseMem creditMem (transferFromSenderWord I)
        rw [solcAddrMask_clean_left hcanonSender]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1570 := evm_run rd1563 with [
    push1 ⟨32⟩, dup3, add, dup6, swap1,
    raw mstore 3 (transferEventBaseMem creditMem (transferFromSenderWord I)
        (transferFromAmountWord I))
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1573 := evm_run rd1570 with [dup6, swap3, dup2]
  have rd1574 := RD.erc6909Dup9 rd1573 (by decide) (by evm_ov)
  have rd1577 := evm_run rd1574 with [and, swap3, swap2]
  have rd1578 := RD.erc6909Dup10 rd1577 (by decide) (by evm_ov)
  have rd1580₀ := evm_run rd1578 with [and, swap2]
  have rd1580 := rd1580₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide,
    solcAddrMask_clean hcanonSender,
    solcAddrMask_clean hcanonReceiver] at rd1580
  have rd1613 := rd1580.pushConst transferTransferTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd1622 := evm_run rd1613 with [
    swap2, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferEventBaseMem_mload64 (transferFromSenderWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have rd1623 := RD.erc6909Log4 0 (UInt256.ofNat 6) rd1622 (by decide) hperm
    mem_cost (by decide) (by evm_ov)
  have rd760 := evm_run rd1623 with [
    pop, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd649 := evm_run rd760 with [
    jumpdest, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd651 := evm_run rd649 with [jumpdest, pop, push1 ⟨1⟩]
  have rd654 := RD.erc6909Swap6 rd651 (by decide) (by evm_ov)
  have rd655 := RD.erc6909Swap5 rd654 (by decide) (by evm_ov)
  have rd193 := evm_run rd655 with [
    pop, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd165 := evm_run rd193 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferEventBaseMem_mload64 (transferFromSenderWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 0 (transferReturnBaseMem creditMem (transferFromSenderWord I)
        (transferFromAmountWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨165⟩, jump (by jump_dest) ]
  exact evm_run rd165 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferReturnBaseMem_mload64 (transferFromSenderWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
            from by decide]
        exact transferReturnBaseMem_read128 (transferFromSenderWord I)
          (transferFromAmountWord I) hcreditMemSize)
      (by evm_ov) ]

theorem erc6909TransferFromX_operatorApproved_toUpdate {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hop : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd556⟩ := erc6909TransferFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hcanonReceiver hreach
  have hslot := transferFromOperatorKeccakSlot I hcanonSender
  have hsenderNeEq :
      ¬ UInt256.eq (transferFromSenderWord I) (transferFromCallerWord I) = ⟨1⟩ := by
    intro heq
    apply hsenderNe
    by_contra hne
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
      Bool.false_eq_true, ↓reduceIte] at heq
    exact absurd heq (by decide)
  have hcallerNeEq :
      ¬ UInt256.eq (transferFromCallerWord I) (transferFromSenderWord I) = ⟨1⟩ := by
    intro heq
    apply hsenderNe
    symm
    by_contra hne
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
      Bool.false_eq_true, ↓reduceIte] at heq
    exact absurd heq (by decide)
  have heq0 : UInt256.eq (transferFromSenderWord I) (transferFromCallerWord I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne hsenderNeEq
  have heq0Caller : UInt256.eq (transferFromCallerWord I) (transferFromSenderWord I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne hcallerNeEq
  have rd615pre := evm_run rd556 with [
    jumpdest, push0, caller, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup7, and, dup2, eq, dup1, iszero, swap1, push2 ⟨620⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      simpa [transferFromCallerWord, approveOwnerWord] using heq0Caller),
    pop, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup1, dup8, and, push0, swap1, dup2,
    raw mstore 0 (isOperatorOwnerMem (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 (isOperatorInnerHashMem (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (isOperatorInnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap4, dup6, and, dup4,
    raw mstore 0 (isOperatorSpenderMem (transferFromSenderWord I)
        (transferFromCallerWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean (transferFromCallerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov),
    swap3, swap1,
    raw mstore 0 (isOperatorOuterHashMem (transferFromSenderWord I)
        (transferFromCallerWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw keccak256 0 (transferFromOperatorSlotI I)
      (UInt256.ofNat 3) (by decide) mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨_, _, rd615⟩ := rd615pre.sload (by decide) (by evm_ov)
  have hopMaskRaw :
      UInt256.land ⟨255⟩
        (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
          (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
          (transferFromOperatorSlot (initState cA gh bl σ σ₀ g A I) I)) ≠ ⟨0⟩ := by
    rw [SimpleAuction.simpleAuctionU256_land_comm]
    exact hop
  have hopMask :
      UInt256.land ⟨255⟩
        (Option.option ⟨0⟩
          (fun ac => Batteries.RBMap.findD ac.storage (transferFromOperatorSlotI I) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner)) ≠ ⟨0⟩ := by
    simpa [transferFromOperatorSlot_init, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage] using hopMaskRaw
  exact ⟨_, _, by
    simpa [transferFromOperatorWord, transferFromOperatorSlot_init, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      evm_run rd615 with [
        push1 ⟨255⟩, and, iszero,
        jumpdest, iszero, push2 ⟨637⟩,
        jumpiT (by rw [isZero_eq_zero_of_ne hopMask]; decide) (by jump_dest),
        jumpdest, push2 ⟨649⟩, dup7, dup7, dup7, dup7, push2 ⟨661⟩,
        jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_operatorFalse_toAllowanceHelper {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1147⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromCallerWord I,
        transferFromSenderWord I, ⟨637⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd556⟩ := erc6909TransferFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hcanonReceiver hreach
  have hslot := transferFromOperatorKeccakSlot I hcanonSender
  have hsenderNeEq :
      ¬ UInt256.eq (transferFromSenderWord I) (transferFromCallerWord I) = ⟨1⟩ := by
    intro heq
    apply hsenderNe
    by_contra hne
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
      Bool.false_eq_true, ↓reduceIte] at heq
    exact absurd heq (by decide)
  have hcallerNeEq :
      ¬ UInt256.eq (transferFromCallerWord I) (transferFromSenderWord I) = ⟨1⟩ := by
    intro heq
    apply hsenderNe
    symm
    by_contra hne
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
      Bool.false_eq_true, ↓reduceIte] at heq
    exact absurd heq (by decide)
  have heq0Caller : UInt256.eq (transferFromCallerWord I) (transferFromSenderWord I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne hcallerNeEq
  have rd615pre := evm_run rd556 with [
    jumpdest, push0, caller, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup7, and, dup2, eq, dup1, iszero, swap1, push2 ⟨620⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      simpa [transferFromCallerWord, approveOwnerWord] using heq0Caller),
    pop, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup1, dup8, and, push0, swap1, dup2,
    raw mstore 0 (isOperatorOwnerMem (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 (isOperatorInnerHashMem (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (isOperatorInnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap4, dup6, and, dup4,
    raw mstore 0 (isOperatorSpenderMem (transferFromSenderWord I)
        (transferFromCallerWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean (transferFromCallerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov),
    swap3, swap1,
    raw mstore 0 (isOperatorOuterHashMem (transferFromSenderWord I)
        (transferFromCallerWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw keccak256 0 (transferFromOperatorSlotI I)
      (UInt256.ofNat 3) (by decide) mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨_, _, rd615⟩ := rd615pre.sload (by decide) (by evm_ov)
  have hopMaskRaw :
      UInt256.land ⟨255⟩
        (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
          (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
          (transferFromOperatorSlot (initState cA gh bl σ σ₀ g A I) I)) = ⟨0⟩ := by
    rw [SimpleAuction.simpleAuctionU256_land_comm]
    exact hopZero
  have hopMask :
      UInt256.land ⟨255⟩
        (Option.option ⟨0⟩
          (fun ac => Batteries.RBMap.findD ac.storage (transferFromOperatorSlotI I) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner)) = ⟨0⟩ := by
    simpa [transferFromOperatorSlot_init, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage] using hopMaskRaw
  exact ⟨_, _, by
    simpa [transferFromOperatorWord, transferFromOperatorSlot_init, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
      evm_run rd615 with [
        push1 ⟨255⟩, and, iszero,
        jumpdest, iszero, push2 ⟨637⟩,
        jumpiNT (by rw [hopMask]; decide),
        push2 ⟨637⟩, dup7, dup3, dup7, dup7, push2 ⟨1147⟩,
        jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_from1147_afterAllowanceLoad
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (rd1147 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1147⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromCallerWord I,
        transferFromSenderWord I, ⟨637⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1193⟩
      [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromAmountWord I, transferFromIdWord I, transferFromCallerWord I,
        transferFromSenderWord I, ⟨637⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (approveTwoWordHashMem (transferFromIdWord I)
        (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
        (approveTwoWordHashMem (transferFromCallerWord I)
          (approveOwnerSlot (transferFromSenderWord I))
          (approveTwoWordHashMem (transferFromSenderWord I) ⟨2⟩ base)))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let ownerMem := approveTwoWordHashMem (transferFromSenderWord I) ⟨2⟩ base
  let ownerKeyMem := approveWordAt0Mem (transferFromSenderWord I) base
  let spenderMem := approveTwoWordHashMem (transferFromCallerWord I)
    (approveOwnerSlot (transferFromSenderWord I)) ownerMem
  let spenderKeyMem := approveWordAt0Mem (transferFromCallerWord I) ownerMem
  let idMem := approveTwoWordHashMem (transferFromIdWord I)
    (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I)) spenderMem
  let idKeyMem := approveWordAt0Mem (transferFromIdWord I) spenderMem
  have hownerMemSize : ownerMem.size = 96 := by
    dsimp [ownerMem]
    exact approveTwoWordHashMem_size (transferFromSenderWord I) ⟨2⟩ hbase
  have hownerMemRead64 :
      ownerMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [ownerMem]
    exact approveTwoWordHashMem_read64 (transferFromSenderWord I) ⟨2⟩ hbase hread64
  have hspenderMemSize : spenderMem.size = 96 := by
    dsimp [spenderMem]
    exact approveTwoWordHashMem_size (transferFromCallerWord I)
      (approveOwnerSlot (transferFromSenderWord I)) hownerMemSize
  have hspenderMemRead64 :
      spenderMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [spenderMem]
    exact approveTwoWordHashMem_read64 (transferFromCallerWord I)
      (approveOwnerSlot (transferFromSenderWord I)) hownerMemSize hownerMemRead64
  have hidMemSize : idMem.size = 96 := by
    dsimp [idMem]
    exact approveTwoWordHashMem_size (transferFromIdWord I)
      (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
      hspenderMemSize
  have hslot := transferFromAllowanceKeccakSlot I hcanonSender
  have rd1175 := evm_run rd1147 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, dup2, and,
    push0, swap1, dup2,
    raw mstore 0 ownerKeyMem (UInt256.ofNat 3) (by decide) mem_cost
      (by
        dsimp [ownerKeyMem]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean_left hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨2⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 ownerMem (UInt256.ofNat 3) (by decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (approveOwnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold approveOwnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian (ffi.KEC (ownerMem.readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((approveOwnerHashMem (transferFromSenderWord I)).readWithPadding 0 64)))
        rw [show ownerMem.readWithPadding 0 64 =
            UInt256.toByteArray (transferFromSenderWord I) ++ UInt256.toByteArray ⟨2⟩ by
          dsimp [ownerMem]
          exact approveTwoWordHashMem_read0_64 (transferFromSenderWord I) ⟨2⟩ hbase]
        rw [approveOwnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1191 := evm_run rd1175 with [
    swap4, dup8, and, dup4,
    raw mstore 0 spenderKeyMem (UInt256.ofNat 3) (by decide) mem_cost
      (by
        dsimp [spenderKeyMem]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean (transferFromCallerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov),
    swap3, dup2,
    raw mstore 0 spenderMem (UInt256.ofNat 3) (by decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    dup3, dup3,
    raw keccak256 0 (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold approveSpenderSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian (ffi.KEC (spenderMem.readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((approveSpenderHashMem (transferFromSenderWord I)
                (transferFromCallerWord I)).readWithPadding 0 64)))
        rw [show spenderMem.readWithPadding 0 64 =
            UInt256.toByteArray (transferFromCallerWord I) ++
              UInt256.toByteArray (approveOwnerSlot (transferFromSenderWord I)) by
          dsimp [spenderMem]
          exact approveTwoWordHashMem_read0_64 (transferFromCallerWord I)
            (approveOwnerSlot (transferFromSenderWord I)) hownerMemSize]
        rw [approveSpenderHashMem_read0_64])
      (by decide) (by evm_ov),
    dup6, dup4,
    raw mstore 0 idKeyMem (UInt256.ofNat 3) (by decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    swap1,
    raw mstore 0 idMem (UInt256.ofNat 3) (by decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw keccak256 0 (transferFromAllowanceSlotI I)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        change UInt256.ofNat
            (fromByteArrayBigEndian (ffi.KEC (idMem.readWithPadding 0 64))) =
          transferFromAllowanceSlotI I
        rw [show idMem.readWithPadding 0 64 =
            UInt256.toByteArray (transferFromIdWord I) ++
              UInt256.toByteArray
                (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I)) by
          dsimp [idMem]
          exact approveTwoWordHashMem_read0_64 (transferFromIdWord I)
            (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
            hspenderMemSize]
        rw [← approveIdHashMem_read0_64 (transferFromSenderWord I) (transferFromCallerWord I)
          (transferFromIdWord I)]
        exact hslot)
      (by decide) (by evm_ov) ]
  obtain ⟨k1, C1, rd1193₀⟩ := rd1191.sload (by decide) (by evm_ov)
  exact ⟨k1, C1, by
    simpa [transferFromCurrentAllowanceWord, transferFromAllowanceSlot_init, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, idMem, idKeyMem,
      spenderMem, spenderKeyMem, ownerMem, ownerKeyMem]
      using rd1193₀⟩

noncomputable def transferFromAllowanceScratchMem (base : ByteArray)
    (I : ExecutionEnv) : ByteArray :=
  approveTwoWordHashMem (transferFromIdWord I)
    (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
    (approveTwoWordHashMem (transferFromCallerWord I)
      (approveOwnerSlot (transferFromSenderWord I))
      (approveTwoWordHashMem (transferFromSenderWord I) ⟨2⟩ base))

theorem transferFromAllowanceScratchMem_size {base : ByteArray} (I : ExecutionEnv)
    (hbase : base.size = 96) :
    (transferFromAllowanceScratchMem base I).size = 96 := by
  unfold transferFromAllowanceScratchMem
  exact approveTwoWordHashMem_size (transferFromIdWord I)
    (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
    (approveTwoWordHashMem_size (transferFromCallerWord I)
      (approveOwnerSlot (transferFromSenderWord I))
      (approveTwoWordHashMem_size (transferFromSenderWord I) ⟨2⟩ hbase))

theorem transferFromAllowanceScratchMem_read64 {base : ByteArray} (I : ExecutionEnv)
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferFromAllowanceScratchMem base I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromAllowanceScratchMem
  exact approveTwoWordHashMem_read64 (transferFromIdWord I)
    (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
    (approveTwoWordHashMem_size (transferFromCallerWord I)
      (approveOwnerSlot (transferFromSenderWord I))
      (approveTwoWordHashMem_size (transferFromSenderWord I) ⟨2⟩ hbase))
    (approveTwoWordHashMem_read64 (transferFromCallerWord I)
      (approveOwnerSlot (transferFromSenderWord I))
      (approveTwoWordHashMem_size (transferFromSenderWord I) ⟨2⟩ hbase)
      (approveTwoWordHashMem_read64 (transferFromSenderWord I) ⟨2⟩ hbase hread64))

noncomputable def transferFromOperatorAllowanceScratchMem (I : ExecutionEnv) : ByteArray :=
  transferFromAllowanceScratchMem
    (isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I)) I

theorem transferFromOperatorAllowanceScratchMem_size (I : ExecutionEnv) :
    (transferFromOperatorAllowanceScratchMem I).size = 96 := by
  unfold transferFromOperatorAllowanceScratchMem
  exact transferFromAllowanceScratchMem_size I
    (isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I))

theorem transferFromOperatorAllowanceScratchMem_read64 (I : ExecutionEnv) :
    (transferFromOperatorAllowanceScratchMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromOperatorAllowanceScratchMem
  exact transferFromAllowanceScratchMem_read64 I
    (isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I))
    (isOperatorOuterHashMem_read64 (transferFromSenderWord I) (transferFromCallerWord I))

theorem erc6909TransferFromX_from637_to661_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (rd637 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨637⟩
      [transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C := by
  exact ⟨_, _, evm_run rd637 with [
    jumpdest, push2 ⟨649⟩, dup7, dup7, dup7, dup7, push2 ⟨661⟩,
    jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_from1193_allowanceMax_to661_base
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (rd1193 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1193⟩
      [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromAmountWord I, transferFromIdWord I, transferFromCallerWord I,
        transferFromSenderWord I, ⟨637⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hmaxToNat :
      (UInt256.ofNat (UInt256.size - 1)).toNat = UInt256.size - 1 := by
    exact ulit_toNat' _ (by
      have hpos : 0 < UInt256.size := by norm_num [UInt256.size]
      exact Nat.sub_lt hpos (by decide))
  have hltMax :
      UInt256.lt
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
        (UInt256.lnot (⟨0⟩ : UInt256)) = ⟨0⟩ := by
    rw [uint256_lnot_zero_max]
    exact ult_zero (by simpa [hmaxToNat] using hallowanceMax)
  have rd637 := evm_run rd1193 with [
    push0, not, dup2, lt, iszero, push2 ⟨1316⟩,
    jumpiT (by rw [hltMax]; decide) (by jump_dest),
    jumpdest, pop, pop, pop, pop, pop, jump (by jump_dest) ]
  exact erc6909TransferFromX_from637_to661_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel) (base := base) rd637

theorem erc6909TransferFromX_from661_toUpdateHelper {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (rd661 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C := by
  exact ⟨_, _, evm_run rd661 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨707⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      exact hsenderNZ)
      (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push2 ⟨748⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonReceiver]
      exact hreceiverNZ)
      (by jump_dest),
    jumpdest, push2 ⟨760⟩, dup5, dup5, dup5, dup5, push2 ⟨1323⟩,
    jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_from661_revert_sender_zero {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderZero : transferFromSenderWord I = ⟨0⟩)
    (rd661 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd676 := evm_run rd661 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨707⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [hsenderZero]
      decide) ]
  exact evm_run rd676 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x01486a41⟩, push1 ⟨231⟩, shl, dup2,
    raw mstore 6 (solcReturnMem transferFromInvalidSenderSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorMem transferFromInvalidSenderSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add,
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorMem_mload64 transferFromInvalidSenderSelectorWord ⟨0⟩)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_from661_revert_receiver_zero {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverZero : transferFromReceiverWord I = ⟨0⟩)
    (rd661 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd722 := evm_run rd661 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨707⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      exact hsenderNZ)
      (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push2 ⟨748⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [hreceiverZero]
      decide) ]
  exact evm_run rd722 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x0b8bbd61⟩, push1 ⟨228⟩, shl, dup2,
    raw mstore 6 (solcReturnMem transferFromInvalidReceiverSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorMem transferFromInvalidReceiverSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorMem_mload64 transferFromInvalidReceiverSelectorWord ⟨0⟩)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_from661_toUpdateHelper_base {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ} {base : ByteArray}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (rd661 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C := by
  exact ⟨_, _, evm_run rd661 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨707⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      exact hsenderNZ)
      (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push2 ⟨748⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonReceiver]
      exact hreceiverNZ)
      (by jump_dest),
    jumpdest, push2 ⟨760⟩, dup5, dup5, dup5, dup5, push2 ⟨1323⟩,
    jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_from1193_allowanceMax_to1323_base
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (rd1193 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1193⟩
      [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromAmountWord I, transferFromIdWord I, transferFromCallerWord I,
        transferFromSenderWord I, ⟨637⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_from1193_allowanceMax_to661_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) (sel := sel) (base := base) hallowanceMax rd1193
  exact erc6909TransferFromX_from661_toUpdateHelper_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel) (base := base) hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ rd661

set_option maxHeartbeats 2000000 in
theorem erc6909TransferFromX_from1193_allowanceDebit_to661_base
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hallowanceNotMax :
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
        UInt256.size - 1)
    (hallowanceEnough : (transferFromAmountWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (rd1193 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1193⟩
      [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromAmountWord I, transferFromIdWord I, transferFromCallerWord I,
        transferFromSenderWord I, ⟨637⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferFromAllowanceScratchMem base I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
        (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  let ownerMem := approveTwoWordHashMem (transferFromSenderWord I) ⟨2⟩ base
  let ownerKeyMem := approveWordAt0Mem (transferFromSenderWord I) base
  let spenderMem := approveTwoWordHashMem (transferFromCallerWord I)
    (approveOwnerSlot (transferFromSenderWord I)) ownerMem
  let spenderKeyMem := approveWordAt0Mem (transferFromCallerWord I) ownerMem
  let idMem := transferFromAllowanceScratchMem base I
  let idKeyMem := approveWordAt0Mem (transferFromIdWord I) spenderMem
  have hownerMemSize : ownerMem.size = 96 := by
    dsimp [ownerMem]
    exact approveTwoWordHashMem_size (transferFromSenderWord I) ⟨2⟩ hbase
  have hspenderMemSize : spenderMem.size = 96 := by
    dsimp [spenderMem]
    exact approveTwoWordHashMem_size (transferFromCallerWord I)
      (approveOwnerSlot (transferFromSenderWord I)) hownerMemSize
  have hmaxToNat :
      (UInt256.ofNat (UInt256.size - 1)).toNat = UInt256.size - 1 := by
    exact ulit_toNat' _ (by
      have hpos : 0 < UInt256.size := by norm_num [UInt256.size]
      exact Nat.sub_lt hpos (by decide))
  have hltMax :
      UInt256.lt
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
        (UInt256.lnot (⟨0⟩ : UInt256)) = ⟨1⟩ := by
    rw [uint256_lnot_zero_max]
    exact ult_one (by simpa [hmaxToNat] using hallowanceNotMax)
  have hltAmount :
      UInt256.lt
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromAmountWord I) = ⟨0⟩ := ult_zero hallowanceEnough
  have hslot := transferFromAllowanceKeccakSlot I hcanonSender
  have rd1202 := evm_run rd1193 with [
    push0, not, dup2, lt, iszero, push2 ⟨1316⟩,
    jumpiNT (by rw [hltMax]; decide) ]
  have rd1266 := evm_run rd1202 with [
    dup2, dup2, lt, iszero, push2 ⟨1266⟩,
    jumpiT (by rw [hltAmount]; decide) (by jump_dest) ]
  have rd1294 := evm_run rd1266 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup7, and,
    push0, swap1, dup2,
    raw mstore 0 ownerKeyMem (UInt256.ofNat 3) (by decide) mem_cost
      (by
        dsimp [ownerKeyMem]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨2⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 ownerMem (UInt256.ofNat 3) (by decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (approveOwnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold approveOwnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian (ffi.KEC (ownerMem.readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((approveOwnerHashMem (transferFromSenderWord I)).readWithPadding 0 64)))
        rw [show ownerMem.readWithPadding 0 64 =
            UInt256.toByteArray (transferFromSenderWord I) ++ UInt256.toByteArray ⟨2⟩ by
          dsimp [ownerMem]
          exact approveTwoWordHashMem_read0_64 (transferFromSenderWord I) ⟨2⟩ hbase]
        rw [approveOwnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1295 := evm_run rd1294 with [swap4]
  have rd1296 := RD.erc6909Dup9 rd1295 (by decide) (by evm_ov)
  have rd1310 := evm_run rd1296 with [
    and, dup4,
    raw mstore 0 spenderKeyMem (UInt256.ofNat 3) (by decide) mem_cost
      (by
        dsimp [spenderKeyMem]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean (transferFromCallerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov),
    swap3, dup2,
    raw mstore 0 spenderMem (UInt256.ofNat 3) (by decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    dup3, dup3,
    raw keccak256 0 (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold approveSpenderSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian (ffi.KEC (spenderMem.readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((approveSpenderHashMem (transferFromSenderWord I)
                (transferFromCallerWord I)).readWithPadding 0 64)))
        rw [show spenderMem.readWithPadding 0 64 =
            UInt256.toByteArray (transferFromCallerWord I) ++
              UInt256.toByteArray (approveOwnerSlot (transferFromSenderWord I)) by
          dsimp [spenderMem]
          exact approveTwoWordHashMem_read0_64 (transferFromCallerWord I)
            (approveOwnerSlot (transferFromSenderWord I)) hownerMemSize]
        rw [approveSpenderHashMem_read0_64])
      (by decide) (by evm_ov),
    dup7, dup4,
    raw mstore 0 idKeyMem (UInt256.ofNat 3) (by decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    swap1,
    raw mstore 0 idMem (UInt256.ofNat 3) (by decide) mem_cost
      (by
        dsimp [idMem, transferFromAllowanceScratchMem]
        rfl)
      (by decide) (by evm_ov),
    raw keccak256 0 (transferFromAllowanceSlotI I)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        change UInt256.ofNat
            (fromByteArrayBigEndian (ffi.KEC (idMem.readWithPadding 0 64))) =
          transferFromAllowanceSlotI I
        rw [show idMem.readWithPadding 0 64 =
            UInt256.toByteArray (transferFromIdWord I) ++
              UInt256.toByteArray
                (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I)) by
          dsimp [idMem, transferFromAllowanceScratchMem]
          exact approveTwoWordHashMem_read0_64 (transferFromIdWord I)
            (approveSpenderSlot (transferFromSenderWord I) (transferFromCallerWord I))
            hspenderMemSize]
        rw [← approveIdHashMem_read0_64 (transferFromSenderWord I) (transferFromCallerWord I)
          (transferFromIdWord I)]
        exact hslot)
      (by decide) (by evm_ov) ]
  have hdebit :
      UInt256.sub
          (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
          (transferFromAmountWord I) =
        transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [usub_toNat hallowanceEnough]
    unfold transferFromAllowanceDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat
        (transferFromAmountWord I).toNat)
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).val.isLt)]
  have rd1315₀ := evm_run rd1310 with [dup3, dup3, sub, swap1]
  have rd1315 := rd1315₀
  rw [hdebit] at rd1315
  obtain ⟨_, _, rd1316⟩ := rd1315.sstore hperm (by decide) (by evm_ov)
  have rd637 := evm_run rd1316 with [
    jumpdest, pop, pop, pop, pop, pop, jump (by jump_dest) ]
  exact erc6909TransferFromX_from637_to661_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (σcur := sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
      (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I))
    (A := A) (g := g) (sel := sel) (base := transferFromAllowanceScratchMem base I)
    rd637

#exit

theorem erc6909TransferFromX_operatorFalse_afterAllowanceLoad
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1193⟩
      [transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromAmountWord I, transferFromIdWord I, transferFromCallerWord I,
        transferFromSenderWord I, ⟨637⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferFromOperatorAllowanceScratchMem I)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  let base := isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I)
  have hbase : base.size = 96 := by
    dsimp [base]
    exact isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I)
  have hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [base]
    exact isOperatorOuterHashMem_read64 (transferFromSenderWord I) (transferFromCallerWord I)
  obtain ⟨_, _, rd1147⟩ := erc6909TransferFromX_operatorFalse_toAllowanceHelper
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hreach
  obtain ⟨k1, C1, rd1193⟩ := erc6909TransferFromX_from1147_afterAllowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) (base := base) hbase hread64 hcanonSender rd1147
  exact ⟨k1, C1, by
    simpa [base, transferFromOperatorAllowanceScratchMem, transferFromAllowanceScratchMem]
      using rd1193⟩

theorem erc6909TransferFromX_operatorFalse_allowanceMax_to661
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferFromOperatorAllowanceScratchMem I)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1193⟩ := erc6909TransferFromX_operatorFalse_afterAllowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hreach
  exact erc6909TransferFromX_from1193_allowanceMax_to661_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) (sel := sel)
    (base := transferFromOperatorAllowanceScratchMem I)
    hallowanceMax rd1193

theorem erc6909TransferFromX_operatorFalse_allowanceMax_to1323
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      (transferFromOperatorAllowanceScratchMem I)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorFalse_allowanceMax_to661
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hallowanceMax hreach
  exact erc6909TransferFromX_from661_toUpdateHelper_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel)
    (base := transferFromOperatorAllowanceScratchMem I)
    hcanonSender hcanonReceiver hsenderNZ hreceiverNZ rd661

theorem erc6909TransferFromX_from661_revert_sender_zero_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hsenderZero : transferFromSenderWord I = ⟨0⟩)
    (rd661 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd676 := evm_run rd661 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨707⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [hsenderZero]
      decide) ]
  exact evm_run rd676 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (erc6909ScratchMem_mload64 hbase hread64) (by decide) (by evm_ov),
    push4 ⟨0x01486a41⟩, push1 ⟨231⟩, shl, dup2,
    raw mstore 6 (solcReturnBaseMem base transferFromInvalidSenderSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorBaseMem base transferFromInvalidSenderSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add,
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorBaseMem_mload64 transferFromInvalidSenderSelectorWord ⟨0⟩
        hbase hread64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_from661_revert_receiver_zero_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverZero : transferFromReceiverWord I = ⟨0⟩)
    (rd661 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨661⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd722 := evm_run rd661 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨707⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      exact hsenderNZ)
      (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push2 ⟨748⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [hreceiverZero]
      decide) ]
  exact evm_run rd722 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (erc6909ScratchMem_mload64 hbase hread64) (by decide) (by evm_ov),
    push4 ⟨0x0b8bbd61⟩, push1 ⟨228⟩, shl, dup2,
    raw mstore 6 (solcReturnBaseMem base transferFromInvalidReceiverSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorBaseMem base transferFromInvalidReceiverSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorBaseMem_mload64 transferFromInvalidReceiverSelectorWord ⟨0⟩
        hbase hread64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_from1323_afterLoad {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1373⟩
      [transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C := by
  have hslot := transferFromSenderBalanceKeccakSlot I hcanonSender
  have rd1340 := evm_run rd1323 with [
    jumpdest, caller, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and,
    iszero, push2 ⟨1476⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      exact isZero_eq_zero_of_ne hsenderNZ) ]
  have rd1372 := evm_run rd1340 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and, push0, swap1, dup2,
    raw mstore 0 (approveWordAt0Mem (transferFromSenderWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (transferInnerHashMem (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup7, dup5,
    raw mstore 0 (approveWordAt0Mem (transferFromIdWord I)
        (transferInnerHashMem (transferFromSenderWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw keccak256 0 (transferOuterSlot (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  obtain ⟨k1, C1, rd1373₀⟩ := rd1372.sload (by decide) (by evm_ov)
  exact ⟨k1, C1, by
    simpa [transferFromSenderBalanceWord, transferFromSenderBalanceSlot,
      hslot, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using rd1373₀⟩

theorem erc6909TransferFromX_from1323_afterRequire {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1437⟩
      [transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C := by
  obtain ⟨_, _, rd1373⟩ := erc6909TransferFromX_from1323_afterLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hcanonSender hsenderNZ rd1323
  have hlt : UInt256.lt
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
      (transferFromAmountWord I) = ⟨0⟩ := ult_zero henough
  exact ⟨_, _, evm_run rd1373 with [
    dup3, dup2, lt, iszero, push2 ⟨1437⟩,
    jumpiT (by rw [hlt]; decide) (by jump_dest) ]⟩

theorem erc6909TransferFromX_from1373_insufficient {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (rd1373 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1373⟩
      [transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hltw : UInt256.lt
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
      (transferFromAmountWord I) = ⟨1⟩ := ult_one hlt
  have rd1381 := evm_run rd1373 with [
    dup3, dup2, lt, iszero, push2 ⟨1437⟩,
    jumpiNT (by rw [hltw]; decide) ]
  exact evm_run rd1381 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      (transferOuterHashMem_mload64 (transferFromSenderWord I) (transferFromIdWord I))
      (by decide) (by evm_ov),
    push4 ⟨0x02c6d3fb⟩, push1 ⟨230⟩, shl, dup2,
    raw mstore 6 (transferInsufficientBalanceSelectorMem (transferFromSenderWord I)
        (transferFromIdWord I))
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup8, and,
    push1 ⟨4⟩, dup3, add,
    raw mstore 3 (transferInsufficientBalanceSenderMem (transferFromSenderWord I)
        (transferFromIdWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, dup2, add, dup3, swap1,
    raw mstore 3 (transferInsufficientBalanceBalanceMem (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I))
      (UInt256.ofNat 7) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨68⟩, dup2, add, dup5, swap1,
    raw mstore 3 (transferInsufficientBalanceAmountMem (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, dup2, add, dup6, swap1,
    raw mstore 3 (transferInsufficientBalanceIdMem (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 9) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨132⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide) mem_cost
      (transferInsufficientBalanceIdMem_mload64 (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
        (transferFromAmountWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_from1323_insufficient {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1373⟩ := erc6909TransferFromX_from1323_afterLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hcanonSender hsenderNZ rd1323
  exact erc6909TransferFromX_from1373_insufficient hcanonSender hlt rd1373

theorem erc6909TransferFromX_from1323_afterLoad_base {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ} {base : ByteArray}
    (hbase : base.size = 96)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1373⟩
      [transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C := by
  have hslot := transferFromSenderBalanceKeccakSlot I hcanonSender
  have rd1340 := evm_run rd1323 with [
    jumpdest, caller, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and,
    iszero, push2 ⟨1476⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSender]
      exact isZero_eq_zero_of_ne hsenderNZ) ]
  have rd1372 := evm_run rd1340 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and, push0, swap1, dup2,
    raw mstore 0 (approveWordAt0Mem (transferFromSenderWord I) base)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩ base)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferInnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩ base
                  ).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((transferInnerHashMem (transferFromSenderWord I)).readWithPadding 0 64)))
        rw [approveTwoWordHashMem_read0_64 (transferFromSenderWord I) ⟨0⟩ hbase,
          transferInnerHashMem_read0_64])
      (by decide) (by evm_ov),
    dup7, dup5,
    raw mstore 0 (approveWordAt0Mem (transferFromIdWord I)
        (approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩ base))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (transferMapScratchMem base (transferFromSenderWord I)
        (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw keccak256 0 (transferOuterSlot (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferOuterSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferMapScratchMem base (transferFromSenderWord I)
                    (transferFromIdWord I)).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I)
                  ).readWithPadding 0 64)))
        rw [transferMapScratchMem_read0_64 (transferFromSenderWord I)
          (transferFromIdWord I) hbase, transferOuterHashMem_read0_64])
      (by decide) (by evm_ov) ]
  obtain ⟨k1, C1, rd1373₀⟩ := rd1372.sload (by decide) (by evm_ov)
  exact ⟨k1, C1, by
    simpa [transferFromSenderBalanceWord, transferFromSenderBalanceSlot,
      hslot, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using rd1373₀⟩

theorem erc6909TransferFromX_from1323_afterRequire_base {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ} {base : ByteArray}
    (hbase : base.size = 96)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1437⟩
      [transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C := by
  obtain ⟨_, _, rd1373⟩ := erc6909TransferFromX_from1323_afterLoad_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hbase hcanonSender hsenderNZ rd1323
  have hlt : UInt256.lt
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
      (transferFromAmountWord I) = ⟨0⟩ := ult_zero henough
  exact ⟨_, _, evm_run rd1373 with [
    dup3, dup2, lt, iszero, push2 ⟨1437⟩,
    jumpiT (by rw [hlt]; decide) (by jump_dest) ]⟩

theorem erc6909TransferFromX_from1373_insufficient_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (rd1373 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1373⟩
      [transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let senderMem := transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I)
  have hsenderMemSize : senderMem.size = 96 := by
    dsimp [senderMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I) hbase
  have hsenderMemRead64 :
      senderMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [senderMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      hbase hread64
  have hltw : UInt256.lt
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
      (transferFromAmountWord I) = ⟨1⟩ := ult_one hlt
  have rd1381 := evm_run rd1373 with [
    dup3, dup2, lt, iszero, push2 ⟨1437⟩,
    jumpiNT (by rw [hltw]; decide) ]
  exact evm_run rd1381 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      (transferMapScratchMem_mload64 (transferFromSenderWord I) (transferFromIdWord I)
        hbase hread64)
      (by decide) (by evm_ov),
    push4 ⟨0x02c6d3fb⟩, push1 ⟨230⟩, shl, dup2,
    raw mstore 6 (transferInsufficientBalanceSelectorBaseMem senderMem)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup8, and,
    push1 ⟨4⟩, dup3, add,
    raw mstore 3 (transferInsufficientBalanceSenderBaseMem senderMem
        (transferFromSenderWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, dup2, add, dup3, swap1,
    raw mstore 3 (transferInsufficientBalanceBalanceBaseMem senderMem
        (transferFromSenderWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I))
      (UInt256.ofNat 7) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨68⟩, dup2, add, dup5, swap1,
    raw mstore 3 (transferInsufficientBalanceAmountBaseMem senderMem
        (transferFromSenderWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, dup2, add, dup6, swap1,
    raw mstore 3 (transferInsufficientBalanceIdBaseMem senderMem
        (transferFromSenderWord I) (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 9) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨132⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide) mem_cost
      (transferInsufficientBalanceIdBaseMem_mload64 (transferFromSenderWord I)
        (transferFromIdWord I)
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
        (transferFromAmountWord I) hsenderMemSize hsenderMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_from1323_insufficient_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1373⟩ := erc6909TransferFromX_from1323_afterLoad_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hbase hcanonSender hsenderNZ rd1323
  exact erc6909TransferFromX_from1373_insufficient_base
    hbase hread64 hcanonSender hlt rd1373

theorem erc6909TransferFromX_from1323_afterDebit {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1476⟩
      [transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd1437⟩ := erc6909TransferFromX_from1323_afterRequire
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hcanonSender hsenderNZ henough rd1323
  have hslot := transferFromSenderBalanceKeccakSlot I hcanonSender
  have rd1451 := evm_run rd1437 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and,
    push0, swap1, dup2,
    raw mstore 0 (approveWordAt0Mem (transferFromSenderWord I)
        (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1456 := evm_run rd1451 with [
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩
        (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1461 := evm_run rd1456 with [
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferInnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩
                    (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
                  ).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((transferInnerHashMem (transferFromSenderWord I)).readWithPadding 0 64)))
        rw [approveTwoWordHashMem_read0_64 (transferFromSenderWord I) ⟨0⟩
          (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I)),
          transferInnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1468 := evm_run rd1461 with [
    dup8, dup5,
    raw mstore 0 (approveWordAt0Mem (transferFromIdWord I)
        (approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩
          (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0
      (transferMapScratchMem
        (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1470 := evm_run rd1468 with [
    swap1,
    raw keccak256 0 (transferOuterSlot (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferOuterSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferMapScratchMem
                    (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
                    (transferFromSenderWord I) (transferFromIdWord I)).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I)
                  ).readWithPadding 0 64)))
        rw [transferMapScratchMem_read0_64 (transferFromSenderWord I) (transferFromIdWord I)
          (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I)),
          transferOuterHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have hdebit :
      UInt256.sub
          (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
          (transferFromAmountWord I) =
        transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I := by
    apply u256_inj
    rw [usub_toNat henough]
    unfold transferFromTailSenderDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat
        (transferFromAmountWord I).toNat)
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).val.isLt)]
  have rd1475₀ := evm_run rd1470 with [
    swap1, dup4, swap1, sub, swap1 ]
  have rd1475 := rd1475₀
  rw [hdebit, hslot] at rd1475
  obtain ⟨_, _, rd1476⟩ := rd1475.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, rd1476⟩

theorem erc6909TransferFromX_from1323_toCheckedAdd {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2017⟩
      [transferFromTailReceiverBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromAmountWord I, ⟨1539⟩, ⟨0⟩, transferFromReceiverBalanceSlot I,
        transferFromAmountWord I, transferFromCallerWord I, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨760⟩, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨649⟩,
        transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem
          (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
          (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd1476⟩ := erc6909TransferFromX_from1323_afterDebit
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hperm hcanonSender hsenderNZ henough rd1323
  let debitMem :=
    transferMapScratchMem (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (transferFromSenderWord I) (transferFromIdWord I)
  have hdebitMemSize : debitMem.size = 96 := by
    dsimp [debitMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I)
      (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I))
  have hdebitMemRead64 :
      debitMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [debitMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I))
      (transferOuterHashMem_read64 (transferFromSenderWord I) (transferFromIdWord I))
  have hslot := transferFromReceiverBalanceKeccakSlot I hcanonReceiver
  have rd1492 := evm_run rd1476 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    iszero, push2 ⟨1545⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonReceiver]
      exact isZero_eq_zero_of_ne hreceiverNZ) ]
  have rd1505 := evm_run rd1492 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and, push0, swap1,
    dup2,
    raw mstore 0 (approveWordAt0Mem (transferFromReceiverWord I) debitMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonReceiver]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1510 := evm_run rd1505 with [
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (approveTwoWordHashMem (transferFromReceiverWord I) ⟨0⟩ debitMem)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1515 := evm_run rd1510 with [
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferFromReceiverWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferInnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((approveTwoWordHashMem (transferFromReceiverWord I) ⟨0⟩ debitMem
                  ).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferInnerHashMem (transferFromReceiverWord I)).readWithPadding 0 64)))
        rw [approveTwoWordHashMem_read0_64 (transferFromReceiverWord I) ⟨0⟩
          hdebitMemSize, transferInnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1522 := evm_run rd1515 with [
    dup7, dup5,
    raw mstore 0 (approveWordAt0Mem (transferFromIdWord I)
        (approveTwoWordHashMem (transferFromReceiverWord I) ⟨0⟩ debitMem))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (transferMapScratchMem debitMem (transferFromReceiverWord I)
        (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup2 ]
  have rd1524 := evm_run rd1522 with [
    raw keccak256 0 (transferOuterSlot (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferOuterSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferMapScratchMem debitMem (transferFromReceiverWord I)
                    (transferFromIdWord I)).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferOuterHashMem (transferFromReceiverWord I) (transferFromIdWord I)
                  ).readWithPadding 0 64)))
        rw [transferMapScratchMem_read0_64 (transferFromReceiverWord I)
          (transferFromIdWord I) hdebitMemSize, transferOuterHashMem_read0_64])
      (by decide) (by evm_ov),
    dup1 ]
  obtain ⟨k1, C1, rd1526₀⟩ := rd1524.sload (by decide) (by evm_ov)
  have rd1526 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1526⟩
      [transferFromTailReceiverBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromReceiverBalanceSlot I, ⟨0⟩, transferFromCallerWord I,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      (transferMapScratchMem debitMem (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I)) k1 C1 := by
    simpa [transferFromTailReceiverBalanceWord, transferFromTailAfterSenderBalanceState,
      transferFromSenderBalanceSlot, hslot, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, storageStore_accountMap, debitMem]
      using rd1526₀
  exact ⟨_, _, evm_run rd1526 with [
    dup5, swap3, swap1, push2 ⟨1539⟩, swap1, dup5, swap1, push2 ⟨2017⟩,
    jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_from1545_successCaller_mem {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (rd1545 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1545⟩
      [transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      mem
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σcur)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  let creditMem := mem
  have hcreditMemSize : creditMem.size = 96 := by
    simpa [creditMem] using hmemSize
  have hcreditMemRead64 :
      creditMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [creditMem] using hmemRead64
  have rd1563 := evm_run rd1545 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (erc6909ScratchMem_mload64 hmemSize hmemRead64)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, dup2, and, dup3,
    raw mstore 6 (transferEventFromBaseMem creditMem (transferFromCallerWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        change (UInt256.toByteArray (UInt256.land solcAddrMask (transferFromCallerWord I))).write 0
          creditMem 128 32 = transferEventFromBaseMem creditMem (transferFromCallerWord I)
        rw [solcAddrMask_clean_left (transferFromCallerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1570 := evm_run rd1563 with [
    push1 ⟨32⟩, dup3, add, dup6, swap1,
    raw mstore 3 (transferEventBaseMem creditMem (transferFromCallerWord I)
        (transferFromAmountWord I))
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1573 := evm_run rd1570 with [dup6, swap3, dup2]
  have rd1574 := RD.erc6909Dup9 rd1573 (by decide) (by evm_ov)
  have rd1577 := evm_run rd1574 with [and, swap3, swap2]
  have rd1578 := RD.erc6909Dup10 rd1577 (by decide) (by evm_ov)
  have rd1580₀ := evm_run rd1578 with [and, swap2]
  have rd1580 := rd1580₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide,
    solcAddrMask_clean hcanonSender,
    solcAddrMask_clean hcanonReceiver] at rd1580
  have rd1613 := rd1580.pushConst transferTransferTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd1622 := evm_run rd1613 with [
    swap2, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferEventBaseMem_mload64 (transferFromCallerWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have rd1623 := RD.erc6909Log4 0 (UInt256.ofNat 6) rd1622 (by decide) hperm
    mem_cost (by decide) (by evm_ov)
  have rd760 := evm_run rd1623 with [
    pop, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd649 := evm_run rd760 with [
    jumpdest, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd651 := evm_run rd649 with [jumpdest, pop, push1 ⟨1⟩]
  have rd654 := RD.erc6909Swap6 rd651 (by decide) (by evm_ov)
  have rd655 := RD.erc6909Swap5 rd654 (by decide) (by evm_ov)
  have rd193 := evm_run rd655 with [
    pop, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd165 := evm_run rd193 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferEventBaseMem_mload64 (transferFromCallerWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 0 (transferReturnBaseMem creditMem (transferFromCallerWord I)
        (transferFromAmountWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨165⟩, jump (by jump_dest) ]
  exact evm_run rd165 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferReturnBaseMem_mload64 (transferFromCallerWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
            from by decide]
        exact transferReturnBaseMem_read128 (transferFromCallerWord I)
          (transferFromAmountWord I) hcreditMemSize)
      (by evm_ov) ]

theorem erc6909TransferFromX_from1545_successCaller {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (rd1545 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1545⟩
      [transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem
          (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
          (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σcur)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  let debitMem :=
    transferMapScratchMem (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
      (transferFromSenderWord I) (transferFromIdWord I)
  let creditMem := transferMapScratchMem debitMem (transferFromReceiverWord I)
    (transferFromIdWord I)
  have hdebitMemSize : debitMem.size = 96 := by
    dsimp [debitMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I)
      (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I))
  have hdebitMemRead64 :
      debitMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [debitMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      (transferOuterHashMem_size (transferFromSenderWord I) (transferFromIdWord I))
      (transferOuterHashMem_read64 (transferFromSenderWord I) (transferFromIdWord I))
  have hcreditMemSize : creditMem.size = 96 := by
    dsimp [creditMem]
    exact transferMapScratchMem_size (transferFromReceiverWord I) (transferFromIdWord I)
      hdebitMemSize
  have hcreditMemRead64 :
      creditMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [creditMem]
    exact transferMapScratchMem_read64 (transferFromReceiverWord I) (transferFromIdWord I)
      hdebitMemSize hdebitMemRead64
  exact erc6909TransferFromX_from1545_successCaller_mem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) (mem := creditMem) hcreditMemSize hcreditMemRead64 hperm hcanonSender
    hcanonReceiver (by simpa [debitMem, creditMem] using rd1545)

theorem erc6909TransferFromX_from1323_afterCredit {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (hfit : transferFromTailReceiverCreditNat (initState cA gh bl σcur σ₀ g A I) I <
      UInt256.size)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1545⟩
      [transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem
          (transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I))
          (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
          (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I))
        (transferFromReceiverBalanceSlot I)
        (transferFromTailReceiverCreditWord (initState cA gh bl σcur σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd2017⟩ := erc6909TransferFromX_from1323_toCheckedAdd
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough rd1323
  obtain ⟨_, _, rd1539₀⟩ := erc6909RoutineCheckedAdd rd2017
    (by simpa [transferFromTailReceiverCreditNat] using hfit)
    (by jump_dest) (by evm_ov)
  have hnew :
      transferFromTailReceiverBalanceWord (initState cA gh bl σcur σ₀ g A I) I +
          transferFromAmountWord I =
        transferFromTailReceiverCreditWord (initState cA gh bl σcur σ₀ g A I) I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt (by
      simpa [transferFromTailReceiverCreditNat] using hfit)]
    unfold transferFromTailReceiverCreditWord
    rw [ulit_toNat' _ hfit]
    rfl
  have rd1539 := rd1539₀
  rw [hnew] at rd1539
  have rd1542 := evm_run rd1539 with [
    jumpdest, swap1, swap2 ]
  obtain ⟨_, _, rd1543⟩ := rd1542.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1543 with [ pop, pop ]⟩

theorem erc6909TransferFromX_from1323_overflow {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (hover : UInt256.size ≤
      transferFromTailReceiverCreditNat (initState cA gh bl σcur σ₀ g A I) I)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2017⟩ := erc6909TransferFromX_from1323_toCheckedAdd
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough rd1323
  exact erc6909RoutineCheckedAdd_overflow rd2017
    (by simpa [transferFromTailReceiverCreditNat] using hover) (by evm_ov)

theorem erc6909TransferFromX_from1323_successCaller {cA gh bl σ σ₀ σcur A I}
    {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (hfit : transferFromTailReceiverCreditNat (initState cA gh bl σcur σ₀ g A I) I <
      UInt256.size)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
          (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I))
        (transferFromReceiverBalanceSlot I)
        (transferFromTailReceiverCreditWord (initState cA gh bl σcur σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd1545⟩ := erc6909TransferFromX_from1323_afterCredit
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough hfit rd1323
  exact erc6909TransferFromX_from1545_successCaller hperm hcanonSender hcanonReceiver rd1545

theorem erc6909TransferFromX_from1323_afterDebit_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1476⟩
      [transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd1437⟩ := erc6909TransferFromX_from1323_afterRequire_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hbase hcanonSender hsenderNZ henough rd1323
  let senderMem := transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I)
  have hsenderMemSize : senderMem.size = 96 := by
    dsimp [senderMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I) hbase
  have hslot := transferFromSenderBalanceKeccakSlot I hcanonSender
  have rd1451 := evm_run rd1437 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and,
    push0, swap1, dup2,
    raw mstore 0 (approveWordAt0Mem (transferFromSenderWord I) senderMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSender]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1456 := evm_run rd1451 with [
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩ senderMem)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1461 := evm_run rd1456 with [
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferFromSenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferInnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩ senderMem
                  ).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC ((transferInnerHashMem (transferFromSenderWord I)).readWithPadding 0 64)))
        rw [approveTwoWordHashMem_read0_64 (transferFromSenderWord I) ⟨0⟩
          hsenderMemSize, transferInnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1468 := evm_run rd1461 with [
    dup8, dup5,
    raw mstore 0 (approveWordAt0Mem (transferFromIdWord I)
        (approveTwoWordHashMem (transferFromSenderWord I) ⟨0⟩ senderMem))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0
      (transferMapScratchMem senderMem (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1470 := evm_run rd1468 with [
    swap1,
    raw keccak256 0 (transferOuterSlot (transferFromSenderWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferOuterSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferMapScratchMem senderMem (transferFromSenderWord I)
                    (transferFromIdWord I)).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferOuterHashMem (transferFromSenderWord I) (transferFromIdWord I)
                  ).readWithPadding 0 64)))
        rw [transferMapScratchMem_read0_64 (transferFromSenderWord I) (transferFromIdWord I)
          hsenderMemSize, transferOuterHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have hdebit :
      UInt256.sub
          (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I)
          (transferFromAmountWord I) =
        transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I := by
    apply u256_inj
    rw [usub_toNat henough]
    unfold transferFromTailSenderDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le
        (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat
        (transferFromAmountWord I).toNat)
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).val.isLt)]
  have rd1475₀ := evm_run rd1470 with [
    swap1, dup4, swap1, sub, swap1 ]
  have rd1475 := rd1475₀
  rw [hdebit, hslot] at rd1475
  obtain ⟨_, _, rd1476⟩ := rd1475.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, by simpa [senderMem] using rd1476⟩

theorem erc6909TransferFromX_from1323_toCheckedAdd_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2017⟩
      [transferFromTailReceiverBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromAmountWord I, ⟨1539⟩, ⟨0⟩, transferFromReceiverBalanceSlot I,
        transferFromAmountWord I, transferFromCallerWord I, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨760⟩, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨649⟩,
        transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem
          (transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I))
          (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd1476⟩ := erc6909TransferFromX_from1323_afterDebit_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hbase hread64 hperm hcanonSender hsenderNZ
    henough rd1323
  let senderMem := transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I)
  let debitMem := transferMapScratchMem senderMem (transferFromSenderWord I)
    (transferFromIdWord I)
  have hsenderMemSize : senderMem.size = 96 := by
    dsimp [senderMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I) hbase
  have hsenderMemRead64 :
      senderMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [senderMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      hbase hread64
  have hdebitMemSize : debitMem.size = 96 := by
    dsimp [debitMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I)
      hsenderMemSize
  have hdebitMemRead64 :
      debitMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [debitMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      hsenderMemSize hsenderMemRead64
  have hslot := transferFromReceiverBalanceKeccakSlot I hcanonReceiver
  have rd1492 := evm_run rd1476 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    iszero, push2 ⟨1545⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonReceiver]
      exact isZero_eq_zero_of_ne hreceiverNZ) ]
  have rd1505 := evm_run rd1492 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and, push0, swap1,
    dup2,
    raw mstore 0 (approveWordAt0Mem (transferFromReceiverWord I) debitMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonReceiver]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1510 := evm_run rd1505 with [
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (approveTwoWordHashMem (transferFromReceiverWord I) ⟨0⟩ debitMem)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1515 := evm_run rd1510 with [
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (transferInnerSlot (transferFromReceiverWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferInnerSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((approveTwoWordHashMem (transferFromReceiverWord I) ⟨0⟩ debitMem
                  ).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferInnerHashMem (transferFromReceiverWord I)).readWithPadding 0 64)))
        rw [approveTwoWordHashMem_read0_64 (transferFromReceiverWord I) ⟨0⟩
          hdebitMemSize, transferInnerHashMem_read0_64])
      (by decide) (by evm_ov) ]
  have rd1522 := evm_run rd1515 with [
    dup7, dup5,
    raw mstore 0 (approveWordAt0Mem (transferFromIdWord I)
        (approveTwoWordHashMem (transferFromReceiverWord I) ⟨0⟩ debitMem))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (transferMapScratchMem debitMem (transferFromReceiverWord I)
        (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup2 ]
  have rd1524 := evm_run rd1522 with [
    raw keccak256 0 (transferOuterSlot (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold transferOuterSlot
        change UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferMapScratchMem debitMem (transferFromReceiverWord I)
                    (transferFromIdWord I)).readWithPadding 0 64))) =
          UInt256.ofNat
            (fromByteArrayBigEndian
              (ffi.KEC
                ((transferOuterHashMem (transferFromReceiverWord I) (transferFromIdWord I)
                  ).readWithPadding 0 64)))
        rw [transferMapScratchMem_read0_64 (transferFromReceiverWord I)
          (transferFromIdWord I) hdebitMemSize, transferOuterHashMem_read0_64])
      (by decide) (by evm_ov),
    dup1 ]
  obtain ⟨k1, C1, rd1526₀⟩ := rd1524.sload (by decide) (by evm_ov)
  have rd1526 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1526⟩
      [transferFromTailReceiverBalanceWord (initState cA gh bl σcur σ₀ g A I) I,
        transferFromReceiverBalanceSlot I, ⟨0⟩, transferFromCallerWord I,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      (transferMapScratchMem debitMem (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
        (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I)) k1 C1 := by
    simpa [transferFromTailReceiverBalanceWord, transferFromTailAfterSenderBalanceState,
      transferFromSenderBalanceSlot, hslot, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, storageStore_accountMap, debitMem]
      using rd1526₀
  exact ⟨_, _, by
    simpa [senderMem, debitMem] using
      evm_run rd1526 with [
        dup5, swap3, swap1, push2 ⟨1539⟩, swap1, dup5, swap1, push2 ⟨2017⟩,
        jump (by jump_dest) ]⟩

theorem erc6909TransferFromX_from1545_successCaller_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (rd1545 : RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1545⟩
      [transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem
          (transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I))
          (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σcur)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  let senderMem := transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I)
  let debitMem := transferMapScratchMem senderMem (transferFromSenderWord I)
    (transferFromIdWord I)
  let creditMem := transferMapScratchMem debitMem (transferFromReceiverWord I)
    (transferFromIdWord I)
  have hsenderMemSize : senderMem.size = 96 := by
    dsimp [senderMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I) hbase
  have hsenderMemRead64 :
      senderMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [senderMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      hbase hread64
  have hdebitMemSize : debitMem.size = 96 := by
    dsimp [debitMem]
    exact transferMapScratchMem_size (transferFromSenderWord I) (transferFromIdWord I)
      hsenderMemSize
  have hdebitMemRead64 :
      debitMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [debitMem]
    exact transferMapScratchMem_read64 (transferFromSenderWord I) (transferFromIdWord I)
      hsenderMemSize hsenderMemRead64
  have hcreditMemSize : creditMem.size = 96 := by
    dsimp [creditMem]
    exact transferMapScratchMem_size (transferFromReceiverWord I) (transferFromIdWord I)
      hdebitMemSize
  have hcreditMemRead64 :
      creditMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [creditMem]
    exact transferMapScratchMem_read64 (transferFromReceiverWord I) (transferFromIdWord I)
      hdebitMemSize hdebitMemRead64
  exact erc6909TransferFromX_from1545_successCaller_mem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) (mem := creditMem) hcreditMemSize hcreditMemRead64 hperm hcanonSender
    hcanonReceiver (by simpa [senderMem, debitMem, creditMem] using rd1545)
/-
  have rd1563 := evm_run rd1545 with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (transferMapScratchMem_mload64 (transferFromReceiverWord I) (transferFromIdWord I)
        hdebitMemSize hdebitMemRead64)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, dup2, and, dup3,
    raw mstore 6 (transferEventFromBaseMem creditMem (transferFromCallerWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        change (UInt256.toByteArray (UInt256.land solcAddrMask (transferFromCallerWord I))).write 0
          creditMem 128 32 = transferEventFromBaseMem creditMem (transferFromCallerWord I)
        rw [solcAddrMask_clean_left (transferFromCallerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov) ]
  have rd1570 := evm_run rd1563 with [
    push1 ⟨32⟩, dup3, add, dup6, swap1,
    raw mstore 3 (transferEventBaseMem creditMem (transferFromCallerWord I)
        (transferFromAmountWord I))
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd1573 := evm_run rd1570 with [dup6, swap3, dup2]
  have rd1574 := RD.erc6909Dup9 rd1573 (by decide) (by evm_ov)
  have rd1577 := evm_run rd1574 with [and, swap3, swap2]
  have rd1578 := RD.erc6909Dup10 rd1577 (by decide) (by evm_ov)
  have rd1580₀ := evm_run rd1578 with [and, swap2]
  have rd1580 := rd1580₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide,
    solcAddrMask_clean hcanonSender,
    solcAddrMask_clean hcanonReceiver] at rd1580
  have rd1613 := rd1580.pushConst transferTransferTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd1622 := evm_run rd1613 with [
    swap2, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferEventBaseMem_mload64 (transferFromCallerWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have rd1623 := RD.erc6909Log4 0 (UInt256.ofNat 6) rd1622 (by decide) hperm
    mem_cost (by decide) (by evm_ov)
  have rd760 := evm_run rd1623 with [
    pop, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd649 := evm_run rd760 with [
    jumpdest, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd651 := evm_run rd649 with [jumpdest, pop, push1 ⟨1⟩]
  have rd654 := RD.erc6909Swap6 rd651 (by decide) (by evm_ov)
  have rd655 := RD.erc6909Swap5 rd654 (by decide) (by evm_ov)
  have rd193 := evm_run rd655 with [
    pop, pop, pop, pop, pop, jump (by jump_dest) ]
  have rd165 := evm_run rd193 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferEventBaseMem_mload64 (transferFromCallerWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 0 (transferReturnBaseMem creditMem (transferFromCallerWord I)
        (transferFromAmountWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨165⟩, jump (by jump_dest) ]
  exact evm_run rd165 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (transferReturnBaseMem_mload64 (transferFromCallerWord I) (transferFromAmountWord I)
        hcreditMemSize hcreditMemRead64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
            from by decide]
        exact transferReturnBaseMem_read128 (transferFromCallerWord I)
          (transferFromAmountWord I) hcreditMemSize)
      (by evm_ov) ]
-/

theorem erc6909TransferFromX_from1323_afterCredit_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (hfit : transferFromTailReceiverCreditNat (initState cA gh bl σcur σ₀ g A I) I <
      UInt256.size)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1545⟩
      [transferFromCallerWord I, transferFromAmountWord I, transferFromIdWord I,
        transferFromReceiverWord I, transferFromSenderWord I, ⟨760⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨649⟩, transferFromCallerWord I, ⟨0⟩,
        transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨193⟩, sel]
      (transferMapScratchMem
        (transferMapScratchMem
          (transferMapScratchMem base (transferFromSenderWord I) (transferFromIdWord I))
          (transferFromSenderWord I) (transferFromIdWord I))
        (transferFromReceiverWord I) (transferFromIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
          (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I))
        (transferFromReceiverBalanceSlot I)
        (transferFromTailReceiverCreditWord (initState cA gh bl σcur σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd2017⟩ := erc6909TransferFromX_from1323_toCheckedAdd_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hbase hread64 hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough rd1323
  obtain ⟨_, _, rd1539₀⟩ := erc6909RoutineCheckedAdd rd2017
    (by simpa [transferFromTailReceiverCreditNat] using hfit)
    (by jump_dest) (by evm_ov)
  have hnew :
      transferFromTailReceiverBalanceWord (initState cA gh bl σcur σ₀ g A I) I +
          transferFromAmountWord I =
        transferFromTailReceiverCreditWord (initState cA gh bl σcur σ₀ g A I) I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt (by
      simpa [transferFromTailReceiverCreditNat] using hfit)]
    unfold transferFromTailReceiverCreditWord
    rw [ulit_toNat' _ hfit]
    rfl
  have rd1539 := rd1539₀
  rw [hnew] at rd1539
  have rd1542 := evm_run rd1539 with [
    jumpdest, swap1, swap2 ]
  obtain ⟨_, _, rd1543⟩ := rd1542.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1543 with [ pop, pop ]⟩

theorem erc6909TransferFromX_from1323_overflow_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (hover : UInt256.size ≤
      transferFromTailReceiverCreditNat (initState cA gh bl σcur σ₀ g A I) I)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2017⟩ := erc6909TransferFromX_from1323_toCheckedAdd_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hbase hread64 hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough rd1323
  exact erc6909RoutineCheckedAdd_overflow rd2017
    (by simpa [transferFromTailReceiverCreditNat] using hover) (by evm_ov)

theorem erc6909TransferFromX_from1323_successCaller_base
    {cA gh bl σ σ₀ σcur A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    {base : ByteArray}
    (hbase : base.size = 96)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σcur σ₀ g A I) I).toNat)
    (hfit : transferFromTailReceiverCreditNat (initState cA gh bl σcur σ₀ g A I) I <
      UInt256.size)
    (rd1323 : RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1323⟩
      [transferFromAmountWord I, transferFromIdWord I, transferFromReceiverWord I,
        transferFromSenderWord I, ⟨760⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨649⟩, transferFromCallerWord I, ⟨0⟩, transferFromAmountWord I,
        transferFromIdWord I, transferFromReceiverWord I, transferFromSenderWord I,
        ⟨193⟩, sel]
      base (UInt256.ofNat 3) ByteArray.empty (cA, σcur) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σcur (transferFromSenderBalanceSlot I)
          (transferFromTailSenderDebitWord (initState cA gh bl σcur σ₀ g A I) I))
        (transferFromReceiverBalanceSlot I)
        (transferFromTailReceiverCreditWord (initState cA gh bl σcur σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd1545⟩ := erc6909TransferFromX_from1323_afterCredit_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σcur)
    (A := A) (g := g) (sel := sel) hbase hread64 hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough hfit rd1323
  exact erc6909TransferFromX_from1545_successCaller_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hbase hread64 hperm hcanonSender hcanonReceiver rd1545

theorem erc6909TransferFromX_operatorFalse_allowanceMax_revert_sender_zero
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hsenderZero : transferFromSenderWord I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbase := transferFromOperatorAllowanceScratchMem_size I
  have hread64 := transferFromOperatorAllowanceScratchMem_read64 I
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorFalse_allowanceMax_to661
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hallowanceMax hreach
  exact erc6909TransferFromX_from661_revert_sender_zero_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel) (base := transferFromOperatorAllowanceScratchMem I)
    hbase hread64 hsenderZero rd661

theorem erc6909TransferFromX_operatorFalse_allowanceMax_revert_receiver_zero
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverZero : transferFromReceiverWord I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbase := transferFromOperatorAllowanceScratchMem_size I
  have hread64 := transferFromOperatorAllowanceScratchMem_read64 I
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorFalse_allowanceMax_to661
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hallowanceMax hreach
  exact erc6909TransferFromX_from661_revert_receiver_zero_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel) (base := transferFromOperatorAllowanceScratchMem I)
    hbase hread64 hcanonSender hsenderNZ hreceiverZero rd661

theorem erc6909TransferFromX_operatorFalse_allowanceMax_insufficient
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbase := transferFromOperatorAllowanceScratchMem_size I
  have hread64 := transferFromOperatorAllowanceScratchMem_read64 I
  obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_operatorFalse_allowanceMax_to1323
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hallowanceMax hsenderNZ hreceiverNZ hreach
  exact erc6909TransferFromX_from1323_insufficient_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel) (base := transferFromOperatorAllowanceScratchMem I)
    hbase hread64 hcanonSender hsenderNZ hlt rd1323

theorem erc6909TransferFromX_operatorFalse_allowanceMax_overflow
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hover : UInt256.size ≤
      transferFromTailReceiverCreditNat (initState cA gh bl σ σ₀ g A I) I)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbase := transferFromOperatorAllowanceScratchMem_size I
  have hread64 := transferFromOperatorAllowanceScratchMem_read64 I
  obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_operatorFalse_allowanceMax_to1323
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hallowanceMax hsenderNZ hreceiverNZ hreach
  exact erc6909TransferFromX_from1323_overflow_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel) (base := transferFromOperatorAllowanceScratchMem I)
    hbase hread64 hperm hcanonSender hcanonReceiver hsenderNZ hreceiverNZ henough hover
    rd1323

theorem erc6909TransferFromX_operatorFalse_allowanceMax_success
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceMax : UInt256.size - 1 ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hfit : transferFromTailReceiverCreditNat (initState cA gh bl σ σ₀ g A I) I <
      UInt256.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromSenderBalanceSlot I)
          (transferFromTailSenderDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferFromReceiverBalanceSlot I)
        (transferFromTailReceiverCreditWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  have hbase := transferFromOperatorAllowanceScratchMem_size I
  have hread64 := transferFromOperatorAllowanceScratchMem_read64 I
  obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_operatorFalse_allowanceMax_to1323
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hallowanceMax hsenderNZ hreceiverNZ hreach
  exact erc6909TransferFromX_from1323_successCaller_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ)
    (A := A) (g := g) (sel := sel) (base := transferFromOperatorAllowanceScratchMem I)
    hbase hread64 hperm hcanonSender hcanonReceiver hsenderNZ hreceiverNZ henough hfit
    rd1323

set_option maxHeartbeats 4000000 in
theorem erc6909TransferFromX_operatorFalse_insufficientAllowance
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hopZero : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I = ⟨0⟩)
    (hallowanceNotMax :
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
        UInt256.size - 1)
    (hltAllowance :
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
        (transferFromAmountWord I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hbase := transferFromOperatorAllowanceScratchMem_size I
  have hread64 := transferFromOperatorAllowanceScratchMem_read64 I
  obtain ⟨_, _, rd1193⟩ := erc6909TransferFromX_operatorFalse_afterAllowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver
    hsenderNe hopZero hreach
  have hmaxToNat :
      (UInt256.ofNat (UInt256.size - 1)).toNat = UInt256.size - 1 := by
    exact ulit_toNat' _ (by
      have hpos : 0 < UInt256.size := by norm_num [UInt256.size]
      exact Nat.sub_lt hpos (by decide))
  have hltMax :
      UInt256.lt
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
        (UInt256.lnot (⟨0⟩ : UInt256)) = ⟨1⟩ := by
    rw [uint256_lnot_zero_max]
    exact ult_one (by simpa [hmaxToNat] using hallowanceNotMax)
  have hltAmount :
      UInt256.lt
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromAmountWord I) = ⟨1⟩ := ult_one hltAllowance
  have rd1202 := evm_run rd1193 with [
    push0, not, dup2, lt, iszero, push2 ⟨1316⟩,
    jumpiNT (by rw [hltMax]; decide) ]
  have rd1266 := evm_run rd1202 with [
    dup2, dup2, lt, iszero, push2 ⟨1266⟩,
    jumpiNT (by rw [hltAmount]; decide) ]
  exact evm_run rd1266 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (erc6909ScratchMem_mload64 hbase hread64) (by decide) (by evm_ov),
    push4 ⟨0x2c51fead⟩, push1 ⟨225⟩, shl, dup2,
    raw mstore 6
      (transferFromInsufficientAllowanceSelectorBaseMem
        (transferFromOperatorAllowanceScratchMem I))
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup6, and,
    push1 ⟨4⟩, dup3, add,
    raw mstore 3
      (transferFromInsufficientAllowanceSenderBaseMem
        (transferFromOperatorAllowanceScratchMem I) (transferFromCallerWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean_left (transferFromCallerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, dup2, add, dup3, swap1,
    raw mstore 3
      (transferFromInsufficientAllowanceAllowanceBaseMem
        (transferFromOperatorAllowanceScratchMem I) (transferFromCallerWord I)
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.ofNat 7) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨68⟩, dup2, add, dup4, swap1,
    raw mstore 3
      (transferFromInsufficientAllowanceAmountBaseMem
        (transferFromOperatorAllowanceScratchMem I) (transferFromCallerWord I)
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 8) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨100⟩, dup2, add, dup5, swap1,
    raw mstore 3
      (transferFromInsufficientAllowanceIdBaseMem
        (transferFromOperatorAllowanceScratchMem I) (transferFromCallerWord I)
        (transferFromIdWord I)
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromAmountWord I))
      (UInt256.ofNat 9) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨132⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide)
      mem_cost
      (transferFromInsufficientAllowanceIdBaseMem_mload64 (transferFromCallerWord I)
        (transferFromIdWord I)
        (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I)
        (transferFromAmountWord I) hbase hread64)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909TransferFromX_operatorApproved_revert_sender_zero
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hop : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I ≠ ⟨0⟩)
    (hsenderZero : transferFromSenderWord I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let base := isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I)
  have hbase : base.size = 96 := by
    dsimp [base]
    exact isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I)
  have hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [base]
    exact isOperatorOuterHashMem_read64 (transferFromSenderWord I) (transferFromCallerWord I)
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorApproved_toUpdate
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderNe hop hreach
  exact erc6909TransferFromX_from661_revert_sender_zero_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hbase hread64 hsenderZero rd661

theorem erc6909TransferFromX_operatorApproved_revert_receiver_zero
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hop : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I ≠ ⟨0⟩)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverZero : transferFromReceiverWord I = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let base := isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I)
  have hbase : base.size = 96 := by
    dsimp [base]
    exact isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I)
  have hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [base]
    exact isOperatorOuterHashMem_read64 (transferFromSenderWord I) (transferFromCallerWord I)
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorApproved_toUpdate
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderNe hop hreach
  exact erc6909TransferFromX_from661_revert_receiver_zero_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hbase hread64 hcanonSender hsenderNZ
    hreceiverZero rd661

theorem erc6909TransferFromX_operatorApproved_insufficient
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hop : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I ≠ ⟨0⟩)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (hlt : (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromAmountWord I).toNat)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let base := isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I)
  have hbase : base.size = 96 := by
    dsimp [base]
    exact isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I)
  have hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [base]
    exact isOperatorOuterHashMem_read64 (transferFromSenderWord I) (transferFromCallerWord I)
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorApproved_toUpdate
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderNe hop hreach
  obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_from661_toUpdateHelper_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hcanonSender hcanonReceiver hsenderNZ
    hreceiverNZ rd661
  exact erc6909TransferFromX_from1323_insufficient_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hbase hread64 hcanonSender hsenderNZ hlt
    rd1323

theorem erc6909TransferFromX_operatorApproved_overflow
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hop : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I ≠ ⟨0⟩)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hover : UInt256.size ≤
      transferFromTailReceiverCreditNat (initState cA gh bl σ σ₀ g A I) I)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let base := isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I)
  have hbase : base.size = 96 := by
    dsimp [base]
    exact isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I)
  have hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [base]
    exact isOperatorOuterHashMem_read64 (transferFromSenderWord I) (transferFromCallerWord I)
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorApproved_toUpdate
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderNe hop hreach
  obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_from661_toUpdateHelper_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hcanonSender hcanonReceiver hsenderNZ
    hreceiverNZ rd661
  exact erc6909TransferFromX_from1323_overflow_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hbase hread64 hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough hover rd1323

theorem erc6909TransferFromX_operatorApproved_success
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus)
    (hsenderNe : transferFromSenderWord I ≠ transferFromCallerWord I)
    (hop : transferFromOperatorWord (initState cA gh bl σ σ₀ g A I) I ≠ ⟨0⟩)
    (hsenderNZ : transferFromSenderWord I ≠ ⟨0⟩)
    (hreceiverNZ : transferFromReceiverWord I ≠ ⟨0⟩)
    (henough : (transferFromAmountWord I).toNat ≤
      (transferFromSenderBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hfit : transferFromTailReceiverCreditNat (initState cA gh bl σ σ₀ g A I) I <
      UInt256.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferFromSenderBalanceSlot I)
          (transferFromTailSenderDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferFromReceiverBalanceSlot I)
        (transferFromTailReceiverCreditWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  let base := isOperatorOuterHashMem (transferFromSenderWord I) (transferFromCallerWord I)
  have hbase : base.size = 96 := by
    dsimp [base]
    exact isOperatorOuterHashMem_size (transferFromSenderWord I) (transferFromCallerWord I)
  have hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [base]
    exact isOperatorOuterHashMem_read64 (transferFromSenderWord I) (transferFromCallerWord I)
  obtain ⟨_, _, rd661⟩ := erc6909TransferFromX_operatorApproved_toUpdate
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz132 hsize hszhi hcanonSender hcanonReceiver hsenderNe hop hreach
  obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_from661_toUpdateHelper_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hcanonSender hcanonReceiver hsenderNZ
    hreceiverNZ rd661
  exact erc6909TransferFromX_from1323_successCaller_base
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (σcur := σ) (A := A)
    (g := g) (sel := sel) (base := base) hbase hread64 hperm hcanonSender hcanonReceiver
    hsenderNZ hreceiverNZ henough hfit rd1323

theorem erc6909TransferFromX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 132)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨1⟩ := by
    simpa using solcCalldataStaticLenCheckShort (words := 4) hsz4 hshort hsize
      (by norm_num)
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push0, push1 ⟨128⟩, dup6, dup8, sub, slt, iszero,
    push2 ⟨1973⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909TransferFromX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨128⟩ = ⟨1⟩ := by
    simpa using solcCalldataStaticLenCheckHuge (words := 4) hbig hsize (by norm_num)
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push0, push1 ⟨128⟩, dup6, dup8, sub, slt, iszero,
    push2 ⟨1973⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909TransferFromX_noncanon_sender {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (transferFromSenderWord I)
      (UInt256.land (transferFromSenderWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_dec1629_sender (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hreach
  simpa [transferFromSenderWord, calldataWord] using RD.erc6909DecodeAddrRevert rd hnc
    (by evm_ov)

theorem erc6909TransferFromX_noncanon_receiver {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz132 : 132 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (transferFromReceiverWord I)
      (UInt256.land (transferFromReceiverWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨388⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := erc6909TransferFromX_dec1629_receiver (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz132 hsize hszhi hcanonSender hreach
  simpa [transferFromReceiverWord, calldataWord] using RD.erc6909DecodeAddrRevert rd hnc
    (by evm_ov)

theorem erc6909TransferFromSelector_size {I : ExecutionEnv}
    (hsel : selIs I (erc6909SelBytes 7)) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (erc6909SelBytes 7).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc6909Dispatch_transferFrom {cd : ByteArray}
    (hsel : (erc6909SelBytes 7 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some transferFromTransition := by
  have hcd : cd.extract 0 4 = erc6909SelBytes 7 := (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition, isOperatorTransition,
      setOperatorTransition, supportsInterfaceTransition, transferTransition])
    (post := [])
    rfl ?_ (by
      rw [selectorOf, erc6909TransferFromSelectorBytes]
      simpa [erc6909SelBytes] using hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, erc6909AllowanceSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909ApproveSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909BalanceOfSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909IsOperatorSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909SetOperatorSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909SupportsInterfaceSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909TransferSelectorBytes, hcd]; decide

#exit

set_option maxHeartbeats 20000000 in
theorem erc6909TransferFromBodyCore
    {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = erc6909BenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (erc6909SelBytes 7))
    (hreach : ∃ k C, RD erc6909BenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨388⟩
      [erc6909SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  have hsz4 := erc6909TransferFromSelector_size hsel
  have hd := erc6909Dispatch_transferFrom (cd := I.calldata) hsel
  let evmE := initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g)
      hAccounts
  have hOperator : transferFromOperatorWord evmE I = transferFromOperatorWord evmS I := by
    unfold transferFromOperatorWord transferFromOperatorSlot
    rw [hσ.executionEnv]
    exact congrArg (fun w => UInt256.land w ⟨255⟩)
      (hσ.storageLoad_codeOwner
        (operatorApprovalSlot
          (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
          (.address evmS.executionEnv.source)))
  have hAllowance :
      transferFromCurrentAllowanceWord evmE I =
        transferFromCurrentAllowanceWord evmS I := by
    unfold transferFromCurrentAllowanceWord transferFromAllowanceSlot
    rw [hσ.executionEnv]
    exact hσ.storageLoad_codeOwner
      (allowanceSlot
        (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
        (.address evmS.executionEnv.source)
        (.int (Int.ofNat (transferFromIdWord I).toNat)))
  have hAllowanceDebit :
      transferFromAllowanceDebitWord evmE I = transferFromAllowanceDebitWord evmS I := by
    simp [transferFromAllowanceDebitWord, hAllowance]
  have hσAfterAllowance :
      EVMStateEquiv (transferFromAfterAllowanceState evmE I)
        (transferFromAfterAllowanceState evmS I) := by
    unfold transferFromAfterAllowanceState transferFromAllowanceSlot
    rw [hσ.executionEnv, hAllowanceDebit]
    exact hσ.storageStore_codeOwner
      (allowanceSlot
        (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
        (.address evmS.executionEnv.source)
        (.int (Int.ofNat (transferFromIdWord I).toNat))) rfl
  have hAfterAllowanceSenderBalance :
      transferFromSenderBalanceWord (transferFromAfterAllowanceState evmE I) I =
        transferFromSenderBalanceWord (transferFromAfterAllowanceState evmS I) I := by
    unfold transferFromSenderBalanceWord
    rw [transferFromAfterAllowance_codeOwner evmE I,
      transferFromAfterAllowance_codeOwner evmS I]
    exact hσAfterAllowance.storageLoad
      (congrArg ExecutionEnv.codeOwner hσ.executionEnv) (transferFromSenderBalanceSlot I)
  have hSenderDebit :
      transferFromSenderDebitWord evmE I = transferFromSenderDebitWord evmS I := by
    simp [transferFromSenderDebitWord, hAfterAllowanceSenderBalance]
  have hσAfterSenderBalance :
      EVMStateEquiv (transferFromAfterSenderBalanceState evmE I)
        (transferFromAfterSenderBalanceState evmS I) := by
    unfold transferFromAfterSenderBalanceState
    rw [hSenderDebit]
    exact hσAfterAllowance.storageStore
      (congrArg ExecutionEnv.codeOwner hσ.executionEnv) (transferFromSenderBalanceSlot I) rfl
  have hReceiverBalance :
      transferFromReceiverBalanceWord evmE I = transferFromReceiverBalanceWord evmS I := by
    unfold transferFromReceiverBalanceWord
    exact hσAfterSenderBalance.storageLoad
      (congrArg ExecutionEnv.codeOwner hσ.executionEnv) (transferFromReceiverBalanceSlot I)
  have hReceiverCreditNat :
      transferFromReceiverCreditNat evmE I = transferFromReceiverCreditNat evmS I := by
    simp [transferFromReceiverCreditNat, hReceiverBalance]
  have hReceiverCreditWord :
      transferFromReceiverCreditWord evmE I = transferFromReceiverCreditWord evmS I := by
    simp [transferFromReceiverCreditWord, hReceiverCreditNat]
  have hσPost :
      EVMStateEquiv (transferFromPostState evmE I) (transferFromPostState evmS I) := by
    unfold transferFromPostState
    rw [hReceiverCreditWord]
    exact hσAfterSenderBalance.storageStore
      (congrArg ExecutionEnv.codeOwner hσ.executionEnv) (transferFromReceiverBalanceSlot I) rfl
  have hTailSenderBalance :
      transferFromSenderBalanceWord evmE I = transferFromSenderBalanceWord evmS I := by
    unfold transferFromSenderBalanceWord
    exact hσ.storageLoad (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferFromSenderBalanceSlot I)
  have hTailSenderDebit :
      transferFromTailSenderDebitWord evmE I = transferFromTailSenderDebitWord evmS I := by
    simp [transferFromTailSenderDebitWord, hTailSenderBalance]
  have hσTailAfterSender :
      EVMStateEquiv (transferFromTailAfterSenderBalanceState evmE I)
        (transferFromTailAfterSenderBalanceState evmS I) := by
    unfold transferFromTailAfterSenderBalanceState
    rw [hTailSenderDebit]
    exact hσ.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferFromSenderBalanceSlot I) rfl
  have hTailReceiverBalance :
      transferFromTailReceiverBalanceWord evmE I =
        transferFromTailReceiverBalanceWord evmS I := by
    unfold transferFromTailReceiverBalanceWord
    exact hσTailAfterSender.storageLoad
      (congrArg ExecutionEnv.codeOwner hσ.executionEnv) (transferFromReceiverBalanceSlot I)
  have hTailReceiverCreditNat :
      transferFromTailReceiverCreditNat evmE I =
        transferFromTailReceiverCreditNat evmS I := by
    simp [transferFromTailReceiverCreditNat, hTailReceiverBalance]
  have hTailReceiverCreditWord :
      transferFromTailReceiverCreditWord evmE I =
        transferFromTailReceiverCreditWord evmS I := by
    simp [transferFromTailReceiverCreditWord, hTailReceiverCreditNat]
  have hσTailPost :
      EVMStateEquiv (transferFromTailPostState evmE I)
        (transferFromTailPostState evmS I) := by
    unfold transferFromTailPostState
    rw [hTailReceiverCreditWord]
    exact hσTailAfterSender.storageStore
      (congrArg ExecutionEnv.codeOwner hσ.executionEnv) (transferFromReceiverBalanceSlot I) rfl
  by_cases hsz132 : 132 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonSender : (transferFromSenderWord I).toNat < EVM.addressModulus
      · by_cases hcanonReceiver : (transferFromReceiverWord I).toNat < EVM.addressModulus
        · have hdec := erc6909Decode_transferFrom_ok (I := I) hsz132 hbig
            hcanonSender hcanonReceiver
          have hsenderZeroAddr :
              transferFromSenderWord I = ⟨0⟩ →
                AccountAddress.ofNat (transferFromSenderWord I).toNat = zeroAccountAddress := by
            intro hz
            simpa [zeroAccountAddress] using
              (approveAccountAddress_ofNat_zero_iff hcanonSender).mpr hz
          have hsenderNZAddr :
              transferFromSenderWord I ≠ ⟨0⟩ →
                AccountAddress.ofNat (transferFromSenderWord I).toNat ≠
                  zeroAccountAddress := by
            intro hnz hz
            exact hnz ((approveAccountAddress_ofNat_zero_iff hcanonSender).mp
              (by simpa [zeroAccountAddress] using hz))
          have hreceiverZeroAddr :
              transferFromReceiverWord I = ⟨0⟩ →
                AccountAddress.ofNat (transferFromReceiverWord I).toNat =
                  zeroAccountAddress := by
            intro hz
            simpa [zeroAccountAddress] using
              (approveAccountAddress_ofNat_zero_iff hcanonReceiver).mpr hz
          have hreceiverNZAddr :
              transferFromReceiverWord I ≠ ⟨0⟩ →
                AccountAddress.ofNat (transferFromReceiverWord I).toNat ≠
                  zeroAccountAddress := by
            intro hnz hz
            exact hnz ((approveAccountAddress_ofNat_zero_iff hcanonReceiver).mp
              (by simpa [zeroAccountAddress] using hz))
          by_cases hsenderCaller : transferFromSenderWord I = transferFromCallerWord I
          · have hgate :=
              evalExpr_transferFrom_allowance_gate_false_sender evmS I
                (by simp [evmS, initState]) hsenderCaller
            by_cases hsenderZero : transferFromSenderWord I = ⟨0⟩
            · have hbody := erc6909TransferFromBodyRevertsNoAllowance_sender_zero evmS I
                (by simp only [evmS, initState]; exact hwv) hgate
                (hsenderZeroAddr hsenderZero)
              exact (erc6909TransferFromX_skipCaller_revert_sender_zero
                  (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                  hcanonReceiver hsenderCaller hsenderZero hreach)
                |>.reEquivExecutionRevert hcode hd hdec hbody
            · by_cases hreceiverZero : transferFromReceiverWord I = ⟨0⟩
              · have hbody := erc6909TransferFromBodyRevertsNoAllowance_receiver_zero evmS I
                  (by simp only [evmS, initState]; exact hwv) hgate
                  (hsenderNZAddr hsenderZero) (hreceiverZeroAddr hreceiverZero)
                exact (erc6909TransferFromX_skipCaller_revert_receiver_zero
                    (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                    hcanonReceiver hsenderCaller hsenderZero hreceiverZero hreach)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
              · by_cases henough :
                  (transferFromAmountWord I).toNat ≤
                    (transferFromSenderBalanceWord evmE I).toNat
                · by_cases hfit : transferFromTailReceiverCreditNat evmE I < UInt256.size
                  · have henoughS :
                        (transferFromAmountWord I).toNat ≤
                          (transferFromSenderBalanceWord evmS I).toNat := by
                      simpa [hTailSenderBalance] using henough
                    have hfitS : transferFromTailReceiverCreditNat evmS I < UInt256.size := by
                      simpa [hTailReceiverCreditNat] using hfit
                    have hbody := erc6909TransferFromBodyCoreNoAllowance evmS I
                      (by simp only [evmS, initState]; exact hwv) hgate
                      (evalExpr_transferFrom_sender_nonzero_true_of_get evmS
                        (transferFromStore I) I (transferFromStore_sender I)
                        (hsenderNZAddr hsenderZero))
                      (evalExpr_transferFrom_receiver_nonzero_true_of_get evmS
                        (transferFromStore I) I (transferFromStore_receiver I)
                        (hreceiverNZAddr hreceiverZero))
                      henoughS hfitS
                    exact (erc6909TransferFromX_skipCaller_success
                        (g := Sat256.ofUInt256 g) hsz132 hsize hbig hperm hcanonSender
                        hcanonReceiver hsenderCaller hsenderZero hreceiverZero henough
                        hfit hreach)
                      |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                        (by simp [evmE, initState, transferFromTailPostState,
                          transferFromTailAfterSenderBalanceState, storageStore_createdAccounts])
                        (accountMapEquiv.of_eq (by
                          simp [evmE, initState, transferFromTailPostState,
                            transferFromTailAfterSenderBalanceState, storageStore_accountMap]))
                        hσTailPost
                        (returnEquiv_of_encode
                          (by simpa [boolTy] using boolTrueReturnEncoding))
                  · have hover : UInt256.size ≤ transferFromTailReceiverCreditNat evmE I := by
                      omega
                    have henoughS :
                        (transferFromAmountWord I).toNat ≤
                          (transferFromSenderBalanceWord evmS I).toNat := by
                      simpa [hTailSenderBalance] using henough
                    have hoverS :
                        UInt256.size ≤ transferFromTailReceiverCreditNat evmS I := by
                      simpa [hTailReceiverCreditNat] using hover
                    have hbody := erc6909TransferFromBodyRevertsNoAllowance_overflow evmS I
                      (by simp only [evmS, initState]; exact hwv) hgate
                      (hsenderNZAddr hsenderZero) (hreceiverNZAddr hreceiverZero)
                      henoughS hoverS
                    exact (erc6909TransferFromX_skipCaller_overflow
                        (g := Sat256.ofUInt256 g) hsz132 hsize hbig hperm hcanonSender
                        hcanonReceiver hsenderCaller hsenderZero hreceiverZero henough hover
                        hreach)
                      |>.reEquivExecutionRevert hcode hd hdec hbody
                · have hlt :
                      (transferFromSenderBalanceWord evmE I).toNat <
                        (transferFromAmountWord I).toNat := by
                    omega
                  have hltS :
                      (transferFromSenderBalanceWord evmS I).toNat <
                        (transferFromAmountWord I).toNat := by
                    simpa [hTailSenderBalance] using hlt
                  have hbody := erc6909TransferFromBodyRevertsNoAllowance_insufficient evmS I
                    (by simp only [evmS, initState]; exact hwv) hgate
                    (hsenderNZAddr hsenderZero) (hreceiverNZAddr hreceiverZero) hltS
                  exact (erc6909TransferFromX_skipCaller_insufficient
                      (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                      hcanonReceiver hsenderCaller hsenderZero hreceiverZero hlt hreach)
                    |>.reEquivExecutionRevert hcode hd hdec hbody
          · have hsenderNeSource :
                AccountAddress.ofNat (transferFromSenderWord I).toNat ≠ I.source := by
              intro haddr
              apply hsenderCaller
              calc
                transferFromSenderWord I =
                    keyValueToWord
                      (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat)) := by
                  exact (erc6909ApproveKeyValueToWord_address_of_canonical _
                    hcanonSender).symm
                _ = keyValueToWord (.address I.source) := by rw [haddr]
                _ = keyValueToWord
                    (.address (AccountAddress.ofNat (transferFromCallerWord I).toNat)) := by
                  rw [← transferFromCaller_ofNat I]
                _ = transferFromCallerWord I := by
                  exact erc6909ApproveKeyValueToWord_address_of_canonical _
                    (transferFromCallerWord_canonical I)
            by_cases hopZero : transferFromOperatorWord evmE I = ⟨0⟩
            · have hgate :=
                evalExpr_transferFrom_allowance_gate_true evmS I
                  (by simp [evmS, initState]) hsenderNeSource
                  (by simpa [hOperator] using hopZero)
              by_cases hallowanceMax :
                  UInt256.size - 1 ≤ (transferFromCurrentAllowanceWord evmE I).toNat
              · have hallowanceMaxS :
                    UInt256.size - 1 ≤
                      (transferFromCurrentAllowanceWord evmS I).toNat := by
                  simpa [hAllowance] using hallowanceMax
                have hallowanceMaxExpr :=
                  evalExpr_transferFrom_allowance_lt_max_false evmS I hallowanceMaxS
                by_cases hsenderZero : transferFromSenderWord I = ⟨0⟩
                · have hbody :=
                    erc6909TransferFromBodyRevertsAllowanceMax_sender_zero evmS I
                      (by simp only [evmS, initState]; exact hwv) hgate
                      hallowanceMaxExpr (hsenderZeroAddr hsenderZero)
                  exact (erc6909TransferFromX_operatorFalse_allowanceMax_revert_sender_zero
                      (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                      hcanonReceiver hsenderCaller hopZero hallowanceMax hsenderZero hreach)
                    |>.reEquivExecutionRevert hcode hd hdec hbody
                · by_cases hreceiverZero : transferFromReceiverWord I = ⟨0⟩
                  · have hbody :=
                      erc6909TransferFromBodyRevertsAllowanceMax_receiver_zero evmS I
                        (by simp only [evmS, initState]; exact hwv) hgate
                        hallowanceMaxExpr (hsenderNZAddr hsenderZero)
                        (hreceiverZeroAddr hreceiverZero)
                    exact (erc6909TransferFromX_operatorFalse_allowanceMax_revert_receiver_zero
                        (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                        hcanonReceiver hsenderCaller hopZero hallowanceMax hsenderZero
                        hreceiverZero hreach)
                      |>.reEquivExecutionRevert hcode hd hdec hbody
                  · by_cases henough :
                      (transferFromAmountWord I).toNat ≤
                        (transferFromSenderBalanceWord evmE I).toNat
                    · by_cases hfit :
                        transferFromTailReceiverCreditNat evmE I < UInt256.size
                      · have henoughS :
                            (transferFromAmountWord I).toNat ≤
                              (transferFromSenderBalanceWord evmS I).toNat := by
                          simpa [hTailSenderBalance] using henough
                        have hfitS :
                            transferFromTailReceiverCreditNat evmS I < UInt256.size := by
                          simpa [hTailReceiverCreditNat] using hfit
                        rcases erc6909TransferFromBodyCoreAllowanceMax evmS I
                          (by simp only [evmS, initState]; exact hwv) hgate
                          hallowanceMaxExpr
                          (evalExpr_transferFrom_sender_nonzero_true_of_get evmS
                            (transferFromStoreCurrentAllowance evmS I) I
                            (transferFromStoreCurrentAllowance_sender evmS I)
                            (hsenderNZAddr hsenderZero))
                          (evalExpr_transferFrom_receiver_nonzero_true_of_get evmS
                            (transferFromStoreCurrentAllowance evmS I) I
                            (transferFromStoreCurrentAllowance_receiver evmS I)
                            (hreceiverNZAddr hreceiverZero))
                          henoughS hfitS with ⟨cs, hbody⟩
                        exact (erc6909TransferFromX_operatorFalse_allowanceMax_success
                            (g := Sat256.ofUInt256 g) hsz132 hsize hbig hperm
                            hcanonSender hcanonReceiver hsenderCaller hopZero hallowanceMax
                            hsenderZero hreceiverZero henough hfit hreach)
                          |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                            (by simp [evmE, initState, transferFromTailPostState,
                              transferFromTailAfterSenderBalanceState,
                              storageStore_createdAccounts])
                            (accountMapEquiv.of_eq (by
                              simp [evmE, initState, transferFromTailPostState,
                                transferFromTailAfterSenderBalanceState,
                                storageStore_accountMap]))
                            hσTailPost
                            (returnEquiv_of_encode
                              (by simpa [boolTy] using boolTrueReturnEncoding))
                      · have hover :
                            UInt256.size ≤ transferFromTailReceiverCreditNat evmE I := by
                          omega
                        have henoughS :
                            (transferFromAmountWord I).toNat ≤
                              (transferFromSenderBalanceWord evmS I).toNat := by
                          simpa [hTailSenderBalance] using henough
                        have hoverS :
                            UInt256.size ≤ transferFromTailReceiverCreditNat evmS I := by
                          simpa [hTailReceiverCreditNat] using hover
                        have hbody :=
                          erc6909TransferFromBodyRevertsAllowanceMax_overflow evmS I
                            (by simp only [evmS, initState]; exact hwv) hgate
                            hallowanceMaxExpr (hsenderNZAddr hsenderZero)
                            (hreceiverNZAddr hreceiverZero) henoughS hoverS
                        exact (erc6909TransferFromX_operatorFalse_allowanceMax_overflow
                            (g := Sat256.ofUInt256 g) hsz132 hsize hbig hperm
                            hcanonSender hcanonReceiver hsenderCaller hopZero hallowanceMax
                            hsenderZero hreceiverZero henough hover hreach)
                          |>.reEquivExecutionRevert hcode hd hdec hbody
                    · have hlt :
                          (transferFromSenderBalanceWord evmE I).toNat <
                            (transferFromAmountWord I).toNat := by
                        omega
                      have hltS :
                          (transferFromSenderBalanceWord evmS I).toNat <
                            (transferFromAmountWord I).toNat := by
                        simpa [hTailSenderBalance] using hlt
                      have hbody :=
                        erc6909TransferFromBodyRevertsAllowanceMax_insufficient_balance evmS I
                          (by simp only [evmS, initState]; exact hwv) hgate
                          hallowanceMaxExpr (hsenderNZAddr hsenderZero)
                          (hreceiverNZAddr hreceiverZero) hltS
                      exact (erc6909TransferFromX_operatorFalse_allowanceMax_insufficient
                          (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                          hcanonReceiver hsenderCaller hopZero hallowanceMax hsenderZero
                          hreceiverZero hlt hreach)
                        |>.reEquivExecutionRevert hcode hd hdec hbody
              · have hallowanceNotMax :
                    (transferFromCurrentAllowanceWord evmE I).toNat < UInt256.size - 1 := by
                  omega
                have hallowanceNotMaxS :
                    (transferFromCurrentAllowanceWord evmS I).toNat < UInt256.size - 1 := by
                  simpa [hAllowance] using hallowanceNotMax
                have hallowanceNotMaxExpr :=
                  evalExpr_transferFrom_allowance_lt_max_true evmS I hallowanceNotMaxS
                by_cases hallowanceEnough :
                    (transferFromAmountWord I).toNat ≤
                      (transferFromCurrentAllowanceWord evmE I).toNat
                · have hallowanceEnoughS :
                      (transferFromAmountWord I).toNat ≤
                        (transferFromCurrentAllowanceWord evmS I).toNat := by
                    simpa [hAllowance] using hallowanceEnough
                  let σAllowance := sstoreAccountMap I.codeOwner σ_evm
                    (transferFromAllowanceSlotI I) (transferFromAllowanceDebitWord evmE I)
                  have hAfterAllowanceInit :
                      transferFromAfterAllowanceState evmE I =
                        initState cA gh bl σAllowance σ₀_evm (Sat256.ofUInt256 g) A I := by
                    cases hfind : σ_evm.find? I.codeOwner <;>
                      simp [evmE, σAllowance, transferFromAfterAllowanceState,
                        transferFromAllowanceSlot, transferFromAllowanceSlotI, initState,
                        Solm.EVM.storageStore, State.lookupAccount, hfind, sstoreAccountMap,
                        Option.option, State.setAccount, Account.updateStorage]
                  have hAfterAllowanceMap :
                      (transferFromAfterAllowanceState evmE I).accountMap =
                        σAllowance := by
                    simpa [initState] using congrArg (fun s : EVM.State => s.accountMap)
                      hAfterAllowanceInit
                  have hPostAsTail :
                      transferFromPostState evmE I =
                        transferFromTailPostState
                          (initState cA gh bl σAllowance σ₀_evm
                            (Sat256.ofUInt256 g) A I) I := by
                    rw [← hAfterAllowanceInit]
                    simp [transferFromPostState, transferFromTailPostState,
                      transferFromAfterSenderBalanceState,
                      transferFromTailAfterSenderBalanceState,
                      transferFromSenderDebitWord, transferFromTailSenderDebitWord,
                      transferFromReceiverCreditWord, transferFromTailReceiverCreditWord,
                      transferFromReceiverCreditNat, transferFromTailReceiverCreditNat,
                      transferFromReceiverBalanceWord, transferFromTailReceiverBalanceWord,
                      transferFromAfterAllowance_codeOwner]
                  have hbase := transferFromOperatorAllowanceScratchMem_size I
                  have hread64 := transferFromOperatorAllowanceScratchMem_read64 I
                  obtain ⟨_, _, rd1193⟩ :=
                    erc6909TransferFromX_operatorFalse_afterAllowanceLoad
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                      (σ₀ := σ₀_evm) (A := A) (g := Sat256.ofUInt256 g)
                      (sel := erc6909SelWord I) hsz132 hsize hbig hcanonSender
                      hcanonReceiver hsenderCaller hopZero hreach
                  obtain ⟨_, _, rd661⟩ :=
                    erc6909TransferFromX_from1193_allowanceDebit_to661_base
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                      (σ₀ := σ₀_evm) (A := A) (g := Sat256.ofUInt256 g)
                      (sel := erc6909SelWord I)
                      (base := transferFromOperatorAllowanceScratchMem I)
                      hbase hperm hcanonSender hallowanceNotMax hallowanceEnough rd1193
                  by_cases hsenderZero : transferFromSenderWord I = ⟨0⟩
                  · have hbody :=
                      erc6909TransferFromBodyRevertsAllowance_sender_zero evmS I
                        (by simp only [evmS, initState]; exact hwv) hgate
                        hallowanceNotMaxExpr hallowanceEnoughS
                        (hsenderZeroAddr hsenderZero)
                    exact (erc6909TransferFromX_from661_revert_sender_zero_base
                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                        (σ₀ := σ₀_evm) (σcur := σAllowance) (A := A)
                        (g := Sat256.ofUInt256 g) (sel := erc6909SelWord I)
                        (base := transferFromAllowanceScratchMem
                          (transferFromOperatorAllowanceScratchMem I) I)
                        (transferFromAllowanceScratchMem_size I hbase)
                        (transferFromAllowanceScratchMem_read64 I hbase hread64)
                        hsenderZero
                        (by simpa [evmE, σAllowance] using rd661))
                      |>.reEquivExecutionRevert hcode hd hdec hbody
                  · by_cases hreceiverZero : transferFromReceiverWord I = ⟨0⟩
                    · have hbody :=
                        erc6909TransferFromBodyRevertsAllowance_receiver_zero evmS I
                          (by simp only [evmS, initState]; exact hwv) hgate
                          hallowanceNotMaxExpr hallowanceEnoughS
                          (hsenderNZAddr hsenderZero) (hreceiverZeroAddr hreceiverZero)
                      exact (erc6909TransferFromX_from661_revert_receiver_zero_base
                          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                          (σ₀ := σ₀_evm) (σcur := σAllowance) (A := A)
                          (g := Sat256.ofUInt256 g) (sel := erc6909SelWord I)
                          (base := transferFromAllowanceScratchMem
                            (transferFromOperatorAllowanceScratchMem I) I)
                          (transferFromAllowanceScratchMem_size I hbase)
                          (transferFromAllowanceScratchMem_read64 I hbase hread64)
                          hcanonSender hsenderZero hreceiverZero
                          (by simpa [evmE, σAllowance] using rd661))
                        |>.reEquivExecutionRevert hcode hd hdec hbody
                    · obtain ⟨_, _, rd1323⟩ := erc6909TransferFromX_from661_toUpdateHelper_base
                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                        (σ₀ := σ₀_evm) (σcur := σAllowance) (A := A)
                        (g := Sat256.ofUInt256 g) (sel := erc6909SelWord I)
                        (base := transferFromAllowanceScratchMem
                          (transferFromOperatorAllowanceScratchMem I) I)
                        hcanonSender hcanonReceiver hsenderZero hreceiverZero
                        (by simpa [evmE, σAllowance] using rd661)
                      by_cases hbalanceEnough :
                          (transferFromAmountWord I).toNat ≤
                            (transferFromSenderBalanceWord
                              (transferFromAfterAllowanceState evmE I) I).toNat
                      · by_cases hfit : transferFromReceiverCreditNat evmE I < UInt256.size
                        · have hbalanceEnoughS :
                              (transferFromAmountWord I).toNat ≤
                                (transferFromSenderBalanceWord
                                  (transferFromAfterAllowanceState evmS I) I).toNat := by
                            simpa [hAfterAllowanceSenderBalance] using hbalanceEnough
                          have hfitS : transferFromReceiverCreditNat evmS I < UInt256.size := by
                            simpa [hReceiverCreditNat] using hfit
                          have hbody := erc6909TransferFromBodyCoreAllowanceDebit evmS I
                            (by simp only [evmS, initState]; exact hwv) hgate
                            hallowanceNotMaxExpr hallowanceEnoughS
                            (evalExpr_transferFrom_sender_nonzero_true_of_get
                              (transferFromAfterAllowanceState evmS I)
                              (transferFromStoreCurrentAllowance evmS I) I
                              (transferFromStoreCurrentAllowance_sender evmS I)
                              (hsenderNZAddr hsenderZero))
                            (evalExpr_transferFrom_receiver_nonzero_true_of_get
                              (transferFromAfterAllowanceState evmS I)
                              (transferFromStoreCurrentAllowance evmS I) I
                              (transferFromStoreCurrentAllowance_receiver evmS I)
                              (hreceiverNZAddr hreceiverZero))
                            hbalanceEnoughS hfitS
                          exact (erc6909TransferFromX_from1323_successCaller_base
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀_evm) (σcur := σAllowance) (A := A)
                              (g := Sat256.ofUInt256 g) (sel := erc6909SelWord I)
                              (base := transferFromAllowanceScratchMem
                                (transferFromOperatorAllowanceScratchMem I) I)
                              (transferFromAllowanceScratchMem_size I hbase)
                              (transferFromAllowanceScratchMem_read64 I hbase hread64)
                              hperm hcanonSender hcanonReceiver hsenderZero hreceiverZero
                              (by simpa [← hAfterAllowanceInit] using hbalanceEnough)
                              (by
                                simpa [← hAfterAllowanceInit, transferFromReceiverCreditNat,
                                  transferFromReceiverBalanceWord,
                                  transferFromAfterSenderBalanceState,
                                  transferFromAfterAllowance_codeOwner,
                                  transferFromTailReceiverCreditNat,
                                  transferFromTailReceiverBalanceWord,
                                  transferFromTailAfterSenderBalanceState,
                                  transferFromSenderDebitWord,
                                  transferFromTailSenderDebitWord] using hfit)
                              rd1323)
                            |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                              (by
                                rw [hPostAsTail]
                                simp [evmE, initState, transferFromTailPostState,
                                  transferFromTailAfterSenderBalanceState,
                                  storageStore_createdAccounts])
                              (accountMapEquiv.of_eq (by
                                rw [hPostAsTail]
                                simp [evmE, initState, transferFromTailPostState,
                                  transferFromTailAfterSenderBalanceState,
                                  storageStore_accountMap]))
                              hσPost
                              (returnEquiv_of_encode
                                (by simpa [boolTy] using boolTrueReturnEncoding))
                        · have hover : UInt256.size ≤ transferFromReceiverCreditNat evmE I := by
                            omega
                          have hbalanceEnoughS :
                              (transferFromAmountWord I).toNat ≤
                                (transferFromSenderBalanceWord
                                  (transferFromAfterAllowanceState evmS I) I).toNat := by
                            simpa [hAfterAllowanceSenderBalance] using hbalanceEnough
                          have hoverS :
                              UInt256.size ≤ transferFromReceiverCreditNat evmS I := by
                            simpa [hReceiverCreditNat] using hover
                          have hbody :=
                            erc6909TransferFromBodyRevertsAllowance_overflow evmS I
                              (by simp only [evmS, initState]; exact hwv) hgate
                              hallowanceNotMaxExpr hallowanceEnoughS
                              (hsenderNZAddr hsenderZero) (hreceiverNZAddr hreceiverZero)
                              hbalanceEnoughS hoverS
                          exact (erc6909TransferFromX_from1323_overflow_base
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀_evm) (σcur := σAllowance) (A := A)
                              (g := Sat256.ofUInt256 g) (sel := erc6909SelWord I)
                              (base := transferFromAllowanceScratchMem
                                (transferFromOperatorAllowanceScratchMem I) I)
                              (transferFromAllowanceScratchMem_size I hbase)
                              (transferFromAllowanceScratchMem_read64 I hbase hread64)
                              hperm hcanonSender hcanonReceiver hsenderZero hreceiverZero
                              (by simpa [← hAfterAllowanceInit] using hbalanceEnough)
                              (by
                                simpa [← hAfterAllowanceInit, transferFromReceiverCreditNat,
                                  transferFromReceiverBalanceWord,
                                  transferFromAfterSenderBalanceState,
                                  transferFromAfterAllowance_codeOwner,
                                  transferFromTailReceiverCreditNat,
                                  transferFromTailReceiverBalanceWord,
                                  transferFromTailAfterSenderBalanceState,
                                  transferFromSenderDebitWord,
                                  transferFromTailSenderDebitWord] using hover)
                              rd1323)
                            |>.reEquivExecutionRevert hcode hd hdec hbody
                      · have hlt :
                            (transferFromSenderBalanceWord
                              (transferFromAfterAllowanceState evmE I) I).toNat <
                              (transferFromAmountWord I).toNat := by
                          omega
                        have hltS :
                            (transferFromSenderBalanceWord
                              (transferFromAfterAllowanceState evmS I) I).toNat <
                              (transferFromAmountWord I).toNat := by
                          simpa [hAfterAllowanceSenderBalance] using hlt
                        have hbody :=
                          erc6909TransferFromBodyRevertsAllowance_insufficient_balance evmS I
                            (by simp only [evmS, initState]; exact hwv) hgate
                            hallowanceNotMaxExpr hallowanceEnoughS
                            (hsenderNZAddr hsenderZero) (hreceiverNZAddr hreceiverZero)
                            hltS
                        exact (erc6909TransferFromX_from1323_insufficient_base
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                            (σ₀ := σ₀_evm) (σcur := σAllowance) (A := A)
                            (g := Sat256.ofUInt256 g) (sel := erc6909SelWord I)
                            (base := transferFromAllowanceScratchMem
                              (transferFromOperatorAllowanceScratchMem I) I)
                            (transferFromAllowanceScratchMem_size I hbase)
                            (transferFromAllowanceScratchMem_read64 I hbase hread64)
                            hcanonSender hsenderZero
                            (by simpa [← hAfterAllowanceInit] using hlt)
                            rd1323)
                          |>.reEquivExecutionRevert hcode hd hdec hbody
                · have hltAllowance :
                      (transferFromCurrentAllowanceWord evmE I).toNat <
                        (transferFromAmountWord I).toNat := by
                    omega
                  have hltAllowanceS :
                      (transferFromCurrentAllowanceWord evmS I).toNat <
                        (transferFromAmountWord I).toNat := by
                    simpa [hAllowance] using hltAllowance
                  have hbody := erc6909TransferFromBodyRevertsAllowance_insufficient evmS I
                    (by simp only [evmS, initState]; exact hwv) hgate
                    hallowanceNotMaxExpr hltAllowanceS
                  exact (erc6909TransferFromX_operatorFalse_insufficientAllowance
                      (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                      hcanonReceiver hsenderCaller hopZero hallowanceNotMax hltAllowance
                      hreach)
                    |>.reEquivExecutionRevert hcode hd hdec hbody
            · have hgate :=
                evalExpr_transferFrom_allowance_gate_false_operator evmS I
                  (by simp [evmS, initState]) hsenderNeSource
                  (by simpa [hOperator] using hopZero)
              by_cases hsenderZero : transferFromSenderWord I = ⟨0⟩
              · have hbody := erc6909TransferFromBodyRevertsNoAllowance_sender_zero evmS I
                  (by simp only [evmS, initState]; exact hwv) hgate
                  (hsenderZeroAddr hsenderZero)
                exact (erc6909TransferFromX_operatorApproved_revert_sender_zero
                    (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                    hcanonReceiver hsenderCaller hopZero hsenderZero hreach)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
              · by_cases hreceiverZero : transferFromReceiverWord I = ⟨0⟩
                · have hbody := erc6909TransferFromBodyRevertsNoAllowance_receiver_zero evmS I
                    (by simp only [evmS, initState]; exact hwv) hgate
                    (hsenderNZAddr hsenderZero) (hreceiverZeroAddr hreceiverZero)
                  exact (erc6909TransferFromX_operatorApproved_revert_receiver_zero
                      (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                      hcanonReceiver hsenderCaller hopZero hsenderZero hreceiverZero hreach)
                    |>.reEquivExecutionRevert hcode hd hdec hbody
                · by_cases henough :
                    (transferFromAmountWord I).toNat ≤
                      (transferFromSenderBalanceWord evmE I).toNat
                  · by_cases hfit : transferFromTailReceiverCreditNat evmE I < UInt256.size
                    · have henoughS :
                          (transferFromAmountWord I).toNat ≤
                            (transferFromSenderBalanceWord evmS I).toNat := by
                        simpa [hTailSenderBalance] using henough
                      have hfitS : transferFromTailReceiverCreditNat evmS I < UInt256.size := by
                        simpa [hTailReceiverCreditNat] using hfit
                      have hbody := erc6909TransferFromBodyCoreNoAllowance evmS I
                        (by simp only [evmS, initState]; exact hwv) hgate
                        (evalExpr_transferFrom_sender_nonzero_true_of_get evmS
                          (transferFromStore I) I (transferFromStore_sender I)
                          (hsenderNZAddr hsenderZero))
                        (evalExpr_transferFrom_receiver_nonzero_true_of_get evmS
                          (transferFromStore I) I (transferFromStore_receiver I)
                          (hreceiverNZAddr hreceiverZero))
                        henoughS hfitS
                      exact (erc6909TransferFromX_operatorApproved_success
                          (g := Sat256.ofUInt256 g) hsz132 hsize hbig hperm
                          hcanonSender hcanonReceiver hsenderCaller hopZero hsenderZero
                          hreceiverZero henough hfit hreach)
                        |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                          (by simp [evmE, initState, transferFromTailPostState,
                            transferFromTailAfterSenderBalanceState,
                            storageStore_createdAccounts])
                          (accountMapEquiv.of_eq (by
                            simp [evmE, initState, transferFromTailPostState,
                              transferFromTailAfterSenderBalanceState,
                              storageStore_accountMap]))
                          hσTailPost
                          (returnEquiv_of_encode
                            (by simpa [boolTy] using boolTrueReturnEncoding))
                    · have hover :
                          UInt256.size ≤ transferFromTailReceiverCreditNat evmE I := by
                        omega
                      have henoughS :
                          (transferFromAmountWord I).toNat ≤
                            (transferFromSenderBalanceWord evmS I).toNat := by
                        simpa [hTailSenderBalance] using henough
                      have hoverS :
                          UInt256.size ≤ transferFromTailReceiverCreditNat evmS I := by
                        simpa [hTailReceiverCreditNat] using hover
                      have hbody := erc6909TransferFromBodyRevertsNoAllowance_overflow evmS I
                        (by simp only [evmS, initState]; exact hwv) hgate
                        (hsenderNZAddr hsenderZero) (hreceiverNZAddr hreceiverZero)
                        henoughS hoverS
                      exact (erc6909TransferFromX_operatorApproved_overflow
                          (g := Sat256.ofUInt256 g) hsz132 hsize hbig hperm
                          hcanonSender hcanonReceiver hsenderCaller hopZero hsenderZero
                          hreceiverZero henough hover hreach)
                        |>.reEquivExecutionRevert hcode hd hdec hbody
                  · have hlt :
                        (transferFromSenderBalanceWord evmE I).toNat <
                          (transferFromAmountWord I).toNat := by
                      omega
                    have hltS :
                        (transferFromSenderBalanceWord evmS I).toNat <
                          (transferFromAmountWord I).toNat := by
                      simpa [hTailSenderBalance] using hlt
                    have hbody := erc6909TransferFromBodyRevertsNoAllowance_insufficient evmS I
                      (by simp only [evmS, initState]; exact hwv) hgate
                      (hsenderNZAddr hsenderZero) (hreceiverNZAddr hreceiverZero) hltS
                    exact (erc6909TransferFromX_operatorApproved_insufficient
                        (g := Sat256.ofUInt256 g) hsz132 hsize hbig hcanonSender
                        hcanonReceiver hsenderCaller hopZero hsenderZero hreceiverZero hlt
                        hreach)
                      |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hdec := erc6909Decode_transferFrom_none_noncanon_receiver (I := I)
            hsz132 hbig hcanonSender hcanonReceiver
          have hnc : UInt256.eq (transferFromReceiverWord I)
              (UInt256.land (transferFromReceiverWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne
              (fun he => hcanonReceiver (solcAddrCanonical_of_clean he))
          exact (erc6909TransferFromX_noncanon_receiver (g := Sat256.ofUInt256 g)
              hsz132 hsize hbig hcanonSender hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := erc6909Decode_transferFrom_none_noncanon_sender (I := I)
          hsz132 hbig hcanonSender
        have hnc : UInt256.eq (transferFromSenderWord I)
            (UInt256.land (transferFromSenderWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne
            (fun he => hcanonSender (solcAddrCanonical_of_clean he))
        exact (erc6909TransferFromX_noncanon_sender (g := Sat256.ofUInt256 g)
            hsz132 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc6909Decode_transferFrom_none_huge (I := I) hbigge
      exact (erc6909TransferFromX_hugearg (g := Sat256.ofUInt256 g)
          hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 132 := by omega
    have hdec := erc6909Decode_transferFrom_none_short (I := I) hsz4 hshort
    exact (erc6909TransferFromX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end OpenZeppelinBench.ERC6909
