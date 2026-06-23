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
set_option maxHeartbeats 2000000

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

abbrev transferFromStore (I : ExecutionEnv) : Store :=
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

abbrev transferFromStoreCurrentAllowance (evm : EVM.State) (I : ExecutionEnv) : Store :=
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

abbrev transferFromStoreFromBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
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

abbrev transferFromStoreToBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
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

abbrev transferFromTailStoreFromBalance (locals : Store) (evm : EVM.State)
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

abbrev transferFromTailStoreToBalance (locals : Store) (evm : EVM.State)
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

/-- Source-side core for the allowance-debit success path of
`transferFrom(address,address,uint256,uint256)`.

The hypotheses name the branch guards that the EVM body at pc 388 must establish on this path.  The
state threading below is deliberately explicit: the sender balance is read from
`transferFromAfterAllowanceState`, after the allowance write.
-/
theorem erc6909TransferFromBodyCore (evm : EVM.State) (I : ExecutionEnv)
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
    refine ExecBlock.consNormal
      (ExecStmt.iteTrue
        (result := .ok { contract := contract, locals := transferFromStoreCurrentAllowance evm I }
          (transferFromAfterAllowanceState evm I))
        hallowanceNotMax ?_) ?_
    · refine ExecBlock.consNormal
        (ExecStmt.requireTrue
          (evalExpr_transferFrom_allowance_ge_true evm I hallowanceEnough)) ?_
      refine ExecBlock.consNormal
        (ExecStmt.assign
          (evalExpr_transferFrom_allowance_debit evm I hallowanceEnough)
          (transferFromAssignAllowance evm I)) ?_
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

end OpenZeppelinBench.ERC6909
