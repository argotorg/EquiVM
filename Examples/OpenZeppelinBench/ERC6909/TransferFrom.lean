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

def transferFromSenderBalanceSlot (I : ExecutionEnv) : UInt256 :=
  balanceSlot (.address (AccountAddress.ofNat (transferFromSenderWord I).toNat))
    (.int (Int.ofNat (transferFromIdWord I).toNat))

def transferFromReceiverBalanceSlot (I : ExecutionEnv) : UInt256 :=
  balanceSlot (.address (AccountAddress.ofNat (transferFromReceiverWord I).toNat))
    (.int (Int.ofNat (transferFromIdWord I).toNat))

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

theorem transferFromReceiverCreditWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromReceiverCreditNat evm I < UInt256.size) :
    (transferFromReceiverCreditWord evm I).toNat = transferFromReceiverCreditNat evm I := by
  unfold transferFromReceiverCreditWord
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

end OpenZeppelinBench.ERC6909
