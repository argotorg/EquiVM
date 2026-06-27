import Examples.SimpleAuction.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace SimpleAuction

/-! ## `bid()` local words, storage slots, and small EVM helpers -/

def bidTimestampWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

def bidAuctionEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)

def bidHighestBidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨3⟩ ⟨0⟩)

def bidHighestBidderRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)

def bidHighestBidderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (bidHighestBidderRawWord σ I) solcAddrMask

def bidHighestBidderKey (σ : AccountMap) (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (bidHighestBidderWord σ I).toNat)

def bidPendingSlot (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  pendingReturnsSlot (bidHighestBidderKey σ I)

def bidPendingReturnsWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (bidPendingSlot σ I) ⟨0⟩)

def bidSenderWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

def bidPackedSenderWord (old : UInt256) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor (bidSenderWord I) (UInt256.land (UInt256.lnot solcAddrMask) old)

def bidPendingMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (bidPendingSlot σ I)
    (bidPendingReturnsWord σ I + bidHighestBidWord σ I)

def bidWriteHighestBidderMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨2⟩
    (bidPackedSenderWord (bidHighestBidderRawWord σ I) I)

def bidWriteHighestBidMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨3⟩ I.weiValue

def bidFinalMapNoPending (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  bidWriteHighestBidMap (bidWriteHighestBidderMap σ I) I

def bidFinalMapWithPending (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  bidWriteHighestBidMap (bidWriteHighestBidderMap (bidPendingMap σ I) I) I

noncomputable def bidPendingBaseMem : ByteArray :=
  (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 solcFreePtrMem 32 32

noncomputable def bidPendingHashMem (key : UInt256) : ByteArray :=
  (UInt256.toByteArray key).write 0 bidPendingBaseMem 0 32

noncomputable def bidPendingKeyMem (key : UInt256) : ByteArray :=
  (UInt256.toByteArray key).write 0 solcFreePtrMem 0 32

def bidAuctionAlreadyEndedSelector : UInt256 :=
  UInt256.shiftLeft (⟨0xd02e774d⟩ : UInt256) ⟨224⟩

def bidNotHighEnoughSelector : UInt256 :=
  UInt256.shiftLeft (⟨0x4e12c1bb⟩ : UInt256) ⟨224⟩

noncomputable def bidNotHighEnoughMem (high : UInt256) : ByteArray :=
  (UInt256.toByteArray high).write 0 (solcReturnMem bidNotHighEnoughSelector) 132 32

def bidHighestBidIncreasedTopic : UInt256 :=
  ⟨0xf4757a49b326036464bec6fe419a4ae38c8a02ce3e68bf0809674f6aab8ad300⟩

noncomputable def bidEventMemCaller (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (bidSenderWord I)).write 0 solcFreePtrMem 128 32

noncomputable def bidEventMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray I.weiValue).write 0 (bidEventMemCaller I) 160 32

noncomputable def bidPendingEventMemCaller (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (bidSenderWord I)).write 0
    (bidPendingHashMem (bidHighestBidderWord σ I)) 128 32

noncomputable def bidPendingEventMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray I.weiValue).write 0 (bidPendingEventMemCaller σ I) 160 32

theorem bidSenderWord_canonical (I : ExecutionEnv) :
    (bidSenderWord I).toNat < EVM.addressModulus := by
  unfold bidSenderWord
  rw [ulit_toNat' _ (lt_of_lt_of_le I.source.isLt (by decide))]
  exact I.source.isLt

theorem bidPendingSlot_eq (σ : AccountMap) (I : ExecutionEnv) :
    bidPendingSlot σ I = simpleAuctionMappingSlot (bidHighestBidderWord σ I) ⟨4⟩ := by
  unfold bidPendingSlot pendingReturnsSlot simpleAuctionMappingSlot bidHighestBidderKey
  rw [keyValueToWord_address_of_canonical]
  exact solcAddrMask_result_canonical (bidHighestBidderRawWord σ I)

theorem bidPendingBaseMem_size : bidPendingBaseMem.size = 96 := by
  unfold bidPendingBaseMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  norm_num

theorem bidPendingHashMem_size (key : UInt256) : (bidPendingHashMem key).size = 96 := by
  unfold bidPendingHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [bidPendingBaseMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, bidPendingBaseMem_size, toByteArray_size]
  norm_num

theorem bidPendingKeyMem_size (key : UInt256) : (bidPendingKeyMem key).size = 96 := by
  unfold bidPendingKeyMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  norm_num

theorem bidPendingHashMem_writeSlot (key : UInt256) :
    (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 (bidPendingKeyMem key) 32 32 =
      bidPendingHashMem key := by
  unfold bidPendingKeyMem bidPendingHashMem bidPendingBaseMem
  rw [write32_eq _ solcFreePtrMem 0 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega)]
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
    omega)]
  rw [write32_eq _ solcFreePtrMem 32 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega)]
  rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
    omega)]
  have hkeyFull : (UInt256.toByteArray key).extract 0 32 = UInt256.toByteArray key := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray key).size ≤ 32
      rw [toByteArray_size])
  have hslotFull :
      (UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨4⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨4⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  rw [hkeyFull, hslotFull]
  have hsolc0 : solcFreePtrMem.extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hsolc0, ByteArray.empty_append]
  rw [show 0 + 32 = 32 from rfl, show 32 + 32 = 64 from rfl, solcFreePtrMem_size]
  have hleft0 :
      (UInt256.toByteArray key ++ solcFreePtrMem.extract 32 96).extract 0 32 =
        UInt256.toByteArray key := by
    rw [extract_append_left _ _ _ _ (by rw [toByteArray_size])]
    exact hkeyFull
  rw [hleft0]
  have hleftTail :
      (UInt256.toByteArray key ++ solcFreePtrMem.extract 32 96).extract 64
          (UInt256.toByteArray key ++ solcFreePtrMem.extract 32 96).size =
        solcFreePtrMem.extract 64 96 := by
    rw [extract_append_right_window _ _ _ _ (by rw [toByteArray_size]; omega)]
    rw [ByteArray.size_append, toByteArray_size, ByteArray.size_extract, solcFreePtrMem_size]
    rw [extract_extract_BA]
    rfl
  rw [hleftTail]
  have hrightZero :
      (solcFreePtrMem.extract 0 32 ++ UInt256.toByteArray (⟨4⟩ : UInt256) ++
          solcFreePtrMem.extract 64 96).extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hrightZero, ByteArray.empty_append]
  have hrightTail :
      (solcFreePtrMem.extract 0 32 ++ UInt256.toByteArray (⟨4⟩ : UInt256) ++
          solcFreePtrMem.extract 64 96).extract 32
        (solcFreePtrMem.extract 0 32 ++ UInt256.toByteArray (⟨4⟩ : UInt256) ++
          solcFreePtrMem.extract 64 96).size =
      UInt256.toByteArray (⟨4⟩ : UInt256) ++ solcFreePtrMem.extract 64 96 := by
    rw [ByteArray.append_assoc]
    exact extract_append_right' _ _ _ _
      (by rw [ByteArray.size_extract, solcFreePtrMem_size]; omega)
      (by
        rw [ByteArray.size_append, ByteArray.size_extract, solcFreePtrMem_size])
  rw [hrightTail]
  exact ByteArray.append_assoc

theorem bidPendingBaseMem_read32 :
    bidPendingBaseMem.readWithPadding 32 32 = UInt256.toByteArray (⟨4⟩ : UInt256) := by
  unfold bidPendingBaseMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [solcFreePtrMem_size]; omega)]
  rw [show (UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨4⟩ : UInt256) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
        show (UInt256.toByteArray (⟨4⟩ : UInt256)).data.size ≤ 32
        rw [show (UInt256.toByteArray (⟨4⟩ : UInt256)).data.size =
          (UInt256.toByteArray (⟨4⟩ : UInt256)).size from rfl, toByteArray_size]]

theorem bidPendingHashMem_read0_64 (key : UInt256) :
    (bidPendingHashMem key).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray (⟨4⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' (bidPendingHashMem key) 0 64
    (by norm_num) (by norm_num) (by rw [bidPendingHashMem_size]; omega)]
  unfold bidPendingHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [bidPendingBaseMem_size]; omega)]
  have hempty : bidPendingBaseMem.extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    simp
  rw [hempty, empty_append]
  have hfirst :
      ((UInt256.toByteArray key ++ bidPendingBaseMem.extract 32 bidPendingBaseMem.size).extract
          0 64) =
        UInt256.toByteArray key ++
          (bidPendingBaseMem.extract 32 bidPendingBaseMem.size).extract 0 32 := by
    rw [extract_append_span (UInt256.toByteArray key)
      (bidPendingBaseMem.extract 32 bidPendingBaseMem.size) 0 64
      (by omega) (by rw [toByteArray_size]; omega)]
    rw [show (UInt256.toByteArray key).extract 0 (UInt256.toByteArray key).size =
        UInt256.toByteArray key from by
          apply ByteArray.ext
          rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
          rfl]
    rw [toByteArray_size]
  rw [show (UInt256.toByteArray key).extract 0 32 = UInt256.toByteArray key from by
      apply ByteArray.ext
      rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
      show (UInt256.toByteArray key).data.size ≤ 32
      rw [show (UInt256.toByteArray key).data.size =
        (UInt256.toByteArray key).size from rfl, toByteArray_size]]
  simp only [Nat.zero_add]
  rw [hfirst]
  have htail :
      (bidPendingBaseMem.extract 32 bidPendingBaseMem.size).extract 0 32 =
        UInt256.toByteArray (⟨4⟩ : UInt256) := by
    rw [extract_extract_BA]
    rw [show 32 + 0 = 32 by norm_num]
    rw [show min (32 + 32) bidPendingBaseMem.size = 64 by
      rw [bidPendingBaseMem_size]; norm_num]
    rw [← readWithPadding_eq_extract bidPendingBaseMem 32
      (by rw [bidPendingBaseMem_size]; omega)]
    exact bidPendingBaseMem_read32
  rw [htail]

theorem bidPendingHashMem_read64 (key : UInt256) :
    (bidPendingHashMem key).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold bidPendingHashMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [bidPendingBaseMem_size]; omega) (by omega) (by rw [bidPendingBaseMem_size])]
  unfold bidPendingBaseMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [solcFreePtrMem_size]; omega) (by omega) (by rw [solcFreePtrMem_size])]
  exact solcFreePtrMem_read64

theorem bidPendingHashMem_mload64 (key : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (bidPendingHashMem key).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((bidPendingHashMem key).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [bidPendingHashMem_size]; decide) (by decide)
    (bidPendingHashMem_read64 key)

theorem bidNotHighEnoughMem_size (high : UInt256) : (bidNotHighEnoughMem high).size = 164 := by
  unfold bidNotHighEnoughMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcReturnMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    solcReturnMem_size, toByteArray_size]
  norm_num

theorem bidNotHighEnoughMem_read64 (high : UInt256) :
    (bidNotHighEnoughMem high).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold bidNotHighEnoughMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [solcReturnMem_size]; omega) (by omega)]
  exact solcReturnMem_read64 bidNotHighEnoughSelector

theorem bidNotHighEnoughMem_mload64 (high : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (bidNotHighEnoughMem high).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((bidNotHighEnoughMem high).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [bidNotHighEnoughMem_size]; decide) (by decide)
    (bidNotHighEnoughMem_read64 high)

theorem bidEventMemCaller_size (I : ExecutionEnv) : (bidEventMemCaller I).size = 160 := by
  simpa [bidEventMemCaller, solcReturnMem] using solcReturnMem_size (bidSenderWord I)

theorem bidEventMem_size (I : ExecutionEnv) : (bidEventMem I).size = 192 := by
  unfold bidEventMem
  rw [toByteArray_write_eq _ _ 160 (by rw [bidEventMemCaller_size])
      (by rw [bidEventMemCaller_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, bidEventMemCaller_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem bidEventMem_read64 (I : ExecutionEnv) :
    (bidEventMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold bidEventMem
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size])
    (by rw [bidEventMemCaller_size]) (by omega)]
  simpa [bidEventMemCaller, solcReturnMem] using solcReturnMem_read64 (bidSenderWord I)

theorem bidEventMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (bidEventMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((bidEventMem I).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [bidEventMem_size]; decide) (by decide) (bidEventMem_read64 I)

theorem bidPendingEventMemCaller_size (σ : AccountMap) (I : ExecutionEnv) :
    (bidPendingEventMemCaller σ I).size = 160 := by
  unfold bidPendingEventMemCaller
  rw [toByteArray_write_eq _ _ 128 (by rw [bidPendingHashMem_size]; omega)
      (by rw [bidPendingHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, bidPendingHashMem_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem bidPendingEventMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (bidPendingEventMem σ I).size = 192 := by
  unfold bidPendingEventMem
  rw [toByteArray_write_eq _ _ 160 (by rw [bidPendingEventMemCaller_size])
      (by rw [bidPendingEventMemCaller_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, bidPendingEventMemCaller_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem bidPendingEventMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (bidPendingEventMem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold bidPendingEventMem
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size])
    (by rw [bidPendingEventMemCaller_size]) (by omega)]
  unfold bidPendingEventMemCaller
  rw [toByteArray_write_eq _ _ 128 (by rw [bidPendingHashMem_size]; omega)
      (by rw [bidPendingHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, bidPendingHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, bidPendingHashMem_size, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
    norm_num)]
  rw [extract_append_left (bidPendingHashMem (bidHighestBidderWord σ I))
      (ffi.ByteArray.zeroes
        (USize.ofNat (128 - (bidPendingHashMem (bidHighestBidderWord σ I)).size))) 64 96
      (by rw [bidPendingHashMem_size])]
  rw [← readWithPadding_eq_extract (bidPendingHashMem (bidHighestBidderWord σ I)) 64
    (by rw [bidPendingHashMem_size])]
  exact bidPendingHashMem_read64 (bidHighestBidderWord σ I)

theorem bidPendingEventMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (bidPendingEventMem σ I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((bidPendingEventMem σ I).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [bidPendingEventMem_size]; decide) (by decide)
    (bidPendingEventMem_read64 σ I)

theorem bidPendingKeccak (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC ((bidPendingHashMem (bidHighestBidderWord σ I)).readWithPadding 0 64)))
      = bidPendingSlot σ I := by
  rw [bidPendingHashMem_read0_64, bidPendingSlot_eq]
  exact mappingSlot_single (bidHighestBidderWord σ I) ⟨4⟩

theorem bidStorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (simpleAuctionUint256Loc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  exact simpleAuctionStorageLocStore_uint256 evm slot val

theorem bidSolcAddrMask_eval :
    UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
  decide

theorem bidCheckedAddNoOverflowGt (a b : UInt256)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    UInt256.gt a (b + a) = ⟨0⟩ := by
  have hsum : (b + a).toNat = b.toNat + a.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (by omega)]
  exact ugt_zero (by rw [hsum]; omega)

theorem bidCheckedAddOverflowGt (a b : UInt256)
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    UInt256.gt a (b + a) = ⟨1⟩ := by
  have hover' : UInt256.size ≤ b.toNat + a.toNat := by omega
  have hsum_lt2 : b.toNat + a.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (b.toNat + a.toNat) % UInt256.size =
      b.toNat + a.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover']
    rw [Nat.mod_eq_of_lt (by omega)]
  have hsum : (b + a).toNat = b.toNat + a.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  show UInt256.fromBool (decide (a > b + a)) = ⟨1⟩
  rw [decide_eq_true]
  · rfl
  · show a.toNat > (b + a).toNat
    rw [hsum]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega

theorem bidCheckedAddOk {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD simpleAuctionBytecode ee g s0 ⟨956⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J simpleAuctionBytecode 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD simpleAuctionBytecode ee g s0 ret ((b + a) :: R) mem aw rdata acc k' C' := by
  have hgt : UInt256.gt a (b + a) = ⟨0⟩ := bidCheckedAddNoOverflowGt a b hfit
  have rd964₀ := evm_run h with [
    jumpdest, dup1, dup3, add, dup1, dup3, gt]
  have rd964 := rd964₀
  rw [hgt] at rd964
  have rd967₀ := evm_run rd964 with [iszero]
  have rd967 := rd967₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd967
  have rd987 := evm_run rd967 with [
    push2 ⟨987⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, evm_run rd987 with [
    jumpdest, swap3, swap2, pop, pop, jump hret]⟩

theorem bidPanicOverflowRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD simpleAuctionBytecode ee g s0 ⟨968⟩ R mem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    RDrev simpleAuctionBytecode g s0 := by
  have hsel : UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
      ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ := by
    decide
  have rd977₀ := evm_run h with [
    push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd977 := rd977₀
  rw [hsel] at rd977
  have rd982 := evm_run rd977 with [
    raw mstore 0
      ((UInt256.toByteArray
        (⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ :
          UInt256)).write 0 mem 0 32)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨17⟩, push1 ⟨4⟩]
  have rd986 := evm_run rd982 with [
    raw mstore 0
      ((UInt256.toByteArray (⟨17⟩ : UInt256)).write 0
        ((UInt256.toByteArray
          (⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ :
            UInt256)).write 0 mem 0 32) 4 32)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, push0]
  exact rd986.rev 0 (by decide) mem_cost (by evm_ov)

theorem bidCheckedAddOverflow {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {a b ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD simpleAuctionBytecode ee g s0 ⟨956⟩ (a :: b :: ret :: R) mem (UInt256.ofNat 3)
      rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat) (hov : R.length + 9 ≤ 1024) :
    RDrev simpleAuctionBytecode g s0 := by
  have hgt : UInt256.gt a (b + a) = ⟨1⟩ := bidCheckedAddOverflowGt a b hover
  have rd964₀ := evm_run h with [
    jumpdest, dup1, dup3, add, dup1, dup3, gt]
  have rd964 := rd964₀
  rw [hgt] at rd964
  have rd967₀ := evm_run rd964 with [iszero]
  have rd967 := rd967₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd967
  have rd968 := evm_run rd967 with [push2 ⟨987⟩, jumpiNT (by decide)]
  exact bidPanicOverflowRevert rd968 (by evm_ov)

theorem simpleAuctionBidSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x19, 0x98, 0xae, 0xef]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x19, 0x98, 0xae, 0xef]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem simpleAuctionDispatch_bid {cd : ByteArray}
    (hsel : ((⟨#[0x19, 0x98, 0xae, 0xef]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg simpleAuctionContract cd = some bidTransition := by
  refine dispatchMsg_eq_some_of_split
    (pre := []) (post := [withdrawTransition, auctionEndTransition, beneficiaryGetter,
      auctionEndTimeGetter, highestBidderGetter, highestBidGetter]) rfl ?_
      (by rw [selectorOf, simpleAuctionBidSelectorBytes]; exact hsel)
  intro _ ht
  simp at ht

theorem simpleAuctionDecode_bid {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (bidTransition.params.map Param.name)
      (transitionSignature bidTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem simpleAuctionX_bidToBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨326⟩
      [⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd114⟩ := hreach
  exact ⟨_, _, evm_run rd114 with [jumpdest, push2 ⟨122⟩, push2 ⟨326⟩,
    jump (by jump_dest)]⟩

theorem simpleAuctionX_bid_timeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (bidAuctionEndWord σ I).toNat < (bidTimestampWord I).toNat) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd326⟩ := simpleAuctionX_bidToBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hreach
  have rd329 := evm_run rd326 with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd330₀⟩ := rd329.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd330⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨330⟩
      [bidAuctionEndWord σ I, ⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bidAuctionEndWord, initState] using rd330₀⟩
  have hgt : UInt256.gt (bidTimestampWord I) (bidAuctionEndWord σ I) = ⟨1⟩ :=
    ugt_one htime
  have rd331 := RD.timestamp rd330 (by decide) (by evm_ov)
  have rd333₀ := evm_run rd331 with [gt, iszero]
  have rd333 := rd333₀
  rw [show UInt256.gt (UInt256.ofNat I.header.timestamp) (bidAuctionEndWord σ I) = ⟨1⟩
      from by simpa [bidTimestampWord] using hgt,
    show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd333
  have rd337 := evm_run rd333 with [push2 ⟨361⟩, jumpiNT (by decide)]
  let errSel : UInt256 := UInt256.shiftLeft (⟨0xd02e774d⟩ : UInt256) ⟨224⟩
  have rd350 := evm_run rd337 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0xd02e774d⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 6 (solcReturnMem errSel) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rfl)
      (by decide) (by evm_ov)]
  have rd360 := evm_run rd350 with [
    push1 ⟨4⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 errSel) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact rd360.rev 0 (by decide) mem_cost (by evm_ov)

theorem simpleAuctionX_bid_afterTime {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (bidTimestampWord I).toNat ≤ (bidAuctionEndWord σ I).toNat) :
    ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨361⟩
      [⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd326⟩ := simpleAuctionX_bidToBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hreach
  have rd329 := evm_run rd326 with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd330₀⟩ := rd329.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd330⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨330⟩
      [bidAuctionEndWord σ I, ⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bidAuctionEndWord, initState] using rd330₀⟩
  have hgt : UInt256.gt (bidTimestampWord I) (bidAuctionEndWord σ I) = ⟨0⟩ :=
    ugt_zero htime
  have rd331 := RD.timestamp rd330 (by decide) (by evm_ov)
  have rd333₀ := evm_run rd331 with [gt, iszero]
  have rd333 := rd333₀
  rw [show UInt256.gt (UInt256.ofNat I.header.timestamp) (bidAuctionEndWord σ I) = ⟨0⟩
      from by simpa [bidTimestampWord] using hgt,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd333
  exact ⟨_, _, evm_run rd333 with [push2 ⟨361⟩, jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem simpleAuctionX_bid_bidRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (bidTimestampWord I).toNat ≤ (bidAuctionEndWord σ I).toNat)
    (hbid : I.weiValue.toNat ≤ (bidHighestBidWord σ I).toNat) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd361⟩ := simpleAuctionX_bid_afterTime (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hreach htime
  have rd364 := evm_run rd361 with [jumpdest, push1 ⟨3⟩]
  obtain ⟨_, _, rd365₀⟩ := rd364.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd365⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨365⟩
      [bidHighestBidWord σ I, ⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bidHighestBidWord, initState] using rd365₀⟩
  have hgt : UInt256.gt I.weiValue (bidHighestBidWord σ I) = ⟨0⟩ :=
    ugt_zero hbid
  have rd367₀ := evm_run rd365 with [callvalue, gt]
  have rd367 := rd367₀
  rw [hgt] at rd367
  have rd371 := evm_run rd367 with [push2 ⟨410⟩, jumpiNT (by decide)]
  have rd374 := evm_run rd371 with [push1 ⟨3⟩]
  obtain ⟨_, _, rd374₀⟩ := rd374.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd374'⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨374⟩
      [bidHighestBidWord σ I, ⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bidHighestBidWord, initState] using rd374₀⟩
  have rd387 := evm_run rd374' with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x4e12c1bb⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 6 (solcReturnMem bidNotHighEnoughSelector) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rfl)
      (by decide) (by evm_ov)]
  have rd401 := evm_run rd387 with [
    push1 ⟨4⟩, add, push2 ⟨401⟩, swap2, dup2,
    raw mstore 3 (bidNotHighEnoughMem (bidHighestBidWord σ I)) (UInt256.ofNat 6)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, jump (by jump_dest), jumpdest]
  have rd409 := evm_run rd401 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (bidNotHighEnoughMem_mload64 (bidHighestBidWord σ I)) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact rd409.rev 0 (by decide) mem_cost (by evm_ov)

theorem simpleAuctionX_bid_afterBid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (bidTimestampWord I).toNat ≤ (bidAuctionEndWord σ I).toNat)
    (hbid : (bidHighestBidWord σ I).toNat < I.weiValue.toNat) :
    ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨410⟩
      [⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd361⟩ := simpleAuctionX_bid_afterTime (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hreach htime
  have rd364 := evm_run rd361 with [jumpdest, push1 ⟨3⟩]
  obtain ⟨_, _, rd365₀⟩ := rd364.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd365⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨365⟩
      [bidHighestBidWord σ I, ⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bidHighestBidWord, initState] using rd365₀⟩
  have hgt : UInt256.gt I.weiValue (bidHighestBidWord σ I) = ⟨1⟩ :=
    ugt_one hbid
  have rd367₀ := evm_run rd365 with [callvalue, gt]
  have rd367 := rd367₀
  rw [hgt] at rd367
  exact ⟨_, _, evm_run rd367 with [push2 ⟨410⟩, jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem simpleAuctionX_bid_afterNoPending {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (bidTimestampWord I).toNat ≤ (bidAuctionEndWord σ I).toNat)
    (hbid : (bidHighestBidWord σ I).toNat < I.weiValue.toNat)
    (hzero : bidHighestBidWord σ I = ⟨0⟩) :
    ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨468⟩
      [⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd410⟩ := simpleAuctionX_bid_afterBid (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hreach htime hbid
  have rd413 := evm_run rd410 with [jumpdest, push1 ⟨3⟩]
  obtain ⟨_, _, rd414₀⟩ := rd413.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd414⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨414⟩
      [bidHighestBidWord σ I, ⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bidHighestBidWord, initState] using rd414₀⟩
  have rd415₀ := evm_run rd414 with [iszero]
  have rd415 := rd415₀
  rw [hzero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd415
  exact ⟨_, _, evm_run rd415 with [push2 ⟨468⟩, jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem simpleAuctionX_bid_pendingToCheckedAdd {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (bidTimestampWord I).toNat ≤ (bidAuctionEndWord σ I).toNat)
    (hbid : (bidHighestBidWord σ I).toNat < I.weiValue.toNat)
    (hnz : bidHighestBidWord σ I ≠ ⟨0⟩) :
    ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨956⟩
      [bidPendingReturnsWord σ I, bidHighestBidWord σ I, ⟨462⟩, ⟨0⟩,
        bidPendingSlot σ I, bidHighestBidWord σ I, ⟨122⟩, simpleAuctionSelWord I]
      (bidPendingHashMem (bidHighestBidderWord σ I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd410⟩ := simpleAuctionX_bid_afterBid (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hreach htime hbid
  have rd413 := evm_run rd410 with [jumpdest, push1 ⟨3⟩]
  obtain ⟨_, _, rd414₀⟩ := rd413.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd414⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨414⟩
      [bidHighestBidWord σ I, ⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bidHighestBidWord, initState] using rd414₀⟩
  have rd415₀ := evm_run rd414 with [iszero]
  have rd415 := rd415₀
  rw [isZero_eq_zero_of_ne hnz] at rd415
  have rd419 := evm_run rd415 with [push2 ⟨468⟩, jumpiNT (by decide)]
  have rd421 := evm_run rd419 with [push1 ⟨3⟩]
  obtain ⟨_, _, rd422₀⟩ := rd421.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd422⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨422⟩
      [bidHighestBidWord σ I, ⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bidHighestBidWord, initState] using rd422₀⟩
  have rd424 := evm_run rd422 with [push1 ⟨2⟩]
  obtain ⟨_, _, rd425₀⟩ := rd424.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd425⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨425⟩
      [bidHighestBidderRawWord σ I, bidHighestBidWord σ I, ⟨122⟩, simpleAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bidHighestBidderRawWord, initState] using rd425₀⟩
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have rd435₀ := evm_run rd425 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, push0, swap1, dup2]
  have rd435 := rd435₀
  rw [hmask, u256_land_comm solcAddrMask (bidHighestBidderRawWord σ I)] at rd435
  have rd438 := evm_run rd435 with [
    raw mstore 0 (bidPendingKeyMem (bidHighestBidderWord σ I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩]
  have rd443 := evm_run rd438 with [
    raw mstore 0 (bidPendingHashMem (bidHighestBidderWord σ I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        change (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
            (bidPendingKeyMem (bidHighestBidderWord σ I)) 32 32 =
          bidPendingHashMem (bidHighestBidderWord σ I)
        exact bidPendingHashMem_writeSlot (bidHighestBidderWord σ I))
      (by decide) (by evm_ov),
    push1 ⟨64⟩, dup2]
  have rd447 := evm_run rd443 with [
    raw keccak256 0 (bidPendingSlot σ I) (UInt256.ofNat 3) (by decide)
      mem_cost (bidPendingKeccak σ I) (by decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd448₀⟩ := rd447.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd449⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩
      [bidPendingReturnsWord σ I, bidPendingSlot σ I, ⟨0⟩, bidHighestBidWord σ I,
        ⟨122⟩, simpleAuctionSelWord I]
      (bidPendingHashMem (bidHighestBidderWord σ I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
    exact ⟨_, _, by simpa [bidPendingReturnsWord, initState] using rd448₀⟩
  have rd461 := evm_run rd449 with [
    swap1, swap2, swap1, push2 ⟨462⟩, swap1, dup5, swap1, push2 ⟨956⟩,
    jump (by jump_dest)]
  exact ⟨_, _, rd461⟩

theorem simpleAuctionX_bid_afterPending {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (bidTimestampWord I).toNat ≤ (bidAuctionEndWord σ I).toNat)
    (hbid : (bidHighestBidWord σ I).toNat < I.weiValue.toNat)
    (hnz : bidHighestBidWord σ I ≠ ⟨0⟩)
    (hfit :
      (bidPendingReturnsWord σ I).toNat + (bidHighestBidWord σ I).toNat < UInt256.size) :
    ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨468⟩
      [⟨122⟩, simpleAuctionSelWord I] (bidPendingHashMem (bidHighestBidderWord σ I))
      (UInt256.ofNat 3) ByteArray.empty (cA, bidPendingMap σ I) k C := by
  obtain ⟨_, _, rd956⟩ := simpleAuctionX_bid_pendingToCheckedAdd (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hreach htime hbid hnz
  obtain ⟨_, _, rd462⟩ := bidCheckedAddOk rd956 hfit (by jump_dest) (by evm_ov)
  have rd465 := evm_run rd462 with [jumpdest, swap1, swap2]
  obtain ⟨_, _, rd466₀⟩ := rd465.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd466⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨466⟩
      [⟨0⟩, bidHighestBidWord σ I, ⟨122⟩, simpleAuctionSelWord I]
      (bidPendingHashMem (bidHighestBidderWord σ I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, bidPendingMap σ I) k C := by
    exact ⟨_, _, by
      simpa [bidPendingMap, u256_add_comm] using rd466₀⟩
  exact ⟨_, _, evm_run rd466 with [pop, pop]⟩

theorem simpleAuctionX_bid_pendingOverflow {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (bidTimestampWord I).toNat ≤ (bidAuctionEndWord σ I).toNat)
    (hbid : (bidHighestBidWord σ I).toNat < I.weiValue.toNat)
    (hnz : bidHighestBidWord σ I ≠ ⟨0⟩)
    (hover : UInt256.size ≤
      (bidPendingReturnsWord σ I).toNat + (bidHighestBidWord σ I).toNat) :
    RDrev simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd956⟩ := simpleAuctionX_bid_pendingToCheckedAdd (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hreach htime hbid hnz
  exact bidCheckedAddOverflow rd956 hover (by evm_ov)

theorem simpleAuctionX_bid_successNoPending {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (bidTimestampWord I).toNat ≤ (bidAuctionEndWord σ I).toNat)
    (hbid : (bidHighestBidWord σ I).toNat < I.weiValue.toNat)
    (hzero : bidHighestBidWord σ I = ⟨0⟩) :
    RDret simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, bidFinalMapNoPending σ I) ByteArray.empty := by
  obtain ⟨_, _, rd468⟩ := simpleAuctionX_bid_afterNoPending (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hreach htime hbid hzero
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have rd472 := evm_run rd468 with [jumpdest, push1 ⟨2⟩, dup1]
  obtain ⟨_, _, rd473₀⟩ := rd472.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd473⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨473⟩
      [bidHighestBidderRawWord σ I, ⟨2⟩, ⟨122⟩, simpleAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bidHighestBidderRawWord, initState] using rd473₀⟩
  have rd486₀ := evm_run rd473 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and, caller, swap1, dup2]
  have rd486 := rd486₀
  rw [hmask] at rd486
  have rd487 := RD.lor rd486 (by decide) (by evm_ov)
  have rd489 := evm_run rd487 with [swap1, swap2]
  obtain ⟨_, _, rd490⟩ := rd489.sstore hperm (by decide) (by evm_ov)
  have rd495 := evm_run rd490 with [callvalue, push1 ⟨3⟩, dup2, swap1]
  obtain ⟨_, _, rd496⟩ := rd495.sstore hperm (by decide) (by evm_ov)
  have rd499 := evm_run rd496 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd502 := evm_run rd499 with [
    swap3, dup4,
    raw mstore 6 (bidEventMemCaller I) (UInt256.ofNat 5) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd510 := evm_run rd502 with [
    push1 ⟨32⟩, dup4, add, swap2, swap1, swap2,
    raw mstore 3 (bidEventMem I) (UInt256.ofNat 6) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd544 := rd510.pushConst bidHighestBidIncreasedTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd553 := evm_run rd544 with [
    swap2, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (bidEventMem_mload64 I) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have hlen64 : ((⟨128⟩ : UInt256) + ⟨64⟩).sub ⟨128⟩ = ⟨64⟩ := by decide
  have rd553' := rd553
  rw [hlen64] at rd553'
  have rd554 := RD.log1 0 (UInt256.ofNat 6) rd553' (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by decide) (by evm_ov)
  have rd123 := evm_run rd554 with [jump (by jump_dest), jumpdest]
  simpa [bidFinalMapNoPending, bidWriteHighestBidMap, bidWriteHighestBidderMap,
    bidPackedSenderWord, bidSenderWord] using rd123.stop (by decide) (by evm_ov)

theorem simpleAuctionX_bid_successWithPending {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD simpleAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (bidTimestampWord I).toNat ≤ (bidAuctionEndWord σ I).toNat)
    (hbid : (bidHighestBidWord σ I).toNat < I.weiValue.toNat)
    (hnz : bidHighestBidWord σ I ≠ ⟨0⟩)
    (hfit :
      (bidPendingReturnsWord σ I).toNat + (bidHighestBidWord σ I).toNat < UInt256.size) :
    RDret simpleAuctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, bidFinalMapWithPending σ I) ByteArray.empty := by
  obtain ⟨_, _, rd468⟩ := simpleAuctionX_bid_afterPending (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hperm hreach htime hbid hnz hfit
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have rd472 := evm_run rd468 with [jumpdest, push1 ⟨2⟩, dup1]
  obtain ⟨_, _, rd473₀⟩ := rd472.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd473⟩ : ∃ k C, RD simpleAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨473⟩
      [bidHighestBidderRawWord (bidPendingMap σ I) I, ⟨2⟩, ⟨122⟩, simpleAuctionSelWord I]
      (bidPendingHashMem (bidHighestBidderWord σ I))
      (UInt256.ofNat 3) ByteArray.empty (cA, bidPendingMap σ I) k C := by
    exact ⟨_, _, by simpa [bidHighestBidderRawWord, initState] using rd473₀⟩
  have rd486₀ := evm_run rd473 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and, caller, swap1, dup2]
  have rd486 := rd486₀
  rw [hmask] at rd486
  have rd487 := RD.lor rd486 (by decide) (by evm_ov)
  have rd489 := evm_run rd487 with [swap1, swap2]
  obtain ⟨_, _, rd490⟩ := rd489.sstore hperm (by decide) (by evm_ov)
  have rd495 := evm_run rd490 with [callvalue, push1 ⟨3⟩, dup2, swap1]
  obtain ⟨_, _, rd496⟩ := rd495.sstore hperm (by decide) (by evm_ov)
  have rd499 := evm_run rd496 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (bidPendingHashMem_mload64 (bidHighestBidderWord σ I)) (by decide) (by evm_ov)]
  have rd502 := evm_run rd499 with [
    swap3, dup4,
    raw mstore 6 (bidPendingEventMemCaller σ I) (UInt256.ofNat 5) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd510 := evm_run rd502 with [
    push1 ⟨32⟩, dup4, add, swap2, swap1, swap2,
    raw mstore 3 (bidPendingEventMem σ I) (UInt256.ofNat 6) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd544 := rd510.pushConst bidHighestBidIncreasedTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd553 := evm_run rd544 with [
    swap2, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (bidPendingEventMem_mload64 σ I) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have hlen64 : ((⟨128⟩ : UInt256) + ⟨64⟩).sub ⟨128⟩ = ⟨64⟩ := by decide
  have rd553' := rd553
  rw [hlen64] at rd553'
  have rd554 := RD.log1 0 (UInt256.ofNat 6) rd553' (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by decide) (by evm_ov)
  have rd123 := evm_run rd554 with [jump (by jump_dest), jumpdest]
  simpa [bidFinalMapWithPending, bidWriteHighestBidMap, bidWriteHighestBidderMap,
    bidPackedSenderWord, bidSenderWord] using rd123.stop (by decide) (by evm_ov)

/-! ## `bid()` Solm-side source execution helpers -/

def bidAfterHighestBidderState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
    (simpleAuctionSetAddressWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) (bidSenderWord I))

def bidPostStateNoPending (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (bidAfterHighestBidderState evm I)
    (bidAfterHighestBidderState evm I).executionEnv.codeOwner ⟨3⟩ I.weiValue

def bidHighestBidWordState (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩

def bidHighestBidderRawState (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩

def bidHighestBidderWordState (evm : EVM.State) : UInt256 :=
  UInt256.land (bidHighestBidderRawState evm) solcAddrMask

def bidHighestBidderKeyState (evm : EVM.State) : KeyValue :=
  .address (AccountAddress.ofNat (bidHighestBidderWordState evm).toNat)

def bidPendingSlotState (evm : EVM.State) : UInt256 :=
  pendingReturnsSlot (bidHighestBidderKeyState evm)

def bidPendingReturnsWordState (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidPendingSlotState evm)

def bidAfterPendingState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (bidPendingSlotState evm)
    (bidPendingReturnsWordState evm + bidHighestBidWordState evm)

def bidPostStateWithPending (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  bidPostStateNoPending (bidAfterPendingState evm) I

theorem bidSenderWord_toNat (I : ExecutionEnv) :
    (bidSenderWord I).toNat = I.source.val := by
  unfold bidSenderWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem bidSender_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (bidSenderWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [bidSenderWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem bidPackedSenderWord_eq_setAddress (old : UInt256) (I : ExecutionEnv) :
    bidPackedSenderWord old I = simpleAuctionSetAddressWord old (bidSenderWord I) := by
  unfold bidPackedSenderWord simpleAuctionSetAddressWord
  rw [u256_land_comm (UInt256.lnot solcAddrMask) old]
  rw [solcAddrMask_clean (bidSenderWord_canonical I)]
  exact u256_lor_comm (bidSenderWord I) (UInt256.land old (UInt256.lnot solcAddrMask))

theorem evalExpr_bid_auctionEndTime (evm : EVM.State) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.storage auctionEndTimeRef) =
        .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)) := by
  have her : evalStorageRef simpleAuctionConfig
      { contract := simpleAuctionContract, locals := ∅ } evm auctionEndTimeRef =
      .ok { base := "auctionEndTime", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, auctionEndTimeRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? simpleAuctionContract.storage
      ({ base := "auctionEndTime", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := by simp) (her := her)
    (hty := hty) (hloc := simpleAuctionConfig_storage_auctionEndTime)]
  rw [simpleAuctionStorageLocLoad_uint256]

theorem evalExpr_bid_highestBid (evm : EVM.State) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.storage highestBidRef) =
        .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)) := by
  have her : evalStorageRef simpleAuctionConfig
      { contract := simpleAuctionContract, locals := ∅ } evm highestBidRef =
      .ok { base := "highestBid", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, highestBidRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? simpleAuctionContract.storage
      ({ base := "highestBid", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := by simp) (her := her)
    (hty := hty) (hloc := simpleAuctionConfig_storage_highestBid)]
  rw [simpleAuctionStorageLocLoad_uint256]

theorem evalExpr_bid_highestBidder (evm : EVM.State) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.storage highestBidderRef) =
        .ok (.address (AccountAddress.ofNat (bidHighestBidderWordState evm).toNat)) := by
  have her : evalStorageRef simpleAuctionConfig
      { contract := simpleAuctionContract, locals := ∅ } evm highestBidderRef =
      .ok { base := "highestBidder", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, highestBidderRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? simpleAuctionContract.storage
      ({ base := "highestBidder", steps := [] } : EvaledStorageRef) =
      some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address) (hbase := by simp) (her := her)
    (hty := hty) (hloc := simpleAuctionConfig_storage_highestBidder)]
  rw [simpleAuctionStorageLocLoad_address_offset0]
  rfl

theorem evalStorageRef_bid_pending_current (evm : EVM.State) :
    evalStorageRef simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (pendingReturnsRef (.storage highestBidderRef)) =
        .ok { base := "pendingReturns", steps := [.mindex (bidHighestBidderKeyState evm)] } := by
  simp [evalStorageRef, evalStorageRefStep, pendingReturnsRef, evalExpr_bid_highestBidder,
    bidHighestBidderKeyState, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalExpr_bid_pendingReturns_current (evm : EVM.State) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.storage (pendingReturnsRef (.storage highestBidderRef))) =
        .ok (.int (Int.ofNat (bidPendingReturnsWordState evm).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := by simp [pendingReturnsRef])
    (her := evalStorageRef_bid_pending_current evm)
    (hty := by simp [storageTypeAt?, simpleAuctionContract, storageDecls, uint256St,
      storageTypeStep?])
    (hloc := simpleAuctionConfig_storage_pendingReturns (bidHighestBidderKeyState evm))]
  rw [simpleAuctionStorageLocLoad_uint256]
  rfl

theorem evalExpr_bid_sender (evm : EVM.State) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      sender = .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_bid_callvalue_I (evm : EVM.State) (I : ExecutionEnv)
    (hEnv : evm.executionEnv = I) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.env .callvalue) = .ok (.int (Int.ofNat I.weiValue.toNat)) := by
  subst I
  simp [evalExpr?, envValue, UInt256.toNat, pure]

theorem evalExpr_bid_time_true (evm : EVM.State)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.binary .le now (.storage auctionEndTimeRef)) = .ok (.bool true) := by
  simp only [evalExpr?, now, envValue, evalExpr_bid_auctionEndTime, bind, EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_bid_time_false (evm : EVM.State)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.binary .le now (.storage auctionEndTimeRef)) = .ok (.bool false) := by
  simp only [evalExpr?, now, envValue, evalExpr_bid_auctionEndTime, bind, EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_bid_value_gt_true (evm : EVM.State)
    (hbid :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat <
        evm.executionEnv.weiValue.toNat) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.binary .gt (.env .callvalue) (.storage highestBidRef)) = .ok (.bool true) := by
  have hgt : Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat <
      Int.ofNat evm.executionEnv.weiValue.toNat :=
    Int.ofNat_lt.mpr hbid
  simp only [evalExpr?, envValue, evalExpr_bid_highestBid, bind, EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using hbid

theorem evalExpr_bid_value_gt_false (evm : EVM.State)
    (hbid :
      evm.executionEnv.weiValue.toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.binary .gt (.env .callvalue) (.storage highestBidRef)) = .ok (.bool false) := by
  simp only [evalExpr?, envValue, evalExpr_bid_highestBid, bind, EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using hbid

theorem evalExpr_bid_highestBid_ne_true (evm : EVM.State)
    (hnz : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩ ≠ ⟨0⟩) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.binary .ne (.storage highestBidRef) (.intLit 0)) = .ok (.bool true) := by
  rw [evalExpr?]
  simp only [evalExpr_bid_highestBid, evalExpr?, bind, EvalResult.bind, pure]
  have hnat : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat ≠ 0 := by
    intro h
    apply hnz
    apply u256_inj
    simpa [UInt256.toNat] using h
  simp [evalBinaryOp?, hnat]

theorem evalExpr_bid_highestBid_ne_false (evm : EVM.State)
    (hzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩ = ⟨0⟩) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (.binary .ne (.storage highestBidRef) (.intLit 0)) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [evalExpr_bid_highestBid, evalExpr?, bind, EvalResult.bind, pure]
  rw [hzero]
  rfl

theorem bidPendingSum_toNat (evm : EVM.State)
    (hfit :
      (bidPendingReturnsWordState evm).toNat + (bidHighestBidWordState evm).toNat < UInt256.size) :
    (bidPendingReturnsWordState evm + bidHighestBidWordState evm).toNat =
      (bidPendingReturnsWordState evm).toNat + (bidHighestBidWordState evm).toNat := by
  rw [uadd_toNat, Nat.mod_eq_of_lt hfit]

theorem evalExpr_bid_pending_add_ok (evm : EVM.State)
    (hfit :
      (bidPendingReturnsWordState evm).toNat + (bidHighestBidWordState evm).toNat < UInt256.size) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (u256 (.binary .add
        (.storage (pendingReturnsRef (.storage highestBidderRef)))
        (.storage highestBidRef))) =
        .ok (.int
          (Int.ofNat (bidPendingReturnsWordState evm + bidHighestBidWordState evm).toNat)) := by
  have hsumWord := bidPendingSum_toNat evm hfit
  have hsumWordRaw :
      (bidPendingReturnsWordState evm +
          Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat =
        (bidPendingReturnsWordState evm).toNat +
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat := by
    simpa [bidHighestBidWordState] using hsumWord
  have hfitNatRaw :
      (bidPendingReturnsWordState evm).toNat +
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat < 2 ^ 256 := by
    simpa [UInt256.size, bidHighestBidWordState] using hfit
  simp only [u256, evalExpr?, evalExpr_bid_pendingReturns_current, evalExpr_bid_highestBid,
    EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [if_neg]
  · simp only [bidHighestBidWordState]
    have hInt :
        Int.ofNat (bidPendingReturnsWordState evm).toNat +
            Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat =
          Int.ofNat ((bidPendingReturnsWordState evm).toNat +
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat) := by
      norm_num
    rw [hInt, ← hsumWordRaw]
  · simp
    omega

theorem evalExpr_bid_pending_add_revert (evm : EVM.State)
    (hover :
      UInt256.size ≤
        (bidPendingReturnsWordState evm).toNat + (bidHighestBidWordState evm).toNat) :
    evalExpr? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      (u256 (.binary .add
        (.storage (pendingReturnsRef (.storage highestBidderRef)))
        (.storage highestBidRef))) = .revert := by
  have hge :
      Int.ofNat ((bidPendingReturnsWordState evm).toNat +
          (bidHighestBidWordState evm).toNat) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [u256, evalExpr?, evalExpr_bid_pendingReturns_current, evalExpr_bid_highestBid,
    EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, uint256Int]
  intro _
  simpa using hge

theorem bidAssignPending (evm : EVM.State) :
    assignStorageRef? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      .storage (pendingReturnsRef (.storage highestBidderRef))
      (.int (Int.ofNat (bidPendingReturnsWordState evm + bidHighestBidWordState evm).toNat)) =
        .ok ({ contract := simpleAuctionContract, locals := ∅ }, bidAfterPendingState evm) := by
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by simp [pendingReturnsRef])
      (her := evalStorageRef_bid_pending_current evm)
      (hty := by simp [storageTypeAt?, simpleAuctionContract, storageDecls, uint256St,
        storageTypeStep?])
      (hloc := simpleAuctionConfig_storage_pendingReturns (bidHighestBidderKeyState evm))
  rw [bidStorageLocStore_uint256]
  simp [bidAfterPendingState, bidPendingSlotState]

theorem bidAssignHighestBidder (evm : EVM.State) (I : ExecutionEnv)
    (hEnv : evm.executionEnv = I) :
    assignStorageRef? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ } evm
      .storage highestBidderRef (.address evm.executionEnv.source) =
        .ok ({ contract := simpleAuctionContract, locals := ∅ },
          bidAfterHighestBidderState evm I) := by
  apply assignStorageRef_storage_scalar_value (ty := addrSt)
      (hbase := by simp)
      (her := by
        simp [evalStorageRef, evalStorageRefSteps, highestBidderRef, EvalResult.bind, pure, bind])
      (hty := by decide)
      (hloc := simpleAuctionConfig_storage_highestBidder)
      (hscalar := by trivial)
  have hsource : evm.executionEnv.source = AccountAddress.ofNat (bidSenderWord I).toNat := by
    rw [hEnv, bidSender_ofNat]
  rw [hsource]
  rw [simpleAuctionStorageLocStore_address_offset0 evm ⟨2⟩ (bidSenderWord I)
    (bidSenderWord_canonical I)]
  rfl

theorem bidAssignHighestBid (evm : EVM.State) (I : ExecutionEnv)
    (_hEnv : evm.executionEnv = I) :
    assignStorageRef? simpleAuctionConfig { contract := simpleAuctionContract, locals := ∅ }
      (bidAfterHighestBidderState evm I) .storage highestBidRef
      (.int (Int.ofNat I.weiValue.toNat)) =
        .ok ({ contract := simpleAuctionContract, locals := ∅ },
          bidPostStateNoPending evm I) := by
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by simp)
      (her := by
        simp [evalStorageRef, evalStorageRefSteps, highestBidRef, EvalResult.bind, pure, bind])
      (hty := by decide)
      (hloc := simpleAuctionConfig_storage_highestBid)
  rw [bidStorageLocStore_uint256]
  simp [bidPostStateNoPending]

theorem simpleAuctionBidBodyReverts_time (evm : EVM.State)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm ∅ bidTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold bidTransition
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_bid_time_false evm htime))

theorem simpleAuctionBidBodyReverts_bid (evm : EVM.State)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)
    (hbid :
      evm.executionEnv.weiValue.toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm ∅ bidTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold bidTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_bid_time_true evm htime)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_bid_value_gt_false evm hbid))

theorem simpleAuctionBidBodyReturnsNoPending (evm : EVM.State) (I : ExecutionEnv)
    (hEnv : evm.executionEnv = I)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)
    (hbid :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat <
        evm.executionEnv.weiValue.toNat)
    (hzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩ = ⟨0⟩) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm ∅ bidTransition.body
      (.returned { contract := simpleAuctionContract, locals := ∅ }
        (bidPostStateNoPending evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  unfold bidTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_bid_time_true evm htime)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_bid_value_gt_true evm hbid)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (evalExpr_bid_highestBid_ne_false evm hzero) ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_bid_sender evm) (bidAssignHighestBidder evm I hEnv)) ?_
  have hAfterEnv : (bidAfterHighestBidderState evm I).executionEnv = I := by
    simp [bidAfterHighestBidderState, storageStore_executionEnv, hEnv]
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_bid_callvalue_I (bidAfterHighestBidderState evm I) I hAfterEnv)
      (bidAssignHighestBid evm I hEnv)) ?_
  exact ExecBlock.nil

theorem simpleAuctionBidBodyReverts_pendingOverflow (evm : EVM.State)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)
    (hbid :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat <
        evm.executionEnv.weiValue.toNat)
    (hnz : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩ ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤
        (bidPendingReturnsWordState evm).toNat + (bidHighestBidWordState evm).toNat) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm ∅ bidTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold bidTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_bid_time_true evm htime)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_bid_value_gt_true evm hbid)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue (evalExpr_bid_highestBid_ne_true evm hnz)
      (ExecBlock.consRevert
        (ExecStmt.assignExprRevert (evalExpr_bid_pending_add_revert evm hover))))

theorem simpleAuctionBidBodyReturnsWithPending (evm : EVM.State) (I : ExecutionEnv)
    (hEnv : evm.executionEnv = I)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)
    (hbid :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat <
        evm.executionEnv.weiValue.toNat)
    (hnz : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩ ≠ ⟨0⟩)
    (hfit :
      (bidPendingReturnsWordState evm).toNat + (bidHighestBidWordState evm).toNat < UInt256.size) :
    ExecTransitionBody simpleAuctionConfig simpleAuctionContract evm ∅ bidTransition.body
      (.returned { contract := simpleAuctionContract, locals := ∅ }
        (bidPostStateWithPending evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  unfold bidTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_bid_time_true evm htime)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_bid_value_gt_true evm hbid)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue (evalExpr_bid_highestBid_ne_true evm hnz)
      (ExecBlock.consNormal
        (ExecStmt.assign (evalExpr_bid_pending_add_ok evm hfit) (bidAssignPending evm))
        ExecBlock.nil)) ?_
  have hPendingEnv : (bidAfterPendingState evm).executionEnv = I := by
    simp [bidAfterPendingState, storageStore_executionEnv, hEnv]
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_bid_sender (bidAfterPendingState evm))
      (bidAssignHighestBidder (bidAfterPendingState evm) I hPendingEnv)) ?_
  have hAfterEnv : (bidAfterHighestBidderState (bidAfterPendingState evm) I).executionEnv = I := by
    simp [bidAfterHighestBidderState, storageStore_executionEnv, hPendingEnv]
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_bid_callvalue_I (bidAfterHighestBidderState (bidAfterPendingState evm) I) I
        hAfterEnv)
      (bidAssignHighestBid (bidAfterPendingState evm) I hPendingEnv)) ?_
  exact ExecBlock.nil

theorem simpleAuctionBidBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = simpleAuctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x19, 0x98, 0xae, 0xef]⟩)
    (hreach : ∃ k C, RD simpleAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨114⟩
      [simpleAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor simpleAuctionConfig simpleAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x19, 0x98, 0xae, 0xef]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hsz := simpleAuctionBidSelector_size hsel'
  have hd := simpleAuctionDispatch_bid (cd := I.calldata) hsel'
  have hdec := simpleAuctionDecode_bid (I := I) hsz
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
  have hAuctionEnd : bidAuctionEndWord σ_evm I = bidAuctionEndWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hHighestBid : bidHighestBidWord σ_evm I = bidHighestBidWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  have hHighestBidderRaw :
      bidHighestBidderRawWord σ_evm I = bidHighestBidderRawWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  by_cases htimeBad : (bidAuctionEndWord σ_evm I).toNat < (bidTimestampWord I).toNat
  · have htimeS' : (bidAuctionEndWord σ_solm I).toNat < (bidTimestampWord I).toNat := by
      simpa [hAuctionEnd] using htimeBad
    have hbody :
        ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
          bidTransition.body .reverted :=
      simpleAuctionBidBodyReverts_time evmS (by
        simpa [evmS, initState, bidAuctionEndWord, bidTimestampWord, Solm.EVM.storageLoad,
          State.lookupAccount] using htimeS')
    exact (simpleAuctionX_bid_timeRevert (g := Sat256.ofUInt256 g) hreach htimeBad)
      |>.reEquivExecutionRevert hcode hd hdec hbody
  · have htimeLe : (bidTimestampWord I).toNat ≤ (bidAuctionEndWord σ_evm I).toNat := by
      omega
    have htimeS' : (bidTimestampWord I).toNat ≤ (bidAuctionEndWord σ_solm I).toNat := by
      simpa [hAuctionEnd] using htimeLe
    by_cases hbidBad : I.weiValue.toNat ≤ (bidHighestBidWord σ_evm I).toNat
    · have hbidS' : I.weiValue.toNat ≤ (bidHighestBidWord σ_solm I).toNat := by
        simpa [hHighestBid] using hbidBad
      have hbody :
          ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
            bidTransition.body .reverted :=
        simpleAuctionBidBodyReverts_bid evmS
          (by
            simpa [evmS, initState, bidAuctionEndWord, bidTimestampWord, Solm.EVM.storageLoad,
              State.lookupAccount] using htimeS')
          (by
            simpa [evmS, initState, bidHighestBidWord, Solm.EVM.storageLoad, State.lookupAccount]
              using hbidS')
      exact (simpleAuctionX_bid_bidRevert (g := Sat256.ofUInt256 g) hreach htimeLe hbidBad)
        |>.reEquivExecutionRevert hcode hd hdec hbody
    · have hbidLt : (bidHighestBidWord σ_evm I).toNat < I.weiValue.toNat := by
        omega
      by_cases hzero : bidHighestBidWord σ_evm I = ⟨0⟩
      · have hbidS' : (bidHighestBidWord σ_solm I).toNat < I.weiValue.toNat := by
          simpa [hHighestBid] using hbidLt
        have hzeroS' : bidHighestBidWord σ_solm I = ⟨0⟩ := by
          simpa [hHighestBid] using hzero
        have hbody :
            ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
              bidTransition.body
              (.returned { contract := simpleAuctionContract, locals := ∅ }
                (bidPostStateNoPending evmS I) none) :=
          simpleAuctionBidBodyReturnsNoPending evmS I (by simp [evmS, initState])
            (by
              simpa [evmS, initState, bidAuctionEndWord, bidTimestampWord,
                Solm.EVM.storageLoad, State.lookupAccount] using htimeS')
            (by
              simpa [evmS, initState, bidHighestBidWord, Solm.EVM.storageLoad,
                State.lookupAccount] using hbidS')
            (by
              simpa [evmS, initState, bidHighestBidWord, Solm.EVM.storageLoad,
                State.lookupAccount] using hzeroS')
        have hσAfter : EVMStateEquiv (bidAfterHighestBidderState evmE I)
            (bidAfterHighestBidderState evmS I) := by
          unfold bidAfterHighestBidderState
          rw [hσ.executionEnv]
          have hval :
              simpleAuctionSetAddressWord
                  (Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner ⟨2⟩)
                  (bidSenderWord I) =
                simpleAuctionSetAddressWord
                  (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨2⟩)
                  (bidSenderWord I) := by
            rw [hσ.storageLoad_codeOwner ⟨2⟩]
          exact hσ.storageStore_codeOwner ⟨2⟩ hval
        have hσPost : EVMStateEquiv (bidPostStateNoPending evmE I)
            (bidPostStateNoPending evmS I) := by
          unfold bidPostStateNoPending
          exact hσAfter.storageStore_codeOwner ⟨3⟩ rfl
        exact (simpleAuctionX_bid_successNoPending (g := Sat256.ofUInt256 g) hperm hreach
            htimeLe hbidLt hzero)
          |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
            (by
              simp [evmE, bidPostStateNoPending, bidAfterHighestBidderState, initState,
                simpleAuctionStorageStore_createdAccounts])
            (accountMapEquiv.of_eq (by
              simp [evmE, bidPostStateNoPending, bidAfterHighestBidderState, initState,
                bidFinalMapNoPending, bidWriteHighestBidMap, bidWriteHighestBidderMap,
                bidHighestBidderRawWord, bidPackedSenderWord_eq_setAddress,
                Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                storageStore_executionEnv,
                simpleAuctionStorageStore_accountMap]))
            hσPost
            (returnEquiv.void rfl rfl rfl)
      · have hnzE : bidHighestBidWord σ_evm I ≠ ⟨0⟩ := hzero
        have hbidS' : (bidHighestBidWord σ_solm I).toNat < I.weiValue.toNat := by
          simpa [hHighestBid] using hbidLt
        have hnzS' : bidHighestBidWord σ_solm I ≠ ⟨0⟩ := by
          intro hz
          apply hnzE
          simpa [hHighestBid] using hz
        have hPendingSlot : bidPendingSlot σ_evm I = bidPendingSlot σ_solm I := by
          simp [bidPendingSlot, bidHighestBidderKey, bidHighestBidderWord, hHighestBidderRaw]
        have hPendingReturns :
            bidPendingReturnsWord σ_evm I = bidPendingReturnsWord σ_solm I := by
          unfold bidPendingReturnsWord
          rw [← hPendingSlot]
          exact accountMapEquiv_storage_findD hAccounts I.codeOwner
            (bidPendingSlot σ_evm I) ⟨0⟩
        have hPendingSlotState : bidPendingSlotState evmE = bidPendingSlotState evmS := by
          simpa [evmE, evmS, initState, bidPendingSlotState, bidHighestBidderKeyState,
            bidHighestBidderWordState, bidHighestBidderRawState, bidPendingSlot,
            bidHighestBidderKey, bidHighestBidderWord, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage] using hPendingSlot
        have hPendingReturnsState :
            bidPendingReturnsWordState evmE = bidPendingReturnsWordState evmS := by
          unfold bidPendingReturnsWordState
          rw [hPendingSlotState]
          exact hσ.storageLoad_codeOwner (bidPendingSlotState evmS)
        have hHighestBidState :
            bidHighestBidWordState evmE = bidHighestBidWordState evmS := by
          unfold bidHighestBidWordState
          exact hσ.storageLoad_codeOwner ⟨3⟩
        by_cases hfit :
            (bidPendingReturnsWord σ_evm I).toNat +
              (bidHighestBidWord σ_evm I).toNat < UInt256.size
        · have hfitS' :
              (bidPendingReturnsWord σ_solm I).toNat +
                (bidHighestBidWord σ_solm I).toNat < UInt256.size := by
            simpa [← hPendingReturns, ← hHighestBid] using hfit
          have hfitSState :
              (bidPendingReturnsWordState evmS).toNat +
                (bidHighestBidWordState evmS).toNat < UInt256.size := by
            simpa [evmS, initState, bidPendingReturnsWordState, bidHighestBidWordState,
              bidPendingReturnsWord, bidHighestBidWord, Solm.EVM.storageLoad,
              State.lookupAccount] using hfitS'
          have hbody :
              ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
                bidTransition.body
                (.returned { contract := simpleAuctionContract, locals := ∅ }
                  (bidPostStateWithPending evmS I) none) :=
            simpleAuctionBidBodyReturnsWithPending evmS I (by simp [evmS, initState])
              (by
                simpa [evmS, initState, bidAuctionEndWord, bidTimestampWord,
                  Solm.EVM.storageLoad, State.lookupAccount] using htimeS')
              (by
                simpa [evmS, initState, bidHighestBidWord, Solm.EVM.storageLoad,
                  State.lookupAccount] using hbidS')
              (by
                simpa [evmS, initState, bidHighestBidWord, Solm.EVM.storageLoad,
                  State.lookupAccount] using hnzS')
              hfitSState
          have hσPending : EVMStateEquiv (bidAfterPendingState evmE)
              (bidAfterPendingState evmS) := by
            unfold bidAfterPendingState
            rw [hσ.executionEnv, hPendingSlotState]
            exact hσ.storageStore_codeOwner (bidPendingSlotState evmS)
              (by rw [hPendingReturnsState, hHighestBidState])
          have hσAfter : EVMStateEquiv
              (bidAfterHighestBidderState (bidAfterPendingState evmE) I)
              (bidAfterHighestBidderState (bidAfterPendingState evmS) I) := by
            unfold bidAfterHighestBidderState
            have hval :
                simpleAuctionSetAddressWord
                    (Solm.EVM.storageLoad (bidAfterPendingState evmE)
                      (bidAfterPendingState evmE).executionEnv.codeOwner ⟨2⟩)
                    (bidSenderWord I) =
                  simpleAuctionSetAddressWord
                    (Solm.EVM.storageLoad (bidAfterPendingState evmS)
                      (bidAfterPendingState evmS).executionEnv.codeOwner ⟨2⟩)
                    (bidSenderWord I) := by
              rw [hσPending.storageLoad_codeOwner ⟨2⟩]
            exact hσPending.storageStore_codeOwner ⟨2⟩ hval
          have hσPost : EVMStateEquiv (bidPostStateWithPending evmE I)
              (bidPostStateWithPending evmS I) := by
            unfold bidPostStateWithPending bidPostStateNoPending
            exact hσAfter.storageStore_codeOwner ⟨3⟩ rfl
          exact (simpleAuctionX_bid_successWithPending (g := Sat256.ofUInt256 g) hperm hreach
              htimeLe hbidLt hnzE hfit)
            |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
              (by
                simp [evmE, bidPostStateWithPending, bidPostStateNoPending,
                  bidAfterHighestBidderState, bidAfterPendingState, initState,
                  simpleAuctionStorageStore_createdAccounts])
              (accountMapEquiv.of_eq (by
                simp [evmE, bidPostStateWithPending, bidPostStateNoPending,
                  bidAfterHighestBidderState, bidAfterPendingState, initState,
                  bidFinalMapWithPending, bidWriteHighestBidMap, bidWriteHighestBidderMap,
                  bidPendingMap, bidHighestBidderRawWord, bidPendingReturnsWord,
                  bidPendingSlot, bidHighestBidderKey, bidHighestBidderWord, bidHighestBidWord,
                  bidPendingReturnsWordState, bidPendingSlotState, bidHighestBidWordState,
                  bidHighestBidderKeyState, bidHighestBidderWordState,
                  bidHighestBidderRawState, bidPackedSenderWord_eq_setAddress,
                  Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                  storageStore_executionEnv, simpleAuctionStorageStore_accountMap]))
              hσPost
              (returnEquiv.void rfl rfl rfl)
        · have hoverE : UInt256.size ≤
              (bidPendingReturnsWord σ_evm I).toNat +
                (bidHighestBidWord σ_evm I).toNat := by
            omega
          have hoverS' : UInt256.size ≤
              (bidPendingReturnsWord σ_solm I).toNat +
                (bidHighestBidWord σ_solm I).toNat := by
            simpa [← hPendingReturns, ← hHighestBid] using hoverE
          have hoverSState :
              UInt256.size ≤
                (bidPendingReturnsWordState evmS).toNat +
                  (bidHighestBidWordState evmS).toNat := by
            simpa [evmS, initState, bidPendingReturnsWordState, bidHighestBidWordState,
              bidPendingReturnsWord, bidHighestBidWord, Solm.EVM.storageLoad,
              State.lookupAccount] using hoverS'
          have hbody :
              ExecTransitionBody simpleAuctionConfig simpleAuctionContract evmS ∅
                bidTransition.body .reverted :=
            simpleAuctionBidBodyReverts_pendingOverflow evmS
              (by
                simpa [evmS, initState, bidAuctionEndWord, bidTimestampWord,
                  Solm.EVM.storageLoad, State.lookupAccount] using htimeS')
              (by
                simpa [evmS, initState, bidHighestBidWord, Solm.EVM.storageLoad,
                  State.lookupAccount] using hbidS')
              (by
                simpa [evmS, initState, bidHighestBidWord, Solm.EVM.storageLoad,
                  State.lookupAccount] using hnzS')
              hoverSState
          exact (simpleAuctionX_bid_pendingOverflow (g := Sat256.ofUInt256 g) hreach
              htimeLe hbidLt hnzE hoverE)
            |>.reEquivExecutionRevert hcode hd hdec hbody

end SimpleAuction
