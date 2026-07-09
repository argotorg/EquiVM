import Examples.BlindAuction.Storage
import Examples.BlindAuction.Bids
import Examples.BlindAuction.BiddingEnd
import Reasoning.ABI
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace BlindAuction

/-! ## `bid(bytes32)` calldata, storage, and trace facts -/

abbrev bidBlindedWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4

abbrev bidBlindedBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev bidBlindedValue (I : ExecutionEnv) : Value :=
  .fixedBytes ⟨31, by decide⟩ (bidBlindedBytes I)

abbrev bidStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "blindedBid" (bidBlindedValue I)

abbrev bidSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

def bidSenderKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

def bidLengthSlot (I : ExecutionEnv) : UInt256 :=
  bidsBase (bidSenderKey I)

def bidElementSlot (I : ExecutionEnv) (len : UInt256) : UInt256 :=
  bidsElemSlot (bidSenderKey I) (.int (Int.ofNat len.toNat))

def bidDepositSlot (I : ExecutionEnv) (len : UInt256) : UInt256 :=
  bidElementSlot I len + ⟨1⟩

def bidLengthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (bidLengthSlot I) ⟨0⟩)

noncomputable def bidBaseSlotMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 solcFreePtrMem 32 32

noncomputable def bidHashMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (bidSourceWord I)).write 0 (bidBaseSlotMem I) 0 32

noncomputable def bidElemBaseMem (I : ExecutionEnv) (lenSlot : UInt256) : ByteArray :=
  (UInt256.toByteArray lenSlot).write 0 (bidHashMem I) 0 32

noncomputable def bidSourceMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (bidSourceWord I)).write 0 solcFreePtrMem 0 32

noncomputable def bidHashMemExec (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 (bidSourceMem I) 32 32

noncomputable def bidAllocMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨192⟩ : UInt256)).write 0 (bidHashMemExec I) 64 32

noncomputable def bidBlindedMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (bidBlindedWord I)).write 0 (bidAllocMem I) 128 32

noncomputable def bidStructMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray I.weiValue).write 0 (bidBlindedMem I) 160 32

noncomputable def bidElemBaseMemExec (I : ExecutionEnv) (lenSlot : UInt256) : ByteArray :=
  (UInt256.toByteArray lenSlot).write 0 (bidStructMem I) 0 32

def bidTooLateSelector : UInt256 :=
  UInt256.shiftLeft (⟨0x348f2b41⟩ : UInt256) ⟨225⟩

noncomputable def bidTooLateMem (deadline : UInt256) : ByteArray :=
  (UInt256.toByteArray deadline).write 0 (solcReturnMem bidTooLateSelector) 132 32

abbrev bidCallValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat I.weiValue.toNat)

abbrev bidTimestampWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

abbrev bidStructValue (I : ExecutionEnv) : Value :=
  .struct "Bid" [("blindedBid", bidBlindedValue I), ("deposit", bidCallValue I)]

def bidAfterLengthState (evm : EVM.State) (I : ExecutionEnv) (len : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (bidLengthSlot I) (len + ⟨1⟩)

def bidAfterBlindedState (evm : EVM.State) (I : ExecutionEnv) (len : UInt256) : EVM.State :=
  Solm.EVM.storageStore (bidAfterLengthState evm I len)
    (bidAfterLengthState evm I len).executionEnv.codeOwner (bidElementSlot I len)
    (bidBlindedWord I)

def bidPostState (evm : EVM.State) (I : ExecutionEnv) (len : UInt256) : EVM.State :=
  Solm.EVM.storageStore (bidAfterBlindedState evm I len)
    (bidAfterBlindedState evm I len).executionEnv.codeOwner (bidDepositSlot I len) I.weiValue

theorem bidLengthSlot_spec (I : ExecutionEnv) :
    bidLengthSlot I = blindAuctionMappingSlot (bidSourceWord I) ⟨4⟩ := by
  unfold bidLengthSlot bidsBase blindAuctionMappingSlot bidSenderKey
  rw [show keyValueToWord (.address I.source) = bidSourceWord I by
    simpa [bidSourceWord] using keyValueToWord_address I.source]

theorem bidElementSlot_spec (I : ExecutionEnv) (len : UInt256) :
    bidElementSlot I len =
      uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (bidLengthSlot I))) +
        UInt256.mul len ⟨2⟩ := by
  unfold bidElementSlot bidsElemSlot
  rw [keyValueToWord_uint256]
  rw [show UInt256.ofNat (len.toNat * 2) = UInt256.mul len ⟨2⟩ from by
    apply u256_inj
    show (Fin.ofNat UInt256.size (len.toNat * 2)).val =
      ((len.val * (⟨2⟩ : UInt256).val) : Fin UInt256.size).val
    rw [Fin.val_mul]
    rfl]
  rw [show bidsBase (bidSenderKey I) = bidLengthSlot I from rfl]

theorem bidBaseSlotMem_size (I : ExecutionEnv) : (bidBaseSlotMem I).size = 96 := by
  unfold bidBaseSlotMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  norm_num

theorem bidHashMem_size (I : ExecutionEnv) : (bidHashMem I).size = 96 := by
  unfold bidHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [bidBaseSlotMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, bidBaseSlotMem_size, toByteArray_size]
  norm_num

theorem bidElemBaseMem_size (I : ExecutionEnv) (lenSlot : UInt256) :
    (bidElemBaseMem I lenSlot).size = 96 := by
  unfold bidElemBaseMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [bidHashMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, bidHashMem_size, toByteArray_size]
  norm_num

theorem bidBaseSlotMem_read32 (I : ExecutionEnv) :
    (bidBaseSlotMem I).readWithPadding 32 32 = UInt256.toByteArray (⟨4⟩ : UInt256) := by
  unfold bidBaseSlotMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [solcFreePtrMem_size]; omega)]
  rw [show (UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨4⟩ : UInt256) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
        show (UInt256.toByteArray (⟨4⟩ : UInt256)).data.size ≤ 32
        rw [show (UInt256.toByteArray (⟨4⟩ : UInt256)).data.size =
          (UInt256.toByteArray (⟨4⟩ : UInt256)).size from rfl, toByteArray_size]]

theorem bidBaseSlotMem_read64 (I : ExecutionEnv) :
    (bidBaseSlotMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold bidBaseSlotMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [solcFreePtrMem_size]; omega)
    (by omega)
    (by rw [solcFreePtrMem_size])]
  exact solcFreePtrMem_read64

set_option maxHeartbeats 2000000 in
theorem bidHashMem_read0_64 (I : ExecutionEnv) :
    (bidHashMem I).readWithPadding 0 64 =
      UInt256.toByteArray (bidSourceWord I) ++ UInt256.toByteArray (⟨4⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' (bidHashMem I) 0 64
    (by norm_num) (by norm_num) (by rw [bidHashMem_size]; omega)]
  unfold bidHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [bidBaseSlotMem_size]; omega)]
  have hempty : (bidBaseSlotMem I).extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    simp
  rw [hempty, empty_append]
  have hfirst :
      ((UInt256.toByteArray (bidSourceWord I) ++ (bidBaseSlotMem I).extract 32
          (bidBaseSlotMem I).size).extract 0 64) =
        UInt256.toByteArray (bidSourceWord I) ++
          ((bidBaseSlotMem I).extract 32 (bidBaseSlotMem I).size).extract 0 32 := by
    rw [extract_append_span (UInt256.toByteArray (bidSourceWord I))
      ((bidBaseSlotMem I).extract 32 (bidBaseSlotMem I).size) 0 64
      (by omega) (by rw [toByteArray_size]; omega)]
    rw [show (UInt256.toByteArray (bidSourceWord I)).extract 0
        (UInt256.toByteArray (bidSourceWord I)).size =
        UInt256.toByteArray (bidSourceWord I) from by
          apply ByteArray.ext
          rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
          rfl]
    rw [toByteArray_size]
  rw [show (UInt256.toByteArray (bidSourceWord I)).extract 0 32 =
      UInt256.toByteArray (bidSourceWord I) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
        show (UInt256.toByteArray (bidSourceWord I)).data.size ≤ 32
        rw [show (UInt256.toByteArray (bidSourceWord I)).data.size =
          (UInt256.toByteArray (bidSourceWord I)).size from rfl, toByteArray_size]]
  simp only [Nat.zero_add]
  rw [hfirst]
  have htail :
      ((bidBaseSlotMem I).extract 32 (bidBaseSlotMem I).size).extract 0 32 =
        UInt256.toByteArray (⟨4⟩ : UInt256) := by
    rw [extract_extract_BA]
    rw [show 32 + 0 = 32 by norm_num]
    rw [show min (32 + 32) (bidBaseSlotMem I).size = 64 by
      rw [bidBaseSlotMem_size]; norm_num]
    rw [← readWithPadding_eq_extract (bidBaseSlotMem I) 32
      (by rw [bidBaseSlotMem_size]; omega)]
    exact bidBaseSlotMem_read32 I
  rw [htail]

theorem bidElemBaseMem_read0 (I : ExecutionEnv) (lenSlot : UInt256) :
    (bidElemBaseMem I lenSlot).readWithPadding 0 32 = UInt256.toByteArray lenSlot := by
  unfold bidElemBaseMem
  rw [write0_read_back_gen _ _ 32 (by decide) (by rw [toByteArray_size]) (by norm_num)]
  apply ByteArray.ext
  rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
  show (UInt256.toByteArray lenSlot).data.size ≤ 32
  rw [show (UInt256.toByteArray lenSlot).data.size =
    (UInt256.toByteArray lenSlot).size from rfl, toByteArray_size]

theorem bid_toByteArray_write_read_back_of_gap (b : UInt256) (mem : ByteArray) (off : ℕ)
    (hgap : off - mem.size < USize.size) :
    ((UInt256.toByteArray b).write 0 mem off 32).readWithPadding off 32 =
      UInt256.toByteArray b := by
  by_cases hle : off ≤ mem.size
  · rw [write32_read_back _ _ off (by rw [toByteArray_size]) hle]
    rw [show 32 = (UInt256.toByteArray b).size by rw [toByteArray_size]]
    exact byteArray_extract_self _
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq _ _ off hge hgap]
    rw [readWithPadding_eq_extract _ off (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
      omega)]
    rw [extract_append_right_window
      (mem ++ ffi.ByteArray.zeroes (off - mem.size))
      (UInt256.toByteArray b) off (off + 32) (by
        rw [ByteArray.size_append, ByteArray_zeroes_size]
        omega)]
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    rw [show off - (mem.size + (off - mem.size)) = 0 by omega,
      show off + 32 - (mem.size + (off - mem.size)) = 32 by omega]
    rw [show (UInt256.toByteArray b).extract 0 32 = UInt256.toByteArray b from by
      rw [show 32 = (UInt256.toByteArray b).size by rw [toByteArray_size]]
      exact byteArray_extract_self _]

theorem bidSourceMem_size (I : ExecutionEnv) : (bidSourceMem I).size = 96 := by
  unfold bidSourceMem
  rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  norm_num

theorem bidHashMemExec_size (I : ExecutionEnv) : (bidHashMemExec I).size = 96 := by
  unfold bidHashMemExec
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [bidSourceMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, bidSourceMem_size, toByteArray_size]
  norm_num

theorem bidAllocMem_size (I : ExecutionEnv) : (bidAllocMem I).size = 96 := by
  unfold bidAllocMem
  rw [write32_eq _ _ 64 (by rw [toByteArray_size]) (by rw [bidHashMemExec_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, bidHashMemExec_size, toByteArray_size]
  norm_num

theorem bidBlindedMem_size (I : ExecutionEnv) : (bidBlindedMem I).size = 160 := by
  unfold bidBlindedMem
  rw [toByteArray_write_eq _ _ 128 (by rw [bidAllocMem_size]; omega)
      (by rw [bidAllocMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, bidAllocMem_size, ByteArray_zeroes_size,
    show 128 - 96 = 32 from by norm_num,
    toByteArray_size]

theorem bidStructMem_size (I : ExecutionEnv) : (bidStructMem I).size = 192 := by
  unfold bidStructMem
  rw [write32_eq _ _ 160 (by rw [toByteArray_size]) (by rw [bidBlindedMem_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, bidBlindedMem_size, toByteArray_size]
  omega

theorem bidElemBaseMemExec_size (I : ExecutionEnv) (lenSlot : UInt256) :
    (bidElemBaseMemExec I lenSlot).size = 192 := by
  unfold bidElemBaseMemExec
  rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by rw [bidStructMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, bidStructMem_size, toByteArray_size]
  omega

theorem bidHashMemExec_read64 (I : ExecutionEnv) :
    (bidHashMemExec I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold bidHashMemExec
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [bidSourceMem_size]; norm_num) (by omega)
      (by rw [bidSourceMem_size])]
  unfold bidSourceMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; norm_num) (by omega)
      (by rw [solcFreePtrMem_size])]
  exact solcFreePtrMem_read64

set_option maxHeartbeats 800000 in
theorem bidHashMemExec_read0_64 (I : ExecutionEnv) :
    (bidHashMemExec I).readWithPadding 0 64 =
      UInt256.toByteArray (bidSourceWord I) ++ UInt256.toByteArray (⟨4⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' (bidHashMemExec I) 0 64
    (by norm_num) (by norm_num) (by rw [bidHashMemExec_size]; omega)]
  unfold bidHashMemExec
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by rw [bidSourceMem_size]; omega)]
  have hprefix :
      (bidSourceMem I).extract 0 32 = UInt256.toByteArray (bidSourceWord I) := by
    rw [← readWithPadding_eq_extract (bidSourceMem I) 0 (by rw [bidSourceMem_size]; omega)]
    unfold bidSourceMem
    rw [write0_read_back_gen _ _ 32 (by decide) (by rw [toByteArray_size]) (by norm_num)]
    apply ByteArray.ext
    rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
    show (UInt256.toByteArray (bidSourceWord I)).data.size ≤ 32
    rw [show (UInt256.toByteArray (bidSourceWord I)).data.size =
      (UInt256.toByteArray (bidSourceWord I)).size from rfl, toByteArray_size]
  have hslot :
      (UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨4⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
    show (UInt256.toByteArray (⟨4⟩ : UInt256)).data.size ≤ 32
    rw [show (UInt256.toByteArray (⟨4⟩ : UInt256)).data.size =
      (UInt256.toByteArray (⟨4⟩ : UInt256)).size from rfl, toByteArray_size]
  have hfirst64 :
      (((bidSourceMem I).extract 0 32 ++
            (UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32 ++
            (bidSourceMem I).extract (32 + 32) (bidSourceMem I).size).extract 0 (0 + 64)) =
        (bidSourceMem I).extract 0 32 ++
          (UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32 := by
    rw [show 0 + 64 = 64 by norm_num]
    rw [extract_append_left
      ((bidSourceMem I).extract 0 32 ++
        (UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32)
      ((bidSourceMem I).extract (32 + 32) (bidSourceMem I).size) 0 64]
    · rw [show 64 =
          ((bidSourceMem I).extract 0 32 ++
            (UInt256.toByteArray (⟨4⟩ : UInt256)).extract 0 32).size by
          rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
            bidSourceMem_size, toByteArray_size]
          omega]
      exact byteArray_extract_self _
    · rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
        bidSourceMem_size, toByteArray_size]
      omega
  rw [hfirst64]
  rw [hprefix, hslot]

theorem bidHashMemExec_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (bidHashMemExec I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((bidHashMemExec I).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [bidHashMemExec_size]; decide) (by decide)
    (bidHashMemExec_read64 I)

theorem bidElemBaseMemExec_read0 (I : ExecutionEnv) (lenSlot : UInt256) :
    (bidElemBaseMemExec I lenSlot).readWithPadding 0 32 = UInt256.toByteArray lenSlot := by
  unfold bidElemBaseMemExec
  rw [write0_read_back_gen _ _ 32 (by decide) (by rw [toByteArray_size]) (by norm_num)]
  apply ByteArray.ext
  rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
  show (UInt256.toByteArray lenSlot).data.size ≤ 32
  rw [show (UInt256.toByteArray lenSlot).data.size =
    (UInt256.toByteArray lenSlot).size from rfl, toByteArray_size]

theorem bidBlindedMem_read128 (I : ExecutionEnv) :
    (bidBlindedMem I).readWithPadding 128 32 = UInt256.toByteArray (bidBlindedWord I) := by
  unfold bidBlindedMem
  exact bid_toByteArray_write_read_back_of_gap (bidBlindedWord I) (bidAllocMem I) 128
    (by rw [bidAllocMem_size]; exact lt_usize _ (by norm_num))

theorem bidStructMem_read128 (I : ExecutionEnv) :
    (bidStructMem I).readWithPadding 128 32 = UInt256.toByteArray (bidBlindedWord I) := by
  unfold bidStructMem
  rw [write32_read_below _ _ 160 128 (by rw [toByteArray_size])
      (by rw [bidBlindedMem_size]) (by omega)]
  exact bidBlindedMem_read128 I

theorem bidStructMem_read160 (I : ExecutionEnv) :
    (bidStructMem I).readWithPadding 160 32 = UInt256.toByteArray I.weiValue := by
  unfold bidStructMem
  rw [write32_read_back _ _ 160 (by rw [toByteArray_size]) (by rw [bidBlindedMem_size])]
  apply ByteArray.ext
  rw [ByteArray.data_extract, Array.extract_eq_self_of_le]
  show (UInt256.toByteArray I.weiValue).data.size ≤ 32
  rw [show (UInt256.toByteArray I.weiValue).data.size =
    (UInt256.toByteArray I.weiValue).size from rfl, toByteArray_size]

theorem bidElemBaseMemExec_read128 (I : ExecutionEnv) (lenSlot : UInt256) :
    (bidElemBaseMemExec I lenSlot).readWithPadding 128 32 =
      UInt256.toByteArray (bidBlindedWord I) := by
  unfold bidElemBaseMemExec
  rw [write32_read_above _ _ 0 128 (by rw [toByteArray_size])
      (by rw [bidStructMem_size]; omega) (by omega) (by rw [bidStructMem_size]; omega)]
  exact bidStructMem_read128 I

theorem bidElemBaseMemExec_read160 (I : ExecutionEnv) (lenSlot : UInt256) :
    (bidElemBaseMemExec I lenSlot).readWithPadding 160 32 =
      UInt256.toByteArray I.weiValue := by
  unfold bidElemBaseMemExec
  rw [write32_read_above _ _ 0 160 (by rw [toByteArray_size])
      (by rw [bidStructMem_size]; norm_num) (by omega)
      (by rw [bidStructMem_size])]
  exact bidStructMem_read160 I

theorem bidElemBaseMemExec_blinded_mload (I : ExecutionEnv) (lenSlot : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥ (bidElemBaseMemExec I lenSlot).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((bidElemBaseMemExec I lenSlot).readWithPadding
         (⟨128⟩ : UInt256).toNat 32))) = bidBlindedWord I := by
  rw [if_neg]
  · rw [show (⟨128⟩ : UInt256).toNat = 128 by decide]
    rw [bidElemBaseMemExec_read128, fromByteArrayBigEndian_toByteArray]
    exact u256_ofNat_toNat (bidBlindedWord I)
  · rw [bidElemBaseMemExec_size]
    simp only [not_or]
    constructor <;> decide

theorem bidElemBaseMemExec_deposit_mload (I : ExecutionEnv) (lenSlot : UInt256) :
    (if (⟨160⟩ : UInt256).toNat ≥ (bidElemBaseMemExec I lenSlot).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((bidElemBaseMemExec I lenSlot).readWithPadding
         (⟨160⟩ : UInt256).toNat 32))) = I.weiValue := by
  rw [if_neg]
  · rw [show (⟨160⟩ : UInt256).toNat = 160 by decide]
    rw [bidElemBaseMemExec_read160, fromByteArrayBigEndian_toByteArray]
    exact u256_ofNat_toNat I.weiValue
  · rw [bidElemBaseMemExec_size]
    simp only [not_or]
    constructor <;> decide

theorem bidMappingBaseKeccakExec (I : ExecutionEnv) :
    UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC ((bidHashMemExec I).readWithPadding 0 64)))
      = bidLengthSlot I := by
  rw [bidHashMemExec_read0_64, bidLengthSlot_spec]
  exact mappingSlot_single (bidSourceWord I) ⟨4⟩

theorem bidArrayDataKeccakExec (I : ExecutionEnv) (lenSlot : UInt256) :
    UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC ((bidElemBaseMemExec I lenSlot).readWithPadding 0 32)))
      = uInt256OfByteArray (ffi.KEC (UInt256.toByteArray lenSlot)) := by
  rw [bidElemBaseMemExec_read0]
  exact keccakSlot_eq (UInt256.toByteArray lenSlot)

theorem bidTooLateMem_size (deadline : UInt256) : (bidTooLateMem deadline).size = 164 := by
  unfold bidTooLateMem
  rw [write32_eq _ _ 132 (by rw [toByteArray_size]) (by rw [solcReturnMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcReturnMem_size, toByteArray_size]
  omega

theorem bidTooLateMem_read64 (deadline : UInt256) :
    (bidTooLateMem deadline).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold bidTooLateMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [solcReturnMem_size]; omega) (by omega)]
  exact solcReturnMem_read64 bidTooLateSelector

theorem bidTooLateMem_mload64 (deadline : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (bidTooLateMem deadline).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((bidTooLateMem deadline).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [bidTooLateMem_size]; decide) (by decide)
    (bidTooLateMem_read64 deadline)

set_option maxHeartbeats 800000 in
theorem bidMappingBaseKeccak (I : ExecutionEnv) :
    UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC ((bidHashMem I).readWithPadding 0 64)))
      = bidLengthSlot I := by
  rw [bidHashMem_read0_64, bidLengthSlot_spec]
  exact mappingSlot_single (bidSourceWord I) ⟨4⟩

theorem bidArrayDataKeccak (I : ExecutionEnv) (lenSlot : UInt256) :
    UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC ((bidElemBaseMem I lenSlot).readWithPadding 0 32)))
      = uInt256OfByteArray (ffi.KEC (UInt256.toByteArray lenSlot)) := by
  rw [bidElemBaseMem_read0]
  exact keccakSlot_eq (UInt256.toByteArray lenSlot)

theorem bidBlindedValue_toWord (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    valueToWord (bidBlindedValue I) = some (bidBlindedWord I) := by
  unfold bidBlindedValue bidBlindedBytes bidBlindedWord calldataWord
  simp only [valueToWord]
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 31 + 1 := by
    rw [List.length_take, List.length_drop]
    rw [byteArray_toList_eq, Array.length_toList]
    change min 32 (I.calldata.size - 4) = 31 + 1
    omega
  rw [if_pos hlen]
  apply congrArg some
  rw [uInt256OfByteArray_eq]
  apply congrArg UInt256.ofNat
  unfold fromByteArrayBigEndian
  rw [byteArray_toList_eq (I.calldata.readBytes 4 32),
    readBytes_at_toList I.calldata 4 (by omega) (by decide)]
  rw [byteArray_toList_eq]

theorem bidWordOfInt_succ (w : UInt256) :
    EVM.wordOfInt (Int.ofNat w.toNat + 1) = w + ⟨1⟩ := by
  have hn : ¬ Int.ofNat w.toNat + 1 < 0 := by
    exact not_lt_of_ge
      (Int.add_nonneg (Int.natCast_nonneg (w.toNat)) (show (0 : Int) ≤ 1 by decide))
  rw [EVM.wordOfInt, if_neg hn]
  apply u256_inj
  show ((Fin.ofNat UInt256.size (Int.toNat (Int.ofNat w.toNat + 1))).val : Nat) =
    ((w + ⟨1⟩ : UInt256).val.val : Nat)
  have hto : (Int.ofNat w.toNat + 1).toNat = w.toNat + 1 := by
    have hcast : (((Int.ofNat w.toNat + 1).toNat : Nat) : Int) = (w.toNat + 1 : Nat) := by
      rw [Int.toNat_of_nonneg (not_lt.mp hn)]
      norm_num
    omega
  rw [hto, Fin.val_ofNat]
  change (w.toNat + 1) % UInt256.size = (w + ⟨1⟩).toNat
  rw [uadd_toNat]
  rw [show ({ val := 1 } : UInt256).toNat = 1 by rfl]

theorem blindAuctionStorageLocStore_bytes32 (evm : EVM.State) (slot word : UInt256) (v : Value)
    (hval : valueToWord v = some word) :
    storageLocStore evm (blindAuctionBytes32Loc slot) v =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot word) := by
  simpa [blindAuctionBytes32Loc, Reasoning.Theory.bytes32Loc] using
    storageLocStore_bytes32 evm slot word v hval

theorem bidStorageLocStore_uint256_succ (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (blindAuctionUint256Loc slot) (.int (Int.ofNat val.toNat + 1)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (val + ⟨1⟩)) := by
  unfold storageLocStore storageLocWriteWord blindAuctionUint256Loc
  simp only [valueToWord, bidWordOfInt_succ, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (val + ⟨1⟩)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = (val + ⟨1⟩).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

theorem bidPushArray_ok (evm : EVM.State) (hsz36 : 36 ≤ evm.executionEnv.calldata.size) :
    pushArray? blindAuctionConfig { contract := blindAuctionContract, locals := bidStore evm.executionEnv }
      evm (bidsRef sender) (some (bidStructValue evm.executionEnv)) =
      .ok (bidPostState evm evm.executionEnv (bidLengthWord evm.accountMap evm.executionEnv)) := by
  unfold pushArray? resolveStorageRef? evalStorageRef evalStorageRefSteps
    evalStorageRefStep bidsRef sender valueToKey? storageTypeAt? storageTypeStep?
    blindAuctionContract storageDecls bidStructTy bidStructDecl blindAuctionConfig
    blindAuctionStorageLayout bidPostState bidAfterBlindedState bidAfterLengthState
    bidDepositSlot bidElementSlot bidLengthSlot bidSenderKey bidStructValue bidCallValue
  simp [bidStore, evalExpr?, envValue, List.nil_append, EvalResult.bind, bind, pure,
    EvalResult.ofOption]
  rw [blindAuctionStorageLocLoad_uint256]
  simp only [EvalResult.bind, bind]
  rw [bidStorageLocStore_uint256_succ]
  simp only [Option.bind, EvalResult.bind, bind, pure]
  rw [writeStorage?.eq_def]
  simp only [EvalResult.bind, bind]
  rw [writeFields?.eq_def]
  simp only [beq_self_eq_true, reduceIte]
  rw [writeStorage?.eq_def]
  simp only [bytes32St]
  simp only [List.cons_append, List.nil_append]
  rw [blindAuctionStorageLocStore_bytes32
    (word := bidBlindedWord evm.executionEnv)
    (hval := bidBlindedValue_toWord evm.executionEnv hsz36)]
  simp only [EvalResult.ofOption, Option.bind, EvalResult.bind, bind, pure]
  rw [writeFields?.eq_def]
  simp only [beq_self_eq_true, reduceIte]
  rw [writeStorage?.eq_def]
  simp only [uint256St]
  simp only [List.cons_append, List.nil_append]
  rw [blindAuctionStorageLocStore_uint256_natCast]
  simp only [EvalResult.ofOption, Option.bind, EvalResult.bind, bind, pure]
  rw [writeFields?.eq_def]
  rfl

theorem evalExpr_bid_biddingEnd (evm : EVM.State) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := bidStore evm.executionEnv } evm
      (.storage biddingEndRef) =
        .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)) := by
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := bidStore evm.executionEnv } evm biddingEndRef =
      .ok { base := "biddingEnd", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, biddingEndRef, bidStore, EvalResult.bind,
      pure, bind]
  have hty : storageTypeAt? blindAuctionContract.storage
      ({ base := "biddingEnd", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [bidStore, biddingEndRef])
    (her := her) (hty := hty) (hloc := blindAuctionConfig_storage_biddingEnd)]
  rw [blindAuctionStorageLocLoad_uint256]

theorem evalExpr_bid_time_true (evm : EVM.State)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := bidStore evm.executionEnv } evm
      (.binary .lt now (.storage biddingEndRef)) = .ok (.bool true) := by
  simp only [evalExpr?, now, envValue, evalExpr_bid_biddingEnd, bind, EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_bid_time_false (evm : EVM.State)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := bidStore evm.executionEnv } evm
      (.binary .lt now (.storage biddingEndRef)) = .ok (.bool false) := by
  simp only [evalExpr?, now, envValue, evalExpr_bid_biddingEnd, bind, EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem blindAuctionBidBodyReverts_time (evm : EVM.State)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm (bidStore evm.executionEnv)
      bidTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold bidTransition
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_bid_time_false evm htime))

theorem blindAuctionBidBodyReturns (evm : EVM.State)
    (hsz36 : 36 ≤ evm.executionEnv.calldata.size)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm (bidStore evm.executionEnv)
      bidTransition.body
      (.returned { contract := blindAuctionContract, locals := bidStore evm.executionEnv }
        (bidPostState evm evm.executionEnv (bidLengthWord evm.accountMap evm.executionEnv))
        none) := by
  refine ExecFuncBody.execBlockOK ?_
  unfold bidTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_bid_time_true evm htime)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.pushVal
      (by
        simp [bidStructValue, bidBlindedValue, bidCallValue, evalExpr?, evalStructFields?,
          envValue, bidStore, EvalResult.ofOption, EvalResult.bind, pure, bind]
        rfl)
      (bidPushArray_ok evm hsz36))
    ExecBlock.nil

theorem blindAuctionBidSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x95, 0x7b, 0xb1, 0xe0]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x95, 0x7b, 0xb1, 0xe0]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem blindAuctionDispatch_bid {cd : ByteArray}
    (hsel : ((⟨#[0x95, 0x7b, 0xb1, 0xe0]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg blindAuctionContract cd = some bidTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x95, 0x7b, 0xb1, 0xe0]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [])
    (post := [revealTransition, withdrawTransition, auctionEndTransition, beneficiaryGetter,
      biddingEndGetter, revealEndGetter, endedGetter, highestBidderGetter, highestBidGetter,
      bidsGetter]) rfl rfl ?_ (by rw [selectorOf, blindAuctionBidSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.not_mem_nil] at ht

theorem blindAuctionDecode_bid_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata (bidTransition.params.map Param.name)
      (transitionSignature bidTransition).paramTypes I.calldata = some (bidStore I) := by
  show decodeCalldata ["blindedBid"] [bytes32] I.calldata = some (bidStore I)
  simpa [bytes32, abiBytes32, abiBytes32Width, bidStore, bidBlindedValue, bidBlindedBytes]
    using decodeCalldata_bytes32_ok (cd := I.calldata) (x := "blindedBid") hsz36 hbig

theorem blindAuctionDecode_bid_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (bidTransition.params.map Param.name)
      (transitionSignature bidTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["blindedBid"] [bytes32] I.calldata = none
  simpa [bytes32, abiBytes32, abiBytes32Width]
    using decodeCalldata_bytes32_none_short (cd := I.calldata) (x := "blindedBid") hsz4 hshort

theorem blindAuctionDecode_bid_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (bidTransition.params.map Param.name)
      (transitionSignature bidTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["blindedBid"] [bytes32] I.calldata = none
  simpa [bytes32, abiBytes32, abiBytes32Width]
    using decodeCalldata_bytes32_none_huge (cd := I.calldata) (x := "blindedBid") hbig

theorem blindAuctionBidX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1944⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨463⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd449⟩ := hreach
  exact ⟨_, _, evm_run rd449 with [
    jumpdest, push2 ⟨276⟩, push2 ⟨463⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1944⟩, jump (by jump_dest) ]⟩

theorem blindAuctionBidX_decode_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1944⟩ := blindAuctionBidX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hreach
  exact evm_run rd1944 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨1960⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem blindAuctionBidX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1426⟩
      [bidBlindedWord I, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd1944⟩ := blindAuctionBidX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hreach
  have rd1960 := evm_run rd1944 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨1960⟩, jumpiT (by rw [hslt]; decide) (by jump_dest) ]
  have rd463 := evm_run rd1960 with [jumpdest, pop, calldataload, swap2, swap1, pop,
    jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [bidBlindedWord, calldataWord] using
      (evm_run rd463 with [jumpdest, push2 ⟨1426⟩, jump (by jump_dest)])⟩

set_option maxHeartbeats 800000 in
theorem blindAuctionBidX_timeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (htime : (biddingEndWord σ I).toNat ≤ (bidTimestampWord I).toNat)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1426⟩ := blindAuctionBidX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hsz36 hsize hszhi hreach
  have rd1429 := evm_run rd1426 with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd1430₀⟩ := rd1429.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1430⟩ : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1430⟩
      [biddingEndWord σ I, bidBlindedWord I, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [biddingEndWord, initState] using rd1430₀⟩
  have hlt : UInt256.lt (bidTimestampWord I) (biddingEndWord σ I) = ⟨0⟩ :=
    ult_zero htime
  have rd1432 := RD.timestamp (evm_run rd1430 with [dup1]) (by decide) (by evm_ov)
  have rd1433₀ := evm_run rd1432 with [lt]
  have rd1433 := rd1433₀
  rw [show UInt256.lt (UInt256.ofNat I.header.timestamp) (biddingEndWord σ I) = ⟨0⟩ from by
    simpa [bidTimestampWord] using hlt] at rd1433
  have rd1437 := evm_run rd1433 with [push2 ⟨1464⟩, jumpiNT (by decide)]
  have rd1450 := evm_run rd1437 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x348f2b41⟩, push1 ⟨225⟩, shl, dup2,
    raw mstore 6 (solcReturnMem bidTooLateSelector) (UInt256.ofNat 5) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1457 := evm_run rd1450 with [
    push1 ⟨4⟩, dup2, add, dup3, swap1,
    raw mstore 3 (bidTooLateMem (biddingEndWord σ I)) (UInt256.ofNat 6) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd600 := evm_run rd1457 with
    [push1 ⟨36⟩, add, push2 ⟨600⟩, jump (by jump_dest)]
  have rd608 := evm_run rd600 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (bidTooLateMem_mload64 (biddingEndWord σ I)) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact rd608.rev 0 (by decide) mem_cost (by evm_ov)

set_option maxHeartbeats 1200000 in
theorem blindAuctionBidX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (htime : (bidTimestampWord I).toNat < (biddingEndWord σ I).toNat)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨449⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I)
      (worldOf (bidPostState (initState cA gh bl σ σ₀ g A I) I (bidLengthWord σ I)))
      ByteArray.empty := by
  obtain ⟨_, _, rd1426⟩ := blindAuctionBidX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hsz36 hsize hszhi hreach
  have rd1429 := evm_run rd1426 with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd1430₀⟩ := rd1429.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1430⟩ : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1430⟩
      [biddingEndWord σ I, bidBlindedWord I, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [biddingEndWord, initState] using rd1430₀⟩
  have hlt : UInt256.lt (bidTimestampWord I) (biddingEndWord σ I) = ⟨1⟩ :=
    ult_one htime
  have rd1432 := RD.timestamp (evm_run rd1430 with [dup1]) (by decide) (by evm_ov)
  have rd1433₀ := evm_run rd1432 with [lt]
  have rd1433 := rd1433₀
  rw [show UInt256.lt (UInt256.ofNat I.header.timestamp) (biddingEndWord σ I) = ⟨1⟩ from by
    simpa [bidTimestampWord] using hlt] at rd1433
  have rd1464 := evm_run rd1433 with [push2 ⟨1464⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1470 := evm_run rd1464 with [jumpdest, pop, caller, push0, swap1, dup2]
  have rd1471 := evm_run rd1470 with [
    raw mstore 0 (bidSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1478 := evm_run rd1471 with [
    push1 ⟨4⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 (bidHashMemExec I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (bidLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost (bidMappingBaseKeccakExec I) (by decide) (by evm_ov),
    dup2]
  have rd1485 := evm_run rd1478 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (bidHashMemExec_mload64 I) (by decide) (by evm_ov),
    dup1, dup4, add, swap1, swap3]
  have rd1491 := evm_run rd1485 with [
    raw mstore 0 (bidAllocMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1501 := evm_run rd1491 with [
    swap4, dup2,
    raw mstore 6 (bidBlindedMem I) (UInt256.ofNat 5) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    callvalue, dup2, dup4, add, swap1, dup2,
    raw mstore 3 (bidStructMem I) (UInt256.ofNat 6) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    dup5]
  obtain ⟨_, _, rd1503₀⟩ := rd1501.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1503⟩ : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1503⟩
      [bidLengthWord σ I, ⟨160⟩, ⟨128⟩, ⟨32⟩, ⟨0⟩, bidLengthSlot I,
        ⟨276⟩, blindAuctionSelWord I]
      (bidStructMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bidLengthWord, initState] using rd1503₀⟩
  have rd1508 := evm_run rd1503 with [push1 ⟨1⟩, dup2, dup2, add, dup8]
  obtain ⟨_, _, rd1510₀⟩ := rd1508.sstore hperm (by decide) (by evm_ov)
  let evm0 := initState cA gh bl σ σ₀ g A I
  obtain ⟨_, _, rd1510⟩ : ∃ k C, RD blindAuctionBytecode I g evm0 ⟨1510⟩
      [⟨1⟩, bidLengthWord σ I, ⟨160⟩, ⟨128⟩, ⟨32⟩, ⟨0⟩, bidLengthSlot I,
        ⟨276⟩, blindAuctionSelWord I]
      (bidStructMem I) (UInt256.ofNat 6) ByteArray.empty
      (worldOf (bidAfterLengthState evm0 I (bidLengthWord σ I))) k C := by
    exact ⟨_, _, by
      simpa [evm0, bidAfterLengthState, initState, worldOf,
        blindAuctionStorageStore_createdAccounts, blindAuctionStorageStore_accountMap,
        u256_add_comm] using rd1510₀⟩
  have rd1516 := evm_run rd1510 with [
    swap6, dup6,
    raw mstore 0 (bidElemBaseMemExec I (bidLengthSlot I)) (UInt256.ofNat 6) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    swap3, swap1, swap4,
    raw keccak256 0 (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (bidLengthSlot I))))
      (UInt256.ofNat 6) (by decide)
      mem_cost (bidArrayDataKeccakExec I (bidLengthSlot I)) (by decide) (by evm_ov),
    swap1,
    raw mload 0 (bidBlindedWord I) (UInt256.ofNat 6) (by decide)
      mem_cost (bidElemBaseMemExec_blinded_mload I (bidLengthSlot I)) (by decide) (by evm_ov),
    push1 ⟨2⟩, swap1, swap3, mul, add]
  have hElemSlotR :
      UInt256.mul (bidLengthWord σ I) ⟨2⟩ +
          uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (bidLengthSlot I))) =
        bidElementSlot I (bidLengthWord σ I) := by
    rw [u256_add_comm, ← bidElementSlot_spec I (bidLengthWord σ I)]
  have rd1516' := rd1516
  rw [hElemSlotR] at rd1516'
  have rd1526 := evm_run rd1516' with [swap1, dup2]
  obtain ⟨_, _, rd1528₀⟩ := rd1526.sstore hperm (by decide) (by evm_ov)
  have rd1531 := evm_run rd1528₀ with [
    swap1,
    raw mload 0 I.weiValue (UInt256.ofNat 6) (by decide)
      mem_cost (bidElemBaseMemExec_deposit_mload I (bidLengthSlot I)) (by decide) (by evm_ov),
    swap2, add]
  have hDepositSlot :
      (⟨1⟩ : UInt256) + bidElementSlot I (bidLengthWord σ I) =
        bidDepositSlot I (bidLengthWord σ I) := by
    unfold bidDepositSlot
    rw [u256_add_comm]
  have rd1531' := rd1531
  rw [hDepositSlot] at rd1531'
  obtain ⟨_, _, rd1533₀⟩ := rd1531'.sstore hperm (by decide) (by evm_ov)
  have rd276 := evm_run rd1533₀ with [jump (by jump_dest), jumpdest]
  simpa [evm0, bidPostState, bidAfterBlindedState, bidAfterLengthState, initState, worldOf,
    storageStore_executionEnv, blindAuctionStorageStore_createdAccounts,
    blindAuctionStorageStore_accountMap]
    using rd276.stop (by decide) (by evm_ov)

/-- `bid(bytes32)` body (pc 449) refines its transition. -/
theorem blindAuctionBidBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x95, 0x7b, 0xb1, 0xe0]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨449⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
 :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by

  have hsz4 := blindAuctionBidSelector_size hsel
  have hd := blindAuctionDispatch_bid (cd := I.calldata) hsel
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
  have hBiddingEnd : biddingEndWord σ_evm I = biddingEndWord σ_solm I := by
    simpa [evmE, evmS, biddingEndWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using hσ.storageLoad_codeOwner ⟨1⟩
  have hLen : bidLengthWord σ_evm I = bidLengthWord σ_solm I := by
    simpa [evmE, evmS, bidLengthWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using hσ.storageLoad_codeOwner (bidLengthSlot I)
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · have hdec := blindAuctionDecode_bid_ok (I := I) hsz36 hbig
      by_cases htime : (bidTimestampWord I).toNat < (biddingEndWord σ_evm I).toNat
      · have htimeS' : (bidTimestampWord I).toNat < (biddingEndWord σ_solm I).toNat := by
          simpa [hBiddingEnd] using htime
        have hbody :
            ExecTransitionBody blindAuctionConfig blindAuctionContract evmS (bidStore I)
              bidTransition.body
              (.returned { contract := blindAuctionContract, locals := bidStore I }
                (bidPostState evmS I (bidLengthWord σ_solm I)) none) :=
          blindAuctionBidBodyReturns evmS
            (by simpa [evmS, initState] using hsz36)
            (by
              simpa [evmS, initState, biddingEndWord, bidTimestampWord, Solm.EVM.storageLoad,
                State.lookupAccount] using htimeS')
        have hσLen : EVMStateEquiv
            (bidAfterLengthState evmE I (bidLengthWord σ_evm I))
            (bidAfterLengthState evmS I (bidLengthWord σ_solm I)) := by
          unfold bidAfterLengthState
          rw [hσ.executionEnv, hLen]
          exact hσ.storageStore_codeOwner (bidLengthSlot I) rfl
        have hσBlind : EVMStateEquiv
            (bidAfterBlindedState evmE I (bidLengthWord σ_evm I))
            (bidAfterBlindedState evmS I (bidLengthWord σ_solm I)) := by
          unfold bidAfterBlindedState
          simpa [hLen] using
            hσLen.storageStore_codeOwner (bidElementSlot I (bidLengthWord σ_solm I)) rfl
        have hσPost : EVMStateEquiv
            (bidPostState evmE I (bidLengthWord σ_evm I))
            (bidPostState evmS I (bidLengthWord σ_solm I)) := by
          unfold bidPostState
          simpa [hLen] using
            hσBlind.storageStore_codeOwner (bidDepositSlot I (bidLengthWord σ_solm I)) rfl
        exact (blindAuctionBidX_ok (g := Sat256.ofUInt256 g) hperm hsz36 hsize hbig
            htime hreach)
          |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
            (by simp [evmE, worldOf])
            (by simp [evmE, worldOf]; exact accountMapEquiv.refl _)
            hσPost
            (returnEquiv.fallthrough rfl rfl (by native_decide))
      · have htimeLe : (biddingEndWord σ_evm I).toNat ≤ (bidTimestampWord I).toNat := by
          omega
        have htimeS' : (biddingEndWord σ_solm I).toNat ≤ (bidTimestampWord I).toNat := by
          simpa [← hBiddingEnd] using htimeLe
        have hbody :
            ExecTransitionBody blindAuctionConfig blindAuctionContract evmS (bidStore I)
              bidTransition.body .reverted :=
          blindAuctionBidBodyReverts_time evmS (by
            simpa [evmS, initState, biddingEndWord, bidTimestampWord, Solm.EVM.storageLoad,
              State.lookupAccount] using htimeS')
        exact (blindAuctionBidX_timeRevert (g := Sat256.ofUInt256 g) hsz36 hsize hbig
            htimeLe hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := blindAuctionDecode_bid_none_huge (I := I) hbigge
      have hslt := solcDecodeLenCheckHuge_4_32 hbigge hsize
      exact (blindAuctionBidX_decode_revert (g := Sat256.ofUInt256 g) hslt hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := blindAuctionDecode_bid_none_short (I := I) hsz4 hshort
    have hslt := solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
    exact (blindAuctionBidX_decode_revert (g := Sat256.ofUInt256 g) hslt hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end BlindAuction
