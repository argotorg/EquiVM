import Benchmarks.Dss.Flopper.AuctionCommon
import Benchmarks.Dss.Flopper.Tick
import Benchmarks.Dss.Flopper.Yank

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

namespace Benchmarks.Dss.Flopper

/-! ## `dent(uint256,uint256,uint256)` -/

abbrev dentIdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev dentLotWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev dentBidWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev dentIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (dentIdWord I).toNat)

abbrev dentLotValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (dentLotWord I).toNat)

abbrev dentBidValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (dentBidWord I).toNat)

abbrev dentLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "id" (dentIdValue I)).insert "lot" (dentLotValue I)).insert "bid"
    (dentBidValue I)

abbrev dentLiveEvaledRef : EvaledStorageRef :=
  { base := "live", steps := [] }

abbrev dentVatEvaledRef : EvaledStorageRef :=
  { base := "vat", steps := [] }

abbrev dentBegEvaledRef : EvaledStorageRef :=
  { base := "beg", steps := [] }

abbrev dentTtlEvaledRef : EvaledStorageRef :=
  { base := "ttl", steps := [] }

abbrev dentBidEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (dentIdWord I)), .field "bid"] }

abbrev dentLotEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (dentIdWord I)), .field "lot"] }

abbrev dentGuyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (dentIdWord I)), .field "guy"] }

abbrev dentTicEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (dentIdWord I)), .field "tic"] }

abbrev dentEndEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (auctionIdKey (dentIdWord I)), .field "end"] }

abbrev dentLiveWord (evm : EVM.State) : UInt256 :=
  flopperSlotWord ⟨8⟩ evm.accountMap evm.executionEnv

abbrev dentVatWord (evm : EVM.State) : UInt256 :=
  flopperAddressReturnWord ⟨2⟩ evm.accountMap evm.executionEnv

abbrev dentBegWord (evm : EVM.State) : UInt256 :=
  flopperSlotWord ⟨4⟩ evm.accountMap evm.executionEnv

abbrev dentTtlWord (evm : EVM.State) : UInt256 :=
  flopperUint48Offset0Word ⟨6⟩ evm.accountMap evm.executionEnv

abbrev dentBidStoredWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flopperSlotWord (auctionBidSlot (dentIdWord I)) evm.accountMap evm.executionEnv

abbrev dentLotStoredWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flopperSlotWord (auctionLotSlot (dentIdWord I)) evm.accountMap evm.executionEnv

abbrev dentGuyWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) evm.accountMap evm.executionEnv

abbrev dentTicWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) evm.accountMap
    evm.executionEnv

abbrev dentEndWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  flopperUint48Offset26Word (auctionPackedSlot (dentIdWord I)) evm.accountMap
    evm.executionEnv

abbrev dentTimestampWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp

abbrev dentNow48Word (evm : EVM.State) : UInt256 :=
  UInt256.land (dentTimestampWord evm) flopperUint48Mask

abbrev dentOneWord : UInt256 :=
  ⟨1000000000000000000⟩

abbrev dentBegLotWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  dentBegWord evm * dentLotWord I

abbrev dentLotOneWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  dentLotStoredWord evm I * dentOneWord

abbrev dentBegLotLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (dentLocals I).insert "begLot" (.int (Int.ofNat (dentBegLotWord evm I).toNat))

abbrev dentLotOneLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (dentBegLotLocals evm I).insert "lotOne" (.int (Int.ofNat (dentLotOneWord evm I).toNat))

abbrev dentMoveLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (dentLotOneLocals evm I).insert "_moveRet" (collapseReturns [])

abbrev dentAshWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev dentAshLocals (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : Store :=
  (dentMoveLocals evm I).insert "Ash" (.int (Int.ofNat (dentAshWord out).toNat))

abbrev dentKissAmtWord (I : ExecutionEnv) (out : ByteArray) : UInt256 :=
  if (dentBidWord I).toNat ≤ (dentAshWord out).toNat then dentBidWord I else dentAshWord out

abbrev dentKissLocals (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : Store :=
  (dentAshLocals evm I out).insert "kissAmt"
    (.int (Int.ofNat (dentKissAmtWord I out).toNat))

abbrev dentKissRetLocals (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : Store :=
  (dentKissLocals evm I out).insert "_kissRet" (collapseReturns [])

abbrev dentMinLocals (x y : UInt256) : Store :=
  ((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat))

def dentAfterGuyStore (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (auctionPackedSlot (dentIdWord I))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (auctionPackedSlot (dentIdWord I)))
      (UInt256.ofNat evm.executionEnv.source.val))

def dentAfterLotStore (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (auctionLotSlot (dentIdWord I))
    (dentLotWord I)

abbrev dentTicPostWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat)

def dentTicStoredWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  let evmLot := dentAfterLotStore evm I
  setUint48Offset20Word
    (Solm.EVM.storageLoad evmLot evmLot.executionEnv.codeOwner (auctionPackedSlot (dentIdWord I)))
    (dentTicPostWord evm I)

def dentAfterTicStore (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  let evmLot := dentAfterLotStore evm I
  Solm.EVM.storageStore evmLot evmLot.executionEnv.codeOwner (auctionPackedSlot (dentIdWord I))
    (dentTicStoredWord evm I)

def dentPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  dentAfterTicStore evm I

abbrev dentTicLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (dentLotOneLocals evm I).insert "tic_" (.int (Int.ofNat (dentTicPostWord evm I).toNat))

abbrev dentTicWrappedNat (evm : EVM.State) (I : ExecutionEnv) : Nat :=
  ((dentNow48Word evm).toNat + (dentTtlWord (dentAfterLotStore evm I)).toNat) % 2 ^ 48

abbrev dentTicWrappedLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (dentLotOneLocals evm I).insert "tic_" (.int (Int.ofNat (dentTicWrappedNat evm I)))

abbrev dentMoveTicLocals (startEvm tickEvm : EVM.State) (I : ExecutionEnv) : Store :=
  (dentMoveLocals startEvm I).insert "tic_"
    (.int (Int.ofNat (dentTicPostWord tickEvm I).toNat))

abbrev dentMoveTicWrappedLocals (startEvm tickEvm : EVM.State) (I : ExecutionEnv) : Store :=
  (dentMoveLocals startEvm I).insert "tic_"
    (.int (Int.ofNat
      (((dentNow48Word tickEvm).toNat +
        (dentTtlWord (dentAfterLotStore tickEvm I)).toNat) % 2 ^ 48)))

abbrev dentKissRetTicLocals
    (startEvm tickEvm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : Store :=
  (dentKissRetLocals startEvm I out).insert "tic_"
    (.int (Int.ofNat (dentTicPostWord tickEvm I).toNat))

abbrev dentKissRetTicWrappedLocals
    (startEvm tickEvm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : Store :=
  (dentKissRetLocals startEvm I out).insert "tic_"
    (.int (Int.ofNat (dentTicWrappedNat tickEvm I)))

abbrev dentRuntimeAfterLotMap (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) :
    AccountMap :=
  sstoreAccountMap owner σ (auctionLotSlot (dentIdWord I)) (dentLotWord I)

abbrev dentRuntimeAfterGuyMap (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) :
    AccountMap :=
  sstoreAccountMap owner σ (auctionPackedSlot (dentIdWord I))
    (setAddressOffset0Word
      (solcSlotWord σ I (auctionPackedSlot (dentIdWord I))) (UInt256.ofNat I.source.val))

abbrev dentRuntimeTtlWord (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  flopperUint48Offset0Word ⟨6⟩ (dentRuntimeAfterLotMap owner σ I) I

abbrev dentRuntimeTicAddWord (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.ofNat I.header.timestamp + dentRuntimeTtlWord owner σ I

abbrev dentRuntimeTicStoredWord (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  setUint48Offset20Word
    (solcSlotWord (dentRuntimeAfterLotMap owner σ I) I (auctionPackedSlot (dentIdWord I)))
    (dentRuntimeTicAddWord owner σ I)

abbrev dentRuntimeTailSuccessAccountMap
    (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap owner (dentRuntimeAfterLotMap owner σ I)
    (auctionPackedSlot (dentIdWord I)) (dentRuntimeTicStoredWord owner σ I)

abbrev dentMoveSelectorWord : UInt256 :=
  ⟨0xbb35783b⟩

abbrev dentMoveSelectorShifted : UInt256 :=
  UInt256.shiftLeft dentMoveSelectorWord ⟨224⟩

abbrev dentMoveOutPtr : UInt256 := ⟨128⟩

abbrev dentMoveInSize : UInt256 := ⟨100⟩

abbrev dentMoveOutSize : UInt256 := ⟨0⟩

abbrev dentMoveEndPtr : UInt256 := ⟨228⟩

abbrev dentAshSelectorSeedWord : UInt256 :=
  ⟨0x0a874acf⟩

abbrev dentAshSelectorWord : UInt256 :=
  ⟨0x2a1d2b3c⟩

abbrev dentAshSelectorShifted : UInt256 :=
  UInt256.shiftLeft dentAshSelectorSeedWord ⟨226⟩

abbrev dentAshOutPtr : UInt256 := ⟨128⟩

abbrev dentAshInSize : UInt256 := ⟨4⟩

abbrev dentAshOutSize : UInt256 := ⟨32⟩

abbrev dentAshEndPtr : UInt256 := ⟨132⟩

abbrev dentKissSelectorWord : UInt256 :=
  ⟨0x2506855a⟩

abbrev dentKissSelectorShifted : UInt256 :=
  UInt256.shiftLeft dentKissSelectorWord ⟨224⟩

abbrev dentKissOutPtr : UInt256 := ⟨128⟩

abbrev dentKissInSize : UInt256 := ⟨36⟩

abbrev dentKissOutSize : UInt256 := ⟨0⟩

abbrev dentKissEndPtr : UInt256 := ⟨164⟩

noncomputable def dentMoveSelectorMem (mem : ByteArray) : ByteArray :=
  dentMoveSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def dentAshSelectorMem (mem : ByteArray) : ByteArray :=
  dentAshSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def dentKissSelectorMem (mem : ByteArray) : ByteArray :=
  dentKissSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def dentKissCalldataMem (amt : UInt256) (mem : ByteArray) : ByteArray :=
  amt.toByteArray.write 0 (dentKissSelectorMem mem) 132 32

noncomputable def dentMoveSrcMem (src : UInt256) (mem : ByteArray) : ByteArray :=
  src.toByteArray.write 0 (dentMoveSelectorMem mem) 132 32

noncomputable def dentMoveGuyMem (src guy : UInt256) (mem : ByteArray) : ByteArray :=
  guy.toByteArray.write 0 (dentMoveSrcMem src mem) 164 32

noncomputable def dentMoveCalldataMem (src guy bid : UInt256) (mem : ByteArray) : ByteArray :=
  bid.toByteArray.write 0 (dentMoveGuyMem src guy mem) 196 32

theorem dentMoveSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (dentMoveSelectorMem mem).size = 160 := by
  unfold dentMoveSelectorMem
  exact toByteArray_write32_size_of_ge mem dentMoveSelectorShifted 128 96 160 hmem
    (by omega) (by native_decide) (by omega)

theorem dentMoveSrcMem_size (src : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (dentMoveSrcMem src mem).size = 164 := by
  unfold dentMoveSrcMem
  exact toByteArray_write32_size_of_le (dentMoveSelectorMem mem) src 132 160 164
    (dentMoveSelectorMem_size hmem)
    (by rw [dentMoveSelectorMem_size hmem]; omega) (by omega)

theorem dentMoveGuyMem_size (src guy : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dentMoveGuyMem src guy mem).size = 196 := by
  unfold dentMoveGuyMem
  exact toByteArray_write32_size_of_le (dentMoveSrcMem src mem) guy 164 164 196
    (dentMoveSrcMem_size src hmem)
    (by rw [dentMoveSrcMem_size src hmem]) (by omega)

theorem dentMoveCalldataMem_size (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dentMoveCalldataMem src guy bid mem).size = 228 := by
  unfold dentMoveCalldataMem
  exact toByteArray_write32_size_of_le (dentMoveGuyMem src guy mem) bid 196 196 228
    (dentMoveGuyMem_size src guy hmem)
    (by rw [dentMoveGuyMem_size src guy hmem]) (by omega)

theorem dentMoveSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dentMoveSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dentMoveSelectorMem
  rw [toByteArray_write_read_below_of_gap dentMoveSelectorShifted mem 128 64
    (by omega) (by native_decide) (by rw [hmem]; native_decide),
    hread64]

theorem dentMoveSrcMem_read64 (src : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dentMoveSrcMem src mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dentMoveSrcMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [dentMoveSelectorMem_size hmem]; omega) (by omega),
    dentMoveSelectorMem_read64 hmem hread64]

theorem dentMoveGuyMem_read64 (src guy : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dentMoveGuyMem src guy mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dentMoveGuyMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [dentMoveSrcMem_size src hmem]) (by omega),
    dentMoveSrcMem_read64 src hmem hread64]

theorem dentMoveCalldataMem_read64 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dentMoveCalldataMem src guy bid mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold dentMoveCalldataMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by rw [dentMoveGuyMem_size src guy hmem]) (by omega),
    dentMoveGuyMem_read64 src guy hmem hread64]

theorem wordAt0Mem_size_of_ge_32 {mem : ByteArray} (word : UInt256)
    (hmem : 32 ≤ mem.size) :
    (wordAt0Mem word mem).size = mem.size := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 mem.size mem.size rfl
    (by omega) (by simp [Nat.max_eq_left hmem])

theorem wordAt32Mem_size_of_ge_64 {mem : ByteArray} (word : UInt256)
    (hmem : 64 ≤ mem.size) :
    (wordAt32Mem word mem).size = mem.size := by
  unfold wordAt32Mem
  exact toByteArray_write32_size_of_le mem word 32 mem.size mem.size rfl
    (by omega) (by simp [Nat.max_eq_left hmem])

theorem twoWordHashMem_size_of_ge_64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem
  rw [wordAt32Mem_size_of_ge_64 slot]
  · exact wordAt0Mem_size_of_ge_32 key (by omega)
  · rw [wordAt0Mem_size_of_ge_32 key (by omega)]
    exact hmem

theorem twoWordHashMem_read64_of_ge_96 {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by
        rw [wordAt0Mem_size_of_ge_32 key (by omega)]
        omega)
      (by omega)
      (by
        rw [wordAt0Mem_size_of_ge_32 key (by omega)]
        omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega)
      (by omega) (by omega)]
  exact hread64

theorem dentAshSelectorMem_read64 {mem : ByteArray}
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dentAshSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dentAshSelectorMem
  rw [toByteArray_write_read_below_of_gap dentAshSelectorShifted mem 128 64
    (by omega) (by omega)
    (by
      have hle : 128 - mem.size ≤ 32 := by omega
      exact lt_of_le_of_lt hle (by native_decide : 32 < USize.size)),
    hread64]

theorem dentAshSelectorMem_read128_4 {mem : ByteArray} (hmem : 96 ≤ mem.size) :
    (dentAshSelectorMem mem).readWithPadding dentAshOutPtr.toNat dentAshInSize.toNat =
      AshSelector := by
  change (dentAshSelectorMem mem).readWithPadding 128 4 = AshSelector
  unfold dentAshSelectorMem
  rw [toByteArray_write_read_window_of_gap dentAshSelectorShifted mem 128 0 4
    (by omega) (by native_decide) (by native_decide)
    (by
      have hle : 128 - mem.size ≤ 32 := by omega
      exact lt_of_le_of_lt hle (by native_decide : 32 < USize.size))]
  native_decide

theorem dentAshEncode_eq {mem : ByteArray} (hmem : 96 ≤ mem.size) :
    config.externalABI.encode? "Ash" [] =
      some ((dentAshSelectorMem mem).readWithPadding dentAshOutPtr.toNat
        dentAshInSize.toNat) := by
  rw [dentAshSelectorMem_read128_4 hmem]
  simp [config, externalABI]

theorem dentKissSelectorMem_read64 {mem : ByteArray}
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dentKissSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dentKissSelectorMem
  rw [toByteArray_write_read_below_of_gap dentKissSelectorShifted mem 128 64
    (by omega) (by omega)
    (by
      have hle : 128 - mem.size ≤ 32 := by omega
      exact lt_of_le_of_lt hle (by native_decide : 32 < USize.size)),
    hread64]

theorem dentKissCalldataMem_read64 (amt : UInt256) {mem : ByteArray}
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dentKissCalldataMem amt mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold dentKissCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by
      unfold dentKissSelectorMem
      have hsize :=
        toByteArray_write_size_ge_off_add32 dentKissSelectorShifted mem 128
          (by
            have hle : 128 - mem.size ≤ 32 := by omega
            exact lt_of_le_of_lt hle (by native_decide : 32 < USize.size))
      omega)
    (by omega)]
  exact dentKissSelectorMem_read64 hmem hread64

theorem dentKissSelectorMem_read128_4 {mem : ByteArray} :
    (dentKissSelectorMem mem).readWithPadding 128 4 = kissSelector := by
  unfold dentKissSelectorMem
  rw [toByteArray_write_read_window_of_gap dentKissSelectorShifted mem 128 0 4
    (by omega) (by native_decide) (by native_decide)
    (by
      exact lt_of_le_of_lt (Nat.sub_le 128 mem.size)
        (by native_decide : 128 < USize.size))]
  native_decide

theorem dentKissCalldataMem_read128_4 (amt : UInt256) {mem : ByteArray} :
    (dentKissCalldataMem amt mem).readWithPadding 128 4 = kissSelector := by
  unfold dentKissCalldataMem
  rw [toByteArray_write_read_below_len_of_gap amt (dentKissSelectorMem mem) 132 128 4
    (by
      unfold dentKissSelectorMem
      have hsize := toByteArray_write_size_ge_off_add32 dentKissSelectorShifted mem 128
        (by
          exact lt_of_le_of_lt (Nat.sub_le 128 mem.size)
            (by native_decide : 128 < USize.size))
      omega)
    (by omega) (by native_decide) (by native_decide)
    (by
      exact lt_of_le_of_lt (Nat.sub_le 132 (dentKissSelectorMem mem).size)
        (by native_decide : 132 < USize.size))]
  exact dentKissSelectorMem_read128_4

theorem dentKissCalldataMem_read132_32 (amt : UInt256) {mem : ByteArray} :
    (dentKissCalldataMem amt mem).readWithPadding 132 32 = amt.toByteArray := by
  unfold dentKissCalldataMem
  rw [toByteArray_write_read_back_of_gap amt (dentKissSelectorMem mem) 132
    (by
      exact lt_of_le_of_lt (Nat.sub_le 132 (dentKissSelectorMem mem).size)
        (by native_decide : 132 < USize.size))]

theorem dentKissCalldataMem_read128_36 (amt : UInt256) {mem : ByteArray} :
    (dentKissCalldataMem amt mem).readWithPadding 128 36 =
      kissSelector ++ amt.toByteArray := by
  have hsize : 164 ≤ (dentKissCalldataMem amt mem).size := by
    unfold dentKissCalldataMem
    simpa [show 132 + 32 = 164 from rfl] using
      toByteArray_write_size_ge_off_add32 amt (dentKissSelectorMem mem) 132
        (by
          exact lt_of_le_of_lt (Nat.sub_le 132 (dentKissSelectorMem mem).size)
            (by native_decide : 132 < USize.size))
  rw [show 36 = 4 + 32 from rfl,
    byteArray_readWithPadding_split (dentKissCalldataMem amt mem) 128 4 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  rw [dentKissCalldataMem_read128_4 amt, dentKissCalldataMem_read132_32 amt]

theorem dentKissEncode_eq (amt : UInt256) {mem : ByteArray} :
    config.externalABI.encode? "kiss" [.int (Int.ofNat amt.toNat)] =
      some ((dentKissCalldataMem amt mem).readWithPadding
        dentKissOutPtr.toNat dentKissInSize.toNat) := by
  change config.externalABI.encode? "kiss" [.int (Int.ofNat amt.toNat)] =
    some ((dentKissCalldataMem amt mem).readWithPadding 128 36)
  rw [dentKissCalldataMem_read128_36 amt]
  have hamtLt : amt.toNat < EVM.twoPow 256 := amt.val.isLt
  have hamtWord : EVM.word amt.toNat = amt := by
    show UInt256.ofNat amt.toNat = amt
    exact u256_ofNat_toNat _
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    uint256, uint256Int, kissSelector, selectorBytes, hamtLt, hamtWord,
    word_toBytesBE_toByteArray_eq_toByteArray]

theorem dentMoveCalldataMem_read128_4 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dentMoveCalldataMem src guy bid mem).readWithPadding 128 4 = moveSelector := by
  have hGuySize := dentMoveGuyMem_size src guy hmem
  have hSrcSize := dentMoveSrcMem_size src hmem
  have hSelectorSize := dentMoveSelectorMem_size hmem
  unfold dentMoveCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (dentMoveGuyMem src guy mem) 196 128 4
      (by rw [hGuySize]; omega) (by omega) (by omega) (by omega)
      (by rw [hGuySize]; native_decide)]
  unfold dentMoveGuyMem
  rw [toByteArray_write_read_below_len_of_gap guy (dentMoveSrcMem src mem) 164 128 4
      (by rw [hSrcSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSrcSize]; native_decide)]
  unfold dentMoveSrcMem
  rw [toByteArray_write_read_below_len_of_gap src (dentMoveSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold dentMoveSelectorMem
  rw [toByteArray_write_read_window_of_gap dentMoveSelectorShifted mem 128 0 4
      (by omega) (by omega) (by omega) (by rw [hmem]; native_decide)]
  native_decide

theorem dentMoveCalldataMem_read132_32 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dentMoveCalldataMem src guy bid mem).readWithPadding 132 32 = src.toByteArray := by
  have hGuySize := dentMoveGuyMem_size src guy hmem
  have hSrcSize := dentMoveSrcMem_size src hmem
  have hSelectorSize := dentMoveSelectorMem_size hmem
  unfold dentMoveCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (dentMoveGuyMem src guy mem) 196 132 32
      (by rw [hGuySize]; omega) (by omega) (by omega) (by omega)
      (by rw [hGuySize]; native_decide)]
  unfold dentMoveGuyMem
  rw [toByteArray_write_read_below_len_of_gap guy (dentMoveSrcMem src mem) 164 132 32
      (by rw [hSrcSize]) (by omega) (by omega) (by omega)
      (by rw [hSrcSize]; native_decide)]
  unfold dentMoveSrcMem
  rw [toByteArray_write_read_back_of_gap src (dentMoveSelectorMem mem) 132
    (by rw [hSelectorSize]; native_decide)]

theorem dentMoveCalldataMem_read164_32 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dentMoveCalldataMem src guy bid mem).readWithPadding 164 32 = guy.toByteArray := by
  have hGuySize := dentMoveGuyMem_size src guy hmem
  have hSrcSize := dentMoveSrcMem_size src hmem
  unfold dentMoveCalldataMem
  rw [toByteArray_write_read_below_len_of_gap bid (dentMoveGuyMem src guy mem) 196 164 32
      (by rw [hGuySize]) (by omega) (by omega) (by omega)
      (by rw [hGuySize]; native_decide)]
  unfold dentMoveGuyMem
  rw [toByteArray_write_read_back_of_gap guy (dentMoveSrcMem src mem) 164
    (by rw [hSrcSize]; native_decide)]

theorem dentMoveCalldataMem_read196_32 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dentMoveCalldataMem src guy bid mem).readWithPadding 196 32 = bid.toByteArray := by
  have hGuySize := dentMoveGuyMem_size src guy hmem
  unfold dentMoveCalldataMem
  rw [toByteArray_write_read_back_of_gap bid (dentMoveGuyMem src guy mem) 196
    (by rw [hGuySize]; native_decide)]

theorem dentMoveCalldataMem_read128_100 (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dentMoveCalldataMem src guy bid mem).readWithPadding 128 100 =
      moveSelector ++ src.toByteArray ++ guy.toByteArray ++ bid.toByteArray := by
  have hsize : (dentMoveCalldataMem src guy bid mem).size = 228 :=
    dentMoveCalldataMem_size src guy bid hmem
  rw [show 100 = 4 + 96 from rfl,
    byteArray_readWithPadding_split (dentMoveCalldataMem src guy bid mem) 128 4 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (dentMoveCalldataMem src guy bid mem) 132 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (dentMoveCalldataMem src guy bid mem) 164 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [dentMoveCalldataMem_read128_4 src guy bid hmem,
    dentMoveCalldataMem_read132_32 src guy bid hmem,
    dentMoveCalldataMem_read164_32 src guy bid hmem,
    dentMoveCalldataMem_read196_32 src guy bid hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem dentMoveEncode_eq (src guy bid : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hsrcCanon : src.toNat < EVM.addressModulus)
    (hguyCanon : guy.toNat < EVM.addressModulus) :
    config.externalABI.encode? "move"
        [.address (AccountAddress.ofNat src.toNat),
          .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat bid.toNat)] =
      some ((dentMoveCalldataMem src guy bid mem).readWithPadding
        dentMoveOutPtr.toNat dentMoveInSize.toNat) := by
  change config.externalABI.encode? "move"
      [.address (AccountAddress.ofNat src.toNat),
        .address (AccountAddress.ofNat guy.toNat), .int (Int.ofNat bid.toNat)] =
    some ((dentMoveCalldataMem src guy bid mem).readWithPadding 128 100)
  rw [dentMoveCalldataMem_read128_100 src guy bid hmem]
  have hbidLt : bid.toNat < EVM.twoPow 256 := bid.val.isLt
  have hbidWord : EVM.word bid.toNat = bid := by
    show UInt256.ofNat bid.toNat = bid
    exact u256_ofNat_toNat _
  have hsrcWord := flopperAddressWord_eq_ofNat_address hsrcCanon
  have hguyWord := flopperAddressWord_eq_ofNat_address hguyCanon
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, uint256, uint256Int, moveSelector, selectorBytes, hbidLt, hbidWord,
    hsrcWord, hguyWord, word_toBytesBE_toByteArray_eq_toByteArray]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem dentTypedCallViaEVM_zero_setSubstate {cfg : Config} {evm evm' : EVM.State}
    {tgt : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray} {perm : Bool}
    (hcall : typedCallViaEVM cfg evm tgt name 0 args (z, evm', out) perm)
    (hdepth : evm.executionEnv.depth ≠ 1024) (A0 : Substate) :
    ∃ A',
      typedCallViaEVM cfg { evm with substate := A0 } tgt name 0 args
        (z,
          { { evm with substate := A0 } with
            accountMap := evm'.accountMap
            substate := A'
            createdAccounts := evm'.createdAccounts },
          out) perm := by
  obtain ⟨calldata, henc, hraw⟩ := hcall
  cases hraw with
  | callMade hvalue hTheta hevm' hvalueLe _hdepth =>
      rename_i valueWord cA' σ' g' A'
      subst evm'
      rcases hTheta with ⟨callGas, A_in, hTheta⟩
      refine ⟨A', ⟨calldata, henc, ?_⟩⟩
      refine callViaEVM.callMade (valueWord := valueWord) (cA' := cA') (σ' := σ')
        (g' := g') (A' := A') (perm := perm) hvalue ⟨callGas, A_in, ?_⟩ ?_ ?_ ?_
      · simpa using hTheta
      · rfl
      · simpa using hvalueLe
      · simpa using hdepth
  | callNotMade _hsubstate _hevm' hfail =>
      exfalso
      exact hfail ⟨(by show (⟨0⟩ : UInt256) ≤ _; exact Fin.zero_le _), hdepth⟩

theorem byteArray_write_size_ge_base
    (src base : ByteArray) (srcOff destOff len : Nat) :
    base.size ≤ (src.write srcOff base destOff len).size := by
  unfold ByteArray.write
  split
  · simp
  · split
    · change base.data.size ≤
        (ByteArray.copySlice (ffi.ByteArray.zeroes (min len (base.size - destOff))) 0 base
          (min destOff base.size) (min len (base.size - destOff)) true).data.size
      rw [ByteArray.data_copySlice]
      simp [Array.size_append, Array.size_extract]
      omega
    · change base.data.size ≤
        (ByteArray.copySlice
          (src ++ ffi.ByteArray.zeroes
            (min base.size (destOff + len) - (destOff + min len (src.size - srcOff))))
          srcOff (base ++ ffi.ByteArray.zeroes (destOff - base.size)) destOff
          (min len (src.size - srcOff) +
            (min base.size (destOff + len) - (destOff + min len (src.size - srcOff))))
          true).data.size
      rw [ByteArray.data_copySlice]
      simp [Array.size_append, Array.size_extract]
      omega

theorem dentRuntimeTtlWord_lt (owner : AccountAddress) (σ : AccountMap) (I : ExecutionEnv) :
    (dentRuntimeTtlWord owner σ I).toNat < 2 ^ 48 := by
  simpa [dentRuntimeTtlWord, flopperUint48Offset0Word, EVM.twoPow] using
    flopperUint48Masked_lt (flopperSlotWord ⟨6⟩ (dentRuntimeAfterLotMap owner σ I) I)

theorem dentLocals_get_id (I : ExecutionEnv) :
    (dentLocals I).get? "id" = some (dentIdValue I) := by
  rw [dentLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem dentLocals_get_lot (I : ExecutionEnv) :
    (dentLocals I).get? "lot" = some (dentLotValue I) := by
  rw [dentLocals, store_get_ne _ _ (by decide), store_get_self]

theorem dentLocals_get_bid (I : ExecutionEnv) :
    (dentLocals I).get? "bid" = some (dentBidValue I) := by
  rw [dentLocals, store_get_self]

theorem dentLocals_get_bids (I : ExecutionEnv) :
    (dentLocals I).get? "bids" = none := by
  rw [dentLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp [Std.HashMap.get?_eq_getElem?]

theorem dentLocals_get_ttl (I : ExecutionEnv) :
    (dentLocals I).get? "ttl" = none := by
  rw [dentLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp [Std.HashMap.get?_eq_getElem?]

theorem dentMinLocals_get_x (x y : UInt256) :
    (dentMinLocals x y).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [dentMinLocals, store_get_self]

theorem dentMinLocals_get_y (x y : UInt256) :
    (dentMinLocals x y).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [dentMinLocals, store_get_ne _ _ (by decide), store_get_self]

theorem dentBegLotLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (dentBegLotLocals evm I).get? "id" = some (dentIdValue I) := by
  rw [dentBegLotLocals, store_get_ne _ _ (by decide)]
  exact dentLocals_get_id I

theorem dentBegLotLocals_get_lot (evm : EVM.State) (I : ExecutionEnv) :
    (dentBegLotLocals evm I).get? "lot" = some (dentLotValue I) := by
  rw [dentBegLotLocals, store_get_ne _ _ (by decide)]
  exact dentLocals_get_lot I

theorem dentBegLotLocals_get_bid (evm : EVM.State) (I : ExecutionEnv) :
    (dentBegLotLocals evm I).get? "bid" = some (dentBidValue I) := by
  rw [dentBegLotLocals, store_get_ne _ _ (by decide)]
  exact dentLocals_get_bid I

theorem dentBegLotLocals_get_begLot (evm : EVM.State) (I : ExecutionEnv) :
    (dentBegLotLocals evm I).get? "begLot" =
      some (.int (Int.ofNat (dentBegLotWord evm I).toNat)) := by
  rw [dentBegLotLocals, store_get_self]

theorem dentBegLotLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) :
    (dentBegLotLocals evm I).get? "bids" = none := by
  rw [dentBegLotLocals, store_get_ne _ _ (by decide)]
  exact dentLocals_get_bids I

theorem dentBegLotLocals_get_ttl (evm : EVM.State) (I : ExecutionEnv) :
    (dentBegLotLocals evm I).get? "ttl" = none := by
  rw [dentBegLotLocals, store_get_ne _ _ (by decide)]
  exact dentLocals_get_ttl I

theorem dentLotOneLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (dentLotOneLocals evm I).get? "id" = some (dentIdValue I) := by
  rw [dentLotOneLocals, store_get_ne _ _ (by decide)]
  exact dentBegLotLocals_get_id evm I

theorem dentLotOneLocals_get_lot (evm : EVM.State) (I : ExecutionEnv) :
    (dentLotOneLocals evm I).get? "lot" = some (dentLotValue I) := by
  rw [dentLotOneLocals, store_get_ne _ _ (by decide)]
  exact dentBegLotLocals_get_lot evm I

theorem dentLotOneLocals_get_bid (evm : EVM.State) (I : ExecutionEnv) :
    (dentLotOneLocals evm I).get? "bid" = some (dentBidValue I) := by
  rw [dentLotOneLocals, store_get_ne _ _ (by decide)]
  exact dentBegLotLocals_get_bid evm I

theorem dentLotOneLocals_get_begLot (evm : EVM.State) (I : ExecutionEnv) :
    (dentLotOneLocals evm I).get? "begLot" =
      some (.int (Int.ofNat (dentBegLotWord evm I).toNat)) := by
  rw [dentLotOneLocals, store_get_ne _ _ (by decide)]
  exact dentBegLotLocals_get_begLot evm I

theorem dentLotOneLocals_get_lotOne (evm : EVM.State) (I : ExecutionEnv) :
    (dentLotOneLocals evm I).get? "lotOne" =
      some (.int (Int.ofNat (dentLotOneWord evm I).toNat)) := by
  rw [dentLotOneLocals, store_get_self]

theorem dentLotOneLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) :
    (dentLotOneLocals evm I).get? "bids" = none := by
  rw [dentLotOneLocals, store_get_ne _ _ (by decide)]
  exact dentBegLotLocals_get_bids evm I

theorem dentLotOneLocals_get_ttl (evm : EVM.State) (I : ExecutionEnv) :
    (dentLotOneLocals evm I).get? "ttl" = none := by
  rw [dentLotOneLocals, store_get_ne _ _ (by decide)]
  exact dentBegLotLocals_get_ttl evm I

theorem dentTicLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (dentTicLocals evm I).get? "id" = some (dentIdValue I) := by
  rw [dentTicLocals, store_get_ne _ _ (by decide)]
  exact dentLotOneLocals_get_id evm I

theorem dentTicLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) :
    (dentTicLocals evm I).get? "bids" = none := by
  rw [dentTicLocals, store_get_ne _ _ (by decide)]
  exact dentLotOneLocals_get_bids evm I

theorem dentTicLocals_get_tic (evm : EVM.State) (I : ExecutionEnv) :
    (dentTicLocals evm I).get? "tic_" =
      some (.int (Int.ofNat (dentTicPostWord evm I).toNat)) := by
  rw [dentTicLocals, store_get_self]

theorem dentTicWrappedLocals_get_tic (evm : EVM.State) (I : ExecutionEnv) :
    (dentTicWrappedLocals evm I).get? "tic_" =
      some (.int (Int.ofNat (dentTicWrappedNat evm I))) := by
  rw [dentTicWrappedLocals, store_get_self]

theorem dentMoveLocals_get_id (evm : EVM.State) (I : ExecutionEnv) :
    (dentMoveLocals evm I).get? "id" = some (dentIdValue I) := by
  rw [dentMoveLocals, store_get_ne _ _ (by decide)]
  exact dentLotOneLocals_get_id evm I

theorem dentMoveLocals_get_lot (evm : EVM.State) (I : ExecutionEnv) :
    (dentMoveLocals evm I).get? "lot" = some (dentLotValue I) := by
  rw [dentMoveLocals, store_get_ne _ _ (by decide)]
  exact dentLotOneLocals_get_lot evm I

theorem dentMoveLocals_get_bid (evm : EVM.State) (I : ExecutionEnv) :
    (dentMoveLocals evm I).get? "bid" = some (dentBidValue I) := by
  rw [dentMoveLocals, store_get_ne _ _ (by decide)]
  exact dentLotOneLocals_get_bid evm I

theorem dentMoveLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) :
    (dentMoveLocals evm I).get? "bids" = none := by
  rw [dentMoveLocals, store_get_ne _ _ (by decide)]
  exact dentLotOneLocals_get_bids evm I

theorem dentMoveLocals_get_ttl (evm : EVM.State) (I : ExecutionEnv) :
    (dentMoveLocals evm I).get? "ttl" = none := by
  rw [dentMoveLocals, store_get_ne _ _ (by decide)]
  exact dentLotOneLocals_get_ttl evm I

theorem dentAshLocals_get_id (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentAshLocals evm I out).get? "id" = some (dentIdValue I) := by
  rw [dentAshLocals, store_get_ne _ _ (by decide)]
  exact dentMoveLocals_get_id evm I

theorem dentAshLocals_get_lot (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentAshLocals evm I out).get? "lot" = some (dentLotValue I) := by
  rw [dentAshLocals, store_get_ne _ _ (by decide)]
  exact dentMoveLocals_get_lot evm I

theorem dentAshLocals_get_bid (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentAshLocals evm I out).get? "bid" = some (dentBidValue I) := by
  rw [dentAshLocals, store_get_ne _ _ (by decide)]
  exact dentMoveLocals_get_bid evm I

theorem dentAshLocals_get_Ash (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentAshLocals evm I out).get? "Ash" =
      some (.int (Int.ofNat (dentAshWord out).toNat)) := by
  rw [dentAshLocals, store_get_self]

theorem dentAshLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentAshLocals evm I out).get? "bids" = none := by
  rw [dentAshLocals, store_get_ne _ _ (by decide)]
  exact dentMoveLocals_get_bids evm I

theorem dentAshLocals_get_ttl (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentAshLocals evm I out).get? "ttl" = none := by
  rw [dentAshLocals, store_get_ne _ _ (by decide)]
  exact dentMoveLocals_get_ttl evm I

theorem dentKissLocals_get_id (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentKissLocals evm I out).get? "id" = some (dentIdValue I) := by
  rw [dentKissLocals, store_get_ne _ _ (by decide)]
  exact dentAshLocals_get_id evm I out

theorem dentKissLocals_get_lot (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentKissLocals evm I out).get? "lot" = some (dentLotValue I) := by
  rw [dentKissLocals, store_get_ne _ _ (by decide)]
  exact dentAshLocals_get_lot evm I out

theorem dentKissLocals_get_bid (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentKissLocals evm I out).get? "bid" = some (dentBidValue I) := by
  rw [dentKissLocals, store_get_ne _ _ (by decide)]
  exact dentAshLocals_get_bid evm I out

theorem dentKissLocals_get_kissAmt (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentKissLocals evm I out).get? "kissAmt" =
      some (.int (Int.ofNat (dentKissAmtWord I out).toNat)) := by
  rw [dentKissLocals, store_get_self]

theorem dentKissLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentKissLocals evm I out).get? "bids" = none := by
  rw [dentKissLocals, store_get_ne _ _ (by decide)]
  exact dentAshLocals_get_bids evm I out

theorem dentKissLocals_not_mem_bids (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    "bids" ∉ dentKissLocals evm I out := by
  intro hmem
  have hsome :=
    (Std.HashMap.mem_iff_isSome_getElem?
      (m := dentKissLocals evm I out) (a := "bids")).mp hmem
  rw [← Std.HashMap.get?_eq_getElem?, dentKissLocals_get_bids evm I out] at hsome
  cases hsome

theorem dentKissLocals_get_ttl (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentKissLocals evm I out).get? "ttl" = none := by
  rw [dentKissLocals, store_get_ne _ _ (by decide)]
  exact dentAshLocals_get_ttl evm I out

theorem dentKissRetLocals_get_id (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentKissRetLocals evm I out).get? "id" = some (dentIdValue I) := by
  rw [dentKissRetLocals, store_get_ne _ _ (by decide)]
  exact dentKissLocals_get_id evm I out

theorem dentKissRetLocals_get_lot (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentKissRetLocals evm I out).get? "lot" = some (dentLotValue I) := by
  rw [dentKissRetLocals, store_get_ne _ _ (by decide)]
  exact dentKissLocals_get_lot evm I out

theorem dentKissRetLocals_get_bid (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentKissRetLocals evm I out).get? "bid" = some (dentBidValue I) := by
  rw [dentKissRetLocals, store_get_ne _ _ (by decide)]
  exact dentKissLocals_get_bid evm I out

theorem dentKissRetLocals_get_bids (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentKissRetLocals evm I out).get? "bids" = none := by
  rw [dentKissRetLocals, store_get_ne _ _ (by decide)]
  exact dentKissLocals_get_bids evm I out

theorem dentKissRetLocals_get_ttl (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentKissRetLocals evm I out).get? "ttl" = none := by
  rw [dentKissRetLocals, store_get_ne _ _ (by decide)]
  exact dentKissLocals_get_ttl evm I out

theorem dentMoveTicLocals_get_tic (startEvm tickEvm : EVM.State) (I : ExecutionEnv) :
    (dentMoveTicLocals startEvm tickEvm I).get? "tic_" =
      some (.int (Int.ofNat (dentTicPostWord tickEvm I).toNat)) := by
  rw [dentMoveTicLocals, store_get_self]

theorem dentMoveTicLocals_get_id (startEvm tickEvm : EVM.State) (I : ExecutionEnv) :
    (dentMoveTicLocals startEvm tickEvm I).get? "id" = some (dentIdValue I) := by
  rw [dentMoveTicLocals, store_get_ne _ _ (by decide)]
  exact dentMoveLocals_get_id startEvm I

theorem dentMoveTicLocals_get_bids (startEvm tickEvm : EVM.State) (I : ExecutionEnv) :
    (dentMoveTicLocals startEvm tickEvm I).get? "bids" = none := by
  rw [dentMoveTicLocals, store_get_ne _ _ (by decide)]
  exact dentMoveLocals_get_bids startEvm I

theorem dentKissRetTicLocals_get_tic
    (startEvm tickEvm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentKissRetTicLocals startEvm tickEvm I out).get? "tic_" =
      some (.int (Int.ofNat (dentTicPostWord tickEvm I).toNat)) := by
  rw [dentKissRetTicLocals, store_get_self]

theorem dentKissRetTicWrappedLocals_get_tic
    (startEvm tickEvm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentKissRetTicWrappedLocals startEvm tickEvm I out).get? "tic_" =
      some (.int (Int.ofNat (dentTicWrappedNat tickEvm I))) := by
  rw [dentKissRetTicWrappedLocals, store_get_self]

theorem dentKissRetTicLocals_get_id
    (startEvm tickEvm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentKissRetTicLocals startEvm tickEvm I out).get? "id" = some (dentIdValue I) := by
  rw [dentKissRetTicLocals, store_get_ne _ _ (by decide)]
  exact dentKissRetLocals_get_id startEvm I out

theorem dentKissRetTicLocals_get_bids
    (startEvm tickEvm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (dentKissRetTicLocals startEvm tickEvm I out).get? "bids" = none := by
  rw [dentKissRetTicLocals, store_get_ne _ _ (by decide)]
  exact dentKissRetLocals_get_bids startEvm I out

theorem dentMoveTicWrappedLocals_get_tic
    (startEvm tickEvm : EVM.State) (I : ExecutionEnv) :
    (dentMoveTicWrappedLocals startEvm tickEvm I).get? "tic_" =
      some (.int (Int.ofNat
        (((dentNow48Word tickEvm).toNat +
          (dentTtlWord (dentAfterLotStore tickEvm I)).toNat) % 2 ^ 48))) := by
  rw [dentMoveTicWrappedLocals, store_get_self]

theorem evalExpr_dent_var_of_get
    {locals : Store} {name : Ident} {value : Value} (evm : EVM.State)
    (hget : locals.get? name = some value) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok value := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) = .ok value
  rw [hget]
  rfl

theorem evalExpr_dent_sender (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_dent_id (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm (.var "id") =
      .ok (dentIdValue I) := by
  exact evalExpr_auction_id evm (dentLocals I) (dentIdWord I)
    (by simpa [dentIdValue] using dentLocals_get_id I)

theorem evalExpr_dent_lot_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm (.var "lot") =
      .ok (dentLotValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((dentLocals I).get? "lot") = _
  rw [dentLocals_get_lot]
  rfl

theorem evalExpr_dent_bid_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm (.var "bid") =
      .ok (dentBidValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((dentLocals I).get? "bid") = _
  rw [dentLocals_get_bid]
  rfl

theorem evalExpr_dent_live_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm (.storage liveRef) =
      .ok (.int (Int.ofNat (dentLiveWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := dentLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := liveRef) (er := dentLiveEvaledRef)
    (t := .int uint256Int) (loc := wordLoc ⟨8⟩)
    (value := .int (Int.ofNat (dentLiveWord evm).toNat))
    (by simp [frame, liveRef])
    (by simp [frame, dentLiveEvaledRef, evalStorageRef, evalStorageRefSteps,
      liveRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [dentLiveWord, flopperSlotWord] using flopperStorageLocLoad_uint256 evm ⟨8⟩)

theorem evalExpr_dent_vat_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat (dentVatWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := dentLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := vatRef) (er := dentVatEvaledRef)
    (t := .address) (loc := addrLoc ⟨2⟩)
    (value := .address (AccountAddress.ofNat (dentVatWord evm).toNat))
    (by simp [frame, vatRef])
    (by simp [frame, dentVatEvaledRef, evalStorageRef, evalStorageRefSteps,
      vatRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      simpa [dentVatWord, flopperAddressReturnWord, flopperSlotWord] using
        flopperStorageLocLoad_address_offset0 evm ⟨2⟩)

theorem evalExpr_dent_beg_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm (.storage begRef) =
      .ok (.int (Int.ofNat (dentBegWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := dentLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := begRef) (er := dentBegEvaledRef)
    (t := .int uint256Int) (loc := wordLoc ⟨4⟩)
    (value := .int (Int.ofNat (dentBegWord evm).toNat))
    (by simp [frame, begRef])
    (by simp [frame, dentBegEvaledRef, evalStorageRef, evalStorageRefSteps,
      begRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [dentBegWord, flopperSlotWord] using flopperStorageLocLoad_uint256 evm ⟨4⟩)

theorem evalExpr_dent_ttl_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm (.storage ttlRef) =
      .ok (.int (Int.ofNat (dentTtlWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := dentLocals I }
  have hload :
      storageLocLoad evm (uint48Loc ⟨6⟩ ⟨0, by decide⟩ (by decide)) =
        .int (Int.ofNat (dentTtlWord evm).toNat) := by
    simpa [dentTtlWord, flopperUint48Offset0Word, flopperSlotWord] using
      flopperStorageLocLoad_uint48_offset0 evm ⟨6⟩
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := ttlRef) (er := dentTtlEvaledRef)
    (t := .int uint48Int) (loc := uint48Loc ⟨6⟩ ⟨0, by decide⟩ (by decide))
    (value := .int (Int.ofNat (dentTtlWord evm).toNat))
    (by simp [frame, ttlRef])
    (by simp [frame, dentTtlEvaledRef, evalStorageRef, evalStorageRefSteps,
      ttlRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, uint48St])
    (by rfl)
    hload

theorem evalExpr_dent_bid_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.storage (bidsF (.var "id") "bid")) =
      .ok (.int (Int.ofNat (dentBidStoredWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := dentLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "bid") (er := dentBidEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (auctionBidSlot (dentIdWord I)))
    (value := .int (Int.ofNat (dentBidStoredWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simpa [frame, dentBidEvaledRef] using
        evalStorageRef_auction_field evm (dentLocals I) (dentIdWord I) "bid"
          (by simpa [dentIdValue] using dentLocals_get_id I))
    (by simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
      BidStructTy, uint256St])
    (by rfl)
    (by simpa [dentBidStoredWord, flopperSlotWord] using
      flopperStorageLocLoad_uint256 evm (auctionBidSlot (dentIdWord I)))

theorem evalExpr_dent_lot_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.storage (bidsF (.var "id") "lot")) =
      .ok (.int (Int.ofNat (dentLotStoredWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := dentLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "lot") (er := dentLotEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (auctionLotSlot (dentIdWord I)))
    (value := .int (Int.ofNat (dentLotStoredWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simpa [frame, dentLotEvaledRef] using
        evalStorageRef_auction_field evm (dentLocals I) (dentIdWord I) "lot"
          (by simpa [dentIdValue] using dentLocals_get_id I))
    (by simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
      BidStructTy, uint256St])
    (by rfl)
    (by simpa [dentLotStoredWord, flopperSlotWord] using
      flopperStorageLocLoad_uint256 evm (auctionLotSlot (dentIdWord I)))

theorem evalExpr_dent_guy_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.storage (bidsF (.var "id") "guy")) =
      .ok (.address (AccountAddress.ofNat (dentGuyWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := dentLocals I }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "guy") (er := dentGuyEvaledRef I)
    (t := .address) (loc := addrLoc (auctionPackedSlot (dentIdWord I)))
    (value := .address (AccountAddress.ofNat (dentGuyWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simpa [frame, dentGuyEvaledRef] using
        evalStorageRef_auction_field evm (dentLocals I) (dentIdWord I) "guy"
          (by simpa [dentIdValue] using dentLocals_get_id I))
    (by simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
      BidStructTy, addrSt])
    (by rfl)
    (by
      simpa [dentGuyWord, flopperAddressReturnWord, flopperSlotWord] using
        flopperStorageLocLoad_address_offset0 evm (auctionPackedSlot (dentIdWord I)))

theorem evalExpr_dent_tic_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.storage (bidsF (.var "id") "tic")) =
      .ok (.int (Int.ofNat (dentTicWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := dentLocals I }
  have hload :
      storageLocLoad evm
          (uint48Loc (auctionPackedSlot (dentIdWord I)) ⟨20, by decide⟩ (by decide)) =
        .int (Int.ofNat (dentTicWord evm I).toNat) := by
    rw [flopperStorageLocLoad_uint48_offset20]
    rw [u256_land_comm
      (UInt256.div
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (auctionPackedSlot (dentIdWord I)))
        (UInt256.ofNat (256 ^ 20)))
      flopperUint48Mask]
    rfl
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "tic") (er := dentTicEvaledRef I)
    (t := .int uint48Int)
    (loc := uint48Loc (auctionPackedSlot (dentIdWord I)) ⟨20, by decide⟩ (by decide))
    (value := .int (Int.ofNat (dentTicWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simpa [frame, dentTicEvaledRef] using
        evalStorageRef_auction_field evm (dentLocals I) (dentIdWord I) "tic"
          (by simpa [dentIdValue] using dentLocals_get_id I))
    (by simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
      BidStructTy, uint48St])
    (by rfl)
    hload

theorem evalExpr_dent_end_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
        (.storage (bidsF (.var "id") "end")) =
      .ok (.int (Int.ofNat (dentEndWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := dentLocals I }
  have hload :
      storageLocLoad evm
          (uint48Loc (auctionPackedSlot (dentIdWord I)) ⟨26, by decide⟩ (by decide)) =
        .int (Int.ofNat (dentEndWord evm I).toNat) := by
    rw [flopperStorageLocLoad_uint48_offset26]
    rw [u256_land_comm
      (UInt256.div
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (auctionPackedSlot (dentIdWord I)))
        (UInt256.ofNat (256 ^ 26)))
      flopperUint48Mask]
    rfl
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "end") (er := dentEndEvaledRef I)
    (t := .int uint48Int)
    (loc := uint48Loc (auctionPackedSlot (dentIdWord I)) ⟨26, by decide⟩ (by decide))
    (value := .int (Int.ofNat (dentEndWord evm I).toNat))
    (by simp [frame, bidsF])
    (by
      simpa [frame, dentEndEvaledRef] using
        evalStorageRef_auction_field evm (dentLocals I) (dentIdWord I) "end"
          (by simpa [dentIdValue] using dentLocals_get_id I))
    (by simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
      BidStructTy, uint48St])
    (by rfl)
    hload

theorem evalExpr_dent_vat_storage_of_locals
    (evm : EVM.State) (I : ExecutionEnv) (locals : Store)
    (hvat : "vat" ∉ locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat (dentVatWord evm).toNat)) := by
  let frame : Frame := { contract := contract, locals := locals }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := vatRef) (er := dentVatEvaledRef)
    (t := .address) (loc := addrLoc ⟨2⟩)
    (value := .address (AccountAddress.ofNat (dentVatWord evm).toNat))
    (by simpa [frame, vatRef] using hvat)
    (by simp [frame, dentVatEvaledRef, evalStorageRef, evalStorageRefSteps,
      vatRef, EvalResult.bind, bind, pure])
    (by simp [frame, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      simpa [dentVatWord, flopperAddressReturnWord, flopperSlotWord] using
        flopperStorageLocLoad_address_offset0 evm ⟨2⟩)

theorem evalExpr_dent_guy_storage_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (dentIdValue I))
    (hbids : "bids" ∉ locals) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.storage (bidsF (.var "id") "guy")) =
      .ok (.address (AccountAddress.ofNat (dentGuyWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := locals }
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "guy") (er := dentGuyEvaledRef I)
    (t := .address) (loc := addrLoc (auctionPackedSlot (dentIdWord I)))
    (value := .address (AccountAddress.ofNat (dentGuyWord evm I).toNat))
    (by simpa [frame, bidsF] using hbids)
    (by
      simpa [frame, dentGuyEvaledRef, dentIdValue] using
        evalStorageRef_auction_field evm locals (dentIdWord I) "guy" hid)
    (by simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
      BidStructTy, addrSt])
    (by rfl)
    (by
      simpa [dentGuyWord, flopperAddressReturnWord, flopperSlotWord] using
        flopperStorageLocLoad_address_offset0 evm (auctionPackedSlot (dentIdWord I)))

theorem evalExpr_dent_tic_storage_of_locals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store}
    (hid : locals.get? "id" = some (dentIdValue I))
    (hbids : "bids" ∉ locals) :
    evalExpr? config { contract := contract, locals := locals } evm
        (.storage (bidsF (.var "id") "tic")) =
      .ok (.int (Int.ofNat (dentTicWord evm I).toNat)) := by
  let frame : Frame := { contract := contract, locals := locals }
  have hload :
      storageLocLoad evm
          (uint48Loc (auctionPackedSlot (dentIdWord I)) ⟨20, by decide⟩ (by decide)) =
        .int (Int.ofNat (dentTicWord evm I).toNat) := by
    rw [flopperStorageLocLoad_uint48_offset20]
    rw [u256_land_comm
      (UInt256.div
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (auctionPackedSlot (dentIdWord I)))
        (UInt256.ofNat (256 ^ 20)))
      flopperUint48Mask]
    rfl
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := frame) (evm := evm)
    (slot := bidsF (.var "id") "tic") (er := dentTicEvaledRef I)
    (t := .int uint48Int)
    (loc := uint48Loc (auctionPackedSlot (dentIdWord I)) ⟨20, by decide⟩ (by decide))
    (value := .int (Int.ofNat (dentTicWord evm I).toNat))
    (by simpa [frame, bidsF] using hbids)
    (by
      simpa [frame, dentTicEvaledRef, dentIdValue] using
        evalStorageRef_auction_field evm locals (dentIdWord I) "tic" hid)
    (by simp [frame, auctionIdKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
      BidStructTy, uint48St])
    (by rfl)
    hload

theorem evalExprs_dent_move_args_lotOneLocals (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := dentLotOneLocals evm I } evm
        [sender, .storage (bidsF (.var "id") "guy"), .var "bid"] =
      .ok [.address evm.executionEnv.source,
        .address (AccountAddress.ofNat (dentGuyWord evm I).toNat),
        .int (Int.ofNat (dentBidWord I).toNat)] := by
  have hsender := evalExpr_dent_sender evm (dentLotOneLocals evm I)
  have hguy := evalExpr_dent_guy_storage_of_locals evm I
    (locals := dentLotOneLocals evm I) (dentLotOneLocals_get_id evm I)
    (by simp [dentLotOneLocals, dentBegLotLocals, dentLocals])
  have hbid := evalExpr_dent_var_of_get evm (dentLotOneLocals_get_bid evm I)
  simp only [evalExprs?, hsender, hguy, hbid, EvalResult.bind, bind, pure]

theorem evalExprs_dent_ash_args (evm : EVM.State) (I : ExecutionEnv) (locals : Store) :
    evalExprs? config { contract := contract, locals := locals } evm [] = .ok [] := by
  rfl

theorem evalExprs_dent_min_args
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExprs? config { contract := contract, locals := dentAshLocals evm I out } evm
        [.var "bid", .var "Ash"] =
      .ok [.int (Int.ofNat (dentBidWord I).toNat),
        .int (Int.ofNat (dentAshWord out).toNat)] := by
  have hbid := evalExpr_dent_var_of_get evm (dentAshLocals_get_bid evm I out)
  have hash := evalExpr_dent_var_of_get evm (dentAshLocals_get_Ash evm I out)
  simp only [evalExprs?, hbid, hash, EvalResult.bind, bind, pure, dentBidValue]

theorem evalExprs_dent_min_args_of_locals
    (localsEvm runEvm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExprs? config { contract := contract, locals := dentAshLocals localsEvm I out } runEvm
        [.var "bid", .var "Ash"] =
      .ok [.int (Int.ofNat (dentBidWord I).toNat),
        .int (Int.ofNat (dentAshWord out).toNat)] := by
  have hbid := evalExpr_dent_var_of_get runEvm (dentAshLocals_get_bid localsEvm I out)
  have hash := evalExpr_dent_var_of_get runEvm (dentAshLocals_get_Ash localsEvm I out)
  simp only [evalExprs?, hbid, hash, EvalResult.bind, bind, pure, dentBidValue]

theorem evalExprs_dent_kiss_args
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExprs? config { contract := contract, locals := dentKissLocals evm I out } evm
        [.var "kissAmt"] =
      .ok [.int (Int.ofNat (dentKissAmtWord I out).toNat)] := by
  have hkiss := evalExpr_dent_var_of_get evm (dentKissLocals_get_kissAmt evm I out)
  simp only [evalExprs?, hkiss, EvalResult.bind, bind, pure]

theorem evalExprs_dent_kiss_args_of_locals
    (localsEvm runEvm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExprs? config { contract := contract, locals := dentKissLocals localsEvm I out } runEvm
        [.var "kissAmt"] =
      .ok [.int (Int.ofNat (dentKissAmtWord I out).toNat)] := by
  have hkiss := evalExpr_dent_var_of_get runEvm
    (dentKissLocals_get_kissAmt localsEvm I out)
  simp only [evalExprs?, hkiss, EvalResult.bind, bind, pure]

theorem dentMin_bindParams (x y : UInt256) :
    bindParams? minFunction.params
        [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] =
      some (dentMinLocals x y) := by
  simp [minFunction, dentMinLocals, uint256, bindParams?]

theorem evalExpr_dent_min_gt_false (evm : EVM.State) (x y : UInt256)
    (hle : x.toNat ≤ y.toNat) :
    evalExpr? config { contract := contract, locals := dentMinLocals x y } evm
        (.binary .gt (.var "x") (.var "y")) =
      .ok (.bool false) := by
  have hx := evalExpr_dent_var_of_get evm (dentMinLocals_get_x x y)
  have hy := evalExpr_dent_var_of_get evm (dentMinLocals_get_y x y)
  simp only [evalExpr?, hx, hy, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hnot : ¬ Int.ofNat x.toNat > Int.ofNat y.toNat :=
    not_lt_of_ge (Int.ofNat_le.mpr hle)
  simp [hnot, hle]

theorem evalExpr_dent_min_gt_true (evm : EVM.State) (x y : UInt256)
    (hlt : y.toNat < x.toNat) :
    evalExpr? config { contract := contract, locals := dentMinLocals x y } evm
        (.binary .gt (.var "x") (.var "y")) =
      .ok (.bool true) := by
  have hx := evalExpr_dent_var_of_get evm (dentMinLocals_get_x x y)
  have hy := evalExpr_dent_var_of_get evm (dentMinLocals_get_y x y)
  simp only [evalExpr?, hx, hy, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hgt : Int.ofNat x.toNat > Int.ofNat y.toNat := Int.ofNat_lt.mpr hlt
  simp [hgt, hlt]

theorem evalExprs_dent_min_return_x (evm : EVM.State) (x y : UInt256) :
    evalExprs? config { contract := contract, locals := dentMinLocals x y } evm
        [.var "x"] =
      .ok [.int (Int.ofNat x.toNat)] := by
  have hx := evalExpr_dent_var_of_get evm (dentMinLocals_get_x x y)
  simpa [evalExprs?, hx, EvalResult.bind, bind, pure]

theorem evalExprs_dent_min_return_y (evm : EVM.State) (x y : UInt256) :
    evalExprs? config { contract := contract, locals := dentMinLocals x y } evm
        [.var "y"] =
      .ok [.int (Int.ofNat y.toNat)] := by
  have hy := evalExpr_dent_var_of_get evm (dentMinLocals_get_y x y)
  simpa [evalExprs?, hy, EvalResult.bind, bind, pure]

theorem dentMinFunctionBody (evm : EVM.State) (x y : UInt256) :
    ExecFuncBody config { contract := contract, locals := dentMinLocals x y } evm
        minFunction.body
      (.returned { contract := contract, locals := dentMinLocals x y } evm
        (some [.int (Int.ofNat (if x.toNat ≤ y.toNat then x else y).toNat)])) := by
  by_cases hle : x.toNat ≤ y.toNat
  · have hcond := evalExpr_dent_min_gt_false evm x y hle
    have hret := evalExprs_dent_min_return_x evm x y
    refine ExecFuncBody.execBlockRet ?_
    simpa [minFunction, hle] using
      (ExecBlock.consReturn
        (ExecStmt.iteFalse hcond
          (ExecBlock.consReturn (ExecStmt.return hret))))
  · have hlt : y.toNat < x.toNat := Nat.lt_of_not_ge hle
    have hcond := evalExpr_dent_min_gt_true evm x y hlt
    have hret := evalExprs_dent_min_return_y evm x y
    refine ExecFuncBody.execBlockRet ?_
    simpa [minFunction, hle] using
      (ExecBlock.consReturn
        (ExecStmt.iteTrue hcond
          (ExecBlock.consReturn (ExecStmt.return hret))))

theorem flopperDentBodyMinCallSuccess
    (localsEvm runEvm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    ExecStmt config { contract := contract, locals := dentAshLocals localsEvm I out } runEvm
      (.internalCall "min" [.var "bid", .var "Ash"] "kissAmt")
      (.ok { contract := contract, locals := dentKissLocals localsEvm I out } runEvm) := by
  have hargs := evalExprs_dent_min_args_of_locals localsEvm runEvm I out
  have hlookup : lookupCallable? contract "min" = some minFunction.toCallable := by
    simp [contract, functions, minFunction, add48Function, mulFunction, lookupCallable?,
      lookupFunction?]
  have hbind := dentMin_bindParams (dentBidWord I) (dentAshWord out)
  have hbody := dentMinFunctionBody runEvm (dentBidWord I) (dentAshWord out)
  have hstmt :=
    internalCallFunctionReturn
      (cfg := config)
      (caller := { contract := contract, locals := dentAshLocals localsEvm I out })
      (evm := runEvm)
      (name := "min")
      (retVar := "kissAmt")
      (args := [.var "bid", .var "Ash"])
      (callee := minFunction)
      hargs hlookup hbind hbody
  simpa only [dentKissLocals, dentKissAmtWord, resumeAfterInternalCall, collapseReturns] using
    hstmt

theorem dentMoveDecode_ok (out : ByteArray) :
    config.externalABI.decode? "move" out = some [] := by
  simp [config, externalABI, decodeVoid?]

theorem dentKissDecode_ok (out : ByteArray) :
    config.externalABI.decode? "kiss" out = some [] := by
  simp [config, externalABI, decodeVoid?]

theorem dentAshDecode_ok {out : ByteArray} (ho32 : 32 ≤ out.size) :
    config.externalABI.decode? "Ash" out =
      some [.int (Int.ofNat (dentAshWord out).toNat)] := by
  have hdec := decodeReturnValueWithMode_legacy_uint256_ok (returndata := out) ho32
  have hlt := fromByteArrayBigEndian_extract0_32_lt (returndata := out) ho32
  have hdec' :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 out =
        some (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) := by
    simpa [uint256, uint256Int, abiUInt256] using hdec
  change decodeReturn? uint256 out =
    some [.int (Int.ofNat (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))).toNat)]
  unfold decodeReturn?
  rw [hdec']
  simp [UInt256.toNat_ofNat_of_lt hlt, Int.ofNat_eq_natCast]

theorem dentAshDecode_none_short {out : ByteArray} (hshort : out.size < 32) :
    config.externalABI.decode? "Ash" out = none := by
  have hdec := decodeReturnValueWithMode_legacy_uint256_none_short
    (returndata := out) hshort
  have hdec' :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 out = none := by
    simpa [uint256, uint256Int, abiUInt256] using hdec
  change decodeReturn? uint256 out = none
  unfold decodeReturn?
  rw [hdec']
  rfl

theorem flopperDentBodyAfterAshSuccessKissNoCode
    (localsEvm evmAsh : EVM.State) (I : ExecutionEnv) (outAsh : ByteArray)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord evmAsh.accountMap (dentGuyWord evmAsh I) =
        ⟨0⟩) :
    ExecBlock config { contract := contract, locals := dentAshLocals localsEvm I outAsh } evmAsh
      ([ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
        checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
          (.intLit 0) [.var "kissAmt"] "_kissRet")
      .reverted := by
  have hminStmt := flopperDentBodyMinCallSuccess localsEvm evmAsh I outAsh
  have hmin :
      ExecBlock config { contract := contract, locals := dentAshLocals localsEvm I outAsh }
          evmAsh
        [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ]
        (.ok { contract := contract, locals := dentKissLocals localsEvm I outAsh } evmAsh) :=
    ExecBlock.consNormal hminStmt ExecBlock.nil
  have htarget :
      evalExpr? config { contract := contract, locals := dentKissLocals localsEvm I outAsh }
          evmAsh (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat (dentGuyWord evmAsh I).toNat)) :=
    evalExpr_dent_guy_storage_of_locals evmAsh I
      (dentKissLocals_get_id localsEvm I outAsh)
      (dentKissLocals_not_mem_bids localsEvm I outAsh)
  have hnoCodeLookup :
      (UInt256.ofNat
        ((evmAsh.lookupAccount (AccountAddress.ofNat (dentGuyWord evmAsh I).toNat)).option
          0 (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_zero_lookup_code_zero
        (σ := evmAsh.accountMap)
        (target := dentGuyWord evmAsh I)
        (addr := AccountAddress.ofNat (dentGuyWord evmAsh I).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hnoCode
  have hguard :
      evalExpr? config { contract := contract, locals := dentKissLocals localsEvm I outAsh }
          evmAsh
        (.binary .gt (.extCodeSize (.storage (bidsF (.var "id") "guy"))) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_yank_extCodeGuard_false htarget hnoCodeLookup
  have hkiss :
      ExecBlock config { contract := contract, locals := dentKissLocals localsEvm I outAsh }
          evmAsh
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
          (.intLit 0) [.var "kissAmt"] "_kissRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode hguard
  simpa [List.cons_append, List.nil_append] using
    Reasoning.Refinement.execBlock_append hmin hkiss

theorem flopperDentBodyAfterAshSuccessKissCallFailure
    (localsEvm evmAsh evmKiss : EVM.State) (I : ExecutionEnv)
    (outAsh outKiss : ByteArray)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evmAsh.accountMap (dentGuyWord evmAsh I) ≠
        ⟨0⟩)
    (hcall :
      typedCallViaEVM config evmAsh
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmAsh I).toNat)) "kiss" 0
        [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (false, evmKiss, outKiss) true) :
    ExecBlock config { contract := contract, locals := dentAshLocals localsEvm I outAsh } evmAsh
      ([ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
        checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
          (.intLit 0) [.var "kissAmt"] "_kissRet")
      .reverted := by
  have hminStmt := flopperDentBodyMinCallSuccess localsEvm evmAsh I outAsh
  have hmin :
      ExecBlock config { contract := contract, locals := dentAshLocals localsEvm I outAsh }
          evmAsh
        [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ]
        (.ok { contract := contract, locals := dentKissLocals localsEvm I outAsh } evmAsh) :=
    ExecBlock.consNormal hminStmt ExecBlock.nil
  have htarget :
      evalExpr? config { contract := contract, locals := dentKissLocals localsEvm I outAsh }
          evmAsh (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat (dentGuyWord evmAsh I).toNat)) :=
    evalExpr_dent_guy_storage_of_locals evmAsh I
      (dentKissLocals_get_id localsEvm I outAsh)
      (dentKissLocals_not_mem_bids localsEvm I outAsh)
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (AccountAddress.ofNat (dentGuyWord evmAsh I).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmAsh.accountMap)
        (target := dentGuyWord evmAsh I)
        (addr := AccountAddress.ofNat (dentGuyWord evmAsh I).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := dentKissLocals localsEvm I outAsh }
          evmAsh
        (.binary .gt (.extCodeSize (.storage (bidsF (.var "id") "guy"))) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true htarget hcodeLookup
  have hargs := evalExprs_dent_kiss_args_of_locals localsEvm evmAsh I outAsh
  have hkiss :
      ExecBlock config { contract := contract, locals := dentKissLocals localsEvm I outAsh }
          evmAsh
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
          (.intLit 0) [.var "kissAmt"] "_kissRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure hguard htarget hargs hcall
  simpa [List.cons_append, List.nil_append] using
    Reasoning.Refinement.execBlock_append hmin hkiss

theorem flopperDentBodyAfterAshSuccessKissCallSuccess
    (localsEvm evmAsh evmKiss : EVM.State) (I : ExecutionEnv)
    (outAsh outKiss : ByteArray)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evmAsh.accountMap (dentGuyWord evmAsh I) ≠
        ⟨0⟩)
    (hcall :
      typedCallViaEVM config evmAsh
        (EVM.address (AccountAddress.ofNat (dentGuyWord evmAsh I).toNat)) "kiss" 0
        [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (true, evmKiss, outKiss) true) :
    ExecBlock config { contract := contract, locals := dentAshLocals localsEvm I outAsh } evmAsh
      ([ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ] ++
        checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
          (.intLit 0) [.var "kissAmt"] "_kissRet")
      (.ok { contract := contract, locals := dentKissRetLocals localsEvm I outAsh } evmKiss) := by
  have hminStmt := flopperDentBodyMinCallSuccess localsEvm evmAsh I outAsh
  have hmin :
      ExecBlock config { contract := contract, locals := dentAshLocals localsEvm I outAsh }
          evmAsh
        [ .internalCall "min" [.var "bid", .var "Ash"] "kissAmt" ]
        (.ok { contract := contract, locals := dentKissLocals localsEvm I outAsh } evmAsh) :=
    ExecBlock.consNormal hminStmt ExecBlock.nil
  have htarget :
      evalExpr? config { contract := contract, locals := dentKissLocals localsEvm I outAsh }
          evmAsh (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat (dentGuyWord evmAsh I).toNat)) :=
    evalExpr_dent_guy_storage_of_locals evmAsh I
      (dentKissLocals_get_id localsEvm I outAsh)
      (dentKissLocals_not_mem_bids localsEvm I outAsh)
  have hcodeLookup :
      0 < (UInt256.ofNat
        ((evmAsh.lookupAccount (AccountAddress.ofNat (dentGuyWord evmAsh I).toNat)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      flopperExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmAsh.accountMap)
        (target := dentGuyWord evmAsh I)
        (addr := AccountAddress.ofNat (dentGuyWord evmAsh I).toNat)
        (by rw [accountAddress_ofUInt256_eq_ofNat_toNat])
        hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := dentKissLocals localsEvm I outAsh }
          evmAsh
        (.binary .gt (.extCodeSize (.storage (bidsF (.var "id") "guy"))) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_yank_extCodeGuard_true htarget hcodeLookup
  have hargs := evalExprs_dent_kiss_args_of_locals localsEvm evmAsh I outAsh
  have hkiss :
      ExecBlock config { contract := contract, locals := dentKissLocals localsEvm I outAsh }
          evmAsh
        (checkedExternalCallStmts (.storage (bidsF (.var "id") "guy")) "kiss"
          (.intLit 0) [.var "kissAmt"] "_kissRet")
        (.ok { contract := contract, locals := dentKissRetLocals localsEvm I outAsh }
          evmKiss) := by
    simpa [checkedExternalCallStmts, dentKissRetLocals] using
      checkedExternalCallSuccess hguard htarget hargs hcall (dentKissDecode_ok outKiss)
  simpa [List.cons_append, List.nil_append] using
    Reasoning.Refinement.execBlock_append hmin hkiss

theorem evalExpr_dent_live_one_true (evm : EVM.State) (I : ExecutionEnv)
    (hlive : dentLiveWord evm = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hstorage : evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.storage liveRef) = .ok (.int 1) := by
    simpa [hlive] using evalExpr_dent_live_storage evm I
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_dent_live_one_false (evm : EVM.State) (I : ExecutionEnv)
    (hlive : dentLiveWord evm ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  have hstorage := evalExpr_dent_live_storage evm I
  have hne :
      Value.int (Int.ofNat (dentLiveWord evm).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hlive
    apply u256_inj
    exact Int.ofNat.inj hbad
  have hbeq :
      (Value.int (Int.ofNat (dentLiveWord evm).toNat) == Value.int 1) = false :=
    beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_dent_guy_ne_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hguy : dentGuyWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) = .ok (.bool false) := by
  let frame : Frame := { contract := contract, locals := dentLocals I }
  have hguyEval :
      evalExpr? config frame evm (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat (dentGuyWord evm I).toNat)) := by
    simpa [frame] using evalExpr_dent_guy_storage evm I
  have hzero :
      evalExpr? config frame evm zeroAddr = .ok (.address (AccountAddress.ofNat 0)) := by
    simp only [zeroAddr, evalExpr?, pure, EvalResult.bind, bind]
    unfold castValue? addrSt
    norm_num
    rfl
  change evalExpr? config frame evm
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) = .ok (.bool false)
  simp only [evalExpr?, hguyEval, hzero, EvalResult.bind, bind]
  rw [hguy]
  simp [zeroAddr, evalBinaryOp?]

theorem evalExpr_dent_guy_ne_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hguy : dentGuyWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) = .ok (.bool true) := by
  let frame : Frame := { contract := contract, locals := dentLocals I }
  let guyWord := dentGuyWord evm I
  have hguyEval :
      evalExpr? config frame evm (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat guyWord.toNat)) := by
    simpa [frame, guyWord] using evalExpr_dent_guy_storage evm I
  have hzero :
      evalExpr? config frame evm zeroAddr = .ok (.address (AccountAddress.ofNat 0)) := by
    simp only [zeroAddr, evalExpr?, pure, EvalResult.bind, bind]
    unfold castValue? addrSt
    norm_num
    rfl
  have haddrNe : AccountAddress.ofNat guyWord.toNat ≠ AccountAddress.ofNat 0 := by
    exact flopperAddressOfNat_ne_zero_of_word_ne_zero
      (by
        simpa [guyWord, dentGuyWord, flopperAddressReturnWord] using
          solcAddrMask_result_canonical
            (flopperSlotWord (auctionPackedSlot (dentIdWord I)) evm.accountMap
              evm.executionEnv))
      (by simpa [guyWord] using hguy)
  have hne :
      Value.address (AccountAddress.ofNat guyWord.toNat) ≠
        Value.address (AccountAddress.ofNat 0) := by
    intro hbad
    injection hbad with haddr
    exact haddrNe haddr
  have hbeq :
      (Value.address (AccountAddress.ofNat guyWord.toNat) ==
        Value.address (AccountAddress.ofNat 0)) = false :=
    beq_eq_false_iff_ne.mpr hne
  change evalExpr? config frame evm
      (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) = .ok (.bool true)
  simp only [evalExpr?, hguyEval, hzero, EvalResult.bind, bind]
  simp only [evalBinaryOp?]
  rw [hbeq]
  rfl

theorem evalExpr_dent_tic_gt_timestamp_true (evm : EVM.State) (I : ExecutionEnv)
    (hgt : (dentTimestampWord evm).toNat < (dentTicWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := dentLocals I } evm
      (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp)) =
        .ok (.bool true) := by
  have hticEval := evalExpr_dent_tic_storage evm I
  simp only [evalExpr?, hticEval, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  simpa [dentTimestampWord] using hgt

end Benchmarks.Dss.Flopper
