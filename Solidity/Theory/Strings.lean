import Solidity.Theory.Body

/-!
# `string`/`bytes` storage on the solc layout

`readBytesStorage`/`writeBytesStorage`/`clearBytesStorage` go through the layout's hooks; on a
`solidityStorageLayout` these are solc's short/long byte-array representation.  Each lemma names
the header slot (`hbase`), its current word (`hload`) and the header's shape, and states the exact
storage the operation produces.  The deep read/write of a `string`-typed reference reduce to them.
-/

namespace Solidity

open Ethereum Storage Reasoning.Theory

variable {cfg : Config} {layout : Solm.EvaledStorageRef → EVM.State → Option Storage.StorageLoc}
  {evm : EVM.State} {er : Solm.EvaledStorageRef} {baseSlot header len : UInt256}

/-! ## Clearing (`delete s`) -/

theorem clearBytesStorage_shortZero (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase : ∃ loc, layout (lengthRef er) evm = some loc ∧ loc.slot = baseSlot)
    (hload : Storage.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    clearBytesStorage cfg evm er .string =
      some (.ok (Storage.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩)) := by
  have hdecode : solidityDecodeBytesLengthHeader (⟨0⟩ : UInt256) = .ok 0 := solidityDecodeBytesLengthHeader_zero
  have hslot := solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [clearBytesStorage, liftRead, hcfg, solidityStorageLayout, solidityClearValue?, solidityPrepareBytesWrite?,
    hslot, checkBytesPacked, hload, solidityBytesHeaderWord]
  rw [show UInt256.ofNat 0 = ({ val := 0 } : UInt256) by native_decide]

theorem clearBytesStorage_shortPacked (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase : ∃ loc, layout (lengthRef er) evm = some loc ∧ loc.slot = baseSlot)
    (hload : Storage.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    clearBytesStorage cfg evm er .string =
      some (.ok (Storage.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot := solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [clearBytesStorage, liftRead, hcfg, solidityStorageLayout, solidityClearValue?, solidityPrepareBytesWrite?,
    hslot, hpacked, solidityBytesHeaderWord]
  rw [show UInt256.ofNat 0 = ({ val := 0 } : UInt256) by native_decide]

theorem clearBytesStorage_longPrepared (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase : ∃ loc, layout (lengthRef er) evm = some loc ∧ loc.slot = baseSlot)
    (hload : Storage.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    clearBytesStorage cfg evm er .string =
      some (.ok (clearSolidityBytesDataWordsFrom
        (Storage.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) baseSlot 0 ((len.toNat + 31) / 32))) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot := solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  have hpacked : checkBytesPacked baseSlot evm = false := checkBytesPacked_of_storageLoad_land_one_ne_zero hload hflag
  simp [clearBytesStorage, liftRead, hcfg, solidityStorageLayout, solidityClearValue?, solidityPrepareBytesWrite?,
    hslot, hpacked, solidityBytesHeaderWord]
  rw [show UInt256.ofNat 0 = ({ val := 0 } : UInt256) by native_decide]

/-! ## Writing -/

theorem writeBytesStorage_shortPacked {value : ByteArray} (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase : ∃ loc, layout (lengthRef er) evm = some loc ∧ loc.slot = baseSlot)
    (hvalueSize : value.size < 32)
    (hload : Storage.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeBytesStorage cfg evm er .string value =
      some (.ok (Storage.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot (solidityShortBytesWord value))) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot := solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [writeBytesStorage, liftRead, hcfg, solidityStorageLayout, solidityWriteValue?, solidityWriteBytesValue?,
    hslot, hpacked, hvalueSize]

theorem writeBytesStorage_shortFromLongPrepared {value : ByteArray} (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase : ∃ loc, layout (lengthRef er) evm = some loc ∧ loc.slot = baseSlot)
    (hvalueSize : value.size < 32)
    (hload : Storage.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeBytesStorage cfg evm er .string value =
      some (.ok (Storage.EVM.storageStore
        (clearSolidityBytesDataWordsFrom evm baseSlot 0 ((len.toNat + 31) / 32))
        (clearSolidityBytesDataWordsFrom evm baseSlot 0 ((len.toNat + 31) / 32)).executionEnv.codeOwner
        baseSlot (solidityShortBytesWord value))) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot := solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  have hpacked : checkBytesPacked baseSlot evm = false := checkBytesPacked_of_storageLoad_land_one_ne_zero hload hflag
  simp [writeBytesStorage, liftRead, hcfg, solidityStorageLayout, solidityWriteValue?, solidityWriteBytesValue?,
    hslot, hpacked, hvalueSize, solidityBytesDataWordCount]

theorem writeBytesStorage_longPacked {value : ByteArray} (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase : ∃ loc, layout (lengthRef er) evm = some loc ∧ loc.slot = baseSlot)
    (hvalueSize : ¬ value.size < 32)
    (hload : Storage.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeBytesStorage cfg evm er .string value =
      some (.ok (Storage.EVM.storageStore
        (writeSolidityBytesDataWordsFrom evm baseSlot value 0 (solidityBytesDataWordCount value.size))
        (writeSolidityBytesDataWordsFrom evm baseSlot value 0 (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
        baseSlot (solidityBytesHeaderWord value.size))) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot := solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [writeBytesStorage, liftRead, hcfg, solidityStorageLayout, solidityWriteValue?, solidityWriteBytesValue?,
    hslot, hpacked, hvalueSize, solidityBytesDataWordCount]

theorem writeBytesStorage_longFromLongPrepared {value : ByteArray} (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase : ∃ loc, layout (lengthRef er) evm = some loc ∧ loc.slot = baseSlot)
    (hvalueSize : ¬ value.size < 32)
    (hload : Storage.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeBytesStorage cfg evm er .string value =
      some (.ok (Storage.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom evm baseSlot (solidityBytesDataWordCount value.size)
            (solidityBytesDataWordCount len.toNat - solidityBytesDataWordCount value.size))
          baseSlot value 0 (solidityBytesDataWordCount value.size))
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom evm baseSlot (solidityBytesDataWordCount value.size)
            (solidityBytesDataWordCount len.toNat - solidityBytesDataWordCount value.size))
          baseSlot value 0 (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
        baseSlot (solidityBytesHeaderWord value.size))) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot := solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  have hpacked : checkBytesPacked baseSlot evm = false := checkBytesPacked_of_storageLoad_land_one_ne_zero hload hflag
  simp [writeBytesStorage, liftRead, hcfg, solidityStorageLayout, solidityWriteValue?, solidityWriteBytesValue?,
    hslot, hpacked, hvalueSize, solidityBytesDataWordCount]

/-- A malformed long header: `Panic(0x22)`. -/
theorem writeBytesStorage_malformedLong {value : ByteArray} (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase : ∃ loc, layout (lengthRef er) evm = some loc ∧ loc.slot = baseSlot)
    (hload : Storage.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    writeBytesStorage cfg evm er .string value = some (.error .storageBytes) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .revert := by
    simp [solidityDecodeBytesLengthHeader, hflag, hbad]
  have hslot := solidityBytesBaseSlotAndLength?_revert_of_layout hbase hload hdecode
  simp [writeBytesStorage, liftRead, hcfg, solidityStorageLayout, solidityWriteValue?, solidityWriteBytesValue?, hslot]
  rfl

theorem writeBytesStorage_malformedShort {value : ByteArray} (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase : ∃ loc, layout (lengthRef er) evm = some loc ∧ loc.slot = baseSlot)
    (hload : Storage.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    writeBytesStorage cfg evm er .string value = some (.error .storageBytes) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .revert := by
    have hbad0 : UInt256.sub ⟨0⟩ (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
      simpa [hflag] using hbad
    simp [solidityDecodeBytesLengthHeader, hflag, hbad0]
  have hslot := solidityBytesBaseSlotAndLength?_revert_of_layout hbase hload hdecode
  simp [writeBytesStorage, liftRead, hcfg, solidityStorageLayout, solidityWriteValue?, solidityWriteBytesValue?, hslot]
  rfl

theorem writeBytesStorage_emptyFromZero (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase : ∃ loc, layout (lengthRef er) evm = some loc ∧ loc.slot = baseSlot)
    (hload : Storage.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    writeBytesStorage cfg evm er .string ByteArray.empty =
      some (.ok (Storage.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩)) := by
  have hdecode : solidityDecodeBytesLengthHeader (⟨0⟩ : UInt256) = .ok 0 := solidityDecodeBytesLengthHeader_zero
  have hslot := solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [writeBytesStorage, liftRead, hcfg, solidityStorageLayout, solidityWriteValue?, solidityWriteBytesValue?,
    solidityShortBytesWord, hslot, checkBytesPacked, hload]
  rw [empty_readWithPadding_word_zero]
  rfl

/-! ## Reading -/

theorem readBytesStorage_shortPacked (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase : ∃ loc, layout (lengthRef er) evm = some loc ∧ loc.slot = baseSlot)
    (hload : Storage.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    readBytesStorage cfg evm er .string = some (.ok (header.toByteArray.extract 0 len.toNat)) := by
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := solidityShortBytesValid_lt32 hvalid0
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot := solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [readBytesStorage, liftRead, hcfg, solidityStorageLayout, solidityReadValue?, solidityReadBytesValue?,
    hslot, hload, hlt32]

theorem readBytesStorage_long (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase : ∃ loc, layout (lengthRef er) evm = some loc ∧ loc.slot = baseSlot)
    (hload : Storage.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    readBytesStorage cfg evm er .string =
      some (.ok (if len.toNat < 32 then header.toByteArray.extract 0 len.toNat
        else (readSolidityBytesDataWordsFrom evm baseSlot 0 (solidityBytesDataWordCount len.toNat)).extract 0 len.toNat)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot := solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [readBytesStorage, liftRead, hcfg, solidityStorageLayout, solidityReadValue?, solidityReadBytesValue?, hslot, hload]
  by_cases hlt : len.toNat < 32 <;> simp [hlt]

/-! ## Deep reads and writes of a `string` -/

theorem readStorageDeep_string {env : TypeEnv} {h : Heap} {data : ByteArray} (fuel : ℕ)
    (hr : readBytesStorage cfg evm er .string = some (.ok data)) :
    readStorageDeep cfg env (fuel + 1) evm h er .string =
      some (.ok (.memRef (h.alloc (.bytes true data)).2, (h.alloc (.bytes true data)).1)) := by
  rw [readStorageDeep]
  · simp [storageTyOf, hr]
  all_goals intros; simp_all

theorem writeStorageDeep_string_memRef {env : TypeEnv} {h : Heap} {id : ℕ} {isStr : Bool} {d : ByteArray}
    {evm' : EVM.State} (fuel : ℕ) (hget : h.get? id = some (.bytes isStr d))
    (hw : writeBytesStorage cfg evm er .string d = some (.ok evm')) :
    writeStorageDeep cfg env (fuel + 1) evm h er .string (.memRef id) = some (.ok evm') := by
  rw [writeStorageDeep.eq_def]
  simp [hget, hw]

theorem writeStorageDeep_string_strLit {env : TypeEnv} {h : Heap} {d : ByteArray} {evm' : EVM.State} (fuel : ℕ)
    (hw : writeBytesStorage cfg evm er .string d = some (.ok evm')) :
    writeStorageDeep cfg env (fuel + 1) evm h er .string (.strLit d) = some (.ok evm') := by
  rw [writeStorageDeep.eq_def]
  simp [storageTyOf, hw]

theorem clearStorage_string {env : TypeEnv} (fuel : ℕ) :
    clearStorage cfg env (fuel + 1) evm er .string = clearBytesStorage cfg evm er .string := by
  rw [clearStorage]
  all_goals first | rfl | (intros; simp_all)

end Solidity
