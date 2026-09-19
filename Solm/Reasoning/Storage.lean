import EVMReasoning.Storage
import Solm.Equiv

/-! # Sol⁻ storage coupling: `readStorage?` / `writeStorage?` / `clearStorage?` on solc string layouts. -/

open Ethereum Ethereum.EVM Solm Storage Refinement

namespace Reasoning.Theory

theorem clearSolidityStringShortZero
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    clearStorage? cfg evm er .string =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hdecode : solidityDecodeBytesLengthHeader (⟨0⟩ : UInt256) = .ok 0 :=
    solidityDecodeBytesLengthHeader_zero
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [clearStorage?, hcfg, solidityStorageLayout, solidityClearValue?,
    solidityPrepareBytesWrite?, hslot, checkBytesPacked, hload,
    solidityBytesHeaderWord, storagePrepareResultToEval]
  rw [show UInt256.ofNat 0 = ({ val := 0 } : UInt256) by native_decide]

theorem clearSolidityStringShortPacked
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    clearStorage? cfg evm er .string =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [clearStorage?, hcfg, solidityStorageLayout, solidityClearValue?,
    solidityPrepareBytesWrite?, hslot, hpacked, solidityBytesHeaderWord,
    storagePrepareResultToEval]
  rw [show UInt256.ofNat 0 = ({ val := 0 } : UInt256) by native_decide]

theorem clearSolidityStringLongPrepared
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    clearStorage? cfg evm er .string =
      .ok (clearSolidityBytesDataWordsFrom
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩)
        baseSlot 0 ((len.toNat + 31) / 32)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  have hpacked : checkBytesPacked baseSlot evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hload hflag
  simp [clearStorage?, hcfg, solidityStorageLayout, solidityClearValue?,
    solidityPrepareBytesWrite?, hslot, hpacked, solidityBytesHeaderWord,
    storagePrepareResultToEval]
  rw [show UInt256.ofNat 0 = ({ val := 0 } : UInt256) by native_decide]

theorem deleteSolidityStringShortZero
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .string))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    deleteStorage? cfg solm evm ref =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hclear := clearSolidityStringShortZero
    (cfg := cfg) (layout := layout) (evm := evm) (er := er) (baseSlot := baseSlot)
    hcfg hbase hload
  simp [deleteStorage?, hresolve, hclear, EvalResult.bind, bind]

theorem deleteSolidityStringShortPacked
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .string))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    deleteStorage? cfg solm evm ref =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hclear := clearSolidityStringShortPacked
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header) (len := len)
    hcfg hbase hload hpacked hflag hlen hvalid
  simp [deleteStorage?, hresolve, hclear, EvalResult.bind, bind]

theorem deleteSolidityStringLongPrepared
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .string))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    deleteStorage? cfg solm evm ref =
      .ok (clearSolidityBytesDataWordsFrom
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩)
        baseSlot 0 ((len.toNat + 31) / 32)) := by
  have hclear := clearSolidityStringLongPrepared
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header) (len := len)
    hcfg hbase hload hflag hlen hvalid
  simp [deleteStorage?, hresolve, hclear, EvalResult.bind, bind]

theorem writeSolidityStringShortPacked
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? cfg evm er .string (.bytes value) =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot
        (solidityShortBytesWord value)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot, hpacked, hvalueSize]

theorem writeSolidityStringShortFromLongPrepared
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? cfg evm er .string (.bytes value) =
      .ok (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom evm baseSlot 0
          ((len.toNat + 31) / 32))
        (clearSolidityBytesDataWordsFrom evm baseSlot 0
          ((len.toNat + 31) / 32)).executionEnv.codeOwner
        baseSlot (solidityShortBytesWord value)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  have hpacked : checkBytesPacked baseSlot evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hload hflag
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot, hpacked, hvalueSize,
    solidityBytesDataWordCount]

theorem writeSolidityStringLongPacked
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? cfg evm er .string (.bytes value) =
      .ok (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom evm baseSlot value 0
          (solidityBytesDataWordCount value.size))
        (writeSolidityBytesDataWordsFrom evm baseSlot value 0
          (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
        baseSlot (solidityBytesHeaderWord value.size)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot, hpacked, hvalueSize,
    solidityBytesDataWordCount]

theorem writeSolidityStringLongPackedAbsent
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hmissing : evm.accountMap.find? evm.executionEnv.codeOwner = none) :
    writeStorage? cfg evm er .string (.bytes value) = .ok evm := by
  have hwrite := writeSolidityStringLongPacked
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header) (len := len) (value := value)
    hcfg hbase hvalueSize hload hpacked hflag hlen hvalid
  have hdata :
      writeSolidityBytesDataWordsFrom evm baseSlot value 0
          (solidityBytesDataWordCount value.size) = evm :=
    writeSolidityBytesDataWordsFrom_absent_same
      (evm := evm) (baseSlot := baseSlot) (value := value) (idx := 0)
      (fuel := solidityBytesDataWordCount value.size) hmissing
  have hstore :
      Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom evm baseSlot value 0
            (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom evm baseSlot value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          baseSlot (solidityBytesHeaderWord value.size) = evm := by
    rw [hdata]
    exact storageStore_absent evm evm.executionEnv.codeOwner hmissing baseSlot
      (solidityBytesHeaderWord value.size)
  simpa [hstore] using hwrite

theorem writeSolidityStringLongFromLongPrepared
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? cfg evm er .string (.bytes value) =
      .ok (Solm.EVM.storageStore
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom evm baseSlot
            (solidityBytesDataWordCount value.size)
            (solidityBytesDataWordCount len.toNat - solidityBytesDataWordCount value.size))
          baseSlot value 0 (solidityBytesDataWordCount value.size))
        (writeSolidityBytesDataWordsFrom
          (clearSolidityBytesDataWordsFrom evm baseSlot
            (solidityBytesDataWordCount value.size)
            (solidityBytesDataWordCount len.toNat - solidityBytesDataWordCount value.size))
          baseSlot value 0 (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
        baseSlot (solidityBytesHeaderWord value.size)) := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  have hpacked : checkBytesPacked baseSlot evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hload hflag
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot, hpacked, hvalueSize,
    solidityBytesDataWordCount]

theorem writeSolidityStringMalformedLong
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? cfg evm er .string (.bytes value) = .revert := by
  have hdecode : solidityDecodeBytesLengthHeader header = .revert := by
    simp [solidityDecodeBytesLengthHeader, hflag, hbad]
  have hslot :=
    solidityBytesBaseSlotAndLength?_revert_of_layout hbase hload hdecode
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot]

theorem writeSolidityStringMalformedShort
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header : UInt256}
    {value : ByteArray}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? cfg evm er .string (.bytes value) = .revert := by
  have hdecode : solidityDecodeBytesLengthHeader header = .revert := by
    have hbad0 :
        UInt256.sub ⟨0⟩
          (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
      simpa [hflag] using hbad
    simp [solidityDecodeBytesLengthHeader, hflag, hbad0]
  have hslot :=
    solidityBytesBaseSlotAndLength?_revert_of_layout hbase hload hdecode
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, hslot]

theorem writeSolidityStringEmptyFromZero
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    writeStorage? cfg evm er .string (.bytes ByteArray.empty) =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hdecode : solidityDecodeBytesLengthHeader (⟨0⟩ : UInt256) = .ok 0 :=
    solidityDecodeBytesLengthHeader_zero
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  simp [writeStorage?, hcfg, solidityStorageLayout, solidityWriteValue?,
    solidityWriteBytesValue?, storagePrepareResultToEval, solidityShortBytesWord,
    hslot, checkBytesPacked, hload]
  rw [empty_readWithPadding_word_zero]
  rfl

theorem assignSolidityStringEmptyFromZero
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .string))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    assignStorageRef? cfg solm evm .storage ref (.bytes ByteArray.empty) =
      .ok (solm, Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  have hwrite := writeSolidityStringEmptyFromZero
    (cfg := cfg) (layout := layout) (evm := evm) (er := er) (baseSlot := baseSlot)
    hcfg hbase hload
  simp [assignStorageRef?, hresolve, hwrite, EvalResult.bind, bind, pure]

theorem readSolidityStringShortPackedExists
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray, readStorage? cfg evm er .string = .ok (.bytes copy) ∧
      copy.size = len.toNat := by
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := solidityShortBytesValid_lt32 hvalid0
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  let copy : ByteArray := header.toByteArray.extract 0 len.toNat
  have hcopySize : copy.size = len.toNat := by
    have hle32 : len.toNat ≤ 32 := by omega
    simp [copy, ByteArray.size_extract, hle32]
  refine ⟨copy, ?_, hcopySize⟩
  simp [readStorage?, hcfg, solidityStorageLayout, solidityReadValue?,
    solidityReadBytesValue?, storageValueResultToEval, hslot, hload, hlt32, copy]

theorem readSolidityStringLongExists
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {evm : EVM.State} {er : EvaledStorageRef} {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray, readStorage? cfg evm er .string = .ok (.bytes copy) ∧
      copy.size = len.toNat := by
  have hdecode : solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot :=
    solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  let copy : ByteArray :=
    if len.toNat < 32 then
      header.toByteArray.extract 0 len.toNat
    else
      (readSolidityBytesDataWordsFrom evm baseSlot 0
        (solidityBytesDataWordCount len.toNat)).extract 0 len.toNat
  have hcopySize : copy.size = len.toNat := by
    by_cases hlt : len.toNat < 32
    · have hle32 : len.toNat ≤ 32 := by omega
      simp [copy, hlt, ByteArray.size_extract, hle32]
    · have hcover : len.toNat ≤ 32 * solidityBytesDataWordCount len.toNat := by
        unfold solidityBytesDataWordCount
        omega
      simp [copy, hlt, ByteArray.size_extract, hcover]
  refine ⟨copy, ?_, hcopySize⟩
  simp [readStorage?, hcfg, solidityStorageLayout, solidityReadValue?,
    solidityReadBytesValue?, storageValueResultToEval, hslot, hload, copy]
  by_cases hlt : len.toNat < 32 <;> simp [hlt]

theorem evalSolidityStringShortPackedExists
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .string))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray, evalExpr? cfg solm evm (.storage ref) = .ok (.bytes copy) ∧
      copy.size = len.toNat := by
  obtain ⟨copy, hread, hcopy⟩ := readSolidityStringShortPackedExists
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header) (len := len)
    hcfg hbase hload hflag hlen hvalid
  refine ⟨copy, ?_, hcopy⟩
  simp [evalExpr?, hresolve, hread, EvalResult.bind, bind]

theorem evalSolidityStringLongExists
    {cfg : Config} {layout : EvaledStorageRef → EVM.State → Option StorageLoc}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {baseSlot header len : UInt256}
    (hcfg : cfg.storage = solidityStorageLayout layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .string))
    (hbase :
      ∃ loc, layout { er with steps := er.steps ++ [.length] } evm = some loc ∧
        loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ copy : ByteArray, evalExpr? cfg solm evm (.storage ref) = .ok (.bytes copy) ∧
      copy.size = len.toNat := by
  obtain ⟨copy, hread, hcopy⟩ := readSolidityStringLongExists
    (cfg := cfg) (layout := layout) (evm := evm) (er := er)
    (baseSlot := baseSlot) (header := header) (len := len)
    hcfg hbase hload hflag hlen hvalid
  refine ⟨copy, ?_, hcopy⟩
  simp [evalExpr?, hresolve, hread, EvalResult.bind, bind]

end Reasoning.Theory
