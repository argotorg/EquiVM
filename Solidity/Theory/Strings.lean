import Solidity.Theory.Body

/-!
# `string`/`bytes` storage on the solc layout

`readBytesStorage`/`writeBytesStorage`/`clearStorage` go through the storage backend; on
`Solm.solidityStorageBackend` these are solc's short/long byte-array representation, whose
clearing and writing `Reasoning.Theory` states (`clearSolidityString*`, `writeSolidityString*`).
Each lemma names the header slot (`hbase`: the reference's anchor), its current word (`hload`) and
the header's shape, and states the exact storage the operation produces.  The deep read/write of a
`string`-typed reference reduce to them.
-/

namespace Solidity

open Ethereum Reasoning.Theory

variable {cfg : Config} {L : Solm.StorageLayout} {evm : EVM.State} {er : Solm.EvaledStorageRef}
  {baseSlot header len : UInt256}

/-- A Sol⁻ config with the solc backend: `Reasoning.Theory`'s string-storage lemmas are stated on
    `Solm.Config`, and only its backend matters. -/
def solmCfg (L : Solm.StorageLayout) : Solm.Config :=
  { storageBackend := Solm.solidityStorageBackend L, externalABI := ⟨fun _ _ => none, fun _ _ => none⟩, selfDeployment := fun _ _ => none }

theorem solm_backend (hcfg : cfg.storageBackend = Solm.solidityStorageBackend L) :
    cfg.storageBackend = (solmCfg L).storageBackend := hcfg

/-! ## Lifting backend results -/

theorem readBytesStorage_of_backend {st : Solm.StorageType} {b : ByteArray}
    (hr : cfg.storageBackend.read er st evm = .ok (.bytes b)) : readBytesStorage cfg evm er st = some (.ok b) := by
  simp [readBytesStorage, liftStorage, hr]

theorem writeBytesStorage_of_backend {st : Solm.StorageType} {d : ByteArray} {evm' : EVM.State}
    (hw : cfg.storageBackend.write er st (.bytes d) evm = .ok evm') :
    writeBytesStorage cfg evm er st d = some (.ok evm') := by
  simp [writeBytesStorage, liftStorage, hw]

/-- A backend revert is `Panic(0x22)` (a malformed byte-array header). -/
theorem writeBytesStorage_revert_of_backend {st : Solm.StorageType} {d : ByteArray}
    (hw : cfg.storageBackend.write er st (.bytes d) evm = .revert) :
    writeBytesStorage cfg evm er st d = some (.error .storageBytes) := by
  simp only [writeBytesStorage, hw, liftStorage]
  rfl

/-! ## Clearing (`delete s`) -/

theorem clearStorage_string_shortZero {env : TypeEnv} (hcfg : cfg.storageBackend = Solm.solidityStorageBackend L)
    (hbase : L er = some (.anchor baseSlot))
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    clearStorage cfg env evm er .string =
      some (.ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩)) :=
  clearStorage_of_backend (storageTypeOf_string env) (by rw [solm_backend hcfg]; exact clearSolidityStringShortZero rfl hbase hload)

theorem clearStorage_string_shortPacked {env : TypeEnv} (hcfg : cfg.storageBackend = Solm.solidityStorageBackend L)
    (hbase : L er = some (.anchor baseSlot))
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : Solm.checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    clearStorage cfg env evm er .string =
      some (.ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩)) :=
  clearStorage_of_backend (storageTypeOf_string env)
    (by rw [solm_backend hcfg]; exact clearSolidityStringShortPacked rfl hbase hload hpacked hflag hlen hvalid)

theorem clearStorage_string_longPrepared {env : TypeEnv} (hcfg : cfg.storageBackend = Solm.solidityStorageBackend L)
    (hbase : L er = some (.anchor baseSlot))
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    clearStorage cfg env evm er .string =
      some (.ok (Solm.clearSolidityBytesDataWordsFrom
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) baseSlot 0 ((len.toNat + 31) / 32))) :=
  clearStorage_of_backend (storageTypeOf_string env)
    (by rw [solm_backend hcfg]; exact clearSolidityStringLongPrepared rfl hbase hload hflag hlen hvalid)

/-! ## Writing (the backend's result; `writeBytesStorage_of_backend` lifts it) -/

theorem writeString_shortPacked {value : ByteArray} (hcfg : cfg.storageBackend = Solm.solidityStorageBackend L)
    (hbase : L er = some (.anchor baseSlot))
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : Solm.checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    cfg.storageBackend.write er .string (.bytes value) evm =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot (Solm.solidityShortBytesWord value)) := by
  rw [solm_backend hcfg]; exact writeSolidityStringShortPacked rfl hbase hvalueSize hload hpacked hflag hlen hvalid

theorem writeString_shortFromLongPrepared {value : ByteArray}
    (hcfg : cfg.storageBackend = Solm.solidityStorageBackend L)
    (hbase : L er = some (.anchor baseSlot))
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    cfg.storageBackend.write er .string (.bytes value) evm =
      .ok (Solm.EVM.storageStore
        (Solm.clearSolidityBytesDataWordsFrom evm baseSlot 0 ((len.toNat + 31) / 32))
        (Solm.clearSolidityBytesDataWordsFrom evm baseSlot 0 ((len.toNat + 31) / 32)).executionEnv.codeOwner
        baseSlot (Solm.solidityShortBytesWord value)) := by
  rw [solm_backend hcfg]; exact writeSolidityStringShortFromLongPrepared rfl hbase hvalueSize hload hflag hlen hvalid

theorem writeString_longPacked {value : ByteArray} (hcfg : cfg.storageBackend = Solm.solidityStorageBackend L)
    (hbase : L er = some (.anchor baseSlot))
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hpacked : Solm.checkBytesPacked baseSlot evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    cfg.storageBackend.write er .string (.bytes value) evm =
      .ok (Solm.EVM.storageStore
        (Solm.writeSolidityBytesDataWordsFrom evm baseSlot value 0 (Solm.solidityBytesDataWordCount value.size))
        (Solm.writeSolidityBytesDataWordsFrom evm baseSlot value 0
          (Solm.solidityBytesDataWordCount value.size)).executionEnv.codeOwner
        baseSlot (Solm.solidityBytesHeaderWord value.size)) := by
  rw [solm_backend hcfg]; exact writeSolidityStringLongPacked rfl hbase hvalueSize hload hpacked hflag hlen hvalid

theorem writeString_longFromLongPrepared {value : ByteArray}
    (hcfg : cfg.storageBackend = Solm.solidityStorageBackend L)
    (hbase : L er = some (.anchor baseSlot))
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    cfg.storageBackend.write er .string (.bytes value) evm =
      .ok (Solm.EVM.storageStore
        (Solm.writeSolidityBytesDataWordsFrom
          (Solm.clearSolidityBytesDataWordsFrom evm baseSlot (Solm.solidityBytesDataWordCount value.size)
            (Solm.solidityBytesDataWordCount len.toNat - Solm.solidityBytesDataWordCount value.size))
          baseSlot value 0 (Solm.solidityBytesDataWordCount value.size))
        (Solm.writeSolidityBytesDataWordsFrom
          (Solm.clearSolidityBytesDataWordsFrom evm baseSlot (Solm.solidityBytesDataWordCount value.size)
            (Solm.solidityBytesDataWordCount len.toNat - Solm.solidityBytesDataWordCount value.size))
          baseSlot value 0 (Solm.solidityBytesDataWordCount value.size)).executionEnv.codeOwner
        baseSlot (Solm.solidityBytesHeaderWord value.size)) := by
  rw [solm_backend hcfg]; exact writeSolidityStringLongFromLongPrepared rfl hbase hvalueSize hload hflag hlen hvalid

/-- A malformed long header: the backend reverts (`Panic(0x22)` after `liftStorage`). -/
theorem writeString_malformedLong {value : ByteArray} (hcfg : cfg.storageBackend = Solm.solidityStorageBackend L)
    (hbase : L er = some (.anchor baseSlot))
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    cfg.storageBackend.write er .string (.bytes value) evm = .revert := by
  rw [solm_backend hcfg]; exact writeSolidityStringMalformedLong rfl hbase hload hflag hbad

theorem writeString_malformedShort {value : ByteArray} (hcfg : cfg.storageBackend = Solm.solidityStorageBackend L)
    (hbase : L er = some (.anchor baseSlot))
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    cfg.storageBackend.write er .string (.bytes value) evm = .revert := by
  rw [solm_backend hcfg]; exact writeSolidityStringMalformedShort rfl hbase hload hflag hbad

theorem writeString_emptyFromZero (hcfg : cfg.storageBackend = Solm.solidityStorageBackend L)
    (hbase : L er = some (.anchor baseSlot))
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    cfg.storageBackend.write er .string (.bytes ByteArray.empty) evm =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩) := by
  rw [solm_backend hcfg]; exact writeSolidityStringEmptyFromZero rfl hbase hload

/-! ## Reading (the backend's result; `readBytesStorage_of_backend` lifts it) -/

theorem readString_shortPacked (hcfg : cfg.storageBackend = Solm.solidityStorageBackend L)
    (hbase : L er = some (.anchor baseSlot))
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    cfg.storageBackend.read er .string evm = .ok (.bytes (header.toByteArray.extract 0 len.toNat)) := by
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by simpa [hflag] using hvalid
  have hlt32 : len.toNat < 32 := solidityShortBytesValid_lt32 hvalid0
  have hdecode : Solm.solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_short_valid hflag hlen hvalid
  have hslot := solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  rw [hcfg]
  simp [Solm.solidityStorageBackend, Solm.solidityReadStorage?, Solm.solidityReadBytesValue?,
    Solm.solidityValueResultToEval, hslot, hload, hlt32]

theorem readString_long (hcfg : cfg.storageBackend = Solm.solidityStorageBackend L)
    (hbase : L er = some (.anchor baseSlot))
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    cfg.storageBackend.read er .string evm =
      .ok (.bytes (if len.toNat < 32 then header.toByteArray.extract 0 len.toNat
        else (Solm.readSolidityBytesDataWordsFrom evm baseSlot 0 (Solm.solidityBytesDataWordCount len.toNat)).extract
          0 len.toNat)) := by
  have hdecode : Solm.solidityDecodeBytesLengthHeader header = .ok len.toNat :=
    solidityDecodeBytesLengthHeader_long_valid hflag hlen hvalid
  have hslot := solidityBytesBaseSlotAndLength?_ok_of_layout hbase hload hdecode
  rw [hcfg]
  simp [Solm.solidityStorageBackend, Solm.solidityReadStorage?, Solm.solidityReadBytesValue?,
    Solm.solidityValueResultToEval, hslot, hload]
  by_cases hlt : len.toNat < 32 <;> simp [hlt]

/-! ## Deep reads and writes of a `string` -/

theorem readStorageDeep_string {env : TypeEnv} {h : Heap} {data : ByteArray} (fuel : ℕ)
    (hr : cfg.storageBackend.read er .string evm = .ok (.bytes data)) :
    readStorageDeep cfg env (fuel + 1) evm h er .string =
      some (.ok (.memRef (h.alloc (.bytes true data)).2, (h.alloc (.bytes true data)).1)) := by
  simp [readStorageDeep, isValueType, leafElemType, storageTypeOf_string, hr, liftStorage, ofAbi, Op.ofOpt]
  rfl

theorem writeStorageDeep_string_memRef {env : TypeEnv} {h : Heap} {id : ℕ} {isStr : Bool} {d : ByteArray}
    {evm' : EVM.State} (fuel : ℕ) (hget : h.get? id = some (.bytes isStr d))
    (hw : cfg.storageBackend.write er .string (.bytes d) evm = .ok evm') :
    writeStorageDeep cfg env (fuel + 1) evm h er .string (.memRef id) = some (.ok evm') :=
  writeStorageDeep_of_value (storageTypeOf_string env) (by simp [storageValueOf, toStorage, hget]) hw

theorem writeStorageDeep_string_strLit {env : TypeEnv} {h : Heap} {d : ByteArray} {evm' : EVM.State} (fuel : ℕ)
    (hw : cfg.storageBackend.write er .string (.bytes d) evm = .ok evm') :
    writeStorageDeep cfg env (fuel + 1) evm h er .string (.strLit d) = some (.ok evm') :=
  writeStorageDeep_of_value (storageTypeOf_string env) (by simp [storageValueOf, toStorage]) hw

end Solidity
