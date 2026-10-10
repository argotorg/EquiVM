import Benchmarks.Morpho.MetaMorphoV1_1.StringHeader

/-! Source reads of the two storage-backed token metadata strings. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def stringStorageLayout : StorageLayout :=
  solidityLayout! [contract.structs] [contract.storage]

def stringViewField (symbol : Bool) : Ident := if symbol then "_vaultSymbol" else "_vaultName"

def stringViewSlot (symbol : Bool) : UInt256 := if symbol then ⟨25⟩ else ⟨24⟩

def storageStringHeader (evm : State) (slot : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot

def storageStringBytes (evm : State) (slot : UInt256) : ByteArray :=
  let header := storageStringHeader evm slot
  let len := (storageStringLength header).toNat
  if len < 32 then header.toByteArray.extract 0 len
  else (readSolidityBytesDataWordsFrom evm slot 0 (solidityBytesDataWordCount len)).extract 0 len

theorem storageStringBytes_size (evm : State) (slot : UInt256) :
    (storageStringBytes evm slot).size =
      (storageStringLength (storageStringHeader evm slot)).toNat := by
  dsimp only [storageStringBytes]
  split
  · rw [ByteArray.size_extract, toByteArray_size]; omega
  · rw [ByteArray.size_extract, readSolidityBytesDataWordsFrom_size]
    unfold solidityBytesDataWordCount
    omega

theorem stringStorageResolve (symbol : Bool) (evm : State) (locals imms : Store)
    (hbase : locals.get? (stringViewField symbol) = none) :
    resolveStorageRef? config ⟨contract, locals, imms⟩ evm ⟨stringViewField symbol, []⟩ =
      .ok (⟨stringViewField symbol, []⟩, .string) := by
  apply resolveStorageRef?_ok hbase
  · simp [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure]
  · cases symbol <;> rfl

theorem storageStringReadAt (field : Ident) (slot : UInt256) (evm : State)
    (hslot : stringStorageLayout ⟨field, []⟩ = some (.anchor slot))
    (hvalid : storageStringValid (storageStringHeader evm slot)) :
    config.storageBackend.read ⟨field, []⟩ .string evm =
      .ok (.bytes (storageStringBytes evm slot)) := by
  have hd := storageStringDecode (storageStringHeader evm slot) hvalid
  have hl : solidityBytesBaseSlotAndLength?
      stringStorageLayout ⟨field, []⟩ evm =
      .ok (slot, (storageStringLength (storageStringHeader evm slot)).toNat) := by
    apply solidityBytesBaseSlotAndLength?_ok_of_layout (header :=
      storageStringHeader evm slot) hslot rfl hd
  change (solidityStorageBackend stringStorageLayout).read ⟨field, []⟩ .string evm = _
  simp only [solidityStorageBackend, solidityReadStorage?, solidityReadBytesValue?, hl]
  dsimp only [storageStringBytes, storageStringHeader]
  split <;> rfl

theorem storageStringReadAtReverts (field : Ident) (slot : UInt256) (evm : State)
    (hslot : stringStorageLayout ⟨field, []⟩ = some (.anchor slot))
    (hbad : ¬ storageStringValid (storageStringHeader evm slot)) :
    config.storageBackend.read ⟨field, []⟩ .string evm = .revert := by
  have hd := storageStringDecodeRevert (storageStringHeader evm slot) hbad
  have hl : solidityBytesBaseSlotAndLength?
      stringStorageLayout ⟨field, []⟩ evm = .revert := by
    apply solidityBytesBaseSlotAndLength?_revert_of_layout (header :=
      storageStringHeader evm slot) hslot rfl hd
  change (solidityStorageBackend stringStorageLayout).read ⟨field, []⟩ .string evm = _
  simp only [solidityStorageBackend, solidityReadStorage?, solidityReadBytesValue?, hl]
  rfl

theorem stringStorageRead (symbol : Bool) (evm : State)
    (hvalid : storageStringValid (storageStringHeader evm (stringViewSlot symbol))) :
    config.storageBackend.read ⟨stringViewField symbol, []⟩ .string evm =
      .ok (.bytes (storageStringBytes evm (stringViewSlot symbol))) :=
  storageStringReadAt _ _ evm (by cases symbol <;> rfl) hvalid

theorem stringStorageReadReverts (symbol : Bool) (evm : State)
    (hbad : ¬ storageStringValid (storageStringHeader evm (stringViewSlot symbol))) :
    config.storageBackend.read ⟨stringViewField symbol, []⟩ .string evm = .revert :=
  storageStringReadAtReverts _ _ evm (by cases symbol <;> rfl) hbad

theorem evalStorage_string (symbol : Bool) (evm : State) (locals imms : Store)
    (hbase : locals.get? (stringViewField symbol) = none)
    (hvalid : storageStringValid (storageStringHeader evm (stringViewSlot symbol))) :
    evalExpr? config ⟨contract, locals, imms⟩ evm (.storage ⟨stringViewField symbol, []⟩) =
      .ok (.bytes (storageStringBytes evm (stringViewSlot symbol))) := by
  rw [evalExpr?, stringStorageResolve symbol evm locals imms hbase]
  exact stringStorageRead symbol evm hvalid

theorem evalStorage_stringReverts (symbol : Bool) (evm : State) (locals imms : Store)
    (hbase : locals.get? (stringViewField symbol) = none)
    (hbad : ¬ storageStringValid (storageStringHeader evm (stringViewSlot symbol))) :
    evalExpr? config ⟨contract, locals, imms⟩ evm (.storage ⟨stringViewField symbol, []⟩) =
      .revert := by
  rw [evalExpr?, stringStorageResolve symbol evm locals imms hbase]
  exact stringStorageReadReverts symbol evm hbad

end Benchmarks.Morpho.MetaMorphoV1_1
