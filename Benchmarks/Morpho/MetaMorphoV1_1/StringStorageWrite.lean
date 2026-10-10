import Benchmarks.Morpho.MetaMorphoV1_1.StringStorageSource

/-! Source string assignments preserve the compiler's clear, data, then header write order. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: the state produced by the generic Solidity string writer.
def storageStringWriteState (evm : State) (slot : UInt256) (bytes : ByteArray) : State :=
  let oldLen := (storageStringLength (storageStringHeader evm slot)).toNat
  if bytes.size < 32 then
    let clean := if checkBytesPacked slot evm then evm
      else clearSolidityBytesDataWordsFrom evm slot 0 (solidityBytesDataWordCount oldLen)
    Solm.EVM.storageStore clean clean.executionEnv.codeOwner slot (solidityShortBytesWord bytes)
  else
    let words := solidityBytesDataWordCount bytes.size
    let clean := if checkBytesPacked slot evm then evm
      else clearSolidityBytesDataWordsFrom evm slot words
        (solidityBytesDataWordCount oldLen - words)
    let data := writeSolidityBytesDataWordsFrom clean slot bytes 0 words
    Solm.EVM.storageStore data data.executionEnv.codeOwner slot (solidityBytesHeaderWord bytes.size)

theorem storageStringWriteAt (field : Ident) (slot : UInt256) (evm : State) (bytes : ByteArray)
    (hslot : stringStorageLayout ⟨field, []⟩ = some (.anchor slot))
    (hvalid : storageStringValid (storageStringHeader evm slot)) :
    config.storageBackend.write ⟨field, []⟩ .string (.bytes bytes) evm =
      .ok (storageStringWriteState evm slot bytes) := by
  have hd := storageStringDecode (storageStringHeader evm slot) hvalid
  have hl := solidityBytesBaseSlotAndLength?_ok_of_layout (header := storageStringHeader evm slot)
    hslot rfl hd
  change (solidityStorageBackend stringStorageLayout).write ⟨field, []⟩ .string (.bytes bytes)
    evm = _
  simp only [solidityStorageBackend, solidityWriteStorage?, solidityWriteBytesValue?, hl]
  unfold storageStringWriteState
  split <;> rfl

theorem storageStringWriteAtReverts (field : Ident) (slot : UInt256) (evm : State)
    (bytes : ByteArray) (hslot : stringStorageLayout ⟨field, []⟩ = some (.anchor slot))
    (hbad : ¬ storageStringValid (storageStringHeader evm slot)) :
    config.storageBackend.write ⟨field, []⟩ .string (.bytes bytes) evm = .revert := by
  have hd := storageStringDecodeRevert (storageStringHeader evm slot) hbad
  have hl := solidityBytesBaseSlotAndLength?_revert_of_layout
    (header := storageStringHeader evm slot) hslot rfl hd
  change (solidityStorageBackend stringStorageLayout).write ⟨field, []⟩ .string (.bytes bytes)
    evm = _
  simp only [solidityStorageBackend, solidityWriteStorage?, solidityWriteBytesValue?, hl]
  rfl

theorem assignStorageString (symbol : Bool) (evm : State) (locals imms : Store)
    (bytes : ByteArray) (hbase : locals.get? (stringViewField symbol) = none)
    (hvalid : storageStringValid (storageStringHeader evm (stringViewSlot symbol))) :
    assignStorageRef? config ⟨contract, locals, imms⟩ evm .storage
      ⟨stringViewField symbol, []⟩ (.bytes bytes) =
      .ok (⟨contract, locals, imms⟩,
        storageStringWriteState evm (stringViewSlot symbol) bytes) := by
  have hw := storageStringWriteAt (stringViewField symbol) (stringViewSlot symbol) evm bytes
    (by cases symbol <;> rfl) hvalid
  simp [assignStorageRef?, stringStorageResolve symbol evm locals imms hbase, hw,
    EvalResult.bind, bind, pure]

theorem assignStorageStringReverts (symbol : Bool) (evm : State) (locals imms : Store)
    (bytes : ByteArray) (hbase : locals.get? (stringViewField symbol) = none)
    (hbad : ¬ storageStringValid (storageStringHeader evm (stringViewSlot symbol))) :
    assignStorageRef? config ⟨contract, locals, imms⟩ evm .storage
      ⟨stringViewField symbol, []⟩ (.bytes bytes) = .revert := by
  have hw := storageStringWriteAtReverts (stringViewField symbol) (stringViewSlot symbol) evm bytes
    (by cases symbol <;> rfl) hbad
  simp [assignStorageRef?, stringStorageResolve symbol evm locals imms hbase, hw,
    EvalResult.bind, bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1
