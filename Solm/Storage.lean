import Storage.Basic

/-! Sol⁻ names for the shared storage layer, now `Storage/Basic.lean`. -/

namespace Solm

export Storage (StorageLoc StorageLoc.mk StorageLoc.slot StorageLoc.offset StorageLoc.size StorageLoc.hbound
  StorageLoc.bitOffset StorageLoc.type StorageReadResult StorageReadResult.ok StorageReadResult.revert
  StorageReadResult.error storageLocLoad storageLocWriteWord storageLocStore StorageLayout StorageLayout.mk
  StorageLayout.layout StorageLayout.readValue? StorageLayout.writeValue? StorageLayout.clearValue?
  StorageLayout.readBytesLength intTypeSize fixedTypeSize)

namespace EVM
export Storage.EVM (storageLoad storageStore)
end EVM

end Solm
