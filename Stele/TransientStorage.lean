import Stele.SolidityStorage

/-!
# Solidity transient storage

Transient storage uses the same layout and encoding as persistent storage. A backend acts on a
storage map, and the semantics hands the transient backend the executing account's transient
storage (`EVM.ownTransient`), so the Solidity transient backend is the persistent one.
-/

namespace Stele

/-- The Solidity backend for transient storage: the persistent backend, applied by the semantics
    to the executing account's transient storage map. -/
abbrev solidityTransientStorageBackend (layout : StorageLayout) : StorageBackend :=
  solidityStorageBackend layout

end Stele
