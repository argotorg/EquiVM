import Examples.BytesStoreLite.Spec
import Examples.BytesStoreLite.CoreSetOldLong
import Reasoning.Refinement
import Reasoning.Storage

/-!
# BytesStoreLite storage readback facts

Small collision-aware readback wrappers for owner storage writes.  These facts intentionally expose
the aliasing branch instead of assuming Solidity storage-layout separation.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace BytesStoreLite

def bytesStoreLiteChunksLengthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)

theorem bytesStoreLiteChunksLengthWord_eq_of_accountMapEquiv {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreLiteChunksLengthWord σ_evm I = bytesStoreLiteChunksLengthWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩

theorem bytesStoreLiteStorageLoad_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (slot : UInt256) (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner slot =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD slot ⟨0⟩)) := by
  have hword :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot (⟨0⟩ : UInt256)
  simpa [Solm.EVM.storageLoad, initState, State.lookupAccount, Account.lookupStorage] using
    hword.symm

def bytesStoreLitePushChunkSlot (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  chunksDataBase + bytesStoreLiteChunksLengthWord σ I

def bytesStoreLitePushChunkHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreLitePushChunkSlot σ I) ⟨0⟩)

def bytesStoreLitePushChunkPostLengthHeaderWord (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  if bytesStoreLitePushChunkSlot σ I = (⟨1⟩ : UInt256) then
    (σ.find? I.codeOwner |>.option ⟨0⟩
      (fun _ => bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
  else
    bytesStoreLitePushChunkHeaderWord σ I

theorem bytesStoreLitePushChunkPostLengthHeaderWord_eq_if
    (σ : AccountMap) (I : ExecutionEnv) :
    bytesStoreLitePushChunkPostLengthHeaderWord σ I =
      if bytesStoreLitePushChunkSlot σ I = (⟨1⟩ : UInt256) then
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun _ => bytesStoreLiteChunksLengthWord σ I + ⟨1⟩))
      else
        bytesStoreLitePushChunkHeaderWord σ I := by
  rfl

theorem bytesStoreLitePushChunkPostLengthHeaderWord_sstore
    (σ : AccountMap) (I : ExecutionEnv) :
    ((sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLitePushChunkSlot σ I) ⟨0⟩)) =
      bytesStoreLitePushChunkPostLengthHeaderWord σ I := by
  simpa [bytesStoreLitePushChunkPostLengthHeaderWord, bytesStoreLitePushChunkSlot,
    bytesStoreLitePushChunkHeaderWord] using
    sstoreAccountMap_storage_findD_eq_if σ I.codeOwner
      (chunksDataBase + bytesStoreLiteChunksLengthWord σ I) ⟨1⟩
      (bytesStoreLiteChunksLengthWord σ I + ⟨1⟩)

theorem bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreLitePushChunkSlot σ_evm I) =
      bytesStoreLitePushChunkHeaderWord σ_evm I := by
  simpa [bytesStoreLitePushChunkHeaderWord] using
    bytesStoreLiteStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStoreLitePushChunkSlot σ_evm I) hAccounts

theorem bytesStoreLiteStorageLoadPushChunkPostLengthHeader_initState_eq_if_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
          (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreLitePushChunkSlot σ_evm I) =
      if bytesStoreLitePushChunkSlot σ_evm I = (⟨1⟩ : UInt256) then
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun _ => bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
      else
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
  let evm0 := initState cA gh bl σ_solm σ₀ g A I
  have hloadElem :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner
          (bytesStoreLitePushChunkSlot σ_evm I) =
        bytesStoreLitePushChunkHeaderWord σ_evm I := by
    simpa [evm0] using
      bytesStoreLiteStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) hAccounts
  simpa [evm0, bytesStoreLitePushChunkSlot, storageStore_executionEnv] using
    (storageLoad_storageStore_eq_if evm0 evm0.executionEnv.codeOwner
      (chunksDataBase + bytesStoreLiteChunksLengthWord σ_evm I) ⟨1⟩
      (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩)).trans
      (by
        split
        · cases hacc : σ_evm.find? I.codeOwner with
          | none =>
              have hnone := accountMapEquiv_find?_none hAccounts hacc
              simpa [evm0, initState, hnone, Option.option, default] using
                (show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by native_decide)
          | some acc =>
              obtain ⟨acc', hsome⟩ := accountMapEquiv_find?_some_exists hAccounts hacc
              simp [evm0, initState, hsome, Option.option]
        · exact hloadElem)

theorem bytesStoreLiteStorageLoadPushChunkPostLengthHeader_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
          (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner ⟨1⟩
          (bytesStoreLiteChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreLitePushChunkSlot σ_evm I) =
      bytesStoreLitePushChunkPostLengthHeaderWord σ_evm I := by
  rw [bytesStoreLiteStorageLoadPushChunkPostLengthHeader_initState_eq_if_of_accountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hAccounts]
  rw [bytesStoreLitePushChunkPostLengthHeaderWord_eq_if]

/-- Reading an owner storage word after a single store, with the collision case explicit. -/
theorem bytesStoreLiteStorageWordAfterSstore_eq_if
    (σ : AccountMap) (I : ExecutionEnv) (readSlot writeSlot val : UInt256) :
    ((sstoreAccountMap I.codeOwner σ writeSlot val).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD readSlot (default : UInt256))) =
      if readSlot = writeSlot then
        ((σ.find? I.codeOwner).option (default : UInt256) (fun _ => val))
      else
        (σ.find? I.codeOwner |>.option (default : UInt256)
          (fun acc => acc.storage.findD readSlot (default : UInt256))) := by
  exact sstoreAccountMap_storage_findD_eq_if σ I.codeOwner readSlot writeSlot val

/-- Preserving an owner storage word after a single store is the non-collision corollary of the
collision-aware readback lemma. -/
theorem bytesStoreLiteStorageWordAfterSstore_ne
    (σ : AccountMap) (I : ExecutionEnv) (readSlot writeSlot val : UInt256)
    (hne : readSlot ≠ writeSlot) :
    ((sstoreAccountMap I.codeOwner σ writeSlot val).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD readSlot (default : UInt256))) =
      (σ.find? I.codeOwner |>.option (default : UInt256)
        (fun acc => acc.storage.findD readSlot (default : UInt256))) := by
  rw [bytesStoreLiteStorageWordAfterSstore_eq_if σ I readSlot writeSlot val, if_neg hne]

theorem bytesStoreLiteStorageWordAfterSstore_eq_if_of_before
    {σ : AccountMap} {I : ExecutionEnv} {readSlot writeSlot val word : UInt256}
    (hword :
      (σ.find? I.codeOwner |>.option (default : UInt256)
        (fun acc => acc.storage.findD readSlot (default : UInt256))) = word) :
    ((sstoreAccountMap I.codeOwner σ writeSlot val).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD readSlot (default : UInt256))) =
      if readSlot = writeSlot then
        ((σ.find? I.codeOwner).option (default : UInt256) (fun _ => val))
      else
        word := by
  rw [bytesStoreLiteStorageWordAfterSstore_eq_if, hword]

/-- Owner `storageLoad` after an owner `storageStore`, with the collision case explicit. -/
theorem bytesStoreLiteStorageLoadAfterStorageStore_eq_if
    (evm : EVM.State) (readSlot writeSlot val : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner writeSlot val)
        evm.executionEnv.codeOwner readSlot =
      if readSlot = writeSlot then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner readSlot := by
  exact storageLoad_storageStore_eq_if evm evm.executionEnv.codeOwner readSlot writeSlot val

/-- Preserving an owner `storageLoad` after an owner `storageStore` is the non-collision corollary
of the collision-aware readback lemma. -/
theorem bytesStoreLiteStorageLoadAfterStorageStore_ne
    (evm : EVM.State) (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner writeSlot val)
        evm.executionEnv.codeOwner readSlot =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner readSlot := by
  rw [bytesStoreLiteStorageLoadAfterStorageStore_eq_if evm readSlot writeSlot val, if_neg hne]

theorem bytesStoreLiteStorageLoadAfterStorageStore_eq_if_of_before
    {evm : EVM.State} {readSlot writeSlot val word : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner readSlot = word) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner writeSlot val)
        evm.executionEnv.codeOwner readSlot =
      if readSlot = writeSlot then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        word := by
  rw [bytesStoreLiteStorageLoadAfterStorageStore_eq_if, hload]

/-- Owner storage header readback after writing a long `bytes` data word, with the collision case
exposed instead of hidden behind a layout assumption. -/
theorem bytesStoreLiteBytesHeaderWordAfterDataSstore_eq_if
    (σ : AccountMap) (I : ExecutionEnv) (baseSlot idx val : UInt256) :
    ((sstoreAccountMap I.codeOwner σ
        (bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) val).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD baseSlot (default : UInt256))) =
      if baseSlot = bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩ then
        ((σ.find? I.codeOwner).option (default : UInt256) (fun _ => val))
      else
        (σ.find? I.codeOwner |>.option (default : UInt256)
          (fun acc => acc.storage.findD baseSlot (default : UInt256))) := by
  exact bytesStoreLiteStorageWordAfterSstore_eq_if σ I baseSlot
    (bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) val

/-- Owner `storageLoad` header readback after writing a long `bytes` data word, with the collision
case exposed instead of hidden behind a layout assumption. -/
theorem bytesStoreLiteStorageLoadBytesHeaderAfterDataStore_eq_if
    (evm : EVM.State) (baseSlot idx val : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) val)
        evm.executionEnv.codeOwner baseSlot =
      if baseSlot = bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩ then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot := by
  exact bytesStoreLiteStorageLoadAfterStorageStore_eq_if evm baseSlot
    (bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) val

theorem bytesStoreLiteBytesHeaderWordAfterDataSstore_ne_of_ne
    (σ : AccountMap) (I : ExecutionEnv) (baseSlot idx val : UInt256)
    (hne : baseSlot ≠ bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) :
    ((sstoreAccountMap I.codeOwner σ
        (bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) val).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD baseSlot (default : UInt256))) =
      (σ.find? I.codeOwner |>.option (default : UInt256)
        (fun acc => acc.storage.findD baseSlot (default : UInt256))) := by
  rw [bytesStoreLiteBytesHeaderWordAfterDataSstore_eq_if]
  exact if_neg hne

theorem bytesStoreLiteStorageLoadBytesHeaderAfterDataStore_ne_of_ne
    (evm : EVM.State) (baseSlot idx val : UInt256)
    (hne : baseSlot ≠ bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) val)
        evm.executionEnv.codeOwner baseSlot =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot := by
  rw [bytesStoreLiteStorageLoadBytesHeaderAfterDataStore_eq_if]
  exact if_neg hne

theorem bytesStoreLiteBytesHeaderWordAfterDataSstore_eq_if_of_before
    {σ : AccountMap} {I : ExecutionEnv} {baseSlot idx val word : UInt256}
    (hword :
      (σ.find? I.codeOwner |>.option (default : UInt256)
        (fun acc => acc.storage.findD baseSlot (default : UInt256))) = word) :
    ((sstoreAccountMap I.codeOwner σ
        (bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) val).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD baseSlot (default : UInt256))) =
      if baseSlot = bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩ then
        ((σ.find? I.codeOwner).option (default : UInt256) (fun _ => val))
      else
        word := by
  exact bytesStoreLiteStorageWordAfterSstore_eq_if_of_before hword

theorem bytesStoreLiteBytesHeaderWordAfterDataSstore_eq_of_before_of_ne
    {σ : AccountMap} {I : ExecutionEnv} {baseSlot idx val word : UInt256}
    (hne : baseSlot ≠ bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩)
    (hword :
      (σ.find? I.codeOwner |>.option (default : UInt256)
        (fun acc => acc.storage.findD baseSlot (default : UInt256))) = word) :
    ((sstoreAccountMap I.codeOwner σ
        (bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) val).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD baseSlot (default : UInt256))) =
      word := by
  rw [bytesStoreLiteBytesHeaderWordAfterDataSstore_eq_if_of_before hword]
  exact if_neg hne

theorem bytesStoreLiteStorageLoadBytesHeaderAfterDataStore_eq_if_of_before
    {evm : EVM.State} {baseSlot idx val word : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = word) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) val)
        evm.executionEnv.codeOwner baseSlot =
      if baseSlot = bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩ then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        word := by
  exact bytesStoreLiteStorageLoadAfterStorageStore_eq_if_of_before hload

theorem bytesStoreLiteStorageLoadBytesHeaderAfterDataStore_eq_of_before_of_ne
    {evm : EVM.State} {baseSlot idx val word : UInt256}
    (hne : baseSlot ≠ bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = word) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) val)
        evm.executionEnv.codeOwner baseSlot =
      word := by
  rw [bytesStoreLiteStorageLoadBytesHeaderAfterDataStore_eq_if_of_before hload]
  exact if_neg hne

theorem bytesStoreLitePacketDataWordAfterTagSstore_eq_if
    (σ : AccountMap) (I : ExecutionEnv) (tag : UInt256) :
    ((sstoreAccountMap I.codeOwner σ ⟨3⟩ tag).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      if (⟨2⟩ : UInt256) = ⟨3⟩ then
        ((σ.find? I.codeOwner).option (default : UInt256) (fun _ => tag))
      else
        (σ.find? I.codeOwner |>.option (default : UInt256)
          (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) := by
  exact bytesStoreLiteStorageWordAfterSstore_eq_if σ I ⟨2⟩ ⟨3⟩ tag

theorem bytesStoreLitePacketDataWordAfterTagSstore_ne
    (σ : AccountMap) (I : ExecutionEnv) (tag : UInt256) :
    ((sstoreAccountMap I.codeOwner σ ⟨3⟩ tag).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      (σ.find? I.codeOwner |>.option (default : UInt256)
        (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) := by
  rw [bytesStoreLitePacketDataWordAfterTagSstore_eq_if]
  exact if_neg (by native_decide : (⟨2⟩ : UInt256) ≠ ⟨3⟩)

theorem bytesStoreLitePacketDataWordAfterTagSstore_eq_of_before
    {σ : AccountMap} {I : ExecutionEnv} {tag word : UInt256}
    (hword :
      (σ.find? I.codeOwner |>.option (default : UInt256)
        (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) = word) :
    ((sstoreAccountMap I.codeOwner σ ⟨3⟩ tag).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      word := by
  exact (bytesStoreLitePacketDataWordAfterTagSstore_ne σ I tag).trans hword

/-- Reading `chunks.length` after a single store, with the collision case explicit. -/
theorem bytesStoreLiteChunksLengthAfterSstore_eq_if
    (σ : AccountMap) (I : ExecutionEnv) (slot val : UInt256) :
    bytesStoreLiteChunksLengthWord (sstoreAccountMap I.codeOwner σ slot val) I =
      if (⟨1⟩ : UInt256) = slot then
        ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256) (fun _ => val))
      else
        bytesStoreLiteChunksLengthWord σ I := by
  exact bytesStoreLiteStorageWordAfterSstore_eq_if σ I ⟨1⟩ slot val

/-- Preserving `chunks.length` after a single store is the non-collision corollary of the
collision-aware readback lemma. -/
theorem bytesStoreLiteChunksLengthAfterSstore_ne
    (σ : AccountMap) (I : ExecutionEnv) (slot val : UInt256)
    (hne : (⟨1⟩ : UInt256) ≠ slot) :
    bytesStoreLiteChunksLengthWord (sstoreAccountMap I.codeOwner σ slot val) I =
      bytesStoreLiteChunksLengthWord σ I := by
  rw [bytesStoreLiteChunksLengthAfterSstore_eq_if σ I slot val, if_neg hne]

theorem bytesStoreLiteChunksLengthAfterSstore_eq_if_of_before
    {σ : AccountMap} {I : ExecutionEnv} {slot val word : UInt256}
    (hword : bytesStoreLiteChunksLengthWord σ I = word) :
    bytesStoreLiteChunksLengthWord (sstoreAccountMap I.codeOwner σ slot val) I =
      if (⟨1⟩ : UInt256) = slot then
        ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256) (fun _ => val))
      else
        word := by
  rw [bytesStoreLiteChunksLengthAfterSstore_eq_if, hword]

def bytesStoreLiteClearDataWordsHitsLength (base idx : UInt256) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
      if (⟨1⟩ : UInt256) = base + idx then
        true
      else
        bytesStoreLiteClearDataWordsHitsLength base ((⟨1⟩ : UInt256) + idx) fuel

/-- Reading `chunks.length` after a clear loop, with collision behavior explicit. -/
theorem bytesStoreLiteChunksLengthAfterClearDataWordsForwardFrom_eq_if
    (σ : AccountMap) (I : ExecutionEnv) (base idx : UInt256) :
    ∀ fuel,
      bytesStoreLiteChunksLengthWord
          (clearDataWordsForwardFrom I.codeOwner σ base idx fuel) I =
        if bytesStoreLiteClearDataWordsHitsLength base idx fuel then
          (⟨0⟩ : UInt256)
        else
          bytesStoreLiteChunksLengthWord σ I
  | 0 => by
      simp [clearDataWordsForwardFrom, bytesStoreLiteClearDataWordsHitsLength]
  | fuel + 1 => by
      simp [clearDataWordsForwardFrom, bytesStoreLiteClearDataWordsHitsLength]
      by_cases hslot : (⟨1⟩ : UInt256) = base + idx
      · simp [hslot]
        rw [bytesStoreLiteChunksLengthAfterClearDataWordsForwardFrom_eq_if
          (sstoreAccountMap I.codeOwner σ (base + idx) ⟨0⟩) I base
          ((base + idx) + idx) fuel]
        cases bytesStoreLiteClearDataWordsHitsLength base ((base + idx) + idx) fuel
        · simp [bytesStoreLiteChunksLengthAfterSstore_eq_if, hslot]
          cases σ.find? I.codeOwner <;> rfl
        · simp
      · simp [hslot]
        rw [bytesStoreLiteChunksLengthAfterClearDataWordsForwardFrom_eq_if
          (sstoreAccountMap I.codeOwner σ (base + idx) ⟨0⟩) I base
          ((⟨1⟩ : UInt256) + idx) fuel]
        cases bytesStoreLiteClearDataWordsHitsLength base ((⟨1⟩ : UInt256) + idx) fuel
        · simp [bytesStoreLiteChunksLengthAfterSstore_ne σ I (base + idx) ⟨0⟩ hslot]
        · simp

theorem bytesStoreLiteChunksLengthAfterClearDataWordsForwardFrom_eq_of_hits_false
    (σ : AccountMap) (I : ExecutionEnv) (base idx : UInt256) (fuel : Nat)
    (hhits : bytesStoreLiteClearDataWordsHitsLength base idx fuel = false) :
    bytesStoreLiteChunksLengthWord
        (clearDataWordsForwardFrom I.codeOwner σ base idx fuel) I =
      bytesStoreLiteChunksLengthWord σ I := by
  rw [bytesStoreLiteChunksLengthAfterClearDataWordsForwardFrom_eq_if]
  simp [hhits]

theorem bytesStoreLiteChunksLengthAfterClearDataWordsForwardFrom_eq_of_hits_true
    (σ : AccountMap) (I : ExecutionEnv) (base idx : UInt256) (fuel : Nat)
    (hhits : bytesStoreLiteClearDataWordsHitsLength base idx fuel = true) :
    bytesStoreLiteChunksLengthWord
        (clearDataWordsForwardFrom I.codeOwner σ base idx fuel) I =
      (⟨0⟩ : UInt256) := by
  rw [bytesStoreLiteChunksLengthAfterClearDataWordsForwardFrom_eq_if]
  simp [hhits]

theorem bytesStoreLiteClearDataWordsHitsLength_false_of_disjoint
    (base idx : UInt256) :
    ∀ fuel,
      (∀ i, i < fuel →
        base + BytesStoreLiteCore.clearDataWordsLoopIndex idx i ≠ (⟨1⟩ : UInt256)) →
      bytesStoreLiteClearDataWordsHitsLength base idx fuel = false
  | 0, _ => by
      simp [bytesStoreLiteClearDataWordsHitsLength]
  | fuel + 1, hdisjoint => by
      simp [bytesStoreLiteClearDataWordsHitsLength]
      have hhead : ¬ (⟨1⟩ : UInt256) = base + idx := by
        exact (hdisjoint 0 (Nat.zero_lt_succ fuel)).symm
      simp [hhead]
      apply bytesStoreLiteClearDataWordsHitsLength_false_of_disjoint
      intro i hi
      have hne := hdisjoint (i + 1) (Nat.succ_lt_succ hi)
      simpa [BytesStoreLiteCore.clearDataWordsLoopIndex,
        BytesStoreLiteCore.clearDataWordsLoopIndex_succ_base] using hne

def bytesStoreLiteCalldataLongDataWord (I : ExecutionEnv)
    (payloadStart stride : UInt256) : Nat → UInt256
  | n =>
      uInt256OfByteArray
        (I.calldata.readBytes
          (payloadStart + BytesStoreLiteCore.longDataWordsLoopStride stride n).toNat 32)

def bytesStoreLiteCalldataLongDataForwardFrom (owner : AccountAddress) (τ : AccountMap)
    (slot payloadStart stride : UInt256) (I : ExecutionEnv) : Nat → AccountMap
  | 0 => τ
  | n + 1 =>
      bytesStoreLiteCalldataLongDataForwardFrom owner
        (sstoreAccountMap owner τ slot
          (bytesStoreLiteCalldataLongDataWord I payloadStart stride 0))
        ((⟨1⟩ : UInt256) + slot) payloadStart ((⟨32⟩ : UInt256) + stride) I n

theorem bytesStoreLiteCalldataLongDataWord_succ_base (I : ExecutionEnv)
    (payloadStart stride : UInt256) :
    ∀ i,
      bytesStoreLiteCalldataLongDataWord I payloadStart ((⟨32⟩ : UInt256) + stride) i =
        bytesStoreLiteCalldataLongDataWord I payloadStart stride (i + 1)
  | 0 => by
      simp [bytesStoreLiteCalldataLongDataWord, BytesStoreLiteCore.longDataWordsLoopStride]
  | i + 1 => by
      simp [bytesStoreLiteCalldataLongDataWord, BytesStoreLiteCore.longDataWordsLoopStride,
        BytesStoreLiteCore.longDataWordsLoopStride_succ_base]

def bytesStoreLiteLongDataWordsHitsLength : UInt256 → Nat → Bool
  | _, 0 => false
  | slot, fuel + 1 =>
      if (⟨1⟩ : UInt256) = slot then
        true
      else
        bytesStoreLiteLongDataWordsHitsLength ((⟨1⟩ : UInt256) + slot) fuel

theorem bytesStoreLiteLongDataWordsLoopSlot_add (slot : UInt256) :
    ∀ start i,
      BytesStoreLiteCore.longDataWordsLoopSlot
          (BytesStoreLiteCore.longDataWordsLoopSlot slot start) i =
        BytesStoreLiteCore.longDataWordsLoopSlot slot (start + i)
  | start, 0 => by
      simp [BytesStoreLiteCore.longDataWordsLoopSlot]
  | start, i + 1 => by
      have hnat : start + (i + 1) = start + i + 1 := by omega
      rw [hnat]
      simp [BytesStoreLiteCore.longDataWordsLoopSlot,
        bytesStoreLiteLongDataWordsLoopSlot_add slot start i]

theorem bytesStoreLiteLongDataWordsHitsLength_false_of_disjoint
    (slot : UInt256) :
    ∀ fuel,
      (∀ i, i < fuel →
        BytesStoreLiteCore.longDataWordsLoopSlot slot i ≠ (⟨1⟩ : UInt256)) →
      bytesStoreLiteLongDataWordsHitsLength slot fuel = false
  | 0, _ => by
      simp [bytesStoreLiteLongDataWordsHitsLength]
  | fuel + 1, hdisjoint => by
      simp [bytesStoreLiteLongDataWordsHitsLength]
      have hhead : ¬ (⟨1⟩ : UInt256) = slot := by
        exact (hdisjoint 0 (Nat.zero_lt_succ fuel)).symm
      simp [hhead]
      apply bytesStoreLiteLongDataWordsHitsLength_false_of_disjoint
      intro i hi
      have hne := hdisjoint (i + 1) (Nat.succ_lt_succ hi)
      simpa [BytesStoreLiteCore.longDataWordsLoopSlot,
        BytesStoreLiteCore.longDataWordsLoopSlot_succ_base] using hne

theorem bytesStoreLiteChunksLengthAfterClearChunkDataSuffix_of_hits_false
    (σ : AccountMap) (I : ExecutionEnv) (chunkIndex start count : UInt256)
    (hhits : bytesStoreLiteClearDataWordsHitsLength
      (start + bytesLikeDataBase (chunksDataBase + chunkIndex)) ⟨0⟩ count.toNat = false) :
    bytesStoreLiteChunksLengthWord
        (clearDataWordsForwardFrom I.codeOwner σ
          (start + bytesLikeDataBase (chunksDataBase + chunkIndex)) ⟨0⟩ count.toNat)
        I =
      bytesStoreLiteChunksLengthWord σ I := by
  exact bytesStoreLiteChunksLengthAfterClearDataWordsForwardFrom_eq_of_hits_false σ I
    (start + bytesLikeDataBase (chunksDataBase + chunkIndex)) ⟨0⟩ count.toNat hhits

theorem bytesStoreLiteChunksLengthAfterLongDataTail_of_ne
    (σ : AccountMap) (I : ExecutionEnv) (slot tailWord : UInt256)
    (hne : (⟨1⟩ : UInt256) ≠ slot) :
    bytesStoreLiteChunksLengthWord
      (sstoreAccountMap I.codeOwner σ slot tailWord) I =
      bytesStoreLiteChunksLengthWord σ I := by
  exact bytesStoreLiteChunksLengthAfterSstore_ne σ I slot tailWord hne

theorem bytesStoreLiteChunksLengthAfterCalldataLongDataFromLoop
    (σ : AccountMap) (I : ExecutionEnv) (slot payloadStart stride : UInt256)
    (fuel : Nat)
    (hhits : bytesStoreLiteLongDataWordsHitsLength slot fuel = false) :
    bytesStoreLiteChunksLengthWord
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          slot payloadStart stride I fuel) I =
      bytesStoreLiteChunksLengthWord σ I := by
  induction fuel generalizing σ slot stride with
  | zero =>
      simp [bytesStoreLiteCalldataLongDataForwardFrom]
  | succ fuel ih =>
      simp [bytesStoreLiteCalldataLongDataForwardFrom]
      have hhead : ¬ (⟨1⟩ : UInt256) = slot := by
        by_cases h : (⟨1⟩ : UInt256) = slot
        · simp [bytesStoreLiteLongDataWordsHitsLength, h] at hhits
        · exact h
      have htail :
          bytesStoreLiteLongDataWordsHitsLength ((⟨1⟩ : UInt256) + slot) fuel = false := by
        simpa [bytesStoreLiteLongDataWordsHitsLength, hhead] using hhits
      rw [ih
        (σ := sstoreAccountMap I.codeOwner σ slot
          (bytesStoreLiteCalldataLongDataWord I payloadStart stride 0))
        (slot := (⟨1⟩ : UInt256) + slot)
        (stride := (⟨32⟩ : UInt256) + stride)
        htail]
      exact bytesStoreLiteChunksLengthAfterSstore_ne σ I slot
        (bytesStoreLiteCalldataLongDataWord I payloadStart stride 0) hhead

theorem bytesStoreLiteChunksLengthAfterChunkHeaderSstore_eq_if
    (σ : AccountMap) (I : ExecutionEnv) (chunkIndex val : UInt256) :
    bytesStoreLiteChunksLengthWord
        (sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) val) I =
      if (⟨1⟩ : UInt256) = chunksDataBase + chunkIndex then
        ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256) (fun _ => val))
      else
        bytesStoreLiteChunksLengthWord σ I := by
  exact bytesStoreLiteChunksLengthAfterSstore_eq_if σ I (chunksDataBase + chunkIndex) val

theorem bytesStoreLiteChunksLengthAfterChunkHeaderSstore_ne_of_ne
    (σ : AccountMap) (I : ExecutionEnv) (chunkIndex val : UInt256)
    (hne : (⟨1⟩ : UInt256) ≠ chunksDataBase + chunkIndex) :
    bytesStoreLiteChunksLengthWord
        (sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) val) I =
      bytesStoreLiteChunksLengthWord σ I := by
  rw [bytesStoreLiteChunksLengthAfterChunkHeaderSstore_eq_if]
  exact if_neg hne

theorem bytesStoreLiteChunksLengthAfterChunkHeaderSstore_eq_if_of_before
    {σ : AccountMap} {I : ExecutionEnv} {chunkIndex val word : UInt256}
    (hword : bytesStoreLiteChunksLengthWord σ I = word) :
    bytesStoreLiteChunksLengthWord
        (sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) val) I =
      if (⟨1⟩ : UInt256) = chunksDataBase + chunkIndex then
        ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256) (fun _ => val))
      else
        word := by
  exact bytesStoreLiteChunksLengthAfterSstore_eq_if_of_before hword

theorem bytesStoreLiteChunkBoundAfterChunkHeaderSstore_of_ne
    {σ : AccountMap} {I : ExecutionEnv} {chunkIndex val : UInt256}
    (hne : (⟨1⟩ : UInt256) ≠ chunksDataBase + chunkIndex)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat) :
    chunkIndex.toNat <
      (bytesStoreLiteChunksLengthWord
        (sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) val) I).toNat := by
  rw [bytesStoreLiteChunksLengthAfterChunkHeaderSstore_ne_of_ne σ I chunkIndex val hne]
  exact hbound

theorem bytesStoreLiteChunkBoundAfterChunkHeaderSstore_of_post_bound
    {σ : AccountMap} {I : ExecutionEnv} {chunkIndex val : UInt256}
    (hbound :
      chunkIndex.toNat <
        (if (⟨1⟩ : UInt256) = chunksDataBase + chunkIndex then
          ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256) (fun _ => val))
        else
          bytesStoreLiteChunksLengthWord σ I).toNat) :
    chunkIndex.toNat <
      (bytesStoreLiteChunksLengthWord
        (sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) val) I).toNat := by
  rw [bytesStoreLiteChunksLengthAfterChunkHeaderSstore_eq_if]
  exact hbound

theorem bytesStoreLiteChunkBoundAfterChunkHeaderSstore_of_length_eq_of_ne
    {σ σ₀ : AccountMap} {I : ExecutionEnv} {chunkIndex val : UInt256}
    (hne : (⟨1⟩ : UInt256) ≠ chunksDataBase + chunkIndex)
    (hlen : bytesStoreLiteChunksLengthWord σ I = bytesStoreLiteChunksLengthWord σ₀ I)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ₀ I).toNat) :
    chunkIndex.toNat <
      (bytesStoreLiteChunksLengthWord
        (sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) val) I).toNat := by
  exact bytesStoreLiteChunkBoundAfterChunkHeaderSstore_of_ne
    (σ := σ) (I := I) (chunkIndex := chunkIndex) (val := val) hne
    (by rw [hlen]; exact hbound)

theorem bytesStoreLiteChunksLengthAfterChunkDataSstore_eq_if
    (σ : AccountMap) (I : ExecutionEnv) (chunkIndex idx val : UInt256) :
    bytesStoreLiteChunksLengthWord
        (sstoreAccountMap I.codeOwner σ
          (bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) val) I =
      if (⟨1⟩ : UInt256) =
          bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩ then
        ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256) (fun _ => val))
      else
        bytesStoreLiteChunksLengthWord σ I := by
  exact bytesStoreLiteChunksLengthAfterSstore_eq_if σ I
    (bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) val

theorem bytesStoreLiteChunksLengthAfterChunkDataSstore_ne_of_ne
    (σ : AccountMap) (I : ExecutionEnv) (chunkIndex idx val : UInt256)
    (hne : (⟨1⟩ : UInt256) ≠
      bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) :
    bytesStoreLiteChunksLengthWord
        (sstoreAccountMap I.codeOwner σ
          (bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) val) I =
      bytesStoreLiteChunksLengthWord σ I := by
  rw [bytesStoreLiteChunksLengthAfterChunkDataSstore_eq_if]
  exact if_neg hne

theorem bytesStoreLiteChunksLengthAfterChunkDataSstore_eq_if_of_before
    {σ : AccountMap} {I : ExecutionEnv} {chunkIndex idx val word : UInt256}
    (hword : bytesStoreLiteChunksLengthWord σ I = word) :
    bytesStoreLiteChunksLengthWord
        (sstoreAccountMap I.codeOwner σ
          (bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) val) I =
      if (⟨1⟩ : UInt256) =
          bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩ then
        ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256) (fun _ => val))
      else
        word := by
  exact bytesStoreLiteChunksLengthAfterSstore_eq_if_of_before hword

theorem bytesStoreLiteChunkBoundAfterChunkDataSstore_of_ne
    {σ : AccountMap} {I : ExecutionEnv} {chunkIndex idx val : UInt256}
    (hne : (⟨1⟩ : UInt256) ≠
      bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩)
    (hbound : chunkIndex.toNat < (bytesStoreLiteChunksLengthWord σ I).toNat) :
    chunkIndex.toNat <
      (bytesStoreLiteChunksLengthWord
        (sstoreAccountMap I.codeOwner σ
          (bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) val) I).toNat := by
  rw [bytesStoreLiteChunksLengthAfterChunkDataSstore_ne_of_ne σ I chunkIndex idx val hne]
  exact hbound

theorem bytesStoreLiteChunkBoundAfterChunkDataSstore_of_post_bound
    {σ : AccountMap} {I : ExecutionEnv} {chunkIndex idx val : UInt256}
    (hbound :
      chunkIndex.toNat <
        (if (⟨1⟩ : UInt256) =
            bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩ then
          ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256) (fun _ => val))
        else
          bytesStoreLiteChunksLengthWord σ I).toNat) :
    chunkIndex.toNat <
      (bytesStoreLiteChunksLengthWord
        (sstoreAccountMap I.codeOwner σ
          (bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) val) I).toNat := by
  rw [bytesStoreLiteChunksLengthAfterChunkDataSstore_eq_if]
  exact hbound

theorem bytesStoreLiteStorageLoadChunksLengthAfterChunkHeaderStore_eq_if
    (evm : EVM.State) (chunkIndex val : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (chunksDataBase + chunkIndex) val)
        evm.executionEnv.codeOwner ⟨1⟩ =
      if (⟨1⟩ : UInt256) = chunksDataBase + chunkIndex then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ := by
  exact bytesStoreLiteStorageLoadAfterStorageStore_eq_if evm ⟨1⟩ (chunksDataBase + chunkIndex) val

theorem bytesStoreLiteStorageLoadChunksLengthAfterChunkHeaderStore_ne_of_ne
    (evm : EVM.State) (chunkIndex val : UInt256)
    (hne : (⟨1⟩ : UInt256) ≠ chunksDataBase + chunkIndex) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (chunksDataBase + chunkIndex) val)
        evm.executionEnv.codeOwner ⟨1⟩ =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ := by
  rw [bytesStoreLiteStorageLoadChunksLengthAfterChunkHeaderStore_eq_if]
  exact if_neg hne

theorem bytesStoreLiteStorageLoadChunksLengthAfterChunkHeaderStore_eq_if_of_before
    {evm : EVM.State} {chunkIndex val word : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = word) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (chunksDataBase + chunkIndex) val)
        evm.executionEnv.codeOwner ⟨1⟩ =
      if (⟨1⟩ : UInt256) = chunksDataBase + chunkIndex then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        word := by
  exact bytesStoreLiteStorageLoadAfterStorageStore_eq_if_of_before hload

theorem bytesStoreLiteStorageLoadChunksLengthAfterChunkHeaderStore_eq_of_before_of_ne
    {evm : EVM.State} {chunkIndex val word : UInt256}
    (hne : (⟨1⟩ : UInt256) ≠ chunksDataBase + chunkIndex)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = word) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner (chunksDataBase + chunkIndex) val)
        evm.executionEnv.codeOwner ⟨1⟩ =
      word := by
  rw [bytesStoreLiteStorageLoadChunksLengthAfterChunkHeaderStore_eq_if_of_before hload]
  exact if_neg hne

theorem bytesStoreLiteStorageLoadChunksLengthAfterChunkDataStore_eq_if
    (evm : EVM.State) (chunkIndex idx val : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) val)
        evm.executionEnv.codeOwner ⟨1⟩ =
      if (⟨1⟩ : UInt256) =
          bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩ then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ := by
  exact bytesStoreLiteStorageLoadAfterStorageStore_eq_if evm ⟨1⟩
    (bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) val

theorem bytesStoreLiteStorageLoadChunksLengthAfterChunkDataStore_ne_of_ne
    (evm : EVM.State) (chunkIndex idx val : UInt256)
    (hne : (⟨1⟩ : UInt256) ≠
      bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) val)
        evm.executionEnv.codeOwner ⟨1⟩ =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ := by
  rw [bytesStoreLiteStorageLoadChunksLengthAfterChunkDataStore_eq_if]
  exact if_neg hne

theorem bytesStoreLiteStorageLoadChunksLengthAfterChunkDataStore_eq_if_of_before
    {evm : EVM.State} {chunkIndex idx val word : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = word) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) val)
        evm.executionEnv.codeOwner ⟨1⟩ =
      if (⟨1⟩ : UInt256) =
          bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩ then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        word := by
  exact bytesStoreLiteStorageLoadAfterStorageStore_eq_if_of_before hload

theorem bytesStoreLiteStorageLoadChunksLengthAfterChunkDataStore_eq_of_before_of_ne
    {evm : EVM.State} {chunkIndex idx val word : UInt256}
    (hne : (⟨1⟩ : UInt256) ≠
      bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ = word) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) val)
        evm.executionEnv.codeOwner ⟨1⟩ =
      word := by
  rw [bytesStoreLiteStorageLoadChunksLengthAfterChunkDataStore_eq_if_of_before hload]
  exact if_neg hne

theorem bytesStoreLiteChunkHeaderWordAfterLengthSstore_eq_if
    (σ : AccountMap) (I : ExecutionEnv) (oldLen val : UInt256) :
    ((sstoreAccountMap I.codeOwner σ ⟨1⟩ val).find? I.codeOwner |>.option
        (default : UInt256)
        (fun acc => acc.storage.findD (chunksDataBase + oldLen) (default : UInt256))) =
      if chunksDataBase + oldLen = (⟨1⟩ : UInt256) then
        ((σ.find? I.codeOwner).option (default : UInt256) (fun _ => val))
      else
        (σ.find? I.codeOwner |>.option (default : UInt256)
          (fun acc => acc.storage.findD (chunksDataBase + oldLen) (default : UInt256))) := by
  exact bytesStoreLiteStorageWordAfterSstore_eq_if σ I (chunksDataBase + oldLen) ⟨1⟩ val

theorem bytesStoreLiteChunkHeaderWordAfterLengthSstore_ne_of_ne
    (σ : AccountMap) (I : ExecutionEnv) (oldLen val : UInt256)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256)) :
    ((sstoreAccountMap I.codeOwner σ ⟨1⟩ val).find? I.codeOwner |>.option
        (default : UInt256)
        (fun acc => acc.storage.findD (chunksDataBase + oldLen) (default : UInt256))) =
      (σ.find? I.codeOwner |>.option (default : UInt256)
        (fun acc => acc.storage.findD (chunksDataBase + oldLen) (default : UInt256))) := by
  rw [bytesStoreLiteChunkHeaderWordAfterLengthSstore_eq_if]
  exact if_neg hne

theorem bytesStoreLiteChunkHeaderWordAfterLengthSstore_eq_if_of_before
    {σ : AccountMap} {I : ExecutionEnv} {oldLen val word : UInt256}
    (hword :
      (σ.find? I.codeOwner |>.option (default : UInt256)
        (fun acc => acc.storage.findD (chunksDataBase + oldLen) (default : UInt256))) = word) :
    ((sstoreAccountMap I.codeOwner σ ⟨1⟩ val).find? I.codeOwner |>.option
        (default : UInt256)
        (fun acc => acc.storage.findD (chunksDataBase + oldLen) (default : UInt256))) =
      if chunksDataBase + oldLen = (⟨1⟩ : UInt256) then
        ((σ.find? I.codeOwner).option (default : UInt256) (fun _ => val))
      else
        word := by
  exact bytesStoreLiteStorageWordAfterSstore_eq_if_of_before hword

theorem bytesStoreLiteChunkHeaderWordAfterLengthSstore_eq_of_before_of_ne
    {σ : AccountMap} {I : ExecutionEnv} {oldLen val word : UInt256}
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hword :
      (σ.find? I.codeOwner |>.option (default : UInt256)
        (fun acc => acc.storage.findD (chunksDataBase + oldLen) (default : UInt256))) = word) :
    ((sstoreAccountMap I.codeOwner σ ⟨1⟩ val).find? I.codeOwner |>.option
        (default : UInt256)
        (fun acc => acc.storage.findD (chunksDataBase + oldLen) (default : UInt256))) =
      word := by
  rw [bytesStoreLiteChunkHeaderWordAfterLengthSstore_eq_if_of_before hword]
  exact if_neg hne

theorem bytesStoreLiteStorageLoadChunkHeaderAfterLengthStore_eq_if
    (evm : EVM.State) (oldLen val : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ val)
        evm.executionEnv.codeOwner (chunksDataBase + oldLen) =
      if chunksDataBase + oldLen = (⟨1⟩ : UInt256) then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) := by
  exact bytesStoreLiteStorageLoadAfterStorageStore_eq_if evm (chunksDataBase + oldLen) ⟨1⟩ val

theorem bytesStoreLiteStorageLoadChunkHeaderAfterLengthStore_ne_of_ne
    (evm : EVM.State) (oldLen val : UInt256)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256)) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ val)
        evm.executionEnv.codeOwner (chunksDataBase + oldLen) =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) := by
  rw [bytesStoreLiteStorageLoadChunkHeaderAfterLengthStore_eq_if]
  exact if_neg hne

theorem bytesStoreLiteStorageLoadChunkHeaderAfterLengthStore_eq_if_of_before
    {evm : EVM.State} {oldLen val word : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = word) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ val)
        evm.executionEnv.codeOwner (chunksDataBase + oldLen) =
      if chunksDataBase + oldLen = (⟨1⟩ : UInt256) then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        word := by
  exact bytesStoreLiteStorageLoadAfterStorageStore_eq_if_of_before hload

theorem bytesStoreLiteStorageLoadChunkHeaderAfterLengthStore_eq_of_before_of_ne
    {evm : EVM.State} {oldLen val word : UInt256}
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = word) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ val)
        evm.executionEnv.codeOwner (chunksDataBase + oldLen) =
      word := by
  rw [bytesStoreLiteStorageLoadChunkHeaderAfterLengthStore_eq_if_of_before hload]
  exact if_neg hne

theorem bytesStoreLiteEmptyChunkHeaderAfterLengthStore_eq_if {evm : EVM.State} (oldLen : UInt256)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = ⟨0⟩) :
    Solm.EVM.storageLoad
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
      evm.executionEnv.codeOwner (chunksDataBase + oldLen) =
        if chunksDataBase + oldLen = (⟨1⟩ : UInt256) then
          (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
            (fun _ => oldLen + ⟨1⟩)
        else
          ⟨0⟩ := by
  exact bytesStoreLiteStorageLoadChunkHeaderAfterLengthStore_eq_if_of_before hload

theorem bytesStoreLiteEmptyChunkHeaderAfterLengthStore_of_ne {evm : EVM.State} (oldLen : UInt256)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = ⟨0⟩) :
    Solm.EVM.storageLoad
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
      evm.executionEnv.codeOwner (chunksDataBase + oldLen) = ⟨0⟩ := by
  rw [bytesStoreLiteEmptyChunkHeaderAfterLengthStore_eq_if oldLen hload]
  exact if_neg hne

theorem bytesStoreLiteChunkHeaderAfterLengthStore_eq_if {evm : EVM.State} (oldLen header : UInt256)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header) :
    Solm.EVM.storageLoad
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
      evm.executionEnv.codeOwner (chunksDataBase + oldLen) =
        if chunksDataBase + oldLen = (⟨1⟩ : UInt256) then
          (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
            (fun _ => oldLen + ⟨1⟩)
        else
          header := by
  exact bytesStoreLiteStorageLoadChunkHeaderAfterLengthStore_eq_if_of_before hload

theorem bytesStoreLiteChunkHeaderAfterLengthStore_of_ne {evm : EVM.State} (oldLen header : UInt256)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header) :
    Solm.EVM.storageLoad
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
      evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header := by
  rw [bytesStoreLiteChunkHeaderAfterLengthStore_eq_if oldLen header hload]
  exact if_neg hne

theorem bytesStoreLitePushChunkHeaderAfterLengthStore_eq_if {σ : AccountMap} {I : ExecutionEnv}
    (oldLen : UInt256) :
    ((sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)).find? I.codeOwner |>.option
        ⟨0⟩ (fun acc => acc.storage.findD (chunksDataBase + oldLen) ⟨0⟩)) =
      if chunksDataBase + oldLen = (⟨1⟩ : UInt256) then
        ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256) (fun _ => oldLen + ⟨1⟩))
      else
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + oldLen) ⟨0⟩)) := by
  exact bytesStoreLiteChunkHeaderWordAfterLengthSstore_eq_if_of_before (by rfl)

theorem bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne {σ : AccountMap} {I : ExecutionEnv}
    (oldLen : UInt256) (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256)) :
    ((sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)).find? I.codeOwner |>.option
        ⟨0⟩ (fun acc => acc.storage.findD (chunksDataBase + oldLen) ⟨0⟩)) =
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (chunksDataBase + oldLen) ⟨0⟩)) := by
  rw [bytesStoreLitePushChunkHeaderAfterLengthStore_eq_if]
  exact if_neg hne

theorem bytesStoreLitePushChunkHeaderAfterLengthStoreZero_of_ne
    {σ : AccountMap} {I : ExecutionEnv} (oldLen : UInt256)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hzero :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (chunksDataBase + oldLen) ⟨0⟩)) = ⟨0⟩) :
    ((sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)).find? I.codeOwner |>.option
        ⟨0⟩ (fun acc => acc.storage.findD (chunksDataBase + oldLen) ⟨0⟩)) = ⟨0⟩ := by
  exact (bytesStoreLitePushChunkHeaderAfterLengthStore_of_ne (σ := σ) (I := I) oldLen hne).trans
    hzero

end BytesStoreLite
