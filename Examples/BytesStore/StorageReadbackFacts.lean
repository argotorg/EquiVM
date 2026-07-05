import Examples.BytesStore.Spec
import Examples.StringStoreLite.SetLong
import Reasoning.Refinement
import Reasoning.Storage

/-!
# BytesStore storage readback facts

Small collision-aware readback wrappers for owner storage writes.  These facts intentionally expose
the aliasing branch instead of assuming Solidity storage-layout separation.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace BytesStore

def bytesStoreChunksLengthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)

theorem bytesStoreChunksLengthWord_eq_of_accountMapEquiv {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreChunksLengthWord σ_evm I = bytesStoreChunksLengthWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩

theorem accountMapEquiv_bytesHeaderStore {σ : AccountMap} {evm : EVM.State}
    (owner : AccountAddress) (slot header : UInt256)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    accountMapEquiv
      (sstoreAccountMap owner σ slot header)
      (Solm.EVM.storageStore evm owner slot header).accountMap := by
  exact accountMapEquiv_storageStore_of_accountMapEquiv hAccounts owner slot header

theorem accountMapEquiv_bytesHeaderAndTagStore {σ : AccountMap} {evm : EVM.State}
    (owner : AccountAddress) (headerSlot header tagSlot tag : UInt256)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    accountMapEquiv
      (sstoreAccountMap owner
        (sstoreAccountMap owner σ headerSlot header) tagSlot tag)
      (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm owner headerSlot header)
        owner tagSlot tag).accountMap := by
  exact accountMapEquiv_storageStore_two_of_accountMapEquiv hAccounts owner owner
    headerSlot header tagSlot tag

set_option maxHeartbeats 8000000 in
theorem accountMapEquiv_pushChunkLengthIncrement {σ_evm σ_solm : AccountMap}
    (I : ExecutionEnv) (oldLen : UInt256)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩))
      (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩)) := by
  exact accountMapEquiv_sstoreAccountMap_sameOwner I.codeOwner ⟨1⟩
    (oldLen + ⟨1⟩) hAccounts

theorem accountMapEquiv_pushChunkWordStorage {σ_evm σ_solm : AccountMap}
    (I : ExecutionEnv) (oldLen valueWord : UInt256)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩))
        (chunksDataBase + oldLen) valueWord)
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
        (chunksDataBase + oldLen) valueWord) := by
  exact accountMapEquiv_sstoreAccountMap_sameOwner_two I.codeOwner
    ⟨1⟩ (oldLen + ⟨1⟩) (chunksDataBase + oldLen) valueWord hAccounts

theorem accountMapEquiv_pushChunkEmptyStorage {σ_evm σ_solm : AccountMap}
    (I : ExecutionEnv) (oldLen : UInt256)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩))
        (chunksDataBase + oldLen) ⟨0⟩)
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
        (chunksDataBase + oldLen) ⟨0⟩) := by
  exact accountMapEquiv_pushChunkWordStorage I oldLen ⟨0⟩ hAccounts

theorem accountMapEquiv_pushChunkShortStorage {σ_evm σ_solm : AccountMap}
    (I : ExecutionEnv) (oldLen valueWord : UInt256)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ (oldLen + ⟨1⟩))
        (chunksDataBase + oldLen) valueWord)
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ_solm ⟨1⟩ (oldLen + ⟨1⟩))
        (chunksDataBase + oldLen) valueWord) := by
  exact accountMapEquiv_pushChunkWordStorage I oldLen valueWord hAccounts

theorem bytesStoreStorageLoad_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (slot : UInt256) (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner slot =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD slot ⟨0⟩)) := by
  exact storageLoad_initState_codeOwner_of_accountMapEquiv slot hAccounts

theorem bytesStoreAccountMapEquiv_storageStore_initState
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) (slot val : UInt256) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner σ_evm slot val)
      (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner slot val).accountMap := by
  exact accountMapEquiv_storageStore_initState_codeOwner hAccounts slot val

def bytesStoreCurrentLengthHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

theorem bytesStoreCurrentLengthHeaderWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreCurrentLengthHeaderWord σ_evm I =
      bytesStoreCurrentLengthHeaderWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩

theorem bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner ⟨0⟩ =
      bytesStoreCurrentLengthHeaderWord σ_evm I := by
  simpa [bytesStoreCurrentLengthHeaderWord] using
    bytesStoreStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) ⟨0⟩ hAccounts

theorem bytesStoreStorageLoadCurrentLength_of_accountMapEquiv
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ =
      bytesStoreCurrentLengthHeaderWord σ I := by
  exact (accountStorageWord_eq_storageLoad_of_accountMapEquiv
    (owner := I.codeOwner) (slot := (⟨0⟩ : UInt256)) howner hAccounts).symm

theorem bytesStoreReadLengthAfterHeaderStoreZero
    {er : EvaledStorageRef} {evm evmData : EVM.State} {baseSlot : UInt256}
    (hevmData :
      evmData = Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot ⟨0⟩)
    (hbase :
      ∃ loc, bytesStoreLayout { er with steps := er.steps ++ [.length] } evmData =
        some loc ∧ loc.slot = baseSlot) :
    readStorageBytesLength? bytesStoreConfig evmData er = .ok 0 := by
  subst evmData
  exact readStorageBytesLength?_ok_of_layout_after_storageStore_zero
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (er := er) (evm := evm) (baseSlot := baseSlot) (by rfl) hbase

theorem bytesStoreReadLengthAfterHeaderStorePresent
    {er : EvaledStorageRef} {evm evmData : EVM.State} {baseSlot header : UInt256}
    {len : Nat} {acc : Account}
    (hevmData :
      evmData = Solm.EVM.storageStore evm evm.executionEnv.codeOwner baseSlot header)
    (hbase :
      ∃ loc, bytesStoreLayout { er with steps := er.steps ++ [.length] } evmData =
        some loc ∧ loc.slot = baseSlot)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hdecode : solidityDecodeBytesLengthHeader header = .ok len) :
    readStorageBytesLength? bytesStoreConfig evmData er = .ok len := by
  subst evmData
  exact readStorageBytesLength?_ok_of_layout_after_storageStore_present
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (er := er) (evm := evm) (baseSlot := baseSlot) (header := header) (len := len)
    (by rfl) hbase hacc hdecode

theorem bytesStoreReadLengthOfHeaderLoad
    {er : EvaledStorageRef} {evm : EVM.State} {baseSlot header : UInt256} {len : Nat}
    (hbase :
      ∃ loc, bytesStoreLayout { er with steps := er.steps ++ [.length] } evm =
        some loc ∧ loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hdecode : solidityDecodeBytesLengthHeader header = .ok len) :
    readStorageBytesLength? bytesStoreConfig evm er = .ok len := by
  exact readStorageBytesLength?_ok_of_layout
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (er := er) (evm := evm) (baseSlot := baseSlot) (header := header) (len := len)
    (by rfl) hbase hload hdecode

theorem bytesStoreReadLengthZeroOfHeaderLoad
    {er : EvaledStorageRef} {evm : EVM.State} {baseSlot : UInt256}
    (hbase :
      ∃ loc, bytesStoreLayout { er with steps := er.steps ++ [.length] } evm =
        some loc ∧ loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = ⟨0⟩) :
    readStorageBytesLength? bytesStoreConfig evm er = .ok 0 := by
  exact bytesStoreReadLengthOfHeaderLoad
    (er := er) (evm := evm) (baseSlot := baseSlot)
    (header := (⟨0⟩ : UInt256)) (len := 0)
    hbase hload solidityDecodeBytesLengthHeader_zero

theorem bytesStoreReadLengthRevertOfHeaderLoad
    {er : EvaledStorageRef} {evm : EVM.State} {baseSlot header : UInt256}
    (hbase :
      ∃ loc, bytesStoreLayout { er with steps := er.steps ++ [.length] } evm =
        some loc ∧ loc.slot = baseSlot)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot = header)
    (hdecode : solidityDecodeBytesLengthHeader header = .revert) :
    readStorageBytesLength? bytesStoreConfig evm er = .revert := by
  exact readStorageBytesLength?_revert_of_layout
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (er := er) (evm := evm) (baseSlot := baseSlot) (header := header)
    (by rfl) hbase hload hdecode

theorem bytesStoreReadCurrentLengthLong_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ g A I) { base := "current" } =
      .ok (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩).toNat := by
  exact readStorageBytesLength?_ok_of_layout
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (er := { base := "current" })
    (evm := initState cA gh bl σ_solm σ₀ g A I) (baseSlot := ⟨0⟩)
    (header := bytesStoreCurrentLengthHeaderWord σ_evm I)
    (len := (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩).toNat)
    (by rfl)
    (by simp [bytesStoreLayout])
    (by
      simpa [initState] using
        bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hAccounts)
    (solidityDecodeBytesLengthHeader_long_valid hflag rfl hvalid)

theorem bytesStoreReadCurrentLengthShort_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ g A I) { base := "current" } =
      .ok (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
        ⟨127⟩).toNat := by
  exact readStorageBytesLength?_ok_of_layout
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (er := { base := "current" })
    (evm := initState cA gh bl σ_solm σ₀ g A I) (baseSlot := ⟨0⟩)
    (header := bytesStoreCurrentLengthHeaderWord σ_evm I)
    (len := (UInt256.land
      (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat)
    (by rfl)
    (by simp [bytesStoreLayout])
    (by
      simpa [initState] using
        bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hAccounts)
    (solidityDecodeBytesLengthHeader_short_valid hflag rfl hvalid)

theorem bytesStoreReadCurrentLengthLongMalformed_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ g A I) { base := "current" } = .revert := by
  exact readStorageBytesLength?_revert_of_layout
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (er := { base := "current" })
    (evm := initState cA gh bl σ_solm σ₀ g A I) (baseSlot := ⟨0⟩)
    (header := bytesStoreCurrentLengthHeaderWord σ_evm I)
    (by rfl)
    (by simp [bytesStoreLayout])
    (by
      simpa [initState] using
        bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hAccounts)
    (by simp [solidityDecodeBytesLengthHeader, hflag, hbad])

theorem bytesStoreReadCurrentLengthShortMalformed_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    readStorageBytesLength? bytesStoreConfig
        (initState cA gh bl σ_solm σ₀ g A I) { base := "current" } = .revert := by
  have hbad0 :
      UInt256.sub ⟨0⟩
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) = ⟨0⟩ := by
    simpa [hflag] using hbad
  exact readStorageBytesLength?_revert_of_layout
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (er := { base := "current" })
    (evm := initState cA gh bl σ_solm σ₀ g A I) (baseSlot := ⟨0⟩)
    (header := bytesStoreCurrentLengthHeaderWord σ_evm I)
    (by rfl)
    (by simp [bytesStoreLayout])
    (by
      simpa [initState] using
        bytesStoreStorageLoadCurrentLength_initState_of_accountMapEquiv
          (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) hAccounts)
    (by simp [solidityDecodeBytesLengthHeader, hflag, hbad0])

def bytesStorePacketLengthHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)

def bytesStorePacketDataRef : EvaledStorageRef :=
  { base := "packet", steps := [.field "data"] }

theorem bytesStorePacketDataRef_length_slot (evm : EVM.State) :
    ∃ loc, bytesStoreLayout
        { bytesStorePacketDataRef with
          steps := bytesStorePacketDataRef.steps ++ [.length] } evm =
          some loc ∧
        loc.slot = (⟨2⟩ : UInt256) := by
  refine ⟨bytesLikeLengthLoc ⟨2⟩ evm, ?_, ?_⟩
  · simp [bytesStoreLayout, bytesStorePacketDataRef]
  · simp [bytesLikeLengthLoc]

theorem bytesStorePacketLengthHeaderWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStorePacketLengthHeaderWord σ_evm I =
      bytesStorePacketLengthHeaderWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩

theorem bytesStoreStorageLoadPacketLength_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner ⟨2⟩ =
      bytesStorePacketLengthHeaderWord σ_evm I := by
  simpa [bytesStorePacketLengthHeaderWord] using
    bytesStoreStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) ⟨2⟩ hAccounts

theorem bytesStoreStorageLoadPacketLength_of_accountMapEquiv
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ =
      bytesStorePacketLengthHeaderWord σ I := by
  exact (accountStorageWord_eq_storageLoad_of_accountMapEquiv
    (owner := I.codeOwner) (slot := (⟨2⟩ : UInt256)) howner hAccounts).symm

def bytesStoreMappedLengthKeyWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def bytesStoreMappedLengthSlot (I : ExecutionEnv) : UInt256 :=
  mappedValueSlot (.int (Int.ofNat (bytesStoreMappedLengthKeyWord I).toNat))

def bytesStoreMappedLengthRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "mapped"
    steps := [.mindex (.int (Int.ofNat (bytesStoreMappedLengthKeyWord I).toNat))] }

theorem bytesStoreMappedLengthRef_length_slot (evm : EVM.State) (I : ExecutionEnv) :
    ∃ loc, bytesStoreLayout
        { bytesStoreMappedLengthRef I with
          steps := (bytesStoreMappedLengthRef I).steps ++ [.length] } evm =
          some loc ∧
        loc.slot = bytesStoreMappedLengthSlot I := by
  refine ⟨bytesLikeLengthLoc (bytesStoreMappedLengthSlot I) evm, ?_, ?_⟩
  · simp [bytesStoreLayout, bytesStoreMappedLengthRef, bytesStoreMappedLengthSlot]
  · simp [bytesLikeLengthLoc]

def bytesStoreMappedLengthHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreMappedLengthSlot I) ⟨0⟩)

theorem bytesStoreMappedLengthHeaderWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreMappedLengthHeaderWord σ_evm I =
      bytesStoreMappedLengthHeaderWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner (bytesStoreMappedLengthSlot I) ⟨0⟩

theorem bytesStoreStorageLoadMappedLength_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreMappedLengthSlot I) =
      bytesStoreMappedLengthHeaderWord σ_evm I := by
  simpa [bytesStoreMappedLengthHeaderWord] using
    bytesStoreStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStoreMappedLengthSlot I) hAccounts

def bytesStoreChunkLengthIndexWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def bytesStoreChunkLengthSlot (I : ExecutionEnv) : UInt256 :=
  chunksDataBase + bytesStoreChunkLengthIndexWord I

def bytesStoreChunkLengthRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "chunks"
    steps := [.aindex (.int (Int.ofNat (bytesStoreChunkLengthIndexWord I).toNat))] }

theorem bytesStoreChunkLengthRef_length_slot (evm : EVM.State) (I : ExecutionEnv) :
    ∃ loc, bytesStoreLayout
        { bytesStoreChunkLengthRef I with
          steps := (bytesStoreChunkLengthRef I).steps ++ [.length] } evm =
          some loc ∧
        loc.slot = bytesStoreChunkLengthSlot I := by
  refine ⟨bytesLikeLengthLoc (bytesStoreChunkLengthSlot I) evm, ?_, ?_⟩
  · have hnonneg : ¬ ((bytesStoreChunkLengthIndexWord I).toNat : Int) < 0 := by
      omega
    simp [bytesStoreLayout, bytesStoreChunkLengthRef, chunksElemSlot?,
      nonnegativeIndexSlot?, bytesStoreChunkLengthSlot, u256_ofNat_toNat]
    simp [hnonneg]
  · simp [bytesLikeLengthLoc]

def bytesStoreChunkLengthHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreChunkLengthSlot I) ⟨0⟩)

theorem bytesStoreChunkLengthHeaderWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreChunkLengthHeaderWord σ_evm I =
      bytesStoreChunkLengthHeaderWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner (bytesStoreChunkLengthSlot I) ⟨0⟩

theorem bytesStoreStorageLoadChunkLength_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreChunkLengthSlot I) =
      bytesStoreChunkLengthHeaderWord σ_evm I := by
  simpa [bytesStoreChunkLengthHeaderWord] using
    bytesStoreStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStoreChunkLengthSlot I) hAccounts

def bytesStorePushChunkSlot (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  chunksDataBase + bytesStoreChunksLengthWord σ I

def bytesStorePushChunkHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStorePushChunkSlot σ I) ⟨0⟩)

def bytesStorePushChunkPostLengthHeaderWord (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  if bytesStorePushChunkSlot σ I = (⟨1⟩ : UInt256) then
    (σ.find? I.codeOwner |>.option ⟨0⟩
      (fun _ => bytesStoreChunksLengthWord σ I + ⟨1⟩))
  else
    bytesStorePushChunkHeaderWord σ I

theorem bytesStorePushChunkPostLengthHeaderWord_eq_if
    (σ : AccountMap) (I : ExecutionEnv) :
    bytesStorePushChunkPostLengthHeaderWord σ I =
      if bytesStorePushChunkSlot σ I = (⟨1⟩ : UInt256) then
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun _ => bytesStoreChunksLengthWord σ I + ⟨1⟩))
      else
        bytesStorePushChunkHeaderWord σ I := by
  rfl

theorem bytesStorePushChunkPostLengthHeaderWord_sstore
    (σ : AccountMap) (I : ExecutionEnv) :
    ((sstoreAccountMap I.codeOwner σ ⟨1⟩
        (bytesStoreChunksLengthWord σ I + ⟨1⟩)).find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStorePushChunkSlot σ I) ⟨0⟩)) =
      bytesStorePushChunkPostLengthHeaderWord σ I := by
  simpa [bytesStorePushChunkPostLengthHeaderWord, bytesStorePushChunkSlot,
    bytesStorePushChunkHeaderWord] using
    sstoreAccountMap_storage_findD_eq_if σ I.codeOwner
      (chunksDataBase + bytesStoreChunksLengthWord σ I) ⟨1⟩
      (bytesStoreChunksLengthWord σ I + ⟨1⟩)

theorem bytesStoreStorageLoadPushChunkHeader_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStorePushChunkSlot σ_evm I) =
      bytesStorePushChunkHeaderWord σ_evm I := by
  simpa [bytesStorePushChunkHeaderWord] using
    bytesStoreStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStorePushChunkSlot σ_evm I) hAccounts

theorem bytesStoreStorageLoadPushChunkPostLengthHeader_initState_eq_if_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
          (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner ⟨1⟩
          (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStorePushChunkSlot σ_evm I) =
      if bytesStorePushChunkSlot σ_evm I = (⟨1⟩ : UInt256) then
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun _ => bytesStoreChunksLengthWord σ_evm I + ⟨1⟩))
      else
        bytesStorePushChunkHeaderWord σ_evm I := by
  let evm0 := initState cA gh bl σ_solm σ₀ g A I
  have hloadElem :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner
          (bytesStorePushChunkSlot σ_evm I) =
        bytesStorePushChunkHeaderWord σ_evm I := by
    simpa [evm0] using
      bytesStoreStorageLoadPushChunkHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) hAccounts
  simpa [evm0, bytesStorePushChunkSlot, storageStore_executionEnv] using
    (storageLoad_storageStore_eq_if evm0 evm0.executionEnv.codeOwner
      (chunksDataBase + bytesStoreChunksLengthWord σ_evm I) ⟨1⟩
      (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩)).trans
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

theorem bytesStoreStorageLoadPushChunkPostLengthHeader_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
          (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner ⟨1⟩
          (bytesStoreChunksLengthWord σ_evm I + ⟨1⟩))
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStorePushChunkSlot σ_evm I) =
      bytesStorePushChunkPostLengthHeaderWord σ_evm I := by
  rw [bytesStoreStorageLoadPushChunkPostLengthHeader_initState_eq_if_of_accountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hAccounts]
  rw [bytesStorePushChunkPostLengthHeaderWord_eq_if]

/-- Reading an owner storage word after a single store, with the collision case explicit. -/
theorem bytesStoreStorageWordAfterSstore_eq_if
    (σ : AccountMap) (I : ExecutionEnv) (readSlot writeSlot val : UInt256) :
    ((sstoreAccountMap I.codeOwner σ writeSlot val).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD readSlot (default : UInt256))) =
      if readSlot = writeSlot then
        ((σ.find? I.codeOwner).option (default : UInt256) (fun _ => val))
      else
        (σ.find? I.codeOwner |>.option (default : UInt256)
          (fun acc => acc.storage.findD readSlot (default : UInt256))) := by
  exact sstoreAccountMap_storage_findD_eq_if σ I.codeOwner readSlot writeSlot val

theorem bytesStoreStorageWordAfterSstore_eq_if_of_before
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
  exact sstoreAccountMap_storage_findD_eq_if_of_before hword

/-- Owner `storageLoad` after an owner `storageStore`, with the collision case explicit. -/
theorem bytesStoreStorageLoadAfterStorageStore_eq_if
    (evm : EVM.State) (readSlot writeSlot val : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner writeSlot val)
        evm.executionEnv.codeOwner readSlot =
      if readSlot = writeSlot then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner readSlot := by
  exact storageLoad_storageStore_codeOwner_eq_if evm readSlot writeSlot val

theorem bytesStoreStorageLoadAfterStorageStore_eq_if_of_before
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
  exact storageLoad_storageStore_codeOwner_eq_if_of_before hload

/-- Owner storage header readback after writing a long `bytes` data word, with the collision case
exposed instead of hidden behind a layout assumption. -/
theorem bytesStoreBytesHeaderWordAfterDataSstore_eq_if
    (σ : AccountMap) (I : ExecutionEnv) (baseSlot idx val : UInt256) :
    ((sstoreAccountMap I.codeOwner σ
        (bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) val).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD baseSlot (default : UInt256))) =
      if baseSlot = bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩ then
        ((σ.find? I.codeOwner).option (default : UInt256) (fun _ => val))
      else
        (σ.find? I.codeOwner |>.option (default : UInt256)
          (fun acc => acc.storage.findD baseSlot (default : UInt256))) := by
  simpa [bytesLikeDataBase, solidityBytesDataSlot, solidityBytesDataBaseSlot,
    u256_ofNat_toNat] using
    (solidityBytesHeaderWordAfterDataSstore_eq_if σ I.codeOwner baseSlot
      (UInt256.div idx ⟨32⟩).toNat val)

/-- Owner `storageLoad` header readback after writing a long `bytes` data word, with the collision
case exposed instead of hidden behind a layout assumption. -/
theorem bytesStoreStorageLoadBytesHeaderAfterDataStore_eq_if
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
  simpa [bytesLikeDataBase, solidityBytesDataSlot, solidityBytesDataBaseSlot,
    u256_ofNat_toNat] using
    (storageLoadSolidityBytesHeaderAfterDataStore_codeOwner_eq_if evm baseSlot
      (UInt256.div idx ⟨32⟩).toNat val)

theorem bytesStoreStorageLoadBytesHeaderAfterDataStore_ne_of_ne
    (evm : EVM.State) (baseSlot idx val : UInt256)
    (hne : baseSlot ≠ bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) val)
        evm.executionEnv.codeOwner baseSlot =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot := by
  rw [bytesStoreStorageLoadBytesHeaderAfterDataStore_eq_if]
  exact if_neg hne

theorem bytesStoreBytesHeaderWordAfterDataSstore_eq_if_of_before
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
  simpa [bytesLikeDataBase, solidityBytesDataSlot, solidityBytesDataBaseSlot,
    u256_ofNat_toNat] using
    (solidityBytesHeaderWordAfterDataSstore_eq_if_of_before
      (owner := I.codeOwner) (wordIndex := (UInt256.div idx ⟨32⟩).toNat) hword)

theorem bytesStoreBytesHeaderWordAfterDataSstore_eq_of_before_of_ne
    {σ : AccountMap} {I : ExecutionEnv} {baseSlot idx val word : UInt256}
    (hne : baseSlot ≠ bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩)
    (hword :
      (σ.find? I.codeOwner |>.option (default : UInt256)
        (fun acc => acc.storage.findD baseSlot (default : UInt256))) = word) :
    ((sstoreAccountMap I.codeOwner σ
        (bytesLikeDataBase baseSlot + UInt256.div idx ⟨32⟩) val).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD baseSlot (default : UInt256))) =
      word := by
  rw [bytesStoreBytesHeaderWordAfterDataSstore_eq_if_of_before hword]
  exact if_neg hne

theorem bytesStorePacketDataWordAfterTagSstore_eq_if
    (σ : AccountMap) (I : ExecutionEnv) (tag : UInt256) :
    ((sstoreAccountMap I.codeOwner σ ⟨3⟩ tag).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      if (⟨2⟩ : UInt256) = ⟨3⟩ then
        ((σ.find? I.codeOwner).option (default : UInt256) (fun _ => tag))
      else
        (σ.find? I.codeOwner |>.option (default : UInt256)
          (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) := by
  exact bytesStoreStorageWordAfterSstore_eq_if σ I ⟨2⟩ ⟨3⟩ tag

theorem bytesStorePacketDataWordAfterTagSstore_ne
    (σ : AccountMap) (I : ExecutionEnv) (tag : UInt256) :
    ((sstoreAccountMap I.codeOwner σ ⟨3⟩ tag).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      (σ.find? I.codeOwner |>.option (default : UInt256)
        (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) := by
  rw [bytesStorePacketDataWordAfterTagSstore_eq_if]
  exact if_neg (by native_decide : (⟨2⟩ : UInt256) ≠ ⟨3⟩)

theorem bytesStorePacketDataWordAfterTagSstore_eq_of_before
    {σ : AccountMap} {I : ExecutionEnv} {tag word : UInt256}
    (hword :
      (σ.find? I.codeOwner |>.option (default : UInt256)
        (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) = word) :
    ((sstoreAccountMap I.codeOwner σ ⟨3⟩ tag).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      word := by
  exact (bytesStorePacketDataWordAfterTagSstore_ne σ I tag).trans hword

theorem bytesStorePacketDataWordAfterDataSstore_zero
    (σ : AccountMap) (I : ExecutionEnv) :
    ((sstoreAccountMap I.codeOwner σ ⟨2⟩ ⟨0⟩).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      ⟨0⟩ := by
  rw [bytesStoreStorageWordAfterSstore_eq_if]
  cases hacc : σ.find? I.codeOwner with
  | none => rfl
  | some acc => rfl

theorem bytesStorePacketDataWordAfterDataSstore_of_find_some
    {σ : AccountMap} {I : ExecutionEnv} {acc : Account} {word : UInt256}
    (hacc : σ.find? I.codeOwner = some acc)
    (hword : (word == (default : UInt256)) = false) :
    ((sstoreAccountMap I.codeOwner σ ⟨2⟩ word).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      word := by
  exact sstoreAccountMap_storage_findD_self_of_find_some σ I.codeOwner acc ⟨2⟩ word hacc hword

theorem bytesStorePacketDataWordAfterDataTagSstore_zero
    (σ : AccountMap) (I : ExecutionEnv) (tag : UInt256) :
    ((sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨2⟩ ⟨0⟩)
        ⟨3⟩ tag).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      ⟨0⟩ := by
  exact bytesStorePacketDataWordAfterTagSstore_eq_of_before
    (σ := sstoreAccountMap I.codeOwner σ ⟨2⟩ ⟨0⟩) (I := I) (tag := tag)
    (bytesStorePacketDataWordAfterDataSstore_zero σ I)

theorem bytesStorePacketDataWordAfterDataTagSstore_of_find_some
    {σ : AccountMap} {I : ExecutionEnv} {acc : Account} {word tag : UInt256}
    (hacc : σ.find? I.codeOwner = some acc)
    (hword : (word == (default : UInt256)) = false) :
    ((sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨2⟩ word)
        ⟨3⟩ tag).find? I.codeOwner |>.option
        (default : UInt256) (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) =
      word := by
  exact bytesStorePacketDataWordAfterTagSstore_eq_of_before
    (σ := sstoreAccountMap I.codeOwner σ ⟨2⟩ word) (I := I) (tag := tag)
    (bytesStorePacketDataWordAfterDataSstore_of_find_some hacc hword)

/-- Reading `chunks.length` after a single store, with the collision case explicit. -/
theorem bytesStoreChunksLengthAfterSstore_eq_if
    (σ : AccountMap) (I : ExecutionEnv) (slot val : UInt256) :
    bytesStoreChunksLengthWord (sstoreAccountMap I.codeOwner σ slot val) I =
      if (⟨1⟩ : UInt256) = slot then
        ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256) (fun _ => val))
      else
        bytesStoreChunksLengthWord σ I := by
  exact bytesStoreStorageWordAfterSstore_eq_if σ I ⟨1⟩ slot val

/-- Preserving `chunks.length` after a single store is the non-collision corollary of the
collision-aware readback lemma. -/
theorem bytesStoreChunksLengthAfterSstore_ne
    (σ : AccountMap) (I : ExecutionEnv) (slot val : UInt256)
    (hne : (⟨1⟩ : UInt256) ≠ slot) :
    bytesStoreChunksLengthWord (sstoreAccountMap I.codeOwner σ slot val) I =
      bytesStoreChunksLengthWord σ I := by
  rw [bytesStoreChunksLengthAfterSstore_eq_if σ I slot val, if_neg hne]

theorem bytesStoreClearDataWordsLoopIndex_eq_uint256SuccFrom (idx : UInt256) :
    ∀ i, StringStoreLite.clearDataWordsLoopIndex idx i = uint256SuccFrom idx i
  | 0 => by
      simp [StringStoreLite.clearDataWordsLoopIndex, uint256SuccFrom]
  | i + 1 => by
      simp [StringStoreLite.clearDataWordsLoopIndex, uint256SuccFrom,
        bytesStoreClearDataWordsLoopIndex_eq_uint256SuccFrom idx i]

theorem bytesStoreChunksLengthWord_eq_storageLoad_of_accountMapEquiv
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    bytesStoreChunksLengthWord σ I =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ := by
  exact accountStorageWord_eq_storageLoad_of_accountMapEquiv
    (owner := I.codeOwner) (slot := (⟨1⟩ : UInt256)) howner hAccounts

theorem bytesStoreStorageLoadChunksLength_of_accountMapEquiv
    {evm : EVM.State} {σ τ : AccountMap} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (hchunks : bytesStoreChunksLengthWord σ I = bytesStoreChunksLengthWord τ I) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩ =
      bytesStoreChunksLengthWord τ I := by
  exact storageLoad_eq_accountStorageWord_of_accountMapEquiv_of_word_eq
    (owner := I.codeOwner) (slot := (⟨1⟩ : UInt256)) howner hAccounts hchunks

theorem bytesStoreStorageLoadChunksLength_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner ⟨1⟩ =
      bytesStoreChunksLengthWord σ_evm I := by
  exact bytesStoreStorageLoadChunksLength_of_accountMapEquiv
    (evm := initState cA gh bl σ_solm σ₀ g A I) (σ := σ_evm) (τ := σ_evm) (I := I)
    (by rfl) (by simpa [initState] using hAccounts) rfl

theorem bytesStoreChunksLengthAfterClearDataWordsForwardFrom
    (σ : AccountMap) (I : ExecutionEnv) (base idx : UInt256) (fuel : Nat)
    (hdisjoint : ∀ i, i < fuel →
      base + StringStoreLite.clearDataWordsLoopIndex idx i ≠ (⟨1⟩ : UInt256)) :
    bytesStoreChunksLengthWord
        (clearDataWordsForwardFrom I.codeOwner σ base idx fuel) I =
      bytesStoreChunksLengthWord σ I := by
  simpa [bytesStoreChunksLengthWord, accountStorageWord] using
    accountStorageWord_clearDataWordsForwardFrom_eq_of_ne σ I.codeOwner
      (⟨1⟩ : UInt256) base idx fuel
      (by
        intro i hi hEq
        have hslot := hdisjoint i hi
        apply hslot
        rw [bytesStoreClearDataWordsLoopIndex_eq_uint256SuccFrom idx i]
        exact hEq.symm)

theorem accountMapEquiv_clearDataWordsForwardFrom_shift_bytesLikeBase
    {owner : AccountAddress} {σ τ : AccountMap} (baseSlot : UInt256) :
    ∀ (offset : Nat) (idx : UInt256) (fuel : Nat),
      accountMapEquiv σ τ →
      accountMapEquiv
        (clearDataWordsForwardFrom owner σ
          (bytesLikeDataBase baseSlot + UInt256.ofNat offset) idx fuel)
        (clearDataWordsForwardFrom owner τ
          (bytesLikeDataBase baseSlot) (UInt256.ofNat offset + idx) fuel)
  | offset, idx, fuel, hAccounts =>
      Reasoning.Theory.accountMapEquiv_clearDataWordsForwardFrom_shift_base_offset
        (owner := owner) (σ := σ) (τ := τ)
        (bytesLikeDataBase baseSlot) (UInt256.ofNat offset) idx fuel hAccounts

def bytesStoreCalldataLongDataWord (I : ExecutionEnv)
    (payloadStart stride : UInt256) : Nat → UInt256
  | n =>
      uInt256OfByteArray
        (I.calldata.readBytes
          (payloadStart + StringStoreLite.longDataWordsLoopStride stride n).toNat 32)

def bytesStoreCalldataLongDataForwardFrom (owner : AccountAddress) (τ : AccountMap)
    (slot payloadStart stride : UInt256) (I : ExecutionEnv) : Nat → AccountMap :=
  accountStorageSuccessiveWordsForwardFrom UInt256 owner τ slot stride
    (fun stride i => bytesStoreCalldataLongDataWord I payloadStart stride i)
    (fun stride => (⟨32⟩ : UInt256) + stride)

theorem bytesStoreCalldataLongDataWord_succ_base (I : ExecutionEnv)
    (payloadStart stride : UInt256) :
    ∀ i,
      bytesStoreCalldataLongDataWord I payloadStart ((⟨32⟩ : UInt256) + stride) i =
        bytesStoreCalldataLongDataWord I payloadStart stride (i + 1)
  | 0 => by
      simp [bytesStoreCalldataLongDataWord, StringStoreLite.longDataWordsLoopStride]
  | i + 1 => by
      simp [bytesStoreCalldataLongDataWord, StringStoreLite.longDataWordsLoopStride,
        StringStoreLite.longDataWordsLoopStride_succ_base]

theorem bytesStoreCalldataLongDataWord_ofNat_stride_add (I : ExecutionEnv)
    (payloadStart : UInt256) :
    ∀ i j,
      bytesStoreCalldataLongDataWord I payloadStart (UInt256.ofNat (32 * i)) j =
        bytesStoreCalldataLongDataWord I payloadStart (UInt256.ofNat (32 * (i + j))) 0
  | i, 0 => by simp
  | i, j + 1 => by
      have hstrideStep :
          (⟨32⟩ : UInt256) + UInt256.ofNat (32 * i) =
            UInt256.ofNat (32 * (i + 1)) := by
        rw [StringStoreLite.u256_32_add_ofNat]
        congr 1
      rw [← bytesStoreCalldataLongDataWord_succ_base I payloadStart
        (UInt256.ofNat (32 * i)) j]
      rw [hstrideStep]
      have htail := bytesStoreCalldataLongDataWord_ofNat_stride_add I payloadStart (i + 1) j
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

theorem bytesStoreCalldataLongDataForwardFrom_eq_accountStorageWordsForwardFrom
    (owner : AccountAddress) (τ : AccountMap) (slot payloadStart stride : UInt256)
    (I : ExecutionEnv) :
    ∀ fuel,
      bytesStoreCalldataLongDataForwardFrom owner τ slot payloadStart stride I fuel =
        accountStorageWordsForwardFrom owner τ
          (fun i => uint256SuccFrom slot i)
          (fun i => bytesStoreCalldataLongDataWord I payloadStart stride i) 0 fuel
  | fuel => by
      exact accountStorageSuccessiveWordsForwardFrom_eq_accountStorageWordsForwardFrom
        owner τ slot stride
        (fun stride i => bytesStoreCalldataLongDataWord I payloadStart stride i)
        (fun stride => (⟨32⟩ : UInt256) + stride)
        (by
          intro stride i
          exact bytesStoreCalldataLongDataWord_succ_base I payloadStart stride i)
        fuel

theorem accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_of_words
    {I : ExecutionEnv} {len payloadStart : UInt256} {owner : AccountAddress}
    {baseSlot : UInt256} {bytes : ByteArray}
    (hword :
      ∀ k, k < len.toNat / 32 →
        bytesStoreCalldataLongDataWord I payloadStart (UInt256.ofNat (32 * k)) 0 =
          solidityDataWordAt bytes k) :
    ∀ {τ : AccountMap} {i fuel : Nat},
      i + fuel ≤ len.toNat / 32 →
      accountMapEquiv
        (solidityDataWordsForwardFrom owner τ baseSlot bytes i fuel)
        (bytesStoreCalldataLongDataForwardFrom owner τ
          (bytesLikeDataBase baseSlot + UInt256.ofNat i) payloadStart
          (UInt256.ofNat (32 * i)) I fuel)
  | τ, i, fuel, hfuel => by
      rw [bytesStoreCalldataLongDataForwardFrom_eq_accountStorageWordsForwardFrom]
      exact accountMapEquiv_solidityDataWordsForwardFrom_accountStorageWordsForwardFrom
        (owner := owner) (σ := τ) (baseSlot := baseSlot) (bytes := bytes)
        (slotAt := fun j => uint256SuccFrom (bytesLikeDataBase baseSlot + UInt256.ofNat i) j)
        (wordAt := fun j =>
          bytesStoreCalldataLongDataWord I payloadStart (UInt256.ofNat (32 * i)) j)
        i 0 fuel
        (by
          intro j hj
          simp [solidityBytesDataSlot, bytesLikeDataBase, solidityBytesDataBaseSlot,
            uint256SuccFrom_add_ofNat])
        (by
          intro j hj
          have hij : i + j < len.toNat / 32 := by omega
          have hshift :=
            bytesStoreCalldataLongDataWord_ofNat_stride_add I payloadStart i j
          simpa [Nat.zero_add] using (hshift.trans (hword (i + j) hij)).symm)

theorem bytesStoreCalldataLongDataWord_full_word_of_addr
    {I : ExecutionEnv} {len payloadStart : UInt256} {i : Nat}
    (haddr :
      (payloadStart + UInt256.ofNat (32 * i)).toNat = payloadStart.toNat + 32 * i)
    (hread : payloadStart.toNat + 32 * i + 32 ≤ I.calldata.size)
    (hsize : (StringStoreLite.setDecodedValueBytes I).size = len.toNat)
    (hdecoded :
      StringStoreLite.setDecodedValueBytes I =
        I.calldata.extract payloadStart.toNat (payloadStart.toNat + len.toNat))
    (hi : i < len.toNat / 32) :
    bytesStoreCalldataLongDataWord I payloadStart (UInt256.ofNat (32 * i)) 0 =
      uInt256OfByteArray
        ((StringStoreLite.setDecodedValueBytes I).readWithPadding (i * 32) 32) := by
  have hfull : 32 * i + 32 ≤ len.toNat := by
    have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
    have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
      Nat.mul_le_mul_left 32 hsucc
    have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
    have hle := le_trans hmul hdiv
    omega
  have hwordDirect :
      uInt256OfByteArray
          ((StringStoreLite.setDecodedValueBytes I).readWithPadding (i * 32) 32) =
        UInt256.ofNat
          (fromBytesBigEndian
            (((StringStoreLite.setDecodedValueBytes I).toList.drop (32 * i)).take 32)) := by
    simpa [Nat.mul_comm] using
      StringStoreLite.setDecodedValueBytes_readWithPadding_full_word
        (I := I) (len := len) (i := i) hsize hi
  have hleftList :
      (ByteArray.readBytes I.calldata (payloadStart.toNat + 32 * i) 32).data.toList =
        ((StringStoreLite.setDecodedValueBytes I).toList.drop (32 * i)).take 32 := by
    rw [hdecoded]
    rw [StringStoreLite.byteArray_extract_toList]
    rw [readBytes_at_toList_any I.calldata (payloadStart.toNat + 32 * i) hread]
    rw [byteArray_toList_eq]
    rw [List.drop_take]
    rw [List.drop_drop]
    rw [List.take_take]
    have hmin :
        min 32 (payloadStart.toNat + len.toNat - payloadStart.toNat - 32 * i) = 32 := by
      omega
    rw [hmin]
  have hleft :
      bytesStoreCalldataLongDataWord I payloadStart (UInt256.ofNat (32 * i)) 0 =
        UInt256.ofNat
          (fromBytesBigEndian
            (((StringStoreLite.setDecodedValueBytes I).toList.drop (32 * i)).take 32)) := by
    have hleftToList :
        (ByteArray.readBytes I.calldata (payloadStart.toNat + 32 * i) 32).toList =
          ((StringStoreLite.setDecodedValueBytes I).toList.drop (32 * i)).take 32 := by
      rw [byteArray_toList_eq]
      exact hleftList
    rw [bytesStoreCalldataLongDataWord, StringStoreLite.longDataWordsLoopStride]
    rw [haddr]
    rw [uInt256OfByteArray_eq]
    unfold fromByteArrayBigEndian
    rw [hleftToList]
  rw [hleft, hwordDirect]

theorem bytesStoreCalldataLongDataWord_full_word
    {I : ExecutionEnv} {len payloadStart : UInt256} {i : Nat}
    (haddr :
      (payloadStart + UInt256.ofNat (32 * i)).toNat = payloadStart.toNat + 32 * i)
    (hread : payloadStart.toNat + 32 * i + 32 ≤ I.calldata.size)
    (hsize : (StringStoreLite.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hi : i < len.toNat / 32) :
    bytesStoreCalldataLongDataWord I payloadStart (UInt256.ofNat (32 * i)) 0 =
      uInt256OfByteArray
        ((StringStoreLite.setDecodedValueBytes I).readWithPadding (i * 32) 32) := by
  exact bytesStoreCalldataLongDataWord_full_word_of_addr
    (I := I) (len := len) (payloadStart := payloadStart) (i := i)
    haddr hread hsize
    (StringStoreLite.setDecodedValueBytes_eq_extract
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax)
    hi

theorem bytesStoreCalldataLongDataRead_full_bounds
    {I : ExecutionEnv} {len payloadStart : UInt256} {i : Nat}
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hi : i < len.toNat / 32) :
    payloadStart.toNat + 32 * i + 32 ≤ I.calldata.size := by
  have hfull : 32 * i + 32 ≤ len.toNat := by
    have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
    have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
      Nat.mul_le_mul_left 32 hsucc
    have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
    have hle := le_trans hmul hdiv
    omega
  omega

theorem bytesStoreCalldataLongDataAddr_toNat_of_bound
    {payloadStart : UInt256} {i : Nat}
    (hbound : payloadStart.toNat + 32 * i < UInt256.size) :
    (payloadStart + UInt256.ofNat (32 * i)).toNat =
      payloadStart.toNat + 32 * i := by
  rw [uadd_toNat]
  have hstride : (UInt256.ofNat (32 * i)).toNat = 32 * i :=
    ulit_toNat' _ (by omega)
  rw [hstride]
  exact Nat.mod_eq_of_lt hbound

theorem accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full
    {I : ExecutionEnv} {len payloadStart : UInt256} {owner : AccountAddress}
    {baseSlot : UInt256}
    (hsize : (StringStoreLite.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (haddr :
      ∀ i, i < len.toNat / 32 →
        (payloadStart + UInt256.ofNat (32 * i)).toNat =
          payloadStart.toNat + 32 * i)
    (hread :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i + 32 ≤ I.calldata.size) :
    ∀ {τ : AccountMap} {i fuel : Nat},
      i + fuel ≤ len.toNat / 32 →
      accountMapEquiv
        (solidityDataWordsForwardFrom owner τ baseSlot
          (StringStoreLite.setDecodedValueBytes I) i fuel)
        (bytesStoreCalldataLongDataForwardFrom owner τ
          (bytesLikeDataBase baseSlot + UInt256.ofNat i) payloadStart
          (UInt256.ofNat (32 * i)) I fuel)
  | τ, i, fuel, hfuel => by
      exact accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_of_words
        (I := I) (len := len) (payloadStart := payloadStart) (owner := owner)
        (baseSlot := baseSlot) (bytes := StringStoreLite.setDecodedValueBytes I)
        (by
          intro k hk
          have hword :=
            bytesStoreCalldataLongDataWord_full_word
              (I := I) (len := len) (payloadStart := payloadStart) (i := k)
              (haddr k hk) (hread k hk) hsize hlenAbi hpayloadStart hoffMax hk
          simpa [solidityDataWordAt] using hword)
        hfuel

theorem accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full_of_bounds
    {I : ExecutionEnv} {len payloadStart : UInt256} {owner : AccountAddress}
    {baseSlot : UInt256}
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hsize : (StringStoreLite.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    ∀ {τ : AccountMap} {i fuel : Nat},
      i + fuel ≤ len.toNat / 32 →
      accountMapEquiv
        (solidityDataWordsForwardFrom owner τ baseSlot
          (StringStoreLite.setDecodedValueBytes I) i fuel)
        (bytesStoreCalldataLongDataForwardFrom owner τ
          (bytesLikeDataBase baseSlot + UInt256.ofNat i) payloadStart
          (UInt256.ofNat (32 * i)) I fuel) := by
  intro τ i fuel hfuel
  exact accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full
    (I := I) (len := len) (payloadStart := payloadStart) (owner := owner)
    (baseSlot := baseSlot) hsize hlenAbi hpayloadStart hoffMax
    (fun j hj => bytesStoreCalldataLongDataAddr_toNat_of_bound
      (payloadStart := payloadStart) (i := j) (haddrBound j hj))
    (fun j hj => bytesStoreCalldataLongDataRead_full_bounds
      (I := I) (len := len) (payloadStart := payloadStart) (i := j) hsrc hj)
    (τ := τ) (i := i) (fuel := fuel) hfuel

theorem accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full_zero
    {I : ExecutionEnv} {len payloadStart : UInt256} {owner : AccountAddress}
    {baseSlot : UInt256}
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hsize : (StringStoreLite.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    {τ : AccountMap} {fuel : Nat}
    (hfuel : fuel ≤ len.toNat / 32) :
    accountMapEquiv
      (solidityDataWordsForwardFrom owner τ baseSlot
        (StringStoreLite.setDecodedValueBytes I) 0 fuel)
      (bytesStoreCalldataLongDataForwardFrom owner τ
        (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fuel) := by
  have h :=
    accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full_of_bounds
      (I := I) (len := len) (payloadStart := payloadStart) (owner := owner)
      (baseSlot := baseSlot) hsrc haddrBound hsize hlenAbi hpayloadStart hoffMax
      (τ := τ) (i := 0) (fuel := fuel) (by simpa using hfuel)
  have hzero : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl
  have hslot : bytesLikeDataBase baseSlot + (⟨0⟩ : UInt256) = bytesLikeDataBase baseSlot := by
    exact StringStoreLite.uint256_add_zero_right (bytesLikeDataBase baseSlot)
  simpa [hslot, hzero] using h

theorem bytesStoreCalldataLongDataForwardFrom_find?_some_exists_of_find_some
    {σ : AccountMap} {owner : AccountAddress} {acc : Account}
    {slot payloadStart stride : UInt256} {I : ExecutionEnv}
    (hacc : σ.find? owner = some acc) :
    ∀ fuel, ∃ acc',
      (bytesStoreCalldataLongDataForwardFrom owner σ slot payloadStart stride I fuel).find?
        owner = some acc'
  | fuel => by
      rw [bytesStoreCalldataLongDataForwardFrom_eq_accountStorageWordsForwardFrom]
      exact accountStorageWordsForwardFrom_find?_some_exists_of_find_some
        (owner := owner) (slotAt := fun i => uint256SuccFrom slot i)
        (wordAt := fun i => bytesStoreCalldataLongDataWord I payloadStart stride i)
        (idx := 0) hacc fuel

theorem bytesStoreCalldataLongDataForwardFrom_absent_same
    {σ : AccountMap} {owner : AccountAddress}
    {slot payloadStart stride : UInt256} {I : ExecutionEnv}
    (hmissing : σ.find? owner = none) :
    ∀ fuel,
      bytesStoreCalldataLongDataForwardFrom owner σ slot payloadStart stride I fuel = σ
  | fuel => by
      rw [bytesStoreCalldataLongDataForwardFrom_eq_accountStorageWordsForwardFrom]
      exact accountStorageWordsForwardFrom_absent_same
        (owner := owner) (slotAt := fun i => uint256SuccFrom slot i)
        (wordAt := fun i => bytesStoreCalldataLongDataWord I payloadStart stride i)
        (idx := 0) hmissing fuel

theorem bytesStoreLongDataWordsLoopSlot_add (slot : UInt256) :
    ∀ start i,
      StringStoreLite.longDataWordsLoopSlot
          (StringStoreLite.longDataWordsLoopSlot slot start) i =
        StringStoreLite.longDataWordsLoopSlot slot (start + i)
  | start, 0 => by
      simp [StringStoreLite.longDataWordsLoopSlot]
  | start, i + 1 => by
      have hnat : start + (i + 1) = start + i + 1 := by omega
      rw [hnat]
      simp [StringStoreLite.longDataWordsLoopSlot,
        bytesStoreLongDataWordsLoopSlot_add slot start i]

theorem bytesStoreChunksLengthAfterChunkHeaderSstore_eq_if
    (σ : AccountMap) (I : ExecutionEnv) (chunkIndex val : UInt256) :
    bytesStoreChunksLengthWord
        (sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) val) I =
      if (⟨1⟩ : UInt256) = chunksDataBase + chunkIndex then
        ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256) (fun _ => val))
      else
        bytesStoreChunksLengthWord σ I := by
  exact bytesStoreChunksLengthAfterSstore_eq_if σ I (chunksDataBase + chunkIndex) val

theorem bytesStoreChunkBoundAfterChunkHeaderSstore_of_post_bound
    {σ : AccountMap} {I : ExecutionEnv} {chunkIndex val : UInt256}
    (hbound :
      chunkIndex.toNat <
        (if (⟨1⟩ : UInt256) = chunksDataBase + chunkIndex then
          ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256) (fun _ => val))
        else
          bytesStoreChunksLengthWord σ I).toNat) :
    chunkIndex.toNat <
      (bytesStoreChunksLengthWord
        (sstoreAccountMap I.codeOwner σ (chunksDataBase + chunkIndex) val) I).toNat := by
  rw [bytesStoreChunksLengthAfterChunkHeaderSstore_eq_if]
  exact hbound

theorem bytesStoreChunksLengthAfterChunkDataSstore_eq_if
    (σ : AccountMap) (I : ExecutionEnv) (chunkIndex idx val : UInt256) :
    bytesStoreChunksLengthWord
        (sstoreAccountMap I.codeOwner σ
          (bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) val) I =
      if (⟨1⟩ : UInt256) =
          bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩ then
        ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256) (fun _ => val))
      else
        bytesStoreChunksLengthWord σ I := by
  exact bytesStoreChunksLengthAfterSstore_eq_if σ I
    (bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) val

theorem bytesStoreChunkBoundAfterChunkDataSstore_of_post_bound
    {σ : AccountMap} {I : ExecutionEnv} {chunkIndex idx val : UInt256}
    (hbound :
      chunkIndex.toNat <
        (if (⟨1⟩ : UInt256) =
            bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩ then
          ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256) (fun _ => val))
        else
          bytesStoreChunksLengthWord σ I).toNat) :
    chunkIndex.toNat <
      (bytesStoreChunksLengthWord
        (sstoreAccountMap I.codeOwner σ
          (bytesLikeDataBase (chunksDataBase + chunkIndex) + UInt256.div idx ⟨32⟩) val) I).toNat := by
  rw [bytesStoreChunksLengthAfterChunkDataSstore_eq_if]
  exact hbound

theorem bytesStoreChunkHeaderWordAfterLengthSstore_eq_if
    (σ : AccountMap) (I : ExecutionEnv) (oldLen val : UInt256) :
    ((sstoreAccountMap I.codeOwner σ ⟨1⟩ val).find? I.codeOwner |>.option
        (default : UInt256)
        (fun acc => acc.storage.findD (chunksDataBase + oldLen) (default : UInt256))) =
      if chunksDataBase + oldLen = (⟨1⟩ : UInt256) then
        ((σ.find? I.codeOwner).option (default : UInt256) (fun _ => val))
      else
        (σ.find? I.codeOwner |>.option (default : UInt256)
          (fun acc => acc.storage.findD (chunksDataBase + oldLen) (default : UInt256))) := by
  exact bytesStoreStorageWordAfterSstore_eq_if σ I (chunksDataBase + oldLen) ⟨1⟩ val

theorem bytesStoreChunkHeaderWordAfterLengthSstore_eq_if_of_before
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
  exact bytesStoreStorageWordAfterSstore_eq_if_of_before hword

theorem bytesStoreStorageLoadChunkHeaderAfterLengthStore_eq_if
    (evm : EVM.State) (oldLen val : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ val)
        evm.executionEnv.codeOwner (chunksDataBase + oldLen) =
      if chunksDataBase + oldLen = (⟨1⟩ : UInt256) then
        (evm.accountMap.find? evm.executionEnv.codeOwner).option (default : UInt256)
          (fun _ => val)
      else
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) := by
  exact bytesStoreStorageLoadAfterStorageStore_eq_if evm (chunksDataBase + oldLen) ⟨1⟩ val

theorem bytesStoreStorageLoadChunkHeaderAfterLengthStore_eq_if_of_before
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
  exact bytesStoreStorageLoadAfterStorageStore_eq_if_of_before hload

theorem bytesStoreEmptyChunkHeaderAfterLengthStore_eq_if {evm : EVM.State} (oldLen : UInt256)
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
  exact bytesStoreStorageLoadChunkHeaderAfterLengthStore_eq_if_of_before hload

theorem bytesStoreEmptyChunkHeaderAfterLengthStore_of_ne {evm : EVM.State} (oldLen : UInt256)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = ⟨0⟩) :
    Solm.EVM.storageLoad
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
      evm.executionEnv.codeOwner (chunksDataBase + oldLen) = ⟨0⟩ := by
  rw [bytesStoreEmptyChunkHeaderAfterLengthStore_eq_if oldLen hload]
  exact if_neg hne

theorem bytesStoreChunkHeaderAfterLengthStore_eq_if {evm : EVM.State} (oldLen header : UInt256)
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
  exact bytesStoreStorageLoadChunkHeaderAfterLengthStore_eq_if_of_before hload

theorem bytesStoreChunkHeaderAfterLengthStore_of_ne {evm : EVM.State} (oldLen header : UInt256)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header) :
    Solm.EVM.storageLoad
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ (oldLen + ⟨1⟩))
      evm.executionEnv.codeOwner (chunksDataBase + oldLen) = header := by
  rw [bytesStoreChunkHeaderAfterLengthStore_eq_if oldLen header hload]
  exact if_neg hne

theorem bytesStorePushChunkHeaderAfterLengthStore_eq_if {σ : AccountMap} {I : ExecutionEnv}
    (oldLen : UInt256) :
    ((sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)).find? I.codeOwner |>.option
        ⟨0⟩ (fun acc => acc.storage.findD (chunksDataBase + oldLen) ⟨0⟩)) =
      if chunksDataBase + oldLen = (⟨1⟩ : UInt256) then
        ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256) (fun _ => oldLen + ⟨1⟩))
      else
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (chunksDataBase + oldLen) ⟨0⟩)) := by
  exact bytesStoreChunkHeaderWordAfterLengthSstore_eq_if_of_before (by rfl)

theorem bytesStorePushChunkHeaderAfterLengthStore_of_ne {σ : AccountMap} {I : ExecutionEnv}
    (oldLen : UInt256) (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256)) :
    ((sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)).find? I.codeOwner |>.option
        ⟨0⟩ (fun acc => acc.storage.findD (chunksDataBase + oldLen) ⟨0⟩)) =
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (chunksDataBase + oldLen) ⟨0⟩)) := by
  rw [bytesStorePushChunkHeaderAfterLengthStore_eq_if]
  exact if_neg hne

theorem bytesStorePushChunkHeaderAfterLengthStoreZero_of_ne
    {σ : AccountMap} {I : ExecutionEnv} (oldLen : UInt256)
    (hne : chunksDataBase + oldLen ≠ (⟨1⟩ : UInt256))
    (hzero :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (chunksDataBase + oldLen) ⟨0⟩)) = ⟨0⟩) :
    ((sstoreAccountMap I.codeOwner σ ⟨1⟩ (oldLen + ⟨1⟩)).find? I.codeOwner |>.option
        ⟨0⟩ (fun acc => acc.storage.findD (chunksDataBase + oldLen) ⟨0⟩)) = ⟨0⟩ := by
  exact (bytesStorePushChunkHeaderAfterLengthStore_of_ne (σ := σ) (I := I) oldLen hne).trans
    hzero

end BytesStore
