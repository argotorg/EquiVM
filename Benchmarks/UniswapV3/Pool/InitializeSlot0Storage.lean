import Benchmarks.UniswapV3.Pool.InitializeSlot0Model

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def initializePriceLoc : StorageLoc :=
  {slot := ⟨0⟩, offset := 0, size := 20, type := .int (.uint ⟨160, by decide⟩), hbound := by decide}

def initializeTickLoc : StorageLoc :=
  {slot := ⟨0⟩, offset := 20, size := 3, type := .int (.sint ⟨24, by decide⟩), hbound := by decide}

def initializeIndexLoc : StorageLoc :=
  {slot := ⟨0⟩, offset := 23, size := 2, type := .int (.uint ⟨16, by decide⟩), hbound := by decide}

def initializeCardinalityLoc : StorageLoc :=
  {slot := ⟨0⟩, offset := 25, size := 2, type := .int (.uint ⟨16, by decide⟩), hbound := by decide}

def initializeNextLoc : StorageLoc :=
  {slot := ⟨0⟩, offset := 27, size := 2, type := .int (.uint ⟨16, by decide⟩), hbound := by decide}

def initializeFeeLoc : StorageLoc :=
  {slot := ⟨0⟩, offset := 29, size := 1, type := .int (.uint ⟨8, by decide⟩), hbound := by decide}

def initializeUnlockedLoc : StorageLoc :=
  {slot := ⟨0⟩, offset := 30, size := 1, type := .bool, hbound := by decide}

theorem initializeSlot0Fields (evm e0 e1 e2 e3 e4 e5 e6 : EVM.State)
    (price : UInt256) (tick : Int)
    (h0 : storageLocStore evm initializePriceLoc (.int (Int.ofNat price.toNat)) = some e0)
    (h1 : storageLocStore e0 initializeTickLoc (.int tick) = some e1)
    (h2 : storageLocStore e1 initializeIndexLoc (.int 0) = some e2)
    (h3 : storageLocStore e2 initializeCardinalityLoc (.int 1) = some e3)
    (h4 : storageLocStore e3 initializeNextLoc (.int 1) = some e4)
    (h5 : storageLocStore e4 initializeFeeLoc (.int 0) = some e5)
    (h6 : storageLocStore e5 initializeUnlockedLoc (.bool true) = some e6) :
    solidityWriteStorage? storageBackend.locate? evm ⟨"slot0", []⟩ slot0StorageType
      (initializeSlot0Value price tick) = .ok e6 := by
  have hl0 : storageBackend.locate? ⟨"slot0", [.field "sqrtPriceX96"]⟩ =
      some (.leaf initializePriceLoc) := rfl
  have hl1 : storageBackend.locate? ⟨"slot0", [.field "tick"]⟩ =
      some (.leaf initializeTickLoc) := rfl
  have hl2 : storageBackend.locate? ⟨"slot0", [.field "observationIndex"]⟩ =
      some (.leaf initializeIndexLoc) := rfl
  have hl3 : storageBackend.locate? ⟨"slot0", [.field "observationCardinality"]⟩ =
      some (.leaf initializeCardinalityLoc) := rfl
  have hl4 : storageBackend.locate? ⟨"slot0", [.field "observationCardinalityNext"]⟩ =
      some (.leaf initializeNextLoc) := rfl
  have hl5 : storageBackend.locate? ⟨"slot0", [.field "feeProtocol"]⟩ =
      some (.leaf initializeFeeLoc) := rfl
  have hl6 : storageBackend.locate? ⟨"slot0", [.field "unlocked"]⟩ =
      some (.leaf initializeUnlockedLoc) := rfl
  simp only [slot0StorageType, initializeSlot0Value, solidityWriteStorage?,
    solidityWriteFields?, ↓reduceIte, List.cons_append, List.nil_append,
    solidityLeafLoc?_of_leaf hl0, solidityLeafLoc?_of_leaf hl1,
    solidityLeafLoc?_of_leaf hl2, solidityLeafLoc?_of_leaf hl3,
    solidityLeafLoc?_of_leaf hl4, solidityLeafLoc?_of_leaf hl5, solidityLeafLoc?_of_leaf hl6,
    h0, h1, h2, h3, h4, h5, h6, EvalResult.ofOption, bind, EvalResult.bind]

theorem initializeSlot0Write (evm : EVM.State) (price : UInt256) (tick : Int)
    (hp : price.toNat < 2 ^ 160) :
    solidityWriteStorage? storageBackend.locate? evm ⟨"slot0", []⟩ slot0StorageType
      (initializeSlot0Value price tick) = .ok (initializeSlot0State evm price tick) := by
  let old := EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let e0 := EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ (packedPrefixWord old price 160)
  let e1 := EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (packedPrefixWord old (initializeTickLow price tick) 184)
  let e2 := EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (packedPrefixWord old (initializeTickLow price tick) 200)
  let e3 := EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (packedPrefixWord old (initializeCardinalityLow price tick) 216)
  let e4 := EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (packedPrefixWord old (initializeNextLow price tick) 232)
  let e5 := EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (packedPrefixWord old (initializeNextLow price tick) 240)
  have ht184 := initializeTickLow_lt price tick hp
  have ht200 : (initializeTickLow price tick).toNat < 2 ^ 200 :=
    lt_of_lt_of_le ht184 (by decide)
  have hc216 := initializeCardinalityLow_lt price tick hp
  have hn232 := initializeNextLow_lt price tick hp
  have hn240 : (initializeNextLow price tick).toNat < 2 ^ 240 :=
    lt_of_lt_of_le hn232 (by decide)
  have h0 : storageLocStore evm initializePriceLoc (.int (Int.ofNat price.toNat)) = some e0 := by
    apply storageLocStore_packed_of_toNat evm _ _ price _
      (by simp only [valueToWord, wordOfInt_ofNat_toNat, pure]) rfl
    rw [packedPrefixWord_toNat old price 160 (by decide) hp]
    change _ = old.toNat % 1 + 1 * (price.toNat % 2 ^ 160) + 2 ^ 160 * (old.toNat / 2 ^ 160)
    rw [Nat.mod_one, Nat.mod_eq_of_lt hp]
    omega
  have h1 : storageLocStore e0 initializeTickLoc (.int tick) = some e1 := by
    apply storageLocStore_extendPrefix evm initializeTickLoc (.int tick) (EVM.wordOfInt tick)
      price (initializeTickLow price tick) rfl rfl hp
    exact packedAppend_toNat price (EVM.wordOfInt tick) 160 24 (by decide) hp
  have h2 : storageLocStore e1 initializeIndexLoc (.int 0) = some e2 := by
    apply storageLocStore_extendPrefix evm initializeIndexLoc (.int 0) ⟨0⟩
      (initializeTickLow price tick) (initializeTickLow price tick) rfl rfl ht184
    change _ = _ + 2 ^ 184 * 0
    omega
  have h3 : storageLocStore e2 initializeCardinalityLoc (.int 1) = some e3 := by
    apply storageLocStore_extendPrefix evm initializeCardinalityLoc (.int 1) ⟨1⟩
      (initializeTickLow price tick) (initializeCardinalityLow price tick) rfl rfl ht200
    exact packedAppend_toNat _ _ 200 16 (by decide) ht200
  have h4 : storageLocStore e3 initializeNextLoc (.int 1) = some e4 := by
    apply storageLocStore_extendPrefix evm initializeNextLoc (.int 1) ⟨1⟩
      (initializeCardinalityLow price tick) (initializeNextLow price tick) rfl rfl hc216
    exact packedAppend_toNat _ _ 216 16 (by decide) hc216
  have h5 : storageLocStore e4 initializeFeeLoc (.int 0) = some e5 := by
    apply storageLocStore_extendPrefix evm initializeFeeLoc (.int 0) ⟨0⟩
      (initializeNextLow price tick) (initializeNextLow price tick) rfl rfl hn232
    change _ = _ + 2 ^ 232 * 0
    omega
  have h6 : storageLocStore e5 initializeUnlockedLoc (.bool true) =
      some (initializeSlot0State evm price tick) := by
    apply storageLocStore_extendPrefix evm initializeUnlockedLoc (.bool true) ⟨1⟩
      (initializeNextLow price tick) (initializeUnlockedLow price tick) rfl rfl hn240
    exact packedAppend_toNat _ _ 240 8 (by decide) hn240
  exact initializeSlot0Fields evm e0 e1 e2 e3 e4 e5 _ price tick h0 h1 h2 h3 h4 h5 h6

theorem assignInitializeSlot0 (locals imms : Store) (evm : EVM.State)
    (price : UInt256) (tick : Int) (hbase : locals.get? "slot0" = none)
    (hp : price.toNat < 2 ^ 160) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm .storage
      ⟨"slot0", []⟩ (initializeSlot0Value price tick) =
      .ok ({contract := contract, locals := locals, immutables := imms},
        initializeSlot0State evm price tick) := by
  have hresolve : resolveStorageRef? config
      {contract := contract, locals := locals, immutables := imms} evm ⟨"slot0", []⟩ =
      .ok (⟨"slot0", []⟩, slot0StorageType) :=
    resolveStorageRef?_ok hbase
      (by simp only [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure]) rfl
  simp only [assignStorageRef?, hresolve, poolStorageBackend_eq, solidityStorageBackend,
    initializeSlot0Write evm price tick hp, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
