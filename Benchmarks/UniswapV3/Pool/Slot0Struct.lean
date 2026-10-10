import Benchmarks.UniswapV3.Pool.Slot0Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def slot0StorageType : StorageType :=
  .struct "Slot0" [
    ("sqrtPriceX96", .elem (.int (.uint ⟨160, by decide⟩))),
    ("tick", .elem (.int (.sint ⟨24, by decide⟩))),
    ("observationIndex", .elem (.int (.uint ⟨16, by decide⟩))),
    ("observationCardinality", .elem (.int (.uint ⟨16, by decide⟩))),
    ("observationCardinalityNext", .elem (.int (.uint ⟨16, by decide⟩))),
    ("feeProtocol", .elem (.int (.uint ⟨8, by decide⟩))),
    ("unlocked", .elem .bool)]

def slot0StructValue (σ : AccountMap) (I : ExecutionEnv) : Value :=
  .struct "Slot0" [
    ("sqrtPriceX96", .int (Int.ofNat (slot0FieldWord 0 20 σ I).toNat)),
    ("tick", .int (slot0TickValue σ I)),
    ("observationIndex", .int (Int.ofNat (slot0FieldWord 23 2 σ I).toNat)),
    ("observationCardinality", .int (Int.ofNat (slot0FieldWord 25 2 σ I).toNat)),
    ("observationCardinalityNext", .int (Int.ofNat (slot0FieldWord 27 2 σ I).toNat)),
    ("feeProtocol", .int (Int.ofNat (slot0FieldWord 29 1 σ I).toNat)),
    ("unlocked", wordToElem .bool (slot0FieldWord 30 1 σ I))]

def slot0StructWords (σ : AccountMap) (I : ExecutionEnv) : List UInt256 :=
  [slot0FieldWord 0 20 σ I, EVM.wordOfInt (slot0TickValue σ I),
    slot0FieldWord 23 2 σ I, slot0FieldWord 25 2 σ I, slot0FieldWord 27 2 σ I,
    slot0FieldWord 29 1 σ I, UInt256.isZero (UInt256.isZero (slot0FieldWord 30 1 σ I))]

theorem readSlot0FieldOfGetter (evm : EVM.State) (name : Ident) (ty : ABI.ElemType)
    (value : Value)
    (htype : storageTypeAt? contract.storage ⟨"slot0", [.field name]⟩ = some (.elem ty))
    (heval : evalExpr? config {contract := contract, locals := ∅} evm
      (.storage ⟨"slot0", [.field name]⟩) = .ok value) :
    solidityReadStorage? storageBackend.locate? evm ⟨"slot0", [.field name]⟩ (.elem ty) = .ok value := by
  have hresolve : resolveStorageRef? config {contract := contract, locals := ∅} evm
      ⟨"slot0", [.field name]⟩ = .ok (⟨"slot0", [.field name]⟩, .elem ty) :=
    resolveStorageRef?_ok (by simp)
      (by simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        EvalResult.bind, bind, pure]) htype
  simpa only [evalExpr?, hresolve, bind, EvalResult.bind] using heval

theorem readSlot0Struct (evm : EVM.State) :
    solidityReadStorage? storageBackend.locate? evm ⟨"slot0", []⟩ slot0StorageType =
      .ok (slot0StructValue evm.accountMap evm.executionEnv) := by
  have h0 := readSlot0FieldOfGetter evm "sqrtPriceX96" (.int (.uint ⟨160, by decide⟩)) _ rfl
    (evalSlot0SqrtPriceX96 ∅ ∅ evm (by simp))
  have h1 := readSlot0FieldOfGetter evm "tick" (.int (.sint ⟨24, by decide⟩)) _ rfl
    (evalSlot0Tick ∅ ∅ evm (by simp))
  have h2 := readSlot0FieldOfGetter evm "observationIndex" (.int (.uint ⟨16, by decide⟩)) _ rfl
    (evalSlot0ObservationIndex ∅ ∅ evm (by simp))
  have h3 := readSlot0FieldOfGetter evm "observationCardinality" (.int (.uint ⟨16, by decide⟩)) _ rfl
    (evalSlot0ObservationCardinality ∅ ∅ evm (by simp))
  have h4 := readSlot0FieldOfGetter evm "observationCardinalityNext" (.int (.uint ⟨16, by decide⟩)) _ rfl
    (evalSlot0ObservationCardinalityNext ∅ ∅ evm (by simp))
  have h5 := readSlot0FieldOfGetter evm "feeProtocol" (.int (.uint ⟨8, by decide⟩)) _ rfl
    (evalSlot0FeeProtocol ∅ ∅ evm (by simp))
  have h6 := readSlot0FieldOfGetter evm "unlocked" .bool _ rfl
    (evalSlot0Unlocked ∅ ∅ evm (by simp))
  rw [slot0StorageType, solidityReadStorage?]
  simp only [solidityReadFields?, List.nil_append, h0, h1, h2, h3, h4, h5, h6,
    bind, EvalResult.bind, pure, slot0StructValue]

theorem evalSlot0Struct (locals imms : Store) (evm : EVM.State)
    (hbase : locals.get? "slot0" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"slot0", []⟩) = .ok (slot0StructValue evm.accountMap evm.executionEnv) := by
  have hresolve : resolveStorageRef? config
      {contract := contract, locals := locals, immutables := imms} evm ⟨"slot0", []⟩ =
      .ok (⟨"slot0", []⟩, slot0StorageType) :=
    resolveStorageRef?_ok hbase
      (by simp only [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure]) rfl
  rw [evalExpr?]
  simp only [hresolve, bind, EvalResult.bind]
  exact readSlot0Struct evm

end Benchmarks.UniswapV3.Pool
