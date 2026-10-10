import Benchmarks.UniswapV3.Pool.Storage
import Benchmarks.UniswapV3.Pool.SourceExpressions
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def bitmapSlot (key : Int) : UInt256 := solcMappingSlot ⟨6⟩ (EVM.wordOfInt key)

theorem evalBitmapStorage (locals imms : Store) (evm : EVM.State) (key : Int) (expr : Expr)
    (hbase : locals.get? "tickBitmap" = none)
    (he : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm expr =
      .ok (.int key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"tickBitmap", [.mindex expr]⟩) =
      .ok (.int (Int.ofNat (solcSlotWordAt (bitmapSlot key)
        evm.accountMap evm.executionEnv).toNat)) := by
  apply evalExpr_storage_scalar_value (t := .int (.uint ⟨256, by decide⟩))
    (er := ⟨"tickBitmap", [.mindex (.int key)]⟩) (loc := uint256Loc (bitmapSlot key)) hbase
    (by simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, he,
      valueToKey?, EvalResult.ofOption, bind, EvalResult.bind, pure]) rfl poolStorageBackend_eq rfl
  rw [storageLocLoad_uint256,
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]

def storeBitmap (evm : EVM.State) (key : Int) (value : UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner (bitmapSlot key) value

theorem assignBitmapStorage (locals imms : Store) (evm : EVM.State) (key : Int) (expr : Expr)
    (value : UInt256) (hbase : locals.get? "tickBitmap" = none)
    (he : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm expr =
      .ok (.int key)) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm
      .storage ⟨"tickBitmap", [.mindex expr]⟩ (.int (Int.ofNat value.toNat)) =
      .ok ({contract := contract, locals := locals, immutables := imms}, storeBitmap evm key value) := by
  apply assignStorageRef_storage_scalar_value (ty := .elem (.int (.uint ⟨256, by decide⟩)))
    (er := ⟨"tickBitmap", [.mindex (.int key)]⟩) (loc := uint256Loc (bitmapSlot key)) hbase
    (by simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, he,
      valueToKey?, EvalResult.ofOption, bind, EvalResult.bind, pure])
    rfl poolStorageBackend_eq rfl (Or.inl ⟨_, rfl⟩)
  exact storageLocStore_uint256 evm (bitmapSlot key) value

def bitmapFlippedWord (σ : AccountMap) (ee : ExecutionEnv) (key : Int) (mask : UInt256) : UInt256 :=
  UInt256.xor (solcSlotWordAt (bitmapSlot key) σ ee) mask

def bitmapFlippedMap (σ : AccountMap) (ee : ExecutionEnv) (key : Int) (mask : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ (bitmapSlot key) (bitmapFlippedWord σ ee key mask)

def flipBitmap (evm : EVM.State) (key : Int) (mask : UInt256) : EVM.State :=
  storeBitmap evm key (UInt256.xor (EVM.storageLoad evm evm.executionEnv.codeOwner (bitmapSlot key)) mask)

theorem SourceState.flipBitmap {s0 ee σ evm} (hs : SourceState s0 ee σ evm)
    (key : Int) (mask : UInt256) :
    SourceState s0 ee (bitmapFlippedMap σ ee key mask) (flipBitmap evm key mask) := by
  have h := hs.readModifyWrite (bitmapSlot key) (fun old ↦ UInt256.xor old mask)
  simpa only [bitmapFlippedMap, Benchmarks.UniswapV3.Pool.flipBitmap, storeBitmap,
    bitmapFlippedWord, hs.accounts, hs.env, solcSlotWordAt] using h

theorem storeBitmap_executionEnv (evm : EVM.State) (key : Int) (value : UInt256) :
    (storeBitmap evm key value).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

end Benchmarks.UniswapV3.Pool
