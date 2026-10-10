import Benchmarks.UniswapV3.Pool.Storage
import Benchmarks.UniswapV3.Pool.SourceWordArithmetic
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def feeGrowthName (second : Bool) : Ident :=
  if second then "feeGrowthGlobal1X128" else "feeGrowthGlobal0X128"

def feeGrowthSlot (second : Bool) : UInt256 := if second then ⟨2⟩ else ⟨1⟩

def feeGrowthWord (second : Bool) (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  solcSlotWordAt (feeGrowthSlot second) σ ee

def storeFeeGrowth (evm : EVM.State) (second : Bool) (value : UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner (feeGrowthSlot second) value

theorem evalFeeGrowth (locals imms : Store) (evm : EVM.State) (second : Bool)
    (hbase : locals.get? (feeGrowthName second) = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨feeGrowthName second, []⟩) =
      .ok (.int (Int.ofNat (feeGrowthWord second evm.accountMap evm.executionEnv).toNat)) := by
  cases second
  · exact evalFeeGrowthGlobal0X128 locals imms evm hbase
  · exact evalFeeGrowthGlobal1X128 locals imms evm hbase

theorem assignFeeGrowth (locals imms : Store) (evm : EVM.State) (second : Bool) (value : UInt256)
    (hbase : locals.get? (feeGrowthName second) = none) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm
      .storage ⟨feeGrowthName second, []⟩ (.int (Int.ofNat value.toNat)) =
      .ok ({contract := contract, locals := locals, immutables := imms},
        storeFeeGrowth evm second value) := by
  apply assignStorageRef_storage_scalar_value (ty := .elem (.int (.uint ⟨256, by decide⟩)))
    (er := ⟨feeGrowthName second, []⟩) (loc := uint256Loc (feeGrowthSlot second)) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, bind, pure])
    (by cases second <;> dsimp only <;> decide +kernel) poolStorageBackend_eq
    (by cases second <;> rfl) (Or.inl ⟨_, rfl⟩)
  exact storageLocStore_uint256 evm (feeGrowthSlot second) value

def addFeeGrowth (evm : EVM.State) (second : Bool) (amount : UInt256) : EVM.State :=
  storeFeeGrowth evm second (feeGrowthWord second evm.accountMap evm.executionEnv + amount)

def addFeeGrowthMap (σ : AccountMap) (ee : ExecutionEnv) (second : Bool)
    (amount : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ (feeGrowthSlot second) (feeGrowthWord second σ ee + amount)

theorem SourceState.addFeeGrowth {s0 ee σ evm} (hs : SourceState s0 ee σ evm)
    (second : Bool) (amount : UInt256) :
    SourceState s0 ee (addFeeGrowthMap σ ee second amount) (addFeeGrowth evm second amount) := by
  have h := hs.readModifyWrite (feeGrowthSlot second) (fun old ↦ old + amount)
  simpa only [addFeeGrowthMap, Benchmarks.UniswapV3.Pool.addFeeGrowth, storeFeeGrowth,
    feeGrowthWord, hs.accounts, hs.env, solcSlotWordAt] using h

end Benchmarks.UniswapV3.Pool
