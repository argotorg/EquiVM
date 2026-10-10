import Benchmarks.UniswapV4PoolManager.PositionStorage
import Benchmarks.UniswapV4PoolManager.WordPackedStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def positionLiquidityStore (evm : EVM.State) (id key value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (positionSlot id key)
    (wordLowSet (positionPackedWord evm id key) value 128)

theorem positionLiquidity_bound (evm : EVM.State) (id key : UInt256) :
    (positionLiquidityWord evm id key).toNat < 2^128 :=
  u256LandMaskToNatLtOfToNat _ _ rfl

theorem positionLiquidity_write {f : Frame} {evm : EVM.State} {name : Ident} {id key value : UInt256}
    (hs : f.locals.get? name = some (positionRefValue id key)) (hv : value.toNat < 2^128) :
    assignStorageRef? config f evm .storage {base := name, steps := [.field "liquidity"]}
      (.int (Int.ofNat value.toNat)) = .ok (f, positionLiquidityStore evm id key value) :=
  assignResolvedStorageScalar (resolveStorageAliasField (field := "liquidity") hs rfl) rfl
    (positionLiquidity_loc id key) (storageLocStore_uintOffset0 evm _ value ⟨16, by decide⟩
      ⟨128, by decide⟩ (by decide) hv)

def positionFeeName : Bool → Ident
  | false => "feeGrowthInside0LastX128"
  | true => "feeGrowthInside1LastX128"
def positionFeeSlot (id key : UInt256) (second : Bool) : UInt256 :=
  positionSlot id key + if second then ⟨2⟩ else ⟨1⟩
def positionFeeRef (id key : UInt256) (second : Bool) : EvaledStorageRef :=
  {base := "_pools", steps := (positionRef id key).steps ++ [.field (positionFeeName second)]}
def positionFeeWord (evm : EVM.State) (id key : UInt256) (second : Bool) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (positionFeeSlot id key second)

theorem positionFee_type (second : Bool) :
    storageTypeStep? positionStateType (.field (positionFeeName second)) =
      some (.elem (.int (.uint ⟨256, by decide⟩))) := by cases second <;> rfl

theorem positionFee_loc (id key : UInt256) (second : Bool) :
    config.storageBackend.locate? (positionFeeRef id key second) =
      some (.leaf (uint256Loc (positionFeeSlot id key second))) := by
  have hi : keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id := keyValueToWord_fixedBytes32 id
  have hk : keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key)) = key := keyValueToWord_fixedBytes32 key
  cases second <;>
    simp only [positionFeeRef, positionRef, positionsRef, poolRef, positionFeeName, config, storageBackend,
      solidityStorageBackend, List.cons_append, List.nil_append] <;> rw [hi, hk] <;> rfl

theorem positionFee_read {f : Frame} {evm : EVM.State} {name : Ident} {id key : UInt256}
    (hs : f.locals.get? name = some (positionRefValue id key)) (second : Bool) :
    evalExpr? config f evm (.storage {base := name, steps := [.field (positionFeeName second)]}) =
      .ok (.int (Int.ofNat (positionFeeWord evm id key second).toNat)) := by
  have hr := readResolvedStorageScalar (cfg := config) (evm := evm)
    (resolveStorageAliasField hs (positionFee_type second)) rfl (positionFee_loc id key second)
  simpa only [storageLocLoad_uint256] using hr

theorem positionFee_write {f : Frame} {evm : EVM.State} {name : Ident} {id key value : UInt256}
    (hs : f.locals.get? name = some (positionRefValue id key)) (second : Bool) :
    assignStorageRef? config f evm .storage {base := name, steps := [.field (positionFeeName second)]}
      (.int (Int.ofNat value.toNat)) = .ok (f, Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (positionFeeSlot id key second) value) :=
  assignResolvedStorageScalar (resolveStorageAliasField hs (positionFee_type second)) rfl
    (positionFee_loc id key second) (storageLocStore_uint256 evm _ value)

end Benchmarks.UniswapV4PoolManager
