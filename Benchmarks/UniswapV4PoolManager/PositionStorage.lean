import Benchmarks.UniswapV4PoolManager.ResolvedStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def positionStateType : StorageType := .struct "Position_State"
  [("liquidity", .elem (.int (.uint ⟨128, by decide⟩))),
   ("feeGrowthInside0LastX128", .elem (.int (.uint ⟨256, by decide⟩))),
   ("feeGrowthInside1LastX128", .elem (.int (.uint ⟨256, by decide⟩)))]
def positionsType : StorageType := .mapping (.bytes abiBytes32Width) positionStateType
def positionsRef (id : UInt256) : EvaledStorageRef :=
  {base := "_pools", steps := (poolRef id).steps ++ [.field "positions"]}
def positionsRefValue (id : UInt256) : Value := .storageRef (positionsRef id) positionsType
def positionRef (id key : UInt256) : EvaledStorageRef :=
  {base := "_pools", steps := (positionsRef id).steps ++ [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))]}
def positionRefValue (id key : UInt256) : Value := .storageRef (positionRef id key) positionStateType
def positionSlot (id key : UInt256) : UInt256 := mappingSlotWord key (poolSlot id+⟨6⟩)

theorem positionMappingResolve {f : Frame} {evm : EVM.State} {name : Ident} {id key : UInt256} {e : Expr}
    (hs : f.locals.get? name = some (positionsRefValue id))
    (he : evalExpr? config f evm e = .ok (wordBytes32Value key)) :
    resolveStorageRef? config f evm {base := name, steps := [.mindex e]} =
      .ok (positionRef id key, positionStateType) :=
  resolveStorageAliasMapping hs he (by simp only [valueToKey?, word_toBytesBE_length_32]; rfl)

def positionLiquidityRef (id key : UInt256) : EvaledStorageRef :=
  {base := "_pools", steps := (positionRef id key).steps ++ [.field "liquidity"]}
def positionLiquidityLoc (id key : UInt256) : StorageLoc :=
  {slot := positionSlot id key, offset := 0, size := 16, hbound := by decide,
   type := .int (.uint ⟨128, by decide⟩)}
def positionPackedWord (evm : EVM.State) (id key : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (positionSlot id key)
def positionLiquidityWord (evm : EVM.State) (id key : UInt256) : UInt256 :=
  UInt256.land (positionPackedWord evm id key) (UInt256.ofNat (2^128-1))

theorem positionLiquidity_loc (id key : UInt256) :
    config.storageBackend.locate? (positionLiquidityRef id key) = some (.leaf (positionLiquidityLoc id key)) := by
  have hi : keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id := keyValueToWord_fixedBytes32 id
  have hk : keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key)) = key := keyValueToWord_fixedBytes32 key
  simp only [positionLiquidityRef, positionRef, positionsRef, poolRef, config, storageBackend, solidityStorageBackend,
    List.cons_append, List.nil_append]
  rw [hi, hk]
  rfl

theorem positionLiquidity_read {f : Frame} {evm : EVM.State} {name : Ident} {id key : UInt256}
    (hs : f.locals.get? name = some (positionRefValue id key)) :
    evalExpr? config f evm (.storage {base := name, steps := [.field "liquidity"]}) =
      .ok (.int (Int.ofNat (positionLiquidityWord evm id key).toNat)) := by
  have hr := readResolvedStorageScalar (cfg := config) (evm := evm)
    (resolveStorageAliasField (field := "liquidity") hs rfl) rfl (positionLiquidity_loc id key)
  have hv := storageLocLoad_uint_offset0 evm (positionSlot id key) ⟨16, by decide⟩ ⟨128, by decide⟩
    (hbound := by decide) rfl (by decide)
  rw [show storageLocLoad evm (positionLiquidityLoc id key) =
    .int (Int.ofNat (positionLiquidityWord evm id key).toNat) from hv] at hr
  exact hr

end Benchmarks.UniswapV4PoolManager
