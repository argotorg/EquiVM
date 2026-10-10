import Benchmarks.UniswapV4PoolManager.ResolvedStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickInfoType : StorageType := .struct "TickInfo"
  [("liquidityPacked", .elem (.int (.uint ⟨256, by decide⟩))),
   ("feeGrowthOutside0X128", .elem (.int (.uint ⟨256, by decide⟩))),
   ("feeGrowthOutside1X128", .elem (.int (.uint ⟨256, by decide⟩)))]

def tickRef (id : UInt256) (tick : Int) : EvaledStorageRef :=
  {base := "_pools", steps := (poolRef id).steps ++ [.field "ticks", .mindex (.int tick)]}
def tickRefValue (id : UInt256) (tick : Int) : Value := .storageRef (tickRef id tick) tickInfoType
def tickSlot (id : UInt256) (tick : Int) : UInt256 :=
  mappingSlotWord (EVM.wordOfInt tick) (poolSlot id+⟨4⟩)

inductive TickField where
  | liquidityPacked | feeGrowthOutside0 | feeGrowthOutside1
def TickField.name : TickField → Ident
  | .liquidityPacked => "liquidityPacked"
  | .feeGrowthOutside0 => "feeGrowthOutside0X128"
  | .feeGrowthOutside1 => "feeGrowthOutside1X128"
def TickField.slot (base : UInt256) : TickField → UInt256
  | .liquidityPacked => base
  | .feeGrowthOutside0 => base+⟨1⟩
  | .feeGrowthOutside1 => base+⟨2⟩
def tickFieldRef (id : UInt256) (tick : Int) (field : TickField) : EvaledStorageRef :=
  {base := "_pools", steps := (tickRef id tick).steps ++ [.field field.name]}
def tickFieldWord (evm : EVM.State) (id : UInt256) (tick : Int) (field : TickField) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (field.slot (tickSlot id tick))

theorem tickField_type (field : TickField) : storageTypeStep? tickInfoType (.field field.name) =
    some (.elem (.int (.uint ⟨256, by decide⟩))) := by cases field <;> rfl

theorem tickField_loc (id : UInt256) (tick : Int) (field : TickField) :
    config.storageBackend.locate? (tickFieldRef id tick field) =
      some (.leaf (uint256Loc (field.slot (tickSlot id tick)))) := by
  have hk : keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id :=
    keyValueToWord_fixedBytes32 id
  cases field <;>
    simp only [tickFieldRef, tickRef, poolRef, TickField.name, config, storageBackend, solidityStorageBackend,
      List.cons_append, List.nil_append] <;>
    rw [hk] <;> rfl

theorem tickMappingResolve {f : Frame} {evm : EVM.State} {name : Ident} {id : UInt256}
    {e : Expr} {tick : Int} (hs : f.locals.get? name = some (poolRefValue id))
    (he : evalExpr? config f evm e = .ok (.int tick)) :
    resolveStorageRef? config f evm {base := name, steps := [.field "ticks", .mindex e]} =
      .ok (tickRef id tick, tickInfoType) :=
  resolveStorageAliasFieldMapping hs rfl he rfl

theorem tickField_read {f : Frame} {evm : EVM.State} {name : Ident} {id : UInt256} {tick : Int}
    (hs : f.locals.get? name = some (tickRefValue id tick)) (field : TickField) :
    evalExpr? config f evm (.storage {base := name, steps := [.field field.name]}) =
      .ok (.int (Int.ofNat (tickFieldWord evm id tick field).toNat)) := by
  have hr := readResolvedStorageScalar (cfg := config) (evm := evm)
    (resolveStorageAliasField hs (tickField_type field)) rfl
    (tickField_loc id tick field)
  simpa only [storageLocLoad_uint256] using hr

theorem tickField_write {f : Frame} {evm : EVM.State} {name : Ident} {id : UInt256} {tick : Int}
    (hs : f.locals.get? name = some (tickRefValue id tick)) (field : TickField) (word : UInt256) :
    assignStorageRef? config f evm .storage {base := name, steps := [.field field.name]}
      (.int (Int.ofNat word.toNat)) = .ok (f, Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (field.slot (tickSlot id tick)) word) :=
  assignResolvedStorageScalar (resolveStorageAliasField hs (tickField_type field)) rfl
    (tickField_loc id tick field) (storageLocStore_uint256 evm _ word)

end Benchmarks.UniswapV4PoolManager
