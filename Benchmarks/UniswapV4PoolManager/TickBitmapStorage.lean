import Benchmarks.UniswapV4PoolManager.ResolvedStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickBitmapType : StorageType := .mapping (.int (.sint ⟨16, by decide⟩)) (.elem (.int (.uint ⟨256, by decide⟩)))
def tickBitmapRef (id : UInt256) : EvaledStorageRef :=
  {base := "_pools", steps := (poolRef id).steps ++ [.field "tickBitmap"]}
def tickBitmapRefValue (id : UInt256) : Value := .storageRef (tickBitmapRef id) tickBitmapType
def tickBitmapWordRef (id : UInt256) (position : Int) : EvaledStorageRef :=
  {base := "_pools", steps := (tickBitmapRef id).steps ++ [.mindex (.int position)]}
def tickBitmapSlot (id : UInt256) (position : Int) : UInt256 :=
  mappingSlotWord (EVM.wordOfInt position) (poolSlot id+⟨5⟩)
def tickBitmapWord (evm : EVM.State) (id : UInt256) (position : Int) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (tickBitmapSlot id position)

theorem tickBitmapWord_loc (id : UInt256) (position : Int) :
    config.storageBackend.locate? (tickBitmapWordRef id position) =
      some (.leaf (uint256Loc (tickBitmapSlot id position))) := by
  have hk : keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id :=
    keyValueToWord_fixedBytes32 id
  simp only [tickBitmapWordRef, tickBitmapRef, poolRef, config, storageBackend, solidityStorageBackend,
    List.cons_append, List.nil_append]
  rw [hk]
  rfl

theorem tickBitmapWord_read {f : Frame} {evm : EVM.State} {name : Ident} {id : UInt256}
    {e : Expr} {position : Int} (hs : f.locals.get? name = some (tickBitmapRefValue id))
    (hp : evalExpr? config f evm e = .ok (.int position)) :
    evalExpr? config f evm (.storage {base := name, steps := [.mindex e]}) =
      .ok (.int (Int.ofNat (tickBitmapWord evm id position).toNat)) := by
  have hr := readResolvedStorageScalar (cfg := config) (evm := evm)
    (resolveStorageAliasMapping hs hp rfl) rfl (tickBitmapWord_loc id position)
  simpa only [storageLocLoad_uint256] using hr

theorem tickBitmapWord_write {f : Frame} {evm : EVM.State} {name : Ident} {id : UInt256}
    {e : Expr} {position : Int} (hs : f.locals.get? name = some (tickBitmapRefValue id))
    (hp : evalExpr? config f evm e = .ok (.int position)) (word : UInt256) :
    assignStorageRef? config f evm .storage {base := name, steps := [.mindex e]}
      (.int (Int.ofNat word.toNat)) = .ok (f, Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (tickBitmapSlot id position) word) :=
  assignResolvedStorageScalar (resolveStorageAliasMapping hs hp rfl) rfl
    (tickBitmapWord_loc id position) (storageLocStore_uint256 evm _ word)

end Benchmarks.UniswapV4PoolManager
