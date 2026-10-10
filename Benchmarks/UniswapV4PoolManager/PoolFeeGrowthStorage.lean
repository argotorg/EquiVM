import Benchmarks.UniswapV4PoolManager.ResolvedStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolFeeGrowthName (second : Bool) : Ident :=
  if second then "feeGrowthGlobal1X128" else "feeGrowthGlobal0X128"
def poolFeeGrowthSlot (id : UInt256) (second : Bool) : UInt256 :=
  poolSlot id + if second then ⟨2⟩ else ⟨1⟩
def poolFeeGrowthRef (id : UInt256) (second : Bool) : EvaledStorageRef :=
  {base := "_pools", steps := (poolRef id).steps ++ [.field (poolFeeGrowthName second)]}
def poolFeeGrowthWord (evm : EVM.State) (id : UInt256) (second : Bool) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (poolFeeGrowthSlot id second)

theorem poolFeeGrowth_type (second : Bool) :
    storageTypeStep? poolStateType (.field (poolFeeGrowthName second)) =
      some (.elem (.int (.uint ⟨256, by decide⟩))) := by cases second <;> rfl

theorem poolFeeGrowth_loc (id : UInt256) (second : Bool) :
    config.storageBackend.locate? (poolFeeGrowthRef id second) =
      some (.leaf (uint256Loc (poolFeeGrowthSlot id second))) := by
  have hk : keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id :=
    keyValueToWord_fixedBytes32 id
  cases second <;>
    simp only [poolFeeGrowthRef, poolFeeGrowthName, Bool.false_eq_true, if_false, if_true,
      poolRef, config, storageBackend, solidityStorageBackend, List.cons_append, List.nil_append] <;>
    rw [hk] <;> rfl

theorem poolFeeGrowth_read {f : Frame} {evm : EVM.State} {name : Ident} {id : UInt256}
    (hs : f.locals.get? name = some (poolRefValue id)) (second : Bool) :
    evalExpr? config f evm (.storage {base := name, steps := [.field (poolFeeGrowthName second)]}) =
      .ok (.int (Int.ofNat (poolFeeGrowthWord evm id second).toNat)) := by
  have hr := readResolvedStorageScalar (cfg := config) (evm := evm)
    (resolveStorageAliasField hs (poolFeeGrowth_type second)) rfl (poolFeeGrowth_loc id second)
  simpa only [storageLocLoad_uint256] using hr

end Benchmarks.UniswapV4PoolManager
