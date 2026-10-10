import Benchmarks.UniswapV4PoolManager.ResolvedStorage
import Benchmarks.UniswapV4PoolManager.WordPackedStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolLiquidityRef (id : UInt256) : EvaledStorageRef :=
  {base := "_pools", steps := (poolRef id).steps ++ [.field "liquidity"]}
def poolLiquiditySlot (id : UInt256) : UInt256 := poolSlot id + ⟨3⟩
def poolLiquidityLoc (id : UInt256) : StorageLoc :=
  {slot := poolLiquiditySlot id, offset := 0, size := 16, hbound := by decide,
   type := .int (.uint ⟨128, by decide⟩)}
def poolLiquidityPacked (evm : State) (id : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (poolLiquiditySlot id)
def poolLiquidityWord (evm : State) (id : UInt256) : UInt256 :=
  UInt256.land (poolLiquidityPacked evm id) (UInt256.ofNat (2^128-1))
def poolLiquidityStore (evm : State) (id value : UInt256) : State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (poolLiquiditySlot id)
    (wordLowSet (poolLiquidityPacked evm id) value 128)

theorem poolLiquidity_loc (id : UInt256) :
    config.storageBackend.locate? (poolLiquidityRef id) = some (.leaf (poolLiquidityLoc id)) := by
  have hk : keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id := keyValueToWord_fixedBytes32 id
  simp only [poolLiquidityRef, poolRef, config, storageBackend, solidityStorageBackend,
    List.cons_append, List.nil_append]
  rw [hk]
  rfl

theorem poolLiquidity_bound (evm : State) (id : UInt256) : (poolLiquidityWord evm id).toNat < 2^128 :=
  u256LandMaskToNatLtOfToNat _ _ rfl

theorem poolLiquidity_read {f : Frame} {evm : State} {name : Ident} {id : UInt256}
    (hs : f.locals.get? name = some (poolRefValue id)) :
    evalExpr? config f evm (.storage {base := name, steps := [.field "liquidity"]}) =
      .ok (.int (Int.ofNat (poolLiquidityWord evm id).toNat)) := by
  have hr := readResolvedStorageScalar (cfg := config) (evm := evm)
    (resolveStorageAliasField (field := "liquidity") hs rfl) rfl (poolLiquidity_loc id)
  exact hr.trans (congrArg EvalResult.ok
    (storageLocLoad_uint_offset0 evm (poolLiquiditySlot id) ⟨16, by decide⟩ ⟨128, by decide⟩
      (hbound := by decide) rfl (by decide)))

theorem poolLiquidity_write {f : Frame} {evm : State} {name : Ident} {id value : UInt256}
    (hs : f.locals.get? name = some (poolRefValue id)) (hv : value.toNat < 2^128) :
    assignStorageRef? config f evm .storage {base := name, steps := [.field "liquidity"]}
      (.int (Int.ofNat value.toNat)) = .ok (f, poolLiquidityStore evm id value) :=
  assignResolvedStorageScalar (resolveStorageAliasField (field := "liquidity") hs rfl) rfl
    (poolLiquidity_loc id) (storageLocStore_uintOffset0 evm _ value ⟨16, by decide⟩ ⟨128, by decide⟩ (by decide) hv)

end Benchmarks.UniswapV4PoolManager
