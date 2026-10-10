import Benchmarks.UniswapV3.Pool.TickClearFields
import Benchmarks.UniswapV3.Pool.ProtocolFeeStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def tickGrossWord (σ : AccountMap) (ee : ExecutionEnv) (tick : Int) : UInt256 :=
  uint128Word (solcSlotWordAt (tickClearBase tick) σ ee)

def tickNetValue (σ : AccountMap) (ee : ExecutionEnv) (tick : Int) : Int :=
  tickSignedFieldValue tick 0 16 ⟨128, by decide⟩ σ ee

theorem tickGrossWord_lt (σ : AccountMap) (ee : ExecutionEnv) (tick : Int) :
    (tickGrossWord σ ee tick).toNat < 2 ^ 128 := uint128Word_lt _

theorem tickNetValue_bounds (σ : AccountMap) (ee : ExecutionEnv) (tick : Int) :
    -(2 ^ 127 : Int) ≤ tickNetValue σ ee tick ∧ tickNetValue σ ee tick < 2 ^ 127 := by
  have h := normalizeSint_bounds ⟨128, by decide⟩ (Int.ofNat
    (UInt256.div (solcSlotWordAt (tickFieldSlot tick 0) σ ee) (UInt256.ofNat (256 ^ 16))).toNat)
  have hb : Int.ofNat (EVM.twoPow ((⟨128, by decide⟩ : ABI.BitWidth).val - 1)) =
      (2 ^ 127 : Int) := by norm_num [EVM.twoPow]
  rw [hb] at h
  exact h

theorem evalTickAliasGross (locals imms : Store) (evm : EVM.State) (bindingName : Ident)
    (tick : Int) (hget : locals.get? bindingName = some (tickAlias tick)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨bindingName, [.field "liquidityGross"]⟩) =
      .ok (.int (Int.ofNat (tickGrossWord evm.accountMap evm.executionEnv tick).toNat)) := by
  rw [evalTickAliasField "liquidityGross" (.int (.uint ⟨128, by decide⟩))
    (tickClearGrossLoc tick) locals imms evm bindingName tick hget rfl rfl]
  simp only [tickClearGrossLoc]
  rw [storageLocLoad_uint_offset _ _ _ _ _ rfl (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  change EvalResult.ok (Value.int (Int.ofNat
    (UInt256.land (UInt256.div (solcSlotWordAt (tickClearBase tick) evm.accountMap evm.executionEnv)
      ⟨1⟩) (UInt256.ofNat (2 ^ 128 - 1))).toNat)) = _
  rw [word_div_one, u256_land_comm]
  rfl

theorem evalTickAliasNet (locals imms : Store) (evm : EVM.State) (bindingName : Ident)
    (tick : Int) (hget : locals.get? bindingName = some (tickAlias tick)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨bindingName, [.field "liquidityNet"]⟩) =
      .ok (.int (tickNetValue evm.accountMap evm.executionEnv tick)) := by
  rw [evalTickAliasField "liquidityNet" (.int (.sint ⟨128, by decide⟩))
    (tickClearNetLoc tick) locals imms evm bindingName tick hget rfl rfl]
  simp only [tickClearNetLoc]
  rw [storageLocLoad_elem_offset _ _ _ _ _ (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]
  simp only [wordToElem, normalizeSint_mask ⟨128, by decide⟩ _
    (UInt256.ofNat (256 ^ (16 : Fin 33).val - 1)) (by native_decide)]
  simp only [tickNetValue, tickSignedFieldValue, tickFieldSlot,
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero]
  rfl

-- GENERALIZES the uint128 pair store to signed fields and arbitrary word-valued source values.
theorem storageLocStore_pair128Value (evm : EVM.State) (slot : UInt256) (second : Bool)
    (ty : ABI.ElemType) (value : Value) (word : UInt256) (hv : valueToWord value = some word) :
    storageLocStore evm
      {slot := slot, offset := if second then 16 else 0, size := 16, type := ty,
        hbound := by cases second <;> decide} value =
      some (EVM.storageStore evm evm.executionEnv.codeOwner slot
        (protocolFeeUpdateWord second (EVM.storageLoad evm evm.executionEnv.codeOwner slot) word)) := by
  have h := storageLocStore_uint128PairField evm slot second word
  simp only [storageLocStore]
  rw [hv]
  simpa only [storageLocStore, valueToWord, wordOfInt_ofNat_toNat, pure] using h

theorem assignTickAliasField (name : Ident) (ty : ABI.ElemType) (loc : StorageLoc)
    (locals imms : Store) (evm evm' : EVM.State) (bindingName : Ident) (tick : Int)
    (value : Value) (hget : locals.get? bindingName = some (tickAlias tick))
    (htype : storageTypeStep? tickStorageType (.field name) = some (.elem ty))
    (hloc : storageBackend.locate? ⟨"ticks", [.mindex (.int tick), .field name]⟩ = some (.leaf loc))
    (hstore : storageLocStore evm loc value = some evm') :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm
      .storage ⟨bindingName, [.field name]⟩ value =
      .ok ({contract := contract, locals := locals, immutables := imms}, evm') :=
  assignStorageRef_resolved_scalar
    (resolveTickAliasField locals imms evm bindingName name tick _ hget htype)
    poolStorageBackend_eq hloc hstore

def tickLiquidityState (evm : EVM.State) (tick : Int) (net : Bool) (word : UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner (tickClearBase tick)
    (protocolFeeUpdateWord net (EVM.storageLoad evm evm.executionEnv.codeOwner (tickClearBase tick)) word)

theorem assignTickLiquidity (locals imms : Store) (evm : EVM.State) (bindingName : Ident)
    (tick : Int) (net : Bool) (value : Value) (word : UInt256)
    (hget : locals.get? bindingName = some (tickAlias tick)) (hv : valueToWord value = some word) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm
      .storage ⟨bindingName, [.field (if net then "liquidityNet" else "liquidityGross")]⟩ value =
      .ok ({contract := contract, locals := locals, immutables := imms},
        tickLiquidityState evm tick net word) := by
  cases net
  · exact assignTickAliasField "liquidityGross" (.int (.uint ⟨128, by decide⟩))
      (tickClearGrossLoc tick) locals imms evm _ bindingName tick value hget rfl rfl
      (storageLocStore_pair128Value evm (tickClearBase tick) false _ value word hv)
  · exact assignTickAliasField "liquidityNet" (.int (.sint ⟨128, by decide⟩))
      (tickClearNetLoc tick) locals imms evm _ bindingName tick value hget rfl rfl
      (storageLocStore_pair128Value evm (tickClearBase tick) true _ value word hv)

end Benchmarks.UniswapV3.Pool
