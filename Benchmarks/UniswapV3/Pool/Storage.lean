import Benchmarks.UniswapV3.Pool.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

theorem poolStorageBackend_eq :
    config.storageBackend = solidityStorageBackend storageBackend.locate? := rfl

-- LIBRARY CANDIDATE: Reasoning.Storage, evaluate a full-word scalar storage variable.
theorem evalExpr_storage_uint256_base {cfg : Config} {layout : StorageLayout}
    {frame : Frame} {evm : EVM.State} {base : Ident} {slot : UInt256}
    (hbase : frame.locals.get? base = none)
    (htype : storageTypeAt? frame.contract.storage ⟨base, []⟩ =
      some (.elem (.int (.uint ⟨256, by decide⟩))))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout ⟨base, []⟩ = some (.leaf (uint256Loc slot))) :
    evalExpr? cfg frame evm (.storage ⟨base, []⟩) =
      .ok (.int (Int.ofNat (solcSlotWordAt slot evm.accountMap evm.executionEnv).toNat)) := by
  apply evalExpr_storage_scalar_value hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, bind, pure]) htype hbackend hloc
  rw [storageLocLoad_uint256, storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv slot rfl]

theorem evalFeeGrowthGlobal0X128 (locals imms : Store) (evm : EVM.State)
    (hbase : locals.get? "feeGrowthGlobal0X128" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"feeGrowthGlobal0X128", []⟩) =
      .ok (.int (Int.ofNat (solcSlotWordAt ⟨1⟩ evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_uint256_base hbase (by dsimp only; decide +kernel) poolStorageBackend_eq rfl

theorem evalFeeGrowthGlobal1X128 (locals imms : Store) (evm : EVM.State)
    (hbase : locals.get? "feeGrowthGlobal1X128" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"feeGrowthGlobal1X128", []⟩) =
      .ok (.int (Int.ofNat (solcSlotWordAt ⟨2⟩ evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_uint256_base hbase (by dsimp only; decide +kernel) poolStorageBackend_eq rfl

theorem evalLiquidity (locals imms : Store) (evm : EVM.State)
    (hbase : locals.get? "liquidity" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"liquidity", []⟩) =
      .ok (.int (Int.ofNat (UInt256.land (solcSlotWordAt ⟨4⟩ evm.accountMap evm.executionEnv)
        (UInt256.ofNat (2 ^ 128 - 1))).toNat)) := by
  apply evalExpr_storage_scalar_value (t := .int (.uint ⟨128, by decide⟩))
    (er := ⟨"liquidity", []⟩)
    (loc := { slot := ⟨4⟩, offset := 0, size := 16,
              type := .int (.uint ⟨128, by decide⟩), hbound := by decide }) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, bind, pure])
    (by dsimp only; decide +kernel) poolStorageBackend_eq rfl
  rw [storageLocLoad_uint_offset0 _ _ _ _ rfl (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv ⟨4⟩ rfl]
  rfl

def protocolFeesToken0Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWordAt ⟨3⟩ σ I) (UInt256.ofNat (2 ^ 128 - 1))

def protocolFeesToken1Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (solcSlotWordAt ⟨3⟩ σ I) (UInt256.ofNat (2 ^ 128)))
    (UInt256.ofNat (2 ^ 128 - 1))

theorem evalProtocolFeesToken0 (locals imms : Store) (evm : EVM.State)
    (hbase : locals.get? "protocolFees" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"protocolFees", [.field "token0"]⟩) =
      .ok (.int (Int.ofNat (protocolFeesToken0Word evm.accountMap evm.executionEnv).toNat)) := by
  apply evalExpr_storage_scalar_value (t := .int (.uint ⟨128, by decide⟩))
    (er := ⟨"protocolFees", [.field "token0"]⟩)
    (loc := { slot := ⟨3⟩, offset := 0, size := 16,
              type := .int (.uint ⟨128, by decide⟩), hbound := by decide }) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, EvalResult.bind, bind, pure])
    (by dsimp only; decide +kernel) poolStorageBackend_eq rfl
  rw [storageLocLoad_uint_offset0 _ _ _ _ rfl (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv ⟨3⟩ rfl]
  rfl

theorem evalProtocolFeesToken1 (locals imms : Store) (evm : EVM.State)
    (hbase : locals.get? "protocolFees" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"protocolFees", [.field "token1"]⟩) =
      .ok (.int (Int.ofNat (protocolFeesToken1Word evm.accountMap evm.executionEnv).toNat)) := by
  apply evalExpr_storage_scalar_value (t := .int (.uint ⟨128, by decide⟩))
    (er := ⟨"protocolFees", [.field "token1"]⟩)
    (loc := { slot := ⟨3⟩, offset := 16, size := 16,
              type := .int (.uint ⟨128, by decide⟩), hbound := by decide }) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, EvalResult.bind, bind, pure])
    (by dsimp only; decide +kernel) poolStorageBackend_eq rfl
  rw [storageLocLoad_uint_offset _ _ _ _ _ rfl (by decide) (by decide),
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv ⟨3⟩ rfl]
  rfl

-- LIBRARY CANDIDATE: Reasoning.Storage, extract any byte-aligned scalar storage field.
theorem storageLocLoad_elem_offset (evm : EVM.State) (slot : UInt256)
    (offset : Fin 32) (size : Fin 33) (ty : ABI.ElemType)
    {hbound : offset.val + size.val - 1 < 32}
    (hoff : 8 * offset.val < 256) (hsize : 8 * size.val ≤ 256) :
    storageLocLoad evm
        { slot := slot, offset := offset, size := size, hbound := hbound, type := ty } =
      wordToElem ty (UInt256.land
        (UInt256.div (EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (256 ^ offset.val))) (UInt256.ofNat (256 ^ size.val - 1))) := by
  unfold storageLocLoad
  dsimp only
  congr
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof
    (EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract
      offset.val (offset.val + size.val)) = _
  rw [List.extract_eq_take_drop, Nat.add_sub_cancel_left]
  exact fromBytes'_drop_take_wordLE_land_div_mask _ offset.val size.val hoff hsize

theorem evalTickBitmap (locals imms : Store) (evm : EVM.State) (key : Int)
    (hbase : locals.get? "tickBitmap" = none)
    (hkey : locals.get? "arg0" = some (.int key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"tickBitmap", [.mindex (.var "arg0")]⟩) =
      .ok (.int (Int.ofNat (solcSlotWordAt (solcMappingSlot ⟨6⟩ (EVM.wordOfInt key))
        evm.accountMap evm.executionEnv).toNat)) := by
  rw [Std.HashMap.get?_eq_getElem?] at hkey
  apply evalExpr_storage_scalar_value
    (t := .int (.uint ⟨256, by decide⟩))
    (er := ⟨"tickBitmap", [.mindex (.int key)]⟩)
    (loc := uint256Loc (solcMappingSlot ⟨6⟩ (EVM.wordOfInt key))) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, hkey, valueToKey?, EvalResult.bind, bind, pure, EvalResult.ofOption])
    (by rfl) poolStorageBackend_eq rfl
  rw [storageLocLoad_uint256,
    storageLoad_codeOwner_eq_solcSlotWordAt evm evm.executionEnv _ rfl]


end Benchmarks.UniswapV3.Pool

