import Benchmarks.CompoundIII.Comet.UserCollateralRead
import Benchmarks.CompoundIII.Comet.TotalsCollateralStorage
import Benchmarks.CompoundIII.Comet.PackedStateWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: replace the low uint128 while preserving the upper uint128.
def low128WriteWord (old data : UInt256) : UInt256 :=
  UInt256.lor (low128 data) (UInt256.land (UInt256.lnot ⟨2^128-1⟩) old)

theorem low128WriteWord_packed (old data : UInt256) :
    packedWriteWord old data 0 16 = low128WriteWord old data := by
  let x : BitVec 256 := ⟨old.val⟩
  let y : BitVec 256 := ⟨data.val⟩
  rw [packedWriteWord_bitvec x y 0 16 (by decide) (by decide) (by decide)]
  have hb : x % BitVec.ofNat 256 (256^0) +
      BitVec.ofNat 256 (256^0) * (y % BitVec.ofNat 256 (256^16)) +
      BitVec.ofNat 256 (256^(0+16)) * (x / BitVec.ofNat 256 (256^(0+16))) =
      (y &&& BitVec.ofNat 256 (2^128-1)) ||| ((~~~BitVec.ofNat 256 (2^128-1)) &&& x) := by
    bv_decide
  rw [hb]
  apply congrArg UInt256.mk
  simp only [low128, UInt256.land, UInt256.lnot,
    BitVec.toFin_and, BitVec.toFin_or, BitVec.toFin_not]
  rfl

theorem sourceState_low128Write {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (slot data : UInt256) :
    SourceState s0 I
      (sstoreAccountMap I.codeOwner σ slot (low128WriteWord (solcSlotWordAt slot σ I) data))
      (storePackedWord evm slot data 0 16) := by
  have hw := hs.readModifyWrite slot (fun old ↦ packedWriteWord old data 0 16)
  change SourceState _ _ _ (storePackedWord evm slot data 0 16) at hw
  rw [low128WriteWord_packed] at hw
  exact hw

theorem writeUserCollateralBalance (evm : EVM.State) (account asset : AccountAddress)
    (word : UInt256) :
    config.storageBackend.write
      ⟨"userCollateral", [.mindex (.address account), .mindex (.address asset), .field "balance"]⟩
      (.elem (.int (.uint ⟨128, by decide⟩))) (.int word.toNat) evm =
      .ok (storePackedWord evm (userCollateralSlot account asset) word 0 16) := by
  apply solidityStorageBackend_write_elem _ _ _ _ _ _
    { slot := userCollateralSlot account asset, offset := 0, size := 16, hbound := by decide,
      type := .int (.uint ⟨128, by decide⟩) }
  · simp only [userCollateralSlot, solcMappingSlot, keyValueToWord_address]; rfl
  · exact storageLocStore_packed_int evm _ word _ _ _

theorem assignUserCollateralBalance (frame : Frame) (evm : EVM.State)
    (account asset : AccountAddress) (accountExpr assetExpr : Expr) (word : UInt256)
    (hc : frame.contract = contract) (hu : frame.locals.get? "userCollateral" = none)
    (ha : evalExpr? config frame evm accountExpr = .ok (.address account))
    (hb : evalExpr? config frame evm assetExpr = .ok (.address asset)) :
    assignStorageRef? config frame evm .storage
      ⟨"userCollateral", [.mindex accountExpr, .mindex assetExpr, .field "balance"]⟩
      (.int word.toNat) =
      .ok (frame, storePackedWord evm (userCollateralSlot account asset) word 0 16) := by
  apply assignStorageRef_storage_typed hu
    (er := ⟨"userCollateral", [.mindex (.address account), .mindex (.address asset),
      .field "balance"]⟩) (ty := .elem (.int (.uint ⟨128, by decide⟩)))
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, ha, hb,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · rw [hc]; rfl
  · exact writeUserCollateralBalance evm account asset word

theorem writeTotalsCollateralBalance (evm : EVM.State) (asset : AccountAddress)
    (word : UInt256) :
    config.storageBackend.write
      ⟨"totalsCollateral", [.mindex (.address asset), .field "totalSupplyAsset"]⟩
      (.elem (.int (.uint ⟨128, by decide⟩))) (.int word.toNat) evm =
      .ok (storePackedWord evm (totalsCollateralSlot asset) word 0 16) := by
  apply solidityStorageBackend_write_elem _ _ _ _ _ _
    { slot := totalsCollateralSlot asset, offset := 0, size := 16, hbound := by decide,
      type := .int (.uint ⟨128, by decide⟩) }
  · simp only [totalsCollateralSlot, solcMappingSlot, keyValueToWord_address]; rfl
  · exact storageLocStore_packed_int evm _ word _ _ _

theorem assignTotalsCollateralBalance (frame : Frame) (evm : EVM.State)
    (asset : AccountAddress) (assetExpr : Expr) (word : UInt256)
    (hc : frame.contract = contract) (hu : frame.locals.get? "totalsCollateral" = none)
    (ha : evalExpr? config frame evm assetExpr = .ok (.address asset)) :
    assignStorageRef? config frame evm .storage
      ⟨"totalsCollateral", [.mindex assetExpr, .field "totalSupplyAsset"]⟩ (.int word.toNat) =
      .ok (frame, storePackedWord evm (totalsCollateralSlot asset) word 0 16) := by
  apply assignStorageRef_storage_typed hu
    (er := ⟨"totalsCollateral", [.mindex (.address asset), .field "totalSupplyAsset"]⟩)
    (ty := .elem (.int (.uint ⟨128, by decide⟩)))
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, ha,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · rw [hc]; rfl
  · exact writeTotalsCollateralBalance evm asset word

end Benchmarks.CompoundIII.Comet
