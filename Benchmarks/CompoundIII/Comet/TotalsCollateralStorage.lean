import Benchmarks.CompoundIII.Comet.PackedGetter

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def totalsCollateralSlot (addr : AccountAddress) : UInt256 :=
  solcMappingSlot ⟨2⟩ (EVM.word addr.val)

def totalsCollateralWord (σ : AccountMap) (I : ExecutionEnv) (addr : AccountAddress) : UInt256 :=
  solcSlotWordAt (totalsCollateralSlot addr) σ I

theorem evalTotalsCollateralFieldVar (evm : EVM.State) (locals imms : Store)
    (addr : AccountAddress) (upper : Bool) (name : Ident)
    (hlocal : locals.get? "totalsCollateral" = none)
    (harg : locals.get? name = some (.address addr)) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"totalsCollateral", [.mindex (.var name),
        .field (if upper then "_reserved" else "totalSupplyAsset")]⟩) =
      .ok (.int ((if upper then high128 else low128)
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (totalsCollateralSlot addr))).toNat) := by
  cases upper
  · apply evalExpr_storage_scalar_value (hbackend := rfl)
      (loc := { slot := totalsCollateralSlot addr
                offset := ⟨0, by decide⟩
                size := ⟨16, by decide⟩
                hbound := by decide
                type := .int (.uint ⟨128, by decide⟩) })
      (er := ⟨"totalsCollateral", [.mindex (.address addr), .field "totalSupplyAsset"]⟩)
      (t := .int (.uint ⟨128, by decide⟩)) hlocal
    · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, harg,
        valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption, Bool.false_eq_true, if_false]
    · change storageTypeAt? contract.storage
        ⟨"totalsCollateral", [.mindex (.address addr), .field "totalSupplyAsset"]⟩ = _
      rfl
    · simp only [totalsCollateralSlot, solcMappingSlot, keyValueToWord_address]
      rfl
    · exact low128_load evm (totalsCollateralSlot addr)
  · apply evalExpr_storage_scalar_value (hbackend := rfl)
      (loc := { slot := totalsCollateralSlot addr
                offset := ⟨16, by decide⟩
                size := ⟨16, by decide⟩
                hbound := by decide
                type := .int (.uint ⟨128, by decide⟩) })
      (er := ⟨"totalsCollateral", [.mindex (.address addr), .field "_reserved"]⟩)
      (t := .int (.uint ⟨128, by decide⟩)) hlocal
    · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, harg,
        valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption, if_true]
    · change storageTypeAt? contract.storage
        ⟨"totalsCollateral", [.mindex (.address addr), .field "_reserved"]⟩ = _
      rfl
    · simp only [totalsCollateralSlot, solcMappingSlot, keyValueToWord_address]
      rfl
    · exact high128_load evm (totalsCollateralSlot addr)

theorem evalTotalsCollateralField (evm : EVM.State) (locals imms : Store)
    (addr : AccountAddress) (upper : Bool)
    (hlocal : locals.get? "totalsCollateral" = none)
    (harg : locals.get? "arg0" = some (.address addr)) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"totalsCollateral", [.mindex (.var "arg0"),
        .field (if upper then "_reserved" else "totalSupplyAsset")]⟩) =
      .ok (.int ((if upper then high128 else low128)
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (totalsCollateralSlot addr))).toNat) :=
  evalTotalsCollateralFieldVar evm locals imms addr upper "arg0" hlocal harg

end Benchmarks.CompoundIII.Comet
