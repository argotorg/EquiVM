import Benchmarks.CompoundIII.Comet.PackedGetter
import Benchmarks.CompoundIII.Comet.AggregateStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def userCollateralSlot (addr₀ addr₁ : AccountAddress) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨6⟩ (EVM.word addr₀.val)) (EVM.word addr₁.val)

def userCollateralWord (σ : AccountMap) (I : ExecutionEnv) (addr₀ addr₁ : AccountAddress) : UInt256 :=
  solcSlotWordAt (userCollateralSlot addr₀ addr₁) σ I

theorem readUserCollateralField (evm : EVM.State) (addr₀ addr₁ : AccountAddress)
    (upper : Bool) :
    config.storageBackend.read
      ⟨"userCollateral", [.mindex (.address addr₀), .mindex (.address addr₁),
        .field (if upper then "_reserved" else "balance")]⟩
      (.elem (.int (.uint ⟨128, by decide⟩))) evm =
      .ok (.int ((if upper then high128 else low128)
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (userCollateralSlot addr₀ addr₁))).toNat) := by
  cases upper
  · simp only [Bool.false_eq_true, if_false]
    rw [readStorage?_elem (hbackend := rfl)
      (loc := { slot := userCollateralSlot addr₀ addr₁, offset := 0, size := ⟨16, by decide⟩,
                hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      (by simp only [userCollateralSlot, solcMappingSlot, keyValueToWord_address]; rfl)]
    rw [low128_load]
  · simp only [if_true]
    rw [readStorage?_elem (hbackend := rfl)
      (loc := { slot := userCollateralSlot addr₀ addr₁, offset := ⟨16, by decide⟩,
                size := ⟨16, by decide⟩,
                hbound := by decide, type := .int (.uint ⟨128, by decide⟩) })
      (by simp only [userCollateralSlot, solcMappingSlot, keyValueToWord_address]; rfl)]
    rw [high128_load]

theorem evalUserCollateral (frame : Frame) (evm : EVM.State)
    (addr₀ addr₁ : AccountAddress) (arg₀ arg₁ : Expr) (upper : Bool)
    (hc : frame.contract = contract) (hlocal : frame.locals.get? "userCollateral" = none)
    (ha : evalExpr? config frame evm arg₀ = .ok (.address addr₀))
    (hb : evalExpr? config frame evm arg₁ = .ok (.address addr₁)) :
    evalExpr? config frame evm (.storage ⟨"userCollateral", [.mindex arg₀, .mindex arg₁,
        .field (if upper then "_reserved" else "balance")]⟩) =
      .ok (.int ((if upper then high128 else low128)
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (userCollateralSlot addr₀ addr₁))).toNat) := by
  apply evalExpr_storage_typed hlocal
    (er := ⟨"userCollateral", [.mindex (.address addr₀), .mindex (.address addr₁),
      .field (if upper then "_reserved" else "balance")]⟩)
    (ty := .elem (.int (.uint ⟨128, by decide⟩)))
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, ha, hb,
      valueToKey?, pure, bind, EvalResult.bind, EvalResult.ofOption]
  · rw [hc]; cases upper <;> rfl
  · exact readUserCollateralField evm addr₀ addr₁ upper

theorem evalUserCollateralField (evm : EVM.State) (locals imms : Store)
    (addr₀ addr₁ : AccountAddress) (upper : Bool)
    (hlocal : locals.get? "userCollateral" = none)
    (harg₀ : locals.get? "arg0" = some (.address addr₀))
    (harg₁ : locals.get? "arg1" = some (.address addr₁)) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"userCollateral", [.mindex (.var "arg0"), .mindex (.var "arg1"),
        .field (if upper then "_reserved" else "balance")]⟩) =
      .ok (.int ((if upper then high128 else low128)
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userCollateralSlot addr₀ addr₁))).toNat) := by
  exact evalUserCollateral _ evm addr₀ addr₁ (.var "arg0") (.var "arg1") upper rfl hlocal
    (by simp only [evalExpr?, harg₀, EvalResult.ofOption])
    (by simp only [evalExpr?, harg₁, EvalResult.ofOption])

end Benchmarks.CompoundIII.Comet
