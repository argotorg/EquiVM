import Benchmarks.Morpho.MorphoBlue.SupplyCollateralSourceStart
import Benchmarks.Morpho.MorphoBlue.SupplyCollateralUpdateReach
import Benchmarks.Morpho.MorphoBlue.StateBlock

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem SupplyCollateralLocals.evalCollateral {p assets account data locals}
    (hl : SupplyCollateralLocals p assets account data locals) (imms : Store) (evm : EVM.State)
    (ha : account.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"position", [.mindex (.var "id"), .mindex (.var "onBehalf"), .field "collateral"]⟩) =
      .ok (.int (Int.ofNat (positionFieldWord evm.accountMap evm.executionEnv p.id account 2).toNat)) :=
  evalMorphoPositionField evm locals imms _ _ p.id account 2 hl.position
    (hl.evalId imms evm) (hl.evalAccount imms evm) ha

theorem morphoSupplyCollateralAssign (p : MarketParamsWords) (assets account : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (hl : SupplyCollateralLocals p assets account data locals)
    (ha : account.toNat < EVM.addressModulus)
    (hi : locals.get? "__c1" = some (.int (Int.ofNat assets.toNat)))
    (hf : (positionFieldWord evm.accountMap evm.executionEnv p.id account 2).toNat + assets.toNat < 2 ^ 128) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      supplyCollateralTransition.body[8]!
      (.ok { contract := contract, locals := locals, immutables := imms }
        (storePositionPacked evm p.id account true (positionFieldWord evm.accountMap evm.executionEnv p.id account 2 + assets))) := by
  have he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "__c1") =
      .ok (.int (Int.ofNat assets.toNat)) := by simp only [evalExpr?, hi, EvalResult.ofOption]
  apply ExecStmt.assign (evalCheckedUint128AddOk (hl.evalCollateral imms evm ha) he hf)
  apply assignPositionPacked evm locals imms (.var "id") (.var "onBehalf") p.id account true _ _ ha hl.position
    (hl.evalId imms evm) (hl.evalAccount imms evm)
  rw [uadd_toNat, Nat.mod_eq_of_lt (show
    (positionFieldWord evm.accountMap evm.executionEnv p.id account 2).toNat + assets.toNat < UInt256.size by
      change _ < 2 ^ 256; omega)]
  exact hf

theorem morphoSupplyCollateralAssignReverts (p : MarketParamsWords) (assets account : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (hl : SupplyCollateralLocals p assets account data locals)
    (ha : account.toNat < EVM.addressModulus)
    (hi : locals.get? "__c1" = some (.int (Int.ofNat assets.toNat)))
    (hf : 2 ^ 128 ≤ (positionFieldWord evm.accountMap evm.executionEnv p.id account 2).toNat + assets.toNat) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      supplyCollateralTransition.body[8]! .reverted := by
  have he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "__c1") =
      .ok (.int (Int.ofNat assets.toNat)) := by simp only [evalExpr?, hi, EvalResult.ofOption]
  exact ExecStmt.assignExprRevert (evalCheckedUint128AddReverts (hl.evalCollateral imms evm ha) he hf)

inductive SupplyCollateralUpdateRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets account srcOff len : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms } evm
      (supplyCollateralTransition.body.drop 7) .reverted → RDrev (deployedRuntime v) g s0 →
      SupplyCollateralUpdateRefines v ee g s0 p assets account srcOff len data locals imms evm R
  | static : ExecBlock config { contract := contract, locals := locals, immutables := imms } evm
      (supplyCollateralTransition.body.drop 7) .staticViolation → RDstatic (deployedRuntime v) g s0 →
      SupplyCollateralUpdateRefines v ee g s0 p assets account srcOff len data locals imms evm R
  | ok {evm' σ' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms } evm
        (supplyCollateralTransition.body.drop 7)
        { contract := contract, locals := locals.insert "__c1" (.int (Int.ofNat assets.toNat)), immutables := imms } evm'
        (supplyCollateralTransition.body.drop 9) → SourceState s0 ee σ' evm' → ee.perm = true →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10235)
        (supplyCollateralUpdateTail p.id assets account srcOff len R) (supplyCollateralPositionMem p account) aw' out' σ' k' C' →
      SupplyCollateralUpdateRefines v ee g s0 p assets account srcOff len data locals imms evm R

theorem morphoSupplyCollateralUpdateRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {aw assets account srcOff len : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (p : MarketParamsWords) (data : ByteArray) (locals imms : Store)
    (hstack : R.length + 28 ≤ 1024) (ha : account.toNat < EVM.addressModulus)
    (hl : SupplyCollateralLocals p assets account data locals) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10184)
      (supplyCollateralUpdateTail p.id assets account srcOff len R) (supplyCollateralGuardMem p) aw out σ k C) :
    SupplyCollateralUpdateRefines v ee g s0 p assets account srcOff len data locals imms evm R := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoSupplyCollateralReachCast p hstack h
  have hm := createMarketHeap_morpho (supplyCollateralGuardHeap p).1 (by decide) 64 (by decide) (lt_usize _ (by decide))
  by_cases hc : assets.toNat < 2 ^ 128
  swap
  · exact .reverted (ExecBlock.consRevert (morphoToUint128CallReverts assets evm locals imms
      (.var "assets") "__c1" (hl.evalAssets imms evm) (Nat.le_of_not_gt hc)))
      (morphoToUint128Reverts (v := v) (by change R.length + 9 + 16 ≤ 1024; omega)
        (hm.alloc64Guard (by decide)) hm.size (by rw [hm.free]; exact hm.lower)
        hm.errorGap hm.errorHi (Nat.le_of_not_gt hc) rd1)
  have hn := morphoToUint128CallOk assets evm locals imms (.var "assets") "__c1" (hl.evalAssets imms evm) hc
  let l1 := locals.insert "__c1" (.int (Int.ofNat assets.toNat))
  have hl1 : SupplyCollateralLocals p assets account data l1 := hl.insert "__c1" _ (by decide) (by decide)
  have ab1 : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
      (supplyCollateralTransition.body.drop 7) { contract := contract, locals := l1, immutables := imms } evm
      (supplyCollateralTransition.body.drop 8) := StateBlock.start.step hn
  obtain ⟨a2, k2, C2, rd2⟩ := morphoToUint128Ok (v := v) (by change R.length + 9 + 16 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (hm.alloc64Guard (by decide)) hc rd1
  obtain ⟨a3, k3, C3, rd3⟩ := morphoSupplyCollateralReachAdd p hstack rd2
  by_cases hf : (positionFieldWord σ ee p.id account 2).toNat + assets.toNat < 2 ^ 128
  swap
  · apply SupplyCollateralUpdateRefines.reverted
    · apply ab1.reverts
      apply morphoSupplyCollateralAssignReverts p assets account data l1 imms evm hl1 ha (store_get_self _ _ _)
      simpa only [hs.env, ← hs.accounts] using Nat.le_of_not_gt hf
    · exact morphoCheckedAdd128Reverts (v := v) (a := positionFieldWord σ ee p.id account 2) (by change R.length + 10 + 6 ≤ 1024; omega)
        (by change (halfWord true _).toNat < 2 ^ 128; exact halfWord_bound _ _) hc (Nat.le_of_not_gt hf) rd3
  have hass := morphoSupplyCollateralAssign p assets account data l1 imms evm hl1 ha (store_get_self _ _ _)
    (by simpa only [hs.env, ← hs.accounts] using hf)
  obtain ⟨k4, C4, rd4⟩ := morphoCheckedAdd128Ok (v := v) (a := positionFieldWord σ ee p.id account 2) (by change R.length + 10 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by change (halfWord true _).toNat < 2 ^ 128; exact halfWord_bound _ _) hc hf rd3
  by_cases hp : ee.perm = true
  swap
  · have hpf : ee.perm = false := Bool.eq_false_iff.mpr hp
    exact .static (ab1.static (execStmt_assign_static hass (by rw [hs.env]; exact hpf)))
      (morphoStoreUint128HighStatic (v := v) (by change R.length + 8 + 7 ≤ 1024; omega) hpf rd4)
  have hsum : (positionFieldWord σ ee p.id account 2 + assets).toNat < 2 ^ 128 := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (show (positionFieldWord σ ee p.id account 2).toNat + assets.toNat < UInt256.size by
      change _ < 2 ^ 256; omega)]; exact hf
  obtain ⟨k5, C5, rd5⟩ := morphoStoreUint128High (v := v) (by change R.length + 8 + 7 ≤ 1024; omega) hp
    (by rw [morphoPatchedValidJumps v]; jump_dest) hsum rd4
  apply SupplyCollateralUpdateRefines.ok (ab1.step hass) _ hp rd5
  simpa only [hs.env, ← hs.accounts] using
    storePositionPacked_bridge hs p.id account true (positionFieldWord σ ee p.id account 2 + assets)

end Benchmarks.Morpho.MorphoBlue
