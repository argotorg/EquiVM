import Benchmarks.Morpho.MorphoBlue.LiquidateBadHighReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive LiquidateBadHighRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets seized shares account badAssets badShares srcOff len : UInt256)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (fp : UInt256) (spare : Nat) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateBadBody.drop 10) .reverted → RDrev (deployedRuntime v) g s0 →
      LiquidateBadHighRefines v ee g s0 p assets seized shares account badAssets badShares srcOff len locals imms evm mem fp spare R
  | ok {evm' σ' mem' aw' out' k' C'} :
      ExecBlock config { contract := contract, locals := locals, immutables := imms }
        evm (liquidateBadBody.drop 10) (.ok { contract := contract, locals := locals, immutables := imms } evm') →
      SourceState s0 ee σ' evm' → MorphoHeap mem' fp spare → HeapAdvance mem fp mem' fp 0 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2574)
        (liquidateEventTail (UInt256.ofNat (deployedRuntime v).size) p.id assets seized shares badAssets badShares srcOff len R)
        mem' aw' out' σ' k' C' →
      LiquidateBadHighRefines v ee g s0 p assets seized shares account badAssets badShares srcOff len locals imms evm mem fp spare R

theorem morphoLiquidateBadHighRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets seized shares account badAssets badShares srcOff len : UInt256} {out mem data : ByteArray}
    {σ : AccountMap} {k C spare : Nat} {R : List UInt256} (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 48 ≤ 1024) (hperm : ee.perm = true)
    (ha : account.toNat < EVM.addressModulus) (haccount : calldataWord ee.calldata 164 = account)
    (hl : LiquidateEventLocals p account seized shares data assets badAssets badShares locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp spare) (hget : locals.get? "__c20" = some (.int (Int.ofNat badShares.toNat)))
    (hbs : badShares.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3140)
      ([badShares, UInt256.ofNat 3169] ++ liquidateBadTail p.id assets seized shares badAssets badShares srcOff len R)
      mem aw out σ k C) :
    LiquidateBadHighRefines v ee g s0 p assets seized shares account badAssets badShares srcOff len locals imms evm mem fp spare R := by
  have hecast : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "__c20") = .ok (.int (Int.ofNat badShares.toNat)) := by
    simp only [evalExpr?, hget, EvalResult.ofOption]
  obtain ⟨a1, k1, C1, rd1⟩ := morphoLiquidateBadHighReachSub (v := v) (by omega) h
  have hb : (marketFieldWord σ ee p.id 3).toNat < 2 ^ 128 := halfWord_bound _ _
  by_cases hf : badShares.toNat ≤ (marketFieldWord σ ee p.id 3).toNat
  swap
  · exact .reverted (ExecBlock.consRevert (morphoMarketSubtractAssignReverts p locals imms evm ⟨3, by decide⟩
      "__c20" badShares hl.toMarketLocals hecast (by simpa only [hs.env, ← hs.accounts] using Nat.lt_of_not_ge hf)))
      (morphoCheckedSub128Reverts (v := v) (ret := UInt256.ofNat 2278)
        (R := [marketFieldSlot p.id 3, UInt256.ofNat 3169] ++ liquidateBadTail p.id assets seized shares badAssets badShares srcOff len R) (by change R.length + 13 + 6 ≤ 1024; omega) hb hbs (Nat.lt_of_not_ge hf) rd1)
  let e1 := storeMarketField evm p.id ⟨3, by decide⟩ (UInt256.sub (marketFieldWord evm.accountMap evm.executionEnv p.id 3) badShares)
  let σ1 := storeMarketFieldAccounts σ ee p.id ⟨3, by decide⟩ (UInt256.sub (marketFieldWord σ ee p.id 3) badShares)
  have hs1 : SourceState s0 ee σ1 e1 := by
    simpa only [e1, σ1, hs.env, ← hs.accounts] using storeMarketField_bridge hs p.id ⟨3, by decide⟩
      (UInt256.sub (marketFieldWord σ ee p.id 3) badShares)
  have hass := morphoMarketSubtractAssign p locals imms evm ⟨3, by decide⟩ "__c20" badShares hl.toMarketLocals hecast
    (by simpa only [hs.env, ← hs.accounts] using hf)
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedSub128Ok (v := v) (ret := UInt256.ofNat 2278)
    (R := [marketFieldSlot p.id 3, UInt256.ofNat 3169] ++ liquidateBadTail p.id assets seized shares badAssets badShares srcOff len R) (by change R.length + 13 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hb hbs hf rd1
  obtain ⟨k3, C3, rd3⟩ := morphoStoreUint128High (v := v) (dest := UInt256.ofNat 3169)
    (R := liquidateBadTail p.id assets seized shares badAssets badShares srcOff len R) (by change R.length + 11 + 7 ≤ 1024; omega)
    hperm (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [usub_toNat hf]; omega) rd2
  have hezero : evalExpr? config { contract := contract, locals := locals, immutables := imms } e1
      (.intLit 0) = .ok (.int (Int.ofNat (UInt256.ofNat 0).toNat)) := by simp only [evalExpr?, pure]; rfl
  have hclear : ExecStmt config { contract := contract, locals := locals, immutables := imms } e1
      liquidateBadBody[11]! (.ok { contract := contract, locals := locals, immutables := imms }
        (storePositionPacked e1 p.id account false (UInt256.ofNat 0))) :=
    ExecStmt.assign hezero (assignPositionPacked e1 locals imms _ _ p.id account false (UInt256.ofNat 0)
      (by decide) ha hl.position (hl.evalId imms e1) (hl.evalBorrower imms e1))
  have he : ExecBlock config { contract := contract, locals := locals, immutables := imms } evm
      (liquidateBadBody.drop 10) (.ok { contract := contract, locals := locals, immutables := imms }
        (storePositionPacked e1 p.id account false (UInt256.ofNat 0))) :=
    ExecBlock.consNormal hass (ExecBlock.consNormal hclear ExecBlock.nil)
  obtain ⟨a4, k4, C4, rd4⟩ := morphoLiquidateBadClear (v := v) (by omega) hperm ha haccount rd3
  have hm1 := hm.hash p.id (UInt256.ofNat 3)
  have had := ((heapAdvance_hash mem fp p.id (UInt256.ofNat 3)).trans
    (heapAdvance_hash _ fp p.id (UInt256.ofNat 2))).trans
    (heapAdvance_hash _ fp account (solcMappingSlot ⟨2⟩ p.id))
  exact .ok he (storePositionPacked_bridge hs1 p.id account false (UInt256.ofNat 0))
    ((hm1.hash p.id (UInt256.ofNat 2)).hash account (solcMappingSlot ⟨2⟩ p.id))
    (by simpa only [Nat.zero_add] using had) rd4

end Benchmarks.Morpho.MorphoBlue
