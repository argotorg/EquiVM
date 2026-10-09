import Benchmarks.Morpho.MorphoBlue.SupplyCallbackTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoSupplyTail {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out data : ByteArray} {aw fp srcOff len assets shares account : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (hl : SupplyLocals p assets shares account data locals) (hs : SourceState s0 ee σ evm) (hp : ee.perm = true)
    (hm : MorphoHeap mem fp 160) (hsize : 160 ≤ mem.size) (hptr : 160 ≤ fp.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat fp.toNat)))
    (hget6 : locals.get? "__c6" = some (.int (Int.ofNat assets.toNat)))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (htoken : memLoad (UInt256.ofNat 128) mem = p.loanToken)
    (hfit : (marketFieldWord σ ee p.id 0).toNat + assets.toNat < 2 ^ 128)
    (hlen : len.toNat ≤ solcMaxU64) (hsrc : srcOff.toNat + len.toNat ≤ ee.calldata.size)
    (hdata : ee.calldata.readWithPadding srcOff.toNat len.toNat = data) (hdataSize : data.size = len.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4124)
      ((marketFieldWord σ ee p.id 0 + assets) :: supplyStoreTail σ ee p.id assets shares account srcOff len [])
      mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (supplyTransition.body.drop 16) supplyTransition.returnType := by
  have hass := morphoAccrueAssetsAssign p locals imms evm ⟨0, by decide⟩ "__c6" assets hl.toMarketLocals
    (by simp only [evalExpr?, hget6, EvalResult.ofOption]) (by simpa only [hs.env, ← hs.accounts] using hfit)
  let e1 := storeMarketField evm p.id ⟨0, by decide⟩ (marketFieldWord evm.accountMap evm.executionEnv p.id 0 + assets)
  let σ1 := storeMarketFieldAccounts σ ee p.id ⟨0, by decide⟩ (marketFieldWord σ ee p.id 0 + assets)
  have hs1 : SourceState s0 ee σ1 e1 := by
    simpa only [e1, σ1, hs.env, ← hs.accounts] using storeMarketField_bridge hs p.id ⟨0, by decide⟩
      (marketFieldWord σ ee p.id 0 + assets)
  have hevent : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
      (supplyTransition.body.drop 16) { contract := contract, locals := locals, immutables := imms } e1
      (supplyTransition.body.drop 18) :=
    (StateBlock.start.step hass).step (supplyEmit p assets shares account data locals imms e1 hl)
  obtain ⟨a1, k1, C1, rd1⟩ := morphoSupplyStoreEvent (v := v) (by decide) hp hm.free (accrueAssetSumClean hfit) h
  obtain ⟨hm1, hpref⟩ := hm.twoWordEvent (by decide) assets shares
  have hm2 := hm1.weaken (by decide : 0 ≤ 160)
  have hz1 : memLoad (UInt256.ofNat 96) (twoWordEventMem mem fp assets shares) = UInt256.ofNat 0 := by
    rw [memoryPrefix_memLoad hpref _ (by decide) (by change 128 ≤ fp.toNat; omega) (by change 128 ≤ mem.size; omega)]
    exact hzero
  have ht1 : memLoad (UInt256.ofNat 128) (twoWordEventMem mem fp assets shares) = p.loanToken := by
    rw [memoryPrefix_memLoad hpref (UInt256.ofNat 128) (by decide) hptr hsize]; exact htoken
  by_cases hz : len = UInt256.ofNat 0
  · rw [if_pos hz] at rd1
    have hd : data.size = 0 := by rw [hdataSize, hz]; rfl
    have hg : evalExpr? config { contract := contract, locals := locals, immutables := imms } e1
        (.binary .gt (.arrayLength .localVar ⟨"data", []⟩) (.intLit 0)) = .ok (.bool false) := by
      rw [supplyDataGuard hl imms e1, hd]; rfl
    have hab : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
        (supplyTransition.body.drop 16) { contract := contract, locals := locals, immutables := imms } e1
        (supplyTransition.body.drop 19) := hevent.step (ExecStmt.iteFalse hg ExecBlock.nil)
    exact (morphoSupplyTransfer p locals imms hc hl hs1 hm2 (le_trans hsize hpref.size) hptr hget hz1 ht1 rd1).prepend hab
  · rw [if_neg hz] at rd1
    have hn : 0 < data.size := by
      rw [hdataSize]
      exact Nat.pos_of_ne_zero (fun h0 => hz (uint256_toNat_eq_zero h0))
    exact (morphoSupplyCallbackTail p locals imms hc hl hs1 hm2 (le_trans hsize hpref.size) hptr hget hz1 ht1
      hn hlen hsrc hdata hdataSize rd1).prepend hevent

end Benchmarks.Morpho.MorphoBlue
