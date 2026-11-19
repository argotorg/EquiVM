import Benchmarks.Midnight.TouchMarketFreshFunding
import Benchmarks.Midnight.TouchMarketHashSpace

/-! The bounded touchMarket routine retains funding, alignment and initialized extent. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES midnightTouchMarketInternal with the memory facts needed by liquidation.
set_option maxRecDepth 2000000 in
theorem midnightTouchMarketInternal_funded {evm : EVM.State} {g : Sat256} {s0 : State}
    {imms : Store} {mem rdata : ByteArray} {aw root ptr arrayPtr ret : UInt256}
    {k C : Nat} {R : List UInt256} (m : MarketData) (hstack : R.length + 26 ≤ 1024)
    (hm : MarketStored mem ptr arrayPtr root m)
    (hb : root.toNat + 5 * m.encodingSize + 800 < 2^64)
    (hroot : root.toNat ≤ mem.size) (halign : root.toNat % 32 = 0)
    (hgas : midnightGasBound g.toUInt256) (ha : MemoryAccounting mem aw C)
    (hfree : memLoad (UInt256.ofNat 64) mem = root) (hw : evm.σ₀ = s0.σ₀)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode evm.executionEnv g s0 ⟨20557⟩ (ptr :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev midnightBytecode g s0 ∧ ExecFuncBody config (touchMarketCallFrame imms m)
      evm touchMarketFunction.body .reverted) ∨
    (RDstatic midnightBytecode g s0 ∧ ExecFuncBody config (touchMarketCallFrame imms m)
      evm touchMarketFunction.body .staticViolation) ∨
    ∃ frame' evm' σ' out mem' free aw' k' C',
      SourceState s0 evm.executionEnv σ' evm' ∧
      ExecFuncBody config (touchMarketCallFrame imms m) evm touchMarketFunction.body
        (.returned frame' evm' (some [wordBytes32Value m.id])) ∧
      MemoryPrefix mem mem' root.toNat ∧ root.toNat ≤ free.toNat ∧ free.toNat < 2^64 ∧
      free.toNat ≤ root.toNat + 4 * m.encodingSize + 672 ∧
      memLoad (UInt256.ofNat 64) mem' = free ∧
      free.toNat % 32 = 0 ∧ free.toNat ≤ mem'.size + 31 ∧
      MemoryFunding 0 mem' aw' C' ∧
      RD midnightBytecode evm.executionEnv g s0 ret (m.id :: R) mem' aw' out σ' k' C' := by
  have hb0 : root.toNat + 2 * m.encodingSize + 288 < 2^64 := by omega
  have hlo : 96 ≤ root.toNat := by
    have := hm.lower; have := hm.array; have := hm.extent; omega
  have hp := touchMarketHashMemory_prefix mem m hlo hb0
  let free0 := touchMarketHashFree root m
  have hfn : free0.toNat = root.toNat + 2 * m.encodingSize + 288 := by
    rw [show free0 = marketIdPreimagePtr root m + UInt256.ofNat 128 from rfl,
      uadd_word_ofNat_toNat _ _ (by rw [(marketIdPointers m hb0).2.2]; change _ < 2^256; omega),
      (marketIdPointers m hb0).2.2]
  have hf := touchMarketHashMemory_free mem root m
  rcases midnightMarketIdTrace_funded m (by simp only [List.length_cons]; omega)
      hm hm.collateralCount hroot hgas ha hfree rd with
    hoog | ⟨_, aw0, k0, C0, hfund0, rd0⟩
  · exact Or.inl hoog
  rcases midnightMarketHashCheck_funded m (by omega) hlo hb0 hret hfund0 rd0 with
    ⟨hexists, aw1, k1, C1, hfund1, rd1⟩ | ⟨hnew, aw1, k1, C1, hfund1, rd1⟩
  · exact Or.inr (Or.inr (Or.inr ⟨_, evm, evm.accountMap, rdata, _, free0, aw1, k1, C1,
      ⟨hw, rfl, rfl⟩, touchMarketExistingSource evm imms m hexists, hp,
      by rw [hfn]; omega, by rw [hfn]; omega, by rw [hfn]; omega, hf,
      by rw [hfn]; dsimp only [MarketData.encodingSize]; omega,
      (touchMarketHashFree_space mem root m hb0).trans (by omega),
      hfund1.weaken (Nat.zero_le _), rd1⟩))
  · have hcond : evalExpr? config (touchMarketIdFrame imms m) evm touchMarketCondition =
        .ok (.bool true) := by
      rw [touchMarketCondition_eval, hnew]
      rfl
    have hsrcMarket : (touchMarketIdFrame imms m).locals.get? "market" =
        some (Model.marketValue m.value) := by
      simp only [touchMarketIdFrame, resumeAfterInternalCall, touchMarketCallFrame,
        touchMarketArguments, store_get_ne _ _ (show ("id" == "market") = false from rfl),
        store_get_self]
    rcases midnightTouchMarketFresh_funded m (frame := touchMarketIdFrame imms m)
      (by omega) (hm.preserve hp) (by rw [hfn]; omega) (by rw [hfn]; omega) hf hw rfl
      hsrcMarket (touchMarketIdFrame_other imms m _ (by decide) (by decide))
      (store_get_self _ _ _) (touchMarketIdFrame_other imms m _ (by decide) (by decide))
      (touchMarketIdFrame_other imms m _ (by decide) (by decide))
      (touchMarketIdFrame_other imms m _ (by decide) (by decide))
      (touchMarketIdFrame_other imms m _ (by decide) (by decide)) hret (hfund1.weaken (credit' := 0) (Nat.zero_le _)) rd1 with
      hoog | ⟨rev, src⟩ | ⟨stat, src⟩ |
        ⟨f, evm', σ', out, mm, aw2, k2, C2, hid, hs', src, hp', hf', hspace, hfund2, rd2⟩
    · exact Or.inl hoog
    · refine Or.inr (Or.inl ⟨rev, ExecFuncBody.execBlockRevert ?_⟩)
      apply (touchMarketIdPrefix evm imms m).run
      exact ExecBlock.consRevert (ExecStmt.iteTrue hcond src)
    · refine Or.inr (Or.inr (Or.inl ⟨stat, ExecFuncBody.execBlockStatic ?_⟩))
      apply (touchMarketIdPrefix evm imms m).run
      exact ExecBlock.consStatic (ExecStmt.iteTrue hcond src)
    · let free := marketDeploymentFree (free0 + UInt256.ofNat 224) m
      have hn224 : (free0 + UInt256.ofNat 224).toNat = free0.toNat + 224 :=
        uadd_word_ofNat_toNat _ _ (by rw [hfn]; change _ < 2^256; omega)
      have hfd : free.toNat = root.toNat + 4 * m.encodingSize + 672 := by
        have hx := (marketIdPointers (root := free0 + UInt256.ofNat 224) m
          (by rw [hn224, hfn]; omega)).2.2
        change free.toNat = _ at hx
        rw [hx, hn224, hfn]
        omega
      refine Or.inr (Or.inr (Or.inr ⟨f, evm', σ', out, mm, free, aw2, k2, C2, hs',
        ?_, hp.trans hp', by rw [hfd]; omega, by rw [hfd]; omega,
        by rw [hfd], hf',
        by rw [hfd]; dsimp only [MarketData.encodingSize]; omega,
        hspace.trans (by omega), hfund2, rd2⟩))
      apply ExecFuncBody.execBlockRet
      apply (touchMarketIdPrefix evm imms m).run
      refine ExecBlock.consNormal (ExecStmt.iteTrue hcond src) ?_
      apply ExecBlock.consReturn
      apply ExecStmt.return
      simp only [evalExprs?, evalExpr?, hid, EvalResult.ofOption, pure, bind, EvalResult.bind]


end Benchmarks.Midnight
