import Benchmarks.Midnight.TouchMarketPrefix
import Benchmarks.Midnight.TouchMarketFresh

/-! Both branches of the shared touchMarket routine, with their source executions. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def touchMarketHashFree (root : UInt256) (m : MarketData) : UInt256 :=
  marketIdPreimagePtr root m + UInt256.ofNat 128

theorem touchMarketHashMemory_free (mem : ByteArray) (root : UInt256) (m : MarketData) :
    memLoad (UInt256.ofNat 64) (touchMarketHashMemory mem root m) = touchMarketHashFree root m := by
  rw [touchMarketHashMemory, memLoad_twoWordHashMem _ _ (UInt256.ofNat 64) (by decide) ?_,
    marketIdWorkMemory_free, touchMarketHashFree]
  dsimp only [marketIdWorkMemory, marketIdMemory]
  rw [writeWord_sparse_size]
  change 96 ≤ max _ (64 + 32)
  omega

theorem touchMarketIdFrame_other (imms : Store) (m : MarketData) (name : Ident)
    (hi : ("id" == name) = false) (hm : ("market" == name) = false) :
    (touchMarketIdFrame imms m).locals.get? name = none := by
  simp only [touchMarketIdFrame, resumeAfterInternalCall, touchMarketCallFrame,
    touchMarketArguments, store_get_ne _ _ hi, store_get_ne _ _ hm]
  simp

set_option maxRecDepth 2000000 in
theorem midnightTouchMarketInternal {evm : EVM.State} {g : Sat256} {s0 : State}
    {imms : Store} {mem rdata : ByteArray} {aw root ptr arrayPtr ret : UInt256}
    {k C : Nat} {R : List UInt256} (m : MarketData) (hstack : R.length + 26 ≤ 1024)
    (hm : MarketStored mem ptr arrayPtr root m)
    (hb : root.toNat + 5 * m.encodingSize + 800 < 2^64)
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
  rcases midnightTouchMarketPrefix m hstack hm hb0 hfree hret rd with
    ⟨hexists, aw1, k1, C1, rd1⟩ | ⟨hnew, aw1, k1, C1, rd1⟩
  · exact Or.inr (Or.inr (Or.inr ⟨_, evm, evm.accountMap, rdata, _, free0, aw1, k1, C1,
      ⟨hw, rfl, rfl⟩, touchMarketExistingSource evm imms m hexists, hp,
      by rw [hfn]; omega, by rw [hfn]; omega, by rw [hfn]; omega, hf, rd1⟩))
  · have hcond : evalExpr? config (touchMarketIdFrame imms m) evm touchMarketCondition =
        .ok (.bool true) := by
      rw [touchMarketCondition_eval, hnew]
      rfl
    have hsrcMarket : (touchMarketIdFrame imms m).locals.get? "market" =
        some (Model.marketValue m.value) := by
      simp only [touchMarketIdFrame, resumeAfterInternalCall, touchMarketCallFrame,
        touchMarketArguments, store_get_ne _ _ (show ("id" == "market") = false from rfl),
        store_get_self]
    rcases midnightTouchMarketFresh m (frame := touchMarketIdFrame imms m)
      (by omega) (hm.preserve hp) (by rw [hfn]; omega) (by rw [hfn]; omega) hf hw rfl
      hsrcMarket (touchMarketIdFrame_other imms m _ (by decide) (by decide))
      (store_get_self _ _ _) (touchMarketIdFrame_other imms m _ (by decide) (by decide))
      (touchMarketIdFrame_other imms m _ (by decide) (by decide))
      (touchMarketIdFrame_other imms m _ (by decide) (by decide))
      (touchMarketIdFrame_other imms m _ (by decide) (by decide)) hret rd1 with
      hoog | ⟨rev, src⟩ | ⟨stat, src⟩ |
        ⟨f, evm', σ', out, mm, aw2, k2, C2, hid, hs', src, hp', hf', rd2⟩
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
        by rw [hfd], hf', rd2⟩))
      apply ExecFuncBody.execBlockRet
      apply (touchMarketIdPrefix evm imms m).run
      refine ExecBlock.consNormal (ExecStmt.iteTrue hcond src) ?_
      apply ExecBlock.consReturn
      apply ExecStmt.return
      simp only [evalExprs?, evalExpr?, hid, EvalResult.ofOption, pure, bind, EvalResult.bind]

end Benchmarks.Midnight
