import Benchmarks.Midnight.TouchMarketInternal
import Benchmarks.Midnight.MarketIdAccounting

/-! The complete touchMarket routine under the unchanged contract gas bound. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightTouchMarketInternal_bounded {evm : EVM.State} {g : Sat256} {s0 : State}
    {imms : Store} {mem rdata : ByteArray} {aw root ptr arrayPtr ret : UInt256}
    {k C : Nat} {R : List UInt256} (m : MarketData) (hstack : R.length + 26 ≤ 1024)
    (hm : MarketStored mem ptr arrayPtr root m)
    (hroot : root.toNat ≤ mem.size) (hgas : midnightGasBound g.toUInt256)
    (ha : MemoryAccounting mem aw C)
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
  by_cases hb : root.toNat + 5 * m.encodingSize + 800 < 2^64
  · exact midnightTouchMarketInternal m hstack hm hb hfree hw hret rd
  rcases memoryAccounting_headroom rd ha hgas with hoog | hroom
  · exact Or.inl hoog
  have hlarge : 128 < m.collaterals.length := by
    by_contra hn
    apply hb
    dsimp only [MarketData.encodingSize]
    omega
  rcases midnightMarketIdTrace_accounted m (by simp only [List.length_cons]; omega)
      hm hm.collateralCount hroot hgas ha hfree rd with
    hoog | ⟨hb0, aw0, k0, C0, _, _⟩
  · exact Or.inl hoog
  have hlo : 96 ≤ root.toNat := by
    have hl := hm.lower
    have ha := hm.array
    have he := hm.extent
    omega
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
    rcases midnightTouchMarketHeader m (by omega) (hm.preserve hp) rd1 with
      ⟨hbad, hrev⟩ | ⟨hgood, _⟩
    · refine Or.inr (Or.inl ⟨hrev, ExecFuncBody.execBlockRevert ?_⟩)
      apply (touchMarketIdPrefix evm imms m).run
      exact ExecBlock.consRevert (ExecStmt.iteTrue hcond (touchMarketHeaderRevert hsrcMarket hbad))
    · have hn := hgood.2.2.2.2.2
      omega

end Benchmarks.Midnight
