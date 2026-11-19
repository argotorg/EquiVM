import Benchmarks.Midnight.TouchMarketInternal
import Benchmarks.Midnight.MarketIdFunding
import Benchmarks.Midnight.MarketHashFunding

/-! Large collateral lists either use an existing market or fail initialization. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightTouchMarketLarge_funded {evm : EVM.State} {g : Sat256} {s0 : State}
    {imms : Store} {mem rdata : ByteArray} {aw root ptr arrayPtr ret : UInt256}
    {k C : Nat} {R : List UInt256} (m : MarketData) (hstack : R.length + 26 ≤ 1024)
    (hm : MarketStored mem ptr arrayPtr root m) (hlarge : 128 < m.collaterals.length)
    (hroot : root.toNat ≤ mem.size) (hgas : midnightGasBound g.toUInt256)
    (ha : MemoryAccounting mem aw C)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode evm.executionEnv g s0 ⟨20557⟩ (ptr :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev midnightBytecode g s0 ∧ ExecFuncBody config (touchMarketCallFrame imms m)
      evm touchMarketFunction.body .reverted) ∨
    (root.toNat + 2 * m.encodingSize + 288 < 2^64 ∧
      ExecFuncBody config (touchMarketCallFrame imms m) evm touchMarketFunction.body
        (.returned (touchMarketIdFrame imms m) evm (some [wordBytes32Value m.id])) ∧
      ∃ aw' k' C', MemoryFunding (128 * m.collaterals.length)
        (touchMarketHashMemory mem root m) aw' C' ∧
        RD midnightBytecode evm.executionEnv g s0 ret (m.id :: R)
          (touchMarketHashMemory mem root m) aw' rdata evm.accountMap k' C') := by
  rcases midnightMarketIdTrace_funded m (by simp only [List.length_cons]; omega)
      hm hm.collateralCount hroot hgas ha hfree rd with
    hoog | ⟨hb, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inl hoog
  have hlo : 96 ≤ root.toNat := by
    have := hm.lower; have := hm.array; have := hm.extent; omega
  have hp := touchMarketHashMemory_prefix mem m hlo hb
  rcases midnightMarketHashCheck_funded m (by omega) hlo hb hret ha1 rd1 with
    ⟨hexists, aw2, k2, C2, ha2, rd2⟩ | ⟨hnew, aw2, k2, C2, ha2, rd2⟩
  · exact Or.inr (Or.inr ⟨hb, touchMarketExistingSource evm imms m hexists,
      aw2, k2, C2, ha2, rd2⟩)
  · have hcond : evalExpr? config (touchMarketIdFrame imms m) evm touchMarketCondition =
        .ok (.bool true) := by
      rw [touchMarketCondition_eval, hnew]
      rfl
    have hsrcMarket : (touchMarketIdFrame imms m).locals.get? "market" =
        some (Model.marketValue m.value) := by
      simp only [touchMarketIdFrame, resumeAfterInternalCall, touchMarketCallFrame,
        touchMarketArguments, store_get_ne _ _ (show ("id" == "market") = false from rfl),
        store_get_self]
    rcases midnightTouchMarketHeader m (by omega) (hm.preserve hp) rd2 with
      ⟨hbad, hrev⟩ | ⟨hgood, _⟩
    · refine Or.inr (Or.inl ⟨hrev, ExecFuncBody.execBlockRevert ?_⟩)
      apply (touchMarketIdPrefix evm imms m).run
      exact ExecBlock.consRevert (ExecStmt.iteTrue hcond (touchMarketHeaderRevert hsrcMarket hbad))
    · have hn := hgood.2.2.2.2.2
      omega

end Benchmarks.Midnight
