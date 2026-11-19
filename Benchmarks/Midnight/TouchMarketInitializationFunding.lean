import Benchmarks.Midnight.TouchMarketValidationFunding
import Benchmarks.Midnight.InitMarketStorageFunding

/-! Validation and ordered writes bring both executions to market-code deployment. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

-- GENERALIZES midnightTouchMarketInitialization with retained funding.
theorem midnightTouchMarketInitialization_funded {credit : Nat} {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr limit root id ret : UInt256}
    {k C : Nat} {R : List UInt256} {frame : Frame} (m : MarketData)
    (hstack : R.length + 18 ≤ 1024) (hm : MarketStored mem ptr arrayPtr limit m)
    (hlimit : limit.toNat ≤ root.toNat) (hb : root.toNat + 224 < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hc : frame.contract = contract)
    (hmarket : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hl : frame.locals.get? "isLltvEnabled" = none)
    (hcu : frame.locals.get? "isLiquidationCursorEnabled" = none)
    (hd : frame.locals.get? "defaultSettlementFeeCbp" = none)
    (hcont : frame.locals.get? "defaultContinuousFee" = none)
    (hfund : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode evm.executionEnv g s0 ⟨20764⟩
      ((ptr + UInt256.ofNat 32) :: ptr :: id :: ret :: R) mem aw rdata evm.accountMap k C) :
    (RDrev midnightBytecode g s0 ∧ ExecBlock config frame evm touchMarketInitBody .reverted) ∨
    (RDstatic midnightBytecode g s0 ∧ ExecBlock config frame evm touchMarketInitBody .staticViolation) ∨
    (∃ frame' mem' aw' k' C',
      evm.executionEnv.perm = true ∧ frame'.contract = contract ∧
      frame'.locals.get? "market" = some (Model.marketValue m.value) ∧
      frame'.locals.get? "id" = some (wordBytes32Value id) ∧
      (∀ result, ExecBlock config frame' (initMarketStorageState evm id m.loanToken)
        (touchMarketInitBody.drop 18) result → ExecBlock config frame evm touchMarketInitBody result) ∧
      MemoryPrefix mem mem' limit.toNat ∧
      memLoad (UInt256.ofNat 64) mem' = root + UInt256.ofNat 224 ∧
      MemoryFunding credit mem' aw' C' ∧
      RD midnightBytecode evm.executionEnv g s0 ⟨24347⟩
        (UInt256.ofNat 21556 :: ptr :: id :: ret :: R) mem' aw' rdata
        (initMarketStorageState evm id m.loanToken).accountMap k' C') := by
  rcases midnightTouchMarketValidation_funded m (by omega) hm hc hmarket hl hcu hfund rd with
    hrev | ⟨previous, f, mm, aw1, k1, C1, hs, hf, hlocals, hp, hfree1, hfund1, rd1⟩
  · exact Or.inl hrev
  · have hbase1 := (hlocals "marketState" (by decide)).trans hbase
    have hid1 := (hlocals "id" (by decide)).trans hid
    cases hperm : evm.executionEnv.perm with
    | false =>
      exact Or.inr (Or.inl ⟨midnightInitMarketStatic (by omega) hperm rd1,
        hs.run (initMarketSourceStatic hf.contract hbase1 hid1 hperm)⟩)
    | true =>
      have hd1 := (hlocals "defaultSettlementFeeCbp" (by decide)).trans hd
      have hcont1 := (hlocals "defaultContinuousFee" (by decide)).trans hcont
      obtain ⟨aw2, k2, C2, hfund2, rd2⟩ := midnightInitMarketStores_funded m hstack (hm.preserve hp)
        hlimit hb (hfree1.trans hfree) hperm hfund1 rd1
      let f' := initMarketFeesFrame f id (initMarketDefaultWord evm id m.loanToken)
      refine Or.inr (Or.inr ⟨f', _, aw2, k2, C2, rfl, hf.contract, ?_, ?_, ?_,
        hp.trans (initMarketStoreMemory_prefix mm root evm id m.loanToken limit.toNat hlimit),
        initMarketStoreMemory_free mm root evm id m.loanToken, hfund2, rd2⟩)
      · rw [initMarketFeesFrame_get _ _ _ _ (by decide) (by decide)]; exact hf.market
      · rw [initMarketFeesFrame_get _ _ _ _ (by decide) (by decide)]; exact hid1
      · intro result htail
        exact hs.run (initMarketSourceStores hf.contract hf.market hbase1 hid1 hd1 hcont1 hperm htail)

end Benchmarks.Midnight
