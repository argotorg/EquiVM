import Benchmarks.Midnight.TouchMarketValidation
import Benchmarks.Midnight.TouchMarketHeaderFunding
import Benchmarks.Midnight.CollateralValidationLoopFunding

/-! Funding through all fresh-market validation checks. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES midnightTouchMarketValidation with retained funding.
set_option maxRecDepth 2000000 in
theorem midnightTouchMarketValidation_funded {credit : Nat} {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr root id ret : UInt256} {k C : Nat}
    {R : List UInt256} {frame : Frame} (m : MarketData)
    (hstack : R.length + 15 ≤ 1024) (hm : MarketStored mem ptr arrayPtr root m)
    (hc : frame.contract = contract)
    (hmarket : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hl : frame.locals.get? "isLltvEnabled" = none)
    (hcu : frame.locals.get? "isLiquidationCursorEnabled" = none)
    (hfund : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode evm.executionEnv g s0 ⟨20764⟩
      ((ptr + UInt256.ofNat 32) :: ptr :: id :: ret :: R) mem aw rdata evm.accountMap k C) :
    (RDrev midnightBytecode g s0 ∧ ExecBlock config frame evm touchMarketInitBody .reverted) ∨
    (∃ previous frame' mem' aw' k' C',
      ABlock config evm frame touchMarketInitBody frame' (touchMarketInitBody.drop 7) ∧
      CollateralSourceFrame frame' m m.collaterals.length previous ∧
      CollateralLocalsPreserved frame frame' ∧ MemoryPrefix mem mem' root.toNat ∧
      memLoad (UInt256.ofNat 64) mem' = memLoad (UInt256.ofNat 64) mem ∧
      MemoryFunding credit mem' aw' C' ∧
      RD midnightBytecode evm.executionEnv g s0 ⟨21130⟩
        (arrayPtr :: UInt256.ofNat previous.val :: ret :: ptr :: (ptr + UInt256.ofNat 96) :: id ::
          UInt256.ofNat m.collaterals.length :: R) mem' aw' rdata evm.accountMap k' C') := by
  rcases midnightTouchMarketHeader_funded m (by omega) hm hfund rd with ⟨hbad, hr⟩ | ⟨hs, aw1, k1, C1, hf1, rd1⟩
  · exact Or.inl ⟨hr, touchMarketHeaderRevert hmarket hbad⟩
  · have hf := touchMarketLoopFrame_inv hc hmarket hl hcu
    rcases midnightCollateralValidationLoop_funded m (AccountAddress.ofNat 0) 0 m.collaterals.length
        (by omega) hstack hm hf hf1 rd1 with
      ⟨hr, hloop⟩ | ⟨p, f, mm, aw2, k2, C2, hf2, hlocals, hmem, hfree, hloop, hf2fund, rd2⟩
    · refine Or.inl ⟨hr, (touchMarketPreviousPrefix hmarket hs).run ?_⟩
      exact ExecBlock.consRevert (ExecStmt.for (touchMarketLoopInitSource frame evm) hloop)
    · right
      refine ⟨p, f, mm, aw2, k2, C2, ?_, hf2,
        (touchMarketLoopFrame_preserved frame).trans hlocals, hmem, hfree, hf2fund, rd2⟩
      exact sourceNormalStep (touchMarketPreviousPrefix hmarket hs)
        (ExecStmt.for (touchMarketLoopInitSource frame evm) hloop)


end Benchmarks.Midnight
