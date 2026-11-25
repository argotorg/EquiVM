import Benchmarks.Midnight.LiquidateEventSource
import Benchmarks.Midnight.LiquidateEventTrace
import Benchmarks.Midnight.MarketCollateralToken

variable {fork : Ethereum.Fork}

/-! Paired execution of the liquidation event and its collateral-index check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidateEvent {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw root budgetRoot id index seized repaid borrower mode badDebt dp dl : UInt256}
    {receiver callback payer : AccountAddress} {data : ByteArray} {m : MarketData}
    {credit : Nat} {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 24 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (hpay : frame.locals.get? "payer" = some (.address payer))
    (hbad : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hd : decodeCalldataMarket I.calldata 4 = some m) (hi : calldataWord I.calldata 36 = index)
    (hroot : root.toNat < 2^64) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hslot : memLoad (UInt256.ofNat 672) mem = solcMappingSlot ⟨1⟩ id)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized)
    (hpaid : memLoad (UInt256.ofNat 608) mem = repaid)
    (hs : SourceState s0 I σ evm) (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨5508⟩
      ([mode, dp, dl, borrower, badDebt, UInt256.ofNat receiver.val, UInt256.ofNat payer.val] ++ R)
      mem aw rdata σ k C) :
    (ExecStmt fork config frame evm (liquidateTransition.body[20]!) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    (ExecStmt fork config frame evm (liquidateTransition.body[20]!) .staticViolation ∧
      RDstatic fork midnightBytecode g s0) ∨
    (index.toNat < m.collaterals.length ∧ I.perm = true ∧ ∃ mem' aw' k' C',
      ExecStmt fork config frame evm (liquidateTransition.body[20]!) (.ok frame evm) ∧
      mem.size ≤ mem'.size ∧
      (∀ read : UInt256, read.toNat + 32 ≤ mem.size → read.toNat + 32 ≤ root.toNat →
        memLoad read mem' = memLoad read mem) ∧
      TransferBudget budgetRoot credit mem' aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨20488⟩
        ([⟨4⟩ + calldataWord I.calldata 4, calldataWord I.calldata 4 + ⟨100⟩,
          ⟨5734⟩, ⟨5750⟩, UInt256.ofNat receiver.val, ⟨5543⟩, ⟨5755⟩, dp, dl, borrower, badDebt,
          UInt256.ofNat receiver.val, UInt256.ofNat payer.val] ++ R) mem' aw' rdata σ k' C') := by
  have hlookup := midnightMarketCollateralToken
    (R := [mode, dp, dl, borrower, badDebt, UInt256.ofNat receiver.val, UInt256.ofNat payer.val] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hd rd
  rw [hi] at hlookup
  rcases hlookup with ⟨hbadIndex, hr⟩ | ⟨hidx, k1, C1, hc1, rd1⟩
  · exact Or.inl ⟨liquidateEventIndexRevert hf hbadIndex, hr⟩
  · have hargs := liquidateEventArgs_eval (evm := evm) hf hpay hbad hidx
    rcases midnightLiquidateEvent (R := R) (by omega) hroot hlo hsize hfree hslot hseized hpaid
      (hb.mono hc1) rd1 with ⟨hp, hr⟩ | ⟨hp, aw2, k2, C2, hb2, rd2⟩
    · exact Or.inr (Or.inl ⟨ExecStmt.emitStatic hargs (by rw [hs.env]; exact hp), hr⟩)
    · let loss := UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I) (UInt256.ofNat 128)
      let fee := UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + UInt256.ofNat 1) σ I)
        (UInt256.ofNat 128)
      let mem2 := liquidateEventMemory mem root I seized repaid mode
        (UInt256.ofNat receiver.val) (UInt256.ofNat payer.val) badDebt loss fee
      exact Or.inr (Or.inr ⟨hidx, hp, mem2, aw2, k2, C2,
        ExecStmt.emit (by rw [hs.env]; exact hp) hargs,
        liquidateEventMemory_size_ge ..,
        fun read hin hbelow ↦ liquidateEventMemory_load_below _ _ _ _ _ _ _ _ _ _ _ _ hin hbelow,
        hb2, rd2⟩)

end Benchmarks.Midnight
