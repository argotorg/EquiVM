import Benchmarks.Midnight.LiquidateMaxRepaidTrace
import Benchmarks.Midnight.LiquidateMaxRepaidSource
import Reasoning.ExternalCall

/-! Source/runtime agreement for the current-debt read and maximum repayment. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem liquidateMaxRepaidStep {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw id borrower maxDebt lif lltv price root : UInt256} {credit : Nat}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 11 ≤ 1024)
    (hc : frame.contract = contract) (hcanon : borrower.toNat < EVM.addressModulus)
    (hp : frame.locals.get? "_position" = some (.storageRef (positionRef id borrower) positionType))
    (hm : frame.locals.get? "maxDebt" = some (.int maxDebt.toNat))
    (hl : frame.locals.get? "lif" = some (.int lif.toNat))
    (hll : frame.locals.get? "lltv" = some (.int lltv.toNat))
    (hs : SourceState s0 I σ evm) (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨7014⟩
      (maxDebt :: lltv :: lif :: price :: positionSlot id borrower :: R) mem aw rdata σ k C) :
    let cap := liquidateMaxRepaid (low128 (healthPositionWord evm id borrower)) maxDebt lif lltv
    (ExecStmt config frame evm (liquidateRcfBody[0]!) .reverted ∧ RDrev midnightBytecode g s0) ∨
    (ExecStmt config frame evm (liquidateRcfBody[0]!)
        (.ok (wordLocal frame "maxRepaid" cap) evm) ∧ ∃ k' C',
      TransferBudget root credit mem aw C' ∧
      RD midnightBytecode I g s0 ⟨7134⟩
        (cap :: lif :: price :: positionSlot id borrower :: R) mem aw rdata σ k' C') := by
  dsimp only
  have hw : healthPositionWord evm id borrower =
      solcSlotWordAt (positionSlot id borrower + UInt256.ofNat 2) σ I := hs.storageRead _
  have htrace := midnightLiquidateMaxRepaid hstack rd
  dsimp only at htrace
  rw [← hw] at htrace
  have hsource := liquidateMaxRepaidSource (evm := evm) hc hcanon hp hm hl hll
  rcases htrace with ⟨hbad, hrev⟩ | ⟨hsafe, k1, C1, hc1, rd1⟩
  · rcases hsource with ⟨_, hsrev⟩ | ⟨hsafe, _⟩
    · exact Or.inl ⟨hsrev, hrev⟩
    · exact (hbad hsafe).elim
  · rcases hsource with ⟨hbad, _⟩ | ⟨_, hsok⟩
    · exact (hbad hsafe).elim
    · exact Or.inr ⟨hsok, k1, C1, hb.mono hc1, rd1⟩

end Benchmarks.Midnight
