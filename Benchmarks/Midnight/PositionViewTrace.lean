import Benchmarks.Midnight.SlashCreditTrace
import Benchmarks.Midnight.SlashPendingTrace
import Benchmarks.Midnight.PositionAccrualTrace
import Benchmarks.Midnight.PositionViewFinish

/-! Complete internal position-view bytecode trace, with every arithmetic revert path. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightPositionViewInternal {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr id user ret maturity : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (hcanon : user.toNat < EVM.addressModulus)
    (hlo : 64 ≤ (ptr + UInt256.ofNat 128).toNat)
    (hhi : (ptr + UInt256.ofNat 128).toNat + 32 ≤ mem.size)
    (hmaturity : memLoad (ptr + UInt256.ofNat 128) mem = maturity)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨22775⟩ (ptr :: id :: user :: ret :: R)
      mem aw rdata σ k C) :
    let w0 := solcSlotWordAt (positionSlot id user) σ I
    let w1 := solcSlotWordAt (positionSlot id user + ⟨1⟩) σ I
    let credit := low128 w0
    let pending := UInt256.shiftRight w0 (UInt256.ofNat 128)
    let lastLoss := low128 w1
    let loss := UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I) (UInt256.ofNat 128)
    let lastAccrual := UInt256.shiftRight w1 (UInt256.ofNat 128)
    let time := UInt256.ofNat I.header.timestamp
    let pc := slashCredit credit lastLoss loss
    let pp := slashPending credit pending pc
    let fee := positionAccruedFee pp lastAccrual maturity time
    (¬ PositionViewSafe credit pending lastLoss loss lastAccrual maturity time ∧
      RDrev midnightBytecode g s0) ∨
    (PositionViewSafe credit pending lastLoss loss lastAccrual maturity time ∧
      ∃ aw' k' C', RD midnightBytecode I g s0 ret
        (fee :: UInt256.sub (low128 pp) fee :: UInt256.sub (low128 pc) fee :: R)
        (positionSlashMemory mem id user lastLoss) aw' rdata σ k' C') := by
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightSlashCredit (by omega) (by omega) hcanon rd
  rcases midnightSlashPending hstack rd1 with ⟨hbad, hr⟩ | ⟨hsafe, k2, C2, rd2⟩
  · exact Or.inl ⟨fun h ↦ hbad h.1, hr⟩
  · have hm : memLoad (ptr + UInt256.ofNat 128)
        (positionSlashMemory mem id user
          (low128 (solcSlotWordAt (positionSlot id user + ⟨1⟩) σ I))) = maturity := by
      rw [positionSlashMemory_load _ _ _ _ _ hlo hhi, hmaturity]
    rcases midnightPositionAccrual hstack hm rd2 with ⟨hbad, hr⟩ | ⟨haccrual, aw3, k3, C3, rd3⟩
    · exact Or.inl ⟨fun h ↦ hbad h.2.1, hr⟩
    · rcases midnightPositionViewFinish (by omega) (positionAccruedFee_lt _ _ _ _) hret rd3 with
        ⟨hbad, hr⟩ | ⟨hcredit, hpending, k4, C4, rd4⟩
      · exact Or.inl ⟨fun h ↦ hbad h.2.2, hr⟩
      · exact Or.inr ⟨⟨hsafe, haccrual, hcredit, hpending⟩, _, _, _, rd4⟩

end Benchmarks.Midnight
