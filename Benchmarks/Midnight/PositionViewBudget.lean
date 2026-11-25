import Benchmarks.Midnight.SlashCreditBudget
import Benchmarks.Midnight.SlashPendingGas
import Benchmarks.Midnight.PositionAccrualBudget
import Benchmarks.Midnight.PositionViewFinishGas

variable {fork : Ethereum.Fork}

/-! The position-view routine retains transfer funding on every successful path. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightPositionViewInternal_budget {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr id user ret maturity : UInt256} {σ : AccountMap} {k C : Nat}
    {budgetRoot : UInt256} {gasCredit : Nat}
    {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (hcanon : user.toNat < EVM.addressModulus)
    (hlo : 64 ≤ (ptr + UInt256.ofNat 128).toNat)
    (hhi : (ptr + UInt256.ofNat 128).toNat + 32 ≤ mem.size)
    (hmaturity : memLoad (ptr + UInt256.ofNat 128) mem = maturity)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (hb : TransferBudget budgetRoot gasCredit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨22775⟩ (ptr :: id :: user :: ret :: R)
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
      RDrev fork midnightBytecode g s0) ∨
    (PositionViewSafe credit pending lastLoss loss lastAccrual maturity time ∧
      ∃ aw' k' C',
        TransferBudget budgetRoot gasCredit
          (positionSlashMemory mem id user lastLoss) aw' C' ∧
        RD fork midnightBytecode I g s0 ret
        (fee :: UInt256.sub (low128 pp) fee :: UInt256.sub (low128 pc) fee :: R)
        (positionSlashMemory mem id user lastLoss) aw' rdata σ k' C') := by
  obtain ⟨aw1, k1, C1, hb1, rd1⟩ := midnightSlashCredit_budget (by omega) (by omega) hcanon hb rd
  rcases midnightSlashPending_mono hstack rd1 with ⟨hbad, hr⟩ | ⟨hsafe, k2, C2, hc2, rd2⟩
  · exact Or.inl ⟨fun h ↦ hbad h.1, hr⟩
  · have hm : memLoad (ptr + UInt256.ofNat 128)
        (positionSlashMemory mem id user
          (low128 (solcSlotWordAt (positionSlot id user + ⟨1⟩) σ I))) = maturity := by
      rw [positionSlashMemory_load _ _ _ _ _ hlo hhi, hmaturity]
    rcases midnightPositionAccrual_budget hstack hm (hb1.mono hc2) rd2 with ⟨hbad, hr⟩ | ⟨haccrual, aw3, k3, C3, hb3, rd3⟩
    · exact Or.inl ⟨fun h ↦ hbad h.2.1, hr⟩
    · rcases midnightPositionViewFinish_mono (by omega) (positionAccruedFee_lt _ _ _ _) hret rd3 with
        ⟨hbad, hr⟩ | ⟨hcredit, hpending, k4, C4, hc4, rd4⟩
      · exact Or.inl ⟨fun h ↦ hbad h.2.2, hr⟩
      · exact Or.inr ⟨⟨hsafe, haccrual, hcredit, hpending⟩, _, _, _, hb3.mono hc4, rd4⟩

end Benchmarks.Midnight
