import Benchmarks.Midnight.PositionViewValues
import Benchmarks.Midnight.PositionStorage
import Benchmarks.Midnight.CheckedUint128
import Benchmarks.Midnight.RuntimeBlocks_088

/-! The two checked balance decreases preceding a position update. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

abbrev updatePositionTopic : UInt256 :=
  UInt256.ofNat 65051904546040886552841725652773437537374545310863051550280193416781215868796

theorem midnightPositionUpdateDecrease {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id user credit pending fee ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (hc : credit.toNat < 2^128) (hp : pending.toNat < 2^128)
    (rd : RD midnightBytecode I g s0 ⟨23680⟩
      ([fee, pending, credit, updatePositionTopic, id, positionSlot id user,
        solcAddrMask, ret, ⟨96⟩, user] ++ R) mem aw rdata σ k C) :
    let w := solcSlotWordAt (positionSlot id user) σ I
    let oldCredit := low128 w
    let oldPending := UInt256.shiftRight w (UInt256.ofNat 128)
    (¬ (credit.toNat ≤ oldCredit.toNat ∧ pending.toNat ≤ oldPending.toNat) ∧ RDrev midnightBytecode g s0) ∨
    (credit.toNat ≤ oldCredit.toNat ∧ pending.toNat ≤ oldPending.toNat ∧
      ∃ k' C', RD midnightBytecode I g s0 ⟨23723⟩
        ([UInt256.sub oldPending pending, ⟨23855⟩, positionSlot id user, user, solcAddrMask,
          ⟨96⟩, updatePositionTopic, id, UInt256.sub oldCredit credit, credit, ret, fee, pending] ++ R)
        mem aw rdata σ k' C') := by
  let w := solcSlotWordAt (positionSlot id user) σ I
  let oldCredit := low128 w
  let oldPending := UInt256.shiftRight w (UInt256.ofNat 128)
  change RD midnightBytecode I g s0 ⟨23680⟩
    (fee :: pending :: credit :: updatePositionTopic :: id :: positionSlot id user ::
      solcAddrMask :: ret :: ⟨96⟩ :: user :: R) mem aw rdata σ k C at rd
  obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_23680 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_23680_stack, uint128Mask_computed] at rd1
  by_cases hcredit : credit.toNat ≤ oldCredit.toNat
  · obtain ⟨k2, C2, rd2⟩ := midnightCheckedSub128 (by simp only [List.length_cons]; omega)
      (low128_lt _) hc hcredit (by jump_dest) rd1
    have rd3 := midnightBlocks.midnight_block_23714 (by simp only [List.length_cons]; omega)
      (by jump_dest) rd2
    simp only [midnightBlocks.midnight_block_23714_stack] at rd3
    by_cases hpending : pending.toNat ≤ oldPending.toNat
    · obtain ⟨k4, C4, rd4⟩ := midnightCheckedSub128 (by simp only [List.length_cons]; omega)
        (shiftRight128_lt _) hp hpending (by jump_dest) rd3
      exact Or.inr ⟨hcredit, hpending, _, _, rd4⟩
    · exact Or.inl ⟨fun h ↦ hpending h.2,
        midnightCheckedSub128Revert (by simp only [List.length_cons]; omega)
          (shiftRight128_lt _) hp (Nat.lt_of_not_ge hpending) rd3⟩
  · exact Or.inl ⟨fun h ↦ hcredit h.1,
      midnightCheckedSub128Revert (by simp only [List.length_cons]; omega)
        (low128_lt _) hc (Nat.lt_of_not_ge hcredit) rd1⟩

end Benchmarks.Midnight
