import Benchmarks.Midnight.LiquidateFeesSource
import Benchmarks.Midnight.LiquidateFeeEntry
import Benchmarks.Midnight.LiquidateFeeStore
import Benchmarks.Midnight.PackedStorageSourceState

variable {fork : Ethereum.Fork}

/-! Source/runtime agreement for the final remaining-fee phase of bad-debt recognition. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateFees {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw root value oldWord id : UInt256} {σ : AccountMap}
    {k C credit : Nat} {R : List UInt256} (hstack : R.length + 12 ≤ 1024)
    (hp : I.perm = true) (hzero : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hslot : memLoad (UInt256.ofNat 672) mem = solcMappingSlot ⟨1⟩ id)
    (hc : frame.contract = contract)
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType))
    (hl : frame.locals.get? "_lossFactor" = some (.int (UInt256.shiftRight oldWord ⟨128⟩).toNat))
    (hs : SourceState s0 I (storeLow128Accounts σ I (solcMappingSlot ⟨1⟩ id) value) evm)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨7603⟩
      (value :: uint128Mask :: oldWord :: R) mem aw rdata σ k C) :
    let oldLoss := UInt256.shiftRight oldWord ⟨128⟩
    let amount := liquidateFeeValue evm id oldLoss
    let evm' := marketBalanceStore evm id 2 amount
    (ExecBlock fork config frame evm (liquidateBadDebtBody.drop 8) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    (∃ σ' aw' k' C', SourceState s0 I σ' evm' ∧
      ExecBlock fork config frame evm (liquidateBadDebtBody.drop 8)
        (.ok (liquidateFeeFrame frame oldLoss amount) evm') ∧
      TransferBudget root credit mem aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨7768⟩ R mem aw' rdata σ' k' C') := by
  dsimp only
  let oldLoss := UInt256.shiftRight oldWord ⟨128⟩
  let σ1 := storeLow128Accounts σ I (solcMappingSlot ⟨1⟩ id) value
  have heperm : evm.executionEnv.perm = true := hs.env ▸ hp
  have hsource := liquidateFeesSource (fork := fork) hc hm hl heperm
  have hfee : marketBalanceWord evm id 2 = UInt256.shiftRight
      (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨1⟩) σ1 I) ⟨128⟩ := by
    change UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
      (solcMappingSlot ⟨1⟩ id + ⟨1⟩)) ⟨128⟩ = _
    rw [hs.storageRead]
    rfl
  have hloss : marketLossWord evm id = UInt256.shiftRight
      (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ1 I) ⟨128⟩ := by
    rw [marketLossWord, hs.storageRead]
    rfl
  rcases midnightLiquidateFeeEntry (R := R) (by omega) hp hzero hb rd with
    ⟨ho, aw1, k1, C1, hb1, rd1⟩ | ⟨ho, aw1, k1, C1, hb1, rd1⟩
  · simp only [hslot] at rd1
    dsimp only [σ1] at hfee hloss
    rw [← hfee, ← hloss] at rd1
    rcases midnightLiquidateFeeArithmetic hstack (marketBalanceWord_lt evm id 2)
      (shiftRight128_lt _) ho rd1 with ⟨hbad, hrev⟩ | ⟨hfit, k2, C2, hc2, rd2⟩
    · rcases hsource with ⟨_, hex⟩ | ⟨hgood, _⟩
      · exact Or.inl ⟨hex, hrev⟩
      · exact (Nat.not_lt.mpr hbad (hgood ho)).elim
    · have hgood : LiquidateFeeSafe evm id oldLoss := fun _ ↦ hfit
      obtain ⟨_, hex⟩ := hsource.resolve_left (fun h ↦ h.1 hgood)
      obtain ⟨aw3, k3, C3, hb3, rd3⟩ := midnightLiquidateFeeStore
        (R := R) (by omega) hp (hb1.mono hc2) rd2
      have hs3 := SourceState.storeHigh128 hs (solcMappingSlot ⟨1⟩ id + ⟨1⟩)
        (liquidateRemainingFees (marketBalanceWord evm id 2) oldLoss (marketLossWord evm id))
      refine Or.inr ⟨storeHigh128Accounts σ1 I (solcMappingSlot ⟨1⟩ id + ⟨1⟩)
        (liquidateRemainingFees (marketBalanceWord evm id 2) oldLoss (marketLossWord evm id)),
        aw3, k3, C3, ?_, hex, hb3, ?_⟩
      · simpa only [liquidateFeeValue, if_pos ho, marketBalanceStore, marketBalanceSlot] using hs3
      · simpa only [hslot] using rd3
  · have hgood : LiquidateFeeSafe evm id oldLoss := fun h ↦ (ho h).elim
    obtain ⟨_, hex⟩ := hsource.resolve_left (fun h ↦ h.1 hgood)
    obtain ⟨aw2, k2, C2, hb2, rd2⟩ := midnightLiquidateFeeStore (R := R) (by omega) hp hb1 rd1
    have hs2 := SourceState.storeHigh128 hs (solcMappingSlot ⟨1⟩ id + ⟨1⟩) ⟨0⟩
    refine Or.inr ⟨storeHigh128Accounts σ1 I (solcMappingSlot ⟨1⟩ id + ⟨1⟩) ⟨0⟩,
      aw2, k2, C2, ?_, hex, hb2, ?_⟩
    · simpa only [liquidateFeeValue, if_neg ho, marketBalanceStore, marketBalanceSlot] using hs2
    · simpa only [hslot] using rd2

end Benchmarks.Midnight
