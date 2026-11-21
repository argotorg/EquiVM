import Benchmarks.Midnight.LiquidateAmountFrames
import Benchmarks.Midnight.LiquidateSeizeTrace
import Benchmarks.Midnight.LiquidateRepayTrace
import Benchmarks.Midnight.MemorySnapshot

/-! Paired amount conversion, retaining argument locals and all other reserved memory words. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem liquidateAmountsConversion {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw id index seized repaid borrower mode bitmap maxDebt price
      originalDebt badDebt lltv lif root : UInt256} {credit : Nat}
    {receiver callback : AccountAddress} {data : ByteArray} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 14 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt)
    (hll : frame.locals.get? "lltv" = some (.int lltv.toNat))
    (hl : frame.locals.get? "lif" = some (.int lif.toNat))
    (hcs : calldataWord I.calldata 68 = seized) (hcr : calldataWord I.calldata 100 = repaid)
    (hms : memLoad ⟨640⟩ mem = seized) (hmr : memLoad ⟨608⟩ mem = repaid)
    (hsize : 672 ≤ mem.size) (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨6639⟩ (maxDebt :: lltv :: lif :: price :: R)
      mem aw rdata σ k C) :
    (ExecStmt config frame evm (liquidateAmountsBody[4]!) .reverted ∧
      RDrev midnightBytecode g s0) ∨
    ∃ frame' seized' repaid' mem' aw' k' C',
      ExecStmt config frame evm (liquidateAmountsBody[4]!) (.ok frame' evm) ∧
      LiquidateSourceFrame frame' m id index seized' repaid' borrower mode receiver callback data ∧
      LiquidateAccumulators frame' bitmap maxDebt price originalDebt badDebt ∧
      frame'.locals.get? "lltv" = some (.int lltv.toNat) ∧
      frame'.locals.get? "lif" = some (.int lif.toNat) ∧
      memLoad ⟨640⟩ mem' = seized' ∧ memLoad ⟨608⟩ mem' = repaid' ∧
      mem.size ≤ mem'.size ∧
      (∀ read : UInt256, read.toNat + 32 ≤ mem.size →
        (read.toNat + 32 ≤ 608 ∨ 672 ≤ read.toNat) → memLoad read mem' = memLoad read mem) ∧
      TransferBudget root credit mem' aw' C' ∧
      RD midnightBytecode I g s0 ⟨6731⟩ (maxDebt :: lltv :: lif :: price :: R)
        mem' aw' rdata σ k' C' := by
  have hcs' : uInt256OfByteArray (I.calldata.readBytes 68 32) = seized := hcs
  by_cases hz : seized = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_6639_taken
      (R := maxDebt :: lltv :: lif :: price :: R)
      (by simp only [List.length_cons]; omega)
      (by simpa only [show (UInt256.ofNat 68).toNat = 68 from rfl, hcs', hz] using
        (show UInt256.isZero ⟨0⟩ ≠ UInt256.ofNat 0 by decide)) (by jump_dest) rd
    have hsource := liquidateRepaySource (evm := evm) hf.contract hf.seized hf.repaid ha.price hl
      (by rw [hz]; rfl)
    rcases midnightLiquidateRepay (R := R) (by omega) hcr (hb.mono (by omega)) rd1 with
      ⟨hbad, hrev⟩ | ⟨hsafe, aw2, k2, C2, hb2, rd2⟩
    · rcases hsource with ⟨_, hsrev⟩ | ⟨hsafe, _⟩
      · exact Or.inl ⟨hsrev, hrev⟩
      · exact (hbad hsafe).elim
    · rcases hsource with ⟨hbad, _⟩ | ⟨_, hsok⟩
      · exact (hbad hsafe).elim
      · refine Or.inr ⟨_, _, repaid, _, aw2, k2, C2, hsok,
          liquidateRepayFrame_arguments hf, liquidateRepayFrame_accumulators ha,
          ?_, ?_, memLoad_writeWord _ _ _, ?_, ?_, ?_, hb2, rd2⟩
        · rw [liquidateRepayFrame_get _ _ _ _ _ (by decide)]; exact hll
        · rw [liquidateRepayFrame_get _ _ _ _ _ (by decide)]; exact hl
        · rw [memLoad_writeWord_preserved _ _ _ _ (by change 640 ≤ mem.size; omega)
            (Or.inl (by decide))]
          exact hmr
        · rw [writeWord_sparse_size]; omega
        · intro read hin hdisj
          exact memLoad_writeWord_preserved _ _ _ _ hin (by
            rcases hdisj with h | h
            · exact Or.inl (by change read.toNat + 32 ≤ 640; omega)
            · exact Or.inr h)
  · have hpos : 0 < seized.toNat := by
      by_contra hn
      exact hz (uint256_toNat_eq_zero (by omega))
    have rd1 := midnightBlocks.midnight_block_6639_fallthrough
      (R := maxDebt :: lltv :: lif :: price :: R)
      (by simp only [List.length_cons]; omega)
      (by simpa only [show (UInt256.ofNat 68).toNat = 68 from rfl, hcs'] using
        isZero_eq_zero_of_ne hz) rd
    have hsource := liquidateSeizeSource (evm := evm) hf.contract hf.seized hf.repaid ha.price hl hpos
    rcases midnightLiquidateSeize (R := R) hstack hms (hb.mono (by omega)) rd1 with
      ⟨hbad, hrev⟩ | ⟨hsafe, aw2, k2, C2, hb2, rd2⟩
    · rcases hsource with ⟨_, hsrev⟩ | ⟨hsafe, _⟩
      · exact Or.inl ⟨hsrev, hrev⟩
      · exact (hbad hsafe).elim
    · rcases hsource with ⟨hbad, _⟩ | ⟨_, hsok⟩
      · exact (hbad hsafe).elim
      · refine Or.inr ⟨_, seized, _, _, aw2, k2, C2, hsok,
          liquidateSeizeFrame_arguments hf, liquidateSeizeFrame_accumulators ha,
          ?_, ?_, ?_, memLoad_writeWord _ _ _, ?_, ?_, hb2, rd2⟩
        · rw [liquidateSeizeFrame_get _ _ _ _ _ (by decide)]; exact hll
        · rw [liquidateSeizeFrame_get _ _ _ _ _ (by decide)]; exact hl
        · exact (memLoad_writeWord_preserved mem 608 (⟨640⟩ : UInt256)
            (liquidateRepaidAmount seized price lif) hsize (Or.inr (by decide))).trans hms
        · rw [writeWord_sparse_size]; omega
        · intro read hin hdisj
          exact memLoad_writeWord_preserved _ _ _ _ hin (by
            rcases hdisj with h | h
            · exact Or.inl h
            · exact Or.inr (by change 608 + 32 ≤ read.toNat; omega))

end Benchmarks.Midnight
