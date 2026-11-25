import Benchmarks.Midnight.CollateralLoopSource
import Benchmarks.Midnight.CollateralValidationTrace

variable {fork : Ethereum.Fork}

/-! The complete collateral-validation loop, coupling source execution with bytecode reachability. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000 in
theorem midnightCollateralValidationLoop {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr root id ret : UInt256} {k C : Nat}
    {R : List UInt256} {frame : Frame} (m : MarketData) (previous : AccountAddress)
    (i remaining : Nat) (hi : i + remaining = m.collaterals.length)
    (hstack : R.length + 15 ≤ 1024) (hm : MarketStored mem ptr arrayPtr root m)
    (hf : CollateralSourceFrame frame m i previous)
    (rd : RD fork midnightBytecode evm.executionEnv g s0 ⟨20840⟩
      (UInt256.ofNat previous.val :: ret :: ptr :: (ptr + UInt256.ofNat 96) :: id ::
        UInt256.ofNat i :: R) mem aw rdata evm.accountMap k C) :
    (RDrev fork midnightBytecode g s0 ∧
      ExecForLoop fork config frame evm collateralLoopCondition collateralLoopPost collateralLoopBody
        .reverted) ∨
    (∃ previous' frame' mem' aw' k' C',
      CollateralSourceFrame frame' m m.collaterals.length previous' ∧
      CollateralLocalsPreserved frame frame' ∧ MemoryPrefix mem mem' root.toNat ∧
      memLoad (UInt256.ofNat 64) mem' = memLoad (UInt256.ofNat 64) mem ∧
      ExecForLoop fork config frame evm collateralLoopCondition collateralLoopPost collateralLoopBody
        (.ok frame' evm) ∧
      RD fork midnightBytecode evm.executionEnv g s0 ⟨21130⟩
        (arrayPtr :: UInt256.ofNat previous'.val :: ret :: ptr :: (ptr + UInt256.ofNat 96) :: id ::
          UInt256.ofNat m.collaterals.length :: R) mem' aw' rdata evm.accountMap k' C') := by
  induction remaining generalizing i previous frame mem aw k C with
  | zero =>
    have he : i = m.collaterals.length := by omega
    have hc : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat m.collaterals.length) = ⟨0⟩ :=
      ult_zero (by rw [he])
    obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_20840_taken_packed (by omega) (by
      rw [hm.arrayPtr, hm.length, hc]; decide) (by jump_dest) rd
    right
    refine ⟨previous, frame, mem, aw1, k1, C1, he ▸ hf, .refl _, .refl _ _, rfl, ?_, ?_⟩
    · exact ExecForLoop.falseDone ((evalCollateralLoopCondition hf).trans
        (by rw [decide_eq_false (by omega)]))
    · simpa only [midnightBlocks.midnight_block_20840_taken_stack, hm.arrayPtr, he] using rd1
  | succ remaining ih =>
    have hlt : i < m.collaterals.length := by omega
    let c := m.collaterals[i]
    have hcond := (evalCollateralLoopCondition (cfg := config) (evm := evm) hf).trans
      (by rw [decide_eq_true hlt])
    rcases midnightCollateralValidationStep m previous c i hlt rfl hstack hm rd with
      ⟨hbad, hr⟩ | ⟨hs, aw1, k1, C1, rd1⟩
    · exact Or.inl ⟨hr, ExecForLoop.bodyRevert hcond
        (collateralValidationSourceRevert hf hlt rfl hbad)⟩
    · have hbody := collateralValidationSource (fork := fork) hf hlt rfl hs
      have hf1 := collateralStepFrame_inv hf c
      have hi64 : i < 2^64 := lt_trans hlt hm.collateralCount
      have hpost := collateralPostSource (fork := fork) (cfg := config) (evm := evm) hf1 (by
        change i + 1 < 2^256; omega)
      have hf2 := collateralPostFrame_inv hf1
      have hp := collateralValidationMemory_prefix mem c root.toNat
      have hm1 := hm.preserve hp
      rcases ih c.token (i + 1) (by omega) hm1 hf2 rd1 with
        ⟨hr, hloop⟩ | ⟨p, f, mm, aw2, k2, C2, hf3, hlocals, hmem, hfree, hloop, rd2⟩
      · exact Or.inl ⟨hr, ExecForLoop.iterate hcond hbody hpost hloop⟩
      · right
        refine ⟨p, f, mm, aw2, k2, C2, hf3, ?_, hp.trans hmem, ?_,
          ExecForLoop.iterate hcond hbody hpost hloop, rd2⟩
        · exact ((collateralStepFrame_preserved frame c).trans
            (collateralPostFrame_preserved _ i)).trans hlocals
        · exact hfree.trans (collateralValidationMemory_free mem c (by
            have hlo := hm.lower; have hms := hm.words.size
            change ptr.toNat + 32 * 8 ≤ mem.size at hms
            omega))

end Benchmarks.Midnight
