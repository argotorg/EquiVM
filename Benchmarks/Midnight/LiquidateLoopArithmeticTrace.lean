import Benchmarks.Midnight.LiquidateRecoveryDivision
import Benchmarks.Midnight.LiquidateLoopEntry
import Benchmarks.Midnight.ZeroFloorSub

/-! All arithmetic and the bitmap update in one liquidation collateral iteration. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidateRecoveryValue (collateral price lltv cursor : UInt256) : UInt256 :=
  mulDivUp (liquidateRoundedValue collateral price) lifScale (maxLif lltv cursor)

def LiquidateLoopArithmeticSafe (collateral price lltv cursor maxDebt : UInt256) : Prop :=
  HealthArithmeticSafe collateral price lltv maxDebt ∧
  MulDivUpSafe collateral price liquidatePriceScale ∧ MaxLifSafe lltv cursor ∧
  MulDivUpSafe (liquidateRoundedValue collateral price) lifScale (maxLif lltv cursor)

theorem midnightLiquidateLoopArithmetic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw maxDebt cp badDebt reverseRep rep price savedPrice pos dp dl
      borrower debtWord bitmap lltv cursor budgetRoot : UInt256}
    {credit : Nat} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 30 ≤ 1024) (hfork : I.fork ≥ .osaka)
    (hbitmap : memLoad (UInt256.ofNat 704) mem = bitmap)
    (hi : (bitmapMsb bitmap).toNat < 128)
    (hlltv : memLoad (cp + UInt256.ofNat 32) mem = lltv)
    (hcursor : memLoad (cp + UInt256.ofNat 64) mem = cursor)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨7967⟩
      (maxDebt :: cp :: badDebt :: reverseRep :: rep :: price :: savedPrice :: pos :: dp :: dl ::
        borrower :: debtWord :: R) mem aw rdata σ k C) :
    let collateral := healthCollateralWord (fun slot ↦ solcSlotWordAt slot σ I)
      (pos + ⟨3⟩) (bitmapMsb bitmap)
    (¬ LiquidateLoopArithmeticSafe collateral price lltv cursor maxDebt ∧
      RDrev midnightBytecode g s0) ∨
    (LiquidateLoopArithmeticSafe collateral price lltv cursor maxDebt ∧ ∃ aw' k' C',
      TransferBudget budgetRoot credit
        (liquidateBitmapMemory mem (bitmapClear bitmap (bitmapMsb bitmap))) aw' C' ∧
      RD midnightBytecode I g s0 ⟨5340⟩
        (debtWord :: reverseRep :: rep :: (maxDebt + healthCollateralCapacity collateral price lltv) ::
          savedPrice :: pos :: dp :: dl :: borrower ::
          zeroFloorSubWord badDebt (liquidateRecoveryValue collateral price lltv cursor) :: R)
        (liquidateBitmapMemory mem (bitmapClear bitmap (bitmapMsb bitmap))) aw' rdata σ k' C') := by
  dsimp only
  let collateral := healthCollateralWord (fun slot ↦ solcSlotWordAt slot σ I)
    (pos + ⟨3⟩) (bitmapMsb bitmap)
  rcases midnightLiquidateCollateralValue (by simp only [List.length_cons]; omega)
      hfork hbitmap hi hlltv hb rd with ⟨hbad, hrev⟩ | ⟨hs1, aw1, k1, C1, hb1, rd1⟩
  · exact Or.inl ⟨fun h ↦ hbad h.1, hrev⟩
  rcases midnightLiquidateRoundedValue (by simp only [List.length_cons]; omega)
      hlltv hcursor hb1 rd1 with ⟨hbad, hrev⟩ | ⟨hs2, aw2, k2, C2, hb2, rd2⟩
  · exact Or.inl ⟨fun h ↦ hbad h.2.1, hrev⟩
  rcases midnightMaxLif_mono (by simp only [List.length_cons]; omega) (by jump_dest) rd2 with
    ⟨hbad, hrev⟩ | ⟨hs3, k3, C3, hc3, rd3⟩
  · exact Or.inl ⟨fun h ↦ hbad h.2.2.1, hrev⟩
  rcases midnightLiquidateRecoveryDivision (by simp only [List.length_cons]; omega) rd3 with
    ⟨hbad, hrev⟩ | ⟨hs4, k4, C4, hc4, rd4⟩
  · exact Or.inl ⟨fun h ↦ hbad h.2.2.2, hrev⟩
  have hb4 := hb2.mono (show C2 ≤ C4 by omega)
  have rd5 := midnightBlocks.midnight_block_8165 (by omega) hfork (by jump_dest) rd4
  have hb5 := transferBudgetAt (root := budgetRoot) (credit := credit) rd5 (by
    unfold midnightBlocks.midnight_block_8165_memory
    transfer_budget hb4)
  have hresult := And.intro hb5 rd5
  simp only [midnightBlocks.midnight_block_8165_stack, zeroFloorSubWord_eq,
    midnightBlocks.midnight_block_8165_memory, hbitmap, uint128Mask_computed,
    writeWord_fold] at hresult
  exact Or.inr ⟨⟨hs1, hs2, hs3, hs4⟩, _, _, _, hresult⟩

end Benchmarks.Midnight
