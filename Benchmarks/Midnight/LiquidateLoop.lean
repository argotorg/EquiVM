import Benchmarks.Midnight.LiquidateLoopStep
import Benchmarks.Midnight.LiquidateMemoryPreserved

/-! The complete liquidation collateral loop terminates and preserves its transfer budget. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateLoop {I : ExecutionEnv} {g : Sat256} {s0 : State} {m : MarketData}
    {id seized repaid borrower mode originalDebt debtWord reverseRep rep dp dl receiverWord
      selector budgetRoot heap : UInt256} {receiver callback : AccountAddress} {data : ByteArray}
    {credit : Nat} {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : I.fork ≥ .osaka)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (fuel : Nat) (evm : State) (frame : Frame) (mem rdata : ByteArray)
    (aw root bitmap maxDebt savedPrice badDebt : UInt256) (σ : AccountMap) (k C : Nat)
    (hfuel : fuel ≤ 128) (hbits : bitmap.toNat < 2^fuel)
    (hroot : root.toNat + 160 * fuel < 2^64) (hlower : 832 ≤ root.toNat)
    (hheap : heap.toNat ≤ root.toNat) (hm : 832 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hbitmap : memLoad (UInt256.ofNat 704) mem = bitmap)
    (hzero : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hmarket : MarketStored mem ⟨832⟩ ⟨1088⟩ heap m)
    (hf : LiquidateSourceFrame frame m id (calldataWord I.calldata 36)
      seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt savedPrice originalDebt badDebt)
    (hs : SourceState s0 I σ evm) (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨5340⟩
      ([debtWord, reverseRep, rep, maxDebt, savedPrice, positionSlot id borrower, dp, dl,
        borrower, badDebt, receiverWord, mode, selector] ++ R) mem aw rdata σ k C) :
    (ExecStmt config frame evm liquidateLoop .reverted ∧ RDrev midnightBytecode g s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (frame' : Frame) (mem' out : ByteArray)
      (root' maxDebt' savedPrice' badDebt' aw' : UInt256) (k' C' : Nat),
      ExecStmt config frame evm liquidateLoop (.ok frame' evm') ∧
      SourceState s0 I σ' evm' ∧ accountStorageStateEq evm.accountMap evm'.accountMap ∧
      LiquidateSourceFrame frame' m id (calldataWord I.calldata 36)
        seized repaid borrower mode receiver callback data ∧
      LiquidateAccumulators frame' ⟨0⟩ maxDebt' savedPrice' originalDebt badDebt' ∧
      MarketStored mem' ⟨832⟩ ⟨1088⟩ heap m ∧
      memLoad (UInt256.ofNat 64) mem' = root' ∧
      memLoad (UInt256.ofNat 704) mem' = ⟨0⟩ ∧ memLoad (UInt256.ofNat 800) mem' = ⟨0⟩ ∧
      root.toNat ≤ root'.toNat ∧ root'.toNat ≤ root.toNat + 160 * fuel ∧
      root'.toNat % 32 = root.toNat % 32 ∧
      LiquidateMemoryPreserved mem mem' root.toNat ∧ TransferBudget budgetRoot credit mem' aw' C' ∧
      RD midnightBytecode I g s0 ⟨5358⟩
        ([debtWord, reverseRep, rep, maxDebt', savedPrice', positionSlot id borrower, dp, dl,
          borrower, badDebt', receiverWord, mode, selector] ++ R) mem' aw' out σ' k' C' := by
  induction fuel using Nat.strong_induction_on generalizing evm frame mem rdata aw root bitmap
      maxDebt savedPrice badDebt σ k C with
  | h fuel ih =>
    by_cases hz : bitmap.toNat = 0
    · have hzeroBitmap : bitmap = ⟨0⟩ := u256_inj hz
      rw [hzeroBitmap] at ha hbitmap
      have rd1 := midnightBlocks.midnight_block_5340_fallthrough
        (R := [debtWord, reverseRep, rep, maxDebt, savedPrice, positionSlot id borrower,
          dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        (by rw [hbitmap]; decide) rd
      have hb1 := transferBudgetAt (root := budgetRoot) (credit := credit) rd1
        (by transfer_budget hb)
      exact Or.inr ⟨evm, σ, frame, mem, rdata, root, maxDebt, savedPrice, badDebt, _, _, _,
        ExecStmt.whileFalse ((evalHealthLoopCond ha.bitmap).trans (by rfl)), hs,
        accountStorageStateEq_refl _, hf, ha, hmarket, hfree, hbitmap, hzero,
        le_rfl, by omega, rfl, .refl _ _, hb1, rd1⟩
    · have hi : (bitmapMsb bitmap).toNat < fuel := bitmapMsb_lt hz hbits
      have h128 : bitmap.toNat < 2^128 :=
        lt_of_lt_of_le hbits (Nat.pow_le_pow_right (by decide) hfuel)
      have h160 : root.toNat + 160 < 2^64 := by omega
      rcases midnightLiquidateLoopStep hstack hfork hcanon hd h128 hz h160 hlower hm
          hfree hbitmap hzero hf ha hs hb rd with
        ⟨hbody, hrev⟩ | ⟨evm1, σ1, frame1, preMem, out1, max1, price1, bad1, aw1, k1, C1,
          hbody, hs1, hstorage1, hf1, ha1, hp1, hfree1, hb1, rd1⟩
      · exact Or.inl ⟨ExecStmt.whileRevert
          ((evalHealthLoopCond ha.bitmap).trans (by rw [decide_eq_true hz])) hbody, hrev⟩
      · let bitmap1 := bitmapClear bitmap (bitmapMsb bitmap)
        let mem1 := liquidateBitmapMemory preMem bitmap1
        have hp1' : LiquidateMemoryPreserved mem mem1 root.toNat := hp1.liquidateClear bitmap1
        have hnext : (root + UInt256.ofNat 160).toNat = root.toNat + 160 :=
          uadd_word_ofNat_toNat root 160 (by change _ < 2^256; omega)
        have hfree1' : memLoad (UInt256.ofNat 64) mem1 = root + UInt256.ofNat 160 := by
          rw [liquidateBitmapMemory_preserved bitmap1 (UInt256.ofNat 64)
            (by change 96 ≤ preMem.size; have := hp1.size; omega) (Or.inl (by decide)), hfree1]
        have hzero1 : memLoad (UInt256.ofNat 800) mem1 = ⟨0⟩ :=
          (hp1'.load (UInt256.ofNat 800) (by decide) hlower hm (Or.inr (by decide))).trans hzero
        have hmarket1 : MarketStored mem1 ⟨832⟩ ⟨1088⟩ heap m :=
          (hmarket.preserve (hp1.mono hheap)).writeWord_below bitmap1 (by decide)
        rcases ih (bitmapMsb bitmap).toNat hi evm1 frame1 mem1 out1 aw1
            (root + UInt256.ofNat 160) bitmap1 max1 price1 bad1 σ1 k1 C1
            (by omega) (bitmapClear_msb_lt hz) (by rw [hnext]; omega)
            (by rw [hnext]; omega) (by rw [hnext]; omega) (hm.trans hp1'.size)
            hfree1' (liquidateBitmapMemory_load _ _) hzero1 hmarket1 hf1 ha1 hs1 hb1 rd1 with
          ⟨hloop, hrev⟩ | ⟨evm2, σ2, frame2, mem2, out2, root2, max2, price2, bad2, aw2, k2, C2,
            hloop, hs2, hstorage2, hf2, ha2, hmarket2, hfree2, hbitmap2, hzero2,
            hlo2, hhi2, hmod2, hp2, hb2, rd2⟩
        · exact Or.inl ⟨ExecStmt.whileTrue
            ((evalHealthLoopCond ha.bitmap).trans (by rw [decide_eq_true hz])) hbody hloop, hrev⟩
        · refine Or.inr ⟨evm2, σ2, frame2, mem2, out2, root2, max2, price2, bad2, aw2, k2, C2,
            ExecStmt.whileTrue
              ((evalHealthLoopCond ha.bitmap).trans (by rw [decide_eq_true hz])) hbody hloop,
            hs2, accountStorageStateEq_trans hstorage1 hstorage2, hf2, ha2, hmarket2,
            hfree2, hbitmap2, hzero2, by omega, by omega, ?_,
            hp1'.trans (hp2.mono (by omega)), hb2, rd2⟩
          rw [hmod2, hnext]
          omega

end Benchmarks.Midnight
