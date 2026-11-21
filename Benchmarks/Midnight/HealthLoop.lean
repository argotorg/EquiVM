import Benchmarks.Midnight.HealthLoopStep

/-! The complete health loop, using the strictly decreasing highest set bit as its measure. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightHealthLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {market arrayPtr heap id user debt : UInt256} {m : MarketData} {R : List UInt256}
    (hstack : R.length + 22 ≤ 1024) (hfork : I.fork ≥ .osaka)
    (hcanon : user.toNat < EVM.addressModulus)
    (fuel : Nat) (evm : State) (frame : Frame) (mem rdata : ByteArray)
    (aw root bitmap maxDebt : UInt256) (σ : AccountMap) (k C : Nat)
    (hfuel : fuel ≤ 128) (hbitmap : bitmap.toNat < 2^fuel)
    (hroot : root.toNat + 32 * fuel < 2^64) (hheap : heap.toNat ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hm : MarketStored mem market arrayPtr heap m)
    (hf : HealthSourceFrame frame m id user bitmap maxDebt debt)
    (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I g s0 ⟨19847⟩
      ([positionSlot id user + ⟨3⟩, market, bitmap, maxDebt] ++ R) mem aw rdata σ k C) :
    (ExecStmt config frame evm healthLoop .reverted ∧ RDrev midnightBytecode g s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (frame' : Frame) (mem' out : ByteArray)
      (root' maxDebt' aw' : UInt256) (k' C' : Nat),
      ExecStmt config frame evm healthLoop (.ok frame' evm') ∧
      SourceState s0 I σ' evm' ∧ HealthSourceFrame frame' m id user ⟨0⟩ maxDebt' debt ∧
      MarketStored mem' market arrayPtr heap m ∧
      memLoad (UInt256.ofNat 64) mem' = root' ∧ heap.toNat ≤ root'.toNat ∧ root'.toNat < 2^64 ∧
      RD midnightBytecode I g s0 ⟨19831⟩
        ([positionSlot id user + ⟨3⟩, market, ⟨0⟩, maxDebt'] ++ R) mem' aw' out σ' k' C' := by
  induction fuel using Nat.strong_induction_on generalizing evm frame mem rdata aw root bitmap
      maxDebt σ k C with
  | h fuel ih =>
    by_cases hz : bitmap.toNat = 0
    · have hb : bitmap = ⟨0⟩ := u256_inj hz
      subst bitmap
      have rd1 := midnightBlocks.midnight_block_19847_taken (R := maxDebt :: R)
        (by simp only [List.length_cons]; omega) (by decide) (by jump_dest) rd
      refine Or.inr ⟨evm, σ, frame, mem, rdata, root, maxDebt, aw, _, _, ?_, hs, hf,
        hm, hfree, hheap, by omega, rd1⟩
      exact ExecStmt.whileFalse ((evalHealthLoopCond hf.bitmap).trans (by rfl))
    · have hi : (bitmapMsb bitmap).toNat < fuel := bitmapMsb_lt hz hbitmap
      have h128 : bitmap.toNat < 2^128 := lt_of_lt_of_le hbitmap (Nat.pow_le_pow_right (by decide) hfuel)
      have h32 : root.toNat + 32 < 2^64 := by omega
      rcases midnightHealthLoopStep hstack hfork hcanon h128 hz h32 hheap hfree hm hf hs rd with
        ⟨hbody, hrev⟩ | ⟨evm1, σ1, frame1, mem1, out1, max1, aw1, k1, C1,
          hbody, hs1, hf1, hm1, hfree1, rd1⟩
      · refine Or.inl ⟨?_, hrev⟩
        exact ExecStmt.whileRevert
          ((evalHealthLoopCond hf.bitmap).trans (by rw [decide_eq_true hz])) hbody
      · have hnext : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
          uadd_word_ofNat_toNat root 32 (by change _ < 2^256; omega)
        rcases ih (bitmapMsb bitmap).toNat hi evm1 frame1 mem1 out1 aw1
            (root + UInt256.ofNat 32) (bitmapClear bitmap (bitmapMsb bitmap)) max1 σ1 k1 C1
            (by omega) (bitmapClear_msb_lt hz) (by rw [hnext]; omega)
            (by rw [hnext]; omega) hfree1 hm1 hf1 hs1 rd1 with
          ⟨hloop, hrev⟩ | ⟨evm2, σ2, frame2, mem2, out2, root2, max2, aw2, k2, C2,
            hloop, hs2, hf2, hm2, hfree2, hheap2, hroot2, rd2⟩
        · refine Or.inl ⟨?_, hrev⟩
          exact ExecStmt.whileTrue
            ((evalHealthLoopCond hf.bitmap).trans (by rw [decide_eq_true hz])) hbody hloop
        · refine Or.inr ⟨evm2, σ2, frame2, mem2, out2, root2, max2, aw2, k2, C2,
            ?_, hs2, hf2, hm2, hfree2, hheap2, hroot2, rd2⟩
          exact ExecStmt.whileTrue
            ((evalHealthLoopCond hf.bitmap).trans (by rw [decide_eq_true hz])) hbody hloop

end Benchmarks.Midnight
