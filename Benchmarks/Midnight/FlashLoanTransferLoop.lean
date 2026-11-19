import Benchmarks.Midnight.FlashLoanTransferStep
import Benchmarks.Midnight.FlashLoanLoopCallSource

/-! Both flash-loan token loops, including any failing token call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightFlashLoanTransferLoop (isFrom : Bool) (remaining : Nat) {I : ExecutionEnv} {g : UInt256}
    {s0 evm : State} {frame : Frame} {mem rdata : ByteArray}
    {aw ptr index tn tp an ap dl dp : UInt256} {callback : AccountAddress} {data : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024) (hn : tn.toNat = index.toNat + remaining)
    (hlen : an.toNat = tn.toNat) (hcount : tn.toNat < 2 ^ 64)
    (htspan : tp.toNat + 32 * tn.toNat < UInt256.size)
    (haspan : ap.toNat + 32 * an.toNat < UInt256.size)
    (hc : CanonicalAddressWords (calldataArrayWords I.calldata tn.toNat tp.toNat))
    (hf : FlashLoanSourceFrame frame (calldataArrayWords I.calldata tn.toNat tp.toNat)
      (calldataArrayWords I.calldata an.toNat ap.toNat) callback data)
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat index.toNat)))
    (hh : TransferHeap mem aw ptr C) (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 (flashLoanTransferLoopPC isFrom)
      (flashLoanTransferLoopStack isFrom index tn tp (UInt256.ofNat callback.val) an ap dl dp ++ R)
      mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecForLoop config frame evm flashLoanLoopCondition flashLoanLoopPost (flashLoanLoopBody isFrom)
      .reverted ∧ RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (frame' : Frame) (evm' : State) (σ' : AccountMap) (mem' rdata' : ByteArray)
      (aw' ptr' : UInt256) (k' C' : Nat),
      ExecForLoop config frame evm flashLoanLoopCondition flashLoanLoopPost (flashLoanLoopBody isFrom)
        (.ok frame' evm') ∧
      SourceState s0 I σ' evm' ∧ TransferHeap mem' aw' ptr' C' ∧
      FlashLoanSourceFrame frame' (calldataArrayWords I.calldata tn.toNat tp.toNat)
        (calldataArrayWords I.calldata an.toNat ap.toNat) callback data ∧
      RD midnightBytecode I (Sat256.ofUInt256 g) s0 (flashLoanTransferExitPC isFrom)
        (flashLoanTransferLoopStack isFrom tn tn tp (UInt256.ofNat callback.val) an ap dl dp ++ R)
        mem' aw' rdata' σ' k' C' := by
  induction remaining generalizing index frame evm mem rdata aw ptr σ k C with
  | zero =>
    have he : index = tn := u256_inj (by omega)
    have hfalse : evalExpr? config frame evm flashLoanLoopCondition = .ok (.bool false) := by
      rw [flashLoanLoopCondition_eval hf hi, calldataArrayWords_length]
      rw [decide_eq_false (by omega)]
    rw [he] at rd
    obtain ⟨k1, C1, hC1, rd1⟩ := midnightFlashLoanTransferExit isFrom hstack rd
    exact Or.inr (Or.inr ⟨frame, evm, σ, mem, rdata, aw, ptr, _, _,
      .falseDone hfalse, hs, hh.mono hC1, hf, rd1⟩)
  | succ remaining ih =>
    have ht : index.toNat < tn.toNat := by omega
    have ha : index.toNat < an.toNat := by omega
    have hti : index.toNat < (calldataArrayWords I.calldata tn.toNat tp.toNat).length := by
      rw [calldataArrayWords_length]; exact ht
    have hai : index.toNat < (calldataArrayWords I.calldata an.toNat ap.toNat).length := by
      rw [calldataArrayWords_length]; exact ha
    have htoken := calldataArrayWords_index I.calldata ht hcount htspan
    have hasset := calldataArrayWords_index I.calldata ha (by omega) haspan
    have hcanon := calldataArrayWords_index_canonical ht hcount htspan hc
    have htrue : evalExpr? config frame evm flashLoanLoopCondition = .ok (.bool true) := by
      rw [flashLoanLoopCondition_eval hf hi, calldataArrayWords_length, decide_eq_true ht]
    have hadd : (index + (⟨1⟩ : UInt256)).toNat = index.toNat + 1 :=
      uadd_word_ofNat_toNat index 1 (by change _ < 2 ^ 256; omega)
    rcases midnightFlashLoanTransferStep isFrom frame.immutables hstack ht ha hcanon hh hgas hfork hs rd with
      hoog | ⟨hbody, hrev⟩ | hsuccess
    · exact Or.inl hoog
    · refine Or.inr (Or.inl ⟨.bodyRevert htrue (flashLoanLoopCallRevert isFrom hf hi hti hai ?_), hrev⟩)
      simpa only [Bool.false_eq_true, if_false, htoken, hasset, hs.env,
        flashLoanTokenAt, flashLoanAssetAt, accountAddress_ofUInt256_eq_ofNat_toNat] using hbody
    · obtain ⟨evm1, σ1, out, mem1, ptr1, aw1, k1, C1, hbody, hs1, _, _, hh1, rd1⟩ := hsuccess
      have hbody1 : ExecBlock config frame evm (flashLoanLoopBody isFrom)
          (.ok (flashLoanLoopCallFrame isFrom frame) evm1) := by
        apply flashLoanLoopCallReturn isFrom hf hi hti hai
        simpa only [Bool.false_eq_true, if_false, htoken, hasset, hs.env,
          flashLoanTokenAt, flashLoanAssetAt, accountAddress_ofUInt256_eq_ofNat_toNat] using hbody
      have hf1 := flashLoanLoopCallFrame_spec isFrom hf
      have hi1 := flashLoanLoopCallFrame_index isFrom hi
      have hpost := flashLoanLoopPost_exec (evm := evm1) hi1
        (by change _ < 2 ^ 256; omega)
      have hf2 := flashLoanSetIndex_spec hf1 (index.toNat + 1)
      have hi2 : (flashLoanSetIndex (flashLoanLoopCallFrame isFrom frame) (index.toNat + 1)).locals.get?
          "i" = some (.int (Int.ofNat (index + (⟨1⟩ : UInt256)).toNat)) := by
        rw [hadd]; exact flashLoanSetIndex_get _ _
      rcases ih (index := index + ⟨1⟩) (by rw [hadd]; omega) hf2 hi2 hh1 hs1 rd1 with
        hoog | ⟨hloop, hrev⟩ | hsuccess
      · exact Or.inl hoog
      · exact Or.inr (Or.inl ⟨.iterate htrue hbody1 hpost hloop, hrev⟩)
      · obtain ⟨frame', evm', σ', mem', rdata', aw', ptr', k', C', hloop, hs', hh', hf', rd'⟩ := hsuccess
        exact Or.inr (Or.inr ⟨frame', evm', σ', mem', rdata', aw', ptr', k', C',
          .iterate htrue hbody1 hpost hloop, hs', hh', hf', rd'⟩)

end Benchmarks.Midnight
