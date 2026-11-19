import Benchmarks.Midnight.MulticallStep
import Benchmarks.Midnight.MulticallSource

/-! The valid-calldata multicall loop, with successful and reverting delegate calls. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMulticallLoop (remaining : Nat) {I : ExecutionEnv} {g : UInt256}
    {s0 evm : State} {frame : Frame} {mem rdata : ByteArray}
    {aw root base index count : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hr : count.toNat = index.toNat + remaining)
    (hn : count.toNat < 2^64) (hsz : I.calldata.size < 2^255)
    (hspan : base.toNat + 32 * count.toNat ≤ I.calldata.size)
    (hv : MulticallTailsValid I.calldata base 0 count.toNat)
    (hf : frame.locals.get? "calls" = some
      (.array ((multicallBytesList I.calldata base 0 count.toNat).map Value.bytes)))
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat index.toNat)))
    (hm : 832 ≤ mem.size) (hl : 832 ≤ root.toNat)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hh : TransferHeap mem aw root C) (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨3605⟩
      (index :: base :: multicallTailBound I.calldata base :: count :: R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecForLoop config frame evm multicallLoopCondition flashLoanLoopPost multicallLoopBody
      .reverted ∧ RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (frame' : Frame) (evm' : State) (σ' : AccountMap),
      ExecForLoop config frame evm multicallLoopCondition flashLoanLoopPost multicallLoopBody
        (.ok frame' evm') ∧ SourceState s0 I σ' evm' ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 σ' ByteArray.empty := by
  induction remaining generalizing evm frame mem rdata aw root index σ k C with
  | zero =>
    have hfalse : evalExpr? config frame evm multicallLoopCondition = .ok (.bool false) := by
      rw [multicallLoopCondition_eval hf hi, multicallBytesList_length,
        decide_eq_false (by omega)]
    have hc : UInt256.isZero (UInt256.lt index count) ≠ ⟨0⟩ := by
      rw [ult_zero (by omega)]
      decide
    have rd1 := midnightBlocks.midnight_block_3605_taken (by omega) hc (by jump_dest) rd
    have hret := midnightBlocks.midnight_block_3723 (by simp only [List.length_cons]; omega) rd1
    rw [hz] at hret
    exact Or.inr (Or.inr ⟨frame, evm, σ, .falseDone hfalse, hs, by
      simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero]
        using hret⟩)
  | succ remaining ih =>
    have ht : index.toNat < count.toNat := by omega
    have hlen : index.toNat < (multicallBytesList I.calldata base 0 count.toNat).length := by
      rw [multicallBytesList_length]
      exact ht
    have hget := multicallBytesList_get I.calldata base 0 count.toNat index.toNat ht
    simp only [Nat.zero_add] at hget
    have htrue : evalExpr? config frame evm multicallLoopCondition = .ok (.bool true) := by
      rw [multicallLoopCondition_eval hf hi, multicallBytesList_length, decide_eq_true ht]
    have hadd : (index + (⟨1⟩ : UInt256)).toNat = index.toNat + 1 :=
      uadd_word_ofNat_toNat index 1 (by change index.toNat + 1 < 2^256; omega)
    rcases midnightMulticallStep hstack ht hn hsz hspan hm hl hz hh hgas hfork hs rd with
      hoog | ⟨hbad, _⟩ | ⟨evm1, success, out, hcall, hbad, hrev⟩ | hsuccess
    · exact Or.inl hoog
    · exact False.elim (hbad (by simpa only [Nat.zero_add] using hv index.toNat ht))
    · refine Or.inr (Or.inl ⟨.bodyRevert htrue
        (multicallSourceRevert (evm' := evm1) hf hi hlen ?_ hbad), hrev⟩)
      simpa only [hs.env, hget] using hcall
    · obtain ⟨evm1, σ1, out, mem1, root1, aw1, k1, C1, _, hcall, hout,
        hs1, hp, hroot, hh1, rd1⟩ := hsuccess
      have hbody : ExecBlock config frame evm multicallLoopBody
          (.ok (multicallCallFrame frame evm true out) evm1) := by
        apply multicallSourceReturn hf hi hlen ?_ hout
        simpa only [hs.env, hget] using hcall
      have hf1 : (multicallCallFrame frame evm true out).locals.get? "calls" =
          some (.array ((multicallBytesList I.calldata base 0 count.toNat).map Value.bytes)) :=
        (multicallCallFrame_get "calls" (by decide)).trans hf
      have hi1 : (multicallCallFrame frame evm true out).locals.get? "i" =
          some (.int (Int.ofNat index.toNat)) :=
        (multicallCallFrame_get "i" (by decide)).trans hi
      have hpost := flashLoanLoopPost_exec (evm := evm1) hi1
        (by change _ < 2^256; omega)
      have hf2 : (flashLoanSetIndex (multicallCallFrame frame evm true out)
          (index.toNat + 1)).locals.get? "calls" =
          some (.array ((multicallBytesList I.calldata base 0 count.toNat).map Value.bytes)) := by
        exact (store_get_ne _ _ (by decide)).trans hf1
      have hi2 : (flashLoanSetIndex (multicallCallFrame frame evm true out)
          (index.toNat + 1)).locals.get? "i" =
          some (.int (Int.ofNat (index + (⟨1⟩ : UInt256)).toNat)) := by
        rw [hadd]
        exact flashLoanSetIndex_get _ _
      have hz1 : memLoad (UInt256.ofNat 800) mem1 = ⟨0⟩ := by
        rw [hp.load (UInt256.ofNat 800) (by decide) hl hm, hz]
      rcases ih (by rw [hadd]; omega) hf2 hi2 (hm.trans hp.size) (hl.trans hroot) hz1 hh1 hs1 rd1 with
        hoog | ⟨hloop, hrev⟩ | ⟨frame', evm', σ', hloop, hs', hret⟩
      · exact Or.inl hoog
      · exact Or.inr (Or.inl ⟨.iterate htrue hbody hpost hloop, hrev⟩)
      · exact Or.inr (Or.inr ⟨frame', evm', σ', .iterate htrue hbody hpost hloop, hs', hret⟩)

end Benchmarks.Midnight
