import Benchmarks.Midnight.FlashLoanCallback
import Benchmarks.Midnight.FlashLoanTransferLoop

variable {fork : Ethereum.Fork}

/-! The complete flash-loan transfer, callback, and repayment sequence. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightFlashLoanTail {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray} {aw root tn tp an ap dl dp : UInt256}
    {callback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 32 ≤ 1024) (hlen : an.toNat = tn.toNat)
    (htn : tn.toNat < 2^64) (hdl : dl.toNat < 2^64)
    (htp : tp.toNat + 32 * tn.toNat < UInt256.size)
    (hap : ap.toNat + 32 * an.toNat ≤ I.calldata.size)
    (hdp : dp.toNat + dl.toNat ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hc : CanonicalAddressWords (calldataArrayWords I.calldata tn.toNat tp.toNat))
    (hf : FlashLoanSourceFrame frame (calldataArrayWords I.calldata tn.toNat tp.toNat)
      (calldataArrayWords I.calldata an.toNat ap.toNat)
      callback (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)))
    (hh : TransferHeap mem aw root C) (hgas : midnightGasBound g) (hfork : fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨16258⟩
      (flashLoanOutLoopStack ⟨0⟩ tn tp (UInt256.ofNat callback.val) an ap dl dp ++ R)
      mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (flashLoanTransition.body.drop 5) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (frame' : Frame) (evm' : State) (σ' : AccountMap),
      ExecBlock fork config frame evm (flashLoanTransition.body.drop 5) (.ok frame' evm') ∧
      SourceState s0 I σ' evm' ∧ RDret fork midnightBytecode (Sat256.ofUInt256 g) s0 σ' ByteArray.empty := by
  have houtshape : flashLoanTransition.body.drop 5 =
      flashLoanTransition.body[5]! :: flashLoanTransition.body.drop 6 := by decide +kernel
  have hinshape : flashLoanTransition.body.drop 8 = [flashLoanTransition.body[8]!] :=
    by decide +kernel
  rcases midnightFlashLoanTransferLoop false tn.toNat (index := ⟨0⟩) (R := R) (by omega)
      (by change tn.toNat = 0 + tn.toNat; omega) hlen htn htp (by omega) hc
      (flashLoanSetIndex_spec hf 0) (flashLoanSetIndex_get frame 0) hh hgas hfork hs rd with
    hoog | ⟨hloop, hrev⟩ | hsuccess
  · exact Or.inl hoog
  · refine Or.inr (Or.inl ⟨?_, hrev⟩)
    rw [houtshape]
    exact .consRevert (flashLoanLoopStatement false hloop)
  obtain ⟨frame1, evm1, σ1, mem1, rdata1, aw1, ptr1, k1, C1, hloop1, hs1, hh1, hf1, rd1⟩ := hsuccess
  have hprefix {result : ExecResult}
      (htail : ExecBlock fork config frame1 evm1 (flashLoanTransition.body.drop 6) result) :
      ExecBlock fork config frame evm (flashLoanTransition.body.drop 5) result := by
    rw [houtshape]
    exact .consNormal (flashLoanLoopStatement false hloop1) htail
  rcases midnightFlashLoanCallback hstack htn (by omega) hdl htp hap hdp hc hf1 hh1 hgas hs1 rd1 with
    hoog | ⟨hcall, hrev⟩ | hsuccess
  · exact Or.inl hoog
  · refine Or.inr (Or.inl ⟨hprefix ?_, hrev⟩)
    rw [flashLoanCallback_shape]
    exact execBlock_reverted_append hcall
  obtain ⟨frame2, evm2, σ2, mem2, out2, aw2, ptr2, k2, C2, hcall, hs2, hh2, hf2, rd2⟩ := hsuccess
  have prefix2 {result : ExecResult}
      (htail : ExecBlock fork config frame2 evm2 (flashLoanTransition.body.drop 8) result) :
      ExecBlock fork config frame evm (flashLoanTransition.body.drop 5) result := by
    apply hprefix
    rw [flashLoanCallback_shape]
    exact execBlock_append hcall htail
  rcases midnightFlashLoanTransferLoop true tn.toNat (index := ⟨0⟩) (R := R)
      (dl := dl) (dp := dp) (by omega)
      (by change tn.toNat = 0 + tn.toNat; omega) hlen htn htp (by omega) hc
      (flashLoanSetIndex_spec hf2 0) (flashLoanSetIndex_get frame2 0) hh2 hgas hfork hs2 rd2 with
    hoog | ⟨hloop, hrev⟩ | hsuccess
  · exact Or.inl hoog
  · refine Or.inr (Or.inl ⟨prefix2 ?_, hrev⟩)
    rw [hinshape]
    exact .consRevert (flashLoanLoopStatement true hloop)
  obtain ⟨frame3, evm3, σ3, mem3, out3, aw3, ptr3, k3, C3, hloop3, hs3, _, _, rd3⟩ := hsuccess
  refine Or.inr (Or.inr ⟨frame3, evm3, σ3, prefix2 ?_, hs3,
    midnightBlocks.midnight_block_16411 ?_ rd3⟩)
  · rw [hinshape]
    exact .consNormal (flashLoanLoopStatement true hloop3) .nil
  · change R.length + 1 + 1 + 1 + 1 + 1 + 1 + 0 ≤ 1024
    omega

end Benchmarks.Midnight
