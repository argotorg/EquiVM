import Benchmarks.Midnight.FlashLoanCallbackRead
import Benchmarks.Midnight.FlashLoanCallbackHeap
import Benchmarks.Midnight.FlashLoanCallbackSource
import Benchmarks.Midnight.TypedCallFunding

/-! The flash-loan callback, including ABI failures and the required acknowledgement. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightFlashLoanCallback {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray} {aw root tn tp an ap dl dp : UInt256}
    {callback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 32 ≤ 1024)
    (htn : tn.toNat < 2^64) (han : an.toNat < 2^64) (hdl : dl.toNat < 2^64)
    (htp : tp.toNat + 32 * tn.toNat < UInt256.size)
    (hap : ap.toNat + 32 * an.toNat ≤ I.calldata.size)
    (hdp : dp.toNat + dl.toNat ≤ I.calldata.size)
    (hc : CanonicalAddressWords (calldataArrayWords I.calldata tn.toNat tp.toNat))
    (hf : FlashLoanSourceFrame frame (calldataArrayWords I.calldata tn.toNat tp.toNat)
      (calldataArrayWords I.calldata an.toNat ap.toNat)
      callback (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)))
    (hh : TransferHeap mem aw root C) (hgas : midnightGasBound g)
    (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨16266⟩
      (flashLoanOutLoopStack tn tn tp (UInt256.ofNat callback.val) an ap dl dp ++ R)
      mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm [flashLoanCallbackStmt, .require flashLoanMagicGuard]
      .reverted ∧ RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (frame' : Frame) (evm' : State) (σ' : AccountMap) (mem' out : ByteArray)
      (aw' ptr' : UInt256) (k' C' : Nat),
      ExecBlock config frame evm [flashLoanCallbackStmt, .require flashLoanMagicGuard]
        (.ok frame' evm') ∧ SourceState s0 I σ' evm' ∧ TransferHeap mem' aw' ptr' C' ∧
      FlashLoanSourceFrame frame' (calldataArrayWords I.calldata tn.toNat tp.toNat)
        (calldataArrayWords I.calldata an.toNat ap.toNat)
        callback (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)) ∧
      RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨16403⟩
        (flashLoanInLoopStack ⟨0⟩ tn tp (UInt256.ofNat callback.val) an ap ++ R)
        mem' aw' out σ' k' C' := by
  rcases midnightMemoryPaid_headroom rd hh.funding.accounting.paid hgas hh.covered with
    hoog | hroot
  · exact Or.inl hoog
  obtain ⟨gasArg, aw1, k1, C1, _, ha1, rd1⟩ := midnightFlashLoanCallbackPrepare hstack
    htn han hdl htp hc (by omega) hh.free hh.funding rd
  let input := flashLoanCallbackMemory mem I.calldata I.source root.toNat tp.toNat tn.toNat
    ap.toNat an.toNat dp.toNat dl.toNat
  change MemoryFunding (transferHeapCredit root + 4) input aw1 C1 at ha1
  have hm := flashLoanCallbackMemory_size mem I.calldata I.source root.toNat tp.toNat tn.toNat
    ap.toNat an.toNat dp.toNat dl.toNat hap hdp
  change input.size = _ at hm
  have hlen : flashLoanCallbackSize tn.toNat an.toNat dl.toNat < 2^72 := by
    unfold flashLoanCallbackSize returnDataAllocation
    omega
  have hn : (UInt256.ofNat (flashLoanCallbackSize tn.toNat an.toNat dl.toNat)).toNat =
      flashLoanCallbackSize tn.toNat an.toNat dl.toNat :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hinmem : root.toNat + flashLoanCallbackSize tn.toNat an.toNat dl.toNat ≤ input.size := by
    rw [hm]
    unfold flashLoanCallbackSize returnDataAllocation
    omega
  have houtmem : root.toNat + 32 ≤ input.size := by rw [hm]; omega
  have hcover := ha1.covered
  change input.size ≤ 32 * aw1.toNat at hcover
  have hcd : config.externalABI.encode? "onFlashLoan"
      (flashLoanCallbackArguments I.source (calldataArrayWords I.calldata tn.toNat tp.toNat)
        (calldataArrayWords I.calldata an.toNat ap.toNat)
        (I.calldata.extract dp.toNat (dp.toNat + dl.toNat))) =
      some (input.readWithPadding root.toNat
        (UInt256.ofNat (flashLoanCallbackSize tn.toNat an.toNat dl.toNat)).toNat) := by
    rw [hn, show input = _ from rfl,
      flashLoanCallbackMemory_read _ _ _ _ _ _ _ _ _ _ hap hdp hdl
        (by change _ < 2^256; omega)]
    exact encodeFlashLoanCallback _ _ _ _ hc
  rcases typedZeroValueCallFunded (R := root :: ap :: UInt256.ofNat callback.val :: an :: tp :: tn :: R)
      rd1 hs (by native_decide) hcd
      (by
        rw [hn]
        have hb : 2^72 ≤ maxReturnDataSizeByGas := by decide +kernel
        omega)
      (by simp only [List.length_cons]; omega) ha1
      (by rw [hn]; omega) (by change root.toNat + 32 ≤ 32 * aw1.toNat; omega) with
    hoog | ⟨evm', σ', success, out, k2, C2, hcall, hs', rd2, hout, ha2⟩
  · exact Or.inl hoog
  have hout' : out.size < UInt256.size := by change _ < 2^256; omega
  have hreply := wordReplyMemory_eq input out root hout'
  change out.write 0 input root.toNat (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat =
    wordReplyMemory input out root at hreply
  rw [hreply] at rd2 ha2
  have hcall' : typedCallViaEVM config evm callback "onFlashLoan" 0
      (flashLoanCallbackArguments evm.executionEnv.source
        (calldataArrayWords I.calldata tn.toNat tp.toNat)
        (calldataArrayWords I.calldata an.toNat ap.toNat)
        (I.calldata.extract dp.toNat (dp.toNat + dl.toNat))) (success, evm', out) true := by
    simpa only [hs.env, accountAddress_roundtrip] using hcall
  have hzero : memLoad (UInt256.ofNat 96) input = ⟨0⟩ := by
    rw [show input = _ from rfl, flashLoanCallbackMemory_load_before _ _ _ _ _ _ _ _ _ _ _
      hap hdp (by change 96 + 32 ≤ mem.size; exact hh.size)
      (by change 96 + 32 ≤ root.toNat; exact hh.lower), hh.zero]
  rcases midnightFlashLoanCallbackReturn success (by simp only [List.length_cons]; omega)
      hout' (by omega) hh.lower houtmem hzero hh.aligned ha2 rd2 with
    ⟨hbad, hrev⟩ | ⟨htrue, h32, he, aw3, k3, C3, hh3, rd3⟩
  · refine Or.inr (Or.inl ⟨?_, hrev⟩)
    cases success with
    | false => exact .consRevert (flashLoanCallbackFailure hf hcall')
    | true =>
      by_cases hshort : out.size < 32
      · exact .consRevert (flashLoanCallbackShort hf hcall' hshort)
      · have hne : calldataWord out 0 ≠ flashLoanMagic := by simpa [hshort] using hbad
        refine .consNormal (flashLoanCallbackSuccess hf hcall' (by omega))
          (.consRevert (.requireFalse ?_))
        rw [flashLoanMagicGuard_eval, decide_eq_false hne]
  · subst success
    refine Or.inr (Or.inr ⟨flashLoanCallbackFrame frame (calldataWord out 0), evm', σ', _, out,
      aw3, root + UInt256.ofNat 32, k3, C3,
      ?_, hs', hh3, flashLoanCallbackFrame_spec hf (calldataWord out 0), rd3⟩)
    refine .consNormal (flashLoanCallbackSuccess hf hcall' h32)
      (.consNormal (.requireTrue ?_) .nil)
    rw [flashLoanMagicGuard_eval, decide_eq_true he]

end Benchmarks.Midnight
