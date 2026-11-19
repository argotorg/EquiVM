import Benchmarks.Midnight.LiquidateCallbackMemory
import Benchmarks.Midnight.LiquidateCallbackReturn
import Benchmarks.Midnight.LiquidateCallbackSource
import Benchmarks.Midnight.TypedCallFunding

/-! Liquidation's callback and acknowledgement preserve the final-transfer heap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateCallback {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw root id index seized repaid borrower mode dp dl badDebt : UInt256}
    {receiver callback : AccountAddress} {m : MarketData} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 24 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback
      (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)))
    (hbad : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hi : calldataWord I.calldata 36 = index)
    (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hid : memLoad (UInt256.ofNat 768) mem = id)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hcallback : memLoad (UInt256.ofNat 736) mem = UInt256.ofNat callback.val)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized)
    (hpaid : memLoad (UInt256.ofNat 608) mem = repaid)
    (hdl : dl.toNat < 2^64) (hdata : dp.toNat + dl.toNat ≤ I.calldata.size)
    (hh : TransferHeap mem aw root C) (hgas : midnightGasBound g) (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨5824⟩
      ([dp, dl, borrower, badDebt, UInt256.ofNat receiver.val] ++ R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm [liquidateCallbackStmt, .require liquidateMagicGuard] .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecBlock config frame evm [liquidateCallbackStmt, .require liquidateMagicGuard]
        (.ok (liquidateCallbackFrame frame (calldataWord out 0)) evm') ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' root.toNat ∧
      root.toNat ≤ (root + UInt256.ofNat 32).toNat ∧
      TransferHeap mem' aw' (root + UInt256.ofNat 32) C' ∧
      RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨6265⟩ R mem' aw' out σ' k' C' := by
  rcases midnightMemoryPaid_headroom rd hh.funding.accounting.paid hgas hh.covered with
    hoog | hroom
  · exact Or.inl hoog
  have hroot : root.toNat + 32 < 2^64 := by omega
  obtain ⟨gasArg, aw1, k1, C1, ha1, rd1⟩ := midnightLiquidateCallbackPrepare hstack hd hi
    (by omega) hlo hsize hh.free hid hz hcallback hcanon hseized hpaid hdl hdata hh.funding rd
  let input := liquidateCallbackMemory mem I.calldata root.toNat I.source m id index seized repaid
    borrower (UInt256.ofNat receiver.val) dp.toNat dl.toNat badDebt
  change MemoryFunding (transferHeapCredit root + 4) input aw1 C1 at ha1
  have hm1 := liquidateCallbackMemory_size_lower mem I.calldata root.toNat I.source m id index
    seized repaid borrower (UInt256.ofNat receiver.val) badDebt dp.toNat dl.toNat hdata
  change root.toNat + 676 + 128 * m.collaterals.length + dl.toNat ≤ input.size at hm1
  have hn : m.collaterals.length < 2^64 := by
    obtain ⟨_, hcount, _, he, _⟩ := decodeCalldataMarket_collateralArray hd
    rw [he]; exact hcount
  have hlen : liquidateCallbackSize m dl.toNat < 2^72 := by
    unfold liquidateCallbackSize returnDataAllocation; omega
  have hsiz : (UInt256.ofNat (liquidateCallbackSize m dl.toNat)).toNat =
      liquidateCallbackSize m dl.toNat := UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hinmem : root.toNat + liquidateCallbackSize m dl.toNat ≤ input.size := by
    unfold liquidateCallbackSize returnDataAllocation; omega
  have houtmem : root.toNat + 32 ≤ input.size := by omega
  have hp : MemoryPrefix mem input root.toNat := liquidateCallbackMemory_prefix
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdata
  have hz1 : memLoad (UInt256.ofNat 800) input = ⟨0⟩ :=
    (hp.load (UInt256.ofNat 800) (by decide) hlo hsize).trans hz
  have hz0 : memLoad (UInt256.ofNat 96) input = ⟨0⟩ :=
    (hp.load (UInt256.ofNat 96) (by decide)
      (by change 128 ≤ root.toNat; omega) hh.size).trans hh.zero
  have hcd : config.externalABI.encode? "onLiquidate"
      (liquidateCallbackArguments I.source m id index seized repaid
        (AccountAddress.ofNat borrower.toNat) receiver
        (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)) badDebt) =
      some (input.readWithPadding root.toNat
        (UInt256.ofNat (liquidateCallbackSize m dl.toNat)).toNat) := by
    have hr := liquidateCallbackMemory_read mem I.calldata root.toNat I.source m id index
      seized repaid (AccountAddress.ofNat borrower.toNat) receiver badDebt dp.toNat dl.toNat
      (by omega) hdata hdl (by change _ < 2^256; omega)
    have hborrower : UInt256.ofNat (AccountAddress.ofNat borrower.toNat).val = borrower :=
      addressWord_eq_ofNat_address hcanon
    rw [hborrower] at hr
    rw [hsiz, hr]
    exact encodeLiquidateCallback _ _ _ _ _ _ _ _ _ _
  rcases typedZeroValueCallFunded rd1 hs (by native_decide) hcd
      (by
        rw [hsiz]
        have hmax : 2^72 ≤ maxReturnDataSizeByGas := by decide +kernel
        omega)
      (by change R.length + 2 ≤ 1024; omega) ha1
      (by rw [hsiz]; exact hinmem.trans ha1.covered)
      (by exact houtmem.trans ha1.covered) with
    hoog | ⟨evm', σ', success, out, k2, C2, hcall, hs', rd2, hout, ha2⟩
  · exact Or.inl hoog
  have hout' : out.size < UInt256.size := by change _ < 2^256; omega
  have hreply := wordReplyMemory_eq input out root hout'
  change out.write 0 input root.toNat (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat =
    wordReplyMemory input out root at hreply
  rw [hreply] at rd2 ha2
  simp only [accountAddress_roundtrip] at hcall
  have hsender : evm.executionEnv.source = I.source :=
    congrArg (fun env : ExecutionEnv ↦ env.source) hs.env
  rw [← hsender] at hcall
  rcases midnightLiquidateCallbackReturn (R := R) success
      (by omega) hout' hroot hlo houtmem hz0 hz1
      hh.aligned ha2 rd2 with
    ⟨hbadReply, hrev⟩ | ⟨htrue, h32, he, aw3, k3, C3, hh3, rd3⟩
  · refine Or.inr (Or.inl ⟨?_, hrev⟩)
    cases success with
    | false => exact .consRevert (liquidateCallbackFailure hf hbad hcall)
    | true =>
      by_cases hshort : out.size < 32
      · exact .consRevert (liquidateCallbackShort hf hbad hcall hshort)
      · have hne : calldataWord out 0 ≠ flashLoanMagic := by simpa [hshort] using hbadReply
        refine .consNormal (liquidateCallbackSuccess hf hbad hcall (by omega))
          (.consRevert (.requireFalse ?_))
        rw [liquidateMagicGuard_eval, decide_eq_false hne]
  · subst success
    refine Or.inr (Or.inr ⟨evm', σ', out, _, aw3, k3, C3, ?_, hs',
      (hp.trans (wordReplyMemory_prefix _ _ _ _ houtmem le_rfl)).trans
        (callbackResultMemory_prefix _ _ _), ?_, hh3, rd3⟩)
    · refine .consNormal (liquidateCallbackSuccess hf hbad hcall h32)
        (.consNormal (.requireTrue ?_) .nil)
      rw [liquidateMagicGuard_eval, decide_eq_true he]
    · rw [uadd_word_ofNat_toNat _ 32 (by change _ < 2^256; omega)]; omega

end Benchmarks.Midnight
