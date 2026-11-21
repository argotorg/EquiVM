import Benchmarks.Midnight.RepayCallbackPrepareBudget
import Benchmarks.Midnight.RepayCallbackMemory
import Benchmarks.Midnight.RepayCallbackReturn
import Benchmarks.Midnight.RepayCallbackSource
import Benchmarks.Midnight.TypedCallBudget

/-! Repayment's external callback, its acknowledgement, and the retained transfer budget. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightRepayCallback {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw root market arrayPtr limit id units user payer dp dl budgetRoot : UInt256}
    {callback : AccountAddress} {credit : Nat} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (m : MarketData) (hstack : R.length + 29 ≤ 1024)
    (hm : MarketStored mem market arrayPtr limit m)
    (hlimit : limit.toNat ≤ root.toNat) (hroot : root.toNat + 32 < 2^64)
    (hlower : 832 ≤ root.toNat) (hmem : 832 ≤ mem.size)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hu : user.toNat < EVM.addressModulus) (hdl : dl.toNat < 2^64)
    (hd : dp.toNat + dl.toNat ≤ I.calldata.size)
    (hf : RepaySourceFrame frame m id user units callback
      (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)))
    (hb : TransferBudget budgetRoot credit mem aw C) (hs : SourceState s0 I σ evm)
    (rd : RD midnightBytecode I g s0 ⟨10127⟩
      ([id, dp, UInt256.ofNat callback.val, dl, user, payer, units, market] ++ R)
      mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock config frame evm [repayCallbackStmt, .require repayMagicGuard] .reverted ∧
      RDrev midnightBytecode g s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecBlock config frame evm [repayCallbackStmt, .require repayMagicGuard]
        (.ok (repayCallbackFrame frame (calldataWord out 0)) evm') ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' root.toNat ∧
      memLoad (UInt256.ofNat 64) mem' = root + UInt256.ofNat 32 ∧
      root.toNat + 32 ≤ mem'.size ∧
      TransferBudget budgetRoot (credit + 4 + 128 * m.collaterals.length) mem' aw' C' ∧
      RD midnightBytecode I g s0 ⟨10259⟩ ([payer, units, market] ++ R)
        mem' aw' out σ' k' C' := by
  obtain ⟨gasArg, aw1, k1, C1, hb1, rd1⟩ := midnightRepayCallbackPrepare_budget m hstack hm
    hlimit (by omega) hlower hmem hz hfree hdl hd hb rd
  let input := repayCallbackMemory mem I.calldata root.toNat m id units user dp.toNat dl.toNat
  change TransferBudget budgetRoot (credit + 4 + 128 * m.collaterals.length) input aw1 C1 at hb1
  have hm1 := repayCallbackMemory_size_lower mem I.calldata root.toNat m id units user
    dp.toNat dl.toNat hd
  change root.toNat + 516 + 128 * m.collaterals.length + dl.toNat ≤ input.size at hm1
  have hn := hm.collateralCount
  have hlen : repayCallbackSize m dl.toNat < 2^72 := by
    unfold repayCallbackSize returnDataAllocation; omega
  have hsiz : (UInt256.ofNat (repayCallbackSize m dl.toNat)).toNat =
      repayCallbackSize m dl.toNat := UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hinmem : root.toNat + repayCallbackSize m dl.toNat ≤ input.size := by
    unfold repayCallbackSize returnDataAllocation; omega
  have houtmem : root.toNat + 32 ≤ input.size := by omega
  have hp : MemoryPrefix mem input root.toNat :=
    repayCallbackMemory_prefix _ _ _ _ _ _ _ _ _ _ le_rfl hd
  have hz1 : memLoad (UInt256.ofNat 800) input = ⟨0⟩ := by
    rw [hp.load (UInt256.ofNat 800) (by decide) hlower hmem, hz]
  have hcd : config.externalABI.encode? "onRepay"
      (repayCallbackArguments m id units (AccountAddress.ofNat user.toNat)
        (I.calldata.extract dp.toNat (dp.toNat + dl.toNat))) =
      some (input.readWithPadding root.toNat
        (UInt256.ofNat (repayCallbackSize m dl.toNat)).toNat) := by
    have hr := repayCallbackMemory_read mem I.calldata root.toNat m id units
      (AccountAddress.ofNat user.toNat) dp.toNat dl.toNat (by omega) hd hdl
      (by change _ < 2^256; omega)
    have huser : UInt256.ofNat (AccountAddress.ofNat user.toNat).val = user :=
      addressWord_eq_ofNat_address hu
    rw [huser] at hr
    rw [hsiz, hr]
    exact encodeRepayCallback _ _ _ _ _
  rcases typedZeroValueCallBudget rd1 hs (by native_decide) hcd
      (by
        rw [hsiz]
        have hmax : 2^72 ≤ maxReturnDataSizeByGas := by decide +kernel
        omega)
      (by change R.length + 5 ≤ 1024; omega) hb1
      (by rw [hsiz]; exact hinmem) (by exact houtmem) with
    hoog | ⟨evm', σ', success, out, aw2, k2, C2, hcall, hs', rd2, hout, hb2⟩
  · exact Or.inl hoog
  have hout' : out.size < UInt256.size := by change _ < 2^256; omega
  have hreply := wordReplyMemory_eq input out root hout'
  change out.write 0 input root.toNat (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat =
    wordReplyMemory input out root at hreply
  rw [hreply] at rd2 hb2
  simp only [accountAddress_roundtrip] at hcall
  rcases midnightRepayCallbackReturn success
      (by change R.length + 14 ≤ 1024; omega)
      hout' hroot hlower houtmem hz1 hb2 rd2 with
    ⟨hbad, hrev⟩ | ⟨htrue, h32, he, aw3, k3, C3, hb3, rd3⟩
  · refine Or.inr (Or.inl ⟨?_, hrev⟩)
    cases success with
    | false => exact .consRevert (repayCallbackFailure hf hcall)
    | true =>
      by_cases hshort : out.size < 32
      · exact .consRevert (repayCallbackShort hf hcall hshort)
      · have hne : calldataWord out 0 ≠ flashLoanMagic := by simpa [hshort] using hbad
        refine .consNormal (repayCallbackSuccess hf hcall (by omega))
          (.consRevert (.requireFalse ?_))
        rw [repayMagicGuard_eval, decide_eq_false hne]
  · subst success
    have hm2 : root.toNat + 32 ≤ (wordReplyMemory input out root).size := by
      rw [wordReplyMemory_size _ _ _ houtmem]; exact houtmem
    refine Or.inr (Or.inr ⟨evm', σ', out, _, aw3, k3, C3, ?_, hs',
      (hp.trans (wordReplyMemory_prefix _ _ _ _ houtmem le_rfl)).trans
        (callbackResultMemory_prefix _ _ _), callbackResultMemory_free _ _ (by omega),
      ?_, hb3, rd3⟩)
    · refine .consNormal (repayCallbackSuccess hf hcall h32)
        (.consNormal (.requireTrue ?_) .nil)
      rw [repayMagicGuard_eval, decide_eq_true he]
    · rw [callbackResultMemory_size _ _ (by omega)]; exact hm2

end Benchmarks.Midnight
