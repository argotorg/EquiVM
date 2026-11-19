import Benchmarks.Midnight.RepayEventBudget
import Benchmarks.Midnight.RepayCallback
import Benchmarks.Midnight.RepayTransfer

/-! Repayment's event, optional callback, and final token transfer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightRepayTail {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray} {σ : AccountMap}
    {aw root market arrayPtr limit id units user dp dl saved : UInt256}
    {callback payer : AccountAddress} {credit k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I σ evm)
    (hf : RepaySourceFrame frame m id user units callback
      (I.calldata.extract dp.toNat (dp.toNat + dl.toNat)))
    (hpayer : frame.locals.get? "payer" = some (.address payer)) (hperm : I.perm = true)
    (hstack : R.length + 30 ≤ 1024) (hmem : 832 ≤ mem.size)
    (hm : MarketStored mem market arrayPtr limit m) (hlimit : limit.toNat ≤ root.toNat)
    (hroot : root.toNat + 32 < 2^64) (hlower : 832 ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hzero800 : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hu : user.toNat < EVM.addressModulus) (hdl : dl.toNat < 2^64)
    (hd : dp.toNat + dl.toNat ≤ I.calldata.size)
    (hb : TransferBudget (root + UInt256.ofNat 32) credit mem aw C)
    (hcredit : 4 * (((root + UInt256.ofNat 32).toNat + safeTransferCallAllocation true + 31) / 32)
      ≤ credit + 999921) (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨10034⟩
      ([repayHasCallback callback, id, dp, UInt256.ofNat callback.val, dl, user,
        UInt256.ofNat payer.val, units, market, saved] ++ R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock config frame evm (repayTransition.body.drop 10) .reverted) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (repayTransition.body.drop 10) (.ok frame' evm') ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap ByteArray.empty := by
  have hn32 : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  obtain ⟨aw1, k1, C1, hb1, rd1⟩ := midnightRepayEvent_budget (R := saved :: R)
    (by simp only [List.length_cons]; omega) hperm (by omega) hfree hb rd
  let mem1 := repayEventMemory mem root units payer
  have hp1 : MemoryPrefix mem mem1 root.toNat := memoryPrefix_writeWordArray _ _ _ _ le_rfl
  have hm1 := hm.preserve (hp1.mono hlimit)
  have hmem1 : 832 ≤ mem1.size := hmem.trans hp1.size
  have hused1 : root.toNat ≤ mem1.size := by
    dsimp only [mem1, repayEventMemory]
    simp only [writeWordArray, writeWord_sparse_size]
    omega
  have hfree1 : memLoad (UInt256.ofNat 64) mem1 = root := by
    dsimp only [mem1, repayEventMemory]
    rw [
      memLoad_writeWordArray_preserved _ _ _ _ (by change 96 ≤ mem.size; omega)
        (Or.inl (by change 96 ≤ root.toNat; omega)), hfree]
  have hz1 : memLoad (UInt256.ofNat 96) mem1 = ⟨0⟩ := by
    rw [hp1.load (UInt256.ofNat 96) (by decide) (by change 128 ≤ root.toNat; omega)
      (by change 128 ≤ mem.size; omega), hzero]
  have hz8001 : memLoad (UInt256.ofNat 800) mem1 = ⟨0⟩ := by
    rw [hp1.load (UInt256.ofNat 800) (by decide) hlower hmem, hzero800]
  have hmarket : (market + UInt256.ofNat 64).toNat = market.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by
      have := hm.array; have := hm.extent; have := hm.bound
      change _ < 2^256; omega)
  have hloan1 : memLoad (market + UInt256.ofNat 64) mem1 = UInt256.ofNat m.loanToken.val :=
    hm1.words.load_word ⟨2, by simp [MarketData.words]⟩ (by simpa using hmarket)
  have emitPrefix {result : ExecResult}
      (ht : ExecBlock config frame evm (repayTransition.body.drop 11) result) :
      ExecBlock config frame evm (repayTransition.body.drop 10) result :=
    (repayEmitSource hf hpayer (by rw [hs.env]; exact hperm)).run ht
  by_cases hcb : callback = 0
  · have sourcePrefix {result : ExecResult}
        (ht : ExecBlock config frame evm (repayTransition.body.drop 12) result) :
        ExecBlock config frame evm (repayTransition.body.drop 10) result := by
      apply emitPrefix
      rw [repayCallback_shape]
      exact .consNormal (.iteFalse (by rw [repayCallbackCondition_eval hf.callback]; simp [hcb])
        .nil) ht
    have hbsmall : TransferBudget root credit mem1 aw1 C1 := by
      rcases hb1 with hsmall | ⟨halign, hfund⟩
      · exact Or.inl (by rw [hn32] at hsmall; omega)
      · exact Or.inr ⟨by rw [hn32] at halign; omega, hfund⟩
    simp only [repayAfterEventPC, hcb, if_true] at rd1
    rcases midnightRepayTransfer (R := saved :: R) hs hf hpayer (by
        simp only [List.length_cons]; omega) hmem1 hlower hloan1 hfree1 hz1 hz8001 hbsmall hused1
        (by rw [hn32] at hcredit; omega) hgas hfork rd1 with
      hoog | ⟨hr, ht⟩ | ⟨frame', evm', ht, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨hr, sourcePrefix ht⟩)
    · exact Or.inr (Or.inr ⟨frame', evm', sourcePrefix ht, hr⟩)
  · simp only [repayAfterEventPC, hcb, if_false] at rd1
    have hcond : evalExpr? config frame evm repayCallbackCondition = .ok (.bool true) := by
      rw [repayCallbackCondition_eval hf.callback, decide_eq_true hcb]
    rcases midnightRepayCallback (R := saved :: R) m
        (by simp only [List.length_cons]; omega) hm1 hlimit hroot hlower hmem1 hz8001 hfree1
        hu hdl hd hf hb1 hs rd1 with
      hoog | ⟨ht, hr⟩ | ⟨evm2, σ2, out, mem2, aw2, k2, C2, ht, hs2, hp2, hfree2, hused2, hb2, rd2⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨hr, emitPrefix (by
        rw [repayCallback_shape]; exact .consRevert (.iteTrue hcond ht))⟩)
    · have sourcePrefix {result : ExecResult}
          (htail : ExecBlock config (repayCallbackFrame frame (calldataWord out 0)) evm2
            (repayTransition.body.drop 12) result) :
          ExecBlock config frame evm (repayTransition.body.drop 10) result := by
        apply emitPrefix
        rw [repayCallback_shape]
        exact .consNormal (.iteTrue hcond ht) htail
      have rd3 := midnightBlocks.midnight_block_10259 (by omega) (by jump_dest) rd2
      have hb3 := transferBudgetAt (root := root + UInt256.ofNat 32)
        (credit := credit + 4 + 128 * m.collaterals.length) rd3 (by transfer_budget hb2)
      have hm2 := hm1.preserve (hp2.mono hlimit)
      have hloan2 : memLoad (market + UInt256.ofNat 64) mem2 = UInt256.ofNat m.loanToken.val :=
        hm2.words.load_word ⟨2, by simp [MarketData.words]⟩ (by simpa using hmarket)
      have hz2 : memLoad (UInt256.ofNat 96) mem2 = ⟨0⟩ := by
        rw [hp2.load (UInt256.ofNat 96) (by decide) (by change 128 ≤ root.toNat; omega)
          (by change 128 ≤ mem1.size; omega), hz1]
      have hz8002 : memLoad (UInt256.ofNat 800) mem2 = ⟨0⟩ := by
        rw [hp2.load (UInt256.ofNat 800) (by decide) hlower hmem1, hz8001]
      have hpay2 : (repayCallbackFrame frame (calldataWord out 0)).locals.get? "payer" =
          some (.address payer) := by
        simpa only [repayCallbackFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, show ("__c3" == "payer") = false from rfl,
          if_false] using hpayer
      rcases midnightRepayTransfer (R := saved :: R) hs2 (repayCallbackFrame_spec hf _) hpay2
          (by simp only [List.length_cons]; omega) (hmem1.trans hp2.size)
          (by rw [hn32]; omega) hloan2 hfree2 hz2 hz8002 hb3 (by rw [hn32]; exact hused2)
          (by omega) hgas hfork rd3 with
        hoog | ⟨hr, htail⟩ | ⟨frame', evm', htail, hr⟩
      · exact Or.inl hoog
      · exact Or.inr (Or.inl ⟨hr, sourcePrefix htail⟩)
      · exact Or.inr (Or.inr ⟨frame', evm', sourcePrefix htail, hr⟩)

end Benchmarks.Midnight
