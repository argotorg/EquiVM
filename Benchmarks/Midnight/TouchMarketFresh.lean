import Benchmarks.Midnight.TouchMarketInitialization
import Benchmarks.Midnight.TouchMarketDeployment

/-! The entire previously-uninitialized market branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem initMarketStorageState_world (evm : EVM.State) (id : UInt256) (token : AccountAddress) :
    (initMarketStorageState evm id token).σ₀ = evm.σ₀ := by
  have hfees (s : EVM.State) (word : UInt256) (n : Nat) :
      (initSettlementState s id word n).σ₀ = s.σ₀ := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [initSettlementState, storeSettlementFee, storageStore_σ₀, ih]
  simp only [initMarketStorageState, initMarketContinuous, storageStore_σ₀, hfees,
    initMarketTick]

set_option maxRecDepth 2000000 in
theorem midnightTouchMarketFresh {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr limit root id ret : UInt256}
    {k C : Nat} {R : List UInt256} {frame : Frame} (m : MarketData)
    (hstack : R.length + 24 ≤ 1024) (hm : MarketStored mem ptr arrayPtr limit m)
    (hlimit : limit.toNat ≤ root.toNat)
    (hb : root.toNat + 3 * m.encodingSize + 512 < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root) (hw : evm.σ₀ = s0.σ₀)
    (hc : frame.contract = contract)
    (hmarket : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hl : frame.locals.get? "isLltvEnabled" = none)
    (hcu : frame.locals.get? "isLiquidationCursorEnabled" = none)
    (hd : frame.locals.get? "defaultSettlementFeeCbp" = none)
    (hcont : frame.locals.get? "defaultContinuousFee" = none)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode evm.executionEnv g s0 ⟨20764⟩
      ((ptr + UInt256.ofNat 32) :: ptr :: id :: ret :: R) mem aw rdata evm.accountMap k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev midnightBytecode g s0 ∧ ExecBlock config frame evm touchMarketInitBody .reverted) ∨
    (RDstatic midnightBytecode g s0 ∧
      ExecBlock config frame evm touchMarketInitBody .staticViolation) ∨
    ∃ frame' evm' σ' out mem' aw' k' C',
      frame'.locals.get? "id" = some (wordBytes32Value id) ∧
      SourceState s0 evm.executionEnv σ' evm' ∧
      ExecBlock config frame evm touchMarketInitBody (.ok frame' evm') ∧
      MemoryPrefix mem mem' limit.toNat ∧
      memLoad (UInt256.ofNat 64) mem' =
        marketDeploymentFree (root + UInt256.ofNat 224) m ∧
      RD midnightBytecode evm.executionEnv g s0 ret (id :: R) mem' aw' out σ' k' C' := by
  rcases midnightTouchMarketInitialization m (by omega) hm hlimit (by omega) hfree
    hc hmarket hbase hid hl hcu hd hcont rd with
    hrev | hstatic | ⟨f, mm, aw1, k1, C1, hperm, hfc, hfm, hfi, hsource, hp, hf, rd1⟩
  · exact Or.inr (Or.inl hrev)
  · exact Or.inr (Or.inr (Or.inl hstatic))
  · let evm1 := initMarketStorageState evm id m.loanToken
    have hs : SourceState s0 evm.executionEnv evm1.accountMap evm1 :=
      ⟨(initMarketStorageState_world _ _ _).trans hw, initMarketStorageState_env _ _ _, rfl⟩
    have hr : (root + UInt256.ofNat 224).toNat = root.toNat + 224 :=
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
    rcases midnightTouchMarketDeployment m hstack (hm.preserve hp)
      (by rw [hr]; omega) (by rw [hr]; omega) hf hs hperm hfc hfm hfi hret rd1 with
      hoog | ⟨rev, src⟩ | ⟨evm', σ', addr, out, mm', aw2, k2, C2, hs', src, hp', hf', rd2⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨rev, hsource _ src⟩)
    · refine Or.inr (Or.inr (Or.inr ⟨_, evm', σ', out, mm', aw2, k2, C2,
        ?_, hs', hsource _ src, hp.trans hp', hf', rd2⟩))
      simp only [marketCreatedFrame, resumeAfterInternalCall,
        store_get_ne _ _ (show ("__c2" == "id") = false from rfl), hfi]

end Benchmarks.Midnight
