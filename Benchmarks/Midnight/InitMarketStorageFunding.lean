import Benchmarks.Midnight.InitMarketPhasesFunding

variable {fork : Ethereum.Fork}

/-! Complete initialization with memory funding retained. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES midnightInitMarketStores with retained funding.
set_option maxRecDepth 2000000 in
theorem midnightInitMarketStores_funded {credit : Nat} {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr limit root id ret previous count : UInt256}
    {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 18 ≤ 1024) (hm : MarketStored mem ptr arrayPtr limit m)
    (hlimit : limit.toNat ≤ root.toNat) (hb : root.toNat + 224 < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root) (hperm : evm.executionEnv.perm = true)
    (hfund : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode evm.executionEnv g s0 ⟨21130⟩
      (arrayPtr :: previous :: ret :: ptr :: (ptr + UInt256.ofNat 96) :: id :: count :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C',
      MemoryFunding credit (initMarketStoreMemory mem root evm id m.loanToken) aw' C' ∧ RD fork midnightBytecode evm.executionEnv g s0 ⟨24347⟩
      (UInt256.ofNat 21556 :: ptr :: id :: ret :: R)
      (initMarketStoreMemory mem root evm id m.loanToken) aw' rdata
      (initMarketStorageState evm id m.loanToken).accountMap k' C' := by
  let d := initMarketDefaultWord evm id m.loanToken
  let mm := initMarketFeeMemory (initMarketScratch mem id m.loanToken) root d
  let s := initSettlementState (initMarketTick evm id) id d 7
  have hroot : 96 ≤ root.toNat := by
    have := hm.lower; have := hm.array; have := hm.extent; omega
  have hw : MemoryWords mm root.toNat (initMarketSettlementFeeWords d) :=
    initMarketFeeMemory_words _ root d hroot (by change _ < 2^256; omega)
  have hmp : MemoryPrefix mem mm limit.toNat :=
    (initMarketScratch_prefix mem id m.loanToken limit.toNat).trans
      (initMarketFeeMemory_prefix _ root d limit.toNat hlimit)
  have hm2 := hm.preserve hmp
  obtain ⟨aw1, k1, C1, hfund1, rd1⟩ := midnightInitMarketTick_funded m (by omega) hm hfree hperm hfund rd
  obtain ⟨aw2, k2, C2, hfund2, rd2⟩ := midnightInitMarketFeeCopy_funded
    (by simp only [List.length_cons]; omega) hb hfund1 rd1
  change RD fork _ _ _ _ _ _ mm _ _ _ _ _ at rd2
  change MemoryFunding credit mm aw2 C2 at hfund2
  obtain ⟨aw3, k3, C3, hfund3, rd3⟩ := midnightInitMarketFirstFees_funded
    (by simp only [List.length_cons]; omega) hperm hw hfund2 rd2
  obtain ⟨aw4, k4, C4, hfund4, rd4⟩ := midnightInitMarketLastFees_funded m.loanToken
    (by simp only [List.length_cons]; omega) hperm hw hm2.loanToken hfund3 rd3
  have hsenv : s.executionEnv = evm.executionEnv := by
    simp only [s, initSettlementState_env, initMarketTick_env]
  have hsaccounts : s.accountMap =
      initSettlementAccounts (initMarketTick evm id).accountMap evm.executionEnv id d 7 := by
    simp only [s, initSettlementState_accounts, initMarketTick_env]
  rw [← hsaccounts, ← hsenv] at rd4
  obtain ⟨aw5, k5, C5, hfund5, rd5⟩ := midnightInitMarketContinuous_funded (evm := s) m.loanToken
    (by simp only [List.length_cons]; omega) (by
      have hsz := hw.size
      change root.toNat + 32 * 7 ≤ mm.size at hsz
      omega) (by rw [hsenv]; exact hperm) hfund4 rd4
  exact ⟨aw5, k5, C5, hfund5, by simpa only [hsenv] using rd5⟩


end Benchmarks.Midnight
