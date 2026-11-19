import Benchmarks.Midnight.MarketDeploymentPrepare
import Benchmarks.Midnight.MarketCreateTrace
import Benchmarks.Midnight.MarketCreatedTrace
import Benchmarks.Midnight.MarketCreatedSource

/-! Complete the creation and event suffix of market initialization. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000 in
theorem midnightTouchMarketDeployment {I : ExecutionEnv} {evm : EVM.State} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw ptr arrayPtr limit root id ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {frame : Frame} (m : MarketData)
    (hstack : R.length + 24 ≤ 1024) (hm : MarketStored mem ptr arrayPtr limit m)
    (hlimit : limit.toNat ≤ root.toNat)
    (hb : root.toNat + 3 * m.encodingSize + 288 < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hc : frame.contract = contract)
    (hmarket : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨24347⟩
      (UInt256.ofNat 21556 :: ptr :: id :: ret :: R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev midnightBytecode g s0 ∧
      ExecBlock config frame evm (touchMarketInitBody.drop 18) .reverted) ∨
    ∃ (evm' : State) (σ' : AccountMap) (addr : AccountAddress)
      (out mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      SourceState s0 I σ' evm' ∧
      ExecBlock config frame evm (touchMarketInitBody.drop 18)
        (.ok (marketCreatedFrame frame addr) evm') ∧
      MemoryPrefix mem mem' limit.toNat ∧
      memLoad (UInt256.ofNat 64) mem' = marketDeploymentFree root m ∧
      RD midnightBytecode I g s0 ret (id :: R) mem' aw' out σ' k' C' := by
  obtain ⟨hp, hf, hi, aw1, k1, C1, rd1⟩ := midnightMarketDeploymentPrepare m
    (by simp only [List.length_cons]; omega) hm hlimit (by omega) hfree rd
  rcases midnightMarketCreate m (frame := touchMarketCallFrame frame.immutables m)
    (by simp only [List.length_cons]; omega) hs hperm (store_get_self _ _ _) hi rd1 with
    hoog | ⟨rev, hrev⟩ | ⟨evm', σ', addr, out, aw2, k2, C2, _, hs', hsrc, rd2⟩
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨rev, marketStoreCallRevert hc hmarket hrev⟩)
  · let free := marketDeploymentFree root m
    have hfn : free.toNat = root.toNat + 2 * m.encodingSize + 160 :=
      (marketIdPointers m (by omega)).2.2
    obtain ⟨aw3, k3, C3, rd3⟩ := midnightMarketCreated m (by omega) (hm.preserve hp)
      (by rw [hfn]; omega) (by rw [hfn]; change _ < 2^256; omega) hf hperm hret rd2
    have hroot : 96 ≤ root.toNat := by
      have := hm.lower; have := hm.array; have := hm.extent; omega
    have hsize : 96 ≤ (marketDeploymentMemory mem root m).size := by
      have hwords := hm.words.size
      have hlo := hm.lower
      have hsz := hp.size
      change ptr.toNat + 32 * 8 ≤ mem.size at hwords
      omega
    refine Or.inr (Or.inr ⟨evm', σ', addr, out, _, aw3, k3, C3, hs',
      marketCreatedSource hc hmarket hid (hs'.env ▸ hperm) hsrc,
      hp.trans ((marketCreatedMemory_prefix _ free m).mono (by rw [hfn]; omega)), ?_, rd3⟩)
    rw [marketCreatedMemory_free _ free m (by rw [hfn]; omega) hsize]
    exact hf

end Benchmarks.Midnight
