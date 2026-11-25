import Benchmarks.Midnight.MarketDeploymentPrepareFunding
import Benchmarks.Midnight.MarketCreateFunding
import Benchmarks.Midnight.MarketCreatedFunding
import Benchmarks.Midnight.MarketCreatedSource

variable {fork : Ethereum.Fork}

/-! Complete the creation and event suffix of market initialization. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem marketCreatedMemory_space (mem : ByteArray) (root : UInt256) (m : MarketData) :
    root.toNat ≤ (marketCreatedMemory mem root m).size := by
  have hs := (marketEncodeMemory_prefix
    (writeWord mem root.toNat (UInt256.ofNat 32)) (root.toNat + 32) root.toNat m
    (by omega)).size
  rw [writeWord_sparse_size] at hs
  change root.toNat ≤ (marketEncodeMemory
    (writeWord mem root.toNat (UInt256.ofNat 32)) (root.toNat + 32) m).size
  omega

set_option maxRecDepth 2000000 in
-- GENERALIZES midnightTouchMarketDeployment with retained funding and heap extent.
theorem midnightTouchMarketDeployment_funded {credit : Nat} {I : ExecutionEnv} {evm : EVM.State} {g : Sat256}
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
    (hfund : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨24347⟩
      (UInt256.ofNat 21556 :: ptr :: id :: ret :: R) mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev fork midnightBytecode g s0 ∧
      ExecBlock fork config frame evm (touchMarketInitBody.drop 18) .reverted) ∨
    ∃ (evm' : State) (σ' : AccountMap) (addr : AccountAddress)
      (out mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      SourceState s0 I σ' evm' ∧
      ExecBlock fork config frame evm (touchMarketInitBody.drop 18)
        (.ok (marketCreatedFrame frame addr) evm') ∧
      MemoryPrefix mem mem' limit.toNat ∧
      memLoad (UInt256.ofNat 64) mem' = marketDeploymentFree root m ∧
      (marketDeploymentFree root m).toNat ≤ mem'.size ∧
      MemoryFunding credit mem' aw' C' ∧
      RD fork midnightBytecode I g s0 ret (id :: R) mem' aw' out σ' k' C' := by
  obtain ⟨hp, hf, hi, aw1, k1, C1, hfund1, rd1⟩ := midnightMarketDeploymentPrepare_funded m
    (by simp only [List.length_cons]; omega) hm hlimit (by omega) hfree hfund rd
  rcases midnightMarketCreate_funded m (frame := touchMarketCallFrame frame.immutables m)
    (by simp only [List.length_cons]; omega) hs hperm (store_get_self _ _ _) hi hfund1 rd1 with
    hoog | ⟨rev, hrev⟩ | ⟨evm', σ', addr, out, aw2, k2, C2, _, hs', hsrc, hfund2, rd2⟩
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨rev, marketStoreCallRevert hc hmarket hrev⟩)
  · let free := marketDeploymentFree root m
    have hfn : free.toNat = root.toNat + 2 * m.encodingSize + 160 :=
      (marketIdPointers m (by omega)).2.2
    obtain ⟨aw3, k3, C3, hfund3, rd3⟩ := midnightMarketCreated_funded m (by omega) (hm.preserve hp)
      (by rw [hfn]; omega) (by rw [hfn]; change _ < 2^256; omega) hf hperm hret hfund2 rd2
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
      hp.trans ((marketCreatedMemory_prefix _ free m).mono (by rw [hfn]; omega)), ?_, marketCreatedMemory_space _ free m, hfund3, rd3⟩)
    rw [marketCreatedMemory_free _ free m (by rw [hfn]; omega) hsize]
    exact hf

end Benchmarks.Midnight
