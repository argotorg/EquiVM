import Benchmarks.Midnight.MarketEncodeMemory
import Benchmarks.Midnight.CollateralEncodeAccounting

variable {fork : Ethereum.Fork}

/-! Complete market encoding with explicit payment for its memory. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMarketEncoder_accounted {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr output ret : UInt256}
    {σ : AccountMap} {limit k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 16 ≤ 1024)
    (hm : MemoryWords mem ptr.toNat (m.words arrayPtr))
    (hn : memLoad arrayPtr mem = UInt256.ofNat m.collaterals.length)
    (hnin : arrayPtr.toNat + 32 ≤ mem.size)
    (hc : CollateralListStored mem (arrayPtr + UInt256.ofNat 32) limit m.collaterals)
    (hbelow : ptr.toNat + 256 ≤ limit) (harray : arrayPtr.toNat + 32 ≤ limit)
    (hlimit : limit ≤ output.toNat)
    (hout : output.toNat + 288 + 128 * m.collaterals.length < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨19181⟩ (ptr :: output :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryAccounting (marketEncodeMemory mem output.toNat m) aw' C' ∧
      RD fork midnightBytecode I g s0 ret
      ((output + UInt256.ofNat (288 + 128 * m.collaterals.length)) :: R)
      (marketEncodeMemory mem output.toNat m) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightMarketEncodeStart_accounted m
    (by simp only [List.length_cons]; omega) hm hn hnin (by omega) (by omega) (by omega) ha rd
  have ho : (output + UInt256.ofNat 288).toNat = output.toNat + 288 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hcount : (UInt256.ofNat m.collaterals.length).toNat =
      (UInt256.ofNat 0).toNat + m.collaterals.length := by
    rw [UInt256.toNat_ofNat_of_lt (by omega)]
    change _ = 0 + m.collaterals.length
    omega
  have hc' := hc.preserve (marketEncodeHeadMemory_prefix mem output.toNat limit m hlimit)
  obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightCollateralEncodeLoop_accounted m.collaterals
    (by simp only [List.length_cons]; omega) hc' hcount (by rw [ho]; omega)
    (by rw [ho]; exact hout) ha1 rd1
  have hm' := marketEncodeHeadMemory_preserve m hm (by
    change ptr.toNat + 32 * 8 ≤ output.toNat
    omega)
  have hm'' := hm'.writeWords (m.collaterals.flatMap CollateralData.words)
    (off := (output + UInt256.ofNat 288).toNat) (Or.inl (by
      change ptr.toNat + 32 * 8 ≤ (output + UInt256.ofNat 288).toNat
      rw [ho]; omega))
  obtain ⟨aw3, k3, C3, ha3, rd3⟩ := midnightMarketEncodeEnd_accounted m (by omega) hm''
    (by omega) (by omega) hret ha2 rd2
  exact ⟨aw3, k3, C3, by simpa only [wordAddNat_add, ho, marketEncodeMemory] using And.intro ha3 rd3⟩

end Benchmarks.Midnight
