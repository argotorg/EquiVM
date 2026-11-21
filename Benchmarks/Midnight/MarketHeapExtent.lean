import Benchmarks.Midnight.MarketHeapMemory

/-! A stored market remains valid when its enclosing heap extent grows. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem CollateralListStored.mono_limit {mem : ByteArray} {ptr : UInt256}
    {limit larger : Nat} {cs : List CollateralData}
    (h : CollateralListStored mem ptr limit cs) (hle : limit ≤ larger) :
    CollateralListStored mem ptr larger cs := by
  induction cs generalizing ptr with
  | nil => trivial
  | cons c cs ih =>
    obtain ⟨p, hlo, he, hin, hr, hptr, hp, hw, ht⟩ := h
    exact ⟨p, hlo, he.trans hle, hin, hr, hptr, hp.trans hle, hw, ih ht⟩

theorem MarketStored.mono_root {mem : ByteArray} {ptr arrayPtr root larger : UInt256}
    {m : MarketData} (h : MarketStored mem ptr arrayPtr root m)
    (hle : root.toNat ≤ larger.toNat) (hbound : larger.toNat < 2^64) :
    MarketStored mem ptr arrayPtr larger m :=
  ⟨h.words, h.header, h.collaterals.mono_limit hle,
    h.lower, h.array, h.extent.trans hle, hbound⟩

end Benchmarks.Midnight
