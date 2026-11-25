import Benchmarks.Midnight.MarketHeapMemory

/-! Reading typed market fields and bounds from the decoded heap invariant. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem CollateralListStored.extent {mem : ByteArray} {ptr : UInt256} {limit : Nat}
    {cs : List CollateralData} (h : CollateralListStored mem ptr limit cs)
    (hstart : ptr.toNat ≤ limit) (hlimit : limit < UInt256.size) :
    ptr.toNat + 32 * cs.length ≤ limit := by
  induction cs generalizing ptr with
  | nil => simpa using hstart
  | cons c cs ih =>
    rcases h with ⟨p, hlo, hlim, hin, hp, hplo, hphi, hm, ht⟩
    have hn := uadd_word_ofNat_toNat ptr 32 (by omega)
    have hi := ih ht (by rw [hn]; omega)
    rw [hn] at hi
    simp only [List.length_cons]
    omega

theorem MarketStored.collateralCount {mem : ByteArray} {ptr arrayPtr root : UInt256}
    {m : MarketData} (h : MarketStored mem ptr arrayPtr root m) :
    m.collaterals.length < 2^64 := by
  have he := h.extent
  have hb := h.bound
  have hn := uadd_word_ofNat_toNat arrayPtr 32 (by change _ < 2^256; omega)
  have ht := h.collaterals.extent (by rw [hn]; exact he) (by change _ < 2^256; omega)
  omega

theorem MarketStored.chainId {mem : ByteArray} {ptr arrayPtr root : UInt256} {m : MarketData}
    (h : MarketStored mem ptr arrayPtr root m) : memLoad ptr mem = m.chainId :=
  h.words.load_word ⟨0, by simp [MarketData.words]⟩ (by simp)

theorem MarketStored.midnight {mem : ByteArray} {ptr arrayPtr root : UInt256} {m : MarketData}
    (h : MarketStored mem ptr arrayPtr root m) :
    memLoad (ptr + UInt256.ofNat 32) mem = UInt256.ofNat m.midnight.val :=
  h.words.load_offset ⟨1, by simp [MarketData.words]⟩ rfl

theorem MarketStored.arrayPtr {mem : ByteArray} {ptr arrayPtr root : UInt256} {m : MarketData}
    (h : MarketStored mem ptr arrayPtr root m) :
    memLoad (ptr + UInt256.ofNat 96) mem = arrayPtr :=
  h.words.load_offset ⟨3, by simp [MarketData.words]⟩ rfl

theorem MarketStored.loanToken {mem : ByteArray} {ptr arrayPtr root : UInt256} {m : MarketData}
    (h : MarketStored mem ptr arrayPtr root m) :
    memLoad (ptr + UInt256.ofNat 64) mem = UInt256.ofNat m.loanToken.val :=
  h.words.load_offset ⟨2, by simp [MarketData.words]⟩ rfl

theorem MarketStored.maturity {mem : ByteArray} {ptr arrayPtr root : UInt256} {m : MarketData}
    (h : MarketStored mem ptr arrayPtr root m) :
    memLoad (ptr + UInt256.ofNat 128) mem = m.maturity :=
  h.words.load_offset ⟨4, by simp [MarketData.words]⟩ rfl

theorem MarketStored.length {mem : ByteArray} {ptr arrayPtr root : UInt256} {m : MarketData}
    (h : MarketStored mem ptr arrayPtr root m) :
    memLoad arrayPtr mem = UInt256.ofNat m.collaterals.length :=
  h.header.load_word ⟨0, by simp⟩ (by simp)

theorem CollateralListStored.get {mem : ByteArray} {writePtr : UInt256} {limit : Nat}
    {cs : List CollateralData} (h : CollateralListStored mem writePtr limit cs)
    (i : Nat) (hi : i < cs.length) :
    ∃ ptr, memLoad (writePtr + UInt256.ofNat (32 * i)) mem = ptr ∧
      96 ≤ ptr.toNat ∧ ptr.toNat + 128 ≤ limit ∧ MemoryWords mem ptr.toNat cs[i].words := by
  induction cs generalizing writePtr i with
  | nil => simp at hi
  | cons c cs ih =>
    rcases h with ⟨ptr, hwlo, hwlim, hwin, hw, hplo, hplim, hm, ht⟩
    cases i with
    | zero => exact ⟨ptr, by simpa only [Nat.mul_zero, wordAddNat_zero] using hw, by omega,
        hplim, hm⟩
    | succ i =>
      obtain ⟨p, hp, hlo, hlim, hs⟩ := ih ht i (by simpa using hi)
      refine ⟨p, ?_, hlo, hlim, hs⟩
      simpa only [wordAddNat_add, show 32 + 32 * i = 32 * (i + 1) by omega] using hp

end Benchmarks.Midnight
