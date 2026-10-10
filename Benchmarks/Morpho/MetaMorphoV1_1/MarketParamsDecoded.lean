import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsEncode
import Benchmarks.Morpho.MetaMorphoV1_1.WordWindow

/-! Connect a decoded parameter struct to its canonical five-word memory representation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem decodedAddressWord {w : UInt256} (hc : w.toNat < EVM.addressModulus) :
    UInt256.ofNat (AccountAddress.ofNat w.toNat).toNat = w :=
  addressWord_eq_ofNat_address hc

theorem marketParamsData_words {out : ByteArray} (hc : MarketParamsChecks out) :
    (marketParamsData out).words =
      [calldataWord out 0, calldataWord out 32, calldataWord out 64,
       calldataWord out 96, calldataWord out 128] := by
  simp only [MarketParamsData.words, marketParamsData, decodedAddressWord hc.2.1,
    decodedAddressWord hc.2.2.1, decodedAddressWord hc.2.2.2.1,
    decodedAddressWord hc.2.2.2.2]

theorem marketParamsData_bytes {out : ByteArray} (hc : MarketParamsChecks out) :
    (marketParamsData out).bytes = out.readWithPadding 0 160 := by
  let words := [calldataWord out 0, calldataWord out 32, calldataWord out 64,
    calldataWord out 96, calldataWord out 128]
  have hw (i : Fin words.length) : words[i] = calldataWord out (32 * i.val) := by
    fin_cases i <;> rfl
  have hread := readWithPadding_words out 0 words (by exact hc.1) (by
    intro i
    have hi : i.val < 5 := i.isLt
    have hin : 32 * i.val + 32 ≤ out.size := by have := hc.1; omega
    rw [hw i, Nat.zero_add, calldataWord_bytes_at hin]
    exact readWithPadding_eq_extract _ _ hin)
  rw [MarketParamsData.bytes, marketParamsData_words hc]
  exact hread.symm

theorem marketParamsLoads_of_fields {mem out : ByteArray} {src : UInt256}
    (hc : MarketParamsChecks out)
    (hfields : ∀ i, i < 5 → memLoad (src + UInt256.ofNat (32 * i)) mem =
      calldataWord out (32 * i)) :
    MarketParamsLoads mem src (marketParamsData out) := by
  have h0 := hfields 0 (by decide)
  simp only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    u256_add_zero] at h0
  simp only [MarketParamsLoads, marketParamsData, decodedAddressWord hc.2.1,
    decodedAddressWord hc.2.2.1, decodedAddressWord hc.2.2.2.1,
    decodedAddressWord hc.2.2.2.2]
  exact ⟨h0, hfields 1 (by decide), hfields 2 (by decide),
    hfields 3 (by decide), hfields 4 (by decide)⟩

theorem marketParamsBytes_of_fields {mem out : ByteArray} {src : UInt256}
    (hc : MarketParamsChecks out) (hmem : src.toNat + 160 ≤ mem.size)
    (hfit : src.toNat + 160 < UInt256.size)
    (hfields : ∀ i, i < 5 → memLoad (src + UInt256.ofNat (32 * i)) mem =
      calldataWord out (32 * i)) :
    mem.readWithPadding src.toNat 160 = (marketParamsData out).bytes := by
  rw [marketParamsData_bytes hc]
  exact wordWindowRead_of_fields (count := 5) hc.1 hmem hfit hfields

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
