import Benchmarks.Safe.SetupCalldata

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def setupOwnersStart (cd : ByteArray) : Nat := 4 + (calldataWord cd 4).toNat + 32

def setupDataStart (cd : ByteArray) : Nat := 4 + (calldataWord cd 100).toNat + 32

def setupCalldataInput (cd : ByteArray) (n len : Nat) : SetupInput :=
  setupInput cd (calldataWords cd (setupOwnersStart cd) n)
    (cd.extract (setupDataStart cd) (setupDataStart cd + len))

structure SetupCalldataBounds (cd : ByteArray) (n len : Nat) : Prop where
  head : 260 ≤ cd.size
  small : cd.size < 2 ^ 255
  ownersOffset : (calldataWord cd 4).toNat ≤ 2 ^ 64 - 1
  ownersWord : calldataWord cd (4 + (calldataWord cd 4).toNat) = UInt256.ofNat n
  ownersLength : n ≤ 2 ^ 64 - 1
  ownersEnd : setupOwnersStart cd + 32 * n ≤ cd.size
  target : (calldataWord cd 68).toNat < EVM.addressModulus
  dataOffset : (calldataWord cd 100).toNat ≤ 2 ^ 64 - 1
  dataWord : calldataWord cd (4 + (calldataWord cd 100).toNat) = UInt256.ofNat len
  dataLength : len ≤ 2 ^ 64 - 1
  dataEnd : setupDataStart cd + len ≤ cd.size
  fallbackHandler : (calldataWord cd 132).toNat < EVM.addressModulus
  paymentToken : (calldataWord cd 164).toNat < EVM.addressModulus
  paymentReceiver : (calldataWord cd 228).toNat < EVM.addressModulus

theorem decodeSetupBounded {cd : ByteArray} {n len : Nat} (hb : SetupCalldataBounds cd n len) :
    decodeCalldata setupNames setupTypes cd =
      if ∀ w ∈ calldataWords cd (setupOwnersStart cd) n, w.toNat < EVM.addressModulus then
        some (setupCalldataInput cd n len).args else none := by
  rw [decodeSetupCore hb.head hb.small, setupCalldataTail,
    if_neg (show ¬solcMaxU64 < (calldataWord cd 4).toNat by
      change ¬2 ^ 64 - 1 < _; have := hb.ownersOffset; omega),
    boundedCalldataWordsValid hb.ownersWord hb.ownersLength hb.ownersEnd]
  dsimp only [bind, Option.bind]
  change (if ¬∀ w ∈ calldataWords cd (setupOwnersStart cd) n,
    w.toNat < EVM.addressModulus then none else _) = _
  by_cases hc : ∀ w ∈ calldataWords cd (setupOwnersStart cd) n,
      w.toNat < EVM.addressModulus
  · rw [if_neg (not_not_intro hc), if_neg (not_not_intro hb.target),
      if_neg (show ¬solcMaxU64 < (calldataWord cd 100).toNat by
        change ¬2 ^ 64 - 1 < _; have := hb.dataOffset; omega),
      boundedCalldataBytesValid hb.dataWord hb.dataLength hb.dataEnd]
    dsimp only [bind, Option.bind]
    rw [if_neg (not_not_intro hb.fallbackHandler), if_neg (not_not_intro hb.paymentToken),
      if_neg (not_not_intro hb.paymentReceiver), if_pos hc]
    rfl
  · rw [if_pos hc, if_neg hc]

set_option maxRecDepth 100000 in
theorem decodeSetupEvidence {cd : ByteArray} {args : Store} (hlong : 4 ≤ cd.size)
    (hd : decodeCalldata setupNames setupTypes cd = some args) :
    ∃ n len, SetupCalldataBounds cd n len ∧
      (∀ w ∈ calldataWords cd (setupOwnersStart cd) n, w.toNat < EVM.addressModulus) ∧
      args = (setupCalldataInput cd n len).args := by
  have hg := decodeDynamicCalldata (cd := cd) (names := setupNames)
    (ty := .dynamicArray abiAddress)
    (types := [abiUInt256, abiAddress, .bytes, abiAddress, abiAddress, abiUInt256, abiAddress])
    (headSize := 256) hlong (by decide +kernel)
    (by simp [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind])
  change decodeCalldata setupNames setupTypes cd = _ at hg
  have hs : cd.size < 2 ^ 255 := by
    by_contra hbad
    rw [hg, if_pos (by omega)] at hd
    cases hd
  have hh : 260 ≤ cd.size := by
    by_contra hbad
    rw [hg, if_neg (by omega), if_pos (by omega)] at hd
    cases hd
  rw [decodeSetupCore hh hs] at hd
  unfold setupCalldataTail at hd
  by_cases ho : solcMaxU64 < (calldataWord cd 4).toNat
  · rw [if_pos ho] at hd; cases hd
  rw [if_neg ho] at hd
  cases hw : boundedCalldataWords cd (calldataWord cd 4).toNat with
  | none => rw [hw] at hd; cases hd
  | some owners =>
      rw [hw] at hd
      dsimp only [bind, Option.bind] at hd
      by_cases hc : ∀ w ∈ owners, w.toNat < EVM.addressModulus
      swap
      · rw [if_pos hc] at hd; cases hd
      rw [if_neg (not_not_intro hc)] at hd
      by_cases ht : (calldataWord cd 68).toNat < EVM.addressModulus
      swap
      · rw [if_pos ht] at hd; cases hd
      rw [if_neg (not_not_intro ht)] at hd
      by_cases hdo : solcMaxU64 < (calldataWord cd 100).toNat
      · rw [if_pos hdo] at hd; cases hd
      rw [if_neg hdo] at hd
      cases hp : boundedCalldataBytes cd (calldataWord cd 100).toNat with
      | none => rw [hp] at hd; cases hd
      | some payload =>
          rw [hp] at hd
          dsimp only [bind, Option.bind] at hd
          by_cases hf : (calldataWord cd 132).toNat < EVM.addressModulus
          swap
          · rw [if_pos hf] at hd; cases hd
          rw [if_neg (not_not_intro hf)] at hd
          by_cases hk : (calldataWord cd 164).toNat < EVM.addressModulus
          swap
          · rw [if_pos hk] at hd; cases hd
          rw [if_neg (not_not_intro hk)] at hd
          by_cases hr : (calldataWord cd 228).toNat < EVM.addressModulus
          swap
          · rw [if_pos hr] at hd; cases hd
          rw [if_neg (not_not_intro hr)] at hd
          obtain ⟨n, hnw, hn, hni, rfl⟩ := boundedCalldataWordsEvidence hw
          obtain ⟨len, hlw, hl, hli, rfl⟩ := boundedCalldataBytesEvidence hlong hp
          refine ⟨n, len, ⟨hh, hs, ?_, hnw, hn, hni, ht, ?_, hlw, hl, hli, hf, hk, hr⟩,
            hc, (Option.some.inj hd).symm⟩
          · change _ ≤ solcMaxU64; omega
          · change _ ≤ solcMaxU64; omega

end Benchmarks.Safe
