import Benchmarks.Safe.ExecTransactionCalldata

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def execTransactionDataStart (cd : ByteArray) : Nat :=
  4 + (calldataWord cd 68).toNat + 32

def execTransactionSignaturesStart (cd : ByteArray) : Nat :=
  4 + (calldataWord cd 292).toNat + 32

def execTransactionCalldataInput (cd : ByteArray) (dataLen sigLen : Nat) :
    ExecTransactionInput :=
  execTransactionInput cd
    (cd.extract (execTransactionDataStart cd) (execTransactionDataStart cd + dataLen))
    (cd.extract (execTransactionSignaturesStart cd)
      (execTransactionSignaturesStart cd + sigLen))

structure ExecTransactionCalldataBounds (cd : ByteArray) (dataLen sigLen : Nat) : Prop where
  head : 324 ≤ cd.size
  small : cd.size < 2 ^ 255
  target : (calldataWord cd 4).toNat < EVM.addressModulus
  dataOffset : (calldataWord cd 68).toNat ≤ 2 ^ 64 - 1
  dataWord : calldataWord cd (4 + (calldataWord cd 68).toNat) = UInt256.ofNat dataLen
  dataLength : dataLen ≤ 2 ^ 64 - 1
  dataEnd : execTransactionDataStart cd + dataLen ≤ cd.size
  operation : (calldataWord cd 100).toNat < 256
  gasToken : (calldataWord cd 228).toNat < EVM.addressModulus
  refundReceiver : (calldataWord cd 260).toNat < EVM.addressModulus
  sigOffset : (calldataWord cd 292).toNat ≤ 2 ^ 64 - 1
  sigWord : calldataWord cd (4 + (calldataWord cd 292).toNat) = UInt256.ofNat sigLen
  sigLength : sigLen ≤ 2 ^ 64 - 1
  sigEnd : execTransactionSignaturesStart cd + sigLen ≤ cd.size

theorem decodeExecTransactionValid {cd : ByteArray} {dataLen sigLen : Nat}
    (hb : ExecTransactionCalldataBounds cd dataLen sigLen) :
    decodeCalldata execTransactionNames execTransactionTypes cd =
      some (execTransactionCalldataInput cd dataLen sigLen).args := by
  rw [decodeExecTransactionCore hb.head hb.small, execTransactionCalldataTail,
    if_neg (not_not_intro hb.target),
    if_neg (show ¬solcMaxU64 < (calldataWord cd 68).toNat by
      change ¬2 ^ 64 - 1 < _; have := hb.dataOffset; omega),
    boundedCalldataBytesValid hb.dataWord hb.dataLength hb.dataEnd]
  dsimp only [bind, Option.bind]
  rw [if_neg (not_not_intro hb.operation), if_neg (not_not_intro hb.gasToken),
    if_neg (not_not_intro hb.refundReceiver),
    if_neg (show ¬solcMaxU64 < (calldataWord cd 292).toNat by
      change ¬2 ^ 64 - 1 < _; have := hb.sigOffset; omega),
    boundedCalldataBytesValid hb.sigWord hb.sigLength hb.sigEnd]
  rfl

set_option maxRecDepth 100000 in
theorem decodeExecTransactionEvidence {cd : ByteArray} {args : Store}
    (hlong : 4 ≤ cd.size)
    (hd : decodeCalldata execTransactionNames execTransactionTypes cd = some args) :
    ∃ dataLen sigLen, ExecTransactionCalldataBounds cd dataLen sigLen ∧
      args = (execTransactionCalldataInput cd dataLen sigLen).args := by
  have hg := decodeDynamicCalldata (cd := cd) (names := execTransactionNames) (ty := abiAddress)
    (types := [abiUInt256, .bytes, abiUInt8, abiUInt256, abiUInt256, abiUInt256,
      abiAddress, abiAddress, .bytes]) (headSize := 320) hlong (by decide +kernel)
    (by simp [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind])
  change decodeCalldata execTransactionNames execTransactionTypes cd = _ at hg
  have hs : cd.size < 2 ^ 255 := by
    by_contra hbad
    rw [hg, if_pos (by omega)] at hd
    cases hd
  have hh : 324 ≤ cd.size := by
    by_contra hbad
    rw [hg, if_neg (by omega), if_pos (by omega)] at hd
    cases hd
  rw [decodeExecTransactionCore hh hs] at hd
  unfold execTransactionCalldataTail at hd
  by_cases ht : (calldataWord cd 4).toNat < EVM.addressModulus
  swap
  · rw [if_pos ht] at hd; cases hd
  rw [if_neg (not_not_intro ht)] at hd
  by_cases hdo : solcMaxU64 < (calldataWord cd 68).toNat
  · rw [if_pos hdo] at hd; cases hd
  rw [if_neg hdo] at hd
  cases hp : boundedCalldataBytes cd (calldataWord cd 68).toNat with
  | none => rw [hp] at hd; cases hd
  | some payload =>
      rw [hp] at hd
      dsimp only [bind, Option.bind] at hd
      by_cases ho : (calldataWord cd 100).toNat < 256
      swap
      · rw [if_pos ho] at hd; cases hd
      rw [if_neg (not_not_intro ho)] at hd
      by_cases hk : (calldataWord cd 228).toNat < EVM.addressModulus
      swap
      · rw [if_pos hk] at hd; cases hd
      rw [if_neg (not_not_intro hk)] at hd
      by_cases hr : (calldataWord cd 260).toNat < EVM.addressModulus
      swap
      · rw [if_pos hr] at hd; cases hd
      rw [if_neg (not_not_intro hr)] at hd
      by_cases hso : solcMaxU64 < (calldataWord cd 292).toNat
      · rw [if_pos hso] at hd; cases hd
      rw [if_neg hso] at hd
      cases hsig : boundedCalldataBytes cd (calldataWord cd 292).toNat with
      | none => rw [hsig] at hd; cases hd
      | some signatures =>
          rw [hsig] at hd
          obtain ⟨dataLen, hdw, hdl, hde, rfl⟩ := boundedCalldataBytesEvidence hlong hp
          obtain ⟨sigLen, hsw, hsl, hse, rfl⟩ := boundedCalldataBytesEvidence hlong hsig
          exact ⟨dataLen, sigLen, ⟨hh, hs, ht, by change _ ≤ solcMaxU64; omega,
            hdw, hdl, hde, ho, hk, hr, by change _ ≤ solcMaxU64; omega,
            hsw, hsl, hse⟩, (Option.some.inj hd).symm⟩

end Benchmarks.Safe
