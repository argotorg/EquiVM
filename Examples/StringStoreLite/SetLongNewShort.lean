import Examples.StringStoreLite.SetLongNewShortOldShort

/-!
# StringStoreLite — valid set-branch, new short

This file proves the valid `set(string)` branch when the decoded new value is short.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000

namespace StringStoreLite

theorem stringStoreLiteSetNewShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hnonzero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) ≠ ⟨0⟩)
    (hnewShort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32) :
    runtimeEquivalenceFor stringStoreLiteConfig stringStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hflag :
    UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalid :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩
    · exact stringStoreLiteSetNewShortOldShortValidRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
        hlenMax hpayload hnonzero hnewShort hflag hvalid
    · exact stringStoreLiteSetShortNonemptyShortMalformedRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
        hlenMax hpayload hnewShort hnonzero hflag
        (by
          by_contra hne
          exact hvalid hne)
  · by_cases hbadLong :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) =
        ⟨0⟩
    · exact stringStoreLiteSetShortNonemptyLongMalformedRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
        hlenMax hpayload hnewShort hnonzero hflag hbadLong
    · exact stringStoreLiteSetShortNonemptyLongValidRuntime
        hcode hsize hperm hwv hsel hAccounts hsz36 hhi hoffMax hlenWord hsizeSign
        hlenMax hpayload hnewShort hnonzero hflag hbadLong


end StringStoreLite
