import Examples.BytesStoreLite.CoreSetLongNewShort
import Examples.BytesStoreLite.CoreSetLongNewLong

/-!
# BytesStoreLiteCore — valid long set-branch router

This file dispatches the valid `set(bytes)` branch to the new-short and new-long proofs.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000

namespace BytesStoreLiteCore

theorem bytesStoreLiteCoreSetValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteCoreBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩)
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
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteCoreConfig bytesStoreLiteCoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hnewShort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32
  · exact bytesStoreLiteCoreSetNewShortRuntime hcode hsize hperm hwv hsel hAccounts hsz36 hhi
      hoffMax hlenWord hsizeSign hlenMax hpayload hnonzero hnewShort
  · exact bytesStoreLiteCoreSetNewLongRuntime hcode hsize hperm hwv hsel hAccounts hsz36 hhi
      hoffMax hlenWord hsizeSign hlenMax hpayload hnonzero hnewShort


end BytesStoreLiteCore
