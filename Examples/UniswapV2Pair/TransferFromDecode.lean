import Examples.UniswapV2Pair.ExternalWrappers
import Examples.UniswapV2Pair.Dispatch
import Examples.UniswapV2Pair.TransferFromSuccess

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! # `transferFrom` decode-failure refinement slices -/

theorem uniswapTransferFromX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapAddressAddressUint256ExternalShort
    (entry := ⟨879⟩) (ret := ⟨797⟩) (routine := ⟨2938⟩)
    hreach uniswap_address_address_uint256_external_entry_wf hsz4 hsize hshort

/-- Short-calldata decode-failure refinement slice for
`transferFrom(address,address,uint256)`.

The dispatcher-level `calldatasize < 4` branch remains in `Correct.lean`; this theorem starts from
the matched `transferFrom` body entry with selector calldata present but fewer than three ABI words.
-/
theorem uniswapTransferFromBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨879⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_transferFrom_none_short (I := I) hsz4 hshort
  exact (uniswapTransferFromX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- Short-calldata decode-failure `transferFrom(address,address,uint256)` refinement slice,
packaged from selector dispatch through the body core. -/
theorem uniswapTransferFromBodyDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ rfl hsel
  exact uniswapTransferFromBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hdispatch
    (uniswapReachTransferFromBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapTransferFromBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus
      · by_cases hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus
        · by_cases hmax : (transferFromCurrentAllowanceWord
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat =
              UInt256.size - 1
          · by_cases hbalance : (transferFromValueWord I).toNat ≤
              (transferFromFromBalanceWord
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat
            · by_cases hfit : transferFromNewToNatMax
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I <
                  UInt256.size
              · exact uniswapTransferFromBodyOk_maxAllowance hcode hsize hperm hwv hsel
                  hsz100 hbig hcanonFrom hcanonTo hmax hbalance hfit hdispatch hAccounts
              · sorry
            · sorry
          · by_cases hallowance : (transferFromValueWord I).toNat ≤
              (transferFromCurrentAllowanceWord
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).toNat
            · by_cases hbalance : (transferFromValueWord I).toNat ≤
                (transferFromFromBalanceWord (transferFromAfterAllowanceState
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I) I).toNat
              · by_cases hfit : transferFromNewToNat
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I <
                    UInt256.size
                · exact uniswapTransferFromBodyOk_finiteAllowance hcode hsize hperm hwv
                    hsel hsz100 hbig hcanonFrom hcanonTo hmax hallowance hbalance hfit
                    hdispatch hAccounts
                · sorry
              · sorry
            · sorry
        · sorry
      · sorry
    · sorry
  · exact uniswapTransferFromBodyDecodeFailed_short hcode hsize hwv hsel (by omega)
      hdispatch

end UniswapV2Pair
