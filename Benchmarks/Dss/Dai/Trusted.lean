import Benchmarks.Dss.Dai.Common

/-!
# Trusted Dai selector facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`.  These facts are the
contract-local selector bytes used to connect Solm dispatch to the runtime dispatcher constants.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Dai

/-- `keccak("allowance(address,address)")[0:4] = 0xdd62ed3e`. -/
axiom daiAllowanceSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr allowanceTransition))).extract 0 4
      = daiSelBytes 0

/-- `keccak("approve(address,uint256)")[0:4] = 0x095ea7b3`. -/
axiom daiApproveSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr approveTransition))).extract 0 4
      = daiSelBytes 1

/-- `keccak("balanceOf(address)")[0:4] = 0x70a08231`. -/
axiom daiBalanceOfSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr balanceOfTransition))).extract 0 4
      = daiSelBytes 2

/-- `keccak("burn(address,uint256)")[0:4] = 0x9dc29fac`. -/
axiom daiBurnSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr burnTransition))).extract 0 4
      = daiSelBytes 3

/-- `keccak("decimals()")[0:4] = 0x313ce567`. -/
axiom daiDecimalsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr decimalsTransition))).extract 0 4
      = daiSelBytes 4

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom daiDenySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4
      = daiSelBytes 5

/-- `keccak("DOMAIN_SEPARATOR()")[0:4] = 0x3644e515`. -/
axiom daiDomainSeparatorSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr domainSeparatorTransition))).extract 0 4
      = daiSelBytes 6

/-- `keccak("mint(address,uint256)")[0:4] = 0x40c10f19`. -/
axiom daiMintSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr mintTransition))).extract 0 4
      = daiSelBytes 7

/-- `keccak("move(address,address,uint256)")[0:4] = 0xbb35783b`. -/
axiom daiMoveSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr moveTransition))).extract 0 4
      = daiSelBytes 8

/-- `keccak("name()")[0:4] = 0x06fdde03`. -/
axiom daiNameSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr nameTransition))).extract 0 4
      = daiSelBytes 9

/-- `keccak("nonces(address)")[0:4] = 0x7ecebe00`. -/
axiom daiNoncesSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr noncesTransition))).extract 0 4
      = daiSelBytes 10

/-- `keccak("permit(address,address,uint256,uint256,bool,uint8,bytes32,bytes32)")[0:4] =
    0x8fcbaf0c`. -/
axiom daiPermitSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr permitTransition))).extract 0 4
      = daiSelBytes 11

/-- `keccak("PERMIT_TYPEHASH()")[0:4] = 0x30adf81f`. -/
axiom daiPermitTypehashSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr permitTypehashTransition))).extract 0 4
      = daiSelBytes 12

/-- `keccak("pull(address,uint256)")[0:4] = 0xf2d5d56b`. -/
axiom daiPullSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr pullTransition))).extract 0 4
      = daiSelBytes 13

/-- `keccak("push(address,uint256)")[0:4] = 0xb753a98c`. -/
axiom daiPushSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr pushTransition))).extract 0 4
      = daiSelBytes 14

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom daiRelySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4
      = daiSelBytes 15

/-- `keccak("symbol()")[0:4] = 0x95d89b41`. -/
axiom daiSymbolSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr symbolTransition))).extract 0 4
      = daiSelBytes 16

/-- `keccak("totalSupply()")[0:4] = 0x18160ddd`. -/
axiom daiTotalSupplySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr totalSupplyTransition))).extract 0 4
      = daiSelBytes 17

/-- `keccak("transfer(address,uint256)")[0:4] = 0xa9059cbb`. -/
axiom daiTransferSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr transferTransition))).extract 0 4
      = daiSelBytes 18

/-- `keccak("transferFrom(address,address,uint256)")[0:4] = 0x23b872dd`. -/
axiom daiTransferFromSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr transferFromTransition))).extract 0 4
      = daiSelBytes 19

/-- `keccak("version()")[0:4] = 0x54fd4d50`. -/
axiom daiVersionSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr versionTransition))).extract 0 4
      = daiSelBytes 20

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom daiWardsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4
      = daiSelBytes 21

end Benchmarks.Dss.Dai
