import Benchmarks.Dss.GemJoin.Common

/-!
# Trusted selector facts for MakerDAO/Sky DSS GemJoin

These are the ABI selector facts accepted by the benchmark prompt.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Dss.GemJoin

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
axiom gemJoinCageSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr cageTransition))).extract 0 4 =
      gemJoinSelBytes 0

/-- `keccak("dec()")[0:4] = 0xb3bcfa82`. -/
axiom gemJoinDecSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr decTransition))).extract 0 4 =
      gemJoinSelBytes 1

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom gemJoinDenySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr denyTransition))).extract 0 4 =
      gemJoinSelBytes 2

/-- `keccak("exit(address,uint256)")[0:4] = 0xef693bed`. -/
axiom gemJoinExitSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr exitTransition))).extract 0 4 =
      gemJoinSelBytes 3

/-- `keccak("gem()")[0:4] = 0x7bd2bea7`. -/
axiom gemJoinGemSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr gemTransition))).extract 0 4 =
      gemJoinSelBytes 4

/-- `keccak("ilk()")[0:4] = 0xc5ce281e`. -/
axiom gemJoinIlkSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr ilkTransition))).extract 0 4 =
      gemJoinSelBytes 5

/-- `keccak("join(address,uint256)")[0:4] = 0x3b4da69f`. -/
axiom gemJoinJoinSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr joinTransition))).extract 0 4 =
      gemJoinSelBytes 6

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
axiom gemJoinLiveSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr liveTransition))).extract 0 4 =
      gemJoinSelBytes 7

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom gemJoinRelySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr relyTransition))).extract 0 4 =
      gemJoinSelBytes 8

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
axiom gemJoinVatSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr vatTransition))).extract 0 4 =
      gemJoinSelBytes 9

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom gemJoinWardsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr wardsTransition))).extract 0 4 =
      gemJoinSelBytes 10

end Benchmarks.Dss.GemJoin
