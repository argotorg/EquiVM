import Solm.DiffTest.Harness
import Benchmarks.Morpho.MetaMorphoV1_1.Spec
import Benchmarks.Morpho.MetaMorphoV1_1.Bytecode
import Benchmarks.Morpho.MetaMorphoV1_1.ImmutableCode
import Benchmarks.Morpho.MetaMorphoV1_1.Fixtures
import Benchmarks.Morpho.MorphoBlue.ImmutableCode

open Solm Solm.DiffTest

namespace Benchmarks.Morpho.MetaMorphoV1_1

/-- Historical deployment's immutable values, applied to the solc 0.8.37 runtime template. -/
def deployedImmutables : Store :=
  (∅ : Store)
    |>.insert "_asset" (.address (EVM.address 0x45804880de22913dafe09f4980848ece6ecbaf78))
    |>.insert "_underlyingDecimals" (.int 18)
    |>.insert "_cachedDomainSeparator" (.int 0x8f37e0b6d6c1781e97de5ecb3bae2dd56076e9111d4b253739015ae80df19392)
    |>.insert "_cachedChainId" (.int 1)
    |>.insert "_cachedThis" (.address (EVM.address 0xbeef7959ae71d4e45e1863dae0b94c35244af816))
    |>.insert "_hashedName" (.int 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470)
    |>.insert "_hashedVersion" (.int 0xc89efdaa54c0f20c7adf612882df0950f5a951637e0307cdcb4c672f298b8bc6)
    |>.insert "_name" (.int 0x0)
    |>.insert "_version" (.int 0x3100000000000000000000000000000000000000000000000000000000000001)
    |>.insert "MORPHO" (.address (EVM.address 0xbbbbbbbbbb9cc5e90e3b3af64bdaf62c37eeffcb))
    |>.insert "DECIMALS_OFFSET" (.int 0)

/-- Freshly compiled mainnet Blue runtime, including its deployed domain separator. -/
def blueRuntime : ByteArray :=
  MorphoBlue.immutableLayout.deployed MorphoBlue.morphoBytecode
    ((∅ : Store).insert "DOMAIN_SEPARATOR"
      (Solm.fixedBytesFromNat ⟨31, by decide⟩ 106934477169923273382738179085036086255493957540965079108323740421095391485229))

/-- IDs checked against mainnet CreateMarket logs; full parameters are pinned in provenance. -/
def marketWords : List Nat :=
  [0xecabc12c73a97c766d0c6aeb4c15c635630d78158b2ac8370455a09efcc50837,
   0xddac43c721a67ea9f19b1c57d2de12039c99f3f271c90123f7d8fc9edb591ee6,
   0x64844761c350e108d3196b7bbafb38b3dc661746207ef4e951fe7c5fe6ad4035]

def vaultCallees : List (EVM.Address × ByteArray) :=
  [(EVM.address 0xBBBBBbbBBb9cC5e90e3b3Af64bdAF62C37EEFFCb, blueRuntime),
   (EVM.address 0x45804880de22913dafe09f4980848ece6ecbaf78, trueERC20Code),
   (EVM.address 0x5001, noReturnERC20Code),
   (EVM.address 0x6000, fixedBlueCode)]

/-- Mainnet immutable valuation; constructors are also compared with the patch function. -/
def diffTarget : Target :=
  { name := "MetaMorphoV1_1", contract := contract, config := config,
    runtime := immutableLayout.deployed metaMorphoV1_1Bytecode deployedImmutables,
    immutables := deployedImmutables,
    initcode := some metaMorphoV1_1CreationBytecode,
    runtimeCodeOf := some (immutableLayout.deployed metaMorphoV1_1Bytecode),
    selfAddress := EVM.address 0xBeeF7959aE71D4e45e1863dae0B94C35244AF816,
    callees := vaultCallees,
    words := [10 ^ 18, 10 ^ 6, 10 ^ 24, 86400, 1209600, 10 ^ 15, 10 ^ 20] ++ marketWords }

end Benchmarks.Morpho.MetaMorphoV1_1
