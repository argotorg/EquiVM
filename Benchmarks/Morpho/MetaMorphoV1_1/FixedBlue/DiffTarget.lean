import Benchmarks.Morpho.MetaMorphoV1_1.DiffTarget

open Solm Solm.DiffTest

namespace Benchmarks.Morpho.MetaMorphoV1_1.FixedBlue

/-- Same vault bytecode, with MORPHO pointing to a fixed-response Blue interface fixture.
Both entries retain the contract name, so --only MetaMorphoV1_1 selects both valuations.
The generated registry lists this fixture after the mainnet valuation. -/
def diffTarget : Target :=
  let imms := deployedImmutables.insert "MORPHO" (.address (EVM.address 0x6000))
  { MetaMorphoV1_1.diffTarget with
    runtime := immutableLayout.deployed metaMorphoV1_1Bytecode imms,
    immutables := imms }

end Benchmarks.Morpho.MetaMorphoV1_1.FixedBlue
