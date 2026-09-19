import Solidity.Test.Specs.OZ.ERC6909

/-! ERC6909Bench (`Examples/OpenZeppelinBench/ERC6909/ERC6909Bench.sol`) in the Solidity spec
language, with its OpenZeppelin bases. -/

namespace OpenZeppelinBench.ERC6909.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation OpenZeppelinBench.OZ

def bench : SourceUnit := sol% contract ERC6909Bench is ERC6909 {}

def program : Program := [context, ierc165, erc165, ierc6909, erc6909, bench]
def target : String := "ERC6909Bench"

#guard (erc6909.contract?.map (·.functions.length)) = some 15
#guard (erc6909.contract?.map (·.errors.length)) = some 6

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) :=
  [ ("allowance(address,address,uint256)", "598af9e7"),
    ("approve(address,uint256,uint256)", "426a8493"),
    ("balanceOf(address,uint256)", "00fdd58e"),
    ("isOperator(address,address)", "b6363cf2"),
    ("setOperator(address,bool)", "558a7297"),
    ("supportsInterface(bytes4)", "01ffc9a7"),
    ("transfer(address,uint256,uint256)", "095bcdb6"),
    ("transferFrom(address,address,uint256,uint256)", "fe99049a") ]

end OpenZeppelinBench.ERC6909.SoliditySpec
