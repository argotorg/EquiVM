import Benchmarks.Scaffolds.ERC721.Bytecode
import Solm.Equiv

/-!
# ERC721 constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace ERC721

theorem erc721ConstructorCorrect :
    constructorEquivalence erc721Config erc721CreationBytecode erc721Contract erc721Bytecode := by
  sorry

end ERC721
