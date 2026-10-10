import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayStorage

/-! Reading complete bytes32 arrays from a Solidity storage layout. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: full-slot array reads, with no restriction on the stored length.
theorem solidityReadWordArray {layout : StorageLayout} {er : EvaledStorageRef}
    {base : UInt256}
    (hloc : ∀ i, layout { er with steps := er.steps ++ [.aindex (.int (Int.ofNat i))] } =
      some (.leaf (bytes32Loc (base + UInt256.ofNat i))))
    (evm : State) (index n : Nat) :
    solidityReadArray? layout evm er (.elem (.bytes abiBytes32Width)) index n =
      .ok (wordArrayValues
        (fun i ↦ Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (base + UInt256.ofNat i))
        index n) := by
  have hl (i : Nat) : layout { er with steps := er.steps ++ [.aindex (.int (i : Int))] } =
      some (.leaf (bytes32Loc (base + UInt256.ofNat i))) := hloc i
  induction n generalizing index with
  | zero => simp only [solidityReadArray?, wordArrayValues, wordArrayWords, List.map_nil]
  | succ n ih =>
      simp only [solidityReadArray?, solidityReadStorage?, solidityLeafLoc?, hl,
        storageLocLoad_bytes32, EvalResult.ofOption, bind, EvalResult.bind, ih]
      rfl

end Benchmarks.Morpho.MetaMorphoV1_1
