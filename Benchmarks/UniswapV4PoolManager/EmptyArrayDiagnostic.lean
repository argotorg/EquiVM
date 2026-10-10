import Benchmarks.UniswapV4PoolManager.DiffTarget

open Solm Solm.DiffTest Solm.Interp ABI Ethereum Ethereum.EVM
open Benchmarks.UniswapV4PoolManager

/-- Regression diagnostic for empty word arrays with legal trailing calldata. -/
def main : IO Unit := do
  let (target, _) := diffTarget.resolveRuntime (Rng.ofSeed 2026)
  for (name, tr) in [("exttload(bytes32[])", exttload_bytes32_arrayTransition),
      ("extsload(bytes32[])", extsload_bytes32_arrayTransition)] do
    let some cd := encodeCallWithSelector?
      ((Ethereum.KEC (String.toByteArray (transitionSigStr tr))).extract 0 4)
      (tr.params.map Param.ty) [.array []]
      | throw (IO.userError s!"encoding failed: {name}")
    for suffix in [ByteArray.empty, ByteArray.mk #[1]] do
      let data := cd ++ suffix
      let c : Case := {
        label := s!"{name}: empty array, {suffix.size} trailing bytes"
        σ := target.world
        I := target.env target.runtime (EVM.address 0x2000) 0 data true
      }
      let result := runCase target c
      IO.println s!"{c.label}: {result.verdict.describe}"
      IO.println s!"EVM result: {describeEvm result.evmResult}"
      IO.println s!"calldata: {hex data}"
  IO.println s!"bytes1-to-uint256 cast rejected: {(castValue? (.fixedBytes ⟨0, by decide⟩ [1]) (.elem (.int (.uint ⟨256, by decide⟩)))).isNone}"
