import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayCalldata
import Benchmarks.Morpho.MetaMorphoV1_1.Common
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_060

/-! Shared indexing into calldata arrays with one-word elements. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem calldataArrayIndex {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {start len i ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hi : i.toNat < len.toNat) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11986⟩
      ([start, len, i, ret] ++ R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret
      ((UInt256.shiftLeft i ⟨5⟩ + start) :: R) mem aw out σ k' C' := by
  have h1 := metaMorphoV1_1_block_11986_fallthrough (immWords := wordsOf (immStore v))
    (by change (ret :: R).length + 4 ≤ 1024
        simpa only [List.length_cons, Nat.add_assoc] using hstack)
    (by rw [ult_one hi]; rfl) rd
  exact RD.pack (metaMorphoV1_1_block_11996 (immWords := wordsOf (immStore v))
    (by omega) hret h1)

theorem calldataArrayIndex_address {cd : ByteArray} (hc : WordArrayCalldataChecks cd)
    {i : Nat} (hi : i < calldataArrayLength cd) :
    (UInt256.shiftLeft (UInt256.ofNat i) ⟨5⟩ +
      UInt256.ofNat (calldataArrayOffset cd + 36)).toNat =
      calldataArrayOffset cd + 36 + 32 * i := by
  have hdata := hc.data
  have hsize : cd.size < UInt256.size := lt_trans hc.size (by decide)
  rw [shiftLeft5_ofNat_eq (by omega)]
  exact (uadd_ofNat_toNat (by omega) (by omega) (by omega)).trans (by omega)

end Benchmarks.Morpho.MetaMorphoV1_1
