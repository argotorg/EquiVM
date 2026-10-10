import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueFinish
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueStatic

/-! Complete runtime mutation and its exact source account map. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem supplyQueueStoreAndFinish {evm s0 : State} {g : Sat256}
    {mem out : ByteArray} {aw : UInt256} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hc : WordArrayCalldataChecks evm.executionEnv.calldata)
    (hlen : calldataArrayLength evm.executionEnv.calldata ≤ 30)
    (hperm : evm.executionEnv.perm = true) (hmem : mem.size = 96)
    (hfree : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨10089⟩
      ([UInt256.ofNat (calldataArrayLength evm.executionEnv.calldata),
        UInt256.ofNat (calldataArrayOffset evm.executionEnv.calldata + 36)] ++ R)
      mem aw out evm.accountMap k C) :
    RDret (deployedRuntime v) g s0
      (supplyQueueSourceState evm
        (fun j ↦ calldataWord evm.executionEnv.calldata
          (calldataArrayOffset evm.executionEnv.calldata + 36 + 32 * j))
        (calldataArrayLength evm.executionEnv.calldata)).accountMap ByteArray.empty := by
  rcases supplyQueuePrepareStore v
      (by change (_ :: R).length + 7 ≤ 1024; simp only [List.length_cons]; omega)
      hperm hlen hmem hfree rd with hoog | ⟨hold, junk, mem1, _, _, aw1, k1, C1, h1⟩
  · exact .inl hoog
  · have h2 := metaMorphoV1_1_block_10103 (immWords := wordsOf (immStore v))
      (by change R.length + 5 ≤ 1024; omega) h1
    simp only [metaMorphoV1_1_block_10103_stack] at h2
    obtain ⟨k3, C3, h3⟩ := supplyQueueWriteLoop v
      (R := UInt256.ofNat (calldataArrayOffset evm.executionEnv.calldata + 36) :: R)
      (calldataArrayLength evm.executionEnv.calldata)
      (by simp only [List.length_cons]; omega)
      hc hperm (i := 0) (by omega) h2
    have hret := supplyQueueFinish v hstack hc hperm h3
    dsimp only [supplyQueueSourceState]
    rw [supplyQueueAccounts_match _ _ _ _ _ hold (by
      have h : 30 < 2 ^ 251 := by decide
      omega)]
    exact hret

end Benchmarks.Morpho.MetaMorphoV1_1
