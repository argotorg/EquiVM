import Benchmarks.Morpho.MetaMorphoV1_1.SubmitTimelockEntry
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitTimelockSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_010
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_025
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_036

/-! Runtime guards before the immediate or deferred timelock update. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem submitTimelockReadDifferent {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hne : value ≠ pendingTimelockDelay evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨6897⟩ (value :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨6908⟩
      (pendingTimelockDelay evm :: value :: R) mem aw rdata evm.accountMap k' C' := by
  exact metaMorphoV1_1_block_6897_fallthrough
    (immWords := wordsOf (immStore v)) hstack (u256_eq_of_ne hne) rd

set_option maxRecDepth 2000 in
theorem submitTimelockReachBranch {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hgood : submitTimelockAllowed evm value)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨6897⟩ (value :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨6938⟩
      (pendingTimelockDelay evm :: value :: R) mem aw rdata evm.accountMap k' C' := by
  obtain ⟨_, _, r1⟩ := submitTimelockReadDifferent v hstack hgood.1 rd
  obtain ⟨_, _, r2⟩ := metaMorphoV1_1_block_6908_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa only [List.length] using hstack) hgood.2.1 r1
  have r3 := metaMorphoV1_1_block_6918_fallthrough (immWords := wordsOf (immStore v))
    hstack (ugt_zero (show value.toNat ≤ (UInt256.ofNat 1209600).toNat from hgood.2.2.1)) r2
  have r4 := metaMorphoV1_1_block_6928_fallthrough (immWords := wordsOf (immStore v))
    hstack (ult_zero (show (UInt256.ofNat 86400).toNat ≤ value.toNat from hgood.2.2.2)) r3
  exact ⟨_, _, r4⟩

set_option maxRecDepth 2000 in
theorem submitTimelockRevertBounds {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hbad : ¬ timelockInBounds value)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨6918⟩
      (pendingTimelockDelay evm :: value :: R) mem aw rdata evm.accountMap k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases hhi : value.toNat ≤ 1209600
  · have r1 := metaMorphoV1_1_block_6918_fallthrough (immWords := wordsOf (immStore v))
      hstack (ugt_zero (show value.toNat ≤ (UInt256.ofNat 1209600).toNat from hhi)) rd
    have hlo : value.toNat < 86400 := by
      have : ¬ 86400 ≤ value.toNat := fun hlo ↦ hbad ⟨hhi, hlo⟩
      omega
    have hc : UInt256.lt value (UInt256.ofNat 86400) ≠ ⟨0⟩ := by
      rw [ult_one (show value.toNat < (UInt256.ofNat 86400).toNat from hlo)]
      decide
    have r2 := metaMorphoV1_1_block_6928_taken (immWords := wordsOf (immStore v)) hstack hc
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    exact metaMorphoV1_1_block_7073 (immWords := wordsOf (immStore v))
      (by simpa only [List.length] using hstack) r2
  · have hc : UInt256.gt value (UInt256.ofNat 1209600) ≠ ⟨0⟩ := by
      rw [ugt_one (show (UInt256.ofNat 1209600).toNat < value.toNat from Nat.lt_of_not_ge hhi)]
      decide
    have r1 := metaMorphoV1_1_block_6918_taken (immWords := wordsOf (immStore v)) hstack hc
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact metaMorphoV1_1_block_7088 (immWords := wordsOf (immStore v))
      (by simpa only [List.length] using hstack) r1

set_option maxRecDepth 2000 in
theorem submitTimelockRevertGuard {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hbad : ¬ submitTimelockAllowed evm value)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨6897⟩ (value :: R)
      mem aw rdata evm.accountMap k C) : RDrev (deployedRuntime v) g s0 := by
  by_cases heq : value = pendingTimelockDelay evm
  · have hc : UInt256.eq value (pendingTimelockDelay evm) ≠ ⟨0⟩ := by
      rw [heq, u256_eq_refl]
      decide
    obtain ⟨_, _, r1⟩ := metaMorphoV1_1_block_6897_taken
      (immWords := wordsOf (immStore v)) hstack hc
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact metaMorphoV1_1_block_1143 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_6897_taken_stack, List.length]; omega) r1
  · obtain ⟨_, _, r1⟩ := submitTimelockReadDifferent v hstack heq rd
    by_cases ht : pendingUpdateTime false (pendingUpdateWord false evm) = ⟨0⟩
    · obtain ⟨_, _, r2⟩ := metaMorphoV1_1_block_6908_fallthrough
        (immWords := wordsOf (immStore v)) (by simpa only [List.length] using hstack) ht r1
      exact submitTimelockRevertBounds v hstack (fun hb ↦ hbad ⟨heq, ht, hb⟩) r2
    · obtain ⟨_, _, r2⟩ := metaMorphoV1_1_block_6908_taken
        (immWords := wordsOf (immStore v)) (by simpa only [List.length] using hstack) ht
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
      exact metaMorphoV1_1_block_4572 (immWords := wordsOf (immStore v))
        (by simpa only [List.length] using hstack) r2

end Benchmarks.Morpho.MetaMorphoV1_1
