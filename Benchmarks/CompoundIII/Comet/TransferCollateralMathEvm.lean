import Benchmarks.CompoundIII.Comet.TransferCollateralStacks
import Benchmarks.CompoundIII.Comet.CheckedSub128Evm
import Benchmarks.CompoundIII.Comet.CheckedAdd128Evm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferCollateralMath {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw amount srcBalance dstBalance ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (src dst asset : AccountAddress) (hstack : R.length + 17 ≤ 1024)
    (ha : amount.toNat < 2^128) (hs : srcBalance.toNat < 2^128) (hd : dstBalance.toNat < 2^128)
    (h : RD (deployedRuntime v) ee g s0 ⟨15305⟩
      (transferCollateralSubStack src dst asset amount srcBalance dstBalance ret R)
      mem aw rdata σ k C) :
    (amount.toNat ≤ srcBalance.toNat ∧ dstBalance.toNat + amount.toNat < 2^128 ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨15435⟩
        (transferCollateralWriteStack src dst asset amount srcBalance (UInt256.sub srcBalance amount)
          dstBalance (dstBalance + amount) ret R) mem aw rdata σ k' C') ∨
    (¬ (amount.toNat ≤ srcBalance.toNat ∧ dstBalance.toNat + amount.toNat < 2^128) ∧
      RDrev (deployedRuntime v) g s0) := by
  rcases cometCheckedSub128 (v := v) (by change R.length + 10 + 6 ≤ 1024; omega) hs ha
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) h with
    ⟨hsub, k1, C1, r1⟩ | ⟨hsub, hr⟩
  · have r2 := cometWithExtendedAssetList_block_15425
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 14 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    rcases cometCheckedAdd128 (v := v) (by change R.length + 11 + 6 ≤ 1024; omega) hd ha
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2 with
      ⟨hadd, k3, C3, r3⟩ | ⟨hadd, hr⟩
    · exact Or.inl ⟨hsub, hadd, k3, C3, r3⟩
    · exact Or.inr ⟨fun hh ↦ hadd hh.2, hr⟩
  · exact Or.inr ⟨fun hh ↦ hsub hh.1, hr⟩

end Benchmarks.CompoundIII.Comet
