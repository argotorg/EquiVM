import Benchmarks.CompoundIII.Comet.AbsorbPointsEvm
import Benchmarks.CompoundIII.Comet.CheckedSub256Evm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbAfterAccounts {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ptr n base startGas ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (addr : AccountAddress) (hstack : R.length + 20 ≤ 1024) (hn : n.toNat < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hmem : 96 ≤ mem.size)
    (hlo : 96 ≤ ptr.toNat) (hb : ptr.toNat + 128 < 2^64)
    (hs : SourceState s0 ee σ evm) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨16703⟩
      (n :: base :: ⟨1⟩ :: EVM.word addr.val :: n :: ret :: startGas :: R)
      mem aw rdata σ k C) :
    ∃ endGas, internalDynamicRun (deployedRuntime v) ee g s0 ret R
      (absorbAfterAccountsOutcome evm addr n startGas endGas) := by
  let endGas := (g.subNat (C + 35)).toUInt256
  refine ⟨endGas, ?_⟩
  have r1 := cometWithExtendedAssetList_block_16703
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hr := cometCheckedSub256 (v := v) (by change R.length + 8 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  by_cases hle : endGas.toNat ≤ startGas.toNat
  · rw [if_pos hle] at hr
    rw [absorbAfterAccountsOutcome, if_pos hle]
    obtain ⟨k2, C2, r2⟩ := hr
    exact cometAbsorbPoints (v := v) addr hstack hn hfree hmem hlo hb hs hret r2
  · rw [if_neg hle] at hr
    rw [absorbAfterAccountsOutcome, if_neg hle]
    exact hr

end Benchmarks.CompoundIII.Comet
