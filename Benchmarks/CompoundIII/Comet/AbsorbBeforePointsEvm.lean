import Benchmarks.CompoundIII.Comet.AbsorbBeforePointsModel
import Benchmarks.CompoundIII.Comet.AbsorbAccountsEvm
import Benchmarks.CompoundIII.Comet.AccrueInternalEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_035

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbBeforePoints {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {rdata : ByteArray}
    {aw absorber : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 47 ≤ 1024) (hvalid : AbsorbCalldataValid ee.calldata)
    (hgas : cometGasBound g.toUInt256) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨16664⟩
      (absorber :: absorbArrayBase ee.calldata :: UInt256.ofNat (absorbArrayLength ee.calldata) ::
        ⟨22⟩ :: R) solcFreePtrMem aw rdata σ k C) :
    X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
      ∃ startGas result, AbsorbBeforePointsTrace v ee.calldata evm result ∧
        absorbAccountsRun (deployedRuntime v) ee g s0 absorber (⟨22⟩ :: startGas :: R) result := by
  have hp : pauseBitWord evm ⟨3, by decide⟩ =
      UInt256.land (UInt256.shiftRight (solcSlotWordAt ⟨1⟩ σ ee) ⟨248⟩) ⟨8⟩ := by
    rw [pauseBitWord, pauseFlagsWord_eq_shift, hs.storageRead]
    rfl
  by_cases hz : (pauseBitWord evm ⟨3, by decide⟩).toNat = 0
  · have hw := uint256_toNat_eq_zero hz
    rw [hp] at hw
    obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_16664_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) hw h
    have r2 := cometWithExtendedAssetList_block_16683
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    let startGas := (g.subNat (C1 + 2)).toUInt256
    have hr := cometAccrueInternal (v := v) (by change R.length + 6 + 37 ≤ 1024; omega) hs
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    cases ha : accrueOutcome v evm with
    | reverted =>
        rw [ha] at hr
        exact Or.inr ⟨startGas, .reverted, .accrueReverted hz ha, hr⟩
    | staticViolation =>
        rw [ha] at hr
        exact Or.inr ⟨startGas, .staticViolation, .accrueStatic hz ha, hr⟩
    | ok evm' =>
        rw [ha] at hr
        obtain ⟨σ', k', C', hs', r3⟩ := hr
        have r4 := cometWithExtendedAssetList_block_16692
          (immWords := wordsOf (immStore v)) (by change R.length + 6 + 1 ≤ 1024; omega) r3
        obtain hoog | ⟨result, ht, hrun⟩ := cometAbsorbAccounts (v := v)
          (by change R.length + 2 + 45 ≤ 1024; omega) hvalid (Nat.zero_le _) hgas
          (Nat.zero_le _) (by decide) solcFreePtrMem_mload64 (by decide)
          (by rw [solcFreePtrMem_size]) (by rw [solcFreePtrMem_size]; decide) hs' r4
        · exact Or.inl hoog
        · exact Or.inr ⟨startGas, result, .accrued hz ha ht, hrun⟩
  · have hw : pauseBitWord evm ⟨3, by decide⟩ ≠ ⟨0⟩ := by
      intro hzero
      exact hz (congrArg UInt256.toNat hzero)
    rw [hp] at hw
    obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_16664_taken
      (immWords := wordsOf (immStore v)) (by omega) hw
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact Or.inr ⟨⟨0⟩, .reverted, .paused hz,
      cometWithExtendedAssetList_block_6727 (immWords := wordsOf (immStore v))
        (by change R.length + 5 + 3 ≤ 1024; omega) r1⟩

end Benchmarks.CompoundIII.Comet
