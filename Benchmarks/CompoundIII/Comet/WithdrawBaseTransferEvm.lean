import Benchmarks.CompoundIII.Comet.WithdrawBaseEventsEvm
import Benchmarks.CompoundIII.Comet.WithdrawBaseTrace
import Benchmarks.CompoundIII.Comet.TransferOutInternal
import Benchmarks.CompoundIII.Comet.InternalDynamicOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometWithdrawBaseTransfer {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount balance supplied ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (src recipient : AccountAddress) (hstack : R.length + 22 ≤ 1024)
    (hsupplied : supplied.toNat < 2^104) (hperm : ee.perm = true)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat)
    (hbound : free.toNat + 68 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨15861⟩
      (balance :: EVM.word recipient.val :: amount :: EVM.word src.val :: supplied :: ret :: R)
      mem aw rdata σ k C) :
    ∃ result, WithdrawBaseTransfer v recipient amount evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have r1 := cometWithExtendedAssetList_block_15861
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [cometWithExtendedAssetList_block_15861_stack] at r1
  rw [wordsOf_immStore_baseToken] at r1
  obtain ⟨result, ht, hr⟩ := cometTransferOutInternal (v := v)
    (by change R.length + 5 + 17 ≤ 1024; omega) hfree hlo hbound
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  cases result with
  | none => exact ⟨.reverted, .failed ht, hr⟩
  | some evm' =>
    obtain ⟨σ', mem', aw', out, k', C', hs', _, _, r2⟩ := hr
    obtain ⟨mem'', aw'', k'', C'', r3⟩ := cometWithdrawBaseEvents (v := v)
      (by omega) hsupplied hperm hret r2
    exact ⟨.ok evm', .done ht, σ', mem'', aw'', out, k'', C'', hs', r3⟩

end Benchmarks.CompoundIII.Comet
