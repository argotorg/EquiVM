import Benchmarks.CompoundIII.Comet.DelegateCallBridge
import Benchmarks.CompoundIII.Comet.FallbackMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_082

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometFallbackRun {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {rdata mem : ByteArray}
    {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hsize : ee.calldata.size < UInt256.size)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨18418⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ evm' σ' z out,
      delegateCallViaEVM evm v.extensionDelegate ee.calldata (z, evm', out) ∧
      SourceState s0 ee σ' evm' ∧
      (if z then RDret (deployedRuntime v) g s0 σ' out
       else RDrev (deployedRuntime v) g s0) := by
  have hlen := UInt256.toNat_ofNat_of_lt hsize
  have hz : (UInt256.ofNat 0).toNat = 0 := rfl
  have r1 := cometWithExtendedAssetList_block_18418
    (immWords := wordsOf (immStore v)) hstack h
  simp only [cometWithExtendedAssetList_block_18418_stack,
    cometWithExtendedAssetList_block_18418_memory, wordsOf_immStore_extensionDelegate] at r1
  obtain ⟨evm', σ', z, out, k', C', hc, hs', r2, hout⟩ := delegateCallBridge r1 hs
    (by
      apply immutableLayout.decodeConcreteOfChecks (byte := 0xf4)
      all_goals native_decide)
    (by simpa only [hlen] using fallbackCopy_read ee.calldata mem) (by simp; omega)
  have haddr : AccountAddress.ofUInt256 (EVM.Word.ofNat v.extensionDelegate.val) =
      v.extensionDelegate := by
    exact accountAddress_roundtrip v.extensionDelegate
  rw [haddr] at hc
  refine ⟨evm', σ', z, out, hc, hs', ?_⟩
  have hol := UInt256.toNat_ofNat_of_lt hout
  cases z with
  | false =>
    have r3 := cometWithExtendedAssetList_block_18465_taken
      (immWords := wordsOf (immStore v)) (by simp; omega)
      (by simp only [hz, hol, Nat.zero_add, le_refl]) (by decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    exact cometWithExtendedAssetList_block_18477
      (immWords := wordsOf (immStore v)) (by simp; omega) r3
  | true =>
    have r3 := cometWithExtendedAssetList_block_18465_fallthrough
      (immWords := wordsOf (immStore v)) (by simp; omega)
      (by simp only [hz, hol, Nat.zero_add, le_refl]) (by decide) r2
    have hr := cometWithExtendedAssetList_block_18474
      (immWords := wordsOf (immStore v)) (by simp; omega) r3
    simpa only [cometWithExtendedAssetList_block_18465_fallthrough_memory, hol, hz,
      fallbackCopy_read, ↓reduceIte] using hr

end Benchmarks.CompoundIII.Comet
