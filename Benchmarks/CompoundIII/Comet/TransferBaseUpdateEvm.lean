import Benchmarks.CompoundIII.Comet.TransferBaseUpdateMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_069

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferBaseUpdate {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw srcNext srcPtr dstNext dstPtr balance withdrawn supplied ret : UInt256}
    {srcBasic dstBasic : UserBasicData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src dst : AccountAddress) (hstack : R.length + 33 ≤ 1024)
    (hsm : UserBasicMemory mem srcPtr srcBasic) (hdm : UserBasicMemory mem dstPtr dstBasic)
    (hslo : 96 ≤ srcPtr.toNat) (hdlo : 96 ≤ dstPtr.toNat)
    (hsep : srcPtr.toNat + 96 ≤ dstPtr.toNat) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14930⟩
      (srcNext :: srcPtr :: dstNext :: dstPtr :: balance :: withdrawn :: EVM.word src.val ::
        supplied :: EVM.word dst.val :: ret :: R) mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0
      (transferBaseUpdateMemory mem srcPtr dstPtr v evm src dst srcBasic dstBasic srcNext dstNext)
      rdata ⟨14950⟩
      (balance :: withdrawn :: EVM.word src.val :: supplied :: EVM.word dst.val :: ret :: R)
      (transferBaseUpdateOutcome v evm src dst srcBasic dstBasic srcNext dstNext) := by
  have r1 := cometWithExtendedAssetList_block_14930
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 10 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hr := cometUpdateBasePrincipal (v := v) src
    (by change R.length + 8 + 25 ≤ 1024; omega) hsm hslo hs
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  cases hu : updateBaseOutcome v evm src srcBasic srcNext with
  | reverted =>
      simpa only [transferBaseUpdateOutcome, hu, internalMemoryRun] using hr
  | staticViolation =>
      simpa only [transferBaseUpdateOutcome, hu, internalMemoryRun] using hr
  | ok evm' =>
      simp only [hu, internalMemoryRun] at hr
      obtain ⟨σ1, aw1, k1, C1, hs1, r2⟩ := hr
      have r3 := cometWithExtendedAssetList_block_14940
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 10 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
      have hdm' := updateBaseMemory_preserveLater v evm src srcBasic dstBasic srcNext
        hsm hdm hdlo hsep
      have hr' := cometUpdateBasePrincipal (v := v) dst
        (by change R.length + 6 + 25 ≤ 1024; omega)
        hdm' hdlo hs1 (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
      simpa only [transferBaseUpdateOutcome, transferBaseUpdateMemory, hu] using hr'

end Benchmarks.CompoundIII.Comet
