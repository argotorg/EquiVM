import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.ReservesInternal
import Benchmarks.CompoundIII.Comet.FreeWordReturn
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_011

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def GetReservesResult (v : CometWithExtendedAssetListImmutables) (σ : AccountMap)
    (I : ExecutionEnv) (g : Sat256) (s0 : EVM.State) : Prop :=
  let w0 := solcSlotWordAt ⟨0⟩ σ I
  let w1 := solcSlotWordAt ⟨1⟩ σ I
  let time := timestampWord I
  if I.weiValue = ⟨0⟩ ∧ I.calldata.size < 2^255 + 4 ∧ CurrentIndicesValid v w0 w1 time then
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray),
      callViaEVM s0 v.baseToken 0 (tokenBalancePayload I.codeOwner) (z, evm', out) false ∧
      σ' = evm'.accountMap ∧ out.size < 2^138 ∧
      if ReservesReplyValid v w0 w1 time z out then
        RDret (deployedRuntime v) g s0 σ' (reservesWord v w0 w1 time (calldataWord out 0)).toByteArray
      else RDrev (deployedRuntime v) g s0
  else RDrev (deployedRuntime v) g s0

theorem getReservesX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 1)) :
    GetReservesResult v σ I g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachGetReservesBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_1375 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_1476_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hhi : I.calldata.size < 2^255 + 4
    · have rd3 := cometWithExtendedAssetList_block_1483_fallthrough
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_ok hsz hhi hsize) rd2
      have rd4 := cometWithExtendedAssetList_block_1495
        (immWords := wordsOf (immStore v)) (by decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
      have hr := cometReservesInternal (v := v)
        (by change 36 ≤ 1024; decide) solcFreePtrMem_mload64 (by decide) (by decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) SourceState.init rd4
      dsimp only at hr
      by_cases hindices : CurrentIndicesValid v (solcSlotWordAt ⟨0⟩ σ I)
          (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I)
      · rw [if_pos hindices] at hr
        unfold GetReservesResult
        rw [if_pos ⟨hv, hhi, hindices⟩]
        obtain ⟨evm', σ', z, out, hcall, hs', hout, hf⟩ := hr
        refine ⟨evm', σ', z, out, hcall, hs'.accounts, hout, ?_⟩
        by_cases hvalid : ReservesReplyValid v (solcSlotWordAt ⟨0⟩ σ I)
            (solcSlotWordAt ⟨1⟩ σ I) (timestampWord I) z out
        · rw [if_pos hvalid] at hf ⊢
          obtain ⟨aw5, k5, C5, rd5⟩ := hf
          exact cometReturnWord (v := v) (by decide) rd5
        · rw [if_neg hvalid] at hf ⊢
          exact hf
      · simp only [GetReservesResult, hindices, and_false, if_false]
        rw [if_neg hindices] at hr
        exact hr
    · simp only [GetReservesResult, hhi, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_1483_taken
        (immWords := wordsOf (immStore v)) (by decide) (getterLength_huge (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [GetReservesResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_1476_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

end Benchmarks.CompoundIII.Comet
