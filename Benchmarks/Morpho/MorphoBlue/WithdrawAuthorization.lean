import Benchmarks.Morpho.MorphoBlue.WithdrawGuardPrepare
import Benchmarks.Morpho.MorphoBlue.SenderAuthorizedReach
import Benchmarks.Morpho.MorphoBlue.UnauthorizedMessage
import Benchmarks.Morpho.MorphoBlue.SupplyAccrueRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem senderAuthorizedMem_createHeap {p : MarketParamsWords} {free : Nat} {mem : ByteArray}
    (hm : CreateMarketHeap p free mem) (hfree : 288 ≤ free) (ee : ExecutionEnv) (account : UInt256) :
    CreateMarketHeap p free (senderAuthorizedMem ee account mem) := by
  unfold senderAuthorizedMem
  split
  · exact hm
  · exact (hm.hash (by omega) account (UInt256.ofNat 6)).hash (by omega) _ _

def withdrawGuardMem (p : MarketParamsWords) (ee : ExecutionEnv) (account : UInt256) : ByteArray :=
  morphoUnauthorizedMem (senderAuthorizedMem ee account (supplyGuardMem p))

theorem withdrawGuardHeap (p : MarketParamsWords) (ee : ExecutionEnv) (account : UInt256) :
    CreateMarketHeap p 544 (withdrawGuardMem p ee account) ∧
      morphoErrorLength (withdrawGuardMem p ee account) (UInt256.ofNat 480) = UInt256.ofNat 12 :=
  ((supplyGuardHeap p).1 |> fun hm => senderAuthorizedMem_createHeap hm (by decide) ee account).message
    (by decide) (by decide) _ _

theorem withdrawGuardMem_zero96 (p : MarketParamsWords) (ee : ExecutionEnv) (account : UInt256) :
    memLoad (UInt256.ofNat 96) (withdrawGuardMem p ee account) = UInt256.ofNat 0 := by
  have hm := senderAuthorizedMem_createHeap (supplyGuardHeap p).1 (by decide) ee account
  rw [withdrawGuardMem, morphoUnauthorizedMem, hm.messageLoad (by decide) (by decide) _ _ _ (by decide) (by decide)]
  have hp := (senderAuthorizedMem_heap
    (createMarketHeap_morpho (supplyGuardHeap p).1 (by decide) 0 (by decide) (lt_usize _ (by decide))) ee account).2
  rw [memoryPrefix_memLoad hp _ (by decide) (by decide) (by rw [(supplyGuardHeap p).1.size]; decide)]
  exact supplyGuardMem_zero96 p

theorem morphoWithdrawAuthorization {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw assets shares account receiver : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (p : MarketParamsWords) (hstack : R.length + 32 ≤ 1024)
    (hc : account.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7629)
      (withdrawAccrueTail p.id assets shares account receiver R) (supplyGuardMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([senderAuthorizedWord σ ee account, UInt256.ofNat 480, UInt256.ofNat 7641] ++
        withdrawAccrueTail p.id assets shares account receiver R)
      (withdrawGuardMem p ee account) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_7629 (immWords := wordsOf (immStore v))
    (by change R.length + 6 + 9 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoSenderAuthorized (v := v)
    (by change R.length + 12 + 8 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hc rd1
  have rd3 := morphoBlocks.morpho_block_5612 (immWords := wordsOf (immStore v))
    (by change R.length + 13 + 2 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  have hm := senderAuthorizedMem_createHeap (supplyGuardHeap p).1 (by decide) ee account
  obtain ⟨a4, k4, C4, rd4⟩ := morphoUnauthorizedMessage (v := v)
    (by change R.length + 13 + 8 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hm.freePtr (by decide) rd3
  have rd5 := morphoBlocks.morpho_block_585 (immWords := wordsOf (immStore v))
    (by change R.length + 12 + 3 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd4
  exact ⟨a4, _, _, rd5⟩

end Benchmarks.Morpho.MorphoBlue
