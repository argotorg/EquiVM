import Benchmarks.Morpho.MorphoBlue.WithdrawAuthorization
import Benchmarks.Morpho.MorphoBlue.BorrowGuardPrepare

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoBorrowAuthorization {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw assets shares account receiver : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (p : MarketParamsWords) (hstack : R.length + 32 ≤ 1024)
    (hc : account.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8469)
      (borrowAccrueTail p.id assets shares account receiver R) (supplyGuardMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      ([senderAuthorizedWord σ ee account, UInt256.ofNat 480, UInt256.ofNat 8481] ++
        borrowAccrueTail p.id assets shares account receiver R)
      (withdrawGuardMem p ee account) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_8469 (immWords := wordsOf (immStore v))
    (by simp only [borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoSenderAuthorized (v := v)
    (by simp only [borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hc rd1
  have rd3 := morphoBlocks.morpho_block_5612 (immWords := wordsOf (immStore v))
    (by simp only [borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  have hm := senderAuthorizedMem_createHeap (supplyGuardHeap p).1 (by decide) ee account
  obtain ⟨a4, k4, C4, rd4⟩ := morphoUnauthorizedMessage (v := v)
    (by simp only [borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hm.freePtr (by decide) rd3
  have rd5 := morphoBlocks.morpho_block_585 (immWords := wordsOf (immStore v))
    (by simp only [borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd4
  exact ⟨a4, _, _, rd5⟩

end Benchmarks.Morpho.MorphoBlue
