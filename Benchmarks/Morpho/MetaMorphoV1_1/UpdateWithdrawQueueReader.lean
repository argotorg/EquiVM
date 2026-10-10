import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueRemoveSource
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueHeap
import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.AllocatedReaderCalls
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_043

/-! Reuse the allocated supply-share reader while preserving both queue arrays. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueReaderSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem out : ByteArray} {aw : UInt256} {k C curr len i : Nat}
    {indexes : List Value} {seen : List Bool} {queue : List UInt256}
    {cursor id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 16 ≤ 1024)
    (hready : UpdateWithdrawQueueReady frame (immStore v) indexes curr i seen queue cursor)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hheap : UpdateWithdrawQueueHeap mem curr len seen queue cursor)
    (hcalldata : I.calldata.size < UInt256.size)
    (hs : SourceState s0 I evm.accountMap evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨8526⟩ (id :: R) mem aw out evm.accountMap k C) :
    (ExecBlock config frame evm (updateWithdrawQueueRemoval.drop 3) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ evm' shares cursor' mem' out',
      SourceState s0 I evm'.accountMap evm' ∧
      UpdateWithdrawQueueHeap mem' curr len seen queue cursor' ∧
      (∀ result, ExecBlock config (cursorResultFrame frame "__c2" (uint256Value shares) cursor')
        evm' (updateWithdrawQueueRemoval.drop 6) result →
        ExecBlock config frame evm (updateWithdrawQueueRemoval.drop 3) result) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨8568⟩ (shares :: id :: R)
        mem' aw' out' evm'.accountMap k' C' := by
  have hc := hready.contract
  have himms := hready.immutables
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc himms hid
  subst c
  subst imms
  have hargs : evalExprs? config
      { contract := contract, locals := locals, immutables := immStore v } evm
      [.immutable "MORPHO", .var "id", .env .this, .var cursorName] =
      .ok [.address v.MORPHO, wordBytes32Value id, .address I.codeOwner,
        uint256Value cursor] := by
    have hm : evalExpr? config
        { contract := contract, locals := locals, immutables := immStore v } evm
        (.immutable "MORPHO") = .ok (.address v.MORPHO) := evalImmutable_MORPHO _ _ _ _ _
    simp only [evalExprs?, hm, evalExpr?, hid, hready.cursor, envValue, hs.env,
      EvalResult.ofOption, bind, EvalResult.bind, pure]
  have haddr (a : AccountAddress) : AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
    rw [ulit_toNat' _ (lt_of_lt_of_le a.isLt (by decide))]
    exact accountAddress_ofNat_toNat a
  have r1 := metaMorphoV1_1_block_8526 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_8526_stack, wordsOf_immStore_MORPHO] at r1
  change RD (deployedRuntime v) I g s0 ⟨14078⟩
    (UInt256.ofNat v.MORPHO.val :: id :: UInt256.ofNat I.codeOwner.val :: ⟨8568⟩ :: id :: R)
    mem aw out evm.accountMap _ _ at r1
  rcases supplySharesAllocationSimulation v (immStore v)
      (by simp only [List.length_cons]; omega) hcalldata hheap.free
      (by have := hheap.cursorLo; omega)
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hs r1 with
    ⟨hbad, hrev⟩ | ⟨evm', final, shares, cursor', mem', aw', out', k', C',
      hsource, hs', hstore, hfree, hlo, hhi, hsize, hprefix, hmono, r2⟩
  · simp only [haddr] at hbad
    exact .inl ⟨ExecBlock.consRevert (supplySharesReaderRevert hargs hbad), hrev⟩
  · simp only [haddr] at hsource
    have hcall := supplySharesReaderCall (ret := slotsAndCursorName) hargs hsource
    refine .inr ⟨evm', shares, cursor', mem', out', hs',
      hheap.preserved hprefix hmono hhi hsize hfree, ?_, aw', k', C', r2⟩
    intro result htail
    exact cursorCallPrefix (by decide) hcall htail

end Benchmarks.Morpho.MetaMorphoV1_1
