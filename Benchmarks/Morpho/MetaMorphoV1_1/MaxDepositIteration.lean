import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositInvariant
import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositQueueRoutines

/-! A complete max-deposit loop body, including its zero-cap continue branch. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem maxDepositIterationSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr total len ret i : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 31 ≤ 1024)
    (hlocals : MaxDepositLocals v frame i total ptr)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hmem : 96 ≤ mem.size)
    (hs : SourceState s0 I σ evm)
    (hbound : i.toNat < (codeOwnerStorageWord I σ ⟨20⟩).toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨13946⟩
      ([UInt256.ofNat v.MORPHO.toNat, len, i, ret, total] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm maxDepositIteration .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (total' ptr' : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      MaxDepositLocals v frame' i total' ptr' ∧
      memLoad ⟨64⟩ mem' = ptr' ∧ 96 ≤ ptr'.toNat ∧ 96 ≤ mem'.size ∧
      (ExecBlock config frame evm maxDepositIteration (.ok frame' evm') ∨
        ExecBlock config frame evm maxDepositIteration (.continue frame' evm')) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨14059⟩
        ([i, ⟨1⟩, UInt256.ofNat v.MORPHO.toNat, len, ret, total'] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  let id := maxDepositIdWord I σ i
  let cap := maxDepositCapWord I σ id
  let frame1 := maxDepositCapFrame frame id cap
  let mem1 := maxDepositQueueMemory mem id
  have hprefix := maxDepositQueuePrefix hlocals.contract hlocals.queue hlocals.config
    hlocals.index hs hbound
  have hlocals1 : MaxDepositLocals v frame1 i total ptr := hlocals.cap id cap
  have hcap : frame1.locals.get? "supplyCap" = some (uint256Value cap) := store_get_self _ _ _
  have hfree1 : memLoad ⟨64⟩ mem1 = ptr := by
    rw [maxDepositQueueMemory_free id hmem, hfree]
  have hmem1 : 96 ≤ mem1.size := by rw [maxDepositQueueMemory_size id hmem]; exact hmem
  obtain ⟨aw1, k1, C1, h1⟩ := maxDepositQueueRoutine v (by omega) hbound rd
  by_cases hz : cap = ⟨0⟩
  · rw [if_pos hz] at h1
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_14067_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    change RD (deployedRuntime v) I g s0 ⟨14059⟩
      ([i, ⟨1⟩, UInt256.ofNat v.MORPHO.toNat, len, ret, total] ++ R)
      mem1 aw2 rdata σ k2 C2 at h2
    rw [hs.accounts] at h2
    refine .inr ⟨evm, frame1, total, ptr, mem1, rdata,
      ⟨hs.world, hs.env, rfl⟩, accountStorageStateEq_refl _, hlocals1, hfree1, hlo, hmem1,
      .inr ?_, aw2, k2, C2, h2⟩
    apply hprefix.run
    apply ExecBlock.consContinue (ExecStmt.iteTrue ?_ (ExecBlock.consContinue ExecStmt.continue))
    rw [maxDepositCapConditionSource hcap]
    simp only [hz, decide_true]
  · rw [if_neg hz] at h1
    have hskip : ExecStmt config frame1 evm
        (.ite maxDepositCapCondition [.continue] []) (.ok frame1 evm) :=
      ExecStmt.iteFalse (by rw [maxDepositCapConditionSource hcap]; simp only [hz, decide_false])
        ExecBlock.nil
    have hid : frame1.locals.get? "id" = some (wordBytes32Value id) := by
      rw [show frame1 = maxDepositCapFrame frame id cap from rfl, maxDepositCapFrame,
        store_get_ne _ _ (by decide), store_get_self]
    rcases maxDepositReadersSimulation v hstack hlocals1.contract hlocals1.imms hid
        hlocals1.cursor hcalldata hfree1 hlo hs h1 with
      ⟨hbad, hrev⟩ | ⟨evm2, shares, ptr1, ptr2, ptr3, sa, ss, ba, params, market,
        mem2, out, hs2, hstore, hsource, hfree2, hlo2, hhi2, hmem2, aw2, k2, C2, h2⟩
    · exact .inl ⟨hprefix.run (ExecBlock.consNormal hskip (hbad _)), hrev⟩
    let frame2 := maxDepositBalancesFrame frame1 shares ptr1 ptr2 ptr3 params
      (marketUpdatedBalancesValue market sa ss ba)
    have hlocals2 : MaxDepositLocals v frame2 i total ptr3 := hlocals1.readers _ _ _ _ _ _
    have hcap2 : frame2.locals.get? "supplyCap" = some (uint256Value cap) := by
      rw [maxDepositBalancesFrame_preserves _ _ _ _ _ _ _ _
        (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcap
    rcases maxDepositArithmeticSimulation (frame := frame2) v (by omega) hlocals2.contract
        (maxDepositBalancesFrame_balances _ _ _ _ _ _ _)
        (maxDepositBalancesFrame_shares _ _ _ _ _ _ _) hcap2 hlocals2.total h2 with
      ⟨hbad, hrev⟩ | ⟨hbody, aw3, k3, C3, h3⟩
    · exact .inl ⟨hprefix.run (ExecBlock.consNormal hskip (hsource _ _ hbad)), hrev⟩
    · refine .inr ⟨evm2, maxDepositArithmeticFrame frame2 shares sa ss cap total,
        total + maxDepositGap shares sa ss cap, ptr3, mem2, out, hs2, hstore,
        hlocals2.arithmetic _ _ _ _, hfree2, hlo2, by omega, .inl ?_, aw3, k3, C3, h3⟩
      exact hprefix.run (ExecBlock.consNormal hskip (hsource _ _ hbody))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
