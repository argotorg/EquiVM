import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueRemoveRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueReader
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueRemovalTailRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueDelete

/-! Complete simulation of an omitted market, with fresh storage reads and modular reader calls. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueOmittedSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem out : ByteArray} {aw : UInt256} {k C curr len i : Nat}
    {indexes : List Value} {seen : List Bool} {queue : List UInt256}
    {cursor : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 17 ≤ 1024)
    (hready : UpdateWithdrawQueueReady frame (immStore v) indexes curr i seen queue cursor)
    (hheap : UpdateWithdrawQueueHeap mem curr len seen queue cursor) (hi : i < curr)
    (hcalldata : I.calldata.size < UInt256.size)
    (hs : SourceState s0 I evm.accountMap evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨8460⟩
      (UInt256.ofNat i :: R) mem aw out evm.accountMap k C) :
    (ExecBlock config frame evm updateWithdrawQueueRemoval .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config frame evm updateWithdrawQueueRemoval .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    ∃ frame' evm' cursor' mem' out',
      SourceState s0 I evm'.accountMap evm' ∧
      UpdateWithdrawQueueReady frame' (immStore v) indexes curr i seen queue cursor' ∧
      UpdateWithdrawQueueHeap mem' curr len seen queue cursor' ∧
      ExecBlock config frame evm updateWithdrawQueueRemoval (.ok frame' evm') ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨8452⟩ (UInt256.ofNat i :: R)
        mem' aw' out' evm'.accountMap k' C' := by
  have hfit : i < UInt256.size := by
    have hf := hheap.seen.fit
    simp only [seenWords, List.length_map, hheap.seenLength] at hf
    omega
  rcases updateWithdrawQueueOmittedIndex v (by omega) rd with
    ⟨hbad, hrev⟩ | ⟨hbound, aw1, k1, C1, r1⟩
  · exact .inl ⟨updateWithdrawQueueOmittedReadRevert hready hfit (by
      change ¬ i < (codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨21⟩).toNat
      rw [hs.env]
      rw [ulit_toNat' _ hfit] at hbad
      omega), hrev⟩
  rw [ulit_toNat' _ hfit] at hbound
  let id := codeOwnerStorageWord I evm.accountMap
    (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨21⟩)) + UInt256.ofNat i)
  have hid_eq : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨21⟩)) + UInt256.ofNat i) = id := by
    change codeOwnerStorageWord evm.executionEnv evm.accountMap _ = id
    rw [hs.env]
  have hread := updateWithdrawQueueOmittedRead (evm := evm) hready hfit (by
    change i < (codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨21⟩).toNat
    rw [hs.env]
    exact hbound)
  dsimp only at hread
  rw [hid_eq] at hread
  have hr1 := hready.idFrame id
  have hid : (updateWithdrawQueueIdFrame frame id).locals.get? "id" =
      some (wordBytes32Value id) := store_get_self _ _ _
  rcases updateWithdrawQueueBeforeCallRuntime (evm := evm) (R := UInt256.ofNat i :: R) v
      (by simp only [List.length_cons]; omega) (id := id)
      (by rw [hs.env])
      (by simpa only [hs.env] using r1) with
    ⟨hbad, hrev⟩ | ⟨hcap, htime, aw2, k2, C2, r2⟩
  · exact .inl ⟨hread.run
      (updateWithdrawQueueBeforeCallRevert hr1.contract hr1.config hr1.pendingCap hid hbad),
      hrev⟩
  have hguards := updateWithdrawQueueBeforeCallSource hr1.contract hr1.config hr1.pendingCap
    hid hcap htime
  have hm2 := ((hheap.scratch ⟨21⟩).mappingScratch id ⟨13⟩).mappingScratch id ⟨16⟩
  rcases updateWithdrawQueueReaderSimulation (R := UInt256.ofNat i :: R) v
      (by simp only [List.length_cons]; omega) hr1 hid hm2 hcalldata hs
      (by simpa only [hs.env] using r2) with
    ⟨hbad, hrev⟩ | ⟨evm3, shares, cursor3, mem3, out3, hs3, hm3, hcall, aw3, k3, C3, r3⟩
  · exact .inl ⟨hread.run (hguards.run hbad), hrev⟩
  let frame3 := cursorResultFrame (updateWithdrawQueueIdFrame frame id)
    "__c2" (uint256Value shares) cursor3
  have hr3 : UpdateWithdrawQueueReady frame3 (immStore v) indexes curr i seen queue cursor3 :=
    hr1.readerFrame shares cursor3
  have hid3 : frame3.locals.get? "id" = some (wordBytes32Value id) := by
    dsimp only [frame3]
    rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact hid
  have hshares : frame3.locals.get? "__c2" = some (uint256Value shares) :=
    cursorResultFrame_value _ _ _ _ (by decide)
  have hprefix (result : ExecResult)
      (ht : ExecBlock config frame3 evm3 (updateWithdrawQueueRemoval.drop 6) result) :
      ExecBlock config frame evm updateWithdrawQueueRemoval result :=
    hread.run (hguards.run (hcall result ht))
  rcases updateWithdrawQueueRemovalTailRuntime (evm := evm3) (R := UInt256.ofNat i :: R) v
      (by simp only [List.length_cons]; omega) hm3 (by simpa only [hs3.env] using r3) with
    ⟨hbad, hrev⟩ | ⟨hgood, mem4, hm4, aw4, k4, C4, r4⟩
  · exact .inl ⟨hprefix _
      (updateWithdrawQueueRemovalTailRevert hr3.contract hr3.config hid3 hshares hbad), hrev⟩
  have r4' : RD (deployedRuntime v) I g s0 ⟨8573⟩ (id :: UInt256.ofNat i :: R)
      mem4 aw4 out3 evm3.accountMap k4 C4 := by simpa only [hs3.env] using r4
  by_cases hperm : I.perm = true
  · obtain ⟨hs5, aw5, k5, C5, r5⟩ := updateWithdrawQueueDeleteReturn v
      (by simp only [List.length_cons]; omega) hperm hs3 r4'
    exact .inr (.inr ⟨frame3, deletedMarketConfigState evm3 id, cursor3, _, out3, hs5,
      hr3, hm4.mappingScratch id ⟨13⟩,
      hprefix _ (updateWithdrawQueueRemovalTailReturns hr3.contract hr3.config hid3 hshares hgood),
      aw5, k5, C5, r5⟩)
  · have hfalse : I.perm = false := Bool.eq_false_of_not_eq_true hperm
    exact .inr (.inl ⟨hprefix _
      (updateWithdrawQueueRemovalTailStatic hr3.contract hr3.config hid3 hshares hgood
        (by rw [hs3.env]; exact hfalse)),
      updateWithdrawQueueDeleteStatic v (by simp only [List.length_cons]; omega) hfalse r4'⟩)

end Benchmarks.Morpho.MetaMorphoV1_1
