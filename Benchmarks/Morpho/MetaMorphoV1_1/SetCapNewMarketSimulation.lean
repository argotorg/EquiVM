import Benchmarks.Morpho.MetaMorphoV1_1.SetCapEnableSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.SetCapQueueRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.SetCapStaticRuntime

/-! Complete source/bytecode simulation of adding a market to the withdrawal queue. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem setCapNewMarketSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params cap id ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 34 ≤ 1024)
    (hready : SetCapReady frame p id cap ptr) (himms : frame.immutables = immStore v)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hmem : ptr.toNat ≤ mem.size) (hparamslo : 96 ≤ params.toNat)
    (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hbytes : mem.readWithPadding params.toNat 160 = p.bytes)
    (hloads : MarketParamsLoads mem params p) (hs : SourceState s0 I σ evm)
    (hacc : ∃ acc, σ.get? I.codeOwner = some acc)
    (rd : RD (deployedRuntime v) I g s0 ⟨13596⟩
      ([params, cap, id, ret, solcMappingSlot ⟨13⟩ id] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm setCapEnableBody .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config frame evm setCapEnableBody .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧ SetCapReady frame' p id cap cursor ∧
      ExecBlock config frame evm setCapEnableBody (.ok frame' evm') ∧ I.perm = true ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨13576⟩
        ([id, cap, id, ret, solcMappingSlot ⟨13⟩ id] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  have hlength : setCapQueueLength evm = codeOwnerStorageWord I σ ⟨21⟩ := hs.storageRead ⟨21⟩
  rcases setCapQueueLengthRuntime v
      (by change R.length + 5 + 5 ≤ 1024; omega) rd with
    ⟨hbad, hrev⟩ | ⟨hsmall, k1, C1, h1⟩
  · refine .inl ⟨setCapEnableBodyRevertsLength hready.contract hready.queue ?_, hrev⟩
    rw [hlength]
    omega
  have hsmallSource : (setCapQueueLength evm).toNat ≤ 2 ^ 64 - 1 := by
    rw [hlength]; omega
  cases hperm : I.perm with
  | false =>
      refine .inr (.inl ⟨setCapEnableBodyPushStatic hready.contract hready.queue hready.id
        hsmallSource (by rw [hs.env]; exact hperm), ?_⟩)
      exact setCapQueueStaticRuntime v (by change R.length + 5 + 4 ≤ 1024; omega) hperm h1
  | true =>
      have hsPush := setCapQueuePushState_source hs id
      have hnewLength : setCapQueueLength (setCapQueuePushState evm id) =
          codeOwnerStorageWord I
            (setCapQueueAccounts I σ (codeOwnerStorageWord I σ ⟨21⟩) id) ⟨21⟩ :=
        hsPush.storageRead ⟨21⟩
      rcases setCapQueuePushRuntime v (by omega) hsmall hacc hperm h1 with
        ⟨hfull, hrev⟩ | ⟨hfits, aw2, k2, C2, h2⟩
      · exact .inl ⟨setCapEnableBodyRevertsFull hready.contract hready.queue hready.id
          hsmallSource (by rwa [hnewLength]), hrev⟩
      have hguard : evalExpr? config frame (setCapQueuePushState evm id)
          (setCapQueueCondition 30) = .ok (.bool true) := by
        rw [setCapQueueConditionSource hready.contract hready.queue, hnewLength,
          decide_eq_true hfits]
      have hprefix (result : ExecResult)
          (htail : ExecBlock config frame (setCapQueuePushState evm id)
            (setCapEnableBody.drop 3) result) :
          ExecBlock config frame evm setCapEnableBody result := by
        apply setCapEnableBodyPushPrefix hready.contract hready.queue hready.id hsmallSource
        exact (ABlock.start.requireStep hguard).run htail
      have hprefixMem : MemoryPrefix mem (wordAt0Mem ⟨21⟩ mem) ptr.toNat :=
        memoryPrefix_sparse_writeWord mem 0 ptr.toNat ⟨21⟩ (.inr (by decide))
      have hfree2 : memLoad ⟨64⟩ (wordAt0Mem ⟨21⟩ mem) = ptr :=
        (memLoad_write_disjoint _ _ _ _ (by change 96 ≤ mem.size; omega)
          (.inr (by decide))).trans hfree
      have hbytes2 : (wordAt0Mem ⟨21⟩ mem).readWithPadding params.toNat 160 = p.bytes := by
        rw [memoryPrefix_read_words hprefixMem 5 params.toNat hparamslo hparams (by omega)]
        exact hbytes
      have hloads2 := hloads.prefix hprefixMem hparamslo (by omega) hparams
        (lt_of_le_of_lt hparams ptr.val.isLt)
      rcases setCapEnableSimulation v p hstack hready himms hcalldata hfree2 hlo
          (le_trans hmem hprefixMem.size) hparamslo hparams hbytes2 hloads2 hsPush hperm h2 with
        ⟨hbad, hrev⟩ | ⟨evm3, frame3, cursor, mem3, out3, hs3, hready3, hsource3,
          aw3, k3, C3, h3⟩
      · exact .inl ⟨hprefix _ hbad, hrev⟩
      · exact .inr (.inr ⟨evm3, frame3, cursor, mem3, out3, hs3, hready3,
          hprefix _ hsource3, rfl, aw3, k3, C3, h3⟩)

end Benchmarks.Morpho.MetaMorphoV1_1
