import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueLoops
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueAllocationRuntime

/-! Simulate the complete authorized queue update after its role check. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueSimulation {evm s0 : State} {g : Sat256}
    {mem out : ByteArray} {aw : UInt256} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 21 ≤ 1024)
    (hc : WordArrayCalldataChecks evm.executionEnv.calldata) (hmem : mem.size ≤ 128)
    (hfree : memLoad ⟨64⟩ mem = ⟨128⟩)
    (hs : SourceState s0 evm.executionEnv evm.accountMap evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨8067⟩
      (UInt256.ofNat (calldataArrayOffset evm.executionEnv.calldata + 36) ::
        UInt256.ofNat (calldataArrayLength evm.executionEnv.calldata) :: R)
      mem aw out evm.accountMap k C) :
    let frame := updateWithdrawQueuePrefixFrame evm (immStore v)
      (calldataUintArrayValues evm.executionEnv.calldata)
    let stmts := updateWithdrawQueueAllocation ++
      [updateWithdrawQueueBuildLoop, updateWithdrawQueueRemoveLoop] ++ updateWithdrawQueueTail
    (ExecBlock config frame evm stmts .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config frame evm stmts .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    ∃ final evm', ExecBlock config frame evm stmts (.ok final evm') ∧
      RDret (deployedRuntime v) g s0 evm'.accountMap ByteArray.empty := by
  dsimp only
  let curr := codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨21⟩
  let len := calldataArrayLength evm.executionEnv.calldata
  let frame := updateWithdrawQueuePrefixFrame evm (immStore v)
    (calldataUintArrayValues evm.executionEnv.calldata)
  let tail := [updateWithdrawQueueBuildLoop, updateWithdrawQueueRemoveLoop] ++
    updateWithdrawQueueTail
  have hcurr : frame.locals.get? "currLength" = some (.int (Int.ofNat curr.toNat)) :=
    store_get_self _ _ _
  have hlen : frame.locals.get? "newLength" = some (.int (Int.ofNat len)) := by
    dsimp only [frame, updateWithdrawQueuePrefixFrame]
    rw [store_get_ne _ _ (by decide), store_get_self, calldataUintArrayValues_length]
  have hn : (UInt256.ofNat len).toNat = len := ulit_toNat' _
    (lt_of_le_of_lt hc.length (by decide))
  have hcd : evm.executionEnv.calldata.size < UInt256.size := lt_trans hc.size (by decide)
  rcases updateWithdrawQueueSeenAllocation v (by omega) hcd hmem hfree rd with
    ⟨hbad, hrev⟩ | ⟨hcb, hbad, hrev⟩ | ⟨hcb, hcf, aw1, k1, C1, r1⟩
  · change solcMaxU64 < curr.toNat at hbad
    exact .inl ⟨updateWithdrawQueueCurrentLengthReverts hcurr (by omega) tail, hrev⟩
  · exact .inl ⟨updateWithdrawQueueSeenAllocationReverts rfl hcurr hcb hbad tail, hrev⟩
  have hp : (UInt256.ofNat (160 + 32 * curr.toNat)).toNat = 160 + 32 * curr.toNat :=
    ulit_toNat' _ (lt_trans hcf (by decide))
  have hm1 : (wordArrayInitMemory mem ⟨128⟩ curr.toNat).size = 160 :=
    wordArrayInitMemory_size _ _ _ hmem (by decide)
  have hf1 : memLoad ⟨64⟩ (wordArrayInitMemory mem ⟨128⟩ curr.toNat) =
      UInt256.ofNat (160 + 32 * curr.toNat) :=
    wordArrayInitMemory_free _ _ _ (by decide)
  rcases updateWithdrawQueueArrayAllocation v (by omega) hcd
      (by rw [hm1, hp]; omega) (by rw [hp]; omega) hf1 r1 with
    ⟨hbad, hrev⟩ | ⟨hnb, hbad, hrev⟩ | ⟨hnb, hnf, aw2, k2, C2, r2⟩
  · change solcMaxU64 < (UInt256.ofNat len).toNat at hbad
    rw [hn] at hbad
    exact False.elim (Nat.not_lt_of_ge hc.length hbad)
  · change ¬ (UInt256.ofNat (160 + 32 * curr.toNat)).toNat + 32 +
        32 * (UInt256.ofNat len).toNat < 2 ^ 64 at hbad
    rw [hp, hn] at hbad
    exact .inl ⟨updateWithdrawQueueArrayAllocationReverts rfl hcurr hlen hcb hc.length hcf
      (by omega) tail, hrev⟩
  change (UInt256.ofNat (160 + 32 * curr.toNat)).toNat + 32 +
    32 * (UInt256.ofNat len).toNat < 2 ^ 64 at hnf
  rw [hp, hn] at hnf
  have hfit : 192 + 32 * curr.toNat + 32 * len < 2 ^ 64 := by omega
  have hdata : UInt256.ofNat (160 + 32 * curr.toNat) + ⟨32⟩ =
      UInt256.ofNat (192 + 32 * curr.toNat) := by
    change UInt256.ofNat (160 + 32 * curr.toNat) + UInt256.ofNat 32 = _
    apply (u256_add_comm _ _).trans
    exact (u256_32_add_ofNat _).trans (congrArg UInt256.ofNat (by omega))
  change RD (deployedRuntime v) evm.executionEnv g s0 ⟨8163⟩
    (⟨0⟩ :: UInt256.ofNat len ::
      UInt256.ofNat (calldataArrayOffset evm.executionEnv.calldata + 36) :: ⟨128⟩ :: curr ::
      UInt256.ofNat (160 + 32 * curr.toNat) :: (UInt256.ofNat (160 + 32 * curr.toNat) + ⟨32⟩) :: R)
    (wordArrayInitMemory (wordArrayInitMemory mem ⟨128⟩ curr.toNat)
      (UInt256.ofNat (160 + 32 * curr.toNat)) (UInt256.ofNat len).toNat)
    aw2 out evm.accountMap k2 C2 at r2
  rw [hn, hdata] at r2
  have r2' : RD (deployedRuntime v) evm.executionEnv g s0 ⟨8163⟩
      ([⟨0⟩, UInt256.ofNat len,
        UInt256.ofNat (calldataArrayOffset evm.executionEnv.calldata + 36), ⟨128⟩,
        UInt256.ofNat curr.toNat, UInt256.ofNat (160 + 32 * curr.toNat),
        UInt256.ofNat (192 + 32 * curr.toNat)] ++ R)
      (updateWithdrawQueueInitMem mem curr.toNat len) aw2 out evm.accountMap k2 C2 := by
    simpa only [u256_ofNat_toNat] using r2
  have hr := updateWithdrawQueueInitialReady evm (immStore v)
    (calldataUintArrayValues evm.executionEnv.calldata)
  dsimp only at hr
  rw [calldataUintArrayValues_length] at hr
  have hm := updateWithdrawQueueInitialMemory mem curr.toNat len hmem
    (lt_trans hfit (by decide))
  have hprefix := updateWithdrawQueueAllocationPass (evm := evm)
    rfl hcurr hlen hcb hc.length hcf hfit tail
  rcases updateWithdrawQueueLoopsSimulation v hstack hc hr hm hfit rfl hs r2' with
    ⟨hbad, hrev⟩ | ⟨hbad, hstatic⟩ | ⟨final, evm', htail, hret⟩
  · exact .inl ⟨hprefix.run hbad, hrev⟩
  · exact .inr (.inl ⟨hprefix.run hbad, hstatic⟩)
  · exact .inr (.inr ⟨final, evm', hprefix.run htail, hret⟩)

end Benchmarks.Morpho.MetaMorphoV1_1
