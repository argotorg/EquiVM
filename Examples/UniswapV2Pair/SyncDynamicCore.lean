import Examples.UniswapV2Pair.Routines
import Examples.UniswapV2Pair.PairDynamicMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev uniswapSyncTopic : UInt256 :=
  ⟨0x1c411e9a96e071241c2f21f7726b17ae89e3cab4c78be50e062b03a9fffbbad1⟩

abbrev uniswapSyncReserve0Word (packed : UInt256) : UInt256 :=
  UInt256.land reserve112Mask packed

abbrev uniswapSyncReserve1Word (packed : UInt256) : UInt256 :=
  UInt256.land reserve112Mask (UInt256.div packed reserve112Shift)

noncomputable def uniswapSyncLogReserve0Mem (packed : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (uniswapSyncReserve0Word packed)).write 0 mem 128 32

noncomputable def uniswapSyncLogMem (packed : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (uniswapSyncReserve1Word packed)).write 0
    (uniswapSyncLogReserve0Mem packed mem) 160 32

set_option maxHeartbeats 3000000 in
/-- Shared `_update` suffix that emits the `Sync(uint112,uint112)` event from the packed reserve
word and jumps to the dynamic return pc. The memory-cost hypotheses keep the helper independent of
the caller's current memory-active-word shape. -/
theorem RD.uniswapUpdateEmitSyncAndJumpCore {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {packed elapsed timestamp reserve1 reserve0 balance1 balance0 ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw awLoad awStore0 awLog ptr : UInt256}
    {mcostLoad mcostStore0 mcostStore1 mcostLoadLog mcostLog : ℕ}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7339⟩
      (reserve112Shift :: reserve112Mask :: packed :: elapsed :: timestamp :: reserve1 ::
        reserve0 :: balance1 :: balance0 :: ret :: R)
      mem aw rdata acc k C)
    (hmcLoad : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = ⟨64⟩ :: ⟨64⟩ :: reserve112Shift :: reserve112Mask :: packed ::
        elapsed :: timestamp :: reserve1 :: reserve0 :: balance1 :: balance0 :: ret :: R →
      memoryExpansionCost s .MLOAD = mcostLoad)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ptr)
    (hawLoad : UInt256.ofNat (MachineState.M aw.toNat 64 32) = awLoad)
    (hmcStore0 : ∀ s : State, s.machineState.activeWords = awLoad →
      s.machineState.stack = ptr :: uniswapSyncReserve0Word packed :: ptr ::
        ⟨64⟩ :: reserve112Shift :: reserve112Mask :: packed :: elapsed :: timestamp ::
        reserve1 :: reserve0 :: balance1 :: balance0 :: ret :: R →
      memoryExpansionCost s .MSTORE = mcostStore0)
    (hawStore0 : UInt256.ofNat (MachineState.M awLoad.toNat ptr.toNat 32) = awStore0)
    (hmcStore1 : ∀ s : State, s.machineState.activeWords = awStore0 →
      s.machineState.stack = ((ptr : UInt256) + ⟨32⟩) ::
        uniswapSyncReserve1Word packed :: ptr :: ⟨64⟩ :: elapsed :: timestamp ::
        reserve1 :: reserve0 :: balance1 :: balance0 :: ret :: R →
      memoryExpansionCost s .MSTORE = mcostStore1)
    (hawStore1 :
      UInt256.ofNat (MachineState.M awStore0.toNat (((ptr : UInt256) + ⟨32⟩).toNat) 32) =
        awLog)
    (hmcLoadLog : ∀ s : State, s.machineState.activeWords = awLog →
      s.machineState.stack = ⟨64⟩ :: ptr :: ⟨64⟩ :: elapsed :: timestamp ::
        reserve1 :: reserve0 :: balance1 :: balance0 :: ret :: R →
      memoryExpansionCost s .MLOAD = mcostLoadLog)
    (hmload64Log :
      (if (⟨64⟩ : UInt256).toNat ≥ (pairDynamicMem mem ptr (uniswapSyncReserve0Word packed) (uniswapSyncReserve1Word packed)).size
          ∨ (⟨64⟩ : UInt256) ≥ awLog * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((pairDynamicMem mem ptr (uniswapSyncReserve0Word packed) (uniswapSyncReserve1Word packed)).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ptr)
    (hawLoadLog : UInt256.ofNat (MachineState.M awLog.toNat 64 32) = awLog)
    (hmcLog : ∀ s : State, s.machineState.activeWords = awLog →
      s.machineState.stack = ptr ::
        ((⟨64⟩ : UInt256) + UInt256.sub ptr ptr) :: uniswapSyncTopic ::
        elapsed :: timestamp :: reserve1 :: reserve0 :: balance1 :: balance0 :: ret :: R →
      memoryExpansionCost s .LOG1 = mcostLog)
    (hawLog : UInt256.ofNat
      (MachineState.M awLog.toNat ptr.toNat
        (((⟨64⟩ : UInt256) + UInt256.sub ptr ptr).toNat)) =
        awLog)
    (hperm : ee.perm = true)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret R
      (pairDynamicMem mem ptr (uniswapSyncReserve0Word packed) (uniswapSyncReserve1Word packed)) awLog rdata acc k' C' := by
  have rd7342 := evm_run h with [
    push1 ⟨64⟩, dup1,
    raw mload mcostLoad ptr awLoad (by decide) hmcLoad hmload64 hawLoad (by evm_ov)]
  have rd7347₀ := evm_run rd7342 with [dup5, dup5, and, dup2]
  have rd7348 := rd7347₀.mstore mcostStore0 (pairDynamicMem0 mem ptr (uniswapSyncReserve0Word packed)) awStore0
    (by decide) hmcStore0 (by rfl) hawStore0 (by evm_ov)
  have rd7359₀ := evm_run rd7348 with [
    swap2, swap1, swap4, div, swap1, swap2, and, push1 ⟨32⟩, dup3, add]
  have rd7360 := rd7359₀.mstore mcostStore1 (pairDynamicMem mem ptr (uniswapSyncReserve0Word packed) (uniswapSyncReserve1Word packed)) awLog
    (by decide) hmcStore1
    (by rfl)
    hawStore1 (by evm_ov)
  have rd7362 := evm_run rd7360 with [
    dup2,
    raw mload mcostLoadLog ptr awLog (by decide) hmcLoadLog hmload64Log hawLoadLog
      (by evm_ov)]
  have rd7395 := rd7362.pushConst uniswapSyncTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd7404 := evm_run rd7395 with [
    swap3, swap2, dup2, swap1, sub, swap1, swap2, add, swap1]
  have rd7405 := rd7404.log1 mcostLog awLog (by decide) hperm hmcLog hawLog
    (by simp only [List.length_cons]; omega)
  have rd7411 := evm_run rd7405 with [pop, pop, pop, pop, pop, pop]
  exact ⟨_, _, rd7411.jump (by decide) hret (by evm_ov)⟩

end UniswapV2Pair
