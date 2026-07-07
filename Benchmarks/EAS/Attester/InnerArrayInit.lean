import Benchmarks.EAS.Attester.InnerArrayEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

abbrev attesterMultiRevokeInnerArrayInitSecondZeroWord
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  attesterMultiOuterArrayInitFreeWord mem aw + (⟨32⟩ : UInt256)

abbrev attesterMultiRevokeInnerArrayInitSecondZeroMem
    (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
    (attesterMultiOuterArrayInitZeroMem mem aw)
    (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat 32

abbrev attesterMultiRevokeInnerArrayInitSecondZeroAw
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiOuterArrayInitZeroAw mem aw).toNat
      (attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw).toNat 32)

abbrev attesterMultiRevokeInnerArrayInitStepMem
    (slot : UInt256) (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray (attesterMultiOuterArrayInitFreeWord mem aw)).write 0
    (attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw) slot.toNat 32

abbrev attesterMultiRevokeInnerArrayInitStepAw
    (slot : UInt256) (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiRevokeInnerArrayInitSecondZeroAw mem aw).toNat
      slot.toNat 32)

structure AttesterMultiRevokeInnerArrayInitState where
  slot : UInt256
  remaining : UInt256
  mem : ByteArray
  aw : UInt256

abbrev attesterMultiRevokeInnerArrayInitStack
    (I : ExecutionEnv) (base len payload : UInt256)
    (a : AttesterMultiRevokeInnerArrayInitState) : List UInt256 :=
  [a.slot, a.remaining, base, ⟨0⟩, len, len, payload,
    ⟨0⟩, ⟨128⟩,
    attesterFirstArrayLengthWord I,
    attesterSecondArrayLengthWord I,
    attesterSecondArrayPayloadStartWord I,
    attesterFirstArrayLengthWord I,
    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
    ⟨97⟩, solcSelectorWord I]

abbrev attesterMultiRevokeInnerArrayInitExitStack
    (I : ExecutionEnv) (base len payload : UInt256)
    (_a : AttesterMultiRevokeInnerArrayInitState) : List UInt256 :=
  [⟨0⟩, base, len, len, payload,
    ⟨0⟩, ⟨128⟩,
    attesterFirstArrayLengthWord I,
    attesterSecondArrayLengthWord I,
    attesterSecondArrayPayloadStartWord I,
    attesterFirstArrayLengthWord I,
    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
    ⟨97⟩, solcSelectorWord I]

abbrev attesterMultiRevokeInnerArrayInitStepState
    (a : AttesterMultiRevokeInnerArrayInitState) :
    AttesterMultiRevokeInnerArrayInitState :=
  { slot := (⟨32⟩ : UInt256) + a.slot,
    remaining := UInt256.sub a.remaining ⟨1⟩,
    mem := attesterMultiRevokeInnerArrayInitStepMem a.slot a.mem a.aw,
    aw := attesterMultiRevokeInnerArrayInitStepAw a.slot a.mem a.aw }

abbrev attesterMultiRevokeInnerArrayInitFinalMem
    (a : AttesterMultiRevokeInnerArrayInitState) : ByteArray :=
  attesterMultiRevokeInnerArrayInitStepMem a.slot a.mem a.aw

abbrev attesterMultiRevokeInnerArrayInitFinalAw
    (a : AttesterMultiRevokeInnerArrayInitState) : UInt256 :=
  attesterMultiRevokeInnerArrayInitStepAw a.slot a.mem a.aw

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeInnerArrayInitFinalIteration
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len payload : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨475⟩ : UInt256)
      [slot, (⟨1⟩ : UInt256), base, ⟨0⟩, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
      [⟨0⟩, base, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      (attesterMultiRevokeInnerArrayInitStepMem slot mem aw)
      (attesterMultiRevokeInnerArrayInitStepAw slot mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  let free := attesterMultiOuterArrayInitFreeWord mem aw
  let aw1 := attesterMultiOuterArrayInitAwAfterMload aw
  let mem1 := attesterMultiOuterArrayInitFreeMem mem aw
  let aw2 := attesterMultiOuterArrayInitFreeAw aw
  let mem2 := attesterMultiOuterArrayInitZeroMem mem aw
  let aw3 := attesterMultiOuterArrayInitZeroAw mem aw
  let second := attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw
  let mem3 := attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw
  let aw4 := attesterMultiRevokeInnerArrayInitSecondZeroAw mem aw
  let mem4 := attesterMultiRevokeInnerArrayInitStepMem slot mem aw
  let aw5 := attesterMultiRevokeInnerArrayInitStepAw slot mem aw
  have hcostMload :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          [⟨64⟩, ⟨64⟩, slot, (⟨1⟩ : UInt256), base, ⟨0⟩,
            len, len, payload, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I] →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStore64 :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          [⟨64⟩, ((⟨64⟩ : UInt256) + free), free, slot,
            (⟨1⟩ : UInt256), base, ⟨0⟩, len, len, payload,
            ⟨0⟩, ⟨128⟩, attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreZero :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          [free, (⟨0⟩ : UInt256), ⟨0⟩, free, slot,
            (⟨1⟩ : UInt256), base, ⟨0⟩, len, len, payload,
            ⟨0⟩, ⟨128⟩, attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreSecondZero :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack =
          [second, (⟨0⟩ : UInt256), free, slot, (⟨1⟩ : UInt256),
            base, ⟨0⟩, len, len, payload, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw4 - Cₘ aw3 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreSlot :
      ∀ s : State,
        s.machineState.activeWords = aw4 →
        s.machineState.stack =
          [slot, free, slot, (⟨1⟩ : UInt256), base, ⟨0⟩,
            len, len, payload, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw5 - Cₘ aw4 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hrd497 : ∃ k497 C497, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨497⟩ : UInt256)
      [slot, (⟨1⟩ : UInt256), base, ⟨0⟩, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem4 aw5 ByteArray.empty (cA, σ) k497 C497 := by
    exact ⟨_, _, by
      simpa [free, aw1, mem1, aw2, mem2, aw3, second, mem3, aw4, mem4, aw5] using
        evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨475⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨476⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨478⟩, 0x80, .DUP1) (by evm_ov),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨479⟩, 0x51, .MLOAD)
      hcostMload (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨480⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨481⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨482⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨483⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨484⟩, 0x91, .SWAP2) (by evm_ov),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨485⟩, 0x52, .MSTORE)
      hcostStore64 (by rfl) (by rfl) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨486⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨487⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨488⟩, 0x82, .DUP3) (by evm_ov),
    raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3
      (by attester_decode_at v, ⟨489⟩, 0x52, .MSTORE)
      hcostStoreZero (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨490⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨492⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨493⟩, 0x01, .ADD) (by evm_ov),
    raw mstore (Cₘ aw4 - Cₘ aw3) mem3 aw4
      (by attester_decode_at v, ⟨494⟩, 0x52, .MSTORE)
      hcostStoreSecondZero (by rfl) (by rfl) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨495⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw5 - Cₘ aw4) mem4 aw5
      (by attester_decode_at v, ⟨496⟩, 0x52, .MSTORE)
      hcostStoreSlot (by rfl) (by rfl) (by evm_ov)]⟩
  obtain ⟨_, _, rd497⟩ := hrd497
  have hrd511 : ∃ k511 C511, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨511⟩ : UInt256)
      [((⟨32⟩ : UInt256) + slot), ⟨0⟩, base, ⟨0⟩, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem4 aw5 ByteArray.empty (cA, σ) k511 C511 := by
    exact ⟨_, _, by
      simpa using
        evm_run rd497 with [
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨497⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨499⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨500⟩, 0x90, .SWAP1) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨501⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨503⟩, 0x90, .SWAP1) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨504⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨505⟩, 0x90, .SWAP1) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨506⟩, 0x81, .DUP2) (by evm_ov),
    raw push2 ⟨475⟩ (by attester_decode_at v, ⟨507⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨510⟩, 0x57, .JUMPI)
      (by native_decide) (by evm_ov)]⟩
  obtain ⟨_, _, rd511⟩ := hrd511
  have rd518 := evm_run rd511 with [
    raw swap1 (by attester_decode_at v, ⟨511⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨512⟩, 0x50, .POP) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨513⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨514⟩, 0x50, .POP) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨515⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨516⟩, 0x50, .POP) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨517⟩, 0x5f, .PUSH0) (by evm_ov)]
  exact ⟨_, _, by
    simpa [free, aw1, mem1, aw2, mem2, aw3, second, mem3, aw4, mem4, aw5] using rd518⟩

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeInnerArrayInitNonFinalIteration
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len payload remaining : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hnext : UInt256.sub remaining (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨475⟩ : UInt256)
      [slot, remaining, base, ⟨0⟩, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨475⟩ : UInt256)
      [((⟨32⟩ : UInt256) + slot), UInt256.sub remaining ⟨1⟩,
        base, ⟨0⟩, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      (attesterMultiRevokeInnerArrayInitStepMem slot mem aw)
      (attesterMultiRevokeInnerArrayInitStepAw slot mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  let free := attesterMultiOuterArrayInitFreeWord mem aw
  let aw1 := attesterMultiOuterArrayInitAwAfterMload aw
  let mem1 := attesterMultiOuterArrayInitFreeMem mem aw
  let aw2 := attesterMultiOuterArrayInitFreeAw aw
  let mem2 := attesterMultiOuterArrayInitZeroMem mem aw
  let aw3 := attesterMultiOuterArrayInitZeroAw mem aw
  let second := attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw
  let mem3 := attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw
  let aw4 := attesterMultiRevokeInnerArrayInitSecondZeroAw mem aw
  let mem4 := attesterMultiRevokeInnerArrayInitStepMem slot mem aw
  let aw5 := attesterMultiRevokeInnerArrayInitStepAw slot mem aw
  have hcostMload :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          [⟨64⟩, ⟨64⟩, slot, remaining, base, ⟨0⟩,
            len, len, payload, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I] →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStore64 :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          [⟨64⟩, ((⟨64⟩ : UInt256) + free), free, slot,
            remaining, base, ⟨0⟩, len, len, payload,
            ⟨0⟩, ⟨128⟩, attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreZero :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          [free, (⟨0⟩ : UInt256), ⟨0⟩, free, slot,
            remaining, base, ⟨0⟩, len, len, payload,
            ⟨0⟩, ⟨128⟩, attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreSecondZero :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack =
          [second, (⟨0⟩ : UInt256), free, slot, remaining,
            base, ⟨0⟩, len, len, payload, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw4 - Cₘ aw3 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreSlot :
      ∀ s : State,
        s.machineState.activeWords = aw4 →
        s.machineState.stack =
          [slot, free, slot, remaining, base, ⟨0⟩,
            len, len, payload, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw5 - Cₘ aw4 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hrd497 : ∃ k497 C497, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨497⟩ : UInt256)
      [slot, remaining, base, ⟨0⟩, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem4 aw5 ByteArray.empty (cA, σ) k497 C497 := by
    exact ⟨_, _, by
      simpa [free, aw1, mem1, aw2, mem2, aw3, second, mem3, aw4, mem4, aw5] using
        evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨475⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨476⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨478⟩, 0x80, .DUP1) (by evm_ov),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨479⟩, 0x51, .MLOAD)
      hcostMload (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨480⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨481⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨482⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨483⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨484⟩, 0x91, .SWAP2) (by evm_ov),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨485⟩, 0x52, .MSTORE)
      hcostStore64 (by rfl) (by rfl) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨486⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨487⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨488⟩, 0x82, .DUP3) (by evm_ov),
    raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3
      (by attester_decode_at v, ⟨489⟩, 0x52, .MSTORE)
      hcostStoreZero (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨490⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨492⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨493⟩, 0x01, .ADD) (by evm_ov),
    raw mstore (Cₘ aw4 - Cₘ aw3) mem3 aw4
      (by attester_decode_at v, ⟨494⟩, 0x52, .MSTORE)
      hcostStoreSecondZero (by rfl) (by rfl) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨495⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw5 - Cₘ aw4) mem4 aw5
      (by attester_decode_at v, ⟨496⟩, 0x52, .MSTORE)
      hcostStoreSlot (by rfl) (by rfl) (by evm_ov)]⟩
  obtain ⟨_, _, rd497⟩ := hrd497
  exact ⟨_, _, by
    simpa [free, aw1, mem1, aw2, mem2, aw3, second, mem3, aw4, mem4, aw5] using
      evm_run rd497 with [
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨497⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨499⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨500⟩, 0x90, .SWAP1) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨501⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨503⟩, 0x90, .SWAP1) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨504⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨505⟩, 0x90, .SWAP1) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨506⟩, 0x81, .DUP2) (by evm_ov),
    raw push2 ⟨475⟩ (by attester_decode_at v, ⟨507⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨510⟩, 0x57, .JUMPI)
      (by simpa using hnext)
      (attesterMultiRevokeInnerArrayInitLoopJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeInnerArrayInitLoop
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len payload : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hlenNe : len.toNat ≠ 0)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨475⟩ : UInt256)
      [slot, len, base, ⟨0⟩, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ a' k' C',
      a'.remaining = (⟨1⟩ : UInt256) ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
        (attesterMultiRevokeInnerArrayInitExitStack I base len payload a')
        (attesterMultiRevokeInnerArrayInitFinalMem a')
        (attesterMultiRevokeInnerArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k' C' := by
  let Inv : Nat → AttesterMultiRevokeInnerArrayInitState → Prop :=
    fun n a => a.remaining = UInt256.ofNat (n + 1) ∧ n + 1 < UInt256.size
  let stk := attesterMultiRevokeInnerArrayInitStack I base len payload
  let memOf : AttesterMultiRevokeInnerArrayInitState → ByteArray := fun a => a.mem
  let awOf : AttesterMultiRevokeInnerArrayInitState → UInt256 := fun a => a.aw
  let exitStk := attesterMultiRevokeInnerArrayInitExitStack I base len payload
  let exitMem := attesterMultiRevokeInnerArrayInitFinalMem
  let exitAw := attesterMultiRevokeInnerArrayInitFinalAw
  have hexit :
      ∀ a, Inv 0 a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨475⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ k' C',
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨518⟩ : UInt256) (exitStk a) (exitMem a) (exitAw a)
            ByteArray.empty (cA, σ) k' C' := by
    intro a hInv k C rd
    have hrem : a.remaining = (⟨1⟩ : UInt256) := by
      simpa [Inv] using hInv.1
    exact attesterX_multiRevokeInnerArrayInitFinalIteration
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
      (payload := payload) (mem := a.mem) (aw := a.aw)
      (by
        simpa [stk, memOf, awOf, hrem, attesterMultiRevokeInnerArrayInitStack]
          using rd)
  have hbody :
      ∀ n a, Inv (n + 1) a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨475⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ a' k' C',
          Inv n a' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨475⟩ : UInt256) (stk a') (memOf a') (awOf a')
            ByteArray.empty (cA, σ) k' C' := by
    intro n a hInv k C rd
    let a' := attesterMultiRevokeInnerArrayInitStepState a
    have hsub :
        UInt256.sub a.remaining (⟨1⟩ : UInt256) = UInt256.ofNat (n + 1) := by
      rw [hInv.1]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        attester_u256_ofNat_succ_sub_one (n := n + 1)
          (by simpa [Inv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hInv.2)
    have hnext : UInt256.sub a.remaining (⟨1⟩ : UInt256) ≠ ⟨0⟩ := by
      rw [hsub]
      exact attester_u256_ofNat_pos_ne_zero
        (n := n + 1) (by omega) (by
          have hlt : n + 1 < UInt256.size := by
            have := hInv.2
            omega
          exact hlt)
    obtain ⟨k', C', rd'⟩ :=
      attesterX_multiRevokeInnerArrayInitNonFinalIteration
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
        (payload := payload) (remaining := a.remaining) (mem := a.mem) (aw := a.aw)
        hnext
        (by
          simpa [stk, memOf, awOf, attesterMultiRevokeInnerArrayInitStack]
            using rd)
    refine ⟨a', k', C', ?_, ?_⟩
    · constructor
      · simpa [a', attesterMultiRevokeInnerArrayInitStepState] using hsub
      · have := hInv.2
        omega
    · simpa [a', stk, memOf, awOf, attesterMultiRevokeInnerArrayInitStack,
        attesterMultiRevokeInnerArrayInitStepState] using rd'
  let a0 : AttesterMultiRevokeInnerArrayInitState :=
    { slot := slot, remaining := len, mem := mem, aw := aw }
  have hInv0 : Inv (len.toNat - 1) a0 := by
    constructor
    · have hsucc : (len.toNat - 1) + 1 = len.toNat := by omega
      simpa [a0, hsucc] using (u256_ofNat_toNat len).symm
    · have hsucc : (len.toNat - 1) + 1 = len.toNat := by omega
      rw [hsucc]
      exact len.val.isLt
  obtain ⟨a', k', C', hInvFinal, rdFinal⟩ :=
    RD.whileLoopCarryExit
      (code := patchedRuntime v) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := ByteArray.empty) (acc := (cA, σ))
      (header := (⟨475⟩ : UInt256)) (exit := (⟨518⟩ : UInt256))
      Inv stk memOf awOf exitStk exitMem exitAw hexit hbody
      (len.toNat - 1) a0 hInv0 k C
      (by
        simpa [a0, stk, memOf, awOf, attesterMultiRevokeInnerArrayInitStack]
          using hreach)
  exact ⟨a', k', C', by simpa [Inv] using hInvFinal.1, rdFinal⟩

theorem attesterX_multiRevokeFirstInnerArrayInitProgress
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (hlenNe : attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩)
    (hprogress :
      ∃ a' k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
        RD (patchedRuntime v) I g
          (initState cA gh bl σ σ₀ g A I) (⟨475⟩ : UInt256)
          (((⟨32⟩ : UInt256) +
              attesterInnerArrayAllocFreeWord
                (attesterMultiOuterArrayInitFinalMem a')
                (attesterMultiOuterArrayInitFinalAw a')) ::
            attesterFirstInnerArrayLengthWord I ::
            attesterInnerArrayAllocFreeWord
              (attesterMultiOuterArrayInitFinalMem a')
              (attesterMultiOuterArrayInitFinalAw a') ::
            ⟨0⟩ ::
            attesterFirstInnerArrayLengthWord I ::
            attesterFirstInnerArrayLengthWord I ::
            (attesterFirstInnerArrayStartWord I + ⟨32⟩) ::
            [⟨0⟩, ⟨128⟩,
              attesterFirstArrayLengthWord I,
              attesterSecondArrayLengthWord I,
              attesterSecondArrayPayloadStartWord I,
              attesterFirstArrayLengthWord I,
              (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
              ⟨97⟩, solcSelectorWord I])
          (attesterInnerArrayAllocMem
            (attesterFirstInnerArrayLengthWord I)
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a'))
          (attesterInnerArrayAllocAw
            (attesterFirstInnerArrayLengthWord I)
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a'))
          ByteArray.empty (cA, σ) k C) :
    ∃ a' b' k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      b'.remaining = (⟨1⟩ : UInt256) ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
        (attesterMultiRevokeInnerArrayInitExitStack I
          (attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a'))
          (attesterFirstInnerArrayLengthWord I)
          (attesterFirstInnerArrayStartWord I + ⟨32⟩)
          b')
        (attesterMultiRevokeInnerArrayInitFinalMem b')
        (attesterMultiRevokeInnerArrayInitFinalAw b')
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨a', k0, C0, hrem, rd0⟩ := hprogress
  have hlenNatNe : (attesterFirstInnerArrayLengthWord I).toNat ≠ 0 := by
    intro hzero
    apply hlenNe
    apply u256_inj
    simpa using hzero
  obtain ⟨b', k1, C1, hbrem, rd1⟩ :=
    attesterX_multiRevokeInnerArrayInitLoop
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (slot :=
        ((⟨32⟩ : UInt256) +
          attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a')))
      (base :=
        attesterInnerArrayAllocFreeWord
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
      (len := attesterFirstInnerArrayLengthWord I)
      (payload := attesterFirstInnerArrayStartWord I + ⟨32⟩)
      (mem :=
        attesterInnerArrayAllocMem
          (attesterFirstInnerArrayLengthWord I)
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
      (aw :=
        attesterInnerArrayAllocAw
          (attesterFirstInnerArrayLengthWord I)
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
      (k := k0) (C := C0) hlenNatNe
      (by simpa using rd0)
  exact ⟨a', b', k1, C1, hrem, hbrem, rd1⟩

abbrev attesterMultiAttestInnerArrayInitFreeBumpWord
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  attesterMultiOuterArrayInitFreeWord mem aw + (⟨192⟩ : UInt256)

abbrev attesterMultiAttestInnerArrayInitFreeMem
    (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray (attesterMultiAttestInnerArrayInitFreeBumpWord mem aw)).write 0
    mem 64 32

abbrev attesterMultiAttestInnerArrayInitFreeAw
    (_mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiOuterArrayInitAwAfterMload aw).toNat 64 32)

abbrev attesterMultiAttestInnerArrayInitField32Word
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  attesterMultiOuterArrayInitFreeWord mem aw + (⟨32⟩ : UInt256)

abbrev attesterMultiAttestInnerArrayInitField64Word
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  attesterMultiOuterArrayInitFreeWord mem aw + (⟨64⟩ : UInt256)

abbrev attesterMultiAttestInnerArrayInitField96Word
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  attesterMultiOuterArrayInitFreeWord mem aw + (⟨96⟩ : UInt256)

abbrev attesterMultiAttestInnerArrayInitField128Word
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  attesterMultiOuterArrayInitFreeWord mem aw + (⟨128⟩ : UInt256)

abbrev attesterMultiAttestInnerArrayInitField160Word
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  attesterMultiOuterArrayInitFreeWord mem aw + (⟨160⟩ : UInt256)

abbrev attesterMultiAttestInnerArrayInitZero0Mem
    (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
    (attesterMultiAttestInnerArrayInitFreeMem mem aw)
    (attesterMultiOuterArrayInitFreeWord mem aw).toNat 32

abbrev attesterMultiAttestInnerArrayInitZero0Aw
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiAttestInnerArrayInitFreeAw mem aw).toNat
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat 32)

abbrev attesterMultiAttestInnerArrayInitZero32Mem
    (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
    (attesterMultiAttestInnerArrayInitZero0Mem mem aw)
    (attesterMultiAttestInnerArrayInitField32Word mem aw).toNat 32

abbrev attesterMultiAttestInnerArrayInitZero32Aw
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiAttestInnerArrayInitZero0Aw mem aw).toNat
      (attesterMultiAttestInnerArrayInitField32Word mem aw).toNat 32)

abbrev attesterMultiAttestInnerArrayInitZero64Mem
    (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
    (attesterMultiAttestInnerArrayInitZero32Mem mem aw)
    (attesterMultiAttestInnerArrayInitField64Word mem aw).toNat 32

abbrev attesterMultiAttestInnerArrayInitZero64Aw
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiAttestInnerArrayInitZero32Aw mem aw).toNat
      (attesterMultiAttestInnerArrayInitField64Word mem aw).toNat 32)

abbrev attesterMultiAttestInnerArrayInitZero96Mem
    (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
    (attesterMultiAttestInnerArrayInitZero64Mem mem aw)
    (attesterMultiAttestInnerArrayInitField96Word mem aw).toNat 32

abbrev attesterMultiAttestInnerArrayInitZero96Aw
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiAttestInnerArrayInitZero64Aw mem aw).toNat
      (attesterMultiAttestInnerArrayInitField96Word mem aw).toNat 32)

abbrev attesterMultiAttestInnerArrayInitDataOffsetMem
    (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨96⟩ : UInt256)).write 0
    (attesterMultiAttestInnerArrayInitZero96Mem mem aw)
    (attesterMultiAttestInnerArrayInitField128Word mem aw).toNat 32

abbrev attesterMultiAttestInnerArrayInitDataOffsetAw
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiAttestInnerArrayInitZero96Aw mem aw).toNat
      (attesterMultiAttestInnerArrayInitField128Word mem aw).toNat 32)

abbrev attesterMultiAttestInnerArrayInitZero160Mem
    (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
    (attesterMultiAttestInnerArrayInitDataOffsetMem mem aw)
    (attesterMultiAttestInnerArrayInitField160Word mem aw).toNat 32

abbrev attesterMultiAttestInnerArrayInitZero160Aw
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiAttestInnerArrayInitDataOffsetAw mem aw).toNat
      (attesterMultiAttestInnerArrayInitField160Word mem aw).toNat 32)

abbrev attesterMultiAttestInnerArrayInitStepMem
    (slot : UInt256) (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray (attesterMultiOuterArrayInitFreeWord mem aw)).write 0
    (attesterMultiAttestInnerArrayInitZero160Mem mem aw) slot.toNat 32

abbrev attesterMultiAttestInnerArrayInitStepAw
    (slot : UInt256) (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiAttestInnerArrayInitZero160Aw mem aw).toNat
      slot.toNat 32)

abbrev attesterMultiAttestInnerArrayInitDecRemaining
    (remaining : UInt256) : UInt256 :=
  remaining + UInt256.lnot (⟨0⟩ : UInt256)

theorem attester_u256_ofNat_succ_add_lnot_zero {n : Nat}
    (hn : n + 1 < UInt256.size) :
    attesterMultiAttestInnerArrayInitDecRemaining (UInt256.ofNat (n + 1)) =
      UInt256.ofNat n := by
  apply u256_inj
  have hlnot0 : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot
    decide
  have hsum : n + 1 + (UInt256.size - 1) = UInt256.size + n := by
    omega
  rw [attesterMultiAttestInnerArrayInitDecRemaining, uadd_toNat,
    ulit_toNat' (n + 1) hn, hlnot0, hsum, Nat.add_mod_left,
    ulit_toNat' n (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

structure AttesterMultiAttestInnerArrayInitState where
  slot : UInt256
  remaining : UInt256
  mem : ByteArray
  aw : UInt256

abbrev attesterMultiAttestInnerArrayInitStack
    (I : ExecutionEnv) (base len payload : UInt256)
    (a : AttesterMultiAttestInnerArrayInitState) : List UInt256 :=
  [a.slot, a.remaining, base, ⟨0⟩, len, len, payload,
    ⟨0⟩, ⟨128⟩,
    attesterFirstArrayLengthWord I, ⟨96⟩,
    attesterSecondArrayLengthWord I,
    attesterSecondArrayPayloadStartWord I,
    attesterFirstArrayLengthWord I,
    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
    ⟨118⟩, solcSelectorWord I]

abbrev attesterMultiAttestInnerArrayInitExitStack
    (I : ExecutionEnv) (base len payload : UInt256)
    (_a : AttesterMultiAttestInnerArrayInitState) : List UInt256 :=
  [⟨0⟩, base, len, len, payload,
    ⟨0⟩, ⟨128⟩,
    attesterFirstArrayLengthWord I, ⟨96⟩,
    attesterSecondArrayLengthWord I,
    attesterSecondArrayPayloadStartWord I,
    attesterFirstArrayLengthWord I,
    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
    ⟨118⟩, solcSelectorWord I]

abbrev attesterMultiAttestInnerArrayInitStepState
    (a : AttesterMultiAttestInnerArrayInitState) :
    AttesterMultiAttestInnerArrayInitState :=
  { slot := (⟨32⟩ : UInt256) + a.slot,
    remaining := attesterMultiAttestInnerArrayInitDecRemaining a.remaining,
    mem := attesterMultiAttestInnerArrayInitStepMem a.slot a.mem a.aw,
    aw := attesterMultiAttestInnerArrayInitStepAw a.slot a.mem a.aw }

abbrev attesterMultiAttestInnerArrayInitFinalMem
    (a : AttesterMultiAttestInnerArrayInitState) : ByteArray :=
  attesterMultiAttestInnerArrayInitStepMem a.slot a.mem a.aw

abbrev attesterMultiAttestInnerArrayInitFinalAw
    (a : AttesterMultiAttestInnerArrayInitState) : UInt256 :=
  attesterMultiAttestInnerArrayInitStepAw a.slot a.mem a.aw

set_option maxHeartbeats 1500000 in
theorem attesterX_multiAttestInnerArrayInitStores
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len payload remaining : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1113⟩ : UInt256)
      [slot, remaining, base, ⟨0⟩, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1162⟩ : UInt256)
      [⟨32⟩, slot, remaining, base, ⟨0⟩, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      (attesterMultiAttestInnerArrayInitStepMem slot mem aw)
      (attesterMultiAttestInnerArrayInitStepAw slot mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  let free := attesterMultiOuterArrayInitFreeWord mem aw
  let aw1 := attesterMultiOuterArrayInitAwAfterMload aw
  let bump := attesterMultiAttestInnerArrayInitFreeBumpWord mem aw
  let mem1 := attesterMultiAttestInnerArrayInitFreeMem mem aw
  let aw2 := attesterMultiAttestInnerArrayInitFreeAw mem aw
  let field32 := attesterMultiAttestInnerArrayInitField32Word mem aw
  let mem2 := attesterMultiAttestInnerArrayInitZero0Mem mem aw
  let aw3 := attesterMultiAttestInnerArrayInitZero0Aw mem aw
  let mem3 := attesterMultiAttestInnerArrayInitZero32Mem mem aw
  let aw4 := attesterMultiAttestInnerArrayInitZero32Aw mem aw
  let field64 := attesterMultiAttestInnerArrayInitField64Word mem aw
  let mem4 := attesterMultiAttestInnerArrayInitZero64Mem mem aw
  let aw5 := attesterMultiAttestInnerArrayInitZero64Aw mem aw
  let field96 := attesterMultiAttestInnerArrayInitField96Word mem aw
  let mem5 := attesterMultiAttestInnerArrayInitZero96Mem mem aw
  let aw6 := attesterMultiAttestInnerArrayInitZero96Aw mem aw
  let field128 := attesterMultiAttestInnerArrayInitField128Word mem aw
  let mem6 := attesterMultiAttestInnerArrayInitDataOffsetMem mem aw
  let aw7 := attesterMultiAttestInnerArrayInitDataOffsetAw mem aw
  let field160 := attesterMultiAttestInnerArrayInitField160Word mem aw
  let mem7 := attesterMultiAttestInnerArrayInitZero160Mem mem aw
  let aw8 := attesterMultiAttestInnerArrayInitZero160Aw mem aw
  let mem8 := attesterMultiAttestInnerArrayInitStepMem slot mem aw
  let aw9 := attesterMultiAttestInnerArrayInitStepAw slot mem aw
  have hcostMload :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          [⟨64⟩, ⟨64⟩, slot, remaining, base, ⟨0⟩,
            len, len, payload, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I, ⟨96⟩,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreFreePtr :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          [⟨64⟩, bump, free, ⟨64⟩, slot, remaining, base, ⟨0⟩,
            len, len, payload, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I, ⟨96⟩,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreZero0 :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          [free, (⟨0⟩ : UInt256), ⟨0⟩, free, ⟨64⟩,
            slot, remaining, base, ⟨0⟩, len, len, payload, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I, ⟨96⟩,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreZero32 :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack =
          [field32, (⟨0⟩ : UInt256), ⟨32⟩, ⟨0⟩, free, ⟨64⟩,
            slot, remaining, base, ⟨0⟩, len, len, payload, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I, ⟨96⟩,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw4 - Cₘ aw3 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreZero64 :
      ∀ s : State,
        s.machineState.activeWords = aw4 →
        s.machineState.stack =
          [field64, (⟨0⟩ : UInt256), ⟨0⟩, free, ⟨32⟩,
            slot, remaining, base, ⟨0⟩, len, len, payload, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I, ⟨96⟩,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw5 - Cₘ aw4 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreZero96 :
      ∀ s : State,
        s.machineState.activeWords = aw5 →
        s.machineState.stack =
          [field96, (⟨0⟩ : UInt256), ⟨96⟩, ⟨0⟩, free, ⟨32⟩,
            slot, remaining, base, ⟨0⟩, len, len, payload, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I, ⟨96⟩,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw6 - Cₘ aw5 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreDataOffset :
      ∀ s : State,
        s.machineState.activeWords = aw6 →
        s.machineState.stack =
          [field128, (⟨96⟩ : UInt256), ⟨0⟩, free, ⟨32⟩,
            slot, remaining, base, ⟨0⟩, len, len, payload, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I, ⟨96⟩,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw7 - Cₘ aw6 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreZero160 :
      ∀ s : State,
        s.machineState.activeWords = aw7 →
        s.machineState.stack =
          [field160, (⟨0⟩ : UInt256), free, ⟨32⟩,
            slot, remaining, base, ⟨0⟩, len, len, payload, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I, ⟨96⟩,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw8 - Cₘ aw7 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreSlot :
      ∀ s : State,
        s.machineState.activeWords = aw8 →
        s.machineState.stack =
          [slot, free, ⟨32⟩, slot, remaining, base, ⟨0⟩,
            len, len, payload, ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I, ⟨96⟩,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw9 - Cₘ aw8 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  exact ⟨_, _, by
    simpa [free, aw1, bump, mem1, aw2, field32, mem2, aw3, mem3, aw4,
      field64, mem4, aw5, field96, mem5, aw6, field128, mem6, aw7,
      field160, mem7, aw8, mem8, aw9] using
      evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨1113⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1114⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1116⟩, 0x80, .DUP1) (by evm_ov),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨1117⟩, 0x51, .MLOAD)
      hcostMload (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨192⟩ (by attester_decode_at v, ⟨1118⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1120⟩, 0x81, .DUP2) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1121⟩, 0x01, .ADD) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨1122⟩, 0x82, .DUP3) (by evm_ov),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨1123⟩, 0x52, .MSTORE)
      hcostStoreFreePtr (by rfl) (by rfl) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨1124⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1125⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨1126⟩, 0x82, .DUP3) (by evm_ov),
    raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3
      (by attester_decode_at v, ⟨1127⟩, 0x52, .MSTORE)
      hcostStoreZero0 (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1128⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1130⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨1131⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1132⟩, 0x01, .ADD) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨1133⟩, 0x82, .DUP3) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1134⟩, 0x90, .SWAP1) (by evm_ov),
    raw mstore (Cₘ aw4 - Cₘ aw3) mem3 aw4
      (by attester_decode_at v, ⟨1135⟩, 0x52, .MSTORE)
      hcostStoreZero32 (by rfl) (by rfl) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨1136⟩, 0x92, .SWAP3) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨1137⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1138⟩, 0x01, .ADD) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1139⟩, 0x81, .DUP2) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1140⟩, 0x90, .SWAP1) (by evm_ov),
    raw mstore (Cₘ aw5 - Cₘ aw4) mem4 aw5
      (by attester_decode_at v, ⟨1141⟩, 0x52, .MSTORE)
      hcostStoreZero64 (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨96⟩ (by attester_decode_at v, ⟨1142⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1144⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨1145⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1146⟩, 0x01, .ADD) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨1147⟩, 0x82, .DUP3) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1148⟩, 0x90, .SWAP1) (by evm_ov),
    raw mstore (Cₘ aw6 - Cₘ aw5) mem5 aw6
      (by attester_decode_at v, ⟨1149⟩, 0x52, .MSTORE)
      hcostStoreZero96 (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨128⟩ (by attester_decode_at v, ⟨1150⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨1152⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1153⟩, 0x01, .ADD) (by evm_ov),
    raw mstore (Cₘ aw7 - Cₘ aw6) mem6 aw7
      (by attester_decode_at v, ⟨1154⟩, 0x52, .MSTORE)
      hcostStoreDataOffset (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨160⟩ (by attester_decode_at v, ⟨1155⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨1157⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1158⟩, 0x01, .ADD) (by evm_ov),
    raw mstore (Cₘ aw8 - Cₘ aw7) mem7 aw8
      (by attester_decode_at v, ⟨1159⟩, 0x52, .MSTORE)
      hcostStoreZero160 (by rfl) (by rfl) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨1160⟩, 0x82, .DUP3) (by evm_ov),
    raw mstore (Cₘ aw9 - Cₘ aw8) mem8 aw9
      (by attester_decode_at v, ⟨1161⟩, 0x52, .MSTORE)
      hcostStoreSlot (by rfl) (by rfl) (by evm_ov)]⟩

theorem attesterX_multiAttestInnerArrayInitFinalIteration
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len payload : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1113⟩ : UInt256)
      [slot, (⟨1⟩ : UInt256), base, ⟨0⟩, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1181⟩ : UInt256)
      [⟨0⟩, base, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      (attesterMultiAttestInnerArrayInitStepMem slot mem aw)
      (attesterMultiAttestInnerArrayInitStepAw slot mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd1162⟩ :=
    attesterX_multiAttestInnerArrayInitStores
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (slot := slot) (base := base) (len := len) (payload := payload)
      (remaining := (⟨1⟩ : UInt256)) (mem := mem) (aw := aw)
      (k := k) (C := C) hreach
  exact ⟨_, _, by
    simpa [attesterMultiAttestInnerArrayInitDecRemaining] using
      evm_run rd1162 with [
    raw push0 (by attester_decode_at v, ⟨1162⟩, 0x5f, .PUSH0) (by evm_ov),
    raw not (by attester_decode_at v, ⟨1163⟩, 0x19, .NOT) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1164⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨1165⟩, 0x92, .SWAP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1166⟩, 0x01, .ADD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨1167⟩, 0x91, .SWAP2) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1168⟩, 0x01, .ADD) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1169⟩, 0x81, .DUP2) (by evm_ov),
    raw push2 ⟨1113⟩ (by attester_decode_at v, ⟨1170⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨1173⟩, 0x57, .JUMPI)
      (by native_decide) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1174⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨1175⟩, 0x50, .POP) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨1176⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨1177⟩, 0x50, .POP) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1178⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨1179⟩, 0x50, .POP) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨1180⟩, 0x5f, .PUSH0) (by evm_ov)]⟩

theorem attesterX_multiAttestInnerArrayInitNonFinalIteration
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len payload remaining : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hnext : attesterMultiAttestInnerArrayInitDecRemaining remaining ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1113⟩ : UInt256)
      [slot, remaining, base, ⟨0⟩, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1113⟩ : UInt256)
      [((⟨32⟩ : UInt256) + slot),
        attesterMultiAttestInnerArrayInitDecRemaining remaining,
        base, ⟨0⟩, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      (attesterMultiAttestInnerArrayInitStepMem slot mem aw)
      (attesterMultiAttestInnerArrayInitStepAw slot mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd1162⟩ :=
    attesterX_multiAttestInnerArrayInitStores
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (slot := slot) (base := base) (len := len) (payload := payload)
      (remaining := remaining) (mem := mem) (aw := aw)
      (k := k) (C := C) hreach
  exact ⟨_, _, by
    simpa [attesterMultiAttestInnerArrayInitDecRemaining] using
      evm_run rd1162 with [
    raw push0 (by attester_decode_at v, ⟨1162⟩, 0x5f, .PUSH0) (by evm_ov),
    raw not (by attester_decode_at v, ⟨1163⟩, 0x19, .NOT) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1164⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨1165⟩, 0x92, .SWAP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1166⟩, 0x01, .ADD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨1167⟩, 0x91, .SWAP2) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1168⟩, 0x01, .ADD) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1169⟩, 0x81, .DUP2) (by evm_ov),
    raw push2 ⟨1113⟩ (by attester_decode_at v, ⟨1170⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨1173⟩, 0x57, .JUMPI)
      (by simpa [attesterMultiAttestInnerArrayInitDecRemaining] using hnext)
      (attesterMultiAttestInnerArrayInitLoopJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiAttestInnerArrayInitLoop
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len payload : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hlenNe : len.toNat ≠ 0)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1113⟩ : UInt256)
      [slot, len, base, ⟨0⟩, len, len, payload,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ a' k' C',
      a'.remaining = (⟨1⟩ : UInt256) ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨1181⟩ : UInt256)
        (attesterMultiAttestInnerArrayInitExitStack I base len payload a')
        (attesterMultiAttestInnerArrayInitFinalMem a')
        (attesterMultiAttestInnerArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k' C' := by
  let Inv : Nat → AttesterMultiAttestInnerArrayInitState → Prop :=
    fun n a => a.remaining = UInt256.ofNat (n + 1) ∧ n + 1 < UInt256.size
  let stk := attesterMultiAttestInnerArrayInitStack I base len payload
  let memOf : AttesterMultiAttestInnerArrayInitState → ByteArray := fun a => a.mem
  let awOf : AttesterMultiAttestInnerArrayInitState → UInt256 := fun a => a.aw
  let exitStk := attesterMultiAttestInnerArrayInitExitStack I base len payload
  let exitMem := attesterMultiAttestInnerArrayInitFinalMem
  let exitAw := attesterMultiAttestInnerArrayInitFinalAw
  have hexit :
      ∀ a, Inv 0 a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨1113⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ k' C',
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨1181⟩ : UInt256) (exitStk a) (exitMem a) (exitAw a)
            ByteArray.empty (cA, σ) k' C' := by
    intro a hInv k C rd
    have hrem : a.remaining = (⟨1⟩ : UInt256) := by
      simpa [Inv] using hInv.1
    exact attesterX_multiAttestInnerArrayInitFinalIteration
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
      (payload := payload) (mem := a.mem) (aw := a.aw)
      (by
        simpa [stk, memOf, awOf, hrem, attesterMultiAttestInnerArrayInitStack]
          using rd)
  have hbody :
      ∀ n a, Inv (n + 1) a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨1113⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ a' k' C',
          Inv n a' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨1113⟩ : UInt256) (stk a') (memOf a') (awOf a')
            ByteArray.empty (cA, σ) k' C' := by
    intro n a hInv k C rd
    let a' := attesterMultiAttestInnerArrayInitStepState a
    have hsub :
        attesterMultiAttestInnerArrayInitDecRemaining a.remaining =
          UInt256.ofNat (n + 1) := by
      rw [hInv.1]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        attester_u256_ofNat_succ_add_lnot_zero (n := n + 1)
          (by simpa [Inv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hInv.2)
    have hnext :
        attesterMultiAttestInnerArrayInitDecRemaining a.remaining ≠ ⟨0⟩ := by
      rw [hsub]
      exact attester_u256_ofNat_pos_ne_zero
        (n := n + 1) (by omega) (by
          have hlt : n + 1 < UInt256.size := by
            have := hInv.2
            omega
          exact hlt)
    obtain ⟨k', C', rd'⟩ :=
      attesterX_multiAttestInnerArrayInitNonFinalIteration
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
        (payload := payload) (remaining := a.remaining) (mem := a.mem) (aw := a.aw)
        hnext
        (by
          simpa [stk, memOf, awOf, attesterMultiAttestInnerArrayInitStack]
            using rd)
    refine ⟨a', k', C', ?_, ?_⟩
    · constructor
      · simpa [a', attesterMultiAttestInnerArrayInitStepState] using hsub
      · have := hInv.2
        omega
    · simpa [a', stk, memOf, awOf, attesterMultiAttestInnerArrayInitStack,
        attesterMultiAttestInnerArrayInitStepState] using rd'
  let a0 : AttesterMultiAttestInnerArrayInitState :=
    { slot := slot, remaining := len, mem := mem, aw := aw }
  have hInv0 : Inv (len.toNat - 1) a0 := by
    constructor
    · have hsucc : (len.toNat - 1) + 1 = len.toNat := by omega
      simpa [a0, hsucc] using (u256_ofNat_toNat len).symm
    · have hsucc : (len.toNat - 1) + 1 = len.toNat := by omega
      rw [hsucc]
      exact len.val.isLt
  obtain ⟨a', k', C', hInvFinal, rdFinal⟩ :=
    RD.whileLoopCarryExit
      (code := patchedRuntime v) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := ByteArray.empty) (acc := (cA, σ))
      (header := (⟨1113⟩ : UInt256)) (exit := (⟨1181⟩ : UInt256))
      Inv stk memOf awOf exitStk exitMem exitAw hexit hbody
      (len.toNat - 1) a0 hInv0 k C
      (by
        simpa [a0, stk, memOf, awOf, attesterMultiAttestInnerArrayInitStack]
          using hreach)
  exact ⟨a', k', C', by simpa [Inv] using hInvFinal.1, rdFinal⟩

theorem attesterX_multiAttestFirstInnerArrayInitProgress
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (hlenNe : attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩)
    (hprogress :
      ∃ a' k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
        RD (patchedRuntime v) I g
          (initState cA gh bl σ σ₀ g A I) (⟨1113⟩ : UInt256)
          (((⟨32⟩ : UInt256) +
              attesterInnerArrayAllocFreeWord
                (attesterMultiOuterArrayInitFinalMem a')
                (attesterMultiOuterArrayInitFinalAw a')) ::
            attesterFirstInnerArrayLengthWord I ::
            attesterInnerArrayAllocFreeWord
              (attesterMultiOuterArrayInitFinalMem a')
              (attesterMultiOuterArrayInitFinalAw a') ::
            ⟨0⟩ ::
            attesterFirstInnerArrayLengthWord I ::
            attesterFirstInnerArrayLengthWord I ::
            (attesterFirstInnerArrayStartWord I + ⟨32⟩) ::
            [⟨0⟩, ⟨128⟩,
              attesterFirstArrayLengthWord I, ⟨96⟩,
              attesterSecondArrayLengthWord I,
              attesterSecondArrayPayloadStartWord I,
              attesterFirstArrayLengthWord I,
              (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
              ⟨118⟩, solcSelectorWord I])
          (attesterInnerArrayAllocMem
            (attesterFirstInnerArrayLengthWord I)
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a'))
          (attesterInnerArrayAllocAw
            (attesterFirstInnerArrayLengthWord I)
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a'))
          ByteArray.empty (cA, σ) k C) :
    ∃ a' b' k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      b'.remaining = (⟨1⟩ : UInt256) ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨1181⟩ : UInt256)
        (attesterMultiAttestInnerArrayInitExitStack I
          (attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a'))
          (attesterFirstInnerArrayLengthWord I)
          (attesterFirstInnerArrayStartWord I + ⟨32⟩)
          b')
        (attesterMultiAttestInnerArrayInitFinalMem b')
        (attesterMultiAttestInnerArrayInitFinalAw b')
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨a', k0, C0, hrem, rd0⟩ := hprogress
  have hlenNatNe : (attesterFirstInnerArrayLengthWord I).toNat ≠ 0 := by
    intro hzero
    apply hlenNe
    apply u256_inj
    simpa using hzero
  obtain ⟨b', k1, C1, hbrem, rd1⟩ :=
    attesterX_multiAttestInnerArrayInitLoop
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (slot :=
        ((⟨32⟩ : UInt256) +
          attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a')))
      (base :=
        attesterInnerArrayAllocFreeWord
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
      (len := attesterFirstInnerArrayLengthWord I)
      (payload := attesterFirstInnerArrayStartWord I + ⟨32⟩)
      (mem :=
        attesterInnerArrayAllocMem
          (attesterFirstInnerArrayLengthWord I)
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
      (aw :=
        attesterInnerArrayAllocAw
          (attesterFirstInnerArrayLengthWord I)
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
      (k := k0) (C := C0) hlenNatNe
      (by simpa using rd0)
  exact ⟨a', b', k1, C1, hrem, hbrem, rd1⟩

end Benchmarks.EAS.Attester
