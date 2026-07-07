import Benchmarks.EAS.Attester.DynamicArray

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

theorem attesterX_multiRevokeOuterArrayInitFinalIteration
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨291⟩ : UInt256)
      [slot, (⟨1⟩ : UInt256), base, ⟨0⟩, len,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
      [⟨0⟩, base, len,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      (attesterMultiOuterArrayInitStepMem slot mem aw)
      (attesterMultiOuterArrayInitStepAw slot mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  let free := attesterMultiOuterArrayInitFreeWord mem aw
  let aw1 := attesterMultiOuterArrayInitAwAfterMload aw
  let mem1 := attesterMultiOuterArrayInitFreeMem mem aw
  let aw2 := attesterMultiOuterArrayInitFreeAw aw
  let mem2 := attesterMultiOuterArrayInitZeroMem mem aw
  let aw3 := attesterMultiOuterArrayInitZeroAw mem aw
  let off := attesterMultiOuterArrayInitOffsetWord mem aw
  let mem3 := attesterMultiOuterArrayInitOffsetMem mem aw
  let aw4 := attesterMultiOuterArrayInitOffsetAw mem aw
  let mem4 := attesterMultiOuterArrayInitStepMem slot mem aw
  let aw5 := attesterMultiOuterArrayInitStepAw slot mem aw
  have hcostMload :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          [⟨64⟩, ⟨64⟩, slot, (⟨1⟩ : UInt256), base, ⟨0⟩, len,
            attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len,
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
          [⟨64⟩, ((⟨64⟩ : UInt256) + free), free, slot, (⟨1⟩ : UInt256),
            base, ⟨0⟩, len, attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
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
          [free, (⟨0⟩ : UInt256), free, slot, (⟨1⟩ : UInt256),
            base, ⟨0⟩, len, attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreOff :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack =
          [off, (⟨96⟩ : UInt256), free, slot, (⟨1⟩ : UInt256),
            base, ⟨0⟩, len, attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
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
          [slot, free, slot, (⟨1⟩ : UInt256), base, ⟨0⟩, len,
            attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw5 - Cₘ aw4 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hrd314 : ∃ k314 C314, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨314⟩ : UInt256)
      [slot, (⟨1⟩ : UInt256), base, ⟨0⟩, len,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem4 aw5 ByteArray.empty (cA, σ) k314 C314 := by
    exact ⟨_, _, by
      simpa [free, aw1, mem1, aw2, mem2, aw3, off, mem3, aw4, mem4, aw5] using
        evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨291⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨292⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨294⟩, 0x80, .DUP1) (by evm_ov),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨295⟩, 0x51, .MLOAD)
      hcostMload (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨296⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨297⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨298⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨299⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨300⟩, 0x91, .SWAP2) (by evm_ov),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨301⟩, 0x52, .MSTORE)
      hcostStore64 (by rfl) (by rfl) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨302⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨303⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3
      (by attester_decode_at v, ⟨304⟩, 0x52, .MSTORE)
      hcostStoreZero (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨96⟩ (by attester_decode_at v, ⟨305⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨307⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨309⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨310⟩, 0x01, .ADD) (by evm_ov),
    raw mstore (Cₘ aw4 - Cₘ aw3) mem3 aw4
      (by attester_decode_at v, ⟨311⟩, 0x52, .MSTORE)
      hcostStoreOff (by rfl) (by rfl) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨312⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw5 - Cₘ aw4) mem4 aw5
      (by attester_decode_at v, ⟨313⟩, 0x52, .MSTORE)
      hcostStoreSlot (by rfl) (by rfl) (by evm_ov)]⟩
  obtain ⟨_, _, rd314⟩ := hrd314
  have hrd328 : ∃ k328 C328, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨328⟩ : UInt256)
      [((⟨32⟩ : UInt256) + slot), ⟨0⟩, base, ⟨0⟩, len,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem4 aw5 ByteArray.empty (cA, σ) k328 C328 := by
    exact ⟨_, _, by
      simpa using
        evm_run rd314 with [
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨314⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨316⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨317⟩, 0x90, .SWAP1) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨318⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨320⟩, 0x90, .SWAP1) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨321⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨322⟩, 0x90, .SWAP1) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨323⟩, 0x81, .DUP2) (by evm_ov),
    raw push2 ⟨291⟩ (by attester_decode_at v, ⟨324⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨327⟩, 0x57, .JUMPI)
      (by native_decide) (by evm_ov)]⟩
  obtain ⟨_, _, rd328⟩ := hrd328
  have rd335 := evm_run rd328 with [
    raw swap1 (by attester_decode_at v, ⟨328⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨329⟩, 0x50, .POP) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨330⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨331⟩, 0x50, .POP) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨332⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨333⟩, 0x50, .POP) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨334⟩, 0x5f, .PUSH0) (by evm_ov)]
  exact ⟨_, _, by
    simpa [free, aw1, mem1, aw2, mem2, aw3, off, mem3, aw4, mem4, aw5] using rd335⟩

theorem attesterX_multiRevokeOuterArrayInitNonFinalIteration
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len remaining : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hnext : UInt256.sub remaining (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨291⟩ : UInt256)
      [slot, remaining, base, ⟨0⟩, len,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨291⟩ : UInt256)
      [((⟨32⟩ : UInt256) + slot), UInt256.sub remaining ⟨1⟩, base, ⟨0⟩, len,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      (attesterMultiOuterArrayInitStepMem slot mem aw)
      (attesterMultiOuterArrayInitStepAw slot mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  let free := attesterMultiOuterArrayInitFreeWord mem aw
  let aw1 := attesterMultiOuterArrayInitAwAfterMload aw
  let mem1 := attesterMultiOuterArrayInitFreeMem mem aw
  let aw2 := attesterMultiOuterArrayInitFreeAw aw
  let mem2 := attesterMultiOuterArrayInitZeroMem mem aw
  let aw3 := attesterMultiOuterArrayInitZeroAw mem aw
  let off := attesterMultiOuterArrayInitOffsetWord mem aw
  let mem3 := attesterMultiOuterArrayInitOffsetMem mem aw
  let aw4 := attesterMultiOuterArrayInitOffsetAw mem aw
  let mem4 := attesterMultiOuterArrayInitStepMem slot mem aw
  let aw5 := attesterMultiOuterArrayInitStepAw slot mem aw
  have hcostMload :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          [⟨64⟩, ⟨64⟩, slot, remaining, base, ⟨0⟩, len,
            attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len,
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
          [⟨64⟩, ((⟨64⟩ : UInt256) + free), free, slot, remaining,
            base, ⟨0⟩, len, attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
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
          [free, (⟨0⟩ : UInt256), free, slot, remaining,
            base, ⟨0⟩, len, attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreOff :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack =
          [off, (⟨96⟩ : UInt256), free, slot, remaining,
            base, ⟨0⟩, len, attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
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
          [slot, free, slot, remaining, base, ⟨0⟩, len,
            attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw5 - Cₘ aw4 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hrd314 : ∃ k314 C314, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨314⟩ : UInt256)
      [slot, remaining, base, ⟨0⟩, len,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem4 aw5 ByteArray.empty (cA, σ) k314 C314 := by
    exact ⟨_, _, by
      simpa [free, aw1, mem1, aw2, mem2, aw3, off, mem3, aw4, mem4, aw5] using
        evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨291⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨292⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨294⟩, 0x80, .DUP1) (by evm_ov),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨295⟩, 0x51, .MLOAD)
      hcostMload (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨296⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨297⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨298⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨299⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨300⟩, 0x91, .SWAP2) (by evm_ov),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨301⟩, 0x52, .MSTORE)
      hcostStore64 (by rfl) (by rfl) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨302⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨303⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3
      (by attester_decode_at v, ⟨304⟩, 0x52, .MSTORE)
      hcostStoreZero (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨96⟩ (by attester_decode_at v, ⟨305⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨307⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨309⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨310⟩, 0x01, .ADD) (by evm_ov),
    raw mstore (Cₘ aw4 - Cₘ aw3) mem3 aw4
      (by attester_decode_at v, ⟨311⟩, 0x52, .MSTORE)
      hcostStoreOff (by rfl) (by rfl) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨312⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw5 - Cₘ aw4) mem4 aw5
      (by attester_decode_at v, ⟨313⟩, 0x52, .MSTORE)
      hcostStoreSlot (by rfl) (by rfl) (by evm_ov)]⟩
  obtain ⟨_, _, rd314⟩ := hrd314
  exact ⟨_, _, by
    simpa [free, aw1, mem1, aw2, mem2, aw3, off, mem3, aw4, mem4, aw5] using
      evm_run rd314 with [
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨314⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨316⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨317⟩, 0x90, .SWAP1) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨318⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨320⟩, 0x90, .SWAP1) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨321⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨322⟩, 0x90, .SWAP1) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨323⟩, 0x81, .DUP2) (by evm_ov),
    raw push2 ⟨291⟩ (by attester_decode_at v, ⟨324⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨327⟩, 0x57, .JUMPI)
      (by simpa using hnext)
      (attesterMultiRevokeOuterArrayInitLoopJumpdest v) (by evm_ov)]⟩

theorem attester_u256_ofNat_succ_sub_one {n : Nat}
    (hn : n + 1 < UInt256.size) :
    UInt256.sub (UInt256.ofNat (n + 1)) (⟨1⟩ : UInt256) =
      UInt256.ofNat n := by
  apply u256_inj
  rw [usub_toNat]
  · rw [ulit_toNat' (n + 1) hn]
    rw [show (⟨1⟩ : UInt256).toNat = 1 by decide]
    rw [ulit_toNat' n (by omega)]
    omega
  · rw [ulit_toNat' (n + 1) hn]
    rw [show (⟨1⟩ : UInt256).toNat = 1 by decide]
    omega

theorem attester_u256_ofNat_pos_ne_zero {n : Nat}
    (hpos : 0 < n) (hn : n < UInt256.size) :
    UInt256.ofNat n ≠ (⟨0⟩ : UInt256) := by
  intro hzero
  have hnat := congrArg UInt256.toNat hzero
  rw [ulit_toNat' n hn] at hnat
  norm_num at hnat
  omega

structure AttesterMultiOuterArrayInitState where
  slot : UInt256
  remaining : UInt256
  mem : ByteArray
  aw : UInt256

abbrev attesterMultiRevokeOuterArrayInitStack
    (I : ExecutionEnv) (base len : UInt256)
    (a : AttesterMultiOuterArrayInitState) : List UInt256 :=
  [a.slot, a.remaining, base, ⟨0⟩, len,
    attesterSecondArrayLengthWord I,
    (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
    len,
    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
    ⟨97⟩, solcSelectorWord I]

abbrev attesterMultiRevokeOuterArrayInitExitStack
    (I : ExecutionEnv) (base len : UInt256)
    (_a : AttesterMultiOuterArrayInitState) : List UInt256 :=
  [⟨0⟩, base, len,
    attesterSecondArrayLengthWord I,
    (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
    len,
    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
    ⟨97⟩, solcSelectorWord I]

abbrev attesterMultiOuterArrayInitStepState
    (a : AttesterMultiOuterArrayInitState) : AttesterMultiOuterArrayInitState :=
  { slot := (⟨32⟩ : UInt256) + a.slot,
    remaining := UInt256.sub a.remaining ⟨1⟩,
    mem := attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw,
    aw := attesterMultiOuterArrayInitStepAw a.slot a.mem a.aw }

abbrev attesterMultiOuterArrayInitFinalMem
    (a : AttesterMultiOuterArrayInitState) : ByteArray :=
  attesterMultiOuterArrayInitStepMem a.slot a.mem a.aw

abbrev attesterMultiOuterArrayInitFinalAw
    (a : AttesterMultiOuterArrayInitState) : UInt256 :=
  attesterMultiOuterArrayInitStepAw a.slot a.mem a.aw

theorem attesterX_multiRevokeOuterArrayInitLoop
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hlenNe : len.toNat ≠ 0)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨291⟩ : UInt256)
      [slot, len, base, ⟨0⟩, len,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ a' k' C',
      a'.remaining = (⟨1⟩ : UInt256) ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        (attesterMultiRevokeOuterArrayInitExitStack I base len a')
        (attesterMultiOuterArrayInitFinalMem a')
        (attesterMultiOuterArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k' C' := by
  let Inv : Nat → AttesterMultiOuterArrayInitState → Prop :=
    fun n a => a.remaining = UInt256.ofNat (n + 1) ∧ n + 1 < UInt256.size
  let stk := attesterMultiRevokeOuterArrayInitStack I base len
  let memOf : AttesterMultiOuterArrayInitState → ByteArray := fun a => a.mem
  let awOf : AttesterMultiOuterArrayInitState → UInt256 := fun a => a.aw
  let exitStk := attesterMultiRevokeOuterArrayInitExitStack I base len
  let exitMem := attesterMultiOuterArrayInitFinalMem
  let exitAw := attesterMultiOuterArrayInitFinalAw
  have hexit :
      ∀ a, Inv 0 a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨291⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ k' C',
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨335⟩ : UInt256) (exitStk a) (exitMem a) (exitAw a)
            ByteArray.empty (cA, σ) k' C' := by
    intro a hInv k C rd
    have hrem : a.remaining = (⟨1⟩ : UInt256) := by
      simpa [Inv] using hInv.1
    exact attesterX_multiRevokeOuterArrayInitFinalIteration
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
      (mem := a.mem) (aw := a.aw)
      (by
        simpa [stk, memOf, awOf, hrem, attesterMultiRevokeOuterArrayInitStack]
          using rd)
  have hbody :
      ∀ n a, Inv (n + 1) a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨291⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ a' k' C',
          Inv n a' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨291⟩ : UInt256) (stk a') (memOf a') (awOf a')
            ByteArray.empty (cA, σ) k' C' := by
    intro n a hInv k C rd
    let a' := attesterMultiOuterArrayInitStepState a
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
      attesterX_multiRevokeOuterArrayInitNonFinalIteration
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
        (remaining := a.remaining) (mem := a.mem) (aw := a.aw) hnext
        (by
          simpa [stk, memOf, awOf, attesterMultiRevokeOuterArrayInitStack]
            using rd)
    refine ⟨a', k', C', ?_, ?_⟩
    · constructor
      · simpa [a', attesterMultiOuterArrayInitStepState] using hsub
      · have := hInv.2
        omega
    · simpa [a', stk, memOf, awOf, attesterMultiRevokeOuterArrayInitStack,
        attesterMultiOuterArrayInitStepState] using rd'
  let a0 : AttesterMultiOuterArrayInitState :=
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
      (header := (⟨291⟩ : UInt256)) (exit := (⟨335⟩ : UInt256))
      Inv stk memOf awOf exitStk exitMem exitAw hexit hbody
      (len.toNat - 1) a0 hInv0 k C
      (by
        simpa [a0, stk, memOf, awOf, attesterMultiRevokeOuterArrayInitStack]
          using hreach)
  exact ⟨a', k', C', by simpa [Inv] using hInvFinal.1, rdFinal⟩


theorem attesterX_multiAttestOuterArrayInitFinalIteration
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨929⟩ : UInt256)
      [slot, (⟨1⟩ : UInt256), base, ⟨0⟩, len, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨973⟩ : UInt256)
      [⟨0⟩, base, len, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      (attesterMultiOuterArrayInitStepMem slot mem aw)
      (attesterMultiOuterArrayInitStepAw slot mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  let free := attesterMultiOuterArrayInitFreeWord mem aw
  let aw1 := attesterMultiOuterArrayInitAwAfterMload aw
  let mem1 := attesterMultiOuterArrayInitFreeMem mem aw
  let aw2 := attesterMultiOuterArrayInitFreeAw aw
  let mem2 := attesterMultiOuterArrayInitZeroMem mem aw
  let aw3 := attesterMultiOuterArrayInitZeroAw mem aw
  let off := attesterMultiOuterArrayInitOffsetWord mem aw
  let mem3 := attesterMultiOuterArrayInitOffsetMem mem aw
  let aw4 := attesterMultiOuterArrayInitOffsetAw mem aw
  let mem4 := attesterMultiOuterArrayInitStepMem slot mem aw
  let aw5 := attesterMultiOuterArrayInitStepAw slot mem aw
  have hcostMload :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          [⟨64⟩, ⟨64⟩, slot, (⟨1⟩ : UInt256), base, ⟨0⟩, len, ⟨96⟩,
            attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStore64 :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          [⟨64⟩, ((⟨64⟩ : UInt256) + free), free, slot, (⟨1⟩ : UInt256),
            base, ⟨0⟩, len, ⟨96⟩, attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreZero :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          [free, (⟨0⟩ : UInt256), free, slot, (⟨1⟩ : UInt256),
            base, ⟨0⟩, len, ⟨96⟩, attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreOff :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack =
          [off, (⟨96⟩ : UInt256), free, slot, (⟨1⟩ : UInt256),
            base, ⟨0⟩, len, ⟨96⟩, attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw4 - Cₘ aw3 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreSlot :
      ∀ s : State,
        s.machineState.activeWords = aw4 →
        s.machineState.stack =
          [slot, free, slot, (⟨1⟩ : UInt256), base, ⟨0⟩, len, ⟨96⟩,
            attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw5 - Cₘ aw4 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hrd314 : ∃ k314 C314, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨952⟩ : UInt256)
      [slot, (⟨1⟩ : UInt256), base, ⟨0⟩, len, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem4 aw5 ByteArray.empty (cA, σ) k314 C314 := by
    exact ⟨_, _, by
      simpa [free, aw1, mem1, aw2, mem2, aw3, off, mem3, aw4, mem4, aw5] using
        evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨929⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨930⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨932⟩, 0x80, .DUP1) (by evm_ov),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨933⟩, 0x51, .MLOAD)
      hcostMload (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨934⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨935⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨936⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨937⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨938⟩, 0x91, .SWAP2) (by evm_ov),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨939⟩, 0x52, .MSTORE)
      hcostStore64 (by rfl) (by rfl) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨940⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨941⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3
      (by attester_decode_at v, ⟨942⟩, 0x52, .MSTORE)
      hcostStoreZero (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨96⟩ (by attester_decode_at v, ⟨943⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨945⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨947⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨948⟩, 0x01, .ADD) (by evm_ov),
    raw mstore (Cₘ aw4 - Cₘ aw3) mem3 aw4
      (by attester_decode_at v, ⟨949⟩, 0x52, .MSTORE)
      hcostStoreOff (by rfl) (by rfl) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨950⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw5 - Cₘ aw4) mem4 aw5
      (by attester_decode_at v, ⟨951⟩, 0x52, .MSTORE)
      hcostStoreSlot (by rfl) (by rfl) (by evm_ov)]⟩
  obtain ⟨_, _, rd314⟩ := hrd314
  have hrd328 : ∃ k328 C328, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨966⟩ : UInt256)
      [((⟨32⟩ : UInt256) + slot), ⟨0⟩, base, ⟨0⟩, len, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem4 aw5 ByteArray.empty (cA, σ) k328 C328 := by
    exact ⟨_, _, by
      simpa using
        evm_run rd314 with [
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨952⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨954⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨955⟩, 0x90, .SWAP1) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨956⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨958⟩, 0x90, .SWAP1) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨959⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨960⟩, 0x90, .SWAP1) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨961⟩, 0x81, .DUP2) (by evm_ov),
    raw push2 ⟨929⟩ (by attester_decode_at v, ⟨962⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨965⟩, 0x57, .JUMPI)
      (by native_decide) (by evm_ov)]⟩
  obtain ⟨_, _, rd328⟩ := hrd328
  have rd335 := evm_run rd328 with [
    raw swap1 (by attester_decode_at v, ⟨966⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨967⟩, 0x50, .POP) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨968⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨969⟩, 0x50, .POP) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨970⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨971⟩, 0x50, .POP) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨972⟩, 0x5f, .PUSH0) (by evm_ov)]
  exact ⟨_, _, by
    simpa [free, aw1, mem1, aw2, mem2, aw3, off, mem3, aw4, mem4, aw5] using rd335⟩

theorem attesterX_multiAttestOuterArrayInitNonFinalIteration
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len remaining : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hnext : UInt256.sub remaining (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨929⟩ : UInt256)
      [slot, remaining, base, ⟨0⟩, len, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨929⟩ : UInt256)
      [((⟨32⟩ : UInt256) + slot), UInt256.sub remaining ⟨1⟩, base, ⟨0⟩, len, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      (attesterMultiOuterArrayInitStepMem slot mem aw)
      (attesterMultiOuterArrayInitStepAw slot mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  let free := attesterMultiOuterArrayInitFreeWord mem aw
  let aw1 := attesterMultiOuterArrayInitAwAfterMload aw
  let mem1 := attesterMultiOuterArrayInitFreeMem mem aw
  let aw2 := attesterMultiOuterArrayInitFreeAw aw
  let mem2 := attesterMultiOuterArrayInitZeroMem mem aw
  let aw3 := attesterMultiOuterArrayInitZeroAw mem aw
  let off := attesterMultiOuterArrayInitOffsetWord mem aw
  let mem3 := attesterMultiOuterArrayInitOffsetMem mem aw
  let aw4 := attesterMultiOuterArrayInitOffsetAw mem aw
  let mem4 := attesterMultiOuterArrayInitStepMem slot mem aw
  let aw5 := attesterMultiOuterArrayInitStepAw slot mem aw
  have hcostMload :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          [⟨64⟩, ⟨64⟩, slot, remaining, base, ⟨0⟩, len, ⟨96⟩,
            attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStore64 :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          [⟨64⟩, ((⟨64⟩ : UInt256) + free), free, slot, remaining,
            base, ⟨0⟩, len, ⟨96⟩, attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreZero :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          [free, (⟨0⟩ : UInt256), free, slot, remaining,
            base, ⟨0⟩, len, ⟨96⟩, attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreOff :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack =
          [off, (⟨96⟩ : UInt256), free, slot, remaining,
            base, ⟨0⟩, len, ⟨96⟩, attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw4 - Cₘ aw3 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreSlot :
      ∀ s : State,
        s.machineState.activeWords = aw4 →
        s.machineState.stack =
          [slot, free, slot, remaining, base, ⟨0⟩, len, ⟨96⟩,
            attesterSecondArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
            len, (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I] →
        memoryExpansionCost s .MSTORE = Cₘ aw5 - Cₘ aw4 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hrd314 : ∃ k314 C314, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨952⟩ : UInt256)
      [slot, remaining, base, ⟨0⟩, len, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem4 aw5 ByteArray.empty (cA, σ) k314 C314 := by
    exact ⟨_, _, by
      simpa [free, aw1, mem1, aw2, mem2, aw3, off, mem3, aw4, mem4, aw5] using
        evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨929⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨930⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨932⟩, 0x80, .DUP1) (by evm_ov),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨933⟩, 0x51, .MLOAD)
      hcostMload (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨934⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨935⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨936⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨937⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨938⟩, 0x91, .SWAP2) (by evm_ov),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨939⟩, 0x52, .MSTORE)
      hcostStore64 (by rfl) (by rfl) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨940⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨941⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3
      (by attester_decode_at v, ⟨942⟩, 0x52, .MSTORE)
      hcostStoreZero (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨96⟩ (by attester_decode_at v, ⟨943⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨945⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨947⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨948⟩, 0x01, .ADD) (by evm_ov),
    raw mstore (Cₘ aw4 - Cₘ aw3) mem3 aw4
      (by attester_decode_at v, ⟨949⟩, 0x52, .MSTORE)
      hcostStoreOff (by rfl) (by rfl) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨950⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw5 - Cₘ aw4) mem4 aw5
      (by attester_decode_at v, ⟨951⟩, 0x52, .MSTORE)
      hcostStoreSlot (by rfl) (by rfl) (by evm_ov)]⟩
  obtain ⟨_, _, rd314⟩ := hrd314
  exact ⟨_, _, by
    simpa [free, aw1, mem1, aw2, mem2, aw3, off, mem3, aw4, mem4, aw5] using
      evm_run rd314 with [
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨952⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨954⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨955⟩, 0x90, .SWAP1) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨956⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨958⟩, 0x90, .SWAP1) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨959⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨960⟩, 0x90, .SWAP1) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨961⟩, 0x81, .DUP2) (by evm_ov),
    raw push2 ⟨929⟩ (by attester_decode_at v, ⟨962⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨965⟩, 0x57, .JUMPI)
      (by simpa using hnext)
      (attesterMultiAttestOuterArrayInitLoopJumpdest v) (by evm_ov)]⟩
abbrev attesterMultiAttestOuterArrayInitStack
    (I : ExecutionEnv) (base len : UInt256)
    (a : AttesterMultiOuterArrayInitState) : List UInt256 :=
  [a.slot, a.remaining, base, ⟨0⟩, len, ⟨96⟩,
    attesterSecondArrayLengthWord I,
    (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
    len,
    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
    ⟨118⟩, solcSelectorWord I]

abbrev attesterMultiAttestOuterArrayInitExitStack
    (I : ExecutionEnv) (base len : UInt256)
    (_a : AttesterMultiOuterArrayInitState) : List UInt256 :=
  [⟨0⟩, base, len, ⟨96⟩,
    attesterSecondArrayLengthWord I,
    (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
    len,
    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
    ⟨118⟩, solcSelectorWord I]
theorem attesterX_multiAttestOuterArrayInitLoop
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hlenNe : len.toNat ≠ 0)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨929⟩ : UInt256)
      [slot, len, base, ⟨0⟩, len, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ a' k' C',
      a'.remaining = (⟨1⟩ : UInt256) ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨973⟩ : UInt256)
        (attesterMultiAttestOuterArrayInitExitStack I base len a')
        (attesterMultiOuterArrayInitFinalMem a')
        (attesterMultiOuterArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k' C' := by
  let Inv : Nat → AttesterMultiOuterArrayInitState → Prop :=
    fun n a => a.remaining = UInt256.ofNat (n + 1) ∧ n + 1 < UInt256.size
  let stk := attesterMultiAttestOuterArrayInitStack I base len
  let memOf : AttesterMultiOuterArrayInitState → ByteArray := fun a => a.mem
  let awOf : AttesterMultiOuterArrayInitState → UInt256 := fun a => a.aw
  let exitStk := attesterMultiAttestOuterArrayInitExitStack I base len
  let exitMem := attesterMultiOuterArrayInitFinalMem
  let exitAw := attesterMultiOuterArrayInitFinalAw
  have hexit :
      ∀ a, Inv 0 a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨929⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ k' C',
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨973⟩ : UInt256) (exitStk a) (exitMem a) (exitAw a)
            ByteArray.empty (cA, σ) k' C' := by
    intro a hInv k C rd
    have hrem : a.remaining = (⟨1⟩ : UInt256) := by
      simpa [Inv] using hInv.1
    exact attesterX_multiAttestOuterArrayInitFinalIteration
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
      (mem := a.mem) (aw := a.aw)
      (by
        simpa [stk, memOf, awOf, hrem, attesterMultiAttestOuterArrayInitStack]
          using rd)
  have hbody :
      ∀ n a, Inv (n + 1) a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨929⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ a' k' C',
          Inv n a' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨929⟩ : UInt256) (stk a') (memOf a') (awOf a')
            ByteArray.empty (cA, σ) k' C' := by
    intro n a hInv k C rd
    let a' := attesterMultiOuterArrayInitStepState a
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
      attesterX_multiAttestOuterArrayInitNonFinalIteration
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
        (remaining := a.remaining) (mem := a.mem) (aw := a.aw) hnext
        (by
          simpa [stk, memOf, awOf, attesterMultiAttestOuterArrayInitStack]
            using rd)
    refine ⟨a', k', C', ?_, ?_⟩
    · constructor
      · simpa [a', attesterMultiOuterArrayInitStepState] using hsub
      · have := hInv.2
        omega
    · simpa [a', stk, memOf, awOf, attesterMultiAttestOuterArrayInitStack,
        attesterMultiOuterArrayInitStepState] using rd'
  let a0 : AttesterMultiOuterArrayInitState :=
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
      (header := (⟨929⟩ : UInt256)) (exit := (⟨973⟩ : UInt256))
      Inv stk memOf awOf exitStk exitMem exitAw hexit hbody
      (len.toNat - 1) a0 hInv0 k C
      (by
        simpa [a0, stk, memOf, awOf, attesterMultiAttestOuterArrayInitStack]
          using hreach)
  exact ⟨a', k', C', by simpa [Inv] using hInvFinal.1, rdFinal⟩

theorem attesterX_multiRevokeOuterSourceLoopFirstGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base len : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hlenNe : len.toNat ≠ 0)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
      [⟨0⟩, base, len,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨344⟩ : UInt256)
      [⟨0⟩, base, len,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  have hlt : UInt256.lt (⟨0⟩ : UInt256) len = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
    omega
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨335⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨336⟩, 0x82, .DUP3) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨337⟩, 0x81, .DUP2) (by evm_ov),
    raw lt (by attester_decode_at v, ⟨338⟩, 0x10, .LT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨339⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨698⟩ (by attester_decode_at v, ⟨340⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨343⟩, 0x57, .JUMPI)
      (by rw [hlt]; decide) (by evm_ov)]⟩

theorem attesterX_multiAttestOuterSourceLoopFirstGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base len : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hlenNe : len.toNat ≠ 0)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨973⟩ : UInt256)
      [⟨0⟩, base, len, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨982⟩ : UInt256)
      [⟨0⟩, base, len, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  have hlt : UInt256.lt (⟨0⟩ : UInt256) len = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
    omega
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨973⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨974⟩, 0x82, .DUP3) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨975⟩, 0x81, .DUP2) (by evm_ov),
    raw lt (by attester_decode_at v, ⟨976⟩, 0x10, .LT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨977⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨1441⟩ (by attester_decode_at v, ⟨978⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨981⟩, 0x57, .JUMPI)
      (by rw [hlt]; decide) (by evm_ov)]⟩

theorem attesterX_multiRevokeOuterSecondArrayAccessCheck
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base len : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hsecondLenNe : (attesterSecondArrayLengthWord I).toNat ≠ 0)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨344⟩ : UInt256)
      [⟨0⟩, base, len,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨355⟩ : UInt256)
      [⟨363⟩, ⟨1⟩, ⟨0⟩, attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, base, len,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  have hlt :
      UInt256.lt (⟨0⟩ : UInt256) (attesterSecondArrayLengthWord I) = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
    omega
  exact ⟨_, _, by
    simpa [hlt] using
      (evm_run hreach with [
        raw calldatasize (by attester_decode_at v, ⟨344⟩, 0x36, .CALLDATASIZE) (by evm_ov),
        raw push0 (by attester_decode_at v, ⟨345⟩, 0x5f, .PUSH0) (by evm_ov),
        raw dup7 (by attester_decode_at v, ⟨346⟩, 0x86, .DUP7) (by evm_ov),
        raw dup7 (by attester_decode_at v, ⟨347⟩, 0x86, .DUP7) (by evm_ov),
        raw dup5 (by attester_decode_at v, ⟨348⟩, 0x84, .DUP5) (by evm_ov),
        raw dup2 (by attester_decode_at v, ⟨349⟩, 0x81, .DUP2) (by evm_ov),
        raw dup2 (by attester_decode_at v, ⟨350⟩, 0x81, .DUP2) (by evm_ov),
        raw lt (by attester_decode_at v, ⟨351⟩, 0x10, .LT) (by evm_ov),
        raw push2 ⟨363⟩ (by attester_decode_at v, ⟨352⟩, 0x61, (.Push .PUSH2))
          (by evm_ov)])⟩

theorem attesterMultiRevokeOuterSourceElementOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨363⟩ : UInt256) = true := by
  let A := attesterBytecode.extract 0 722
  let B := (patchedRuntime v).extract 722 (patchedRuntime v).size
  have hprefix : (patchedRuntime v).extract 0 722 = A := by
    unfold A
    rw [patchedRuntime_extract_preserved_len v 0 722
      (by simp [runtimeWrites, WindowDisjointFromWrites])
      (by norm_num)
      (by norm_num)
      (by norm_num)]
  have hsplit : patchedRuntime v = A ++ B := by
    unfold B
    have h := ByteArray.extract_append_extract (a := patchedRuntime v)
      (i := 0) (j := 722) (k := (patchedRuntime v).size)
    rw [← hprefix]
    have hsize : 722 ≤ (patchedRuntime v).size := by
      rw [patchedRuntime_size v]
      norm_num
    have hmax : max 722 (patchedRuntime v).size = (patchedRuntime v).size :=
      Nat.max_eq_right hsize
    have hmin : min 0 722 = 0 := by omega
    simpa [hmin, hmax, ByteArray.extract_zero_size] using h.symm
  rw [hsplit]
  apply Reasoning.Theory.D_J_contains_append_left
  unfold A
  native_decide

theorem attesterX_multiRevokeOuterSecondArrayAccessOk
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base len : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hsecondLenNe : (attesterSecondArrayLengthWord I).toNat ≠ 0)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨344⟩ : UInt256)
      [⟨0⟩, base, len,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨363⟩ : UInt256)
      [⟨0⟩, attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, base, len,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd0⟩ :=
    attesterX_multiRevokeOuterSecondArrayAccessCheck
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := base) (len := len) (mem := mem) (aw := aw)
      (k := k) (C := C) hsecondLenNe hreach
  exact ⟨_, _, evm_run rd0 with [
    raw jumpiT (by attester_decode_at v, ⟨355⟩, 0x57, .JUMPI)
      (by decide) (attesterMultiRevokeOuterSourceElementOkJumpdest v)
      (by evm_ov)]⟩

syntax "attester_dj_parse_at " term "," term : tactic
macro_rules
  | `(tactic| attester_dj_parse_at $varg, $pc) =>
      `(tactic|
        (rw [patchedRuntime_get?_preserved $varg ($pc : Nat)
            (by norm_num [runtimeWrites, WindowDisjointFromWrites])
            (by norm_num)];
          native_decide))

syntax "attester_dj_step " term "," term "," term : tactic
macro_rules
  | `(tactic| attester_dj_step $varg, $pc, $instr) =>
      `(tactic|
        (rw [D_J_aux_eq_some (patchedRuntime $varg) $pc _ $instr
            (by attester_dj_parse_at $varg, $pc)];
          simp [EVM.N, argOnNBytesOfInstr]))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem attesterMultiAttestOuterSourceElementOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨1001⟩ : UInt256) = true := by
  unfold D_J
  attester_dj_step v, 0, (.Push .PUSH1)
  attester_dj_step v, 2, (.Push .PUSH1)
  attester_dj_step v, 4, .MSTORE
  attester_dj_step v, 5, .CALLVALUE
  attester_dj_step v, 6, .DUP1
  attester_dj_step v, 7, .ISZERO
  attester_dj_step v, 8, (.Push .PUSH2)
  attester_dj_step v, 11, .JUMPI
  attester_dj_step v, 12, (.Push .PUSH0)
  attester_dj_step v, 13, .DUP1
  attester_dj_step v, 14, .REVERT
  attester_dj_step v, 15, .JUMPDEST
  attester_dj_step v, 16, .POP
  attester_dj_step v, 17, (.Push .PUSH1)
  attester_dj_step v, 19, .CALLDATASIZE
  attester_dj_step v, 20, .LT
  attester_dj_step v, 21, (.Push .PUSH2)
  attester_dj_step v, 24, .JUMPI
  attester_dj_step v, 25, (.Push .PUSH0)
  attester_dj_step v, 26, .CALLDATALOAD
  attester_dj_step v, 27, (.Push .PUSH1)
  attester_dj_step v, 29, .SHR
  attester_dj_step v, 30, .DUP1
  attester_dj_step v, 31, (.Push .PUSH4)
  attester_dj_step v, 36, .EQ
  attester_dj_step v, 37, (.Push .PUSH2)
  attester_dj_step v, 40, .JUMPI
  attester_dj_step v, 41, .DUP1
  attester_dj_step v, 42, (.Push .PUSH4)
  attester_dj_step v, 47, .EQ
  attester_dj_step v, 48, (.Push .PUSH2)
  attester_dj_step v, 51, .JUMPI
  attester_dj_step v, 52, .DUP1
  attester_dj_step v, 53, (.Push .PUSH4)
  attester_dj_step v, 58, .EQ
  attester_dj_step v, 59, (.Push .PUSH2)
  attester_dj_step v, 62, .JUMPI
  attester_dj_step v, 63, .DUP1
  attester_dj_step v, 64, (.Push .PUSH4)
  attester_dj_step v, 69, .EQ
  attester_dj_step v, 70, (.Push .PUSH2)
  attester_dj_step v, 73, .JUMPI
  attester_dj_step v, 74, .JUMPDEST
  attester_dj_step v, 75, (.Push .PUSH0)
  attester_dj_step v, 76, .DUP1
  attester_dj_step v, 77, .REVERT
  attester_dj_step v, 78, .JUMPDEST
  attester_dj_step v, 79, (.Push .PUSH2)
  attester_dj_step v, 82, (.Push .PUSH2)
  attester_dj_step v, 85, .CALLDATASIZE
  attester_dj_step v, 86, (.Push .PUSH1)
  attester_dj_step v, 88, (.Push .PUSH2)
  attester_dj_step v, 91, .JUMP
  attester_dj_step v, 92, .JUMPDEST
  attester_dj_step v, 93, (.Push .PUSH2)
  attester_dj_step v, 96, .JUMP
  attester_dj_step v, 97, .JUMPDEST
  attester_dj_step v, 98, .STOP
  attester_dj_step v, 99, .JUMPDEST
  attester_dj_step v, 100, (.Push .PUSH2)
  attester_dj_step v, 103, (.Push .PUSH2)
  attester_dj_step v, 106, .CALLDATASIZE
  attester_dj_step v, 107, (.Push .PUSH1)
  attester_dj_step v, 109, (.Push .PUSH2)
  attester_dj_step v, 112, .JUMP
  attester_dj_step v, 113, .JUMPDEST
  attester_dj_step v, 114, (.Push .PUSH2)
  attester_dj_step v, 117, .JUMP
  attester_dj_step v, 118, .JUMPDEST
  attester_dj_step v, 119, (.Push .PUSH1)
  attester_dj_step v, 121, .MLOAD
  attester_dj_step v, 122, (.Push .PUSH2)
  attester_dj_step v, 125, .SWAP2
  attester_dj_step v, 126, .SWAP1
  attester_dj_step v, 127, (.Push .PUSH2)
  attester_dj_step v, 130, .JUMP
  attester_dj_step v, 131, .JUMPDEST
  attester_dj_step v, 132, (.Push .PUSH1)
  attester_dj_step v, 134, .MLOAD
  attester_dj_step v, 135, .DUP1
  attester_dj_step v, 136, .SWAP2
  attester_dj_step v, 137, .SUB
  attester_dj_step v, 138, .SWAP1
  attester_dj_step v, 139, .RETURN
  attester_dj_step v, 140, .JUMPDEST
  attester_dj_step v, 141, (.Push .PUSH2)
  attester_dj_step v, 144, (.Push .PUSH2)
  attester_dj_step v, 147, .CALLDATASIZE
  attester_dj_step v, 148, (.Push .PUSH1)
  attester_dj_step v, 150, (.Push .PUSH2)
  attester_dj_step v, 153, .JUMP
  attester_dj_step v, 154, .JUMPDEST
  attester_dj_step v, 155, (.Push .PUSH2)
  attester_dj_step v, 158, .JUMP
  attester_dj_step v, 159, .JUMPDEST
  attester_dj_step v, 160, (.Push .PUSH1)
  attester_dj_step v, 162, .MLOAD
  attester_dj_step v, 163, .SWAP1
  attester_dj_step v, 164, .DUP2
  attester_dj_step v, 165, .MSTORE
  attester_dj_step v, 166, (.Push .PUSH1)
  attester_dj_step v, 168, .ADD
  attester_dj_step v, 169, (.Push .PUSH2)
  attester_dj_step v, 172, .JUMP
  attester_dj_step v, 173, .JUMPDEST
  attester_dj_step v, 174, (.Push .PUSH2)
  attester_dj_step v, 177, (.Push .PUSH2)
  attester_dj_step v, 180, .CALLDATASIZE
  attester_dj_step v, 181, (.Push .PUSH1)
  attester_dj_step v, 183, (.Push .PUSH2)
  attester_dj_step v, 186, .JUMP
  attester_dj_step v, 187, .JUMPDEST
  attester_dj_step v, 188, (.Push .PUSH2)
  attester_dj_step v, 191, .JUMP
  attester_dj_step v, 192, .JUMPDEST
  attester_dj_step v, 193, .DUP3
  attester_dj_step v, 194, .DUP1
  attester_dj_step v, 195, .ISZERO
  attester_dj_step v, 196, .DUP1
  attester_dj_step v, 197, (.Push .PUSH2)
  attester_dj_step v, 200, .JUMPI
  attester_dj_step v, 201, .POP
  attester_dj_step v, 202, .DUP1
  attester_dj_step v, 203, .DUP3
  attester_dj_step v, 204, .EQ
  attester_dj_step v, 205, .ISZERO
  attester_dj_step v, 206, .JUMPDEST
  attester_dj_step v, 207, .ISZERO
  attester_dj_step v, 208, (.Push .PUSH2)
  attester_dj_step v, 211, .JUMPI
  attester_dj_step v, 212, (.Push .PUSH1)
  attester_dj_step v, 214, .MLOAD
  attester_dj_step v, 215, (.Push .PUSH4)
  attester_dj_step v, 220, (.Push .PUSH1)
  attester_dj_step v, 222, .SHL
  attester_dj_step v, 223, .DUP2
  attester_dj_step v, 224, .MSTORE
  attester_dj_step v, 225, (.Push .PUSH1)
  attester_dj_step v, 227, .ADD
  attester_dj_step v, 228, (.Push .PUSH1)
  attester_dj_step v, 230, .MLOAD
  attester_dj_step v, 231, .DUP1
  attester_dj_step v, 232, .SWAP2
  attester_dj_step v, 233, .SUB
  attester_dj_step v, 234, .SWAP1
  attester_dj_step v, 235, .REVERT
  attester_dj_step v, 236, .JUMPDEST
  attester_dj_step v, 237, (.Push .PUSH0)
  attester_dj_step v, 238, .DUP2
  attester_dj_step v, 239, (.Push .PUSH1)
  attester_dj_step v, 241, (.Push .PUSH1)
  attester_dj_step v, 243, (.Push .PUSH1)
  attester_dj_step v, 245, .SHL
  attester_dj_step v, 246, .SUB
  attester_dj_step v, 247, .DUP2
  attester_dj_step v, 248, .GT
  attester_dj_step v, 249, .ISZERO
  attester_dj_step v, 250, (.Push .PUSH2)
  attester_dj_step v, 253, .JUMPI
  attester_dj_step v, 254, (.Push .PUSH2)
  attester_dj_step v, 257, (.Push .PUSH2)
  attester_dj_step v, 260, .JUMP
  attester_dj_step v, 261, .JUMPDEST
  attester_dj_step v, 262, (.Push .PUSH1)
  attester_dj_step v, 264, .MLOAD
  attester_dj_step v, 265, .SWAP1
  attester_dj_step v, 266, .DUP1
  attester_dj_step v, 267, .DUP3
  attester_dj_step v, 268, .MSTORE
  attester_dj_step v, 269, .DUP1
  attester_dj_step v, 270, (.Push .PUSH1)
  attester_dj_step v, 272, .MUL
  attester_dj_step v, 273, (.Push .PUSH1)
  attester_dj_step v, 275, .ADD
  attester_dj_step v, 276, .DUP3
  attester_dj_step v, 277, .ADD
  attester_dj_step v, 278, (.Push .PUSH1)
  attester_dj_step v, 280, .MSTORE
  attester_dj_step v, 281, .DUP1
  attester_dj_step v, 282, .ISZERO
  attester_dj_step v, 283, (.Push .PUSH2)
  attester_dj_step v, 286, .JUMPI
  attester_dj_step v, 287, .DUP2
  attester_dj_step v, 288, (.Push .PUSH1)
  attester_dj_step v, 290, .ADD
  attester_dj_step v, 291, .JUMPDEST
  attester_dj_step v, 292, (.Push .PUSH1)
  attester_dj_step v, 294, .DUP1
  attester_dj_step v, 295, .MLOAD
  attester_dj_step v, 296, .DUP1
  attester_dj_step v, 297, .DUP3
  attester_dj_step v, 298, .ADD
  attester_dj_step v, 299, .SWAP1
  attester_dj_step v, 300, .SWAP2
  attester_dj_step v, 301, .MSTORE
  attester_dj_step v, 302, (.Push .PUSH0)
  attester_dj_step v, 303, .DUP2
  attester_dj_step v, 304, .MSTORE
  attester_dj_step v, 305, (.Push .PUSH1)
  attester_dj_step v, 307, (.Push .PUSH1)
  attester_dj_step v, 309, .DUP3
  attester_dj_step v, 310, .ADD
  attester_dj_step v, 311, .MSTORE
  attester_dj_step v, 312, .DUP2
  attester_dj_step v, 313, .MSTORE
  attester_dj_step v, 314, (.Push .PUSH1)
  attester_dj_step v, 316, .ADD
  attester_dj_step v, 317, .SWAP1
  attester_dj_step v, 318, (.Push .PUSH1)
  attester_dj_step v, 320, .SWAP1
  attester_dj_step v, 321, .SUB
  attester_dj_step v, 322, .SWAP1
  attester_dj_step v, 323, .DUP2
  attester_dj_step v, 324, (.Push .PUSH2)
  attester_dj_step v, 327, .JUMPI
  attester_dj_step v, 328, .SWAP1
  attester_dj_step v, 329, .POP
  attester_dj_step v, 330, .JUMPDEST
  attester_dj_step v, 331, .POP
  attester_dj_step v, 332, .SWAP1
  attester_dj_step v, 333, .POP
  attester_dj_step v, 334, (.Push .PUSH0)
  attester_dj_step v, 335, .JUMPDEST
  attester_dj_step v, 336, .DUP3
  attester_dj_step v, 337, .DUP2
  attester_dj_step v, 338, .LT
  attester_dj_step v, 339, .ISZERO
  attester_dj_step v, 340, (.Push .PUSH2)
  attester_dj_step v, 343, .JUMPI
  attester_dj_step v, 344, .CALLDATASIZE
  attester_dj_step v, 345, (.Push .PUSH0)
  attester_dj_step v, 346, .DUP7
  attester_dj_step v, 347, .DUP7
  attester_dj_step v, 348, .DUP5
  attester_dj_step v, 349, .DUP2
  attester_dj_step v, 350, .DUP2
  attester_dj_step v, 351, .LT
  attester_dj_step v, 352, (.Push .PUSH2)
  attester_dj_step v, 355, .JUMPI
  attester_dj_step v, 356, (.Push .PUSH2)
  attester_dj_step v, 359, (.Push .PUSH2)
  attester_dj_step v, 362, .JUMP
  attester_dj_step v, 363, .JUMPDEST
  attester_dj_step v, 364, .SWAP1
  attester_dj_step v, 365, .POP
  attester_dj_step v, 366, (.Push .PUSH1)
  attester_dj_step v, 368, .MUL
  attester_dj_step v, 369, .DUP2
  attester_dj_step v, 370, .ADD
  attester_dj_step v, 371, .SWAP1
  attester_dj_step v, 372, (.Push .PUSH2)
  attester_dj_step v, 375, .SWAP2
  attester_dj_step v, 376, .SWAP1
  attester_dj_step v, 377, (.Push .PUSH2)
  attester_dj_step v, 380, .JUMP
  attester_dj_step v, 381, .JUMPDEST
  attester_dj_step v, 382, .SWAP1
  attester_dj_step v, 383, .SWAP3
  attester_dj_step v, 384, .POP
  attester_dj_step v, 385, .SWAP1
  attester_dj_step v, 386, .POP
  attester_dj_step v, 387, .DUP1
  attester_dj_step v, 388, (.Push .PUSH0)
  attester_dj_step v, 389, .DUP2
  attester_dj_step v, 390, .SWAP1
  attester_dj_step v, 391, .SUB
  attester_dj_step v, 392, (.Push .PUSH2)
  attester_dj_step v, 395, .JUMPI
  attester_dj_step v, 396, (.Push .PUSH1)
  attester_dj_step v, 398, .MLOAD
  attester_dj_step v, 399, (.Push .PUSH4)
  attester_dj_step v, 404, (.Push .PUSH1)
  attester_dj_step v, 406, .SHL
  attester_dj_step v, 407, .DUP2
  attester_dj_step v, 408, .MSTORE
  attester_dj_step v, 409, (.Push .PUSH1)
  attester_dj_step v, 411, .ADD
  attester_dj_step v, 412, (.Push .PUSH1)
  attester_dj_step v, 414, .MLOAD
  attester_dj_step v, 415, .DUP1
  attester_dj_step v, 416, .SWAP2
  attester_dj_step v, 417, .SUB
  attester_dj_step v, 418, .SWAP1
  attester_dj_step v, 419, .REVERT
  attester_dj_step v, 420, .JUMPDEST
  attester_dj_step v, 421, (.Push .PUSH0)
  attester_dj_step v, 422, .DUP2
  attester_dj_step v, 423, (.Push .PUSH1)
  attester_dj_step v, 425, (.Push .PUSH1)
  attester_dj_step v, 427, (.Push .PUSH1)
  attester_dj_step v, 429, .SHL
  attester_dj_step v, 430, .SUB
  attester_dj_step v, 431, .DUP2
  attester_dj_step v, 432, .GT
  attester_dj_step v, 433, .ISZERO
  attester_dj_step v, 434, (.Push .PUSH2)
  attester_dj_step v, 437, .JUMPI
  attester_dj_step v, 438, (.Push .PUSH2)
  attester_dj_step v, 441, (.Push .PUSH2)
  attester_dj_step v, 444, .JUMP
  attester_dj_step v, 445, .JUMPDEST
  attester_dj_step v, 446, (.Push .PUSH1)
  attester_dj_step v, 448, .MLOAD
  attester_dj_step v, 449, .SWAP1
  attester_dj_step v, 450, .DUP1
  attester_dj_step v, 451, .DUP3
  attester_dj_step v, 452, .MSTORE
  attester_dj_step v, 453, .DUP1
  attester_dj_step v, 454, (.Push .PUSH1)
  attester_dj_step v, 456, .MUL
  attester_dj_step v, 457, (.Push .PUSH1)
  attester_dj_step v, 459, .ADD
  attester_dj_step v, 460, .DUP3
  attester_dj_step v, 461, .ADD
  attester_dj_step v, 462, (.Push .PUSH1)
  attester_dj_step v, 464, .MSTORE
  attester_dj_step v, 465, .DUP1
  attester_dj_step v, 466, .ISZERO
  attester_dj_step v, 467, (.Push .PUSH2)
  attester_dj_step v, 470, .JUMPI
  attester_dj_step v, 471, .DUP2
  attester_dj_step v, 472, (.Push .PUSH1)
  attester_dj_step v, 474, .ADD
  attester_dj_step v, 475, .JUMPDEST
  attester_dj_step v, 476, (.Push .PUSH1)
  attester_dj_step v, 478, .DUP1
  attester_dj_step v, 479, .MLOAD
  attester_dj_step v, 480, .DUP1
  attester_dj_step v, 481, .DUP3
  attester_dj_step v, 482, .ADD
  attester_dj_step v, 483, .SWAP1
  attester_dj_step v, 484, .SWAP2
  attester_dj_step v, 485, .MSTORE
  attester_dj_step v, 486, (.Push .PUSH0)
  attester_dj_step v, 487, .DUP1
  attester_dj_step v, 488, .DUP3
  attester_dj_step v, 489, .MSTORE
  attester_dj_step v, 490, (.Push .PUSH1)
  attester_dj_step v, 492, .DUP3
  attester_dj_step v, 493, .ADD
  attester_dj_step v, 494, .MSTORE
  attester_dj_step v, 495, .DUP2
  attester_dj_step v, 496, .MSTORE
  attester_dj_step v, 497, (.Push .PUSH1)
  attester_dj_step v, 499, .ADD
  attester_dj_step v, 500, .SWAP1
  attester_dj_step v, 501, (.Push .PUSH1)
  attester_dj_step v, 503, .SWAP1
  attester_dj_step v, 504, .SUB
  attester_dj_step v, 505, .SWAP1
  attester_dj_step v, 506, .DUP2
  attester_dj_step v, 507, (.Push .PUSH2)
  attester_dj_step v, 510, .JUMPI
  attester_dj_step v, 511, .SWAP1
  attester_dj_step v, 512, .POP
  attester_dj_step v, 513, .JUMPDEST
  attester_dj_step v, 514, .POP
  attester_dj_step v, 515, .SWAP1
  attester_dj_step v, 516, .POP
  attester_dj_step v, 517, (.Push .PUSH0)
  attester_dj_step v, 518, .JUMPDEST
  attester_dj_step v, 519, .DUP3
  attester_dj_step v, 520, .DUP2
  attester_dj_step v, 521, .LT
  attester_dj_step v, 522, .ISZERO
  attester_dj_step v, 523, (.Push .PUSH2)
  attester_dj_step v, 526, .JUMPI
  attester_dj_step v, 527, (.Push .PUSH1)
  attester_dj_step v, 529, .MLOAD
  attester_dj_step v, 530, .DUP1
  attester_dj_step v, 531, (.Push .PUSH1)
  attester_dj_step v, 533, .ADD
  attester_dj_step v, 534, (.Push .PUSH1)
  attester_dj_step v, 536, .MSTORE
  attester_dj_step v, 537, .DUP1
  attester_dj_step v, 538, .DUP7
  attester_dj_step v, 539, .DUP7
  attester_dj_step v, 540, .DUP5
  attester_dj_step v, 541, .DUP2
  attester_dj_step v, 542, .DUP2
  attester_dj_step v, 543, .LT
  attester_dj_step v, 544, (.Push .PUSH2)
  attester_dj_step v, 547, .JUMPI
  attester_dj_step v, 548, (.Push .PUSH2)
  attester_dj_step v, 551, (.Push .PUSH2)
  attester_dj_step v, 554, .JUMP
  attester_dj_step v, 555, .JUMPDEST
  attester_dj_step v, 556, .SWAP1
  attester_dj_step v, 557, .POP
  attester_dj_step v, 558, (.Push .PUSH1)
  attester_dj_step v, 560, .MUL
  attester_dj_step v, 561, .ADD
  attester_dj_step v, 562, .CALLDATALOAD
  attester_dj_step v, 563, .DUP2
  attester_dj_step v, 564, .MSTORE
  attester_dj_step v, 565, (.Push .PUSH1)
  attester_dj_step v, 567, .ADD
  attester_dj_step v, 568, (.Push .PUSH0)
  attester_dj_step v, 569, .DUP2
  attester_dj_step v, 570, .MSTORE
  attester_dj_step v, 571, .POP
  attester_dj_step v, 572, .DUP3
  attester_dj_step v, 573, .DUP3
  attester_dj_step v, 574, .DUP2
  attester_dj_step v, 575, .MLOAD
  attester_dj_step v, 576, .DUP2
  attester_dj_step v, 577, .LT
  attester_dj_step v, 578, (.Push .PUSH2)
  attester_dj_step v, 581, .JUMPI
  attester_dj_step v, 582, (.Push .PUSH2)
  attester_dj_step v, 585, (.Push .PUSH2)
  attester_dj_step v, 588, .JUMP
  attester_dj_step v, 589, .JUMPDEST
  attester_dj_step v, 590, (.Push .PUSH1)
  attester_dj_step v, 592, .SWAP1
  attester_dj_step v, 593, .DUP2
  attester_dj_step v, 594, .MUL
  attester_dj_step v, 595, .SWAP2
  attester_dj_step v, 596, .SWAP1
  attester_dj_step v, 597, .SWAP2
  attester_dj_step v, 598, .ADD
  attester_dj_step v, 599, .ADD
  attester_dj_step v, 600, .MSTORE
  attester_dj_step v, 601, (.Push .PUSH1)
  attester_dj_step v, 603, .ADD
  attester_dj_step v, 604, (.Push .PUSH2)
  attester_dj_step v, 607, .JUMP
  attester_dj_step v, 608, .JUMPDEST
  attester_dj_step v, 609, .POP
  attester_dj_step v, 610, (.Push .PUSH1)
  attester_dj_step v, 612, .MLOAD
  attester_dj_step v, 613, .DUP1
  attester_dj_step v, 614, (.Push .PUSH1)
  attester_dj_step v, 616, .ADD
  attester_dj_step v, 617, (.Push .PUSH1)
  attester_dj_step v, 619, .MSTORE
  attester_dj_step v, 620, .DUP1
  attester_dj_step v, 621, .DUP13
  attester_dj_step v, 622, .DUP13
  attester_dj_step v, 623, .DUP9
  attester_dj_step v, 624, .DUP2
  attester_dj_step v, 625, .DUP2
  attester_dj_step v, 626, .LT
  attester_dj_step v, 627, (.Push .PUSH2)
  attester_dj_step v, 630, .JUMPI
  attester_dj_step v, 631, (.Push .PUSH2)
  attester_dj_step v, 634, (.Push .PUSH2)
  attester_dj_step v, 637, .JUMP
  attester_dj_step v, 638, .JUMPDEST
  attester_dj_step v, 639, .SWAP1
  attester_dj_step v, 640, .POP
  attester_dj_step v, 641, (.Push .PUSH1)
  attester_dj_step v, 643, .MUL
  attester_dj_step v, 644, .ADD
  attester_dj_step v, 645, .CALLDATALOAD
  attester_dj_step v, 646, .DUP2
  attester_dj_step v, 647, .MSTORE
  attester_dj_step v, 648, (.Push .PUSH1)
  attester_dj_step v, 650, .ADD
  attester_dj_step v, 651, .DUP3
  attester_dj_step v, 652, .DUP2
  attester_dj_step v, 653, .MSTORE
  attester_dj_step v, 654, .POP
  attester_dj_step v, 655, .DUP7
  attester_dj_step v, 656, .DUP7
  attester_dj_step v, 657, .DUP2
  attester_dj_step v, 658, .MLOAD
  attester_dj_step v, 659, .DUP2
  attester_dj_step v, 660, .LT
  attester_dj_step v, 661, (.Push .PUSH2)
  attester_dj_step v, 664, .JUMPI
  attester_dj_step v, 665, (.Push .PUSH2)
  attester_dj_step v, 668, (.Push .PUSH2)
  attester_dj_step v, 671, .JUMP
  attester_dj_step v, 672, .JUMPDEST
  attester_dj_step v, 673, (.Push .PUSH1)
  attester_dj_step v, 675, .MUL
  attester_dj_step v, 676, (.Push .PUSH1)
  attester_dj_step v, 678, .ADD
  attester_dj_step v, 679, .ADD
  attester_dj_step v, 680, .DUP2
  attester_dj_step v, 681, .SWAP1
  attester_dj_step v, 682, .MSTORE
  attester_dj_step v, 683, .POP
  attester_dj_step v, 684, .POP
  attester_dj_step v, 685, .POP
  attester_dj_step v, 686, .POP
  attester_dj_step v, 687, .POP
  attester_dj_step v, 688, .DUP1
  attester_dj_step v, 689, (.Push .PUSH1)
  attester_dj_step v, 691, .ADD
  attester_dj_step v, 692, .SWAP1
  attester_dj_step v, 693, .POP
  attester_dj_step v, 694, (.Push .PUSH2)
  attester_dj_step v, 697, .JUMP
  attester_dj_step v, 698, .JUMPDEST
  attester_dj_step v, 699, .POP
  attester_dj_step v, 700, (.Push .PUSH1)
  attester_dj_step v, 702, .MLOAD
  attester_dj_step v, 703, (.Push .PUSH4)
  attester_dj_step v, 708, (.Push .PUSH1)
  attester_dj_step v, 710, .SHL
  attester_dj_step v, 711, .DUP2
  attester_dj_step v, 712, .MSTORE
  attester_dj_step v, 713, (.Push .PUSH1)
  attester_dj_step v, 715, (.Push .PUSH1)
  attester_dj_step v, 717, (.Push .PUSH1)
  attester_dj_step v, 719, .SHL
  attester_dj_step v, 720, .SUB
  attester_dj_step v, 721, (.Push .PUSH32)
  attester_dj_step v, 754, .AND
  attester_dj_step v, 755, .SWAP1
  attester_dj_step v, 756, (.Push .PUSH4)
  attester_dj_step v, 761, .SWAP1
  attester_dj_step v, 762, (.Push .PUSH2)
  attester_dj_step v, 765, .SWAP1
  attester_dj_step v, 766, .DUP5
  attester_dj_step v, 767, .SWAP1
  attester_dj_step v, 768, (.Push .PUSH1)
  attester_dj_step v, 770, .ADD
  attester_dj_step v, 771, (.Push .PUSH2)
  attester_dj_step v, 774, .JUMP
  attester_dj_step v, 775, .JUMPDEST
  attester_dj_step v, 776, (.Push .PUSH0)
  attester_dj_step v, 777, (.Push .PUSH1)
  attester_dj_step v, 779, .MLOAD
  attester_dj_step v, 780, .DUP1
  attester_dj_step v, 781, .DUP4
  attester_dj_step v, 782, .SUB
  attester_dj_step v, 783, .DUP2
  attester_dj_step v, 784, (.Push .PUSH0)
  attester_dj_step v, 785, .DUP8
  attester_dj_step v, 786, .DUP1
  attester_dj_step v, 787, .EXTCODESIZE
  attester_dj_step v, 788, .ISZERO
  attester_dj_step v, 789, .DUP1
  attester_dj_step v, 790, .ISZERO
  attester_dj_step v, 791, (.Push .PUSH2)
  attester_dj_step v, 794, .JUMPI
  attester_dj_step v, 795, (.Push .PUSH0)
  attester_dj_step v, 796, .DUP1
  attester_dj_step v, 797, .REVERT
  attester_dj_step v, 798, .JUMPDEST
  attester_dj_step v, 799, .POP
  attester_dj_step v, 800, .GAS
  attester_dj_step v, 801, .CALL
  attester_dj_step v, 802, .ISZERO
  attester_dj_step v, 803, .DUP1
  attester_dj_step v, 804, .ISZERO
  attester_dj_step v, 805, (.Push .PUSH2)
  attester_dj_step v, 808, .JUMPI
  attester_dj_step v, 809, .RETURNDATASIZE
  attester_dj_step v, 810, (.Push .PUSH0)
  attester_dj_step v, 811, .DUP1
  attester_dj_step v, 812, .RETURNDATACOPY
  attester_dj_step v, 813, .RETURNDATASIZE
  attester_dj_step v, 814, (.Push .PUSH0)
  attester_dj_step v, 815, .REVERT
  attester_dj_step v, 816, .JUMPDEST
  attester_dj_step v, 817, .POP
  attester_dj_step v, 818, .POP
  attester_dj_step v, 819, .POP
  attester_dj_step v, 820, .POP
  attester_dj_step v, 821, .POP
  attester_dj_step v, 822, .POP
  attester_dj_step v, 823, .POP
  attester_dj_step v, 824, .POP
  attester_dj_step v, 825, .POP
  attester_dj_step v, 826, .POP
  attester_dj_step v, 827, .JUMP
  attester_dj_step v, 828, .JUMPDEST
  attester_dj_step v, 829, (.Push .PUSH1)
  attester_dj_step v, 831, .DUP4
  attester_dj_step v, 832, .DUP1
  attester_dj_step v, 833, .ISZERO
  attester_dj_step v, 834, .DUP1
  attester_dj_step v, 835, (.Push .PUSH2)
  attester_dj_step v, 838, .JUMPI
  attester_dj_step v, 839, .POP
  attester_dj_step v, 840, .DUP1
  attester_dj_step v, 841, .DUP4
  attester_dj_step v, 842, .EQ
  attester_dj_step v, 843, .ISZERO
  attester_dj_step v, 844, .JUMPDEST
  attester_dj_step v, 845, .ISZERO
  attester_dj_step v, 846, (.Push .PUSH2)
  attester_dj_step v, 849, .JUMPI
  attester_dj_step v, 850, (.Push .PUSH1)
  attester_dj_step v, 852, .MLOAD
  attester_dj_step v, 853, (.Push .PUSH4)
  attester_dj_step v, 858, (.Push .PUSH1)
  attester_dj_step v, 860, .SHL
  attester_dj_step v, 861, .DUP2
  attester_dj_step v, 862, .MSTORE
  attester_dj_step v, 863, (.Push .PUSH1)
  attester_dj_step v, 865, .ADD
  attester_dj_step v, 866, (.Push .PUSH1)
  attester_dj_step v, 868, .MLOAD
  attester_dj_step v, 869, .DUP1
  attester_dj_step v, 870, .SWAP2
  attester_dj_step v, 871, .SUB
  attester_dj_step v, 872, .SWAP1
  attester_dj_step v, 873, .REVERT
  attester_dj_step v, 874, .JUMPDEST
  attester_dj_step v, 875, (.Push .PUSH0)
  attester_dj_step v, 876, .DUP2
  attester_dj_step v, 877, (.Push .PUSH1)
  attester_dj_step v, 879, (.Push .PUSH1)
  attester_dj_step v, 881, (.Push .PUSH1)
  attester_dj_step v, 883, .SHL
  attester_dj_step v, 884, .SUB
  attester_dj_step v, 885, .DUP2
  attester_dj_step v, 886, .GT
  attester_dj_step v, 887, .ISZERO
  attester_dj_step v, 888, (.Push .PUSH2)
  attester_dj_step v, 891, .JUMPI
  attester_dj_step v, 892, (.Push .PUSH2)
  attester_dj_step v, 895, (.Push .PUSH2)
  attester_dj_step v, 898, .JUMP
  attester_dj_step v, 899, .JUMPDEST
  attester_dj_step v, 900, (.Push .PUSH1)
  attester_dj_step v, 902, .MLOAD
  attester_dj_step v, 903, .SWAP1
  attester_dj_step v, 904, .DUP1
  attester_dj_step v, 905, .DUP3
  attester_dj_step v, 906, .MSTORE
  attester_dj_step v, 907, .DUP1
  attester_dj_step v, 908, (.Push .PUSH1)
  attester_dj_step v, 910, .MUL
  attester_dj_step v, 911, (.Push .PUSH1)
  attester_dj_step v, 913, .ADD
  attester_dj_step v, 914, .DUP3
  attester_dj_step v, 915, .ADD
  attester_dj_step v, 916, (.Push .PUSH1)
  attester_dj_step v, 918, .MSTORE
  attester_dj_step v, 919, .DUP1
  attester_dj_step v, 920, .ISZERO
  attester_dj_step v, 921, (.Push .PUSH2)
  attester_dj_step v, 924, .JUMPI
  attester_dj_step v, 925, .DUP2
  attester_dj_step v, 926, (.Push .PUSH1)
  attester_dj_step v, 928, .ADD
  attester_dj_step v, 929, .JUMPDEST
  attester_dj_step v, 930, (.Push .PUSH1)
  attester_dj_step v, 932, .DUP1
  attester_dj_step v, 933, .MLOAD
  attester_dj_step v, 934, .DUP1
  attester_dj_step v, 935, .DUP3
  attester_dj_step v, 936, .ADD
  attester_dj_step v, 937, .SWAP1
  attester_dj_step v, 938, .SWAP2
  attester_dj_step v, 939, .MSTORE
  attester_dj_step v, 940, (.Push .PUSH0)
  attester_dj_step v, 941, .DUP2
  attester_dj_step v, 942, .MSTORE
  attester_dj_step v, 943, (.Push .PUSH1)
  attester_dj_step v, 945, (.Push .PUSH1)
  attester_dj_step v, 947, .DUP3
  attester_dj_step v, 948, .ADD
  attester_dj_step v, 949, .MSTORE
  attester_dj_step v, 950, .DUP2
  attester_dj_step v, 951, .MSTORE
  attester_dj_step v, 952, (.Push .PUSH1)
  attester_dj_step v, 954, .ADD
  attester_dj_step v, 955, .SWAP1
  attester_dj_step v, 956, (.Push .PUSH1)
  attester_dj_step v, 958, .SWAP1
  attester_dj_step v, 959, .SUB
  attester_dj_step v, 960, .SWAP1
  attester_dj_step v, 961, .DUP2
  attester_dj_step v, 962, (.Push .PUSH2)
  attester_dj_step v, 965, .JUMPI
  attester_dj_step v, 966, .SWAP1
  attester_dj_step v, 967, .POP
  attester_dj_step v, 968, .JUMPDEST
  attester_dj_step v, 969, .POP
  attester_dj_step v, 970, .SWAP1
  attester_dj_step v, 971, .POP
  attester_dj_step v, 972, (.Push .PUSH0)
  attester_dj_step v, 973, .JUMPDEST
  attester_dj_step v, 974, .DUP3
  attester_dj_step v, 975, .DUP2
  attester_dj_step v, 976, .LT
  attester_dj_step v, 977, .ISZERO
  attester_dj_step v, 978, (.Push .PUSH2)
  attester_dj_step v, 981, .JUMPI
  attester_dj_step v, 982, .CALLDATASIZE
  attester_dj_step v, 983, (.Push .PUSH0)
  attester_dj_step v, 984, .DUP8
  attester_dj_step v, 985, .DUP8
  attester_dj_step v, 986, .DUP5
  attester_dj_step v, 987, .DUP2
  attester_dj_step v, 988, .DUP2
  attester_dj_step v, 989, .LT
  attester_dj_step v, 990, (.Push .PUSH2)
  attester_dj_step v, 993, .JUMPI
  attester_dj_step v, 994, (.Push .PUSH2)
  attester_dj_step v, 997, (.Push .PUSH2)
  attester_dj_step v, 1000, .JUMP
  attester_dj_step v, 1001, .JUMPDEST
  rw [Reasoning.Theory.D_J_aux_acc (patchedRuntime v) 1002]
  rw [Array.mem_append]
  apply Or.inl
  native_decide

theorem attesterX_multiAttestOuterSecondArrayAccessCheck
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base len : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hsecondLenNe : (attesterSecondArrayLengthWord I).toNat ≠ 0)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨982⟩ : UInt256)
      [⟨0⟩, base, len, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨993⟩ : UInt256)
      [⟨1001⟩, ⟨1⟩, ⟨0⟩, attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, base, len, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  have hlt :
      UInt256.lt (⟨0⟩ : UInt256) (attesterSecondArrayLengthWord I) = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
    omega
  exact ⟨_, _, by
    simpa [hlt] using
      (evm_run hreach with [
        raw calldatasize (by attester_decode_at v, ⟨982⟩, 0x36, .CALLDATASIZE) (by evm_ov),
        raw push0 (by attester_decode_at v, ⟨983⟩, 0x5f, .PUSH0) (by evm_ov),
        raw dup8 (by attester_decode_at v, ⟨984⟩, 0x87, .DUP8) (by evm_ov),
        raw dup8 (by attester_decode_at v, ⟨985⟩, 0x87, .DUP8) (by evm_ov),
        raw dup5 (by attester_decode_at v, ⟨986⟩, 0x84, .DUP5) (by evm_ov),
        raw dup2 (by attester_decode_at v, ⟨987⟩, 0x81, .DUP2) (by evm_ov),
        raw dup2 (by attester_decode_at v, ⟨988⟩, 0x81, .DUP2) (by evm_ov),
        raw lt (by attester_decode_at v, ⟨989⟩, 0x10, .LT) (by evm_ov),
        raw push2 ⟨1001⟩ (by attester_decode_at v, ⟨990⟩, 0x61, (.Push .PUSH2))
          (by evm_ov)])⟩

theorem attesterX_multiAttestOuterSecondArrayAccessOk
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base len : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hsecondLenNe : (attesterSecondArrayLengthWord I).toNat ≠ 0)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨982⟩ : UInt256)
      [⟨0⟩, base, len, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1001⟩ : UInt256)
      [⟨0⟩, attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, base, len, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        len,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd0⟩ :=
    attesterX_multiAttestOuterSecondArrayAccessCheck
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := base) (len := len) (mem := mem) (aw := aw)
      (k := k) (C := C) hsecondLenNe hreach
  exact ⟨_, _, evm_run rd0 with [
    raw jumpiT (by attester_decode_at v, ⟨993⟩, 0x57, .JUMPI)
      (by decide) (attesterMultiAttestOuterSourceElementOkJumpdest v)
      (by evm_ov)]⟩

end Benchmarks.EAS.Attester
