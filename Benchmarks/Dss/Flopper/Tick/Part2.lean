import Benchmarks.Dss.Flopper.Tick.Part1

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper
set_option maxHeartbeats 1000000 in
theorem flopperTickX_toCheckedMulStart
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hendLt :
      (flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ I = ⟨0⟩)
    (rd4292 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tickIdWord I
    let memEnd := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memTic := twoWordHashMem id ⟨1⟩ memEnd
    let memLot := twoWordHashMem id ⟨1⟩ memTic
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4674⟩
      [flopperSlotWord (auctionLotSlot id) σ I, flopperSlotWord ⟨5⟩ σ I,
        ⟨4558⟩, tickOneWord, id, ⟨334⟩, sel]
      memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memEnd memTic memLot
  obtain ⟨_, _, rd4435⟩ := flopperTickX_toTicZeroGuard hendLt rd4292
  have hcond :
      UInt256.isZero (flopperUint48Offset20Word (auctionPackedSlot id) σ I) ≠ ⟨0⟩ := by
    rw [show flopperUint48Offset20Word (auctionPackedSlot id) σ I =
      flopperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ I from rfl, htic]
    decide
  have rd4438 := rd4435.push2 ⟨4515⟩ (by native_decide) (by evm_ov)
  have rd4515 := rd4438.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
  have rd4516 := rd4515.jumpdest (by native_decide) (by evm_ov)
  have rd4525 := rd4516.pushConst tickOneWord (width := 8) (op := .PUSH8)
    (by decide : Operation.POp.PUSH8 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4530 := evm_run rd4525 with [
    raw push2 ⟨4558⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k4531, C4531, rd4531raw⟩ := rd4530.sload (by native_decide) (by evm_ov)
  have rd4531 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4531⟩
      [flopperSlotWord ⟨5⟩ σ I, ⟨4558⟩, tickOneWord, id, ⟨334⟩, sel]
      memTic (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4531 C4531 := by
    simpa [flopperSlotWord, id] using rd4531raw
  let memKey := wordAt0Mem id memTic
  let base := solcMappingSlot ⟨1⟩ id
  have rd4537pre := evm_run rd4531 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd4538 := rd4537pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, memLot, memTic, memEnd, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd4543pre := evm_run rd4538 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd4544 := rd4543pre.mstore 0 memLot (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show ((⟨32⟩ : UInt256) + ⟨0⟩).toNat = 32 from by native_decide]
      simp [memKey, memLot, memTic, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd4549pre := evm_run rd4544 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memLot.readWithPadding 0 64))) = base := by
    simpa [base, memLot, memTic, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memTic
  have rd4550 := rd4549pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd4552pre := evm_run rd4550 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hlotSlot : (⟨1⟩ : UInt256) + base = auctionLotSlot id := by
    rw [u256_add_comm]
    simp [base, auctionLotSlot_eq, id]
  rw [hlotSlot] at rd4552pre
  obtain ⟨k4553, C4553, rd4553raw⟩ := rd4552pre.sload (by native_decide) (by evm_ov)
  have rd4554 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4554⟩
      [flopperSlotWord (auctionLotSlot id) σ I, flopperSlotWord ⟨5⟩ σ I,
        ⟨4558⟩, tickOneWord, id, ⟨334⟩, sel]
      memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4553 C4553 := by
    simpa [flopperSlotWord] using rd4553raw
  have rd4557 := rd4554.push2 ⟨4674⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd4557.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem flopperTickX_mulOverflow {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hendLt :
      (flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ I = ⟨0⟩)
    (hover :
      UInt256.size ≤ (flopperSlotWord ⟨5⟩ σ I).toNat *
        (flopperSlotWord (auctionLotSlot (tickIdWord I)) σ I).toNat)
    (rd4292 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4674⟩ := flopperTickX_toCheckedMulStart hendLt htic rd4292
  exact RD.flopperCheckedMulOverflowReverts
    (R := [tickOneWord, tickIdWord I, ⟨334⟩, sel])
    (hRlen := by simp)
    (hover := hover)
    rd4674

theorem flopperTickX_toLotStoreStart
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hendLt :
      (flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ I = ⟨0⟩)
    (hmulFit :
      (flopperSlotWord ⟨5⟩ σ I).toNat *
        (flopperSlotWord (auctionLotSlot (tickIdWord I)) σ I).toNat < UInt256.size)
    (rd4292 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tickIdWord I
    let memEnd := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memTic := twoWordHashMem id ⟨1⟩ memEnd
    let memLot := twoWordHashMem id ⟨1⟩ memTic
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4558⟩
      [flopperSlotWord ⟨5⟩ σ I * flopperSlotWord (auctionLotSlot id) σ I,
        tickOneWord, id, ⟨334⟩, sel]
      memLot (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  intro id memEnd memTic memLot
  obtain ⟨_, _, rd4674⟩ := flopperTickX_toCheckedMulStart hendLt htic rd4292
  obtain ⟨_, _, rd4558⟩ := RD.flopperCheckedMulReturns
    (R := [tickOneWord, id, ⟨334⟩, sel])
    (hRlen := by simp)
    (hret := by native_decide)
    (hfit := by simpa [id] using hmulFit)
    rd4674
  exact ⟨_, _, rd4558⟩

set_option maxHeartbeats 1000000 in
theorem flopperTickX_toCheckedAddStart
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hendLt :
      (flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ I = ⟨0⟩)
    (hmulFit :
      (flopperSlotWord ⟨5⟩ σ I).toNat *
        (flopperSlotWord (auctionLotSlot (tickIdWord I)) σ I).toNat < UInt256.size)
    (rd4292 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tickIdWord I
    let memEnd := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memTic := twoWordHashMem id ⟨1⟩ memEnd
    let memLot := twoWordHashMem id ⟨1⟩ memTic
    let memStore := twoWordHashMem id ⟨1⟩ memLot
    let σLot := tickRuntimeAfterLotMap I.codeOwner σ I
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4740⟩
      [tickRuntimeTauWord I.codeOwner σ I, UInt256.ofNat I.header.timestamp,
        ⟨4618⟩, id, ⟨334⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty (cA, σLot) k' C' := by
  intro id memEnd memTic memLot memStore σLot
  obtain ⟨_, _, rd4558⟩ := flopperTickX_toLotStoreStart hendLt htic hmulFit rd4292
  have rd4563pre := evm_run rd4558 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨4565⟩ (by native_decide) (by evm_ov)]
  have hone : tickOneWord ≠ ⟨0⟩ := by native_decide
  have rd4565 := rd4563pre.jumpiT (by native_decide) hone (by jump_dest) (by evm_ov)
  have rd4566 := rd4565.jumpdest (by native_decide) (by evm_ov)
  let lotBase := tickRuntimeLotBaseWord σ I
  let lotPost := tickRuntimeLotPostWord σ I
  let memKey := wordAt0Mem id memLot
  let base := solcMappingSlot ⟨1⟩ id
  have rd4570pre := evm_run rd4566 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd4571 := rd4570pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, memLot, memTic, memEnd, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd4577pre := evm_run rd4571 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd4578 := rd4577pre.mstore 0 memStore (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memStore, memLot, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd4582pre := evm_run rd4578 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memStore.readWithPadding 0 64))) = base := by
    simpa [base, memStore, memLot, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memLot
  have rd4583 := rd4582pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd4589pre := evm_run rd4583 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hlotSlot : base + ⟨1⟩ = auctionLotSlot id := by
    simp [base, auctionLotSlot_eq, id]
  rw [hlotSlot] at rd4589pre
  obtain ⟨k4590, C4590, rd4590raw⟩ := rd4589pre.sstore hperm
    (by native_decide) (by evm_ov)
  have rd4590 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4590⟩
      [id, ⟨334⟩, sel] memStore (UInt256.ofNat 3) ByteArray.empty
      (cA, σLot) k4590 C4590 := by
    simpa [σLot, tickRuntimeAfterLotMap, tickRuntimeLotPostWord,
      tickRuntimeLotBaseWord, lotBase, lotPost, id] using rd4590raw
  have rd4592 := rd4590.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨k4593, C4593, rd4593raw⟩ := rd4592.sload (by native_decide) (by evm_ov)
  have rd4593 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4593⟩
      [flopperSlotWord ⟨6⟩ σLot I, id, ⟨334⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty (cA, σLot) k4593 C4593 := by
    simpa [flopperSlotWord] using rd4593raw
  have rd4606 := evm_run rd4593 with [
    raw push2 ⟨4618⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw timestamp (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨48⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd4614 := rd4606.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4614' := rd4614.and (by native_decide) (by evm_ov)
  have rd4617 := rd4614'.push2 ⟨4740⟩ (by native_decide) (by evm_ov)
  have rd4740 := rd4617.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa [σLot, tickRuntimeTauWord, tickRuntimeAfterLotMap, flopperUint48Offset6Word,
      show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨48⟩ = UInt256.ofNat (256 ^ 6)
        from by native_decide]
      using rd4740⟩

set_option maxHeartbeats 1000000 in
theorem flopperTickX_toEndStoreStart
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hendLt :
      (flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ I = ⟨0⟩)
    (hmulFit :
      (flopperSlotWord ⟨5⟩ σ I).toNat *
        (flopperSlotWord (auctionLotSlot (tickIdWord I)) σ I).toNat < UInt256.size)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (tickRuntimeTauWord I.codeOwner σ I).toNat < 2 ^ 48)
    (rd4292 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    let id := tickIdWord I
    let memEnd := twoWordHashMem id ⟨1⟩ solcFreePtrMem
    let memTic := twoWordHashMem id ⟨1⟩ memEnd
    let memLot := twoWordHashMem id ⟨1⟩ memTic
    let memStore := twoWordHashMem id ⟨1⟩ memLot
    let σLot := tickRuntimeAfterLotMap I.codeOwner σ I
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4618⟩
      [tickRuntimeAddWord I.codeOwner σ I, id, ⟨334⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty (cA, σLot) k' C' := by
  intro id memEnd memTic memLot memStore σLot
  obtain ⟨_, _, rd4740⟩ :=
    flopperTickX_toCheckedAddStart hperm hendLt htic hmulFit rd4292
  let tau := tickRuntimeTauWord I.codeOwner σ I
  let timestamp := UInt256.ofNat I.header.timestamp
  let addWord := tickRuntimeAddWord I.codeOwner σ I
  have rd4744 := evm_run rd4740 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have rd4751 := rd4744.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4759 := evm_run rd4751 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨4710⟩ (by native_decide) (by evm_ov)]
  have hltFalse :
      UInt256.lt (UInt256.land (timestamp + tau) flopperUint48Mask)
          (UInt256.land timestamp flopperUint48Mask) = ⟨0⟩ := by
    simpa [timestamp, tau] using uint48AddGuard_false_of_no_wrap timestamp tau haddFit
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.land (timestamp + tau) flopperUint48Mask)
            (UInt256.land timestamp flopperUint48Mask)) ≠ ⟨0⟩ := by
    rw [hltFalse]
    decide
  have rd4710 := rd4759.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
  have rd4715 := evm_run rd4710 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd4618 := rd4715.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa [timestamp, tau, addWord, tickRuntimeAddWord] using rd4618⟩

set_option maxHeartbeats 1000000 in
theorem flopperTickX_success
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hendLt :
      (flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ I = ⟨0⟩)
    (hmulFit :
      (flopperSlotWord ⟨5⟩ σ I).toNat *
        (flopperSlotWord (auctionLotSlot (tickIdWord I)) σ I).toNat < UInt256.size)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (tickRuntimeTauWord I.codeOwner σ I).toNat < 2 ^ 48)
    (rd4292 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flopperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, tickRuntimeSuccessAccountMap I.codeOwner σ I) ByteArray.empty := by
  let id := tickIdWord I
  let memEnd := twoWordHashMem id ⟨1⟩ solcFreePtrMem
  let memTic := twoWordHashMem id ⟨1⟩ memEnd
  let memLot := twoWordHashMem id ⟨1⟩ memTic
  let memStore := twoWordHashMem id ⟨1⟩ memLot
  let memEndStore := twoWordHashMem id ⟨1⟩ memStore
  let σLot := tickRuntimeAfterLotMap I.codeOwner σ I
  let addWord := tickRuntimeAddWord I.codeOwner σ I
  let base := solcMappingSlot ⟨1⟩ id
  let packedSlot := auctionPackedSlot id
  let oldPacked := solcSlotWord σLot I packedSlot
  obtain ⟨_, _, rd4618⟩ :=
    flopperTickX_toEndStoreStart hperm hendLt htic hmulFit haddFit rd4292
  let memKey := wordAt0Mem id memStore
  have rd4623pre := evm_run rd4618 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd4624 := rd4623pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, memStore, memLot, memTic, memEnd, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd4628pre := evm_run rd4624 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd4629 := rd4628pre.mstore 0 memEndStore (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memEndStore, memStore, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd4633pre := evm_run rd4629 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memEndStore.readWithPadding 0 64))) = base := by
    simpa [base, memEndStore, memStore, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStore
  have rd4634 := rd4633pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd4636pre := evm_run rd4634 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpackedSlot : (⟨2⟩ : UInt256) + base = packedSlot := by
    rw [u256_add_comm]
    simp [packedSlot, base, auctionPackedSlot_eq, id]
  rw [hpackedSlot] at rd4636pre
  have rd4638pre := rd4636pre.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k4639, C4639, rd4639raw⟩ := rd4638pre.sload (by native_decide) (by evm_ov)
  have rd4639 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4639⟩
      [oldPacked, packedSlot, addWord, ⟨334⟩, sel]
      memEndStore (UInt256.ofNat 3) ByteArray.empty (cA, σLot) k4639 C4639 := by
    simpa [oldPacked, packedSlot, solcSlotWord, addWord] using rd4639raw
  have rd4646 := rd4639.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4672pre := evm_run rd4646 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw or (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k4673, C4673, rd4673raw⟩ := rd4672pre.sstore hperm
    (by native_decide) (by evm_ov)
  have rd334 := rd4673raw.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd335 := rd334.jumpdest (by native_decide) (by evm_ov)
  simpa [tickRuntimeSuccessAccountMap, σLot, oldPacked, packedSlot, addWord,
    tickRuntimeEndStoredRawWord, tickRuntimeEndShiftedWord, tickRuntimeEndClearMask, id]
    using RD.stop rd335 (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem flopperTickX_addOverflow
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hendLt :
      (flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ I = ⟨0⟩)
    (hmulFit :
      (flopperSlotWord ⟨5⟩ σ I).toNat *
        (flopperSlotWord (auctionLotSlot (tickIdWord I)) σ I).toNat < UInt256.size)
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (tickRuntimeTauWord I.codeOwner σ I).toNat)
    (rd4292 : ∃ k C, RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4740⟩ :=
    flopperTickX_toCheckedAddStart hperm hendLt htic hmulFit rd4292
  let tau := tickRuntimeTauWord I.codeOwner σ I
  let timestamp := UInt256.ofNat I.header.timestamp
  have rd4744 := evm_run rd4740 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have rd4751 := rd4744.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd4759 := evm_run rd4751 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨4710⟩ (by native_decide) (by evm_ov)]
  have htauLt : tau.toNat < 2 ^ 48 := by
    simpa [tau, tickRuntimeTauWord, flopperUint48Offset6Word, EVM.twoPow,
      u256_land_comm] using
      flopperUint48Masked_lt
        (UInt256.div
          (flopperSlotWord ⟨6⟩ (tickRuntimeAfterLotMap I.codeOwner σ I) I)
          (UInt256.ofNat (256 ^ 6)))
  have hltTrue :
      UInt256.lt (UInt256.land (timestamp + tau) flopperUint48Mask)
          (UInt256.land timestamp flopperUint48Mask) = ⟨1⟩ := by
    simpa [timestamp, tau] using
      uint48AddGuard_true_of_wrap timestamp tau htauLt haddOverflow
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.land (timestamp + tau) flopperUint48Mask)
            (UInt256.land timestamp flopperUint48Mask)) = ⟨0⟩ := by
    rw [hltTrue]
    native_decide
  have rd4763 := rd4759.jumpiNT (by native_decide) hcond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd4763
    (by native_decide) (by native_decide) (by native_decide)
    (by simp)

theorem tickRuntimeAfterLotMap_source_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (tickRuntimeAfterLotMap I.codeOwner σ_evm I)
      (tickAfterLotStore (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I).accountMap := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have h := tickRuntimeAfterLotMap_accountMapEquiv (owner := I.codeOwner) (I := I)
    hAccounts
  simpa [evmSolm, initState, tickAfterLotStore, storageStore_accountMap,
    tickRuntimeAfterLotMap, tickRuntimeLotPostWord, tickRuntimeLotBaseWord,
    tickLotPostWord, tickLotBaseWord, tickPadWord, tickLotWord, flopperSlotWord]
    using h

theorem tickRuntimeTauWord_source_eq
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    tickRuntimeTauWord I.codeOwner σ_evm I =
      tickTauWord
        (tickAfterLotStore
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I) := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hAfter :=
    tickRuntimeAfterLotMap_source_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts
  have h := flopperUint48Offset6Word_accountMapEquiv (I := I) hAfter ⟨6⟩
  simpa [evmSolm, tickRuntimeTauWord, tickTauWord, tickAfterLotStore_executionEnv,
    initState] using h

theorem tickRuntimeSuccessAccountMap_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (tickRuntimeTauWord I.codeOwner σ_evm I).toNat < 2 ^ 48) :
    accountMapEquiv (tickRuntimeSuccessAccountMap I.codeOwner σ_evm I)
      (tickPostState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I).accountMap := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (tickIdWord I)
  let runtimeOld := solcSlotWord (tickRuntimeAfterLotMap I.codeOwner σ_evm I) I packedSlot
  let runtimeAdd := tickRuntimeAddWord I.codeOwner σ_evm I
  have hAfter :=
    tickRuntimeAfterLotMap_source_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts
  have htau :=
    tickRuntimeTauWord_source_eq
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts
  have haddFitSolm :
      (tickNow48Word evmSolm).toNat +
          (tickTauWord (tickAfterLotStore evmSolm I)).toNat < 2 ^ 48 := by
    simpa [evmSolm, tickNow48Word, tickTimestampWord, initState, htau] using haddFit
  have hmaskedRuntime :
      UInt256.land runtimeAdd flopperUint48Mask = tickEndPostWord evmSolm I := by
    apply u256_inj
    change (UInt256.land (tickRuntimeAddWord I.codeOwner σ_evm I) flopperUint48Mask).toNat =
      (tickEndPostWord evmSolm I).toNat
    rw [tickRuntimeAddWord]
    rw [uint48Mask_add_no_wrap_toNat (UInt256.ofNat I.header.timestamp)
      (tickRuntimeTauWord I.codeOwner σ_evm I) haddFit]
    rw [tickEndPostWord_toNat evmSolm I haddFitSolm]
    simpa [evmSolm, tickNow48Word, tickTimestampWord, initState, htau]
  have hsourceClean :
      UInt256.land (tickEndPostWord evmSolm I) flopperUint48Mask =
        tickEndPostWord evmSolm I := by
    apply flopperUint48Mask_clean_of_canonical
    have hendNat := tickEndPostWord_toNat evmSolm I haddFitSolm
    rw [hendNat]
    simpa [EVM.twoPow] using haddFitSolm
  have hold :
      runtimeOld =
        Solm.EVM.storageLoad (tickAfterLotStore evmSolm I)
          (tickAfterLotStore evmSolm I).executionEnv.codeOwner packedSlot := by
    have hslot := flopperSlotWord_accountMapEquiv (I := I) hAfter packedSlot
    simpa [runtimeOld, packedSlot, flopperSlotWord, solcSlotWord, evmSolm,
      initState, tickAfterLotStore_executionEnv] using hslot
  have hstored :
      tickRuntimeEndStoredRawWord runtimeOld runtimeAdd = tickEndStoredWord evmSolm I := by
    rw [tickRuntimeEndStoredRawWord_eq_setUint48Offset26Word]
    unfold tickEndStoredWord
    apply u256_inj
    rw [setUint48Offset26Word_toNat, setUint48Offset26Word_toNat]
    rw [hold, hmaskedRuntime, hsourceClean]
  simpa [evmSolm, initState, storageStore_accountMap, tickAfterLotStore_executionEnv,
    packedSlot, runtimeOld, runtimeAdd, tickRuntimeSuccessAccountMap, tickPostState,
    hstored] using
    accountMapEquiv_sstoreAccountMap I.codeOwner packedSlot (tickEndStoredWord evmSolm I)
      hAfter

theorem flopperTickBodyCoreEndNotExpired
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hendGe :
      (UInt256.ofNat I.header.timestamp).toNat ≤
        (flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ_evm I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some tickTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tickTransition.params.map Param.name)
        (transitionSignature tickTransition).paramTypes I.calldata = some (tickLocals I))
    (rd4292 : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hendGeSolm :
      (tickTimestampWord evmSolm).toNat ≤ (tickEndWord evmSolm I).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    simpa [evmSolm, tickTimestampWord, tickEndWord, initState, hword] using hendGe
  have hbody :
      ExecTransitionBody config contract evmSolm (tickLocals I) tickTransition.body
        .reverted := by
    exact flopperTickBodyReverts_endNotExpired evmSolm I
      (by simpa [evmSolm, initState] using hwv) hendGeSolm
  exact (flopperTickX_endNotExpired (g := Sat256.ofUInt256 g) hendGe rd4292)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperTickBodyCoreTicNonzero
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hendLt :
      (flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ_evm I ≠ ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some tickTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tickTransition.params.map Param.name)
        (transitionSignature tickTransition).paramTypes I.calldata = some (tickLocals I))
    (rd4292 : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hendLtSolm :
      (tickEndWord evmSolm I).toNat < (tickTimestampWord evmSolm).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    simpa [evmSolm, tickEndWord, tickTimestampWord, initState, hword] using hendLt
  have hticSolm : tickTicWord evmSolm I ≠ ⟨0⟩ := by
    intro hzero
    apply htic
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    rw [hword]
    simpa [evmSolm, tickTicWord, initState] using hzero
  have hbody :
      ExecTransitionBody config contract evmSolm (tickLocals I) tickTransition.body
        .reverted := by
    exact flopperTickBodyReverts_ticNonzero evmSolm I
      (by simpa [evmSolm, initState] using hwv) hendLtSolm hticSolm
  exact (flopperTickX_ticNonzero (g := Sat256.ofUInt256 g) hendLt htic rd4292)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperTickBodyCoreMulOverflow
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hendLt :
      (flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ_evm I = ⟨0⟩)
    (hover :
      UInt256.size ≤ (flopperSlotWord ⟨5⟩ σ_evm I).toNat *
        (flopperSlotWord (auctionLotSlot (tickIdWord I)) σ_evm I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some tickTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tickTransition.params.map Param.name)
        (transitionSignature tickTransition).paramTypes I.calldata = some (tickLocals I))
    (rd4292 : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hendLtSolm :
      (tickEndWord evmSolm I).toNat < (tickTimestampWord evmSolm).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    simpa [evmSolm, tickEndWord, tickTimestampWord, initState, hword] using hendLt
  have hticSolm : tickTicWord evmSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    simpa [evmSolm, tickTicWord, initState, hword] using htic
  have hoverSolm :
      UInt256.size ≤ (tickPadWord evmSolm).toNat * (tickLotWord evmSolm I).toNat := by
    have hpad := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨5⟩
    have hlot := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (tickIdWord I))
    simpa [evmSolm, tickPadWord, tickLotWord, initState, hpad, hlot] using hover
  have hbody :
      ExecTransitionBody config contract evmSolm (tickLocals I) tickTransition.body
        .reverted := by
    exact flopperTickBodyReverts_mulOverflow evmSolm I
      (by simpa [evmSolm, initState] using hwv) hendLtSolm hticSolm hoverSolm
  exact (flopperTickX_mulOverflow (g := Sat256.ofUInt256 g) hendLt htic hover rd4292)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperTickBodyCoreAddOverflow
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hendLt :
      (flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ_evm I = ⟨0⟩)
    (hmulFit :
      (flopperSlotWord ⟨5⟩ σ_evm I).toNat *
        (flopperSlotWord (auctionLotSlot (tickIdWord I)) σ_evm I).toNat < UInt256.size)
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (tickRuntimeTauWord I.codeOwner σ_evm I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some tickTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tickTransition.params.map Param.name)
        (transitionSignature tickTransition).paramTypes I.calldata = some (tickLocals I))
    (rd4292 : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hendLtSolm :
      (tickEndWord evmSolm I).toNat < (tickTimestampWord evmSolm).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    simpa [evmSolm, tickEndWord, tickTimestampWord, initState, hword] using hendLt
  have hticSolm : tickTicWord evmSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    simpa [evmSolm, tickTicWord, initState, hword] using htic
  have hmulFitSolm :
      (tickPadWord evmSolm).toNat * (tickLotWord evmSolm I).toNat < UInt256.size := by
    have hpad := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨5⟩
    have hlot := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (tickIdWord I))
    simpa [evmSolm, tickPadWord, tickLotWord, initState, hpad, hlot] using hmulFit
  have htau :=
    tickRuntimeTauWord_source_eq
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts
  have haddOverflowSolm :
      2 ^ 48 ≤
        (tickNow48Word evmSolm).toNat +
          (tickTauWord (tickAfterLotStore evmSolm I)).toNat := by
    simpa [evmSolm, tickNow48Word, tickTimestampWord, initState, htau]
      using haddOverflow
  have hbody :
      ExecTransitionBody config contract evmSolm (tickLocals I) tickTransition.body
        .reverted := by
    exact flopperTickBodyReverts_addOverflow evmSolm I
      (by simpa [evmSolm, initState] using hwv) hendLtSolm hticSolm hmulFitSolm
      haddOverflowSolm
  exact (flopperTickX_addOverflow (g := Sat256.ofUInt256 g) hperm hendLt htic
      hmulFit haddOverflow rd4292)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperTickBodyCoreSuccess
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hendLt :
      (flopperUint48Offset26Word (auctionPackedSlot (tickIdWord I)) σ_evm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat)
    (htic : flopperUint48Offset20Word (auctionPackedSlot (tickIdWord I)) σ_evm I = ⟨0⟩)
    (hmulFit :
      (flopperSlotWord ⟨5⟩ σ_evm I).toNat *
        (flopperSlotWord (auctionLotSlot (tickIdWord I)) σ_evm I).toNat < UInt256.size)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (tickRuntimeTauWord I.codeOwner σ_evm I).toNat < 2 ^ 48)
    (hdispatch : dispatchMsg contract I.calldata = some tickTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tickTransition.params.map Param.name)
        (transitionSignature tickTransition).paramTypes I.calldata = some (tickLocals I))
    (rd4292 : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4292⟩
      [tickIdWord I, ⟨334⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hendLtSolm :
      (tickEndWord evmSolm I).toNat < (tickTimestampWord evmSolm).toNat := by
    have hword := flopperUint48Offset26Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    simpa [evmSolm, tickEndWord, tickTimestampWord, initState, hword] using hendLt
  have hticSolm : tickTicWord evmSolm I = ⟨0⟩ := by
    have hword := flopperUint48Offset20Word_accountMapEquiv (I := I) hAccounts
      (auctionPackedSlot (tickIdWord I))
    simpa [evmSolm, tickTicWord, initState, hword] using htic
  have hmulFitSolm :
      (tickPadWord evmSolm).toNat * (tickLotWord evmSolm I).toNat < UInt256.size := by
    have hpad := flopperSlotWord_accountMapEquiv (I := I) hAccounts ⟨5⟩
    have hlot := flopperSlotWord_accountMapEquiv (I := I) hAccounts
      (auctionLotSlot (tickIdWord I))
    simpa [evmSolm, tickPadWord, tickLotWord, initState, hpad, hlot] using hmulFit
  have htau :=
    tickRuntimeTauWord_source_eq
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts
  have haddFitSolm :
      (tickNow48Word evmSolm).toNat +
          (tickTauWord (tickAfterLotStore evmSolm I)).toNat < 2 ^ 48 := by
    simpa [evmSolm, tickNow48Word, tickTimestampWord, initState, htau] using haddFit
  have hbody :
      ExecTransitionBody config contract evmSolm (tickLocals I) tickTransition.body
        (.returned { contract := contract, locals := tickEndLocals evmSolm I }
          (tickPostState evmSolm I) none) := by
    exact flopperTickBodyReturns_success evmSolm I
      (by simpa [evmSolm, initState] using hwv) hendLtSolm hticSolm hmulFitSolm
      haddFitSolm
  have hret := flopperTickX_success (g := Sat256.ofUInt256 g) hperm hendLt htic
    hmulFit haddFit rd4292
  have hpostAccounts :=
    tickRuntimeSuccessAccountMap_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hAccounts haddFit
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by
      simp [evmSolm, tickPostState, tickAfterLotStore, initState,
        storageStore_createdAccounts])
    (by simpa [evmSolm] using hpostAccounts)
    (by
      simpa [tickTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flopperTickBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some tickTransition)
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨849⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (flopperTickX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch
      (flopperDecode_tick_none_short hsz4 hshort)

theorem flopperTickBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flopperSelBytes 14))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flopperSelBytes 14) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some tickTransition :=
    flopperDispatchTick hsel
  have hreach := flopperReachTickBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have rd4292 := flopperTickX_decoded (g := Sat256.ofUInt256 g)
      hsz36 hsize hreach
    let id := tickIdWord I
    let packedSlot := auctionPackedSlot id
    by_cases hendLt :
        (flopperUint48Offset26Word packedSlot σ_evm I).toNat <
          (UInt256.ofNat I.header.timestamp).toNat
    · by_cases htic : flopperUint48Offset20Word packedSlot σ_evm I = ⟨0⟩
      · by_cases hmulFit :
          (flopperSlotWord ⟨5⟩ σ_evm I).toNat *
            (flopperSlotWord (auctionLotSlot id) σ_evm I).toNat < UInt256.size
        · by_cases haddFit :
            (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
              (tickRuntimeTauWord I.codeOwner σ_evm I).toNat < 2 ^ 48
          · exact flopperTickBodyCoreSuccess hcode hperm hwv
              (by simpa [id, packedSlot] using hendLt)
              (by simpa [id, packedSlot] using htic)
              (by simpa [id] using hmulFit) haddFit hdispatch
              (flopperDecode_tick_ok hsz36) rd4292 hAccounts
          · exact flopperTickBodyCoreAddOverflow hcode hperm hwv
              (by simpa [id, packedSlot] using hendLt)
              (by simpa [id, packedSlot] using htic)
              (by simpa [id] using hmulFit) (Nat.le_of_not_gt haddFit) hdispatch
              (flopperDecode_tick_ok hsz36) rd4292 hAccounts
        · exact flopperTickBodyCoreMulOverflow hcode hwv
            (by simpa [id, packedSlot] using hendLt)
            (by simpa [id, packedSlot] using htic)
            (by simpa [id] using Nat.le_of_not_gt hmulFit) hdispatch
            (flopperDecode_tick_ok hsz36) rd4292 hAccounts
      · exact flopperTickBodyCoreTicNonzero hcode hwv
          (by simpa [id, packedSlot] using hendLt)
          (by simpa [id, packedSlot] using htic) hdispatch
          (flopperDecode_tick_ok hsz36) rd4292 hAccounts
    · exact flopperTickBodyCoreEndNotExpired hcode hwv
        (by simpa [id, packedSlot] using Nat.le_of_not_gt hendLt) hdispatch
        (flopperDecode_tick_ok hsz36) rd4292 hAccounts
  · exact flopperTickBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Flopper
