import Benchmarks.Dss.Flopper.Dent.Part5

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

namespace Benchmarks.Dss.Flopper
set_option maxHeartbeats 1000000 in
theorem flopperDentX_moveSuccessTicZeroToAshExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hticZero :
      flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I = ⟨0⟩)
    (rd2545 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2545⟩
      (⟨1⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
        flopperAddressReturnWord ⟨2⟩ σ I :: dentBidWord I :: dentLotWord I ::
        dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C) :
    let id := dentIdWord I
    let packedSlot := auctionPackedSlot id
    let target := flopperAddressReturnWord packedSlot σ' I
    ∃ (memAshSelector : ByteArray) (k' C' : ℕ),
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2674⟩
        (target :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨4⟩ :: ⟨128⟩ :: ⟨32⟩ ::
          ⟨132⟩ :: dentAshSelectorWord :: target :: ⟨0⟩ :: dentBidWord I ::
          dentLotWord I :: id :: ⟨334⟩ :: sel :: [])
        memAshSelector (UInt256.ofNat 8) out (cA', σ') k' C' ∧
      memAshSelector.readWithPadding dentAshOutPtr.toNat dentAshInSize.toNat =
        AshSelector ∧
      128 ≤ memAshSelector.size ∧
      memAshSelector.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  intro id packedSlot target
  let memTicKey := wordAt0Mem id mem
  let memTic := twoWordHashMem id ⟨1⟩ mem
  let memAshKey := wordAt0Mem id memTic
  let memAsh := twoWordHashMem id ⟨1⟩ memTic
  let memAshSelector := dentAshSelectorMem memAsh
  let base := solcMappingSlot ⟨1⟩ id
  let oldPacked := solcSlotWord σ' I packedSlot
  have hmemTic : memTic.size = mem.size := by
    simpa [memTic, id] using twoWordHashMem_size_of_ge_64 id ⟨1⟩ (by omega : 64 ≤ mem.size)
  have hread64Tic :
      memTic.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memTic, id] using twoWordHashMem_read64_of_ge_96 id ⟨1⟩ hmem hread64
  have hmemAsh : memAsh.size = mem.size := by
    calc
      memAsh.size = memTic.size := by
        simpa [memAsh, id] using
          twoWordHashMem_size_of_ge_64 id ⟨1⟩ (by rw [hmemTic]; omega : 64 ≤ memTic.size)
      _ = mem.size := hmemTic
  have hread64Ash :
      memAsh.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memAsh, id] using
      twoWordHashMem_read64_of_ge_96 id ⟨1⟩ (by rw [hmemTic]; exact hmem) hread64Tic
  have hread64AshSelector :
      memAshSelector.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memAshSelector] using
      dentAshSelectorMem_read64 (by rw [hmemAsh]; exact hmem) hread64Ash
  have hmemAshSelector160 : 160 ≤ memAshSelector.size := by
    unfold memAshSelector dentAshSelectorMem
    simpa [show (128 : ℕ) + 32 = 160 from rfl] using
      toByteArray_write_size_ge_off_add32 dentAshSelectorShifted memAsh 128
        (by
          have hle : 128 - memAsh.size ≤ 32 := by rw [hmemAsh]; omega
          exact lt_of_le_of_lt hle (by native_decide : 32 < USize.size))
  have hmload64Ash :
      (if (⟨64⟩ : UInt256).toNat ≥ memAsh.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memAsh.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemAsh]; omega) (by decide) hread64Ash
  have hmload64AshSelector :
      (if (⟨64⟩ : UInt256).toNat ≥ memAshSelector.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (memAshSelector.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (lt_of_lt_of_le (by decide : 64 < 160) hmemAshSelector160)
      (by decide) hread64AshSelector
  obtain ⟨_, _, rd2563⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨2545⟩) (okPc := ⟨2561⟩) rd2545
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2565 := evm_run rd2563 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd2569pre := evm_run rd2565 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2570 := rd2569pre.mstore 0 memTicKey (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memTicKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2574pre := evm_run rd2570 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2575 := rd2574pre.mstore 0 memTic (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memTicKey, memTic, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2578pre := evm_run rd2575 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbaseTic :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memTic.readWithPadding 0 64))) = base := by
    simpa [base, memTic, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id mem
  have rd2579pre := rd2578pre.keccak256 0 base (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbaseTic)
    (by native_decide)
    (by evm_ov)
  have rd2582pre := evm_run rd2579pre with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = packedSlot := by
    rw [u256_add_comm]
    simp [packedSlot, base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd2582pre
  obtain ⟨k2583, C2583, rd2583raw⟩ := rd2582pre.sload (by native_decide) (by evm_ov)
  have rd2583 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2583⟩
      [oldPacked, flopperAddressReturnWord ⟨2⟩ σ I, dentBidWord I, dentLotWord I,
        id, ⟨334⟩, sel]
      memTic (UInt256.ofNat 8) out (cA', σ') k2583 C2583 := by
    simpa [oldPacked, packedSlot, solcSlotWord] using rd2583raw
  have rd2602pre := evm_run rd2583 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov)]
  have rd2598 := rd2602pre.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd2602 := evm_run rd2598 with [
    raw and (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have hticRaw :
      UInt256.land flopperUint48Mask
          (UInt256.div oldPacked (UInt256.ofNat (256 ^ 20))) =
        flopperUint48Offset20Word packedSlot σ' I := by
    rfl
  have hcond :
      UInt256.isZero
          (UInt256.isZero
            (UInt256.land flopperUint48Mask
              (UInt256.div oldPacked (UInt256.ofNat (256 ^ 20))))) =
        ⟨0⟩ := by
    rw [hticRaw, hticZero]
    decide
  have rd2605 := rd2602.push2 ⟨2855⟩ (by native_decide) (by evm_ov)
  have rd2606 := rd2605.jumpiNT (by native_decide) hcond (by evm_ov)
  have rd2609pre := evm_run rd2606 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2610 := rd2609pre.mstore 0 memAshKey (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memAshKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2617pre := evm_run rd2610 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2618 := rd2617pre.mstore 0 memAsh (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memAshKey, memAsh, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2622pre := evm_run rd2618 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have hbaseAsh :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memAsh.readWithPadding 0 64))) = base := by
    simpa [base, memAsh, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memTic
  have rd2623pre := rd2622pre.keccak256 0 base (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbaseAsh)
    (by native_decide)
    (by evm_ov)
  have rd2626pre := evm_run rd2623pre with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [hpacked] at rd2626pre
  obtain ⟨k2627, C2627, rd2627raw⟩ := rd2626pre.sload (by native_decide) (by evm_ov)
  have rd2627 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2627⟩
      [oldPacked, ⟨64⟩, ⟨32⟩, ⟨0⟩, dentBidWord I, dentLotWord I,
        id, ⟨334⟩, sel]
      memAsh (UInt256.ofNat 8) out (cA', σ') k2627 C2627 := by
    simpa [oldPacked, packedSlot, solcSlotWord] using rd2627raw
  have rd2637pre := evm_run rd2627 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Ash (by decide) (by evm_ov),
    raw push4 dentAshSelectorSeedWord (by native_decide) (by evm_ov),
    raw push1 ⟨226⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2639 := rd2637pre.mstore 0 memAshSelector (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      simp [memAshSelector, dentAshSelectorMem, dentAshSelectorShifted,
        show (⟨128⟩ : UInt256).toNat = 128 from by decide])
    (by native_decide)
    (by evm_ov)
  have hpc2639 :
      (⟨2627⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨2639⟩ := by
    native_decide
  rw [hpc2639] at rd2639
  have rd2674pre := evm_run rd2639 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64AshSelector (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 dentAshSelectorWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hpc2674 :
      (⟨2639⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ =
        ⟨2674⟩ := by
    native_decide
  rw [hpc2674] at rd2674pre
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by
    native_decide
  exact ⟨memAshSelector, _, _, by
    simpa [target, oldPacked, packedSlot, flopperAddressReturnWord, flopperSlotWord,
      solcSlotWord, dentAshSelectorWord, hmask, u256_land_comm,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide,
      show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ from by native_decide,
      show (⟨0⟩ : UInt256) + ⟨4⟩ = ⟨4⟩ from by native_decide,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by native_decide,
      show (⟨4⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨4⟩
        from by native_decide]
      using rd2674pre, by
    simpa [memAshSelector, dentAshOutPtr, dentAshInSize] using
      dentAshSelectorMem_read128_4 (by rw [hmemAsh]; exact hmem), by
    exact le_trans (by decide : 128 ≤ 160) hmemAshSelector160, hread64AshSelector⟩

theorem flopperDentX_moveSuccessTicZeroAshNoCode
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hticZero :
      flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I = ⟨0⟩)
    (hashNoCode :
      Reasoning.Theory.extCodeSizeWord σ'
        (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I) = ⟨0⟩)
    (rd2545 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2545⟩
      (⟨1⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
        flopperAddressReturnWord ⟨2⟩ σ I :: dentBidWord I :: dentLotWord I ::
        dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd2674, _hashCalldata, _hmem128, _hread64⟩ :=
    flopperDentX_moveSuccessTicZeroToAshExtcodesizeGuard
      (g := g) hmem hread64 hticZero rd2545
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2674⟩) (okPc := ⟨2686⟩) rd2674
    hashNoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem flopperDentX_ashCallFailure
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {target : UInt256} {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd2690 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2690⟩
      (⟨0⟩ :: dentAshEndPtr :: dentAshSelectorWord :: target :: ⟨0⟩ ::
        dentBidWord I :: dentLotWord I :: dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem aw out (cA', σ') k C)
    (houtSize : out.size < UInt256.size) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2690⟩) (okPc := ⟨2706⟩) rd2690
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtSize (by simp)

theorem flopperDentX_moveSuccessTicZeroAshCall
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem outMove : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hticZero :
      flopperUint48Offset20Word (auctionPackedSlot (dentIdWord I)) σ' I = ⟨0⟩)
    (hashCodeSize :
      Reasoning.Theory.extCodeSizeWord σ'
        (flopperAddressReturnWord (auctionPackedSlot (dentIdWord I)) σ' I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd2545 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2545⟩
      (⟨1⟩ :: dentMoveEndPtr :: dentMoveSelectorWord ::
        flopperAddressReturnWord ⟨2⟩ σ I :: dentBidWord I :: dentLotWord I ::
        dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outMove (cA', σ') k C) :
    let id := dentIdWord I
    let packedSlot := auctionPackedSlot id
    let target := flopperAddressReturnWord packedSlot σ' I
    ∃ (memAshSelector : ByteArray) (cAAsh : Batteries.RBSet AccountAddress compare)
      (σAsh : AccountMap) (z : Bool) (outAsh : ByteArray) (Ain AAsh : Substate)
      (k' C' : ℕ),
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2690⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: dentAshEndPtr :: dentAshSelectorWord ::
          target :: ⟨0⟩ :: dentBidWord I :: dentLotWord I :: id :: ⟨334⟩ :: sel :: [])
        (outAsh.write 0 memAshSelector dentAshOutPtr.toNat
          (min dentAshOutSize (UInt256.ofNat outAsh.size)).toNat)
        (UInt256.ofNat 8) outAsh (cAAsh, σAsh) k' C' ∧
      typedCallViaEVM config
        { initState cA gh bl σ σ₀ g A I with
            accountMap := σ', substate := Ain, createdAccounts := cA' }
        (EVM.address (AccountAddress.ofNat target.toNat)) "Ash" 0 []
        (z,
          { initState cA gh bl σ σ₀ g A I with
              accountMap := σAsh, substate := AAsh, createdAccounts := cAAsh },
          outAsh) true ∧
      outAsh.size < UInt256.size ∧
      64 <
        (outAsh.write 0 memAshSelector dentAshOutPtr.toNat
          (min dentAshOutSize (UInt256.ofNat outAsh.size)).toNat).size ∧
      (outAsh.write 0 memAshSelector dentAshOutPtr.toNat
          (min dentAshOutSize (UInt256.ofNat outAsh.size)).toNat).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ ∧
      (32 ≤ outAsh.size →
        128 <
          (outAsh.write 0 memAshSelector dentAshOutPtr.toNat
            (min dentAshOutSize (UInt256.ofNat outAsh.size)).toNat).size) ∧
      (32 ≤ outAsh.size →
        (outAsh.write 0 memAshSelector dentAshOutPtr.toNat
            (min dentAshOutSize (UInt256.ofNat outAsh.size)).toNat).readWithPadding
          dentAshOutPtr.toNat 32 = outAsh.extract 0 32) := by
  intro id packedSlot target
  obtain ⟨memAshSelector, _, _, rd2674, hashCalldata, hmemAshSelector128,
      hread64AshSelector⟩ :=
    flopperDentX_moveSuccessTicZeroToAshExtcodesizeGuard
      (g := g) hmem hread64 hticZero rd2545
  obtain ⟨gasWord, _, _, rd2689⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2674⟩) (okPc := ⟨2686⟩) rd2674
      hashCodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cAAsh, σAsh, z, outAsh, Ain, callGas, k2690, C2690, hΘpack, rd2690raw,
      houtAshSize⟩ :=
    RD.call rd2689 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', AAsh, hΘ⟩ := hΘpack
  refine ⟨memAshSelector, cAAsh, σAsh, z, outAsh, Ain, AAsh, k2690, C2690,
    ?_, ?_, houtAshSize, ?_, ?_, ?_, ?_⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          dentAshOutPtr.toNat dentAshInSize.toNat)
          dentAshOutPtr.toNat dentAshOutSize.toNat) = UInt256.ofNat 8 := by
      unfold dentAshOutPtr dentAshInSize dentAshOutSize
      native_decide
    exact haw ▸ rd2690raw
  · have hashEncode :
        config.externalABI.encode? "Ash" [] =
          some (memAshSelector.readWithPadding dentAshOutPtr.toNat dentAshInSize.toNat) := by
      rw [hashCalldata]
      simp [config, externalABI]
    let evmPre : EVM.State :=
      { initState cA gh bl σ σ₀ g A I with
          accountMap := σ', substate := Ain, createdAccounts := cA' }
    have htyped :=
      callCoincides (cfg := config) (evm := evmPre) (name := "Ash") (args := [])
        (tgt := EVM.address (AccountAddress.ofNat target.toNat)) (targetWord := target)
        (cA' := cAAsh) (σ' := σAsh) (A' := AAsh) (A_in := Ain)
        (z := z) (o := outAsh) (g'' := g'') (callGas := callGas)
        (mem := memAshSelector) (inOff := dentAshOutPtr) (inSize := dentAshInSize)
        (callPerm := true)
        (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
        flopperAddressWord_address_eq_target
        hashEncode
        (by simpa [evmPre, initState, hperm] using hΘ)
    simpa [evmPre] using htyped
  · exact lt_of_lt_of_le (by decide : 64 < 128)
      (le_trans hmemAshSelector128
        (byteArray_write_size_ge_base outAsh memAshSelector 0 dentAshOutPtr.toNat
          (min dentAshOutSize (UInt256.ofNat outAsh.size)).toNat))
  · by_cases hlen :
        (min dentAshOutSize (UInt256.ofNat outAsh.size)).toNat = 0
    · rw [hlen, byteArray_write_len_zero]
      exact hread64AshSelector
    · have hlenSrc :
          (min dentAshOutSize (UInt256.ofNat outAsh.size)).toNat ≤ outAsh.size := by
        have hminLe :
            (min dentAshOutSize (UInt256.ofNat outAsh.size)).toNat ≤
              (UInt256.ofNat outAsh.size).toNat := by
          simp only [min]
          split
          · assumption
          · rfl
        rwa [ulit_toNat' outAsh.size houtAshSize] at hminLe
      rw [write_read_below_gen_extend outAsh memAshSelector dentAshOutPtr.toNat
        (min dentAshOutSize (UInt256.ofNat outAsh.size)).toNat 64 hlen hlenSrc
        (by simpa [dentAshOutPtr] using hmemAshSelector128)
        (by native_decide)]
      exact hread64AshSelector
  · intro houtAsh32
    have hmin :
        (min dentAshOutSize (UInt256.ofNat outAsh.size)).toNat = 32 := by
      simpa [dentAshOutSize] using
        (umin_ofNat_right_toNat_of_ge (c := 32) (n := outAsh.size)
          (by norm_num [UInt256.size]) houtAsh32 houtAshSize)
    rw [hmin]
    change 128 < (outAsh.write 0 memAshSelector 128 32).size
    rw [write32_eq outAsh memAshSelector 128 houtAsh32 hmemAshSelector128]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract]
    omega
  · intro houtAsh32
    have hmin :
        (min dentAshOutSize (UInt256.ofNat outAsh.size)).toNat = 32 := by
      simpa [dentAshOutSize] using
        (umin_ofNat_right_toNat_of_ge (c := 32) (n := outAsh.size)
          (by norm_num [UInt256.size]) houtAsh32 houtAshSize)
    rw [hmin]
    simpa [dentAshOutPtr] using
      write32_read_back outAsh memAshSelector 128 houtAsh32 hmemAshSelector128

theorem flopperDentX_ashCallSuccessDecodeShort
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {target : UInt256} {mem out : ByteArray} {k C : ℕ}
    (hshort : out.size < 32)
    (houtSize : out.size < UInt256.size)
    (hmem64 : 64 < mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2690 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2690⟩
      (⟨1⟩ :: dentAshEndPtr :: dentAshSelectorWord :: target :: ⟨0⟩ ::
        dentBidWord I :: dentLotWord I :: dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out acc k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2708⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨2690⟩) (okPc := ⟨2706⟩) rd2690
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue hmem64 (by decide) hread64
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨2708⟩) (okPc := ⟨2728⟩)
    rd2708 hshort houtSize
    mem_cost (by decide) hmload64
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem flopperDentX_ashCallSuccessDecodeOk
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {target : UInt256} {mem out : ByteArray} {k C : ℕ}
    (hout32 : 32 ≤ out.size)
    (houtSize : out.size < UInt256.size)
    (hmem64 : 64 < mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hmem128 : 128 < mem.size)
    (hread128 : mem.readWithPadding 128 32 = out.extract 0 32)
    (rd2690 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2690⟩
      (⟨1⟩ :: dentAshEndPtr :: dentAshSelectorWord :: target :: ⟨0⟩ ::
        dentBidWord I :: dentLotWord I :: dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out acc k C) :
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2731⟩
      (dentAshWord out :: ⟨0⟩ :: dentBidWord I :: dentLotWord I :: dentIdWord I ::
        ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out acc k' C' := by
  obtain ⟨_, _, rd2708⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨2690⟩) (okPc := ⟨2706⟩) rd2690
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue hmem64 (by decide) hread64
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        dentAshWord out := by
    have hnot :
        ¬ ((⟨128⟩ : UInt256).toNat ≥ mem.size
            ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩) := by
      intro h
      cases h with
      | inl hge =>
          have h128 : (⟨128⟩ : UInt256).toNat = 128 := by decide
          omega
      | inr hge =>
          exact (by native_decide :
            ¬ ((⟨128⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩)) hge
    rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide, hread128]
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨2708⟩) (okPc := ⟨2728⟩)
    (retWord := dentAshWord out) rd2708 hout32 houtSize
    mem_cost (by decide) hmload64 hmload128 mem_cost (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

theorem flopperDentX_minReturnToKissSetup
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd4716 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4716⟩
      (dentAshWord out :: dentBidWord I :: ⟨2775⟩ :: dentKissSelectorWord :: target ::
        dentAshWord out :: dentBidWord I :: dentLotWord I :: dentIdWord I :: ⟨334⟩ ::
        sel :: [])
      mem aw out acc k C) :
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2775⟩
      (dentKissAmtWord I out :: dentKissSelectorWord :: target :: dentAshWord out ::
        dentBidWord I :: dentLotWord I :: dentIdWord I :: ⟨334⟩ :: sel :: [])
      mem aw out acc k' C' := by
  have rd4726pre := evm_run rd4716 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨4733⟩ (by native_decide) (by evm_ov)]
  by_cases hle : (dentBidWord I).toNat ≤ (dentAshWord out).toNat
  · have hgt : UInt256.gt (dentBidWord I) (dentAshWord out) = ⟨0⟩ :=
      ugt_zero hle
    have hcond :
        UInt256.isZero (UInt256.gt (dentBidWord I) (dentAshWord out)) ≠ ⟨0⟩ := by
      rw [hgt]
      decide
    have rd4733 := rd4726pre.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
    have rd4739 := evm_run rd4733 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw swap1 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw swap1 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rd2775 := rd4739.jump (by native_decide) (by jump_dest) (by evm_ov)
    exact ⟨_, _, by simpa [dentKissAmtWord, hle] using rd2775⟩
  · have hlt : (dentAshWord out).toNat < (dentBidWord I).toNat := by omega
    have hgt : UInt256.gt (dentBidWord I) (dentAshWord out) = ⟨1⟩ :=
      ugt_one hlt
    have hcond :
        UInt256.isZero (UInt256.gt (dentBidWord I) (dentAshWord out)) = ⟨0⟩ := by
      rw [hgt]
      decide
    have rd4727 := rd4726pre.jumpiNT (by native_decide) hcond (by evm_ov)
    have rd4732 := evm_run rd4727 with [
      raw pop (by native_decide) (by evm_ov),
      raw dup1 (by native_decide) (by evm_ov),
      raw push2 ⟨4710⟩ (by native_decide) (by evm_ov)]
    have rd4710 := rd4732.jump (by native_decide) (by jump_dest) (by evm_ov)
    have rd4715 := evm_run rd4710 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rd2775 := rd4715.jump (by native_decide) (by jump_dest) (by evm_ov)
    exact ⟨_, _, by simpa [dentKissAmtWord, hle] using rd2775⟩

set_option maxHeartbeats 1000000 in
theorem flopperDentX_ashDecodeOkToKissExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    (hmem128 : 128 < mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd2731 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2731⟩
      (dentAshWord out :: ⟨0⟩ :: dentBidWord I :: dentLotWord I :: dentIdWord I ::
        ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out acc k C) :
    let id := dentIdWord I
    let packedSlot := auctionPackedSlot id
    let target := flopperAddressReturnWord packedSlot acc.2 I
    let kissAmt := dentKissAmtWord I out
    let memMap := twoWordHashMem id ⟨1⟩ mem
    let memKiss := dentKissCalldataMem kissAmt memMap
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2817⟩
      (target :: target :: ⟨0⟩ :: dentKissOutPtr :: dentKissInSize :: dentKissOutPtr ::
        dentKissOutSize :: dentKissEndPtr :: dentKissSelectorWord :: target ::
        dentAshWord out :: dentBidWord I :: dentLotWord I :: id :: ⟨334⟩ :: sel :: [])
      memKiss (UInt256.ofNat 8) out acc k' C' := by
  intro id packedSlot target kissAmt memMap memKiss
  let base := solcMappingSlot ⟨1⟩ id
  let oldPacked := solcSlotWord acc.2 I packedSlot
  have hmem96 : 96 ≤ mem.size := by omega
  have hmemMapSize : memMap.size = mem.size := by
    simpa [memMap, id] using twoWordHashMem_size_of_ge_64 id ⟨1⟩ (by omega : 64 ≤ mem.size)
  have hread64Map :
      memMap.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memMap, id] using twoWordHashMem_read64_of_ge_96 id ⟨1⟩ hmem96 hread64
  have rd2735pre := evm_run rd2731 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2736 := rd2735pre.mstore 0 (wordAt0Mem id mem) (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2740pre := evm_run rd2736 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2741 := rd2740pre.mstore 0 memMap (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memMap, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2744pre := evm_run rd2741 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memMap.readWithPadding 0 64))) = base := by
    simpa [base, memMap, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id mem
  have rd2745pre := rd2744pre.keccak256 0 base (UInt256.ofNat 8)
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
  have rd2748pre := evm_run rd2745pre with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = packedSlot := by
    rw [u256_add_comm]
    simp [packedSlot, base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd2748pre
  obtain ⟨k2749, C2749, rd2749raw⟩ := rd2748pre.sload (by native_decide) (by evm_ov)
  have rd2749 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2749⟩
      [oldPacked, dentAshWord out, ⟨0⟩, dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memMap (UInt256.ofNat 8) out acc k2749 C2749 := by
    simpa [oldPacked, packedSlot, solcSlotWord] using rd2749raw
  have rd2761pre := evm_run rd2749 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hrd2761 :
      ∃ k2761 C2761, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2761⟩
        [target, dentAshWord out, dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
        memMap (UInt256.ofNat 8) out acc k2761 C2761 := by
    exact ⟨_, _, by
      simpa [target, oldPacked, packedSlot, flopperAddressReturnWord, solcSlotWord,
        hmask, u256_land_comm] using rd2761pre⟩
  obtain ⟨_, _, rd2761⟩ := hrd2761
  have rd2774pre := evm_run rd2761 with [
    raw push4 dentKissSelectorWord (by native_decide) (by evm_ov),
    raw push2 ⟨2775⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨4716⟩ (by native_decide) (by evm_ov)]
  have rd4716 := rd2774pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd2775⟩ := flopperDentX_minReturnToKissSetup rd4716
  have hmload64Map :
      (if (⟨64⟩ : UInt256).toNat ≥ memMap.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memMap.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue (by rw [hmemMapSize]; omega) (by decide) hread64Map
  have rd2790pre := evm_run rd2775 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Map (by decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2791 := rd2790pre.mstore 0 (dentKissSelectorMem memMap) (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      simp [dentKissSelectorMem, dentKissSelectorShifted, u256_land_comm,
        show UInt256.shiftLeft (UInt256.land dentKissSelectorWord ⟨4294967295⟩)
            ⟨224⟩ = dentKissSelectorShifted from by native_decide,
        show (⟨128⟩ : UInt256).toNat = 128 from by decide])
    (by native_decide)
    (by evm_ov)
  have rd2797pre := evm_run rd2791 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2798 := rd2797pre.mstore 0 memKiss (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKiss, kissAmt, dentKissCalldataMem,
      show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat = 132 from by native_decide,
      show (⟨132⟩ : UInt256).toNat = 132 from by decide])
    (by native_decide)
    (by evm_ov)
  have hread64Kiss :
      memKiss.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memKiss, kissAmt, memMap] using
      dentKissCalldataMem_read64 kissAmt
        (by rw [hmemMapSize]; exact hmem96)
        hread64Map
  have hmemKiss64 : 64 < memKiss.size := by
    have hselBase :
        memMap.size ≤ (dentKissSelectorMem memMap).size :=
      byteArray_write_size_ge_base dentKissSelectorShifted.toByteArray memMap 0 128 32
    have hcallBase :
        (dentKissSelectorMem memMap).size ≤ memKiss.size := by
      simpa [memKiss, kissAmt, dentKissCalldataMem] using
        byteArray_write_size_ge_base kissAmt.toByteArray (dentKissSelectorMem memMap) 0 132 32
    have hmemMap64 : 64 < memMap.size := by rw [hmemMapSize]; omega
    exact lt_of_lt_of_le hmemMap64 (le_trans hselBase hcallBase)
  have hmload64Kiss :
      (if (⟨64⟩ : UInt256).toNat ≥ memKiss.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memKiss.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue hmemKiss64 (by decide) hread64Kiss
  have rd2817pre := evm_run rd2798 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Kiss (by decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [id, packedSlot, target, kissAmt, memMap, memKiss, dentKissOutPtr,
      dentKissInSize, dentKissOutSize, dentKissEndPtr,
      show UInt256.sub (⟨164⟩ : UInt256) ⟨128⟩ = ⟨36⟩ from by native_decide,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide,
      show (⟨132⟩ : UInt256) + ⟨32⟩ = ⟨164⟩ from by native_decide]
      using rd2817pre⟩

theorem flopperDentX_kissNoCode
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    (hnoCode : Reasoning.Theory.extCodeSizeWord acc.2 target = ⟨0⟩)
    (rd2817 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2817⟩
      (target :: target :: ⟨0⟩ :: dentKissOutPtr :: dentKissInSize :: dentKissOutPtr ::
        dentKissOutSize :: dentKissEndPtr :: dentKissSelectorWord :: target ::
        dentAshWord out :: dentBidWord I :: dentLotWord I :: dentIdWord I :: ⟨334⟩ ::
        sel :: [])
      mem (UInt256.ofNat 8) out acc k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2817⟩) (okPc := ⟨2829⟩) rd2817
    hnoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

set_option maxHeartbeats 1000000 in
theorem flopperDentX_kissCall
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outAsh : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord acc.2 target ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hencode :
      config.externalABI.encode? "kiss"
          [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)] =
        some (mem.readWithPadding dentKissOutPtr.toNat dentKissInSize.toNat))
    (rd2817 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2817⟩
      (target :: target :: ⟨0⟩ :: dentKissOutPtr :: dentKissInSize :: dentKissOutPtr ::
        dentKissOutSize :: dentKissEndPtr :: dentKissSelectorWord :: target ::
        dentAshWord outAsh :: dentBidWord I :: dentLotWord I :: dentIdWord I :: ⟨334⟩ ::
        sel :: [])
      mem (UInt256.ofNat 8) outAsh acc k C) :
    ∃ (cAKiss : Batteries.RBSet AccountAddress compare) (σKiss : AccountMap) (z : Bool)
      (outKiss : ByteArray) (Ain AKiss : Substate) (k' C' : ℕ),
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2833⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: dentKissEndPtr :: dentKissSelectorWord ::
          target :: dentAshWord outAsh :: dentBidWord I :: dentLotWord I ::
          dentIdWord I :: ⟨334⟩ :: sel :: [])
        mem (UInt256.ofNat 8) outKiss (cAKiss, σKiss) k' C' ∧
      typedCallViaEVM config
        { initState cA gh bl σ σ₀ g A I with
            accountMap := acc.2, substate := Ain, createdAccounts := acc.1 }
        (EVM.address (AccountAddress.ofNat target.toNat)) "kiss" 0
        [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)]
        (z,
          { initState cA gh bl σ σ₀ g A I with
              accountMap := σKiss, substate := AKiss, createdAccounts := cAKiss },
          outKiss) true ∧
      outKiss.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd2832⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2817⟩) (okPc := ⟨2829⟩) rd2817
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cAKiss, σKiss, z, outKiss, Ain, callGas, k2833, C2833, hΘpack, rd2833raw,
      houtKissSize⟩ :=
    RD.call rd2832 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', AKiss, hΘ⟩ := hΘpack
  refine ⟨cAKiss, σKiss, z, outKiss, Ain, AKiss, k2833, C2833, ?_, ?_, houtKissSize⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          dentKissOutPtr.toNat dentKissInSize.toNat)
          dentKissOutPtr.toNat dentKissOutSize.toNat) = UInt256.ofNat 8 := by
      unfold dentKissOutPtr dentKissInSize dentKissOutSize
      native_decide
    have hmin : (min dentKissOutSize (UInt256.ofNat outKiss.size)).toNat = 0 := by
      unfold dentKissOutSize
      rfl
    have rd2833 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2833⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: dentKissEndPtr :: dentKissSelectorWord ::
          target :: dentAshWord outAsh :: dentBidWord I :: dentLotWord I ::
          dentIdWord I :: ⟨334⟩ :: sel :: [])
        (outKiss.write 0 mem dentKissOutPtr.toNat
          (min dentKissOutSize (UInt256.ofNat outKiss.size)).toNat)
        (UInt256.ofNat 8) outKiss (cAKiss, σKiss) k2833 C2833 :=
      haw ▸ rd2833raw
    rw [hmin, byteArray_write_len_zero] at rd2833
    exact rd2833
  · have htyped :=
      callCoincides (cfg := config)
        (evm := { initState cA gh bl σ σ₀ g A I with
            accountMap := acc.2, substate := Ain, createdAccounts := acc.1 })
        (name := "kiss")
        (args := [.int (Int.ofNat (dentKissAmtWord I outAsh).toNat)])
        (tgt := EVM.address (AccountAddress.ofNat target.toNat)) (targetWord := target)
        (cA' := cAKiss) (σ' := σKiss) (A' := AKiss) (A_in := Ain)
        (z := z) (o := outKiss) (g'' := g'') (callGas := callGas)
        (mem := mem) (inOff := dentKissOutPtr) (inSize := dentKissInSize)
        (callPerm := true)
        (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
        flopperAddressWord_address_eq_target
        hencode
        (by simpa [initState, hperm] using hΘ)
    exact htyped

theorem flopperDentX_kissCallFailure
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outAsh outKiss : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd2833 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2833⟩
      (⟨0⟩ :: dentKissEndPtr :: dentKissSelectorWord :: target ::
        dentAshWord outAsh :: dentBidWord I :: dentLotWord I :: dentIdWord I ::
        ⟨334⟩ :: sel :: [])
      mem aw outKiss acc k C)
    (houtSize : outKiss.size < UInt256.size) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2833⟩) (okPc := ⟨2849⟩) rd2833
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtSize (by simp)

set_option maxHeartbeats 1000000 in
theorem flopperDentX_guyStoreTailFrom2855
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {mem out : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (rd2855 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2855⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      mem (UInt256.ofNat 8) out (cA', σ') k C) :
    ∃ (memGuy : ByteArray) (k' C' : ℕ),
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2889⟩
        [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
        memGuy (UInt256.ofNat 8) out
        (cA', dentRuntimeAfterGuyMap I.codeOwner σ' I) k' C' := by
  let id := dentIdWord I
  let packedSlot := auctionPackedSlot id
  let memGuyKey := wordAt0Mem id mem
  let memGuy := twoWordHashMem id ⟨1⟩ mem
  let base := solcMappingSlot ⟨1⟩ id
  let oldPacked := solcSlotWord σ' I packedSlot
  let src := UInt256.ofNat I.source.val
  let σGuy := dentRuntimeAfterGuyMap I.codeOwner σ' I
  have rd2860pre := evm_run rd2855 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2861 := rd2860pre.mstore 0 memGuyKey (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memGuyKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2865pre := evm_run rd2861 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2866 := rd2865pre.mstore 0 memGuy (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memGuyKey, memGuy, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2869pre := evm_run rd2866 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbaseGuy :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memGuy.readWithPadding 0 64))) = base := by
    simpa [base, memGuy, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id mem
  have rd2870pre := rd2869pre.keccak256 0 base (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbaseGuy)
    (by native_decide)
    (by evm_ov)
  have rd2873pre := evm_run rd2870pre with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpacked : (⟨2⟩ : UInt256) + base = packedSlot := by
    rw [u256_add_comm]
    simp [packedSlot, base, auctionPackedSlot_eq, id]
  rw [hpacked] at rd2873pre
  have rd2874pre := rd2873pre.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k2875, C2875, rd2875raw⟩ := rd2874pre.sload (by native_decide) (by evm_ov)
  have rd2875 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2875⟩
      [oldPacked, packedSlot, dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memGuy (UInt256.ofNat 8) out (cA', σ') k2875 C2875 := by
    simpa [oldPacked, packedSlot, solcSlotWord] using rd2875raw
  have rd2887pre := evm_run rd2875 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k2889, C2889, rd2889raw⟩ := rd2887pre.sstore hperm
    (by native_decide) (by evm_ov)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by
    native_decide
  have hsrcCanon : src.toNat < EVM.addressModulus := by
    simpa [src, solcSourceWord] using solcSourceWord_canonical I
  have hsrcClean : UInt256.land src solcAddrMask = src := by
    exact solcAddrMask_clean hsrcCanon
  have hstored :
      UInt256.lor src (UInt256.land (UInt256.lnot solcAddrMask) oldPacked) =
        setAddressOffset0Word oldPacked src := by
    calc
      UInt256.lor src (UInt256.land (UInt256.lnot solcAddrMask) oldPacked) =
          UInt256.lor (UInt256.land oldPacked (UInt256.lnot solcAddrMask)) src := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) oldPacked]
            exact u256_lor_comm _ _
      _ = UInt256.lor (UInt256.land oldPacked (UInt256.lnot solcAddrMask))
            (UInt256.land src solcAddrMask) := by
            rw [hsrcClean]
      _ = setAddressOffset0Word oldPacked src := rfl
  have rd2889 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2889⟩
      [dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memGuy (UInt256.ofNat 8) out (cA', σGuy) k2889 C2889 := by
    simpa [σGuy, dentRuntimeAfterGuyMap, oldPacked, packedSlot, src, hmask, hstored]
      using rd2889raw
  exact ⟨memGuy, _, _, by simpa [id] using rd2889⟩

theorem flopperDentX_kissCallSuccessToTail
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel target : UInt256}
    {cAKiss : Batteries.RBSet AccountAddress compare} {σKiss : AccountMap}
    {mem outAsh outKiss : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (rd2833 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2833⟩
      (⟨1⟩ :: dentKissEndPtr :: dentKissSelectorWord :: target ::
        dentAshWord outAsh :: dentBidWord I :: dentLotWord I :: dentIdWord I ::
        ⟨334⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outKiss (cAKiss, σKiss) k C) :
    ∃ (memGuy : ByteArray) (k' C' : ℕ),
      RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2889⟩
        [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
        memGuy (UInt256.ofNat 8) outKiss
        (cAKiss, dentRuntimeAfterGuyMap I.codeOwner σKiss I) k' C' := by
  obtain ⟨_, _, rd2851⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨2833⟩) (okPc := ⟨2849⟩) rd2833
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2855 := evm_run rd2851 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact flopperDentX_guyStoreTailFrom2855 (g := g) hperm rd2855

set_option maxHeartbeats 1000000 in
theorem flopperDentX_toCheckedAddStartFromTail
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {retData : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (rd2889 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2889⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) retData (cA, σ) k C) :
    let id := dentIdWord I
    let memLotStore := twoWordHashMem id ⟨1⟩ memStart
    let σLot := dentRuntimeAfterLotMap I.codeOwner σ I
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4740⟩
      [dentRuntimeTtlWord I.codeOwner σ I, UInt256.ofNat I.header.timestamp, ⟨2932⟩,
        dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memLotStore (UInt256.ofNat 3) retData (cA, σLot) k' C' := by
  intro id memLotStore σLot
  let memKey := wordAt0Mem id memStart
  let base := solcMappingSlot ⟨1⟩ id
  have rd2894pre := evm_run rd2889 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2895 := rd2894pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2901pre := evm_run rd2895 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2902 := rd2901pre.mstore 0 memLotStore (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memLotStore, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2906pre := evm_run rd2902 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memLotStore.readWithPadding 0 64))) = base := by
    simpa [base, memLotStore, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd2907pre := rd2906pre.keccak256 0 base (UInt256.ofNat 3)
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
  have rd2910pre := evm_run rd2907pre with [
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hlotSlot : base + ⟨1⟩ = auctionLotSlot id := by
    simp [base, auctionLotSlot_eq, id]
  rw [hlotSlot] at rd2910pre
  obtain ⟨k2911, C2911, rd2911raw⟩ := rd2910pre.sstore hperm
    (by native_decide) (by evm_ov)
  have rd2911 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2911⟩
      [dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memLotStore (UInt256.ofNat 3) retData (cA, σLot) k2911 C2911 := by
    simpa [σLot, dentRuntimeAfterLotMap, id] using rd2911raw
  have rd2913 := rd2911.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨k2914, C2914, rd2914raw⟩ := rd2913.sload (by native_decide) (by evm_ov)
  have rd2914 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2914⟩
      [flopperSlotWord ⟨6⟩ σLot I, dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memLotStore (UInt256.ofNat 3) retData (cA, σLot) k2914 C2914 := by
    simpa [flopperSlotWord] using rd2914raw
  have rd2920 := evm_run rd2914 with [
    raw push2 ⟨2932⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw timestamp (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2927 := rd2920.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd2928 := rd2927.and (by native_decide) (by evm_ov)
  have rd2931 := rd2928.push2 ⟨4740⟩ (by native_decide) (by evm_ov)
  have rd4740 := rd2931.jump (by native_decide) (by jump_dest) (by evm_ov)
  have httlRaw :
      UInt256.land flopperUint48Mask (flopperSlotWord ⟨6⟩ σLot I) =
        dentRuntimeTtlWord I.codeOwner σ I := by
    rw [u256_land_comm]
    rfl
  exact ⟨_, _, by
    simpa [σLot, dentRuntimeTtlWord, flopperUint48Offset0Word, id, httlRaw]
      using rd4740⟩

set_option maxHeartbeats 1000000 in
theorem flopperDentX_addOverflowFromCheckedAdd
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {retData : ByteArray} {k C : ℕ}
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (dentRuntimeTtlWord I.codeOwner σ I).toNat)
    (rd4740 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4740⟩
      [dentRuntimeTtlWord I.codeOwner σ I, UInt256.ofNat I.header.timestamp, ⟨2932⟩,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) retData
      (cA, dentRuntimeAfterLotMap I.codeOwner σ I) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let ttl := dentRuntimeTtlWord I.codeOwner σ I
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
  have httlLt : ttl.toNat < 2 ^ 48 := by
    simpa [ttl] using dentRuntimeTtlWord_lt I.codeOwner σ I
  have hltTrue :
      UInt256.lt (UInt256.land (timestamp + ttl) flopperUint48Mask)
          (UInt256.land timestamp flopperUint48Mask) = ⟨1⟩ := by
    simpa [timestamp, ttl] using
      uint48AddGuard_true_of_wrap timestamp ttl httlLt haddOverflow
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.land (timestamp + ttl) flopperUint48Mask)
            (UInt256.land timestamp flopperUint48Mask)) = ⟨0⟩ := by
    rw [hltTrue]
    native_decide
  have rd4763 := rd4759.jumpiNT (by native_decide) hcond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd4763
    (by native_decide) (by native_decide) (by native_decide)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem flopperDentX_addOkFromCheckedAdd
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {retData : ByteArray} {k C : ℕ}
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (dentRuntimeTtlWord I.codeOwner σ I).toNat < 2 ^ 48)
    (rd4740 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4740⟩
      [dentRuntimeTtlWord I.codeOwner σ I, UInt256.ofNat I.header.timestamp, ⟨2932⟩,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) retData
      (cA, dentRuntimeAfterLotMap I.codeOwner σ I) k C) :
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2932⟩
      [dentRuntimeTicAddWord I.codeOwner σ I,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) retData
      (cA, dentRuntimeAfterLotMap I.codeOwner σ I) k' C' := by
  let ttl := dentRuntimeTtlWord I.codeOwner σ I
  let timestamp := UInt256.ofNat I.header.timestamp
  let addWord := dentRuntimeTicAddWord I.codeOwner σ I
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
      UInt256.lt (UInt256.land (timestamp + ttl) flopperUint48Mask)
          (UInt256.land timestamp flopperUint48Mask) = ⟨0⟩ := by
    simpa [timestamp, ttl] using uint48AddGuard_false_of_no_wrap timestamp ttl haddFit
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.land (timestamp + ttl) flopperUint48Mask)
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
  have rd2932 := rd4715.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa [timestamp, ttl, addWord, dentRuntimeTicAddWord] using rd2932⟩

set_option maxHeartbeats 1000000 in
theorem flopperDentX_successFromAddOk
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {retData : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (rd2932 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2932⟩
      [dentRuntimeTicAddWord I.codeOwner σ I,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) retData
      (cA, dentRuntimeAfterLotMap I.codeOwner σ I) k C) :
    RDret flopperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, dentRuntimeTailSuccessAccountMap I.codeOwner σ I) ByteArray.empty := by
  let id := dentIdWord I
  let σLot := dentRuntimeAfterLotMap I.codeOwner σ I
  let addWord := dentRuntimeTicAddWord I.codeOwner σ I
  let memStore := twoWordHashMem id ⟨1⟩ memStart
  let base := solcMappingSlot ⟨1⟩ id
  let packedSlot := auctionPackedSlot id
  let oldPacked := solcSlotWord σLot I packedSlot
  let σSuccess := dentRuntimeTailSuccessAccountMap I.codeOwner σ I
  let memKey := wordAt0Mem id memStart
  have rd2937pre := evm_run rd2932 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rd2938 := rd2937pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2942pre := evm_run rd2938 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2943 := rd2942pre.mstore 0 memStore (UInt256.ofNat 3)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memStore, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2947pre := evm_run rd2943 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memStore.readWithPadding 0 64))) = base := by
    simpa [base, memStore, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd2948pre := rd2947pre.keccak256 0 base (UInt256.ofNat 3)
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
  have rd2951pre := evm_run rd2948pre with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpackedSlot : (⟨2⟩ : UInt256) + base = packedSlot := by
    rw [u256_add_comm]
    simp [packedSlot, base, auctionPackedSlot_eq, id]
  rw [hpackedSlot] at rd2951pre
  have rd2952pre := rd2951pre.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k2953, C2953, rd2953raw⟩ := rd2952pre.sload (by native_decide) (by evm_ov)
  have rd2953 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2953⟩
      [oldPacked, packedSlot, dentBidWord I, dentLotWord I, addWord, ⟨334⟩, sel]
      memStore (UInt256.ofNat 3) retData (cA, σLot) k2953 C2953 := by
    simpa [oldPacked, packedSlot, solcSlotWord, addWord, σLot] using rd2953raw
  have rd2960 := rd2953.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd2970pre := evm_run rd2960 with [
    raw swap5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov)]
  have rd2977 := rd2970pre.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd2990pre := evm_run rd2977 with [
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  obtain ⟨k2991, C2991, rd2991raw⟩ := rd2990pre.sstore hperm
    (by native_decide) (by evm_ov)
  have hstoredRaw :
      UInt256.lor
          (UInt256.land oldPacked
            (UInt256.lnot (UInt256.shiftLeft flopperUint48Mask ⟨160⟩)))
          (UInt256.mul (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)
            (UInt256.land flopperUint48Mask addWord)) =
        setUint48Offset20Word oldPacked addWord := by
    simpa [setUint48Offset20RawWord] using
      setUint48Offset20RawWord_eq_setUint48Offset20Word oldPacked addWord
  rw [hstoredRaw] at rd2991raw
  have rd2991 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2991⟩
      [dentLotWord I, dentBidWord I, ⟨334⟩, sel]
      memStore (UInt256.ofNat 3) retData (cA, σSuccess) k2991 C2991 := by
    simpa [σSuccess, dentRuntimeTailSuccessAccountMap, dentRuntimeTicStoredWord,
      σLot, oldPacked, packedSlot, addWord, id] using rd2991raw
  have rd2993 := evm_run rd2991 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd334 := rd2993.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd335 := rd334.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd335 (by native_decide) (by evm_ov)

theorem flopperDentX_addOverflowFromTail
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {retData : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (dentRuntimeTtlWord I.codeOwner σ I).toNat)
    (rd2889 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2889⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) retData (cA, σ) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4740⟩ := flopperDentX_toCheckedAddStartFromTail hperm rd2889
  exact flopperDentX_addOverflowFromCheckedAdd haddOverflow rd4740

theorem flopperDentX_successFromTail
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {retData : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (dentRuntimeTtlWord I.codeOwner σ I).toNat < 2 ^ 48)
    (rd2889 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2889⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 3) retData (cA, σ) k C) :
    RDret flopperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, dentRuntimeTailSuccessAccountMap I.codeOwner σ I) ByteArray.empty := by
  obtain ⟨_, _, rd4740⟩ := flopperDentX_toCheckedAddStartFromTail hperm rd2889
  obtain ⟨_, _, rd2932⟩ := flopperDentX_addOkFromCheckedAdd haddFit rd4740
  exact flopperDentX_successFromAddOk hperm rd2932

theorem flopperDentX_toCheckedAddStartFromTailAw8
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {retData : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (rd2889 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2889⟩
      [dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 8) retData (cAcur, τ) k C) :
    let id := dentIdWord I
    let memLotStore := twoWordHashMem id ⟨1⟩ memStart
    let σLot := dentRuntimeAfterLotMap I.codeOwner τ I
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4740⟩
      [dentRuntimeTtlWord I.codeOwner τ I, UInt256.ofNat I.header.timestamp, ⟨2932⟩,
        dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memLotStore (UInt256.ofNat 8) retData (cAcur, σLot) k' C' := by
  intro id memLotStore σLot
  let memKey := wordAt0Mem id memStart
  let base := solcMappingSlot ⟨1⟩ id
  have rd2894pre := evm_run rd2889 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2895 := rd2894pre.mstore 0 memKey (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by simp [memKey, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd2901pre := evm_run rd2895 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2902 := rd2901pre.mstore 0 memLotStore (UInt256.ofNat 8)
    (by native_decide)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack haw hstk (by native_decide))
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memLotStore, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd2906pre := evm_run rd2902 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC (memLotStore.readWithPadding 0 64))) = base := by
    simpa [base, memLotStore, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStart
  have rd2907pre := rd2906pre.keccak256 0 base (UInt256.ofNat 8)
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
  have rd2910pre := evm_run rd2907pre with [
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hlotSlot : base + ⟨1⟩ = auctionLotSlot id := by
    simp [base, auctionLotSlot_eq, id]
  rw [hlotSlot] at rd2910pre
  obtain ⟨k2911, C2911, rd2911raw⟩ := rd2910pre.sstore hperm
    (by native_decide) (by evm_ov)
  have rd2911 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2911⟩
      [dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memLotStore (UInt256.ofNat 8) retData (cAcur, σLot) k2911 C2911 := by
    simpa [σLot, dentRuntimeAfterLotMap, id] using rd2911raw
  have rd2913 := rd2911.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨k2914, C2914, rd2914raw⟩ := rd2913.sload (by native_decide) (by evm_ov)
  have rd2914 : RD flopperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2914⟩
      [flopperSlotWord ⟨6⟩ σLot I, dentBidWord I, dentLotWord I, id, ⟨334⟩, sel]
      memLotStore (UInt256.ofNat 8) retData (cAcur, σLot) k2914 C2914 := by
    simpa [flopperSlotWord] using rd2914raw
  have rd2920 := evm_run rd2914 with [
    raw push2 ⟨2932⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw timestamp (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2927 := rd2920.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd2928 := rd2927.and (by native_decide) (by evm_ov)
  have rd2931 := rd2928.push2 ⟨4740⟩ (by native_decide) (by evm_ov)
  have rd4740 := rd2931.jump (by native_decide) (by jump_dest) (by evm_ov)
  have httlRaw :
      UInt256.land flopperUint48Mask (flopperSlotWord ⟨6⟩ σLot I) =
        dentRuntimeTtlWord I.codeOwner τ I := by
    rw [u256_land_comm]
    rfl
  exact ⟨_, _, by
    simpa [σLot, dentRuntimeTtlWord, flopperUint48Offset0Word, id, httlRaw]
      using rd4740⟩

set_option maxHeartbeats 1000000 in
theorem flopperDentX_addOverflowFromCheckedAddAw8
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {retData : ByteArray} {k C : ℕ}
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (dentRuntimeTtlWord I.codeOwner τ I).toNat)
    (rd4740 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4740⟩
      [dentRuntimeTtlWord I.codeOwner τ I, UInt256.ofNat I.header.timestamp, ⟨2932⟩,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 8) retData
      (cAcur, dentRuntimeAfterLotMap I.codeOwner τ I) k C) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let ttl := dentRuntimeTtlWord I.codeOwner τ I
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
  have httlLt : ttl.toNat < 2 ^ 48 := by
    simpa [ttl] using dentRuntimeTtlWord_lt I.codeOwner τ I
  have hltTrue :
      UInt256.lt (UInt256.land (timestamp + ttl) flopperUint48Mask)
          (UInt256.land timestamp flopperUint48Mask) = ⟨1⟩ := by
    simpa [timestamp, ttl] using
      uint48AddGuard_true_of_wrap timestamp ttl httlLt haddOverflow
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.land (timestamp + ttl) flopperUint48Mask)
            (UInt256.land timestamp flopperUint48Mask)) = ⟨0⟩ := by
    rw [hltTrue]
    native_decide
  have rd4763 := rd4759.jumpiNT (by native_decide) hcond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd4763
    (by native_decide) (by native_decide) (by native_decide)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem flopperDentX_addOkFromCheckedAddAw8
    {cA cAcur gh bl σ τ σ₀ A I} {g : Sat256} {sel : UInt256} {memStart : ByteArray}
    {retData : ByteArray} {k C : ℕ}
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (dentRuntimeTtlWord I.codeOwner τ I).toNat < 2 ^ 48)
    (rd4740 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4740⟩
      [dentRuntimeTtlWord I.codeOwner τ I, UInt256.ofNat I.header.timestamp, ⟨2932⟩,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 8) retData
      (cAcur, dentRuntimeAfterLotMap I.codeOwner τ I) k C) :
    ∃ k' C', RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2932⟩
      [dentRuntimeTicAddWord I.codeOwner τ I,
        dentBidWord I, dentLotWord I, dentIdWord I, ⟨334⟩, sel]
      memStart (UInt256.ofNat 8) retData
      (cAcur, dentRuntimeAfterLotMap I.codeOwner τ I) k' C' := by
  let ttl := dentRuntimeTtlWord I.codeOwner τ I
  let timestamp := UInt256.ofNat I.header.timestamp
  let addWord := dentRuntimeTicAddWord I.codeOwner τ I
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
      UInt256.lt (UInt256.land (timestamp + ttl) flopperUint48Mask)
          (UInt256.land timestamp flopperUint48Mask) = ⟨0⟩ := by
    simpa [timestamp, ttl] using uint48AddGuard_false_of_no_wrap timestamp ttl haddFit
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.land (timestamp + ttl) flopperUint48Mask)
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
  have rd2932 := rd4715.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa [timestamp, ttl, addWord, dentRuntimeTicAddWord] using rd2932⟩

end Benchmarks.Dss.Flopper
