import Benchmarks.Dss.Flipper.DentRefund

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## EVM helpers for the caller-changing `dent` refund branch -/

theorem flipperDentX_takeRefundBranch {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hcaller : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
    (h : RD flipperBytecode I g s0 ⟨4733⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4767⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4750 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (twoWordHashMem (dentId I) ⟨1⟩ mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (dentId I) hmemSize)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k4752, C4752, rd4752raw⟩ := rd4750.sload (by native_decide) (by evm_ov)
  have rd4752 : RD flipperBytecode I g s0 ⟨4752⟩
      [bidPackedWord (dentId I) σ I, dentBid I, dentLot I, dentId I, ret, sel]
      (twoWordHashMem (dentId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4752 C4752 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (dentId I) =
          bidPackedSlotOfWord (dentId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [bidPackedWord, flipperSlotWord, hslotAdd] using rd4752raw
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by
    native_decide
  have rd4763raw := evm_run rd4752 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  obtain ⟨k4763, C4763, rd4763⟩ : ∃ k' C',
      RD flipperBytecode I g s0 ⟨4763⟩
        [UInt256.eq (solcSourceWord I) (bidGuyWord (dentId I) σ I), dentBid I,
          dentLot I, dentId I, ret, sel]
        (twoWordHashMem (dentId I) ⟨1⟩ mem)
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by
      simpa [bidGuyWord, bidPackedWord, flipperAddressReturnWord, hmask160, u256_land_comm]
        using rd4763raw⟩
  have heq : UInt256.eq (solcSourceWord I) (bidGuyWord (dentId I) σ I) = ⟨0⟩ :=
    u256_eq_of_ne hcaller
  rw [heq] at rd4763
  exact ⟨_, _, evm_run rd4763 with [
    raw push2 ⟨4927⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)]⟩

theorem flipperDentX_refundCalldataReady {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD flipperBytecode I g s0 ⟨4767⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4831⟩
      (⟨128⟩ :: solcAddrMask :: ⟨0⟩ :: flipperSlotWord ⟨2⟩ σ I :: ⟨64⟩ ::
        dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (dentVatRefundCallMem mem σ I) (UInt256.ofNat 8) ByteArray.empty
      (cA, σ) k' C' := by
  let rawVat := flipperSlotWord ⟨2⟩ σ I
  let rawPacked := flipperSlotWord (bidPackedSlotOfWord (dentId I)) σ I
  let base := solcMappingSlot ⟨1⟩ (dentId I)
  let memHash := dentVatHashMem mem I
  let mem1 := writeWord memHash 128 yankVatMoveSelectorWord
  let mem2 := writeWord mem1 132 (solcSourceWord I)
  let mem3 := writeWord mem2 164 (bidGuyWord (dentId I) σ I)
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hguyCleanLeft :
      UInt256.land solcAddrMask rawPacked = bidGuyWord (dentId I) σ I := by
    simpa [rawPacked, bidGuyWord, flipperAddressReturnWord] using
      (u256_land_comm solcAddrMask rawPacked)
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ memHash.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (memHash.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [dentVatHashMem_size hmemSize]; decide) (by decide)
      (dentVatHashMem_read64 hmemSize hmemRead64)
  have rd4770 := evm_run h with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k4771, C4771, rd4771raw⟩ := rd4770.sload (by native_decide) (by evm_ov)
  have rd4771 : RD flipperBytecode I g s0 ⟨4771⟩
      [rawVat, ⟨2⟩, dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4771 C4771 := by
    simpa [rawVat, flipperSlotWord, solcSlotWord] using rd4771raw
  have rd4789pre := evm_run rd4771 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 memHash (UInt256.ofNat 3)
      (by native_decide) mem_cost (by
        dsimp [memHash, dentVatHashMem, twoWordHashMem, wordAt32Mem, wordAt0Mem]
        rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [memHash, dentVatHashMem, base, bidBaseOfWord] using
        dentVatHashMem_solcMappingSlot hmemSize)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k4790, C4790, rd4790raw⟩ := rd4789pre.sload (by native_decide) (by evm_ov)
  have rd4790 : RD flipperBytecode I g s0 ⟨4790⟩
      (rawPacked :: ⟨0⟩ :: rawVat :: ⟨64⟩ :: dentBid I :: dentLot I ::
        dentId I :: ret :: sel :: [])
      memHash (UInt256.ofNat 3) ByteArray.empty (cA, σ) k4790 C4790 := by
    have hslotAdd : (⟨2⟩ : UInt256) + base = bidPackedSlotOfWord (dentId I) := by
      simpa [base, bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [rawPacked, flipperSlotWord, hslotAdd] using rd4790raw
  have rd4808 := evm_run rd4790 with [
    raw dup4 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨3140843579⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 mem1 (UInt256.ofNat 5)
      (by native_decide) mem_cost (by
        dsimp [mem1, yankVatMoveSelectorWord, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 mem2 (UInt256.ofNat 6)
      (by native_decide) mem_cost (by
        dsimp [mem1, mem2, solcSourceWord, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov)]
  have rd4824 := evm_run rd4808 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 mem3 (UInt256.ofNat 7)
      (by native_decide) mem_cost (by
        rw [hmask160, hguyCleanLeft]
        dsimp [mem2, mem3, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov)]
  have rd4831 := evm_run rd4824 with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 (dentVatRefundCallMem mem σ I) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by
        dsimp [mem1, mem2, mem3, dentVatRefundCallMem, dentVatHashMem,
          Reasoning.Theory.writeWord, writeCascade]
        rfl) (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa [rawVat] using rd4831⟩

theorem flipperDentX_toRefundExtcodesizeGuard {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcaller : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
    (h : RD flipperBytecode I g s0 ⟨4733⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4857⟩
      (flipperVatTargetWord σ I :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (dentVatRefundCallMem (twoWordHashMem (dentId I) ⟨1⟩ mem) σ I)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k' C' := by
  let memHash := twoWordHashMem (dentId I) ⟨1⟩ mem
  have hhashSize : memHash.size = 96 := by
    dsimp [memHash]
    exact twoWordHashMem_size_96 (dentId I) ⟨1⟩ hmemSize
  have hhashRead64 : memHash.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memHash]
    exact twoWordHashMem_read64 (dentId I) ⟨1⟩ hmemSize hmemRead64
  have hvatClean :
      UInt256.land (flipperSlotWord ⟨2⟩ σ I) solcAddrMask = flipperVatTargetWord σ I := by
    simp [flipperVatTargetWord, flipperAddressReturnWord]
  have hmload64Refund :
      (if (⟨64⟩ : UInt256).toNat ≥ (dentVatRefundCallMem memHash σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((dentVatRefundCallMem memHash σ I).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [dentVatRefundCallMem_size hhashSize]; decide) (by decide)
      (dentVatRefundCallMem_read64 hhashSize hhashRead64)
  obtain ⟨_, _, rd4767⟩ := flipperDentX_takeRefundBranch hmemSize hcaller h
  obtain ⟨_, _, rd4831⟩ := flipperDentX_refundCalldataReady hhashSize hhashRead64 rd4767
  have rd4857 := evm_run rd4831 with [
    raw swap4 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Refund (by decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 ⟨3140843579⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hsubAdd : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨100⟩ = ⟨100⟩ := by
    native_decide
  have hadd : (⟨128⟩ : UInt256) + ⟨100⟩ = ⟨228⟩ := by
    native_decide
  rw [hsubAdd, hadd, hvatClean] at rd4857
  exact ⟨_, _, by simpa [memHash] using rd4857⟩

theorem flipperDentX_refundNoCode {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcaller : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨4733⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd4857⟩ :=
    flipperDentX_toRefundExtcodesizeGuard hmemSize hmemRead64 hcaller h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4857⟩) (okPc := ⟨4869⟩) rd4857
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem flipperDentX_toRefundCall {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcaller : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨4733⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ gasWord k' C', RD flipperBytecode I g s0 ⟨4872⟩
      (gasWord :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (dentVatRefundCallMem (twoWordHashMem (dentId I) ⟨1⟩ mem) σ I)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd4857⟩ :=
    flipperDentX_toRefundExtcodesizeGuard hmemSize hmemRead64 hcaller h
  obtain ⟨gasWord, k4872, C4872, rd4872⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4857⟩) (okPc := ⟨4869⟩) rd4857
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k4872, C4872, by simpa using rd4872⟩

theorem flipperDentX_refundDepthLimit {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcaller : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = (1024 : Fin 1025))
    (h : RD flipperBytecode I g s0 ⟨4733⟩ [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4873⟩
      (⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (dentVatRefundCallMem (twoWordHashMem (dentId I) ⟨1⟩ mem) σ I)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨gasWord, _, _, rd4872⟩ :=
    flipperDentX_toRefundCall hmemSize hmemRead64 hcaller hcodeSize h
  obtain ⟨k4873, C4873, rd4873raw⟩ :=
    RD.callDepthLimit rd4872 (by native_decide) hdepth (by evm_ov)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
    native_decide
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  have rd4873 : RD flipperBytecode I g s0 ⟨4873⟩
      (⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (ByteArray.empty.write 0
        (dentVatRefundCallMem (twoWordHashMem (dentId I) ⟨1⟩ mem) σ I) 128
        (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k4873 C4873 := by
    simpa using haw ▸ rd4873raw
  rw [hmin, byteArray_write_len_zero] at rd4873
  exact ⟨_, _, rd4873⟩

theorem flipperDentX_refundPostCall
    {cA0 gh bl σbase σ₀ A I} {g : UInt256}
    {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap} {Acur : Substate}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcaller : solcSourceWord I ≠ bidGuyWord (dentId I) σ I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨4733⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨4873⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: ⟨3140843579⟩ ::
          flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
        (dentVatRefundCallMem (twoWordHashMem (dentId I) ⟨1⟩ mem) σ I)
        (UInt256.ofNat 8) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ, substate := Acur, createdAccounts := cA })
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (dentRefundMoveArgValsOf
          ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA }) I)
        (z,
          { { initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA } with
            accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd4872⟩ :=
    flipperDentX_toRefundCall hmemSize hmemRead64 hcaller hcodeSize h
  obtain ⟨cA', σ', z, out, A_in, callGas, k4873, C4873, hΘpack, rd4873raw,
      houtsz⟩ :=
    RD.call rd4872 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k4873, C4873, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
      native_decide
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      rfl
    have rd4873 : RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨4873⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: ⟨3140843579⟩ ::
          flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
        (out.write 0
          (dentVatRefundCallMem (twoWordHashMem (dentId I) ⟨1⟩ mem) σ I) 128
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k4873 C4873 :=
      haw ▸ rd4873raw
    rw [hmin, byteArray_write_len_zero] at rd4873
    exact rd4873
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := flipperVatTargetWord σ I)
      (mem := dentVatRefundCallMem (twoWordHashMem (dentId I) ⟨1⟩ mem) σ I)
      (inOff := ⟨128⟩) (inSize := ⟨100⟩)
      (fun hdepthEq => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [initState] using hdepthEq
        exact absurd hdepth (by rw [hEq]; decide))
      (flipperVatEvmAddress_eq_target_of_accountMapEquiv (accountMapEquiv.refl σ))
      ?_ ?_
    · have hhashSize :
          (twoWordHashMem (dentId I) ⟨1⟩ mem).size = 96 :=
        twoWordHashMem_size_96 (dentId I) ⟨1⟩ hmemSize
      simpa [dentRefundMoveArgValsOf, initState, flipperSlotWord, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        bidGuyWord, bidPackedSlotOfWord, flipperAddressReturnWord]
        using dentVatRefundCallMem_encode (mem := twoWordHashMem (dentId I) ⟨1⟩ mem)
          (σ := σ) (I := I) hhashSize
    · simpa [initState, hperm] using hΘ

theorem flipperDentX_refundCallFailure {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector bid lot : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨4873⟩
      (⟨0⟩ :: ⟨228⟩ :: selector :: target :: bid :: lot :: id :: ret :: sel :: [])
      mem aw out acc k C)
    (houtsz : out.size < UInt256.size) :
    RDrev flipperBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨4873⟩) (okPc := ⟨4889⟩) h
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtsz (by simp)

theorem flipperDentX_refundCallSuccessToStoreStart {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector bid lot : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨4873⟩
      (⟨1⟩ :: ⟨228⟩ :: selector :: target :: bid :: lot :: id :: ret :: sel :: [])
      mem aw out acc k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4893⟩
      (target :: bid :: lot :: id :: ret :: sel :: []) mem aw out acc k' C' := by
  obtain ⟨_, _, rd4889⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨4873⟩) (okPc := ⟨4889⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp)
  have rd4893 := evm_run rd4889 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd4893⟩

theorem flipperDentX_storeRefundGuyToFluxStart {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {target ret sel : UInt256}
    (hperm : I.perm = true)
    (hmemSize : 64 ≤ mem.size)
    (h : RD flipperBytecode I g s0 ⟨4893⟩
      [target, dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 8) out (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨4927⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      (twoWordHashMem (dentId I) ⟨1⟩ mem) (UInt256.ofNat 8) out
      (cA, dentAfterRefundMap σ I) k' C' := by
  let mem1 := wordAt0Mem (dentId I) mem
  let mem2 := twoWordHashMem (dentId I) ⟨1⟩ mem
  let slot := bidPackedSlotOfWord (dentId I)
  let old := flipperSlotWord slot σ I
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hstoredRaw :
      UInt256.lor (solcSourceWord I)
          (UInt256.land (UInt256.lnot solcAddrMask) old) =
        setAddressOffset0Word old (solcSourceWord I) := by
    have hsourceClean :
        UInt256.land (solcSourceWord I) solcAddrMask = solcSourceWord I :=
      solcAddrMask_clean (solcSourceWord_canonical I)
    calc
      UInt256.lor (solcSourceWord I)
          (UInt256.land (UInt256.lnot solcAddrMask) old) =
          UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) old)
            (solcSourceWord I) := by
            exact u256_lor_comm _ _
      _ = UInt256.lor (UInt256.land old (UInt256.lnot solcAddrMask))
            (UInt256.land (solcSourceWord I) solcAddrMask) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) old, hsourceClean]
      _ = setAddressOffset0Word old (solcSourceWord I) := by
            rfl
  have rd4910 := evm_run h with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 mem1 (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 mem2 (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (dentId I)) (UInt256.ofNat 8)
      (by native_decide) mem_cost
      (by
        simpa [mem2, bidBaseOfWord] using
          tendTwoWordHashMem_solcMappingSlot_of_size_ge ⟨1⟩ (dentId I) hmemSize)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k4912, C4912, rd4912raw⟩ := rd4910.sload (by native_decide) (by evm_ov)
  have rd4912 : RD flipperBytecode I g s0 ⟨4912⟩
      [old, slot, target, dentBid I, dentLot I, dentId I, ret, sel]
      mem2 (UInt256.ofNat 8) out (cA, σ) k4912 C4912 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (dentId I) = slot := by
      simpa [slot, bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (dentId I)))
    simpa [old, slot, flipperSlotWord, solcSlotWord, hslotAdd] using rd4912raw
  have rd4925 := evm_run rd4912 with [
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
  rw [hmask160, hstoredRaw] at rd4925
  obtain ⟨k4926, C4926, rd4926raw⟩ := rd4925.sstore hperm (by native_decide) (by evm_ov)
  have rd4926 : RD flipperBytecode I g s0 ⟨4926⟩
      [target, dentBid I, dentLot I, dentId I, ret, sel]
      mem2 (UInt256.ofNat 8) out (cA, dentAfterRefundMap σ I) k4926 C4926 := by
    simpa [dentAfterRefundMap, old, slot, flipperSlotWord] using rd4926raw
  exact ⟨_, _, evm_run rd4926 with [
    raw pop (by native_decide) (by evm_ov)]⟩

theorem dentVatHashMem_size_228 {mem : ByteArray} (I : ExecutionEnv)
    (hmemSize : mem.size = 228) :
    (dentVatHashMem mem I).size = 228 := by
  unfold dentVatHashMem
  rw [tendTwoWordHashMem_size_of_size_ge]
  · exact hmemSize
  · rw [hmemSize]
    norm_num

theorem dentVatHashMem_read64_228 {mem : ByteArray} (I : ExecutionEnv)
    (hmemSize : mem.size = 228)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dentVatHashMem mem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dentVatHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  change (writeWord (writeWord mem 0 (dentId I)) 32 (⟨1⟩ : UInt256)).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩
  have h0size : (writeWord mem 0 (dentId I)).size = 228 := by
    rw [writeWord_size]
    · rw [hmemSize]; native_decide
    · rw [hmemSize]; native_decide
  rw [writeWord_read_preserved]
  · rw [writeWord_read_preserved]
    · exact hmemRead64
    · rw [hmemSize]; native_decide
    · right
      rw [hmemSize]
      constructor <;> omega
  · rw [h0size]; native_decide
  · right
    rw [h0size]
    constructor <;> omega

theorem dentVatFluxCallMem_size_228 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 228) :
    (dentVatFluxCallMem mem σ I).size = 260 := by
  rw [dentVatFluxCallMem_eq_cascade]
  exact writeCascade_size_of_base (dentVatHashMem mem I)
    [(128, dentVatFluxSelectorWord),
     (132, flipperSlotWord ⟨3⟩ σ I),
     (164, EVM.word I.codeOwner.val),
     (196, bidUsrWord (dentId I) σ I),
     (228, UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))]
    (dentVatHashMem_size_228 I hmemSize)
    (by simp [WriteGapsOk] <;> native_decide)
    (by norm_num [writeCascadeSize])

theorem dentVatFluxCallMem_read64_228 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 228)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dentVatFluxCallMem mem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [dentVatFluxCallMem_eq_cascade]
  rw [writeCascade_read_preserved_of_base (dentVatHashMem mem I)
    [(128, dentVatFluxSelectorWord),
     (132, flipperSlotWord ⟨3⟩ σ I),
     (164, EVM.word I.codeOwner.val),
     (196, bidUsrWord (dentId I) σ I),
     (228, UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))]
    (dentVatHashMem_size_228 I hmemSize)
    (by simp [WindowDisjointFromWrites] <;> native_decide)]
  exact dentVatHashMem_read64_228 I hmemSize hmemRead64

theorem dentVatFluxCallMem_read128_4_228 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 228) :
    (dentVatFluxCallMem mem σ I).readWithPadding 128 4 = vatFluxSelector := by
  rw [dentVatFluxCallMem_eq_cascade]
  rw [writeCascade_read_window_of_head (dentVatHashMem mem I) 128 0 4
    dentVatFluxSelectorWord
    [(132, flipperSlotWord ⟨3⟩ σ I),
     (164, EVM.word I.codeOwner.val),
     (196, bidUsrWord (dentId I) σ I),
     (228, UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))]
    (by rw [dentVatHashMem_size_228 I hmemSize]; native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)
    (by norm_num) (by norm_num) (by norm_num)]
  exact dentVatFluxSelectorWord_prefix

theorem dentVatFluxCallMem_read132_228 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 228) :
    (dentVatFluxCallMem mem σ I).readWithPadding 132 32 =
      UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I) := by
  rw [dentVatFluxCallMem_eq_cascade, writeCascade_cons]
  have hbase :
      (writeWord (dentVatHashMem mem I) 128 dentVatFluxSelectorWord).size = 228 := by
    rw [writeWord_size]
    · rw [dentVatHashMem_size_228 I hmemSize]; native_decide
    · rw [dentVatHashMem_size_228 I hmemSize]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord (dentVatHashMem mem I) 128 dentVatFluxSelectorWord)
    (base := 228) (off := 132) (word := flipperSlotWord ⟨3⟩ σ I)
    (rest := [(164, EVM.word I.codeOwner.val),
      (196, bidUsrWord (dentId I) σ I),
      (228, UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem dentVatFluxCallMem_read164_228 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 228) :
    (dentVatFluxCallMem mem σ I).readWithPadding 164 32 =
      UInt256.toByteArray (EVM.word I.codeOwner.val) := by
  rw [dentVatFluxCallMem_eq_cascade, writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (dentVatHashMem mem I) 128 dentVatFluxSelectorWord
  have hmem1 : mem1.size = 228 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [dentVatHashMem_size_228 I hmemSize]; native_decide
    · rw [dentVatHashMem_size_228 I hmemSize]; native_decide
  have hbase :
      (writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I)).size = 228 := by
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I))
    (base := 228) (off := 164) (word := EVM.word I.codeOwner.val)
    (rest := [(196, bidUsrWord (dentId I) σ I),
      (228, UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem dentVatFluxCallMem_read196_228 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 228) :
    (dentVatFluxCallMem mem σ I).readWithPadding 196 32 =
      UInt256.toByteArray (bidUsrWord (dentId I) σ I) := by
  rw [dentVatFluxCallMem_eq_cascade, writeCascade_cons, writeCascade_cons,
    writeCascade_cons]
  let mem1 := writeWord (dentVatHashMem mem I) 128 dentVatFluxSelectorWord
  let mem2 := writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I)
  have hmem1 : mem1.size = 228 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [dentVatHashMem_size_228 I hmemSize]; native_decide
    · rw [dentVatHashMem_size_228 I hmemSize]; native_decide
  have hmem2 : mem2.size = 228 := by
    dsimp [mem2]
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  have hbase : (writeWord mem2 164 (EVM.word I.codeOwner.val)).size = 228 := by
    rw [writeWord_size]
    · rw [hmem2]; native_decide
    · rw [hmem2]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem2 164 (EVM.word I.codeOwner.val))
    (base := 228) (off := 196) (word := bidUsrWord (dentId I) σ I)
    (rest := [(228, UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem dentVatFluxCallMem_read228_228 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 228) :
    (dentVatFluxCallMem mem σ I).readWithPadding 228 32 =
      UInt256.toByteArray (UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I)) := by
  rw [dentVatFluxCallMem_eq_cascade, writeCascade_cons, writeCascade_cons,
    writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (dentVatHashMem mem I) 128 dentVatFluxSelectorWord
  let mem2 := writeWord mem1 132 (flipperSlotWord ⟨3⟩ σ I)
  let mem3 := writeWord mem2 164 (EVM.word I.codeOwner.val)
  have hmem1 : mem1.size = 228 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [dentVatHashMem_size_228 I hmemSize]; native_decide
    · rw [dentVatHashMem_size_228 I hmemSize]; native_decide
  have hmem2 : mem2.size = 228 := by
    dsimp [mem2]
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  have hmem3 : mem3.size = 228 := by
    dsimp [mem3]
    rw [writeWord_size]
    · rw [hmem2]; native_decide
    · rw [hmem2]; native_decide
  have hbase : (writeWord mem3 196 (bidUsrWord (dentId I) σ I)).size = 228 := by
    rw [writeWord_size]
    · rw [hmem3]; native_decide
    · rw [hmem3]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem3 196 (bidUsrWord (dentId I) σ I))
    (base := 228) (off := 228)
    (word := UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))
    (rest := [])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites])

theorem dentVatFluxCallMem_read_228 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 228) :
    (dentVatFluxCallMem mem σ I).readWithPadding 128 132 =
      vatFluxSelector ++
      UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I) ++
      UInt256.toByteArray (EVM.word I.codeOwner.val) ++
      UInt256.toByteArray (bidUsrWord (dentId I) σ I) ++
      UInt256.toByteArray (UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I)) := by
  rw [byteArray_readWithPadding_split (dentVatFluxCallMem mem σ I) 128 4 128
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dentVatFluxCallMem_size_228 σ I hmemSize])]
  rw [dentVatFluxCallMem_read128_4_228 σ I hmemSize]
  rw [byteArray_readWithPadding_split (dentVatFluxCallMem mem σ I) 132 32 96
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dentVatFluxCallMem_size_228 σ I hmemSize])]
  rw [dentVatFluxCallMem_read132_228 σ I hmemSize]
  rw [byteArray_readWithPadding_split (dentVatFluxCallMem mem σ I) 164 32 64
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dentVatFluxCallMem_size_228 σ I hmemSize])]
  rw [dentVatFluxCallMem_read164_228 σ I hmemSize]
  rw [byteArray_readWithPadding_split (dentVatFluxCallMem mem σ I) 196 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [dentVatFluxCallMem_size_228 σ I hmemSize])]
  rw [dentVatFluxCallMem_read196_228 σ I hmemSize,
    dentVatFluxCallMem_read228_228 σ I hmemSize]
  simp [ByteArray.append_assoc]

theorem dentVatFluxCallMem_encode_228 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 228) :
    config.externalABI.encode? "flux" (dentFluxArgValsMap σ I) =
      some ((dentVatFluxCallMem mem σ I).readWithPadding 128 132) := by
  rw [dentVatFluxCallMem_read_228 σ I hmemSize]
  unfold dentFluxArgValsMap config externalABI
  simp only [if_true]
  unfold ABI.encodeCallWithSelector?
  have husr :
      encodeABIValue? addr
          (.address (AccountAddress.ofNat (bidUsrWord (dentId I) σ I).toNat)) =
        some (UInt256.toByteArray (bidUsrWord (dentId I) σ I)).toList := by
    simpa [bidUsrWord, flipperAddressReturnWord] using
      yankEncodeABIValue_address_word (flipperSlotWord (bidSlotOfWord (dentId I) ⟨3⟩) σ I)
  have hpayload :
      encodeABIValues? [bytes32, addr, addr, uint256]
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (flipperSlotWord ⟨3⟩ σ I)),
          .address I.codeOwner,
          .address (AccountAddress.ofNat (bidUsrWord (dentId I) σ I).toNat),
          .int (Int.ofNat
            (UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I)).toNat)] =
          some (UInt256.toByteArray (flipperSlotWord ⟨3⟩ σ I) ++
            UInt256.toByteArray (EVM.word I.codeOwner.val) ++
            UInt256.toByteArray (bidUsrWord (dentId I) σ I) ++
            UInt256.toByteArray
              (UInt256.sub (bidLotWord (dentId I) σ I) (dentLot I))).toList := by
    unfold encodeABIValues?
    rw [show abiTupleHeadSize? [bytes32, addr, addr, uint256] = some 128 by native_decide]
    simp only [encodeABIValuesFrom?, Option.bind, bind]
    rw [yankEncodeABIValue_bytes32_word, yankEncodeABIValue_this_address, husr,
      yankEncodeABIValue_uint256_word]
    simp [show isDynamicABIType bytes32 = false by native_decide,
      show isDynamicABIType addr = false by native_decide,
      show isDynamicABIType uint256 = false by native_decide,
      ByteArray.append_assoc, byteArray_toList_eq]
  rw [hpayload]
  apply congrArg some
  apply ByteArray.ext
  simp [vatFluxSelector, byteArray_toList_eq, ByteArray.append_assoc]

theorem flipperDentX_toFluxExtcodesizeGuardAw8 {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem rdata : ByteArray}
    (hmemSize : mem.size = 228)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD flipperBytecode I g s0 ⟨4927⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 8) rdata (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨5037⟩
      (flipperVatTargetWord σ I :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
        flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I :: ret :: sel :: [])
      (dentVatFluxCallMem mem σ I) (UInt256.ofNat 9) rdata (cA, σ) k' C' := by
  let rawVat := flipperSlotWord ⟨2⟩ σ I
  let rawIlk := flipperSlotWord ⟨3⟩ σ I
  let rawUsr := flipperSlotWord (bidSlotOfWord (dentId I) ⟨3⟩) σ I
  let rawLot := flipperSlotWord (bidSlotOfWord (dentId I) ⟨1⟩) σ I
  let base := solcMappingSlot ⟨1⟩ (dentId I)
  let memHash := dentVatHashMem mem I
  let memSel := writeWord memHash 128 dentVatFluxSelectorWord
  let memIlk := writeWord memSel 132 rawIlk
  let memThis := writeWord memIlk 164 (EVM.word I.codeOwner.val)
  let memUsr := writeWord memThis 196 (bidUsrWord (dentId I) σ I)
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by
    native_decide
  have hvatClean : UInt256.land rawVat solcAddrMask = flipperVatTargetWord σ I := by
    simp [rawVat, flipperVatTargetWord, flipperAddressReturnWord]
  have husrCleanLeft :
      UInt256.land solcAddrMask rawUsr = bidUsrWord (dentId I) σ I := by
    simpa [rawUsr, bidUsrWord, flipperAddressReturnWord] using
      (u256_land_comm solcAddrMask rawUsr)
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ (dentVatHashMem mem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((dentVatHashMem mem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [dentVatHashMem_size_228 I hmemSize]; decide) (by decide)
      (dentVatHashMem_read64_228 I hmemSize hmemRead64)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (dentVatFluxCallMem mem σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((dentVatFluxCallMem mem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [dentVatFluxCallMem_size_228 σ I hmemSize]; decide)
      (by decide) (dentVatFluxCallMem_read64_228 σ I hmemSize hmemRead64)
  have rd4930pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k4931, C4931, rd4931raw⟩ := rd4930pre.sload (by native_decide) (by evm_ov)
  have rd4931 : RD flipperBytecode I g s0 ⟨4931⟩
      [rawVat, dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 8) rdata (cA, σ) k4931 C4931 := by
    simpa [rawVat, flipperSlotWord, solcSlotWord] using rd4931raw
  have rd4934 := evm_run rd4931 with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k4935, C4935, rd4935raw⟩ := rd4934.sload (by native_decide) (by evm_ov)
  have rd4935 : RD flipperBytecode I g s0 ⟨4935⟩
      [rawIlk, ⟨3⟩, rawVat, dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 8) rdata (cA, σ) k4935 C4935 := by
    simpa [rawIlk, flipperSlotWord, solcSlotWord] using rd4935raw
  have rd4954 := evm_run rd4935 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (dentId I) mem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 memHash (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 8)
      (by native_decide) mem_cost
      (by
        have hmemGe : 64 ≤ mem.size := by
          rw [hmemSize]
          norm_num
        simpa [memHash, base, dentVatHashMem, bidBaseOfWord] using
          (tendTwoWordHashMem_solcMappingSlot_of_size_ge (mem := mem) ⟨1⟩
            (dentId I) hmemGe))
      (by decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k4956, C4956, rd4956raw⟩ := rd4954.sload (by native_decide) (by evm_ov)
  have rd4956 : RD flipperBytecode I g s0 ⟨4956⟩
      [rawUsr, ⟨64⟩, ⟨1⟩, ⟨0⟩, rawIlk, base, rawVat, dentBid I,
        dentLot I, dentId I, ret, sel]
      memHash (UInt256.ofNat 8) rdata (cA, σ) k4956 C4956 := by
    have hslotAdd : base + (⟨3⟩ : UInt256) = bidSlotOfWord (dentId I) ⟨3⟩ := by
      simp [base, bidSlotOfWord, bidBaseOfWord]
    simpa [rawUsr, flipperSlotWord, hslotAdd] using rd4956raw
  have rd4959 := evm_run rd4956 with [
    raw swap5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k4961, C4961, rd4961raw⟩ := rd4959.sload (by native_decide) (by evm_ov)
  have rd4961 : RD flipperBytecode I g s0 ⟨4961⟩
      [rawLot, ⟨64⟩, ⟨0⟩, rawIlk, rawUsr, rawVat, dentBid I,
        dentLot I, dentId I, ret, sel]
      memHash (UInt256.ofNat 8) rdata (cA, σ) k4961 C4961 := by
    have hslotAdd :
        (⟨1⟩ : UInt256) + base = bidSlotOfWord (dentId I) ⟨1⟩ := by
      simpa [base, bidSlotOfWord, bidBaseOfWord] using
        (u256_add_comm (⟨1⟩ : UInt256) (solcMappingSlot ⟨1⟩ (dentId I)))
    simpa [rawLot, flipperSlotWord, hslotAdd] using rd4961raw
  have rd4972 := evm_run rd4961 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨814276375⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨225⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 memSel (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4980 := evm_run rd4972 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw mstore 0 memIlk (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4981 := RD.address rd4980 (by native_decide) (by evm_ov)
  have rd4986 := evm_run rd4981 with [
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 memThis (UInt256.ofNat 8)
      (by native_decide) mem_cost (by
        dsimp [memThis]
        rfl) (by decide) (by evm_ov)]
  have rd5002 := evm_run rd4986 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 memUsr (UInt256.ofNat 8)
      (by native_decide) mem_cost (by
        rw [hmask160, husrCleanLeft]
        dsimp [memUsr]
        rfl) (by decide) (by evm_ov)]
  have rd5010 := evm_run rd5002 with [
    raw dup8 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (dentVatFluxCallMem mem σ I) (UInt256.ofNat 9)
      (by native_decide) mem_cost (by
        dsimp [memUsr, memThis, memIlk, memSel, memHash, dentVatFluxCallMem,
          dentVatHashMem, writeCascade, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov)]
  have rd5037 := evm_run rd5010 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 ⟨1628552750⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨132⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  rw [hmask160, hvatClean] at rd5037
  exact ⟨_, _, by simpa [rawVat] using rd5037⟩

theorem flipperDentX_fluxNoCodeAw8 {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem out : ByteArray}
    (hmemSize : mem.size = 228)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨4927⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 8) out (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd5037⟩ := flipperDentX_toFluxExtcodesizeGuardAw8
    hmemSize hmemRead64 h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨5037⟩) (okPc := ⟨5049⟩) rd5037
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem flipperDentX_toFluxCallAw8 {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem out : ByteArray}
    (hmemSize : mem.size = 228)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨4927⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 8) out (cA, σ) k C) :
    ∃ gasWord k' C', RD flipperBytecode I g s0 ⟨5052⟩
      (gasWord :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨132⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
        flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I ::
        ret :: sel :: [])
      (dentVatFluxCallMem mem σ I) (UInt256.ofNat 9) out (cA, σ) k' C' := by
  obtain ⟨_, _, rd5037⟩ := flipperDentX_toFluxExtcodesizeGuardAw8
    hmemSize hmemRead64 h
  obtain ⟨gasWord, k5052, C5052, rd5052⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨5037⟩) (okPc := ⟨5049⟩) rd5037
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k5052, C5052, by simpa using rd5052⟩

theorem flipperDentX_fluxPostCallAw8
    {cA0 gh bl σbase σ₀ A I} {g : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {Acur : Substate}
    {k C : ℕ} {mem out0 : ByteArray} {ret sel : UInt256}
    (hmemSize : mem.size = 228)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨4927⟩
      [dentBid I, dentLot I, dentId I, ret, sel]
      mem (UInt256.ofNat 8) out0 (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨5053⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: ⟨1628552750⟩ ::
          flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I ::
          ret :: sel :: [])
        (dentVatFluxCallMem mem σ I) (UInt256.ofNat 9) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ, substate := Acur, createdAccounts := cA })
        (EVM.address (flipperVatAddress σ I)) "flux" 0
        (dentFluxArgValsOf
          ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA })
          I)
        (z,
          { { initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA } with
            accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd5052⟩ :=
    flipperDentX_toFluxCallAw8 hmemSize hmemRead64 hcodeSize h
  obtain ⟨cA', σ', z, out, A_in, callGas, k5053, C5053, hΘpack, rd5053raw,
      houtsz⟩ :=
    RD.call rd5052 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k5053, C5053, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
          (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 9 := by
      native_decide
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      rfl
    have rd5053 : RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨5053⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: ⟨1628552750⟩ ::
          flipperVatTargetWord σ I :: dentBid I :: dentLot I :: dentId I ::
          ret :: sel :: [])
        (out.write 0 (dentVatFluxCallMem mem σ I) 128
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 9) out (cA', σ') k5053 C5053 :=
      haw ▸ rd5053raw
    rw [hmin, byteArray_write_len_zero] at rd5053
    exact rd5053
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := flipperVatTargetWord σ I)
      (mem := dentVatFluxCallMem mem σ I) (inOff := ⟨128⟩) (inSize := ⟨132⟩)
      (fun hdepthEq => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [initState] using hdepthEq
        exact absurd hdepth (by rw [hEq]; decide))
      (flipperVatEvmAddress_eq_target_of_accountMapEquiv (accountMapEquiv.refl σ))
      ?_ ?_
    · simpa [dentFluxArgValsOf, dentFluxArgValsMap, initState, flipperSlotWord,
        solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        bidUsrWord, bidLotWord, bidSlotOfWord, bidBaseOfWord, flipperAddressReturnWord]
        using dentVatFluxCallMem_encode_228 (mem := mem) (σ := σ) (I := I) hmemSize
    · simpa [initState, hperm] using hΘ

end Benchmarks.Dss.Flipper
