import Benchmarks.Dss.Flipper.Kick

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

theorem test_kickFieldHashMem_solcMappingSlot (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC ((kickFieldHashMem σ I).readWithPadding 0 64))) =
      bidBaseOfWord (kickIdWord σ I) := by
  unfold kickFieldHashMem
  simpa [bidBaseOfWord] using
    twoWordHashMem_solcMappingSlot ⟨1⟩ (kickIdWord σ I)
      (twoWordHashMem_size_96 (kickIdWord σ I) ⟨1⟩
        (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size))

theorem test_flipperKickDecodePushMask2258 :
    decode flipperBytecode (⟨2258⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  decide +native

theorem test_flipperKickX_toEndStore {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hperm : I.perm = true)
    (h : RD flipperBytecode I g s0 ⟨2235⟩
      [kickNow I + kickTauWord (kickAfterGuyMap σ I) I, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickBidHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterGuyMap σ I) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2293⟩
      [bidBaseOfWord (kickIdWord σ I), ⟨64⟩, ⟨0⟩, ⟨2⟩, kickIdWord σ I,
        kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterEndMap σ I) k' C' := by
  let mem0 := kickBidHashMem σ I
  let mem1 := wordAt0Mem (kickIdWord σ I) mem0
  have rd2246 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 mem1 (UInt256.ofNat 3) (by decide +native)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw mstore 0 (kickFieldHashMem σ I) (UInt256.ofNat 3) (by decide +native)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd2250 := evm_run rd2246 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (kickIdWord σ I)) (UInt256.ofNat 3)
      (by decide +native) mem_cost (test_kickFieldHashMem_solcMappingSlot σ I)
      (by decide) (by evm_ov)]
  have rd2256 := evm_run rd2250 with [
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  obtain ⟨k2257, C2257, rd2257raw⟩ := rd2256.sload (by decide +native) (by evm_ov)
  have rd2258 : RD flipperBytecode I g s0 ⟨2258⟩
      [solcSlotWord (kickAfterGuyMap σ I) I (bidBaseOfWord (kickIdWord σ I) + ⟨2⟩),
        bidBaseOfWord (kickIdWord σ I) + ⟨2⟩, ⟨2⟩,
        bidBaseOfWord (kickIdWord σ I), ⟨64⟩, ⟨0⟩,
        kickNow I + kickTauWord (kickAfterGuyMap σ I) I, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterGuyMap σ I) k2257 C2257 := by
    simpa [solcSlotWord] using rd2257raw
  have rd2291 := evm_run rd2258 with [
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by decide +native)
      test_flipperKickDecodePushMask2258
      (by evm_ov),
    raw swap7 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap7 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨208⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw mul (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨208⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap7 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap6 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap6 (by decide +native) (by evm_ov),
    raw or (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov)]
  have hdiv26 :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩ = uint48Divisor26 := by
    decide +native
  have hstoredRaw :
      UInt256.lor
        (UInt256.land
          (solcSlotWord (kickAfterGuyMap σ I) I (bidBaseOfWord (kickIdWord σ I) + ⟨2⟩))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩) ⟨1⟩))
        (UInt256.mul
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)
          (UInt256.land uint48Mask
            (kickNow I + kickTauWord (kickAfterGuyMap σ I) I))) =
        kickEndStoredWord (kickIdWord σ I) (kickAfterGuyMap σ I) I := by
    calc
      UInt256.lor
        (UInt256.land
          (solcSlotWord (kickAfterGuyMap σ I) I (bidBaseOfWord (kickIdWord σ I) + ⟨2⟩))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩) ⟨1⟩))
        (UInt256.mul
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)
          (UInt256.land uint48Mask
            (kickNow I + kickTauWord (kickAfterGuyMap σ I) I))) =
        UInt256.lor
          (UInt256.land
            (solcSlotWord (kickAfterGuyMap σ I) I (bidBaseOfWord (kickIdWord σ I) + ⟨2⟩))
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩) ⟨1⟩))
          (UInt256.mul
            (UInt256.land (kickNow I + kickTauWord (kickAfterGuyMap σ I) I) uint48Mask)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)) := by
          rw [u256_land_comm uint48Mask
            (kickNow I + kickTauWord (kickAfterGuyMap σ I) I), u256_mul_comm]
      _ =
        setUint48Offset26Word
          (solcSlotWord (kickAfterGuyMap σ I) I (bidBaseOfWord (kickIdWord σ I) + ⟨2⟩))
          (UInt256.land (kickNow I + kickTauWord (kickAfterGuyMap σ I) I) uint48Mask) := by
          rw [hdiv26]
          exact Benchmarks.Dss.Flipper.setUint48Offset26RuntimeWord
            (solcSlotWord (kickAfterGuyMap σ I) I (bidBaseOfWord (kickIdWord σ I) + ⟨2⟩))
            (kickNow I + kickTauWord (kickAfterGuyMap σ I) I)
      _ = kickEndStoredWord (kickIdWord σ I) (kickAfterGuyMap σ I) I := by
          rw [kickEndStoredWord, flipperSlotWord]
          change setUint48Offset26Word
              (solcSlotWord (kickAfterGuyMap σ I) I (bidBaseOfWord (kickIdWord σ I) + ⟨2⟩))
              (UInt256.land (kickNow I + kickTauWord (kickAfterGuyMap σ I) I) uint48Mask) =
            setUint48Offset26Word
              (solcSlotWord (kickAfterGuyMap σ I) I (bidPackedSlotOfWord (kickIdWord σ I)))
              (kickEndNewWord (kickAfterGuyMap σ I) I)
          rw [show bidBaseOfWord (kickIdWord σ I) + ⟨2⟩ =
              bidPackedSlotOfWord (kickIdWord σ I) from rfl]
          rw [kickEndNewWord_fullTimestampAdd]
  rw [hstoredRaw] at rd2291
  obtain ⟨k2292, C2292, rd2292⟩ : ∃ k' C',
      RD flipperBytecode I g s0 ⟨2292⟩
        [bidBaseOfWord (kickIdWord σ I) + ⟨2⟩,
          kickEndStoredWord (kickIdWord σ I) (kickAfterGuyMap σ I) I,
          bidBaseOfWord (kickIdWord σ I), ⟨64⟩, ⟨0⟩, ⟨2⟩, kickIdWord σ I,
          kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
        (kickFieldHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
        (cA, kickAfterGuyMap σ I) k' C' := by
    exact ⟨_, _, by simpa only using rd2291⟩
  obtain ⟨k2293, C2293, rd2293raw⟩ := rd2292.sstore hperm (by decide +native) (by evm_ov)
  exact ⟨k2293, C2293, by
    have hmap :
        sstoreAccountMap I.codeOwner (kickAfterGuyMap σ I)
            (bidBaseOfWord (kickIdWord σ I) + ⟨2⟩)
            (kickEndStoredWord (kickIdWord σ I) (kickAfterGuyMap σ I) I) =
          kickAfterEndMap σ I := by
      rfl
    rw [← hmap]
    exact rd2293raw⟩

theorem test_kickUsrKey_clean (I : ExecutionEnv) :
    UInt256.land (kickUsrKey I) solcAddrMask = kickUsrKey I := by
  have hcanon : (kickUsrKey I).toNat < EVM.addressModulus := by
    simpa [kickUsrKey, u256_land_comm] using
      solcAddrMask_result_canonical (calldataWord I.calldata 4)
  exact solcAddrMask_clean hcanon

theorem test_flipperKickX_toUsrStore {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hperm : I.perm = true)
    (h : RD flipperBytecode I g s0 ⟨2293⟩
      [bidBaseOfWord (kickIdWord σ I), ⟨64⟩, ⟨0⟩, ⟨2⟩, kickIdWord σ I,
        kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterEndMap σ I) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2327⟩
      [UInt256.lnot solcAddrMask, solcAddrMask, ⟨3⟩, bidBaseOfWord (kickIdWord σ I),
        ⟨64⟩, ⟨0⟩, ⟨2⟩, kickIdWord σ I, kickBid I, kickLot I, kickTab I,
        kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterUsrMap σ I) k' C' := by
  have rd2298 := evm_run h with [
    raw push1 ⟨3⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  obtain ⟨k2299, C2299, rd2299raw⟩ := rd2298.sload (by decide +native) (by evm_ov)
  have rd2300 : RD flipperBytecode I g s0 ⟨2300⟩
      [solcSlotWord (kickAfterEndMap σ I) I (bidBaseOfWord (kickIdWord σ I) + ⟨3⟩),
        bidBaseOfWord (kickIdWord σ I) + ⟨3⟩, ⟨3⟩,
        bidBaseOfWord (kickIdWord σ I), ⟨64⟩, ⟨0⟩, ⟨2⟩, kickIdWord σ I,
        kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterEndMap σ I) k2299 C2299 := by
    simpa [solcSlotWord] using rd2299raw
  have rd2325 := evm_run rd2300 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup15 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw not (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw or (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov)]
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have hstoredRaw :
      UInt256.lor
        (UInt256.land (UInt256.lnot solcAddrMask)
          (solcSlotWord (kickAfterEndMap σ I) I
            (bidBaseOfWord (kickIdWord σ I) + ⟨3⟩)))
        (UInt256.land (kickUsrKey I) solcAddrMask) =
        kickUsrStoredWord σ I := by
    calc
      UInt256.lor
        (UInt256.land (UInt256.lnot solcAddrMask)
          (solcSlotWord (kickAfterEndMap σ I) I
            (bidBaseOfWord (kickIdWord σ I) + ⟨3⟩)))
        (UInt256.land (kickUsrKey I) solcAddrMask) =
        UInt256.lor
          (UInt256.land
            (solcSlotWord (kickAfterEndMap σ I) I
              (bidBaseOfWord (kickIdWord σ I) + ⟨3⟩))
            (UInt256.lnot solcAddrMask))
          (UInt256.land (kickUsrKey I) solcAddrMask) := by
          rw [u256_land_comm (UInt256.lnot solcAddrMask)
            (solcSlotWord (kickAfterEndMap σ I) I
              (bidBaseOfWord (kickIdWord σ I) + ⟨3⟩))]
      _ = setAddressOffset0Word
          (solcSlotWord (kickAfterEndMap σ I) I
            (bidBaseOfWord (kickIdWord σ I) + ⟨3⟩))
          (kickUsrKey I) := by
          rfl
      _ = kickUsrStoredWord σ I := by
          rw [kickUsrStoredWord, flipperSlotWord]
  rw [hmask160] at rd2325
  rw [hstoredRaw] at rd2325
  obtain ⟨k2326, C2326, rd2326⟩ : ∃ k' C',
      RD flipperBytecode I g s0 ⟨2326⟩
        [bidBaseOfWord (kickIdWord σ I) + ⟨3⟩, kickUsrStoredWord σ I,
          UInt256.lnot solcAddrMask, solcAddrMask, ⟨3⟩, bidBaseOfWord (kickIdWord σ I),
          ⟨64⟩, ⟨0⟩, ⟨2⟩, kickIdWord σ I, kickBid I, kickLot I, kickTab I,
          kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
        (kickFieldHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
        (cA, kickAfterEndMap σ I) k' C' := by
    exact ⟨_, _, by simpa only using rd2325⟩
  obtain ⟨k2327, C2327, rd2327raw⟩ := rd2326.sstore hperm (by decide +native) (by evm_ov)
  exact ⟨k2327, C2327, by
    have hmap :
        sstoreAccountMap I.codeOwner (kickAfterEndMap σ I)
            (bidBaseOfWord (kickIdWord σ I) + ⟨3⟩) (kickUsrStoredWord σ I) =
          kickAfterUsrMap σ I := by
      rfl
    rw [← hmap]
    exact rd2327raw⟩

theorem test_kickGalKey_clean (I : ExecutionEnv) :
    UInt256.land (kickGalKey I) solcAddrMask = kickGalKey I := by
  have hcanon : (kickGalKey I).toNat < EVM.addressModulus := by
    simpa [kickGalKey, u256_land_comm] using
      solcAddrMask_result_canonical (calldataWord I.calldata 36)
  exact solcAddrMask_clean hcanon

theorem test_flipperKickX_toGalStore {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hperm : I.perm = true)
    (h : RD flipperBytecode I g s0 ⟨2327⟩
      [UInt256.lnot solcAddrMask, solcAddrMask, ⟨3⟩, bidBaseOfWord (kickIdWord σ I),
        ⟨64⟩, ⟨0⟩, ⟨2⟩, kickIdWord σ I, kickBid I, kickLot I, kickTab I,
        kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterUsrMap σ I) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2346⟩
      [⟨4⟩, solcAddrMask, ⟨3⟩, bidBaseOfWord (kickIdWord σ I), ⟨64⟩, ⟨0⟩,
        ⟨2⟩, kickIdWord σ I, kickBid I, kickLot I, kickTab I, kickGalKey I,
        kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterGalMap σ I) k' C' := by
  have rd2333 := evm_run h with [
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  obtain ⟨k2334, C2334, rd2334raw⟩ := rd2333.sload (by decide +native) (by evm_ov)
  have rd2334 : RD flipperBytecode I g s0 ⟨2334⟩
      [solcSlotWord (kickAfterUsrMap σ I) I (bidBaseOfWord (kickIdWord σ I) + ⟨4⟩),
        bidBaseOfWord (kickIdWord σ I) + ⟨4⟩, ⟨4⟩,
        UInt256.lnot solcAddrMask, solcAddrMask, ⟨3⟩,
        bidBaseOfWord (kickIdWord σ I), ⟨64⟩, ⟨0⟩, ⟨2⟩, kickIdWord σ I,
        kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterUsrMap σ I) k2334 C2334 := by
    simpa [solcSlotWord] using rd2334raw
  have rd2345 := evm_run rd2334 with [
    raw dup15 (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw or (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov)]
  have hstoredRaw :
      UInt256.lor
        (UInt256.land (UInt256.lnot solcAddrMask)
          (solcSlotWord (kickAfterUsrMap σ I) I
            (bidBaseOfWord (kickIdWord σ I) + ⟨4⟩)))
        (UInt256.land solcAddrMask (kickGalKey I)) =
        kickGalStoredWord σ I := by
    calc
      UInt256.lor
        (UInt256.land (UInt256.lnot solcAddrMask)
          (solcSlotWord (kickAfterUsrMap σ I) I
            (bidBaseOfWord (kickIdWord σ I) + ⟨4⟩)))
        (UInt256.land solcAddrMask (kickGalKey I)) =
        UInt256.lor
          (UInt256.land (UInt256.lnot solcAddrMask)
            (solcSlotWord (kickAfterUsrMap σ I) I
              (bidBaseOfWord (kickIdWord σ I) + ⟨4⟩)))
          (UInt256.land (kickGalKey I) solcAddrMask) := by
          rw [u256_land_comm solcAddrMask (kickGalKey I)]
      _ = UInt256.lor
          (UInt256.land
            (solcSlotWord (kickAfterUsrMap σ I) I
              (bidBaseOfWord (kickIdWord σ I) + ⟨4⟩))
            (UInt256.lnot solcAddrMask))
          (UInt256.land (kickGalKey I) solcAddrMask) := by
          rw [u256_land_comm (UInt256.lnot solcAddrMask)
            (solcSlotWord (kickAfterUsrMap σ I) I
              (bidBaseOfWord (kickIdWord σ I) + ⟨4⟩))]
      _ = setAddressOffset0Word
          (solcSlotWord (kickAfterUsrMap σ I) I
            (bidBaseOfWord (kickIdWord σ I) + ⟨4⟩))
          (kickGalKey I) := by
          rfl
      _ = kickGalStoredWord σ I := by
          rw [kickGalStoredWord, flipperSlotWord]
  rw [hstoredRaw] at rd2345
  obtain ⟨k2346, C2346, rd2346raw⟩ := rd2345.sstore hperm (by decide +native) (by evm_ov)
  exact ⟨k2346, C2346, by
    have hmap :
        sstoreAccountMap I.codeOwner (kickAfterUsrMap σ I)
            (bidBaseOfWord (kickIdWord σ I) + ⟨4⟩) (kickGalStoredWord σ I) =
          kickAfterGalMap σ I := by
      rfl
    rw [← hmap]
    exact rd2346raw⟩

theorem test_flipperKickX_toTabStore {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hperm : I.perm = true)
    (h : RD flipperBytecode I g s0 ⟨2346⟩
      [⟨4⟩, solcAddrMask, ⟨3⟩, bidBaseOfWord (kickIdWord σ I), ⟨64⟩, ⟨0⟩,
        ⟨2⟩, kickIdWord σ I, kickBid I, kickLot I, kickTab I, kickGalKey I,
        kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterGalMap σ I) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2354⟩
      [solcAddrMask, ⟨3⟩, ⟨4⟩, ⟨64⟩, ⟨0⟩, ⟨2⟩, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, kickAfterTabMap σ I) k' C' := by
  have rd2353 := evm_run h with [
    raw push1 ⟨5⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup11 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  obtain ⟨k2354, C2354, rd2354raw⟩ := rd2353.sstore hperm (by decide +native) (by evm_ov)
  exact ⟨k2354, C2354, by
    have hmap :
        sstoreAccountMap I.codeOwner (kickAfterGalMap σ I)
            (bidBaseOfWord (kickIdWord σ I) + ⟨5⟩) (kickTab I) =
          kickAfterTabMap σ I := by
      rfl
    rw [← hmap]
    exact rd2354raw⟩

theorem test_flipperKickX_toVatCallMem {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out : ByteArray} {sel : UInt256}
    (h : RD flipperBytecode I g s0 ⟨2354⟩
      [solcAddrMask, ⟨3⟩, ⟨4⟩, ⟨64⟩, ⟨0⟩, ⟨2⟩, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) out (cA, kickAfterTabMap σ I) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2393⟩
      [flipperSlotWord ⟨2⟩ (kickAfterTabMap σ I) I, ⟨128⟩, ⟨64⟩, ⟨0⟩,
        solcAddrMask, kickIdWord σ I, kickBid I, kickLot I, kickTab I,
        kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickVatFluxCallMem σ (kickAfterTabMap σ I) I) (UInt256.ofNat 9) out
      (cA, kickAfterTabMap σ I) k' C' := by
  let σcall := kickAfterTabMap σ I
  let rawVat := flipperSlotWord ⟨2⟩ σcall I
  let rawIlk := flipperSlotWord ⟨3⟩ σcall I
  have hmload64Field :
      (if (⟨64⟩ : UInt256).toNat ≥ (kickFieldHashMem σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((kickFieldHashMem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [kickFieldHashMem_size]; decide) (by decide)
      (kickFieldHashMem_read64 σ I)
  have rd2355 := evm_run h with [
    raw swap5 (by decide +native) (by evm_ov)]
  obtain ⟨k2356, C2356, rd2356raw⟩ := rd2355.sload (by decide +native) (by evm_ov)
  have rd2356 : RD flipperBytecode I g s0 ⟨2356⟩
      [rawVat, ⟨3⟩, ⟨4⟩, ⟨64⟩, ⟨0⟩, solcAddrMask, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) out (cA, σcall) k2356 C2356 := by
    simpa [rawVat, σcall, flipperSlotWord, solcSlotWord] using rd2356raw
  have rd2357 := evm_run rd2356 with [
    raw swap1 (by decide +native) (by evm_ov)]
  obtain ⟨k2358, C2358, rd2358raw⟩ := rd2357.sload (by decide +native) (by evm_ov)
  have rd2358 : RD flipperBytecode I g s0 ⟨2358⟩
      [rawIlk, rawVat, ⟨4⟩, ⟨64⟩, ⟨0⟩, solcAddrMask, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) out (cA, σcall) k2358 C2358 := by
    simpa [rawIlk, σcall, flipperSlotWord, solcSlotWord] using rd2358raw
  have rd2374 := evm_run rd2358 with [
    raw dup4 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost hmload64Field (by decide) (by evm_ov),
    raw push4 ⟨814276375⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨225⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 6 (kickVatFluxSelectorMem σ I) (UInt256.ofNat 5)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (kickVatFluxIlkMem σ σcall I) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd2375 := RD.caller rd2374 (by decide +native) (by evm_ov)
  have rd2380 := evm_run rd2375 with [
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (kickVatFluxSenderMem σ σcall I) (UInt256.ofNat 7)
      (by decide +native) mem_cost
      (by
        unfold kickVatFluxSenderMem
        rfl)
      (by decide) (by evm_ov)]
  have rd2381 := RD.address rd2380 (by decide +native) (by evm_ov)
  have rd2386 := evm_run rd2381 with [
    raw push1 ⟨68⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (kickVatFluxThisMem σ σcall I) (UInt256.ofNat 8)
      (by decide +native) mem_cost
      (by
        unfold kickVatFluxThisMem
        rfl)
      (by decide) (by evm_ov)]
  have rd2393 := evm_run rd2386 with [
    raw push1 ⟨100⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup9 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 3 (kickVatFluxCallMem σ σcall I) (UInt256.ofNat 9)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa only [rawVat, σcall] using rd2393⟩

theorem test_flipperKickX_fromVatCallMemToVatMload {cA σ I}
    {g : Sat256} {s0 : State} {k C : ℕ} {out : ByteArray} {sel : UInt256}
    (h : RD flipperBytecode I g s0 ⟨2393⟩
      [flipperSlotWord ⟨2⟩ (kickAfterTabMap σ I) I, ⟨128⟩, ⟨64⟩, ⟨0⟩,
        solcAddrMask, kickIdWord σ I, kickBid I, kickLot I, kickTab I,
        kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickVatFluxCallMem σ (kickAfterTabMap σ I) I) (UInt256.ofNat 9) out
      (cA, kickAfterTabMap σ I) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2395⟩
      [⟨128⟩, ⟨128⟩, flipperSlotWord ⟨2⟩ (kickAfterTabMap σ I) I, ⟨0⟩,
        solcAddrMask, kickIdWord σ I, kickBid I, kickLot I, kickTab I,
        kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickVatFluxCallMem σ (kickAfterTabMap σ I) I) (UInt256.ofNat 9) out
      (cA, kickAfterTabMap σ I) k' C' := by
  let σcall := kickAfterTabMap σ I
  let rawVat := flipperSlotWord ⟨2⟩ σcall I
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (kickVatFluxCallMem σ σcall I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((kickVatFluxCallMem σ σcall I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [kickVatFluxCallMem_size]; decide) (by decide)
      (kickVatFluxCallMem_read64 σ σcall I)
  have h' : RD flipperBytecode I g s0 ⟨2393⟩
      [rawVat, ⟨128⟩, ⟨64⟩, ⟨0⟩, solcAddrMask, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickVatFluxCallMem σ σcall I) (UInt256.ofNat 9) out (cA, σcall) k C := by
    simpa only [rawVat, σcall] using h
  have rd2395 := evm_run h' with [
    raw swap2 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa only [rawVat, σcall] using rd2395⟩

theorem test_flipperKickX_fromVatMloadToMaskedTarget {cA σ I}
    {g : Sat256} {s0 : State} {k C : ℕ} {out : ByteArray} {sel : UInt256}
    (h : RD flipperBytecode I g s0 ⟨2395⟩
      [⟨128⟩, ⟨128⟩, flipperSlotWord ⟨2⟩ (kickAfterTabMap σ I) I, ⟨0⟩,
        solcAddrMask, kickIdWord σ I, kickBid I, kickLot I, kickTab I,
        kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickVatFluxCallMem σ (kickAfterTabMap σ I) I) (UInt256.ofNat 9) out
      (cA, kickAfterTabMap σ I) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2399⟩
      [flipperVatTargetWord (kickAfterTabMap σ I) I, ⟨128⟩, ⟨0⟩, ⟨128⟩,
        kickIdWord σ I, kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I,
        ⟨426⟩, sel]
      (kickVatFluxCallMem σ (kickAfterTabMap σ I) I) (UInt256.ofNat 9) out
      (cA, kickAfterTabMap σ I) k' C' := by
  let σcall := kickAfterTabMap σ I
  let rawVat := flipperSlotWord ⟨2⟩ σcall I
  have hvatClean : UInt256.land rawVat solcAddrMask = flipperVatTargetWord σcall I := by
    simp [rawVat, σcall, flipperVatTargetWord, flipperAddressReturnWord]
  have hvatCleanLeft : UInt256.land solcAddrMask rawVat = flipperVatTargetWord σcall I := by
    rw [u256_land_comm]
  have h' : RD flipperBytecode I g s0 ⟨2395⟩
      [⟨128⟩, ⟨128⟩, rawVat, ⟨0⟩, solcAddrMask, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickVatFluxCallMem σ σcall I) (UInt256.ofNat 9) out (cA, σcall) k C := by
    simpa only [rawVat, σcall] using h
  have rd2399 := evm_run h' with [
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov)]
  rw [hvatCleanLeft] at rd2399
  exact ⟨_, _, by
    simpa only [rawVat, σcall] using rd2399⟩

theorem test_flipperKickX_fromVatCallMemToMaskedTarget {cA σ I}
    {g : Sat256} {s0 : State} {k C : ℕ} {out : ByteArray} {sel : UInt256}
    (h : RD flipperBytecode I g s0 ⟨2393⟩
      [flipperSlotWord ⟨2⟩ (kickAfterTabMap σ I) I, ⟨128⟩, ⟨64⟩, ⟨0⟩,
        solcAddrMask, kickIdWord σ I, kickBid I, kickLot I, kickTab I,
        kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickVatFluxCallMem σ (kickAfterTabMap σ I) I) (UInt256.ofNat 9) out
      (cA, kickAfterTabMap σ I) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2399⟩
      [flipperVatTargetWord (kickAfterTabMap σ I) I, ⟨128⟩, ⟨0⟩, ⟨128⟩,
        kickIdWord σ I, kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I,
        ⟨426⟩, sel]
      (kickVatFluxCallMem σ (kickAfterTabMap σ I) I) (UInt256.ofNat 9) out
      (cA, kickAfterTabMap σ I) k' C' := by
  obtain ⟨_, _, rd2395⟩ := test_flipperKickX_fromVatCallMemToVatMload h
  exact test_flipperKickX_fromVatMloadToMaskedTarget rd2395

theorem test_flipperKickX_fromMaskedTargetToExtcodesizeGuard {cA σ I}
    {g : Sat256} {s0 : State} {k C : ℕ} {out : ByteArray} {sel : UInt256}
    (h : RD flipperBytecode I g s0 ⟨2399⟩
      [flipperVatTargetWord (kickAfterTabMap σ I) I, ⟨128⟩, ⟨0⟩, ⟨128⟩,
        kickIdWord σ I, kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I,
        ⟨426⟩, sel]
      (kickVatFluxCallMem σ (kickAfterTabMap σ I) I) (UInt256.ofNat 9) out
      (cA, kickAfterTabMap σ I) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2422⟩
      [flipperVatTargetWord (kickAfterTabMap σ I) I,
        flipperVatTargetWord (kickAfterTabMap σ I) I, ⟨0⟩, ⟨128⟩, ⟨132⟩,
        ⟨128⟩, ⟨0⟩, ⟨260⟩, ⟨1628552750⟩,
        flipperVatTargetWord (kickAfterTabMap σ I) I, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickVatFluxCallMem σ (kickAfterTabMap σ I) I) (UInt256.ofNat 9) out
      (cA, kickAfterTabMap σ I) k' C' := by
  have rd2422 := evm_run h with [
    raw swap3 (by decide +native) (by evm_ov),
    raw push4 ⟨1628552750⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨132⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  exact ⟨_, _, by
    simpa only using rd2422⟩

theorem test_flipperKickX_fromVatCallMemToExtcodesizeGuard {cA σ I}
    {g : Sat256} {s0 : State} {k C : ℕ} {out : ByteArray} {sel : UInt256}
    (h : RD flipperBytecode I g s0 ⟨2393⟩
      [flipperSlotWord ⟨2⟩ (kickAfterTabMap σ I) I, ⟨128⟩, ⟨64⟩, ⟨0⟩,
        solcAddrMask, kickIdWord σ I, kickBid I, kickLot I, kickTab I,
        kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickVatFluxCallMem σ (kickAfterTabMap σ I) I) (UInt256.ofNat 9) out
      (cA, kickAfterTabMap σ I) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2422⟩
      [flipperVatTargetWord (kickAfterTabMap σ I) I,
        flipperVatTargetWord (kickAfterTabMap σ I) I, ⟨0⟩, ⟨128⟩, ⟨132⟩,
        ⟨128⟩, ⟨0⟩, ⟨260⟩, ⟨1628552750⟩,
        flipperVatTargetWord (kickAfterTabMap σ I) I, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickVatFluxCallMem σ (kickAfterTabMap σ I) I) (UInt256.ofNat 9) out
      (cA, kickAfterTabMap σ I) k' C' := by
  obtain ⟨_, _, rd2399⟩ := test_flipperKickX_fromVatCallMemToMaskedTarget h
  exact test_flipperKickX_fromMaskedTargetToExtcodesizeGuard rd2399

theorem test_flipperKickX_toVatExtcodesizeGuard {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out : ByteArray} {sel : UInt256}
    (h : RD flipperBytecode I g s0 ⟨2354⟩
      [solcAddrMask, ⟨3⟩, ⟨4⟩, ⟨64⟩, ⟨0⟩, ⟨2⟩, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) out (cA, kickAfterTabMap σ I) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2422⟩
      [flipperVatTargetWord (kickAfterTabMap σ I) I,
        flipperVatTargetWord (kickAfterTabMap σ I) I, ⟨0⟩, ⟨128⟩, ⟨132⟩,
        ⟨128⟩, ⟨0⟩, ⟨260⟩, ⟨1628552750⟩,
        flipperVatTargetWord (kickAfterTabMap σ I) I, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickVatFluxCallMem σ (kickAfterTabMap σ I) I) (UInt256.ofNat 9) out
      (cA, kickAfterTabMap σ I) k' C' := by
  obtain ⟨_, _, rd2393⟩ := test_flipperKickX_toVatCallMem h
  exact test_flipperKickX_fromVatCallMemToExtcodesizeGuard rd2393

theorem test_flipperKickX_vatNoCode {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out : ByteArray} {sel : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord (kickAfterTabMap σ I)
        (flipperVatTargetWord (kickAfterTabMap σ I) I) = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨2354⟩
      [solcAddrMask, ⟨3⟩, ⟨4⟩, ⟨64⟩, ⟨0⟩, ⟨2⟩, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) out (cA, kickAfterTabMap σ I) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd2422⟩ := test_flipperKickX_toVatExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2422⟩) (okPc := ⟨2434⟩) rd2422
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp)

theorem test_flipperKickX_toVatCall {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out : ByteArray} {sel : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord (kickAfterTabMap σ I)
        (flipperVatTargetWord (kickAfterTabMap σ I) I) ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨2354⟩
      [solcAddrMask, ⟨3⟩, ⟨4⟩, ⟨64⟩, ⟨0⟩, ⟨2⟩, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) out (cA, kickAfterTabMap σ I) k C) :
    ∃ gasWord k' C', RD flipperBytecode I g s0 ⟨2437⟩
      (gasWord :: flipperVatTargetWord (kickAfterTabMap σ I) I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ ::
        flipperVatTargetWord (kickAfterTabMap σ I) I :: kickIdWord σ I :: kickBid I ::
        kickLot I :: kickTab I :: kickGalKey I :: kickUsrKey I :: ⟨426⟩ :: sel :: [])
      (kickVatFluxCallMem σ (kickAfterTabMap σ I) I) (UInt256.ofNat 9) out
      (cA, kickAfterTabMap σ I) k' C' := by
  obtain ⟨_, _, rd2422⟩ := test_flipperKickX_toVatExtcodesizeGuard h
  obtain ⟨gasWord, k2437, C2437, rd2437⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2422⟩) (okPc := ⟨2434⟩) rd2422
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  exact ⟨gasWord, k2437, C2437, by simpa using rd2437⟩

theorem test_flipperKickX_vatPostCall
    {cA0 gh bl σbase σ₀ A I} {g : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {Acur : Substate}
    {k C : ℕ} {out0 : ByteArray} {sel : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord (kickAfterTabMap σ I)
        (flipperVatTargetWord (kickAfterTabMap σ I) I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨2354⟩
      [solcAddrMask, ⟨3⟩, ⟨4⟩, ⟨64⟩, ⟨0⟩, ⟨2⟩, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) out0 (cA, kickAfterTabMap σ I) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨2438⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: ⟨1628552750⟩ ::
          flipperVatTargetWord (kickAfterTabMap σ I) I :: kickIdWord σ I ::
          kickBid I :: kickLot I :: kickTab I :: kickGalKey I :: kickUsrKey I ::
          ⟨426⟩ :: sel :: [])
        (kickVatFluxCallMem σ (kickAfterTabMap σ I) I) (UInt256.ofNat 9) out
        (cA', σ') k' C'
    ∧ typedCallViaEVM config
        ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := kickAfterTabMap σ I, substate := Acur, createdAccounts := cA })
        (EVM.address (flipperVatAddress (kickAfterTabMap σ I) I)) "flux" 0
        (kickFluxArgValsOf
          ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := kickAfterTabMap σ I, substate := Acur, createdAccounts := cA }))
        (z,
          { { initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := kickAfterTabMap σ I, substate := Acur, createdAccounts := cA } with
            accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  let σcall := kickAfterTabMap σ I
  obtain ⟨gasWord, _, _, rd2437⟩ := test_flipperKickX_toVatCall hcodeSize h
  obtain ⟨cA', σ', z, out, A_in, callGas, k2438, C2438, hΘpack, rd2438raw,
      houtsz⟩ :=
    RD.call rd2437 (by decide +native) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k2438, C2438, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
          (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 9 := by
      decide +native
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      rfl
    have rd2438 : RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨2438⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: ⟨1628552750⟩ ::
          flipperVatTargetWord σcall I :: kickIdWord σ I :: kickBid I :: kickLot I ::
          kickTab I :: kickGalKey I :: kickUsrKey I :: ⟨426⟩ :: sel :: [])
        (out.write 0 (kickVatFluxCallMem σ σcall I) 128
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 9) out (cA', σ') k2438 C2438 :=
      haw ▸ rd2438raw
    rw [hmin, byteArray_write_len_zero] at rd2438
    simpa [σcall] using rd2438
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := flipperVatTargetWord σcall I)
      (mem := kickVatFluxCallMem σ σcall I) (inOff := ⟨128⟩) (inSize := ⟨132⟩)
      (fun hdepthEq => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [initState] using hdepthEq
        exact absurd hdepth (by rw [hEq]; decide))
      (flipperVatEvmAddress_eq_target_of_accountMapEquiv (accountMapEquiv.refl σcall))
      ?_ ?_
    · simpa [σcall, kickFluxArgValsOf, initState, flipperSlotWord, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using
        kickVatFluxCallMem_encode σ σcall I
    · simpa [initState, hperm] using hΘ

theorem test_flipperKickX_vatCallFailure {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id bid lot tab gal usr ret sel selector : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨2438⟩
      (⟨0⟩ :: ⟨260⟩ :: selector :: target :: id :: bid :: lot :: tab :: gal :: usr ::
        ret :: sel :: [])
      mem aw out acc k C)
    (houtsz : out.size < UInt256.size) :
    RDrev flipperBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2438⟩) (okPc := ⟨2454⟩) h
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    houtsz (by simp)

theorem test_flipperKickX_vatCallDepthLimit {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out : ByteArray} {sel : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord (kickAfterTabMap σ I)
        (flipperVatTargetWord (kickAfterTabMap σ I) I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (h : RD flipperBytecode I g s0 ⟨2354⟩
      [solcAddrMask, ⟨3⟩, ⟨4⟩, ⟨64⟩, ⟨0⟩, ⟨2⟩, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickFieldHashMem σ I) (UInt256.ofNat 3) out (cA, kickAfterTabMap σ I) k C) :
    RDrev flipperBytecode g s0 := by
  let σcall := kickAfterTabMap σ I
  obtain ⟨gasWord, _, _, rd2437⟩ := test_flipperKickX_toVatCall hcodeSize h
  obtain ⟨k2438, C2438, rd2438raw⟩ :=
    RD.callDepthLimit
      (code := flipperBytecode) (ee := I) (g := g) (s0 := s0) (pc := ⟨2437⟩)
      (mem := kickVatFluxCallMem σ σcall I) (aw := UInt256.ofNat 9) (rdata := out)
      (cA := cA) (σ := σcall) (gasArg := gasWord) (target := flipperVatTargetWord σcall I)
      (inOffset := ⟨128⟩) (inSize := ⟨132⟩) (outOffset := ⟨128⟩) (outSize := ⟨0⟩)
      (t := [⟨260⟩, ⟨1628552750⟩, flipperVatTargetWord σcall I, kickIdWord σ I,
        kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel])
      rd2437 (by decide +native) hdepth (by simp)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 9 := by
    decide +native
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  have rd2438 : RD flipperBytecode I g s0 ⟨2438⟩
      (⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ :: flipperVatTargetWord σcall I ::
        kickIdWord σ I :: kickBid I :: kickLot I :: kickTab I :: kickGalKey I ::
        kickUsrKey I :: ⟨426⟩ :: sel :: [])
      (kickVatFluxCallMem σ σcall I) (UInt256.ofNat 9) ByteArray.empty (cA, σcall)
      k2438 C2438 :=
    by
      rw [hmin, byteArray_write_len_zero] at rd2438raw
      exact haw ▸ rd2438raw
  exact test_flipperKickX_vatCallFailure rd2438 (by decide +native)

theorem test_flipperKickX_vatCallSuccessToLogStart {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray}
    {aw target id bid lot tab gal usr ret sel selector : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨2438⟩
      (⟨1⟩ :: ⟨260⟩ :: selector :: target :: id :: bid :: lot :: tab :: gal :: usr ::
        ret :: sel :: [])
      mem aw out acc k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2457⟩
      (selector :: target :: id :: bid :: lot :: tab :: gal :: usr :: ret :: sel :: [])
      mem aw out acc k' C' := by
  obtain ⟨k2456, C2456, rd2456⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨2438⟩) (okPc := ⟨2454⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
      (by simp)
  have rd2457 := evm_run rd2456 with [
    raw pop (by decide +native) (by evm_ov)]
  exact ⟨_, _, by
    convert rd2457 using 1 <;> decide +native⟩

abbrev test_kickKickEventTopic : UInt256 :=
  ⟨90598421132990109512674422884689516419241996603330962467584404604738313333370⟩

noncomputable abbrev test_kickKickLogMem
    (σmem σcall σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  writeCascade (kickVatFluxCallMem σmem σcall I)
    [(128, kickIdWord σ I),
     (160, kickLot I),
     (192, kickBid I),
     (224, kickTab I)]

theorem test_kickKickLogMem_eq_cascade
    (σmem σcall σ : AccountMap) (I : ExecutionEnv) :
    test_kickKickLogMem σmem σcall σ I =
      writeCascade (kickVatFluxCallMem σmem σcall I)
        [(128, kickIdWord σ I),
         (160, kickLot I),
         (192, kickBid I),
         (224, kickTab I)] := rfl

theorem test_kickKickLogMem_size
    (σmem σcall σ : AccountMap) (I : ExecutionEnv) :
    (test_kickKickLogMem σmem σcall σ I).size = 260 := by
  rw [test_kickKickLogMem_eq_cascade]
  exact writeCascade_size_of_base (kickVatFluxCallMem σmem σcall I)
    [(128, kickIdWord σ I),
     (160, kickLot I),
     (192, kickBid I),
     (224, kickTab I)]
    (kickVatFluxCallMem_size σmem σcall I)
    (by simp [WriteGapsOk] <;> decide +native)
    (by norm_num [writeCascadeSize])

theorem test_kickKickLogMem_read64
    (σmem σcall σ : AccountMap) (I : ExecutionEnv) :
    (test_kickKickLogMem σmem σcall σ I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [test_kickKickLogMem_eq_cascade]
  rw [writeCascade_read_preserved_of_base (kickVatFluxCallMem σmem σcall I)
    [(128, kickIdWord σ I),
     (160, kickLot I),
     (192, kickBid I),
     (224, kickTab I)]
    (kickVatFluxCallMem_size σmem σcall I)
    (by simp [WindowDisjointFromWrites] <;> decide +native)]
  exact kickVatFluxCallMem_read64 σmem σcall I

theorem test_kickKickLogMem_read128
    (σmem σcall σ : AccountMap) (I : ExecutionEnv) :
    (test_kickKickLogMem σmem σcall σ I).readWithPadding 128 32 =
      UInt256.toByteArray (kickIdWord σ I) := by
  rw [test_kickKickLogMem_eq_cascade]
  exact writeCascade_read_word_of_head_of_base
    (kickVatFluxCallMem σmem σcall I) (base := 260) (off := 128)
    (word := kickIdWord σ I)
    (rest := [(160, kickLot I), (192, kickBid I), (224, kickTab I)])
    (kickVatFluxCallMem_size σmem σcall I)
    (by decide +native)
    (by simp [WindowDisjointFromWrites] <;> decide +native)

noncomputable abbrev test_kickReturnMem
    (σmem σcall σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  Reasoning.Theory.writeWord (test_kickKickLogMem σmem σcall σ I) 128 (kickIdWord σ I)

theorem test_kickReturnMem_read64
    (σmem σcall σ : AccountMap) (I : ExecutionEnv) :
    (test_kickReturnMem σmem σcall σ I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold test_kickReturnMem
  unfold Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_of_gap]
  · exact test_kickKickLogMem_read64 σmem σcall σ I
  · rw [test_kickKickLogMem_size]; decide +native
  · decide +native
  · rw [test_kickKickLogMem_size]; decide +native

theorem test_kickReturnMem_size
    (σmem σcall σ : AccountMap) (I : ExecutionEnv) :
    (test_kickReturnMem σmem σcall σ I).size = 260 := by
  unfold test_kickReturnMem
  rw [writeWord_size]
  · rw [test_kickKickLogMem_size]
    decide +native
  · rw [test_kickKickLogMem_size]
    decide +native

theorem test_kickReturnMem_read128
    (σmem σcall σ : AccountMap) (I : ExecutionEnv) :
    (test_kickReturnMem σmem σcall σ I).readWithPadding 128 32 =
      UInt256.toByteArray (kickIdWord σ I) := by
  unfold test_kickReturnMem
  exact writeWord_read_back (test_kickKickLogMem σmem σcall σ I) 128 (kickIdWord σ I)
    (by
      rw [test_kickKickLogMem_size]
      decide +native)

theorem test_flipperReturnWordFromMem9 {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {val ret : UInt256} {R : List UInt256}
    {mem memout rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨426⟩ (val :: ret :: R) mem (UInt256.ofNat 9)
      rdata acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout : (UInt256.toByteArray val).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray val)
    (hov : R.length + 5 ≤ 1024) :
    RDret flipperBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw mstore 0 memout (UInt256.ofNat 9) (by decide +native) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide +native)
      mem_cost hmemoutLoad64 (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw ret 0 (UInt256.toByteArray val) (by decide +native) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

theorem test_flipperKickX_toKickLog {cA σmem σcall σacc σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out : ByteArray} {target sel : UInt256}
    (h : RD flipperBytecode I g s0 ⟨2457⟩
      [⟨1628552750⟩, target, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickVatFluxCallMem σmem σcall I) (UInt256.ofNat 9) out (cA, σacc) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨2544⟩
      [⟨128⟩, ⟨128⟩, test_kickKickEventTopic, kickUsrKey I, kickGalKey I,
        kickIdWord σ I, kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I,
        ⟨426⟩, sel]
      (test_kickKickLogMem σmem σcall σ I) (UInt256.ofNat 9) out (cA, σacc) k' C' := by
  let mem0 := kickVatFluxCallMem σmem σcall I
  let mem1 := Reasoning.Theory.writeWord mem0 128 (kickIdWord σ I)
  let mem2 := Reasoning.Theory.writeWord mem1 160 (kickLot I)
  let mem3 := Reasoning.Theory.writeWord mem2 192 (kickBid I)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ mem0.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem0.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    dsimp [mem0]
    exact mloadFreePtrValue (by rw [kickVatFluxCallMem_size]; decide) (by decide)
      (kickVatFluxCallMem_read64 σmem σcall I)
  have hmload64Log :
      (if (⟨64⟩ : UInt256).toNat ≥ (test_kickKickLogMem σmem σcall σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((test_kickKickLogMem σmem σcall σ I).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [test_kickKickLogMem_size]; decide) (by decide)
      (test_kickKickLogMem_read64 σmem σcall σ I)
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have rd2484 := evm_run h with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 mem1 (UInt256.ofNat 9)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 mem2 (UInt256.ofNat 9)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 mem3 (UInt256.ofNat 9)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨96⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup9 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 (test_kickKickLogMem σmem σcall σ I) (UInt256.ofNat 9)
      (by decide +native) mem_cost
      (by
        dsimp [mem0, mem1, mem2, mem3, test_kickKickLogMem, Reasoning.Theory.writeCascade,
          Reasoning.Theory.writeWord]
        rfl)
      (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd2502 := evm_run rd2484 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide +native)
      mem_cost hmload64Log (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup11 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw dup11 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  rw [hmask160] at rd2502
  rw [test_kickGalKey_clean I, test_kickUsrKey_clean I] at rd2502
  have rd2536 := rd2502.pushConst test_kickKickEventTopic (width := 32) (op := .PUSH32)
    (show Operation.POp.PUSH32 ≠ Operation.POp.PUSH0 by decide +native)
    (by decide +native) (by evm_ov)
  have rd2544 := evm_run rd2536 with [
    raw swap2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨128⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  exact ⟨_, _, by
    convert rd2544 using 1 <;> decide +native⟩

theorem test_flipperKickX_fromKickLogToReturnPc {cA σmem σcall σacc σ I}
    {g : Sat256} {s0 : State} {k C : ℕ} {out : ByteArray} {sel : UInt256}
    (hperm : I.perm = true)
    (h : RD flipperBytecode I g s0 ⟨2544⟩
      [⟨128⟩, ⟨128⟩, test_kickKickEventTopic, kickUsrKey I, kickGalKey I,
        kickIdWord σ I, kickBid I, kickLot I, kickTab I, kickGalKey I, kickUsrKey I,
        ⟨426⟩, sel]
      (test_kickKickLogMem σmem σcall σ I) (UInt256.ofNat 9) out (cA, σacc) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨426⟩
      [kickIdWord σ I, sel]
      (test_kickKickLogMem σmem σcall σ I) (UInt256.ofNat 9) out (cA, σacc) k' C' := by
  have rd2545 := h.log3 0 (UInt256.ofNat 9) (by decide +native) hperm
    mem_cost (by decide) (by change 8 ≤ 1024; decide)
  have rd2552 := evm_run rd2545 with [
    raw swap6 (by decide +native) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  have rd426 := rd2552.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    convert rd426 using 1 <;> decide +native⟩

theorem test_flipperKickX_logAndReturn {cA σmem σcall σacc σ I}
    {g : Sat256} {s0 : State} {k C : ℕ} {out : ByteArray} {target sel : UInt256}
    (hperm : I.perm = true)
    (h : RD flipperBytecode I g s0 ⟨2457⟩
      [⟨1628552750⟩, target, kickIdWord σ I, kickBid I,
        kickLot I, kickTab I, kickGalKey I, kickUsrKey I, ⟨426⟩, sel]
      (kickVatFluxCallMem σmem σcall I) (UInt256.ofNat 9) out (cA, σacc) k C) :
    RDret flipperBytecode g s0 (cA, σacc) (UInt256.toByteArray (kickIdWord σ I)) := by
  obtain ⟨_, _, rd2544⟩ := test_flipperKickX_toKickLog h
  obtain ⟨_, _, rd426⟩ := test_flipperKickX_fromKickLogToReturnPc hperm rd2544
  have hmload64Log :
      (if (⟨64⟩ : UInt256).toNat ≥ (test_kickKickLogMem σmem σcall σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((test_kickKickLogMem σmem σcall σ I).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [test_kickKickLogMem_size]; decide) (by decide)
      (test_kickKickLogMem_read64 σmem σcall σ I)
  have hmload64Return :
      (if (⟨64⟩ : UInt256).toNat ≥ (test_kickReturnMem σmem σcall σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((test_kickReturnMem σmem σcall σ I).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [test_kickReturnMem_size]; decide) (by decide)
      (test_kickReturnMem_read64 σmem σcall σ I)
  exact test_flipperReturnWordFromMem9 rd426 hmload64Log
    (by
      unfold test_kickReturnMem Reasoning.Theory.writeWord
      rfl)
    hmload64Return (test_kickReturnMem_read128 σmem σcall σ I) (by decide)

end Benchmarks.Dss.Flipper
