import Benchmarks.Dss.Flopper.Kick.Part1

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper
theorem RD.flopperKickReturnWordFromMem7 {σ I} {g : Sat256} {s0 : State}
    {sel id : UInt256} {mem memout rdata : ByteArray} {k C : ℕ}
    (h : RD flopperBytecode I g s0 ⟨644⟩ [id, sel] mem (UInt256.ofNat 7) rdata
      σ k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hmemout : (UInt256.toByteArray id).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray id) :
    RDret flopperBytecode g s0 σ (UInt256.toByteArray id) := by
  exact evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mstore 0 memout (UInt256.ofNat 7) (by native_decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmemoutLoad64 (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw ret 0 (UInt256.toByteArray id) (by native_decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem flopperKickX_toEndStoreStart {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (kickRuntimeTauWord I.codeOwner σ I).toNat < 2 ^ 48)
    (h : RD flopperBytecode I g s0 ⟨3643⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    let id := kickRuntimeIdWord σ I
    let memStore := twoWordHashMem id ⟨1⟩ (relyAuthHashMem I)
    let σGuy := kickRuntimeAfterGuyMap I.codeOwner σ I
    ∃ k' C', RD flopperBytecode I g s0 ⟨3737⟩
      [kickRuntimeAddWord I.codeOwner σ I, id, kickBidWord I, kickLotWord I,
        kickGalMaskedWord I, ⟨644⟩, sel]
      memStore (UInt256.ofNat 3) ByteArray.empty σGuy k' C' := by
  intro id memStore σGuy
  obtain ⟨_, _, rd4740⟩ := flopperKickX_toCheckedAddStart hperm h
  let tau := kickRuntimeTauWord I.codeOwner σ I
  let timestamp := UInt256.ofNat I.header.timestamp
  let addWord := kickRuntimeAddWord I.codeOwner σ I
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
  have rd3737 := rd4715.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa [timestamp, tau, addWord, kickRuntimeAddWord, id, memStore, σGuy] using rd3737⟩

set_option maxHeartbeats 1000000 in
theorem flopperKickX_addOverflow {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (kickRuntimeTauWord I.codeOwner σ I).toNat)
    (h : RD flopperBytecode I g s0 ⟨3643⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev flopperBytecode g s0 := by
  obtain ⟨_, _, rd4740⟩ := flopperKickX_toCheckedAddStart hperm h
  let tau := kickRuntimeTauWord I.codeOwner σ I
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
    simpa [tau] using kickRuntimeTauWord_lt I.codeOwner σ I
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

set_option maxHeartbeats 1000000 in
theorem flopperKickX_toEventStart {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (kickRuntimeTauWord I.codeOwner σ I).toNat < 2 ^ 48)
    (h : RD flopperBytecode I g s0 ⟨3643⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    let id := kickRuntimeIdWord σ I
    let memStore := twoWordHashMem id ⟨1⟩ (relyAuthHashMem I)
    let memEndStore := twoWordHashMem id ⟨1⟩ memStore
    let σSuccess := kickRuntimeSuccessAccountMap I.codeOwner σ I
    ∃ k' C', RD flopperBytecode I g s0 ⟨3796⟩
      [⟨64⟩, ⟨32⟩, id, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      memEndStore (UInt256.ofNat 3) ByteArray.empty σSuccess k' C' := by
  intro id memStore memEndStore σSuccess
  let σGuy := kickRuntimeAfterGuyMap I.codeOwner σ I
  let addWord := kickRuntimeAddWord I.codeOwner σ I
  let base := solcMappingSlot ⟨1⟩ id
  let packedSlot := auctionPackedSlot id
  let oldPacked := solcSlotWord σGuy I packedSlot
  obtain ⟨_, _, rd3737⟩ := flopperKickX_toEndStoreStart hperm haddFit h
  let memKey := wordAt0Mem id memStore
  have rd3742pre := evm_run rd3737 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3743 := rd3742pre.mstore 0 memKey (UInt256.ofNat 3)
    (by native_decide)
    (by
      native_decide)
    (by simp [memKey, memStore, id, wordAt0Mem])
    (by native_decide)
    (by evm_ov)
  have rd3749pre := evm_run rd3743 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3750 := rd3749pre.mstore 0 memEndStore (UInt256.ofNat 3)
    (by native_decide)
    (by
      native_decide)
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      simp [memKey, memEndStore, memStore, id, twoWordHashMem, wordAt32Mem])
    (by native_decide)
    (by evm_ov)
  have rd3755pre := evm_run rd3750 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hbase :
      UInt256.ofNat (fromByteArrayBigEndian
        (KEC (memEndStore.readWithPadding 0 64))) = base := by
    simpa [base, memEndStore, memStore, id] using
      twoWordHashMem_solcMappingSlot_any ⟨1⟩ id memStore
  have rd3756 := rd3755pre.keccak256 0 base (UInt256.ofNat 3)
    (by native_decide)
    (by norm_num [M, MachineState.M, Cₘ] <;> native_decide)
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hbase)
    (by native_decide)
    (by evm_ov)
  have rd3759pre := evm_run rd3756 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have hpackedSlot : ⟨2⟩ + base = packedSlot := by
    rw [u256_add_comm]
    simp [packedSlot, base, auctionPackedSlot_eq, id]
  rw [hpackedSlot] at rd3759pre
  have rd3760 := rd3759pre.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k3761, C3761, rd3761raw⟩ := rd3760.sload (by native_decide) (by evm_ov)
  have rd3761 : RD flopperBytecode I g s0 ⟨3761⟩
      [oldPacked, packedSlot, ⟨32⟩, ⟨64⟩, addWord, id, kickBidWord I, kickLotWord I,
        kickGalMaskedWord I, ⟨644⟩, sel]
      memEndStore (UInt256.ofNat 3) ByteArray.empty σGuy k3761 C3761 := by
    simpa [oldPacked, packedSlot, solcSlotWord, addWord] using rd3761raw
  have rd3795pre := rd3761.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd3795pre' := evm_run rd3795pre with [
    raw swap5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
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
    raw swap5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw or (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  obtain ⟨k3796, C3796, rd3796raw⟩ := rd3795pre'.sstore hperm
    (by native_decide) (by evm_ov)
  have hpc3796 :
      (⟨3761⟩ : UInt256) + UInt256.ofNat 7 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨3796⟩ := by
    native_decide
  rw [hpc3796] at rd3796raw
  have hstoredRaw :
      UInt256.lor
          (UInt256.land oldPacked
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩) ⟨1⟩))
          (UInt256.mul (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩)
            (UInt256.land flopperUint48Mask addWord)) =
        setUint48Offset26Word oldPacked addWord := by
    simpa [tickRuntimeEndStoredRawWord, tickRuntimeEndShiftedWord, tickRuntimeEndClearMask,
      Sub.sub, HSub.hSub, Mul.mul, HMul.hMul]
      using tickRuntimeEndStoredRawWord_eq_setUint48Offset26Word oldPacked addWord
  rw [hstoredRaw] at rd3796raw
  have rd3796 : RD flopperBytecode I g s0 ⟨3796⟩
      [⟨64⟩, ⟨32⟩, id, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      memEndStore (UInt256.ofNat 3) ByteArray.empty σSuccess k3796 C3796 := by
    simpa [σSuccess, kickRuntimeSuccessAccountMap, kickRuntimeEndStoredWord,
      σGuy, oldPacked, packedSlot, addWord, hstoredRaw,
      tickRuntimeEndStoredRawWord, tickRuntimeEndShiftedWord, tickRuntimeEndClearMask, id]
      using rd3796raw
  exact ⟨_, _, rd3796⟩

set_option maxHeartbeats 1000000 in
theorem flopperKickX_success {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (kickRuntimeTauWord I.codeOwner σ I).toNat < 2 ^ 48)
    (h : RD flopperBytecode I g s0 ⟨3643⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret flopperBytecode g s0 (kickRuntimeSuccessAccountMap I.codeOwner σ I)
      (UInt256.toByteArray (kickRuntimeIdWord σ I)) := by
  let id := kickRuntimeIdWord σ I
  let memStore := twoWordHashMem id ⟨1⟩ (relyAuthHashMem I)
  let memEndStore := twoWordHashMem id ⟨1⟩ memStore
  let memEvent0 := writeWord memEndStore 128 id
  let memEvent1 := writeWord memEvent0 160 (kickLotWord I)
  let memEvent := kickEventMem memEndStore id (kickLotWord I) (kickBidWord I)
  let σSuccess := kickRuntimeSuccessAccountMap I.codeOwner σ I
  obtain ⟨_, _, rd3796⟩ := flopperKickX_toEventStart hperm haddFit h
  have hmemStore : memStore.size = 96 := by
    simpa [memStore, id] using twoWordHashMem_size_96 id ⟨1⟩ (relyAuthHashMem_size I)
  have hreadStore : memStore.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memStore, id] using
      twoWordHashMem_read64 id ⟨1⟩ (relyAuthHashMem_size I) (relyAuthHashMem_read64 I)
  have hmemEnd : memEndStore.size = 96 := by
    simpa [memEndStore, memStore, id] using twoWordHashMem_size_96 id ⟨1⟩ hmemStore
  have hreadEnd : memEndStore.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [memEndStore, memStore, id] using twoWordHashMem_read64 id ⟨1⟩ hmemStore hreadStore
  have hmload64End :
      (if (⟨64⟩ : UInt256).toNat ≥ memEndStore.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memEndStore.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemEnd]; decide) hreadEnd
  have rd3799pre := evm_run rd3796 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      hmload64End (by decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd3800 := rd3799pre.mstore 6 memEvent0 (UInt256.ofNat 5)
    (by native_decide)
    (by
      native_decide)
    (by rfl)
    (by native_decide)
    (by evm_ov)
  have rd3805pre := evm_run rd3800 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3806 := rd3805pre.mstore 3 memEvent1 (UInt256.ofNat 6)
    (by native_decide)
    (by
      native_decide)
    (by rfl)
    (by native_decide)
    (by evm_ov)
  have rd3811pre := evm_run rd3806 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3812 := rd3811pre.mstore 3 memEvent (UInt256.ofNat 7)
    (by native_decide)
    (by
      native_decide)
    (by rfl)
    (by native_decide)
    (by evm_ov)
  have hmload64Event :
      (if (⟨64⟩ : UInt256).toNat ≥ memEvent.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memEvent.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩ := by
    simpa [memEvent] using kickEventMem_mload64 id (kickLotWord I) (kickBidWord I)
      hmemEnd hreadEnd
  have rd3824 := evm_run rd3812 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide) mem_cost
      hmload64Event (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  let kickTopic : UInt256 :=
    ⟨57232600449834081365935232875560862584875913243754734604176407410798957956598⟩
  have rd3858 := rd3824.pushConst kickTopic (width := 32) (op := .PUSH32)
    (by decide : Operation.POp.PUSH32 ≠ .PUSH0)
    (by native_decide)
    (by simp)
  have rd3867 := evm_run rd3858 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨96⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd3868 := RD.log2 0 (UInt256.ofNat 7) rd3867 (by native_decide) hperm
    mem_cost (by decide)
    (by
      simp only [List.length_cons, List.length_nil]
      omega)
  have rd644 := evm_run rd3868 with [
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact RD.flopperKickReturnWordFromMem7 rd644
    (by simpa [memEvent] using
      (kickEventMem_mload64 id (kickLotWord I) (kickBidWord I) hmemEnd hreadEnd))
    (by rfl)
    (by simpa [memEvent] using
      (kickEventReturnMem_mload64 id (kickLotWord I) (kickBidWord I) hmemEnd hreadEnd))
    (by simpa [memEvent] using
      (kickEventReturnMem_read128 id (kickLotWord I) (kickBidWord I) hmemEnd))

theorem kickRuntimeIdWord_source_eq
    {σ σ₀ A I} {g : UInt256} :
    kickRuntimeIdWord σ I =
      kickIdWord (initState σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  simp [kickRuntimeIdWord, kickIdWord, kickKicksWord, evmSolm, initState]

theorem kickRuntimeAfterKicksMap_source_eq
    {σ σ₀ A I} {g : UInt256} :
    Eq (kickRuntimeAfterKicksMap I.codeOwner σ I)
      (kickAfterKicksState
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)).accountMap := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hid := kickRuntimeIdWord_source_eq
    (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
  simp [evmSolm, initState, storageStore_accountMap, kickAfterKicksState,
    kickRuntimeAfterKicksMap, hid]

theorem kickRuntimeAfterBidMap_source_eq
    {σ σ₀ A I} {g : UInt256} :
    Eq (kickRuntimeAfterBidMap I.codeOwner σ I)
      (kickAfterBidState
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).accountMap := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hAfter :=
    kickRuntimeAfterKicksMap_source_eq
      (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
  have hid := kickRuntimeIdWord_source_eq
    (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
  simpa [evmSolm, initState, storageStore_accountMap, kickAfterBidState,
    kickAfterKicksState_executionEnv, kickRuntimeAfterBidMap, hid] using
    congrArg (fun accounts => sstoreAccountMap I.codeOwner accounts
      (auctionBidSlot (kickRuntimeIdWord σ I)) (kickBidWord I)) hAfter

theorem kickRuntimeAfterLotMap_source_eq
    {σ σ₀ A I} {g : UInt256} :
    Eq (kickRuntimeAfterLotMap I.codeOwner σ I)
      (kickAfterLotState
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).accountMap := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hAfter :=
    kickRuntimeAfterBidMap_source_eq
      (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
  have hid := kickRuntimeIdWord_source_eq
    (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
  simpa [evmSolm, initState, storageStore_accountMap, kickAfterLotState,
    kickAfterBidState_executionEnv, kickRuntimeAfterLotMap, hid] using
    congrArg (fun accounts => sstoreAccountMap I.codeOwner accounts
      (auctionLotSlot (kickRuntimeIdWord σ I)) (kickLotWord I)) hAfter

theorem kickRuntimeAfterGuyMap_source_eq
    {σ σ₀ A I} {g : UInt256} :
    Eq (kickRuntimeAfterGuyMap I.codeOwner σ I)
      (kickAfterGuyState
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) I).accountMap := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (kickRuntimeIdWord σ I)
  have hAfter :=
    kickRuntimeAfterLotMap_source_eq
      (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
  have hid := kickRuntimeIdWord_source_eq
    (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
  have hold :
      solcSlotWord (kickRuntimeAfterLotMap I.codeOwner σ I) I packedSlot =
        Solm.EVM.storageLoad (kickAfterLotState evmSolm I)
          (kickAfterLotState evmSolm I).executionEnv.codeOwner
          (auctionPackedSlot (kickIdWord evmSolm)) := by
    have hslot :=
      congrArg (fun accounts => flopperSlotWord packedSlot accounts I) hAfter
    simpa [packedSlot, flopperSlotWord, solcSlotWord, evmSolm, initState,
      kickAfterLotState_executionEnv, hid] using hslot
  have hstored :
      kickRuntimeGuyStoredWord I.codeOwner σ I = kickGuyStoredWord evmSolm I := by
    unfold kickRuntimeGuyStoredWord kickGuyStoredWord
    change
      setAddressOffset0Word
          (solcSlotWord (kickRuntimeAfterLotMap I.codeOwner σ I) I packedSlot)
          (kickGalMaskedWord I) =
        setAddressOffset0Word
          (Solm.EVM.storageLoad (kickAfterLotState evmSolm I)
            (kickAfterLotState evmSolm I).executionEnv.codeOwner
            (auctionPackedSlot (kickIdWord evmSolm)))
          (kickGalMaskedWord I)
    rw [hold]
  simpa [evmSolm, initState, storageStore_accountMap, kickAfterGuyState,
    kickAfterLotState_executionEnv, kickRuntimeAfterGuyMap, packedSlot, hid, hstored] using
    congrArg (fun accounts => sstoreAccountMap I.codeOwner accounts packedSlot
      (kickRuntimeGuyStoredWord I.codeOwner σ I)) hAfter

theorem kickRuntimeTauWord_source_eq
    {σ σ₀ A I} {g : UInt256} :
    kickRuntimeTauWord I.codeOwner σ I =
      kickTauWord
        (kickAfterGuyState
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) I) := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hAfter :=
    kickRuntimeAfterGuyMap_source_eq
      (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
  have h := congrArg (fun accounts => flopperUint48Offset6Word ⟨6⟩ accounts I) hAfter
  simpa [evmSolm, kickRuntimeTauWord, kickTauWord, kickAfterGuyState_executionEnv,
    initState] using h

theorem kickRuntimeSuccessAccountMap_eq_postState
    {σ σ₀ A I} {g : UInt256}
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (kickRuntimeTauWord I.codeOwner σ I).toNat < 2 ^ 48) :
    Eq (kickRuntimeSuccessAccountMap I.codeOwner σ I)
      (kickPostState (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        I).accountMap := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let packedSlot := auctionPackedSlot (kickRuntimeIdWord σ I)
  let runtimeOld := solcSlotWord (kickRuntimeAfterGuyMap I.codeOwner σ I) I packedSlot
  let runtimeAdd := kickRuntimeAddWord I.codeOwner σ I
  have hid := kickRuntimeIdWord_source_eq
    (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
  have hAfter :=
    kickRuntimeAfterGuyMap_source_eq
      (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
  have htau :=
    kickRuntimeTauWord_source_eq
      (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
  have haddFitSolm :
      (kickNow48Word evmSolm).toNat +
          (kickTauWord (kickAfterGuyState evmSolm I)).toNat < 2 ^ 48 := by
    simpa [evmSolm, kickNow48Word, kickTimestampWord, initState, htau] using haddFit
  have hmaskedRuntime :
      UInt256.land runtimeAdd flopperUint48Mask = kickEndPostWord evmSolm I := by
    apply u256_inj
    change (UInt256.land (kickRuntimeAddWord I.codeOwner σ I) flopperUint48Mask).toNat =
      (kickEndPostWord evmSolm I).toNat
    rw [kickRuntimeAddWord]
    rw [uint48Mask_add_no_wrap_toNat (UInt256.ofNat I.header.timestamp)
      (kickRuntimeTauWord I.codeOwner σ I) haddFit]
    rw [kickEndPostWord_toNat evmSolm I haddFitSolm]
    simpa [evmSolm, kickNow48Word, kickTimestampWord, initState, htau]
  have hsourceClean :
      UInt256.land (kickEndPostWord evmSolm I) flopperUint48Mask =
        kickEndPostWord evmSolm I := by
    apply flopperUint48Mask_clean_of_canonical
    have hendNat := kickEndPostWord_toNat evmSolm I haddFitSolm
    rw [hendNat]
    simpa [EVM.twoPow] using haddFitSolm
  have hold :
      runtimeOld =
        Solm.EVM.storageLoad (kickAfterGuyState evmSolm I)
          (kickAfterGuyState evmSolm I).executionEnv.codeOwner
          (auctionPackedSlot (kickIdWord evmSolm)) := by
    have hslot :=
      congrArg (fun accounts => flopperSlotWord packedSlot accounts I) hAfter
    simpa [runtimeOld, packedSlot, flopperSlotWord, solcSlotWord, evmSolm,
      initState, kickAfterGuyState_executionEnv, hid] using hslot
  have hstored :
      kickRuntimeEndStoredWord I.codeOwner σ I = kickEndStoredWord evmSolm I := by
    unfold kickRuntimeEndStoredWord kickEndStoredWord
    change setUint48Offset26Word runtimeOld runtimeAdd =
      setUint48Offset26Word
        (Solm.EVM.storageLoad (kickAfterGuyState evmSolm I)
          (kickAfterGuyState evmSolm I).executionEnv.codeOwner
          (auctionPackedSlot (kickIdWord evmSolm)))
        (kickEndPostWord evmSolm I)
    apply u256_inj
    rw [setUint48Offset26Word_toNat, setUint48Offset26Word_toNat]
    rw [hold, hmaskedRuntime, hsourceClean]
  simpa [evmSolm, initState, storageStore_accountMap, kickAfterGuyState_executionEnv,
    packedSlot, runtimeOld, runtimeAdd, kickRuntimeSuccessAccountMap, kickPostState,
    hstored, hid] using
    congrArg (fun accounts => sstoreAccountMap I.codeOwner accounts packedSlot
      (kickRuntimeEndStoredWord I.codeOwner σ I)) hAfter

theorem flopperKickBodyCoreUnauthorized
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some kickTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (kickTransition.params.map Param.name)
        (transitionSignature kickTransition).paramTypes I.calldata = some (kickLocals I))
    (rd3401 : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3401⟩
      [kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm :
      Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠
        ⟨1⟩ := by
    intro hbad
    have hbad' : relyAuthWord σ I = ⟨1⟩ := by
      simpa [evmSolm, relyAuthWord, flopperSlotWord, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using hbad
    exact hauth hbad'
  have hbody :
      ExecTransitionBody config contract evmSolm (kickLocals I) kickTransition.body
        .reverted := by
    exact flopperKickBodyReverts_unauthorized evmSolm I
      (by simpa [evmSolm, initState] using hwv)
      (by simp [evmSolm, initState])
      hauthSolm
  obtain ⟨_, _, rd3401'⟩ := rd3401
  exact (flopperKickX_unauthorized (g := Sat256.ofUInt256 g) hauth rd3401')
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperKickBodyCoreNotLive
    {σ σ₀ A I} {g : UInt256} {sel : UInt256} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some kickTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (kickTransition.params.map Param.name)
        (transitionSignature kickTransition).paramTypes I.calldata = some (kickLocals I))
    (rd3494 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3494⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm :
      Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner (relyAuthStorageSlot I) =
        ⟨1⟩ := by
    simpa [evmSolm, relyAuthWord, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using hauth
  have hliveSolm : kickLiveWord evmSolm ≠ ⟨1⟩ := by
    intro hbad
    apply hlive
    simpa [kickLiveWord, evmSolm, initState] using hbad
  have hbody :
      ExecTransitionBody config contract evmSolm (kickLocals I) kickTransition.body
        .reverted := by
    exact flopperKickBodyReverts_notLive evmSolm I
      (by simpa [evmSolm, initState] using hwv)
      (by simp [evmSolm, initState])
      hauthSolm
      hliveSolm
  exact (flopperKickX_notLive (g := Sat256.ofUInt256 g) hlive rd3494)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperKickBodyCoreKicksOverflow
    {σ σ₀ A I} {g : UInt256} {sel : UInt256} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hkicksGe : UInt256.size - 1 ≤ (flopperSlotWord ⟨7⟩ σ I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some kickTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (kickTransition.params.map Param.name)
        (transitionSignature kickTransition).paramTypes I.calldata = some (kickLocals I))
    (rd3568 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3568⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm :
      Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner (relyAuthStorageSlot I) =
        ⟨1⟩ := by
    simpa [evmSolm, relyAuthWord, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using hauth
  have hliveSolm : kickLiveWord evmSolm = ⟨1⟩ := by
    simpa [kickLiveWord, evmSolm, initState] using hlive
  have hkicksGeSolm : UInt256.size - 1 ≤ (kickKicksWord evmSolm).toNat := by
    simpa [kickKicksWord, evmSolm, initState] using hkicksGe
  have hbody :
      ExecTransitionBody config contract evmSolm (kickLocals I) kickTransition.body
        .reverted := by
    exact flopperKickBodyReverts_kicksOverflow evmSolm I
      (by simpa [evmSolm, initState] using hwv)
      (by simp [evmSolm, initState])
      hauthSolm
      hliveSolm
      hkicksGeSolm
  exact (flopperKickX_kicksOverflow (g := Sat256.ofUInt256 g) hkicksGe rd3568)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperKickBodyCoreAddOverflow
    {σ σ₀ A I} {g : UInt256} {sel : UInt256} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hkicksLt : (flopperSlotWord ⟨7⟩ σ I).toNat < UInt256.size - 1)
    (haddOverflow :
      2 ^ 48 ≤ (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (kickRuntimeTauWord I.codeOwner σ I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some kickTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (kickTransition.params.map Param.name)
        (transitionSignature kickTransition).paramTypes I.calldata = some (kickLocals I))
    (rd3643 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3643⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm :
      Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner (relyAuthStorageSlot I) =
        ⟨1⟩ := by
    simpa [evmSolm, relyAuthWord, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using hauth
  have hliveSolm : kickLiveWord evmSolm = ⟨1⟩ := by
    simpa [kickLiveWord, evmSolm, initState] using hlive
  have hkicksLtSolm : (kickKicksWord evmSolm).toNat < UInt256.size - 1 := by
    simpa [kickKicksWord, evmSolm, initState] using hkicksLt
  have htau :=
    kickRuntimeTauWord_source_eq
      (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
  have haddOverflowSolm :
      2 ^ 48 ≤
        (kickNow48Word evmSolm).toNat +
          (kickTauWord (kickAfterGuyState evmSolm I)).toNat := by
    simpa [evmSolm, kickNow48Word, kickTimestampWord, initState, htau]
      using haddOverflow
  have hbody :
      ExecTransitionBody config contract evmSolm (kickLocals I) kickTransition.body
        .reverted := by
    exact flopperKickBodyReverts_addOverflow evmSolm I
      (by simpa [evmSolm, initState] using hwv)
      (by simp [evmSolm, initState])
      hauthSolm
      hliveSolm
      hkicksLtSolm
      haddOverflowSolm
  exact (flopperKickX_addOverflow (g := Sat256.ofUInt256 g) hperm haddOverflow rd3643)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flopperKickBodyCoreSuccess
    {σ σ₀ A I} {g : UInt256} {sel : UInt256} {k C : ℕ}
    (hcode : I.code = flopperBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hkicksLt : (flopperSlotWord ⟨7⟩ σ I).toNat < UInt256.size - 1)
    (haddFit :
      (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
        (kickRuntimeTauWord I.codeOwner σ I).toNat < 2 ^ 48)
    (hdispatch : dispatchMsg contract I.calldata = some kickTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (kickTransition.params.map Param.name)
        (transitionSignature kickTransition).paramTypes I.calldata = some (kickLocals I))
    (rd3643 : RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3643⟩
      [⟨0⟩, kickBidWord I, kickLotWord I, kickGalMaskedWord I, ⟨644⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hid := kickRuntimeIdWord_source_eq
    (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
  have hauthSolm :
      Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner (relyAuthStorageSlot I) =
        ⟨1⟩ := by
    simpa [evmSolm, relyAuthWord, flopperSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using hauth
  have hliveSolm : kickLiveWord evmSolm = ⟨1⟩ := by
    simpa [kickLiveWord, evmSolm, initState] using hlive
  have hkicksLtSolm : (kickKicksWord evmSolm).toNat < UInt256.size - 1 := by
    simpa [kickKicksWord, evmSolm, initState] using hkicksLt
  have htau :=
    kickRuntimeTauWord_source_eq
      (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
  have haddFitSolm :
      (kickNow48Word evmSolm).toNat +
          (kickTauWord (kickAfterGuyState evmSolm I)).toNat < 2 ^ 48 := by
    simpa [evmSolm, kickNow48Word, kickTimestampWord, initState, htau] using haddFit
  have hbody :
      ExecTransitionBody config contract evmSolm (kickLocals I) kickTransition.body
        (.returned { contract := contract, locals := kickEndLocals evmSolm I }
          (kickPostState evmSolm I)
          (some [.int (Int.ofNat (kickIdWord evmSolm).toNat)])) := by
    exact flopperKickBodyReturns_success evmSolm I
      (by simpa [evmSolm, initState] using hwv)
      (by simp [evmSolm, initState])
      hauthSolm
      hliveSolm
      hkicksLtSolm
      haddFitSolm
  have hret := flopperKickX_success (g := Sat256.ofUInt256 g) hperm haddFit rd3643
  have hpostAccounts :=
    kickRuntimeSuccessAccountMap_eq_postState
      (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) haddFit
  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
    (by simpa [evmSolm] using hpostAccounts)
    (by
      rw [hid]
      simpa [kickTransition] using
        (returnEquiv_of_encode
          (by simpa [uint256] using uint256ReturnEncoding (kickIdWord evmSolm))))

theorem flopperKickBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg contract I.calldata = some kickTransition)
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨716⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact (flopperKickX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch
      (flopperDecode_kick_none_short hsz4 hshort)

set_option maxHeartbeats 1000000 in
theorem flopperKickBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flopperSelBytes 8)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flopperSelBytes 8) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some kickTransition :=
    flopperDispatchKick hsel
  have hreach := flopperReachKickBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have rd3401ex := flopperKickX_decoded (g := Sat256.ofUInt256 g)
      hsz100 hsize hreach
    obtain ⟨_, _, rd3401⟩ := rd3401ex
    by_cases hauth : relyAuthWord σ I = ⟨1⟩
    · obtain ⟨_, _, rd3494⟩ := flopperKickX_authorized (g := Sat256.ofUInt256 g)
        hauth rd3401
      by_cases hlive : flopperSlotWord ⟨8⟩ σ I = ⟨1⟩
      · obtain ⟨_, _, rd3568⟩ := flopperKickX_liveOk (g := Sat256.ofUInt256 g)
          hlive rd3494
        by_cases hkicksLt : (flopperSlotWord ⟨7⟩ σ I).toNat < UInt256.size - 1
        · obtain ⟨_, _, rd3643⟩ := flopperKickX_kicksOk (g := Sat256.ofUInt256 g)
            hkicksLt rd3568
          by_cases haddFit :
              (UInt256.land (UInt256.ofNat I.header.timestamp) flopperUint48Mask).toNat +
                (kickRuntimeTauWord I.codeOwner σ I).toNat < 2 ^ 48
          · exact flopperKickBodyCoreSuccess hcode hperm hwv hauth hlive hkicksLt
              haddFit hdispatch (flopperDecode_kick_ok hsz100) rd3643
          · exact flopperKickBodyCoreAddOverflow hcode hperm hwv hauth hlive hkicksLt
              (Nat.le_of_not_gt haddFit) hdispatch (flopperDecode_kick_ok hsz100)
              rd3643
        · exact flopperKickBodyCoreKicksOverflow hcode hwv hauth hlive
            (Nat.le_of_not_gt hkicksLt) hdispatch (flopperDecode_kick_ok hsz100)
            rd3568
      · exact flopperKickBodyCoreNotLive hcode hwv hauth hlive hdispatch
          (flopperDecode_kick_ok hsz100) rd3494
    · exact flopperKickBodyCoreUnauthorized hcode hwv hauth hdispatch
        (flopperDecode_kick_ok hsz100) ⟨_, _, rd3401⟩
  · exact flopperKickBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Flopper
