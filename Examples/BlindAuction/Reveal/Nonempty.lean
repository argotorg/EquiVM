import Examples.BlindAuction.Reveal.Loop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 800000

namespace BlindAuction

/-! Helpers for assembling the nonempty `reveal` loop. -/

theorem scratch_reveal_aw_mstore0_of_ge3 {aw : UInt256} (haw : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := by
  apply u256_inj
  simp [MachineState.M]
  rw [UInt256.toNat_ofNat_of_lt]
  · omega
  · exact lt_of_le_of_lt (by omega : max aw.toNat 1 ≤ aw.toNat) aw.val.isLt

theorem scratch_reveal_aw_mstore32_of_ge3 {aw : UInt256} (haw : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw := by
  apply u256_inj
  simp [MachineState.M]
  rw [UInt256.toNat_ofNat_of_lt]
  · omega
  · exact lt_of_le_of_lt (by omega : max aw.toNat 2 ≤ aw.toNat) aw.val.isLt

theorem scratch_reveal_aw_mstore4_of_ge3 {aw : UInt256} (haw : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 4 32) = aw := by
  apply u256_inj
  simp [MachineState.M]
  rw [UInt256.toNat_ofNat_of_lt]
  · omega
  · exact lt_of_le_of_lt (by omega : max aw.toNat 2 ≤ aw.toNat) aw.val.isLt

theorem scratch_reveal_aw_keccak64_of_ge3 {aw : UInt256} (haw : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw := by
  apply u256_inj
  simp [MachineState.M]
  rw [UInt256.toNat_ofNat_of_lt]
  · omega
  · exact lt_of_le_of_lt (by omega : max aw.toNat 2 ≤ aw.toNat) aw.val.isLt

theorem scratch_reveal_aw_mload64_of_ge3 {aw : UInt256} (haw : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := by
  apply u256_inj
  simp [MachineState.M]
  rw [UInt256.toNat_ofNat_of_lt]
  · omega
  · exact lt_of_le_of_lt (by omega : max aw.toNat 3 ≤ aw.toNat) aw.val.isLt

theorem scratch_revealPackedHashWord_toBytesBE (value : UInt256) (fake : Bool)
    (secret : UInt256) :
    EVM.Word.toBytesBE
        (uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) =
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList :=
  toBytesBE_keccak_uInt256OfByteArray _

theorem scratch_revealPackedHash_ne_of_word_ne {blinded value secret : UInt256}
    {fake : Bool}
    (hne :
      blinded ≠
        uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) :
    EVM.Word.toBytesBE blinded ≠
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList := by
  intro hbytes
  apply hne
  apply word_toBytesBE_inj
  rw [hbytes, scratch_revealPackedHashWord_toBytesBE value fake secret]

theorem scratch_word_ne_of_u256_eq_zero {a b : UInt256}
    (h : UInt256.eq a b = ⟨0⟩) : a ≠ b := by
  intro heq
  rw [heq, u256_eq_refl] at h
  have hnat := congrArg UInt256.toNat h
  change (1 : Nat) = 0 at hnat
  omega

theorem scratch_revealPackedHash_eq_of_u256_eq_one {blinded value secret : UInt256}
    {fake : Bool}
    (h :
      UInt256.eq blinded
          (uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) =
        ⟨1⟩) :
    EVM.Word.toBytesBE blinded =
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList := by
  have hword := uInt256_eq_one_eq h
  rw [hword, scratch_revealPackedHashWord_toBytesBE value fake secret]

theorem scratch_revealPackedHash_ne_of_u256_eq_zero {blinded value secret : UInt256}
    {fake : Bool}
    (h :
      UInt256.eq blinded
          (uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) =
        ⟨0⟩) :
    EVM.Word.toBytesBE blinded ≠
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList := by
  exact scratch_revealPackedHash_ne_of_word_ne
    (scratch_word_ne_of_u256_eq_zero h)

set_option maxHeartbeats 1000000 in
theorem scratch_blindAuctionRevealX_callMade_fromCall_general {I} {g : Sat256}
    {s0 : State} {k C : ℕ}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {gasArg refund len freePtr revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd
      secretsLen secretsEnd sel : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hbalance : refund ≤ (σ.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024)
    (rd : RD blindAuctionBytecode I g s0 ⟨1349⟩
      [gasArg, revealScratchSenderWord I, refund, freePtr, ⟨0⟩, freePtr, ⟨0⟩,
        freePtr, refund, revealScratchSenderWord I, ⟨0⟩, refund, len,
        revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty (cA, σ) k C)
    (hawCall :
      UInt256.ofNat
        (MachineState.M (MachineState.M aw.toNat freePtr.toNat (⟨0⟩ : UInt256).toNat)
          freePtr.toNat (⟨0⟩ : UInt256).toNat) = aw) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
          s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (revealScratchSenderWord I))
          (toExecute σ (AccountAddress.ofUInt256 (revealScratchSenderWord I)))
          callGas (UInt256.ofNat I.gasPrice) refund refund
          ByteArray.empty (I.depth + 1) I.header I.perm)
      ∧ o.size < 2 ^ 255
      ∧ RD blindAuctionBytecode I g s0 ⟨1350⟩
          [(if z then ⟨1⟩ else ⟨0⟩), freePtr, refund, revealScratchSenderWord I,
            ⟨0⟩, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
            fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
          mem aw o (cA', σ') k' C' := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd1350₀⟩ :=
    RD.callValueMade rd (by decide) hperm hbalance hdepth (by simp)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  have hcd : mem.readWithPadding freePtr.toNat (⟨0⟩ : UInt256).toNat = ByteArray.empty := by
    exact byteArray_readWithPadding_zero _ _
  have hΘ' : ∃ (g'' : UInt256) (A' : Substate),
      (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
        s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
        (AccountAddress.ofUInt256 (revealScratchSenderWord I))
        (toExecute σ (AccountAddress.ofUInt256 (revealScratchSenderWord I)))
        callGas (UInt256.ofNat I.gasPrice) refund refund
        ByteArray.empty (I.depth + 1) I.header I.perm := by
    rcases hΘ with ⟨g'', A', hΘeq⟩
    refine ⟨g'', A', ?_⟩
    rw [hcd] at hΘeq
    exact hΘeq
  have ho255 : o.size < 2 ^ 255 := by
    rcases hΘ' with ⟨g'', A', hΘeq⟩
    have ho : o = (Ethereum.EVM.Θ I.blobVersionedHashes cA
        s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
        (AccountAddress.ofUInt256 (revealScratchSenderWord I))
        (toExecute σ (AccountAddress.ofUInt256 (revealScratchSenderWord I)))
        callGas (UInt256.ofNat I.gasPrice) refund refund
        ByteArray.empty (I.depth + 1) I.header I.perm).2.2.2.2.2 :=
      congrArg (fun t => t.2.2.2.2.2) hΘeq
    rw [ho]
    exact Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [hmin, byteArray_write_len_zero, hawCall] at rd1350₀
  exact ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ', ho255,
    by simpa [revealScratchSenderWord] using rd1350₀⟩

set_option maxHeartbeats 1000000 in
theorem scratch_blindAuctionRevealX_callDepth_fromCall_general {I} {g : Sat256}
    {s0 : State} {k C : ℕ}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {gasArg refund len freePtr revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd
      secretsLen secretsEnd sel : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hdepth : I.depth = 1024)
    (rd : RD blindAuctionBytecode I g s0 ⟨1349⟩
      [gasArg, revealScratchSenderWord I, refund, freePtr, ⟨0⟩, freePtr, ⟨0⟩,
        freePtr, refund, revealScratchSenderWord I, ⟨0⟩, refund, len,
        revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty (cA, σ) k C)
    (hawCall :
      UInt256.ofNat
        (MachineState.M (MachineState.M aw.toNat freePtr.toNat (⟨0⟩ : UInt256).toNat)
          freePtr.toNat (⟨0⟩ : UInt256).toNat) = aw) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1350⟩
      [⟨0⟩, freePtr, refund, revealScratchSenderWord I, ⟨0⟩, refund, len,
        revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd1350₀⟩ :=
    RD.callValueDepthLimit rd hperm (by decide) hdepth (by simp)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  rw [hmin, byteArray_write_len_zero, hawCall] at rd1350₀
  exact ⟨k', C', by simpa [revealScratchSenderWord] using rd1350₀⟩

set_option maxHeartbeats 1000000 in
theorem scratch_blindAuctionRevealX_callInsufficient_fromCall_general {I} {g : Sat256}
    {s0 : State} {k C : ℕ}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {gasArg refund len freePtr revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd
      secretsLen secretsEnd sel : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hbalance : ¬ refund ≤ (σ.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024)
    (rd : RD blindAuctionBytecode I g s0 ⟨1349⟩
      [gasArg, revealScratchSenderWord I, refund, freePtr, ⟨0⟩, freePtr, ⟨0⟩,
        freePtr, refund, revealScratchSenderWord I, ⟨0⟩, refund, len,
        revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty (cA, σ) k C)
    (hawCall :
      UInt256.ofNat
        (MachineState.M (MachineState.M aw.toNat freePtr.toNat (⟨0⟩ : UInt256).toNat)
          freePtr.toNat (⟨0⟩ : UInt256).toNat) = aw) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1350⟩
      [⟨0⟩, freePtr, refund, revealScratchSenderWord I, ⟨0⟩, refund, len,
        revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd1350₀⟩ :=
    RD.callValueInsufficientBalance rd hperm (by decide) hbalance hdepth (by simp)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  rw [hmin, byteArray_write_len_zero, hawCall] at rd1350₀
  exact ⟨k', C', by simpa [revealScratchSenderWord] using rd1350₀⟩

def scratch_revealPanicSelector : UInt256 :=
  UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩

noncomputable def scratch_revealPanicMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray scratch_revealPanicSelector).write 0 mem 0 32

noncomputable def scratch_revealPanicMem (panicCode : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray panicCode).write 0 (scratch_revealPanicMem0 mem) 4 32

theorem RD.blindAuctionPanic32Revert1967 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD blindAuctionBytecode ee g s0 ⟨1967⟩ R mem aw rdata acc k C)
    (haw : 3 ≤ aw.toNat)
    (hov : R.length + 2 ≤ 1024) :
    RDrev blindAuctionBytecode g s0 := by
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ = scratch_revealPanicSelector := by
    rfl
  have rd1974₀ := evm_run h with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd1974 := rd1974₀
  rw [hsel] at rd1974
  have rd1978 := evm_run rd1974 with [
    raw mstore 0 (scratch_revealPanicMem0 mem) aw
      (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [scratch_reveal_aw_mstore0_of_ge3 haw]
        simp)
      (by rfl) (scratch_reveal_aw_mstore0_of_ge3 haw) (by evm_ov),
    push1 ⟨0x32⟩, push1 ⟨4⟩]
  have rd1984 := evm_run rd1978 with [
    raw mstore 0 (scratch_revealPanicMem ⟨0x32⟩ mem) aw
      (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨4⟩ : UInt256).toNat = 4 by native_decide]
        rw [scratch_reveal_aw_mstore4_of_ge3 haw]
        simp)
      (by rfl) (scratch_reveal_aw_mstore4_of_ge3 haw) (by evm_ov),
    push1 ⟨0x24⟩, push0]
  exact rd1984.rev 0 (by decide)
    (fun s haws hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
      rw [show (⟨36⟩ : UInt256).toNat = 36 by native_decide]
      have hM : MachineState.M aw.toNat 0 36 = aw.toNat := by
        simp [MachineState.M]
        omega
      rw [hM, u256_ofNat_toNat]
      omega)
    (by evm_ov)

theorem RD.blindAuctionPanic11Revert2025 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD blindAuctionBytecode ee g s0 ⟨2025⟩ R mem aw rdata acc k C)
    (haw : 3 ≤ aw.toNat)
    (hov : R.length + 2 ≤ 1024) :
    RDrev blindAuctionBytecode g s0 := by
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ = scratch_revealPanicSelector := by
    rfl
  have rd2032₀ := evm_run h with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2032 := rd2032₀
  rw [hsel] at rd2032
  have rd2036 := evm_run rd2032 with [
    raw mstore 0 (scratch_revealPanicMem0 mem) aw
      (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [scratch_reveal_aw_mstore0_of_ge3 haw]
        simp)
      (by rfl) (scratch_reveal_aw_mstore0_of_ge3 haw) (by evm_ov),
    push1 ⟨0x11⟩, push1 ⟨4⟩]
  have rd2042 := evm_run rd2036 with [
    raw mstore 0 (scratch_revealPanicMem ⟨0x11⟩ mem) aw
      (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨4⟩ : UInt256).toNat = 4 by native_decide]
        rw [scratch_reveal_aw_mstore4_of_ge3 haw]
        simp)
      (by rfl) (scratch_reveal_aw_mstore4_of_ge3 haw) (by evm_ov),
    push1 ⟨0x24⟩, push0]
  exact rd2042.rev 0 (by decide)
    (fun s haws hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
      rw [show (⟨36⟩ : UInt256).toNat = 36 by native_decide]
      have hM : MachineState.M aw.toNat 0 36 = aw.toNat := by
        simp [MachineState.M]
        omega
      rw [hM, u256_ofNat_toNat]
      omega)
    (by evm_ov)

theorem scratch_blindAuctionCheckedAddOverflowRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode ee g s0 ⟨2045⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (haw : 3 ≤ aw.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev blindAuctionBytecode g s0 := by
  have hgt := scratch_blindAuctionCheckedAddOverflowGt a b hover
  have rd2052₀ := evm_run rd with [jumpdest, dup1, dup3, add, dup1, dup3, gt]
  have rd2052 := rd2052₀
  rw [hgt] at rd2052
  have rd2025 := evm_run rd2052 with [
    iszero, push2 ⟨1654⟩, jumpiNT (by decide), push2 ⟨1654⟩, push2 ⟨2025⟩,
    jump (by jump_dest)]
  exact RD.blindAuctionPanic11Revert2025 rd2025 haw (by simp at hov ⊢; omega)

theorem scratch_revealBid_arrayIndexInBounds_revert (evm : EVM.State) (i curLen : UInt256)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hbound : curLen.toNat ≤ i.toNat) :
    arrayIndexInBounds? blindAuctionConfig evm blindAuctionContract.storage "bids"
      [.mindex (.address evm.executionEnv.source)] (.int (Int.ofNat i.toNat)) = .revert := by
  simp [arrayIndexInBounds?, storageTypeAt?, storageTypeStep?, blindAuctionConfig,
    blindAuctionStorageLayout, blindAuctionContract, storageDecls, bidStructTy, uint256St,
    bytes32St, blindAuctionStorageLocLoad_uint256, hlen]
  omega

theorem scratch_resolveStorageRef_reveal_bid_revert_of_get (evm : EVM.State) (locals : Store)
    (i curLen : UInt256)
    (hbids : locals.get? "bids" = none)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hbound : curLen.toNat ≤ i.toNat) :
    resolveStorageRef? blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm (bidElemRef sender (.var "i")) = .revert := by
  have hbounds := scratch_revealBid_arrayIndexInBounds_revert evm i curLen hlen hbound
  have her :
      evalStorageRef blindAuctionConfig
        { contract := blindAuctionContract, locals := locals }
        evm (bidElemRef sender (.var "i")) = .revert := by
    simp only [bidElemRef, sender, evalStorageRef, evalStorageRefSteps.eq_def,
      evalStorageRefStep.eq_def, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, bind, pure, List.nil_append, hi]
    rw [hbounds]
  unfold resolveStorageRef?
  simp only [bidElemRef]
  have hbids' : locals["bids"]? = none := by
    simpa [Std.HashMap.get?_eq_getElem?] using hbids
  have her' :
      evalStorageRef blindAuctionConfig { contract := blindAuctionContract, locals := locals }
        evm { base := "bids", steps := [StorageRefStep.mindex sender,
          StorageRefStep.aindex (.var "i")] } = .revert := by
    simpa [bidElemRef] using her
  simp [hbids', her']

theorem scratch_revealLoopBody_revert_bounds_of_get (evm : EVM.State) (locals : Store)
    (i curLen : UInt256)
    (hbids : locals.get? "bids" = none)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hbound : curLen.toNat ≤ i.toNat) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts .reverted := by
  unfold scratch_revealLoopBodyStmts
  exact ExecBlock.consRevert
    (ExecStmt.letStorageRevert
      (scratch_resolveStorageRef_reveal_bid_revert_of_get evm locals i curLen hbids hi hlen
        hbound))

theorem scratch_blindAuctionRevealX_loopBody_toElemSlot_curLen {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1023⟩
      (scratch_revealEvmLoopStack i refund len revealEnd biddingEnd secretsLen secretsEnd
        fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata acc k C)
    (haw0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw)
    (haw32 : UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw)
    (haw64 : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw)
    (hbaseHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
            ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32).readWithPadding 0 64))) =
        revealScratchBidsLengthSlot I)
    (hlenLoad :
      (acc.2.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩) = curLen)
    (hbound : i.toNat < curLen.toNat)
    (hdataHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0
            ((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
              ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32) 0 32).readWithPadding 0 32))) =
        uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I)))) :
    ∃ mem' aw' k' C', RD blindAuctionBytecode I g s0 ⟨1069⟩
      [bidsElemSlot (.address I.source) (.int (Int.ofNat i.toNat)), i, refund, len, revealEnd,
        biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem' aw' rdata acc k' C' := by
  let mem1 : ByteArray := (UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32
  let mem2 : ByteArray := (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 mem1 32 32
  let mem3 : ByteArray := (UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0 mem2 0 32
  have rd' : RD blindAuctionBytecode I g s0 ⟨1023⟩
      [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C := by
    simpa [scratch_revealEvmLoopStack] using rd
  have rd1027 := evm_run rd' with [
    caller, push0, swap1, dup2,
    raw mstore 0 mem1 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [haw0]
        simp)
      (by rfl) haw0 (by evm_ov)]
  have rd1033 := evm_run rd1027 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 mem2 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨32⟩ : UInt256).toNat = 32 by native_decide]
        rw [haw32]
        simp)
      (by rfl) haw32 (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (revealScratchBidsLengthSlot I) aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨64⟩ : UInt256).toNat = 64 by native_decide]
        rw [haw64]
        simp)
      (by simpa [mem2, mem1, revealScratchSenderWord] using hbaseHash) haw64
      (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1039₀⟩ := rd1033.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1039⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1039⟩
      [curLen, revealScratchBidsLengthSlot I, ⟨0⟩, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem2 aw rdata acc k' C' := by
    exact ⟨_, _, by simpa [hlenLoad] using rd1039₀⟩
  have hlt : UInt256.lt i curLen = ⟨1⟩ := ult_one hbound
  have rd1047₀ := evm_run rd1039 with [dup4, swap1, dup2, lt]
  have rd1047 := rd1047₀
  rw [hlt] at rd1047
  have rd1054 := evm_run rd1047 with [
    push2 ⟨1054⟩, jumpiT one_ne_zero_uint (by jump_dest), jumpdest]
  have rd1062 := evm_run rd1054 with [
    swap1, push0,
    raw mstore 0 mem3 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [haw0]
        simp)
      (by rfl) haw0 (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0
      (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))))
      aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨32⟩ : UInt256).toNat = 32 by native_decide]
        rw [haw0]
        simp)
      (by simpa [mem3, mem2, mem1, revealScratchSenderWord] using hdataHash) haw0
      (by evm_ov)]
  have hslot :
      UInt256.mul ⟨2⟩ i +
          uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))) =
        bidsElemSlot (.address I.source) (.int (Int.ofNat i.toNat)) := by
    have hmul : UInt256.mul ⟨2⟩ i = UInt256.mul i ⟨2⟩ := by
      apply u256_inj
      show ((⟨2⟩ : UInt256).val * i.val).val = (i.val * (⟨2⟩ : UInt256).val).val
      rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]
    rw [hmul]
    rw [u256_add_comm]
    exact scratch_revealBidsElemSlot_eq I i
  have rd1069 := evm_run rd1062 with [swap1, push1 ⟨2⟩, mul, add, swap1, pop]
  have hpc1069 :
      (⟨1054⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ :
          UInt256) = ⟨1069⟩ := by
    native_decide
  exact ⟨mem3, aw, _, _, by simpa [hslot, hpc1069] using rd1069⟩

theorem scratch_blindAuctionRevealX_loopBody_bounds_revert {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1023⟩
      (scratch_revealEvmLoopStack i refund len revealEnd biddingEnd secretsLen secretsEnd
        fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata acc k C)
    (haw : 3 ≤ aw.toNat)
    (hbaseHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
            ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32).readWithPadding 0 64))) =
        revealScratchBidsLengthSlot I)
    (hlenLoad :
      (acc.2.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩) = curLen)
    (hbound : curLen.toNat ≤ i.toNat) :
    RDrev blindAuctionBytecode g s0 := by
  let mem1 : ByteArray := (UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32
  let mem2 : ByteArray := (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 mem1 32 32
  have rd' : RD blindAuctionBytecode I g s0 ⟨1023⟩
      [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C := by
    simpa [scratch_revealEvmLoopStack] using rd
  have rd1027 := evm_run rd' with [
    caller, push0, swap1, dup2,
    raw mstore 0 mem1 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [scratch_reveal_aw_mstore0_of_ge3 haw]
        simp)
      (by rfl) (scratch_reveal_aw_mstore0_of_ge3 haw) (by evm_ov)]
  have rd1033 := evm_run rd1027 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 mem2 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨32⟩ : UInt256).toNat = 32 by native_decide]
        rw [scratch_reveal_aw_mstore32_of_ge3 haw]
        simp)
      (by rfl) (scratch_reveal_aw_mstore32_of_ge3 haw) (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (revealScratchBidsLengthSlot I) aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨64⟩ : UInt256).toNat = 64 by native_decide]
        rw [scratch_reveal_aw_keccak64_of_ge3 haw]
        simp)
      (by simpa [mem2, mem1, revealScratchSenderWord] using hbaseHash)
      (scratch_reveal_aw_keccak64_of_ge3 haw)
      (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1039₀⟩ := rd1033.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1039⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1039⟩
      [curLen, revealScratchBidsLengthSlot I, ⟨0⟩, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem2 aw rdata acc k' C' := by
    exact ⟨_, _, by simpa [hlenLoad] using rd1039₀⟩
  have hlt : UInt256.lt i curLen = ⟨0⟩ := ult_zero hbound
  have rd1047₀ := evm_run rd1039 with [dup4, swap1, dup2, lt]
  have rd1047 := rd1047₀
  rw [hlt] at rd1047
  have rd1967 := evm_run rd1047 with [
    push2 ⟨1054⟩, jumpiNT (by decide),
    push2 ⟨1054⟩, push2 ⟨1967⟩, jump (by jump_dest)]
  exact RD.blindAuctionPanic32Revert1967 rd1967 haw (by simp)

theorem scratch_revealLoopBody_bounds_pair {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1023⟩
      (scratch_revealEvmLoopStack i refund len revealEnd biddingEnd secretsLen secretsEnd
        fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, σ) k C)
    (haw : 3 ≤ aw.toNat)
    (hbaseHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
            ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32).readWithPadding 0 64))) =
        revealScratchBidsLengthSlot I)
    (hlenLoad :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩) = curLen)
    (hbound : curLen.toNat ≤ i.toNat)
    (hbids : L.get? "bids" = none)
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts .reverted ∧
      RDrev blindAuctionBytecode g s0 := by
  exact ⟨
    scratch_revealLoopBody_revert_bounds_of_get evm L i curLen hbids hi hlen hbound,
    scratch_blindAuctionRevealX_loopBody_bounds_revert
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
      (i := i) (refund := refund) (len := len) (curLen := curLen)
      (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
      (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
      (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel)
      rd haw hbaseHash hlenLoad hbound⟩

theorem scratch_revealLoopBody_fakeInvalid_pair {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {values fakes secrets : List Value}
    {i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value fakeWord : UInt256}
    {fakeRaw : Value}
    (rd : RD blindAuctionBytecode I g s0 ⟨1023⟩
      (scratch_revealEvmLoopStack i refund len revealEnd biddingEnd secretsLen secretsEnd
        fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, σ) k C)
    (haw : 3 ≤ aw.toNat)
    (hbaseHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
            ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32).readWithPadding 0 64))) =
        revealScratchBidsLengthSlot I)
    (hlenLoad :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩) = curLen)
    (hboundBids : i.toNat < curLen.toNat)
    (hdataHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0
            ((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
              ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32) 0 32).readWithPadding 0 32))) =
        uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))))
    (hvalueBound : i.toNat < valuesLen.toNat)
    (hfakesBound : i.toNat < fakesLen.toNat)
    (hvalueLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + valuesEnd).toNat 32) =
        value)
    (hfakeSlt :
      UInt256.slt
          (UInt256.sub
            (UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩)
            (UInt256.mul ⟨32⟩ i + fakesEnd)) ⟨32⟩ = ⟨0⟩)
    (hfakeLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + fakesEnd).toNat 32) = fakeWord)
    (hfakeZero : fakeWord ≠ ⟨0⟩)
    (hfakeOne : fakeWord ≠ ⟨1⟩)
    (hbids : L.get? "bids" = none)
    (hvalues : L.get? "values" = some (.array values))
    (hfakes : L.get? "fakes" = some (.array fakes))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .revert) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts .reverted ∧
      RDrev blindAuctionBytecode g s0 := by
  obtain ⟨memSlot, awSlot, k1, C1, rd1069⟩ :=
    scratch_blindAuctionRevealX_loopBody_toElemSlot_curLen
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
      (i := i) (refund := refund) (len := len) (curLen := curLen) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) rd
      (scratch_reveal_aw_mstore0_of_ge3 haw)
      (scratch_reveal_aw_mstore32_of_ge3 haw)
      (scratch_reveal_aw_keccak64_of_ge3 haw)
      hbaseHash hlenLoad hboundBids hdataHash
  obtain ⟨k2, C2, rd1987⟩ :=
    scratch_blindAuctionRevealX_loopBody_loads_toFakeDecoder
      (I := I) (g := g) (s0 := s0) (k := k1) (C := C1)
      (mem := memSlot) (aw := awSlot) (rdata := rdata) (acc := (cA, σ))
      (slot := bidsElemSlot (.address I.source) (.int (Int.ofNat i.toNat)))
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (value := value)
      rd1069 hvalueBound hfakesBound hvalueLoad
  exact ⟨
    scratch_revealLoopBody_revert_fake_invalid_of_get evm L values fakes secrets
      curLen i value fakeRaw hbids hvalues hfakes hi hlen hboundBids hboundValues
      hboundFakes hvalueLookup hfakeLookup hfakeNorm,
    scratch_blindAuctionRevealX_loopBody_fakeDecoder_invalid_revert
      (I := I) (g := g) (s0 := s0) (k := k2) (C := C2)
      (mem := memSlot) (aw := awSlot) (rdata := rdata) (acc := (cA, σ))
      (slot := bidsElemSlot (.address I.source) (.int (Int.ofNat i.toNat)))
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (value := value) (word := fakeWord)
      rd1987 hfakeSlt hfakeLoad hfakeZero hfakeOne⟩

-- LIBRARY CANDIDATE: `Reasoning.SolmBody` / `Reasoning.Reach`.
-- Joint loop runner for solc while-loop bytecode paired with a Solm `for` loop whose body may
-- revert before the loop reaches its false condition.
theorem scratch_revealLoop_from_body_or_revert {I} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {α : Type}
    (len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd
      sel : UInt256)
    (Inv : ℕ → α → Store → EVM.State → Prop)
    (idx refund : α → UInt256)
    (mem : α → ByteArray) (aw : α → UInt256)
    (acc : α → Batteries.RBSet AccountAddress compare × AccountMap)
    (hshape : ∀ v a L evm, Inv v a L evm →
      L.get? "i" = some (.int (Int.ofNat (idx a).toNat)) ∧
      L.get? "length" = some (.int (Int.ofNat len.toNat)) ∧
      L.get? "refund" = some (.int (Int.ofNat (refund a).toNat)) ∧
      (idx a).toNat + v = len.toNat ∧
      (idx a).toNat ≤ len.toNat)
    (hbody : ∀ v a L evm, Inv (v + 1) a L evm → ∀ k C,
        RD blindAuctionBytecode I g s0 ⟨1023⟩
          (scratch_revealEvmLoopStack (idx a) (refund a) len revealEnd biddingEnd
            secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
          (mem a) (aw a) rdata (acc a) k C →
        (ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
            scratch_revealLoopBodyStmts .reverted ∧
          RDrev blindAuctionBytecode g s0) ∨
        ∃ a' L1 evm1 L2 evm2 k' C',
          (ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
              scratch_revealLoopBodyStmts
              (.ok { contract := blindAuctionContract, locals := L1 } evm1) ∨
            ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
              scratch_revealLoopBodyStmts
              (.continue { contract := blindAuctionContract, locals := L1 } evm1)) ∧
          ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm1
            scratch_revealLoopPostStmts
            (.ok { contract := blindAuctionContract, locals := L2 } evm2) ∧
          Inv v a' L2 evm2 ∧
          RD blindAuctionBytecode I g s0 ⟨1014⟩
            (scratch_revealEvmLoopStack (idx a') (refund a') len revealEnd biddingEnd
              secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
            (mem a') (aw a') rdata (acc a') k' C') :
    ∀ v a L evm, Inv v a L evm → ∀ k C,
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack (idx a) (refund a) len revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        (mem a) (aw a) rdata (acc a) k C →
      (∃ a' L' evm' k' C',
        ExecForLoop blindAuctionConfig
          { contract := blindAuctionContract, locals := L } evm
          (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
          scratch_revealLoopBodyStmts
          (.ok { contract := blindAuctionContract, locals := L' } evm') ∧
        Inv 0 a' L' evm' ∧
        RD blindAuctionBytecode I g s0 ⟨1331⟩
          (scratch_revealEvmLoopStack (idx a') (refund a') len revealEnd biddingEnd
            secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
          (mem a') (aw a') rdata (acc a') k' C') ∨
      (ExecForLoop blindAuctionConfig
          { contract := blindAuctionContract, locals := L } evm
          (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
          scratch_revealLoopBodyStmts .reverted ∧
        RDrev blindAuctionBytecode g s0) := by
  intro v
  induction v with
  | zero =>
      intro a L evm hInv k C rd
      rcases hshape 0 a L evm hInv with ⟨hi, hlen, _hrefund, hvar, _hle⟩
      obtain ⟨k', C', rdExit⟩ :=
        scratch_blindAuctionRevealX_loopCond_exit
          (I := I) (g := g) (s0 := s0) (k := k) (C := C)
          (mem := mem a) (aw := aw a) (rdata := rdata) (acc := acc a)
          (i := idx a) (refund := refund a) (len := len) (revealEnd := revealEnd)
          (biddingEnd := biddingEnd) (secretsLen := secretsLen)
          (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
          (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel)
          rd (by omega)
      have hcond :
          evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
            (.binary .lt (.var "i") (.var "length")) = .ok (.bool false) :=
        scratch_evalExpr_reveal_loop_cond_false_of_get evm L len (idx a) hi hlen (by omega)
      exact Or.inl ⟨a, L, evm, k', C', ExecForLoop.falseDone hcond, hInv, rdExit⟩
  | succ v ih =>
      intro a L evm hInv k C rd
      rcases hshape (v + 1) a L evm hInv with ⟨hi, hlen, _hrefund, hvar, _hle⟩
      obtain ⟨k1, C1, rd1023⟩ := blindAuctionRevealX_loopCond_taken
        (I := I) (g := g) (s0 := s0) (k := k) (C := C)
        (mem := mem a) (aw := aw a) (rdata := rdata) (acc := acc a)
        (i := idx a) (refund := refund a) (len := len) (revealEnd := revealEnd)
        (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
        (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
        (valuesEnd := valuesEnd) (sel := sel)
        (by simpa [scratch_revealEvmLoopStack] using rd) (by omega)
      have hcond :
          evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
            (.binary .lt (.var "i") (.var "length")) = .ok (.bool true) :=
        scratch_evalExpr_reveal_loop_cond_true_of_get evm L len (idx a) hi hlen (by omega)
      rcases hbody v a L evm hInv k1 C1
        (by simpa [scratch_revealEvmLoopStack] using rd1023) with hrev | hstep
      · exact Or.inr ⟨ExecForLoop.bodyRevert hcond hrev.1, hrev.2⟩
      · rcases hstep with
          ⟨a', L1, evm1, L2, evm2, k2, C2, hbodyStep, hpost, hInv', rdNext⟩
        rcases ih a' L2 evm2 hInv' k2 C2 rdNext with hdone | hloopRev
        · rcases hdone with ⟨a'', L', evm', k', C', hloop, hInv0, rdExit⟩
          rcases hbodyStep with hbodyOk | hbodyCont
          · exact Or.inl ⟨a'', L', evm', k', C',
              ExecForLoop.iterate hcond hbodyOk hpost hloop, hInv0, rdExit⟩
          · exact Or.inl ⟨a'', L', evm', k', C',
              ExecForLoop.continueIter hcond hbodyCont hpost hloop, hInv0, rdExit⟩
        · rcases hloopRev with ⟨hloop, hrdRev⟩
          rcases hbodyStep with hbodyOk | hbodyCont
          · exact Or.inr ⟨ExecForLoop.iterate hcond hbodyOk hpost hloop, hrdRev⟩
          · exact Or.inr ⟨ExecForLoop.continueIter hcond hbodyCont hpost hloop, hrdRev⟩

theorem scratch_blindAuctionRevealBodyReverts_fromLoopRevertOfLocals
    (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesLen : fakes.length = len.toNat)
    (hsecretsLen : secrets.length = len.toNat)
    (hloop :
      ExecForLoop blindAuctionConfig
        ({ contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ } :
          Frame) evm
        (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
        scratch_revealLoopBodyStmts .reverted) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs revealTransition.body
      .reverted := by
  let lengthFrame : Frame :=
    { contract := blindAuctionContract, locals := scratch_revealLengthStore callargs len }
  let refundFrame : Frame :=
    { contract := blindAuctionContract, locals := scratch_revealRefundStore callargs len ⟨0⟩ }
  let initLoopFrame : Frame :=
    { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ }
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs }
        evm (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
    exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig lengthFrame evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "values" values len ?_
        (by simp [scratch_revealLengthStore]) hvaluesLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hvalues
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "fakes" fakes len ?_
        (by simp [scratch_revealLengthStore]) hfakesLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hfakes
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "secrets" secrets len ?_
        (by simp [scratch_revealLengthStore]) hsecretsLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hsecrets
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
  change ExecBlock blindAuctionConfig refundFrame evm
    [ scratch_revealForStmt,
      .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
      .require (.var "success") ]
    .reverted
  have hfor :
      ExecStmt blindAuctionConfig refundFrame evm scratch_revealForStmt .reverted := by
    have hinit :
        ExecBlock blindAuctionConfig
          refundFrame evm
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.ok initLoopFrame evm) := by
      refine ExecBlock.consNormal
        (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
      exact ExecBlock.nil
    exact ExecStmt.for hinit hloop
  exact ExecBlock.consRevert hfor

end BlindAuction
