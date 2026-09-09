import Examples.BlindAuction.Reveal.Nonempty

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace BlindAuction

structure RevealLoopCursor where
  idx : UInt256
  refund : UInt256
  mem : ByteArray
  aw : UInt256
  acc : Batteries.RBSet AccountAddress compare × AccountMap
  fp : UInt256
  haw : 3 ≤ aw.toNat
  hawSmall : aw.toNat * 32 < UInt256.size
  hfpLoad :
    (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
     then ⟨0⟩
     else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp
  hfpRead : mem.readWithPadding 64 32 = UInt256.toByteArray fp
  hmem96 : 96 ≤ mem.size
  hmemle : mem.size ≤ fp.toNat + 32
  hgap : fp.toNat + 32 - mem.size < USize.size
  hfpIdx : fp.toNat = 128 + 97 * idx.toNat

theorem RevealLoopCursor.fp_add128_lt_size_of_idx_le (a : RevealLoopCursor)
    (hidx : a.idx.toNat ≤ solcMaxU64) :
    a.fp.toNat + 128 < UInt256.size := by
  rw [a.hfpIdx]
  have hmul : 97 * a.idx.toNat ≤ 97 * solcMaxU64 := Nat.mul_le_mul_left 97 hidx
  have hcap : 128 + 97 * solcMaxU64 + 128 < UInt256.size := by
    decide
  omega

def RevealLoopInv (loopLen : UInt256) (values fakes secrets : List Value)
    (I : ExecutionEnv) (σ₀ : AccountMap) (gh : BlockHeader) (bl : ProcessedBlocks)
    (A : Substate) : ℕ → RevealLoopCursor → Store → EVM.State → Prop :=
  fun v a L evm =>
    L.get? "i" = some (.int (Int.ofNat a.idx.toNat)) ∧
    L.get? "length" = some (.int (Int.ofNat loopLen.toNat)) ∧
    L.get? "refund" = some (.int (Int.ofNat a.refund.toNat)) ∧
    L.get? "bids" = none ∧
    L.get? "values" = some (.array values) ∧
    L.get? "fakes" = some (.array fakes) ∧
    L.get? "secrets" = some (.array secrets) ∧
    a.idx.toNat + v = loopLen.toNat ∧
    a.idx.toNat ≤ loopLen.toNat ∧
    evm.executionEnv = I ∧
    evm.σ₀ = σ₀ ∧
    evm.genesisBlockHeader = gh ∧
    evm.blocks = bl ∧
    evm.createdAccounts = a.acc.1 ∧
    evm.substate = A ∧
    accountMapEquiv a.acc.2 evm.accountMap

theorem RevealLoopInv_shape (loopLen : UInt256) (values fakes secrets : List Value)
    (I : ExecutionEnv) (σ₀ : AccountMap) (gh : BlockHeader) (bl : ProcessedBlocks)
    (A : Substate) :
    ∀ v a L evm, RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A v a L evm →
      L.get? "i" = some (.int (Int.ofNat a.idx.toNat)) ∧
      L.get? "length" = some (.int (Int.ofNat loopLen.toNat)) ∧
      L.get? "refund" = some (.int (Int.ofNat a.refund.toNat)) ∧
      a.idx.toNat + v = loopLen.toNat ∧
      a.idx.toNat ≤ loopLen.toNat := by
  intro v a L evm hInv
  rcases hInv with
    ⟨hi, hlen, hrefund, _hbids, _hvalues, _hfakes, _hsecrets, hvariant, hidxLe,
      _henv, _hσ0, _hgh, _hbl, _hcreated, _hsub, _haccounts⟩
  exact ⟨hi, hlen, hrefund, hvariant, hidxLe⟩

theorem scratch_reveal_aw_call_empty (aw fp : UInt256) :
    UInt256.ofNat
      (MachineState.M (MachineState.M aw.toNat fp.toNat (⟨0⟩ : UInt256).toNat)
        fp.toNat (⟨0⟩ : UInt256).toNat) = aw := by
  simpa [MachineState.M] using (u256_ofNat_toNat aw)

theorem scratch_storageStore_σ0 (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).σ₀ = evm.σ₀ := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases h : evm.accountMap.find? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage, h]

theorem scratch_storageStore_genesisBlockHeader (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases h : evm.accountMap.find? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage, h]

theorem scratch_storageStore_blocks (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).blocks = evm.blocks := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases h : evm.accountMap.find? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage, h]

theorem scratch_storageStore_substate (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).substate = evm.substate := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases h : evm.accountMap.find? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage, h]

theorem scratch_revealLoopBody_refundOverflow_from1247_pair {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {values fakes secrets : List Value}
    {slot i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd
      valuesLen valuesEnd sel value secret fakeWord blinded deposit : UInt256}
    {fake : Bool} {fakeRaw : Value} {hashBytes : List UInt8}
    (rd : RD blindAuctionBytecode I g s0 ⟨1247⟩
      [secret, fakeWord, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (haw : 3 ≤ aw.toNat)
    (hdepositEvm :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hbids : L.get? "bids" = none)
    (hvalues : L.get? "values" = some (.array values))
    (hfakes : L.get? "fakes" = some (.array fakes))
    (hsecrets : L.get? "secrets" = some (.array secrets))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : L.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hboundBids : i.toNat < curLen.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf L evm i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hover : UInt256.size ≤ refund.toNat + deposit.toNat) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts .reverted ∧
      RDrev blindAuctionBytecode g s0 := by
  have hsrc :=
    scratch_revealLoopBody_revert_refundOverflow_of_get evm L values fakes secrets curLen refund
      i value secret blinded deposit fake fakeRaw
      hashBytes hbids hvalues hfakes hsecrets hi hrefund hlen hboundBids hboundValues
      hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup hblinded
      hdeposit hhash heq hover
  have rd1252₀ := evm_run rd with [jumpdest, push1 ⟨1⟩, dup5, add]
  obtain ⟨_, _, rd1253₀⟩ := rd1252₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1253⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1253⟩
      [deposit, secret, fakeWord, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [hdepositEvm] using rd1253₀⟩
  have rd2045 := evm_run rd1253 with [push2 ⟨1262⟩, swap1, dup8, push2 ⟨2045⟩,
    jump (by jump_dest)]
  exact ⟨hsrc,
    scratch_blindAuctionCheckedAddOverflowRevert
      (a := refund) (b := deposit) (ret := ⟨1262⟩)
      (R := [secret, fakeWord, value, slot, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel])
      rd2045 hover haw (by simp)⟩

theorem scratch_revealThreeScratchWrites_preserve_fp {mem : ByteArray}
    {fp key slot data : UInt256}
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fp)
    (hmem96 : 96 ≤ mem.size) :
    let mem1 := (UInt256.toByteArray key).write 0 mem 0 32
    let mem2 := (UInt256.toByteArray slot).write 0 mem1 32 32
    let mem3 := (UInt256.toByteArray data).write 0 mem2 0 32
    mem3.readWithPadding 64 32 = UInt256.toByteArray fp ∧ mem3.size = mem.size := by
  intro mem1 mem2 mem3
  have hmem1_read : mem1.readWithPadding 64 32 = UInt256.toByteArray fp := by
    dsimp [mem1]
    rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega)
      (by omega) (by omega)]
    exact hread
  have hmem1_size : mem1.size = mem.size := by
    dsimp [mem1]
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
    omega
  have hmem2_read : mem2.readWithPadding 64 32 = UInt256.toByteArray fp := by
    dsimp [mem2]
    rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])]
    · exact hmem1_read
    · rw [hmem1_size]
      omega
    · omega
    · rw [hmem1_size]
      omega
  have hmem2_size : mem2.size = mem.size := by
    dsimp [mem2]
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem1_size]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem1_size]
    omega
  have hmem3_read : mem3.readWithPadding 64 32 = UInt256.toByteArray fp := by
    dsimp [mem3]
    rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])]
    · exact hmem2_read
    · rw [hmem2_size]
      omega
    · omega
    · rw [hmem2_size]
      omega
  have hmem3_size : mem3.size = mem.size := by
    dsimp [mem3]
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem2_size]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem2_size]
    omega
  exact ⟨hmem3_read, hmem3_size⟩

theorem scratch_revealLoopBody_toPacked_fromElemSlot_cursor {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value secret fakeWord fp : UInt256}
    {fake : Bool}
    (rd : RD blindAuctionBytecode I g s0 ⟨1069⟩
      [slot, i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (haw : 3 ≤ aw.toNat) (hawSmall : aw.toNat * 32 < UInt256.size)
    (hfit128 : fp.toNat + 128 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fp)
    (hmem96 : 96 ≤ mem.size) (hfp96 : 96 ≤ fp.toNat)
    (hfpPrefix :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hvalueBound : i.toNat < valuesLen.toNat)
    (hfakesBound : i.toNat < fakesLen.toNat)
    (hsecretsBound : i.toNat < secretsLen.toNat)
    (hvalueLoad :
      uInt256OfByteArray (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + valuesEnd).toNat 32) =
        value)
    (hfakeSlt :
      UInt256.slt
          (UInt256.sub (UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩)
            (UInt256.mul ⟨32⟩ i + fakesEnd)) ⟨32⟩ = ⟨0⟩)
    (hfakeLoad :
      uInt256OfByteArray (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + fakesEnd).toNat 32) =
        fakeWord)
    (hfakeWord : fakeWord = if fake then (⟨1⟩ : UInt256) else ⟨0⟩)
    (hsecretLoad :
      uInt256OfByteArray (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + secretsEnd).toNat 32) =
        secret) :
    ∃ (newFree : UInt256) (memPacked : ByteArray) (awPacked : UInt256)
      (memNext : ByteArray) (awNext : UInt256) (k' C' : ℕ),
      RD blindAuctionBytecode I g s0 ⟨1207⟩
        [newFree, secret, fakeWord, value, slot, i, refund, len, revealEnd, biddingEnd,
          secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
        memPacked awPacked rdata (cA, σ) k' C' ∧
      3 ≤ awNext.toNat ∧
      awNext.toNat * 32 < UInt256.size ∧
      (if (⟨64⟩ : UInt256).toNat ≥ memNext.size ∨
          (⟨64⟩ : UInt256) ≥ awNext * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (memNext.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        newFree ∧
      memNext.readWithPadding 64 32 = UInt256.toByteArray newFree ∧
      96 ≤ memNext.size ∧
      memNext.size ≤ newFree.toNat + 32 ∧
      newFree.toNat + 32 - memNext.size < USize.size ∧
      newFree.toNat = fp.toNat + 97 ∧
      (if (⟨64⟩ : UInt256).toNat ≥ memPacked.size ∨
          (⟨64⟩ : UInt256) ≥ awPacked * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (memPacked.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        fp ∧
      (let base := (⟨32⟩ : UInt256) + fp
       let newFree := (⟨65⟩ : UInt256) + base
       let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
       let mem4 := scratch_revealPackedLenMem memPacked fp packedLen
       let aw1 := UInt256.ofNat (MachineState.M awPacked.toNat (⟨64⟩ : UInt256).toNat 32)
       let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
       let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
       let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
       if fp.toNat ≥ mem5.size ∨ fp ≥ aw3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem5.readWithPadding fp.toNat 32))) =
        UInt256.sub (UInt256.sub (((⟨65⟩ : UInt256) + ((⟨32⟩ : UInt256) + fp))) fp)
          ⟨32⟩ ∧
        (let base := (⟨32⟩ : UInt256) + fp
         let newFree := (⟨65⟩ : UInt256) + base
         let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
         let mem4 := scratch_revealPackedLenMem memPacked fp packedLen
         let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
         UInt256.ofNat
            (fromByteArrayBigEndian (ffi.KEC (mem5.readWithPadding base.toNat packedLen.toNat))) =
          uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) ∧
        newFree = (⟨65⟩ : UInt256) + ((⟨32⟩ : UInt256) + fp) ∧
        (let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
         let mem4 := scratch_revealPackedLenMem memPacked fp packedLen
         memNext = scratch_revealPackedFreePtrMem mem4 newFree) ∧
        (let base := (⟨32⟩ : UInt256) + fp
         let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
         let aw1 := UInt256.ofNat (MachineState.M awPacked.toNat (⟨64⟩ : UInt256).toNat 32)
         let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
         let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
         let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
         awNext = UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)) := by
  have hfit97 : fp.toNat + 97 < UInt256.size := by
    omega
  have hfp64 : 64 ≤ fp.toNat := by
    omega
  let awP1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let base := (⟨32⟩ : UInt256) + fp
  let fakeBase := base + ⟨32⟩
  let secretBase := base + ⟨33⟩
  let newFree := (⟨65⟩ : UInt256) + base
  let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
  let memP1 := scratch_revealPackedValueMem mem base value
  let awP2 := UInt256.ofNat (MachineState.M awP1.toNat base.toNat 32)
  let memP2 := scratch_revealPackedFakeMem memP1 fakeBase fakeWord
  let awP3 := UInt256.ofNat (MachineState.M awP2.toNat fakeBase.toNat 32)
  let memP3 := scratch_revealPackedSecretMem memP2 secretBase secret
  let awP4 := UInt256.ofNat (MachineState.M awP3.toNat secretBase.toNat 32)
  let memP4 := scratch_revealPackedLenMem memP3 fp packedLen
  let awS1 := UInt256.ofNat (MachineState.M awP4.toNat (⟨64⟩ : UInt256).toNat 32)
  let awS2 := UInt256.ofNat (MachineState.M awS1.toNat fp.toNat 32)
  let memP5 := scratch_revealPackedFreePtrMem memP4 newFree
  let awS3 := UInt256.ofNat (MachineState.M awS2.toNat (⟨64⟩ : UInt256).toNat 32)
  let awS4 := UInt256.ofNat (MachineState.M awS3.toNat fp.toNat 32)
  let awS5 := UInt256.ofNat (MachineState.M awS4.toNat base.toNat packedLen.toNat)
  have hAwFacts :
      newFree.toNat = fp.toNat + 97 ∧ packedLen.toNat = 65 ∧
        3 ≤ awS2.toNat ∧ awS2.toNat * 32 < UInt256.size ∧
        3 ≤ awP4.toNat ∧ awP4.toNat * 32 < UInt256.size ∧
        3 ≤ awS3.toNat ∧ awS3.toNat * 32 < UInt256.size ∧
        3 ≤ awS5.toNat ∧ awS5.toNat * 32 < UInt256.size := by
    simpa [awP1, base, fakeBase, secretBase, newFree, packedLen, awP2, awP3,
      awP4, awS1, awS2, awS3, awS4, awS5]
      using scratch_revealPacked_aw_facts (aw := aw) (fp := fp) haw hawSmall hfit128
  rcases hAwFacts with
    ⟨hnewFreeNat, _hpackedLenNat, hawS2, hawS2Small, hawP4, hawP4Small, _hawS3,
      _hawS3Small, hawS5, hawS5Small⟩
  have hreadP3 : memP3.readWithPadding 64 32 = UInt256.toByteArray fp := by
    simpa [base, fakeBase, secretBase, memP1, memP2, memP3]
      using scratch_revealPackedPrefix_preserve_fp (mem := mem) (fp := fp)
        (value := value) (fakeWord := fakeWord) (secret := secret) hfit97 hmemle hgap
        hread hmem96 hfp64
  have hsizeP3 : memP3.size = fp.toNat + 97 := by
    simpa [base, fakeBase, secretBase, memP1, memP2, memP3]
      using scratch_revealPackedPrefix_size (mem := mem) (fp := fp) (value := value)
        (fakeWord := fakeWord) (secret := secret) hfit97 hmemle hgap
  have hfpPacked :
      (if (⟨64⟩ : UInt256).toNat ≥ memP3.size ∨
          (⟨64⟩ : UInt256) ≥ awP4 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (memP3.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        fp := by
    exact scratch_mload_of_read
      (mem := memP3) (fp := (⟨64⟩ : UInt256)) (packedLen := fp) (aw := awP4)
      (by
        change 64 < memP3.size
        rw [hsizeP3]
        omega)
      (by simpa [awP4] using scratch_not_mload64_oob_of_aw_ge3_small hawP4 hawP4Small)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by decide] using hreadP3)
  have hreadLen : memP5.readWithPadding fp.toNat 32 = UInt256.toByteArray packedLen := by
    simpa [base, fakeBase, secretBase, newFree, packedLen, memP1, memP2, memP3,
      memP4, memP5]
      using scratch_revealPackedMem_len_read (mem := mem) (fp := fp) (value := value)
        (fakeWord := fakeWord) (secret := secret) hfit97 hmemle hgap hfp96
  have hsizeP5 : memP5.size = fp.toNat + 97 := by
    simpa [base, fakeBase, secretBase, newFree, packedLen, memP1, memP2, memP3,
      memP4, memP5]
      using scratch_revealPackedMem_size (mem := mem) (fp := fp) (value := value)
        (fakeWord := fakeWord) (secret := secret) hfit97 hmemle hgap
  have hlenPacked :
      (let base := (⟨32⟩ : UInt256) + fp
       let newFree := (⟨65⟩ : UInt256) + base
       let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
       let mem4 := scratch_revealPackedLenMem memP3 fp packedLen
       let aw1 := UInt256.ofNat (MachineState.M awP4.toNat (⟨64⟩ : UInt256).toNat 32)
       let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
       let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
       let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
       if fp.toNat ≥ mem5.size ∨ fp ≥ aw3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem5.readWithPadding fp.toNat 32))) =
        packedLen := by
    exact scratch_mload_of_read
      (mem := memP5) (fp := fp) (packedLen := packedLen) (aw := awS3)
      (by rw [hsizeP5]; omega)
      (by
        have hnotS2 : ¬ (fp ≥ awS2 * ⟨32⟩) := by
          simpa [awS2] using
            scratch_not_mload_oob_after_M32 (aw := awS1) (off := fp) hawS2Small
        have hS3eqS2 : awS3 = awS2 := by
          simpa [awS3] using scratch_reveal_aw_mload64_of_ge3 hawS2
        simpa [hS3eqS2] using hnotS2)
      hreadLen
  have hhashPacked :
      (let base := (⟨32⟩ : UInt256) + fp
       let newFree := (⟨65⟩ : UInt256) + base
       let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
       let mem4 := scratch_revealPackedLenMem memP3 fp packedLen
       let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
       UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC (mem5.readWithPadding base.toNat packedLen.toNat))) =
          uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) := by
    simpa [base, fakeBase, secretBase, newFree, packedLen, memP1, memP2, memP3,
      memP4, memP5]
      using scratch_revealPackedMem_hash (mem := mem) (fp := fp) (value := value)
        (fakeWord := fakeWord) (secret := secret) (fake := fake) hfit97 hmemle hgap hfp64
        hfakeWord
  have hreadFree : memP5.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    simpa [base, fakeBase, secretBase, newFree, packedLen, memP1, memP2, memP3,
      memP4, memP5]
      using scratch_revealPackedMem_freePtr_read (mem := mem) (fp := fp) (value := value)
        (fakeWord := fakeWord) (secret := secret) hfit97 hmemle hgap
  have hfpFinal :
      (if (⟨64⟩ : UInt256).toNat ≥ memP5.size ∨
          (⟨64⟩ : UInt256) ≥ awS5 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (memP5.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        newFree := by
    exact scratch_mload_of_read
      (mem := memP5) (fp := (⟨64⟩ : UInt256)) (packedLen := newFree) (aw := awS5)
      (by
        change 64 < memP5.size
        rw [hsizeP5]
        omega)
      (by simpa [awS5] using scratch_not_mload64_oob_of_aw_ge3_small hawS5 hawS5Small)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by decide] using hreadFree)
  obtain ⟨kLoad, CLoad, rd1987⟩ :=
    scratch_blindAuctionRevealX_loopBody_loads_toFakeDecoder
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
      (slot := slot) (i := i) (refund := refund) (len := len)
      (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
      (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
      (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) (value := value)
      rd hvalueBound hfakesBound hvalueLoad
  obtain ⟨kBool, CBool, rd1135⟩ :
      ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1135⟩
        [fakeWord, value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd, biddingEnd,
          secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
        mem aw rdata (cA, σ) k' C' := by
    cases fake with
    | false =>
        simp at hfakeWord
        obtain ⟨kBool, CBool, rd1135⟩ :=
          scratch_blindAuctionRevealX_loopBody_fakeDecoder_zero_toBool
            (I := I) (g := g) (s0 := s0) (k := kLoad) (C := CLoad)
            (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
            (slot := slot) (i := i) (refund := refund) (len := len)
            (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
            (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
            (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) (value := value)
            rd1987 hfakeSlt (by rw [hfakeLoad, hfakeWord])
        exact ⟨kBool, CBool, by simpa [hfakeWord] using rd1135⟩
    | true =>
        simp at hfakeWord
        obtain ⟨kBool, CBool, rd1135⟩ :=
          scratch_blindAuctionRevealX_loopBody_fakeDecoder_one_toBool
            (I := I) (g := g) (s0 := s0) (k := kLoad) (C := CLoad)
            (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
            (slot := slot) (i := i) (refund := refund) (len := len)
            (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
            (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
            (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) (value := value)
            rd1987 hfakeSlt (by rw [hfakeLoad, hfakeWord])
        exact ⟨kBool, CBool, by simpa [hfakeWord] using rd1135⟩
  obtain ⟨kSecret, CSecret, rd1167⟩ :=
    scratch_blindAuctionRevealX_loopBody_secret_toPacked
      (I := I) (g := g) (s0 := s0) (k := kBool) (C := CBool)
      (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
      (fakeWord := fakeWord) (value := value) (slot := slot) (i := i)
      (refund := refund) (len := len) (revealEnd := revealEnd) (biddingEnd := biddingEnd)
      (secretsLen := secretsLen) (secretsEnd := secretsEnd) (fakesLen := fakesLen)
      (fakesEnd := fakesEnd) (valuesLen := valuesLen) (valuesEnd := valuesEnd)
      (sel := sel) (secret := secret) rd1135 hsecretsBound hsecretLoad
  obtain ⟨kPrefix, CPrefix, rd1207Let⟩ :=
    scratch_blindAuctionRevealX_loopBody_packed_prefix
      (I := I) (g := g) (s0 := s0) (k := kSecret) (C := CSecret)
      (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
      (secret := secret) (fakeWord := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (fp := fp) rd1167 hfpPrefix
  have rd1207 :
      RD blindAuctionBytecode I g s0 ⟨1207⟩
        [newFree, secret, fakeWord, value, slot, i, refund, len, revealEnd, biddingEnd,
          secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
        memP3 awP4 rdata (cA, σ) kPrefix CPrefix := by
    simpa [awP1, base, fakeBase, secretBase, newFree, memP1, awP2, memP2, awP3,
      memP3, awP4] using rd1207Let
  refine ⟨newFree, memP3, awP4, memP5, awS5, kPrefix, CPrefix, rd1207, hawS5,
    hawS5Small, hfpFinal, hreadFree, ?_, ?_, ?_, hnewFreeNat, hfpPacked, ?_,
    hhashPacked, rfl, ?_, ?_⟩
  · rw [hsizeP5]
    omega
  · rw [hsizeP5, hnewFreeNat]
    omega
  · rw [hsizeP5, hnewFreeNat]
    have hsmall : 32 < USize.size := lt_usize 32 (by norm_num)
    omega
  · simpa [base, newFree, packedLen] using hlenPacked
  · simp [base, newFree, packedLen, memP4, memP5]
  · simp [awS1, awS2, awS3, awS4, awS5, base, newFree, packedLen]

theorem scratch_placeBidPendingHashMem_preserve_fp {mem : ByteArray} {fp key : UInt256}
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fp)
    (hmem96 : 96 ≤ mem.size) :
    (scratch_placeBidPendingHashMem mem key).readWithPadding 64 32 =
        UInt256.toByteArray fp ∧
      (scratch_placeBidPendingHashMem mem key).size = mem.size := by
  let memKey := scratch_placeBidPendingKeyMem mem key
  have hkeyRead : memKey.readWithPadding 64 32 = UInt256.toByteArray fp := by
    dsimp [memKey, scratch_placeBidPendingKeyMem]
    rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega)
      (by omega) (by omega)]
    exact hread
  have hkeySize : memKey.size = mem.size := by
    dsimp [memKey, scratch_placeBidPendingKeyMem]
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
    omega
  have hhashRead :
      (scratch_placeBidPendingHashMem mem key).readWithPadding 64 32 =
        UInt256.toByteArray fp := by
    dsimp [scratch_placeBidPendingHashMem, memKey]
    rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])]
    · exact hkeyRead
    · rw [hkeySize]
      omega
    · omega
    · rw [hkeySize]
      omega
  have hhashSize :
      (scratch_placeBidPendingHashMem mem key).size = mem.size := by
    dsimp [scratch_placeBidPendingHashMem, memKey]
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hkeySize]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hkeySize]
    omega
  exact ⟨hhashRead, hhashSize⟩

theorem scratch_blindAuctionRevealX_loopBody_toElemSlot_curLen_concrete {I} {g : Sat256}
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
      (ffi.KEC
        (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
          ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
            32 32).readWithPadding 0 64)) =
        UInt256.toByteArray (revealScratchBidsLengthSlot I))
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
    let mem1 : ByteArray := (UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32
    let mem2 : ByteArray := (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 mem1 32 32
    let mem3 : ByteArray := (UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0 mem2 0 32
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1069⟩
      [bidsElemSlot (.address I.source) (.int (Int.ofNat i.toNat)), i, refund, len, revealEnd,
        biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem3 aw rdata acc k' C' := by
  intro mem1 mem2 mem3
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
        rw [show (⟨32⟩ : UInt256).toNat = 32 by decide +native]
        rw [haw32]
        simp)
      (by rfl) haw32 (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (revealScratchBidsLengthSlot I) aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨64⟩ : UInt256).toNat = 64 by decide +native]
        rw [haw64]
        simp)
      (by
        have hword :
            UInt256.ofNat (fromByteArrayBigEndian
              (ffi.KEC
                (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
                  ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
                    32 32).readWithPadding 0 64))) =
              revealScratchBidsLengthSlot I := by
          have hdecode := congrArg
            (fun arr => UInt256.ofNat (fromByteArrayBigEndian arr)) hbaseHash
          simpa [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat] using hdecode
        simpa [mem2, mem1, revealScratchSenderWord] using hword) haw64
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
        rw [show (⟨32⟩ : UInt256).toNat = 32 by decide +native]
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
    decide +native
  exact ⟨_, _, by simpa [hslot, hpc1069] using rd1069⟩

theorem scratch_blindAuctionDecode_reveal_fakes_slt {I : ExecutionEnv} {callargs : Store}
    {values fakes secrets : List Value} {i : UInt256} {word : Nat}
    (hsize : I.calldata.size < UInt256.size)
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hstore :
      callargs =
        (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
          "secrets" (.array secrets))
    (hlookup : lookupNth? fakes i.toNat = some (rawBoolWordValue word)) :
    UInt256.slt
      (UInt256.sub
        (UInt256.mul ⟨32⟩ i + (((⟨4⟩ : UInt256) + revealFakesOffsetWord I) + ⟨32⟩) +
          ⟨32⟩)
        (UInt256.mul ⟨32⟩ i + (((⟨4⟩ : UInt256) + revealFakesOffsetWord I) + ⟨32⟩)))
      ⟨32⟩ = ⟨0⟩ := by
  obtain ⟨_e0, _e1, _e2, _hval0, hval1, _hval2⟩ :=
    blindAuctionDecode_reveal_array_decodes hdec hstore
  have hread :
      readNat? (List.drop 4 I.calldata.toList)
        ((revealFakesOffsetWord I).toNat + 32 + 32 * i.toNat) = some word := by
    exact revealDecode_dynamicArray_bool_lookup_readNat hval1 hlookup
  have hreadLen := readNat?_some_length hread
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hbound :
      4 + ((revealFakesOffsetWord I).toNat + 32 + 32 * i.toNat) + 32 ≤
        I.calldata.size := by
    rw [List.length_drop, htlen] at hreadLen
    omega
  let start : UInt256 :=
    UInt256.mul ⟨32⟩ i + (((⟨4⟩ : UInt256) + revealFakesOffsetWord I) + ⟨32⟩)
  have hstart :
      start.toNat = 4 + ((revealFakesOffsetWord I).toNat + 32 + 32 * i.toNat) := by
    dsimp [start]
    exact revealArrayElemAddr_toNat (off := revealFakesOffsetWord I) (i := i)
      (lim := I.calldata.size) hbound hsize
  have hplus : (start + ⟨32⟩).toNat = start.toNat + 32 := by
    rw [uadd_toNat]
    change (start.toNat + 32) % UInt256.size = start.toNat + 32
    apply Nat.mod_eq_of_lt
    rw [hstart]
    omega
  have hsubToNat : (UInt256.sub (start + ⟨32⟩) start).toNat = 32 := by
    rw [usub_toNat]
    · rw [hplus]
      omega
    · rw [hplus]
      omega
  have hsubEq : UInt256.sub (start + ⟨32⟩) start = ⟨32⟩ := by
    apply u256_inj
    rw [hsubToNat]
    rfl
  change UInt256.slt (UInt256.sub (start + ⟨32⟩) start) ⟨32⟩ = ⟨0⟩
  rw [hsubEq]
  decide +native

theorem scratch_blindAuctionDecode_reveal_fakes_word_toNat {I : ExecutionEnv}
    {callargs : Store} {values fakes secrets : List Value} {i : UInt256} {word : Nat}
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hstore :
      callargs =
        (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
          "secrets" (.array secrets))
    (hlookup : lookupNth? fakes i.toNat = some (rawBoolWordValue word)) :
    (UInt256.ofNat word).toNat = word := by
  obtain ⟨_e0, _e1, _e2, _hval0, hval1, _hval2⟩ :=
    blindAuctionDecode_reveal_array_decodes hdec hstore
  have hread :
      readNat? (List.drop 4 I.calldata.toList)
        ((revealFakesOffsetWord I).toNat + 32 + 32 * i.toNat) = some word := by
    exact revealDecode_dynamicArray_bool_lookup_readNat hval1 hlookup
  have hreadLen := readNat?_some_length hread
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hbound :
      4 + ((revealFakesOffsetWord I).toNat + 32 + 32 * i.toNat) + 32 ≤
        I.calldata.size := by
    rw [List.length_drop, htlen] at hreadLen
    omega
  unfold readNat? readWord? readBytes? at hread
  have hle :
      32 ≤ (List.drop 4 I.calldata.toList).length -
        ((revealFakesOffsetWord I).toNat + 32 + 32 * i.toNat) := by
    omega
  have hleFull :
      32 ≤ I.calldata.toList.length -
        (4 + ((revealFakesOffsetWord I).toNat + 32 + 32 * i.toNat)) := by
    rw [htlen]
    omega
  simp [hle, hleFull, List.drop_drop] at hread
  cases hread
  exact ulit_toNat' _
    (bytesToWord
      (List.take 32
        (List.drop (4 + ((revealFakesOffsetWord I).toNat + 32 + 32 * i.toNat))
          I.calldata.toList))).val.isLt

theorem scratch_normalizeRawBoolWord_false_of_u256 {word : Nat}
    (hword : (UInt256.ofNat word).toNat = word) (hzero : UInt256.ofNat word = ⟨0⟩) :
    normalizeRawBoolWord? (rawBoolWordValue word) = .ok (.bool false) := by
  have hword0 : word = 0 := by
    have h := congrArg UInt256.toNat hzero
    simpa [hword] using h
  subst word
  rfl

theorem scratch_normalizeRawBoolWord_true_of_u256 {word : Nat}
    (hword : (UInt256.ofNat word).toNat = word) (hone : UInt256.ofNat word = ⟨1⟩) :
    normalizeRawBoolWord? (rawBoolWordValue word) = .ok (.bool true) := by
  have hword1 : word = 1 := by
    have h := congrArg UInt256.toNat hone
    simpa [hword] using h
  subst word
  rfl

theorem scratch_normalizeRawBoolWord_revert_of_u256 {word : Nat}
    (hword : (UInt256.ofNat word).toNat = word)
    (hzero : UInt256.ofNat word ≠ ⟨0⟩) (hone : UInt256.ofNat word ≠ ⟨1⟩) :
    normalizeRawBoolWord? (rawBoolWordValue word) = .revert := by
  have hword0 : word ≠ 0 := by
    intro h0
    apply hzero
    subst word
    rfl
  have hword1 : word ≠ 1 := by
    intro h1
    apply hone
    subst word
    rfl
  simp [normalizeRawBoolWord?, rawBoolWordValue, hword0, hword1]

theorem scratch_revealLoopBody_hashMatch_noPlace_fromPacked_pair {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {values fakes secrets : List Value}
    {slot i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd
      valuesLen valuesEnd sel value secret fakeWord blinded deposit fp : UInt256}
    {fake : Bool} {fakeRaw : Value}
    (rd : RD blindAuctionBytecode I g s0 ⟨1207⟩
      [((⟨65⟩ : UInt256) + ((⟨32⟩ : UInt256) + fp)), secret, fakeWord, value, slot,
        i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hlenPacked :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
      (if fp.toNat ≥ mem5.size ∨ fp ≥ aw3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem5.readWithPadding fp.toNat 32))) =
        packedLen)
    (hhashPacked :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (mem5.readWithPadding base.toNat packedLen.toNat))) =
        uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)))
    (hstore :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩) = blinded)
    (hflag :
      UInt256.eq blinded
          (uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) =
        ⟨1⟩)
    (hdepositEvm :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hperm : I.perm = true)
    (hbids : L.get? "bids" = none)
    (hvalues : L.get? "values" = some (.array values))
    (hfakes : L.get? "fakes" = some (.array fakes))
    (hsecrets : L.get? "secrets" = some (.array secrets))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : L.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hboundBids : i.toNat < curLen.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hfakeWord : fakeWord = if fake then (⟨1⟩ : UInt256) else ⟨0⟩)
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hskipPlace : fake = true ∨ deposit.toNat < value.toNat) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.ok
          { contract := blindAuctionContract,
            locals := scratch_revealRefundAddedStoreOf L evm i refund value secret deposit fake }
          (scratch_revealZeroBlindedState evm i)) ∧
      ∃ k' C',
        let base := (⟨32⟩ : UInt256) + fp
        let newFree := (⟨65⟩ : UInt256) + base
        let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
        let mem4 := scratch_revealPackedLenMem mem fp packedLen
        let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
        let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
        let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
        let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
        let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
        let aw5 := UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)
        RD blindAuctionBytecode I g s0 ⟨1014⟩
          (scratch_revealEvmLoopStack (i + ⟨1⟩) (deposit + refund) len revealEnd biddingEnd
            secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
          mem5 aw5 rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k' C' := by
  let base := (⟨32⟩ : UInt256) + fp
  let newFree := (⟨65⟩ : UInt256) + base
  let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
  let mem4 := scratch_revealPackedLenMem mem fp packedLen
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
  let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
  let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
  let aw5 := UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)
  have heq :
      EVM.Word.toBytesBE blinded =
        (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList := by
    exact scratch_revealPackedHash_eq_of_u256_eq_one
      (blinded := blinded) (value := value) (secret := secret) (fake := fake) hflag
  have hhashEval := scratch_evalExpr_revealPackedHash_of_secretStoreOf evm L i value secret fake
  have hsrc :=
    scratch_revealLoopBody_ok_noPlace_of_get evm L values fakes secrets curLen refund i value
      secret blinded deposit fake fakeRaw
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList
      hbids hvalues hfakes hsecrets hi hrefund hlen hboundBids hboundValues hboundFakes
      hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup hblinded hdeposit
      hhashEval heq hfit hskipPlace
  obtain ⟨k1, C1, rd1235⟩ :=
    scratch_blindAuctionRevealX_loopBody_packed_suffix
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem) (aw := aw) (rdata := rdata) (cA := cA) (σ := σ)
      (secret := secret) (fakeWord := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (fp := fp)
      (hash :=
        uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)))
      (blinded := blinded) (flag := ⟨1⟩)
      rd hfp hlenPacked hhashPacked hstore hflag
  obtain ⟨k2, C2, rd1247⟩ :=
    scratch_blindAuctionRevealX_hashGuard_match_to1247
      (I := I) (g := g) (s0 := s0) (k := k1) (C := C1)
      (rdata := rdata) (acc := (cA, σ))
      (secret := secret) (fake := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) rd1235
  obtain ⟨k3, C3, rd1265⟩ :=
    scratch_blindAuctionRevealX_refundAdd_toPlaceCond
      (I := I) (g := g) (s0 := s0) (k := k2) (C := C2)
      (rdata := rdata) (cA := cA) (σ := σ)
      (secret := secret) (fake := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (deposit := deposit) rd1247 hdepositEvm hfit
  cases fake with
  | false =>
      simp at hfakeWord
      rcases hskipPlace with hfakeTrue | hlt
      · cases hfakeTrue
      · obtain ⟨k4, C4, rdNext⟩ :=
          scratch_blindAuctionRevealX_placeCond_depositLt_toNext
            (I := I) (g := g) (s0 := s0) (k := k3) (C := C3)
            (rdata := rdata) (cA := cA) (σ := σ)
            (secret := secret) (value := value) (slot := slot) (i := i)
            (refund := deposit + refund) (len := len) (revealEnd := revealEnd)
            (biddingEnd := biddingEnd) (secretsLen := secretsLen)
            (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
            (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel)
            (deposit := deposit) (by simpa [hfakeWord] using rd1265) hdepositEvm hlt hperm
        exact ⟨hsrc, ⟨k4, C4, by
          simpa [base, newFree, packedLen, mem4, mem5, aw1, aw2, aw3, aw4, aw5]
            using rdNext⟩⟩
  | true =>
      simp at hfakeWord
      obtain ⟨k4, C4, rdNext⟩ :=
        scratch_blindAuctionRevealX_placeCond_fake_toNext
          (I := I) (g := g) (s0 := s0) (k := k3) (C := C3)
          (rdata := rdata) (cA := cA) (σ := σ)
          (secret := secret) (value := value) (slot := slot) (i := i)
          (refund := deposit + refund) (len := len) (revealEnd := revealEnd)
          (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
          (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
          (valuesEnd := valuesEnd) (sel := sel) (by simpa [hfakeWord] using rd1265) hperm
      exact ⟨hsrc, ⟨k4, C4, by
        simpa [base, newFree, packedLen, mem4, mem5, aw1, aw2, aw3, aw4, aw5]
          using rdNext⟩⟩

private theorem scratch_revealRefundAddedStoreOf_get_preserve_cases (locals : Store)
    (evm : EVM.State) (i refund value secret deposit : UInt256) (fake : Bool) {name : Ident}
    (hrefund : ("refund" == name) = false)
    (hsecret : ("secret" == name) = false)
    (hfake : ("fake" == name) = false)
    (hvalue : ("value" == name) = false)
    (hbid : ("bidToCheck" == name) = false) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get? name =
      locals.get? name := by
  unfold scratch_revealRefundAddedStoreOf scratch_revealSecretStoreOf scratch_revealFakeStoreOf
    scratch_revealValueStoreOf scratch_revealBidToCheckStoreOf
  rw [store_get_ne5]
  · exact hbid
  · exact hvalue
  · exact hfake
  · exact hsecret
  · exact hrefund

theorem scratch_revealLoopAdvance_refundAdded_zeroBlinded {I} {g : Sat256}
    {s0 : State} {σ₀ : AccountMap} {gh : BlockHeader} {bl : ProcessedBlocks}
    {A : Substate} {v k C : ℕ}
    {loopLen slot revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value secret deposit newFree : UInt256}
    {memNext : ByteArray} {awNext : UInt256}
    {values fakes secrets : List Value} {a : RevealLoopCursor} {L : Store}
    {evm : EVM.State} {fake : Bool}
    (hInv : RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A (v + 1) a L evm)
    (hbodyOk :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.ok
          { contract := blindAuctionContract,
            locals :=
              scratch_revealRefundAddedStoreOf L evm a.idx a.refund value secret deposit fake }
          (scratch_revealZeroBlindedState evm a.idx)))
    (rdNext : RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (a.idx + ⟨1⟩) (deposit + a.refund) loopLen
        revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      memNext awNext ByteArray.empty
      (a.acc.1, sstoreAccountMap I.codeOwner a.acc.2 slot ⟨0⟩) k C)
    (hslot : slot = bidsElemSlot (.address I.source) (.int (Int.ofNat a.idx.toNat)))
    (hfit : a.refund.toNat + deposit.toNat < UInt256.size)
    (hawNext : 3 ≤ awNext.toNat)
    (hawNextSmall : awNext.toNat * 32 < UInt256.size)
    (hfpNext :
      (if (⟨64⟩ : UInt256).toNat ≥ memNext.size ∨ (⟨64⟩ : UInt256) ≥ awNext * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (memNext.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        newFree)
    (hreadNext : memNext.readWithPadding 64 32 = UInt256.toByteArray newFree)
    (hmemNext96 : 96 ≤ memNext.size)
    (hmemNextLe : memNext.size ≤ newFree.toNat + 32)
    (hgapNext : newFree.toNat + 32 - memNext.size < USize.size)
    (hnextFpNat : newFree.toNat = a.fp.toNat + 97) :
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
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A v a' L2 evm2 ∧
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack a'.idx a'.refund loopLen revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        a'.mem a'.aw ByteArray.empty a'.acc k' C' := by
  rcases hInv with
    ⟨hiL, hlenL, _hrefundL, hbidsL, hvaluesL, hfakesL, hsecretsL,
      hvariant, hidxLe, henv, hσ0, hgh, hbl, hcreated, hsub, haccounts⟩
  have hidxFit : a.idx.toNat + 1 < UInt256.size := by
    have hloopLt : loopLen.toNat < UInt256.size := loopLen.val.isLt
    omega
  let L1 : Store :=
    scratch_revealRefundAddedStoreOf L evm a.idx a.refund value secret deposit fake
  let nextIdx : UInt256 := a.idx + ⟨1⟩
  let L2 : Store := L1.insert "i" (.int (Int.ofNat nextIdx.toNat))
  have hiL1 :
      L1.get? "i" = some (.int (Int.ofNat a.idx.toNat)) := by
    have hpreserve : L1.get? "i" = L.get? "i" := by
      simpa [L1] using
        scratch_revealRefundAddedStoreOf_get_preserve_cases L evm a.idx a.refund value secret
          deposit fake (name := "i") (by decide) (by decide) (by decide) (by decide)
          (by decide)
    rw [hpreserve]
    exact hiL
  have hlenL1 :
      L1.get? "length" = some (.int (Int.ofNat loopLen.toNat)) := by
    have hpreserve : L1.get? "length" = L.get? "length" := by
      simpa [L1] using
        scratch_revealRefundAddedStoreOf_get_preserve_cases L evm a.idx a.refund value secret
          deposit fake (name := "length") (by decide) (by decide) (by decide) (by decide)
          (by decide)
    rw [hpreserve]
    exact hlenL
  have hbidsL1 : L1.get? "bids" = none := by
    have hpreserve : L1.get? "bids" = L.get? "bids" := by
      simpa [L1] using
        scratch_revealRefundAddedStoreOf_get_preserve_cases L evm a.idx a.refund value secret
          deposit fake (name := "bids") (by decide) (by decide) (by decide) (by decide)
          (by decide)
    rw [hpreserve]
    exact hbidsL
  have hvaluesL1 :
      L1.get? "values" = some (.array values) := by
    have hpreserve : L1.get? "values" = L.get? "values" := by
      simpa [L1] using
        scratch_revealRefundAddedStoreOf_get_preserve_cases L evm a.idx a.refund value secret
          deposit fake (name := "values") (by decide) (by decide) (by decide) (by decide)
          (by decide)
    rw [hpreserve]
    exact hvaluesL
  have hfakesL1 :
      L1.get? "fakes" = some (.array fakes) := by
    have hpreserve : L1.get? "fakes" = L.get? "fakes" := by
      simpa [L1] using
        scratch_revealRefundAddedStoreOf_get_preserve_cases L evm a.idx a.refund value secret
          deposit fake (name := "fakes") (by decide) (by decide) (by decide) (by decide)
          (by decide)
    rw [hpreserve]
    exact hfakesL
  have hsecretsL1 :
      L1.get? "secrets" = some (.array secrets) := by
    have hpreserve : L1.get? "secrets" = L.get? "secrets" := by
      simpa [L1] using
        scratch_revealRefundAddedStoreOf_get_preserve_cases L evm a.idx a.refund value secret
          deposit fake (name := "secrets") (by decide) (by decide) (by decide) (by decide)
          (by decide)
    rw [hpreserve]
    exact hsecretsL
  have hpost :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 }
        (scratch_revealZeroBlindedState evm a.idx) scratch_revealLoopPostStmts
        (.ok { contract := blindAuctionContract, locals := L2 }
          (scratch_revealZeroBlindedState evm a.idx)) := by
    simpa [L2, nextIdx] using
      scratch_revealLoopPostStep (scratch_revealZeroBlindedState evm a.idx) L1 a.idx hiL1
        hidxFit
  let nextCursor : RevealLoopCursor :=
    { idx := nextIdx,
      refund := deposit + a.refund,
      mem := memNext,
      aw := awNext,
      acc := (a.acc.1, sstoreAccountMap I.codeOwner a.acc.2 slot ⟨0⟩),
      fp := newFree,
      haw := hawNext,
      hawSmall := hawNextSmall,
      hfpLoad := hfpNext,
      hfpRead := hreadNext,
      hmem96 := hmemNext96,
      hmemle := hmemNextLe,
      hgap := hgapNext,
      hfpIdx := by
        have hadd : nextIdx.toNat = a.idx.toNat + 1 := by
          simpa [nextIdx] using add1_toNat hidxFit
        rw [hnextFpNat, a.hfpIdx, hadd]
        omega }
  have hrefundNext :
      L1.get? "refund" =
        some (.int (Int.ofNat ((deposit + a.refund).toNat))) := by
    have hadd : (deposit + a.refund).toNat = deposit.toNat + a.refund.toNat := by
      rw [uadd_toNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hcomm : a.refund + deposit = deposit + a.refund := u256_add_comm _ _
    simpa [L1, hcomm, hadd, Nat.add_comm] using
      scratch_revealRefundAddedStoreOf_refund_get L evm a.idx a.refund value secret deposit fake
  have haccountsNext :
      accountMapEquiv (sstoreAccountMap I.codeOwner a.acc.2 slot ⟨0⟩)
        (scratch_revealZeroBlindedState evm a.idx).accountMap := by
    unfold scratch_revealZeroBlindedState
    rw [storageStore_accountMap]
    simpa [scratch_revealBidBlindedSlot, hslot, henv, EVM.Word.ofNat] using
      accountMapEquiv_sstoreAccountMap I.codeOwner slot (⟨0⟩ : UInt256) haccounts
  have hInvNext :
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A v nextCursor L2
        (scratch_revealZeroBlindedState evm a.idx) := by
    refine
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [L2, nextIdx, nextCursor, store_get_self]
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "length" =
        some (.int (Int.ofNat loopLen.toNat))
      rw [store_get_ne]
      · exact hlenL1
      · decide
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "refund" =
        some (.int (Int.ofNat nextCursor.refund.toNat))
      rw [store_get_ne]
      · simpa [nextCursor] using hrefundNext
      · decide
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "bids" = none
      rw [store_get_ne]
      · exact hbidsL1
      · decide
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "values" =
        some (.array values)
      rw [store_get_ne]
      · exact hvaluesL1
      · decide
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "fakes" =
        some (.array fakes)
      rw [store_get_ne]
      · exact hfakesL1
      · decide
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "secrets" =
        some (.array secrets)
      rw [store_get_ne]
      · exact hsecretsL1
      · decide
    · have hadd : (a.idx + ⟨1⟩ : UInt256).toNat = a.idx.toNat + 1 := add1_toNat hidxFit
      simp [nextCursor, nextIdx, hadd]
      omega
    · have hadd : (a.idx + ⟨1⟩ : UInt256).toNat = a.idx.toNat + 1 := add1_toNat hidxFit
      simp [nextCursor, nextIdx, hadd]
      omega
    · simpa [scratch_revealZeroBlindedState, storageStore_executionEnv, henv] using henv
    · unfold scratch_revealZeroBlindedState Solm.EVM.storageStore State.lookupAccount
      cases h : evm.accountMap.find? evm.executionEnv.codeOwner <;>
        simp [Option.option, State.setAccount, Account.updateStorage, h, hσ0]
    · unfold scratch_revealZeroBlindedState Solm.EVM.storageStore State.lookupAccount
      cases h : evm.accountMap.find? evm.executionEnv.codeOwner <;>
        simp [Option.option, State.setAccount, Account.updateStorage, h, hgh]
    · unfold scratch_revealZeroBlindedState Solm.EVM.storageStore State.lookupAccount
      cases h : evm.accountMap.find? evm.executionEnv.codeOwner <;>
        simp [Option.option, State.setAccount, Account.updateStorage, h, hbl]
    · simpa [nextCursor, scratch_revealZeroBlindedState, storageStore_createdAccounts]
        using hcreated
    · unfold scratch_revealZeroBlindedState Solm.EVM.storageStore State.lookupAccount
      cases h : evm.accountMap.find? evm.executionEnv.codeOwner <;>
        simp [Option.option, State.setAccount, Account.updateStorage, h, hsub]
    · simpa [nextCursor] using haccountsNext
  exact
      ⟨nextCursor, L1, scratch_revealZeroBlindedState evm a.idx, L2,
        scratch_revealZeroBlindedState evm a.idx, k, C, Or.inl (by simpa [L1] using hbodyOk),
        hpost, hInvNext, by simpa [nextCursor, nextIdx, L1] using rdNext⟩

theorem scratch_revealLoopAdvance_of_get {I} {g : Sat256}
    {s0 : State} {σ₀ : AccountMap} {gh : BlockHeader} {bl : ProcessedBlocks}
    {A : Substate} {v k C : ℕ}
    {loopLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd
      sel newRefund newFree : UInt256}
    {memNext : ByteArray} {awNext : UInt256}
    {values fakes secrets : List Value} {a : RevealLoopCursor} {L L1 : Store}
    {evm evm1 : EVM.State} {accNext : Batteries.RBSet AccountAddress compare × AccountMap}
    (hInv : RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A (v + 1) a L evm)
    (hbodyOk :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts (.ok { contract := blindAuctionContract, locals := L1 } evm1))
    (rdNext : RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (a.idx + ⟨1⟩) newRefund loopLen revealEnd biddingEnd
        secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      memNext awNext ByteArray.empty accNext k C)
    (hiL1 : L1.get? "i" = some (.int (Int.ofNat a.idx.toNat)))
    (hlenL1 : L1.get? "length" = some (.int (Int.ofNat loopLen.toNat)))
    (hrefundL1 : L1.get? "refund" = some (.int (Int.ofNat newRefund.toNat)))
    (hbidsL1 : L1.get? "bids" = none)
    (hvaluesL1 : L1.get? "values" = some (.array values))
    (hfakesL1 : L1.get? "fakes" = some (.array fakes))
    (hsecretsL1 : L1.get? "secrets" = some (.array secrets))
    (henv1 : evm1.executionEnv = I)
    (hσ01 : evm1.σ₀ = σ₀)
    (hgh1 : evm1.genesisBlockHeader = gh)
    (hbl1 : evm1.blocks = bl)
    (hcreated1 : evm1.createdAccounts = accNext.1)
    (hsub1 : evm1.substate = A)
    (haccounts1 : accountMapEquiv accNext.2 evm1.accountMap)
    (hawNext : 3 ≤ awNext.toNat)
    (hawNextSmall : awNext.toNat * 32 < UInt256.size)
    (hfpNext :
      (if (⟨64⟩ : UInt256).toNat ≥ memNext.size ∨ (⟨64⟩ : UInt256) ≥ awNext * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (memNext.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        newFree)
    (hreadNext : memNext.readWithPadding 64 32 = UInt256.toByteArray newFree)
    (hmemNext96 : 96 ≤ memNext.size)
    (hmemNextLe : memNext.size ≤ newFree.toNat + 32)
    (hgapNext : newFree.toNat + 32 - memNext.size < USize.size)
    (hnextFpNat : newFree.toNat = a.fp.toNat + 97) :
    ∃ a' L1' evm1' L2 evm2 k' C',
      (ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
          scratch_revealLoopBodyStmts
          (.ok { contract := blindAuctionContract, locals := L1' } evm1') ∨
        ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
          scratch_revealLoopBodyStmts
          (.continue { contract := blindAuctionContract, locals := L1' } evm1')) ∧
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1' } evm1'
        scratch_revealLoopPostStmts
        (.ok { contract := blindAuctionContract, locals := L2 } evm2) ∧
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A v a' L2 evm2 ∧
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack a'.idx a'.refund loopLen revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        a'.mem a'.aw ByteArray.empty a'.acc k' C' := by
  rcases hInv with
    ⟨_hiL, _hlenL, _hrefundL, _hbidsL, _hvaluesL, _hfakesL, _hsecretsL,
      hvariant, hidxLe, _henv, _hσ0, _hgh, _hbl, _hcreated, _hsub, _haccounts⟩
  have hidxFit : a.idx.toNat + 1 < UInt256.size := by
    have hloopLt : loopLen.toNat < UInt256.size := loopLen.val.isLt
    omega
  let nextIdx : UInt256 := a.idx + ⟨1⟩
  let L2 : Store := L1.insert "i" (.int (Int.ofNat nextIdx.toNat))
  have hpost :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 }
        evm1 scratch_revealLoopPostStmts
        (.ok { contract := blindAuctionContract, locals := L2 } evm1) := by
    simpa [L2, nextIdx] using scratch_revealLoopPostStep evm1 L1 a.idx hiL1 hidxFit
  let nextCursor : RevealLoopCursor :=
    { idx := nextIdx,
      refund := newRefund,
      mem := memNext,
      aw := awNext,
      acc := accNext,
      fp := newFree,
      haw := hawNext,
      hawSmall := hawNextSmall,
      hfpLoad := hfpNext,
      hfpRead := hreadNext,
      hmem96 := hmemNext96,
      hmemle := hmemNextLe,
      hgap := hgapNext,
      hfpIdx := by
        have hadd : nextIdx.toNat = a.idx.toNat + 1 := by
          simpa [nextIdx] using add1_toNat hidxFit
        rw [hnextFpNat, a.hfpIdx, hadd]
        omega }
  have hInvNext :
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A v nextCursor L2 evm1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [L2, nextIdx, nextCursor, store_get_self]
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "length" =
        some (.int (Int.ofNat loopLen.toNat))
      rw [store_get_ne]
      · exact hlenL1
      · decide
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "refund" =
        some (.int (Int.ofNat nextCursor.refund.toNat))
      rw [store_get_ne]
      · simpa [nextCursor] using hrefundL1
      · decide
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "bids" = none
      rw [store_get_ne]
      · exact hbidsL1
      · decide
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "values" =
        some (.array values)
      rw [store_get_ne]
      · exact hvaluesL1
      · decide
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "fakes" =
        some (.array fakes)
      rw [store_get_ne]
      · exact hfakesL1
      · decide
    · change (L1.insert "i" (.int (Int.ofNat nextIdx.toNat))).get? "secrets" =
        some (.array secrets)
      rw [store_get_ne]
      · exact hsecretsL1
      · decide
    · have hadd : (a.idx + ⟨1⟩ : UInt256).toNat = a.idx.toNat + 1 := add1_toNat hidxFit
      simp [nextCursor, nextIdx, hadd]
      omega
    · have hadd : (a.idx + ⟨1⟩ : UInt256).toNat = a.idx.toNat + 1 := add1_toNat hidxFit
      simp [nextCursor, nextIdx, hadd]
      omega
    · exact henv1
    · exact hσ01
    · exact hgh1
    · exact hbl1
    · simpa [nextCursor] using hcreated1
    · exact hsub1
    · simpa [nextCursor] using haccounts1
  exact
    ⟨nextCursor, L1, evm1, L2, evm1, k, C, Or.inl hbodyOk, hpost, hInvNext,
      by simpa [nextCursor, nextIdx] using rdNext⟩

theorem scratch_revealLoopAdvance_refundAddedOk_zeroBlinded {I} {g : Sat256}
    {s0 : State} {σ₀ : AccountMap} {gh : BlockHeader} {bl : ProcessedBlocks}
    {A : Substate} {v k C : ℕ}
    {loopLen slot revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value secret deposit newFree : UInt256}
    {memNext : ByteArray} {awNext : UInt256}
    {values fakes secrets : List Value} {a : RevealLoopCursor} {L : Store}
    {evm : EVM.State}
    (hInv : RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A (v + 1) a L evm)
    (hbodyOk :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.ok
          { contract := blindAuctionContract,
            locals :=
              (scratch_revealRefundAddedStoreOf L evm a.idx a.refund value secret deposit false)
                |>.insert "ok" (.bool false) }
          (scratch_revealZeroBlindedState evm a.idx)))
    (rdNext : RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (a.idx + ⟨1⟩) (deposit + a.refund) loopLen
        revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      memNext awNext ByteArray.empty
      (a.acc.1, sstoreAccountMap I.codeOwner a.acc.2 slot ⟨0⟩) k C)
    (hslot : slot = bidsElemSlot (.address I.source) (.int (Int.ofNat a.idx.toNat)))
    (hfit : a.refund.toNat + deposit.toNat < UInt256.size)
    (hawNext : 3 ≤ awNext.toNat)
    (hawNextSmall : awNext.toNat * 32 < UInt256.size)
    (hfpNext :
      (if (⟨64⟩ : UInt256).toNat ≥ memNext.size ∨ (⟨64⟩ : UInt256) ≥ awNext * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (memNext.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        newFree)
    (hreadNext : memNext.readWithPadding 64 32 = UInt256.toByteArray newFree)
    (hmemNext96 : 96 ≤ memNext.size)
    (hmemNextLe : memNext.size ≤ newFree.toNat + 32)
    (hgapNext : newFree.toNat + 32 - memNext.size < USize.size)
    (hnextFpNat : newFree.toNat = a.fp.toNat + 97) :
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
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A v a' L2 evm2 ∧
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack a'.idx a'.refund loopLen revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        a'.mem a'.aw ByteArray.empty a'.acc k' C' := by
  have hInvOrig := hInv
  rcases hInv with
    ⟨hiL, hlenL, _hrefundL, hbidsL, hvaluesL, hfakesL, hsecretsL,
      _hvariant, _hidxLe, henv, hσ0, hgh, hbl, hcreated, hsub, haccounts⟩
  let L1 : Store :=
    (scratch_revealRefundAddedStoreOf L evm a.idx a.refund value secret deposit false)
      |>.insert "ok" (.bool false)
  have hiL1 : L1.get? "i" = some (.int (Int.ofNat a.idx.toNat)) := by
    change ((scratch_revealRefundAddedStoreOf L evm a.idx a.refund value secret deposit false)
      |>.insert "ok" (.bool false)).get? "i" = some (.int (Int.ofNat a.idx.toNat))
    rw [store_get_ne]
    · exact scratch_revealRefundAddedStoreOf_i_get L evm a.idx a.refund value secret deposit
        false hiL
    · decide
  have hlenL1 : L1.get? "length" = some (.int (Int.ofNat loopLen.toNat)) := by
    change ((scratch_revealRefundAddedStoreOf L evm a.idx a.refund value secret deposit false)
      |>.insert "ok" (.bool false)).get? "length" =
        some (.int (Int.ofNat loopLen.toNat))
    rw [store_get_ne]
    · exact scratch_revealRefundAddedStoreOf_length_get L evm a.idx a.refund loopLen value
        secret deposit false hlenL
    · decide
  have hrefundL1 :
      L1.get? "refund" = some (.int (Int.ofNat ((deposit + a.refund).toNat))) := by
    change ((scratch_revealRefundAddedStoreOf L evm a.idx a.refund value secret deposit false)
      |>.insert "ok" (.bool false)).get? "refund" =
        some (.int (Int.ofNat ((deposit + a.refund).toNat)))
    rw [store_get_ne]
    · have hadd : (deposit + a.refund).toNat = deposit.toNat + a.refund.toNat := by
        rw [uadd_toNat]
        exact Nat.mod_eq_of_lt (by omega)
      have hcomm : a.refund + deposit = deposit + a.refund := u256_add_comm _ _
      simpa [hcomm, hadd, Nat.add_comm] using
        scratch_revealRefundAddedStoreOf_refund_get L evm a.idx a.refund value secret deposit
          false
    · decide
  have hbidsL1 : L1.get? "bids" = none := by
    change ((scratch_revealRefundAddedStoreOf L evm a.idx a.refund value secret deposit false)
      |>.insert "ok" (.bool false)).get? "bids" = none
    rw [store_get_ne]
    · exact scratch_revealRefundAddedStoreOf_bids_get L evm a.idx a.refund value secret
        deposit false hbidsL
    · decide
  have hvaluesL1 : L1.get? "values" = some (.array values) := by
    change ((scratch_revealRefundAddedStoreOf L evm a.idx a.refund value secret deposit false)
      |>.insert "ok" (.bool false)).get? "values" = some (.array values)
    rw [store_get_ne]
    · exact scratch_revealRefundAddedStoreOf_values_get L evm a.idx a.refund value secret
        deposit false values hvaluesL
    · decide
  have hfakesL1 : L1.get? "fakes" = some (.array fakes) := by
    change ((scratch_revealRefundAddedStoreOf L evm a.idx a.refund value secret deposit false)
      |>.insert "ok" (.bool false)).get? "fakes" = some (.array fakes)
    rw [store_get_ne]
    · exact scratch_revealRefundAddedStoreOf_fakes_get L evm a.idx a.refund value secret
        deposit false fakes hfakesL
    · decide
  have hsecretsL1 : L1.get? "secrets" = some (.array secrets) := by
    change ((scratch_revealRefundAddedStoreOf L evm a.idx a.refund value secret deposit false)
      |>.insert "ok" (.bool false)).get? "secrets" = some (.array secrets)
    rw [store_get_ne]
    · exact scratch_revealRefundAddedStoreOf_secrets_get L evm a.idx a.refund value secret
        deposit false secrets hsecretsL
    · decide
  have haccountsNext :
      accountMapEquiv (sstoreAccountMap I.codeOwner a.acc.2 slot ⟨0⟩)
        (scratch_revealZeroBlindedState evm a.idx).accountMap := by
    unfold scratch_revealZeroBlindedState
    rw [storageStore_accountMap]
    simpa [scratch_revealBidBlindedSlot, hslot, henv, EVM.Word.ofNat] using
      accountMapEquiv_sstoreAccountMap I.codeOwner slot (⟨0⟩ : UInt256) haccounts
  exact
    scratch_revealLoopAdvance_of_get
      (I := I) (g := g) (s0 := s0) (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
      (v := v) (k := k) (C := C) (loopLen := loopLen) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (newRefund := deposit + a.refund)
      (newFree := newFree) (memNext := memNext) (awNext := awNext)
      (values := values) (fakes := fakes) (secrets := secrets) (a := a) (L := L)
      (L1 := L1) (evm := evm) (evm1 := scratch_revealZeroBlindedState evm a.idx)
      (accNext := (a.acc.1, sstoreAccountMap I.codeOwner a.acc.2 slot ⟨0⟩))
      hInvOrig (by simpa [L1] using hbodyOk) rdNext hiL1 hlenL1 hrefundL1 hbidsL1
      hvaluesL1 hfakesL1 hsecretsL1
      (by simpa [scratch_revealZeroBlindedState, storageStore_executionEnv, henv] using henv)
      (by
        unfold scratch_revealZeroBlindedState Solm.EVM.storageStore State.lookupAccount
        cases h : evm.accountMap.find? evm.executionEnv.codeOwner <;>
          simp [Option.option, State.setAccount, Account.updateStorage, h, hσ0])
      (by
        unfold scratch_revealZeroBlindedState Solm.EVM.storageStore State.lookupAccount
        cases h : evm.accountMap.find? evm.executionEnv.codeOwner <;>
          simp [Option.option, State.setAccount, Account.updateStorage, h, hgh])
      (by
        unfold scratch_revealZeroBlindedState Solm.EVM.storageStore State.lookupAccount
        cases h : evm.accountMap.find? evm.executionEnv.codeOwner <;>
          simp [Option.option, State.setAccount, Account.updateStorage, h, hbl])
      (by simpa [scratch_revealZeroBlindedState, storageStore_createdAccounts] using hcreated)
      (by
        unfold scratch_revealZeroBlindedState Solm.EVM.storageStore State.lookupAccount
        cases h : evm.accountMap.find? evm.executionEnv.codeOwner <;>
          simp [Option.option, State.setAccount, Account.updateStorage, h, hsub])
      haccountsNext hawNext hawNextSmall hfpNext hreadNext hmemNext96 hmemNextLe
      hgapNext hnextFpNat

theorem scratch_revealLoopAdvance_refundPlaced_of_get {I} {g : Sat256}
    {s0 : State} {σ₀ : AccountMap} {gh : BlockHeader} {bl : ProcessedBlocks}
    {A : Substate} {v k C : ℕ}
    {loopLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd
      sel value secret deposit newFree : UInt256}
    {memNext : ByteArray} {awNext : UInt256}
    {values fakes secrets : List Value} {a : RevealLoopCursor} {L : Store}
    {evm evm1 : EVM.State} {accNext : Batteries.RBSet AccountAddress compare × AccountMap}
    (hInv : RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A (v + 1) a L evm)
    (hbodyOk :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.ok
          { contract := blindAuctionContract,
            locals := scratch_revealRefundPlacedStoreOf L evm a.idx a.refund value secret deposit }
          evm1))
    (rdNext : RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (a.idx + ⟨1⟩)
        (UInt256.sub (deposit + a.refund) value) loopLen revealEnd biddingEnd
        secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      memNext awNext ByteArray.empty accNext k C)
    (hfit : a.refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (henv1 : evm1.executionEnv = I)
    (hσ01 : evm1.σ₀ = σ₀)
    (hgh1 : evm1.genesisBlockHeader = gh)
    (hbl1 : evm1.blocks = bl)
    (hcreated1 : evm1.createdAccounts = accNext.1)
    (hsub1 : evm1.substate = A)
    (haccounts1 : accountMapEquiv accNext.2 evm1.accountMap)
    (hawNext : 3 ≤ awNext.toNat)
    (hawNextSmall : awNext.toNat * 32 < UInt256.size)
    (hfpNext :
      (if (⟨64⟩ : UInt256).toNat ≥ memNext.size ∨ (⟨64⟩ : UInt256) ≥ awNext * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (memNext.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        newFree)
    (hreadNext : memNext.readWithPadding 64 32 = UInt256.toByteArray newFree)
    (hmemNext96 : 96 ≤ memNext.size)
    (hmemNextLe : memNext.size ≤ newFree.toNat + 32)
    (hgapNext : newFree.toNat + 32 - memNext.size < USize.size)
    (hnextFpNat : newFree.toNat = a.fp.toNat + 97) :
    ∃ a' L1 evm1' L2 evm2 k' C',
      (ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
          scratch_revealLoopBodyStmts
          (.ok { contract := blindAuctionContract, locals := L1 } evm1') ∨
        ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
          scratch_revealLoopBodyStmts
          (.continue { contract := blindAuctionContract, locals := L1 } evm1')) ∧
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm1'
        scratch_revealLoopPostStmts
        (.ok { contract := blindAuctionContract, locals := L2 } evm2) ∧
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A v a' L2 evm2 ∧
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack a'.idx a'.refund loopLen revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        a'.mem a'.aw ByteArray.empty a'.acc k' C' := by
  have hInvOrig := hInv
  rcases hInv with
    ⟨hiL, hlenL, _hrefundL, hbidsL, hvaluesL, hfakesL, hsecretsL,
      _hvariant, _hidxLe, _henv, _hσ0, _hgh, _hbl, _hcreated, _hsub, _haccounts⟩
  let L1 : Store := scratch_revealRefundPlacedStoreOf L evm a.idx a.refund value secret deposit
  have hiL1 : L1.get? "i" = some (.int (Int.ofNat a.idx.toNat)) := by
    simpa [L1] using scratch_revealRefundPlacedStoreOf_i_get L evm a.idx a.refund value secret
      deposit hiL
  have hlenL1 : L1.get? "length" = some (.int (Int.ofNat loopLen.toNat)) := by
    simpa [L1] using
      scratch_revealRefundPlacedStoreOf_length_get L evm a.idx a.refund loopLen value secret
        deposit hlenL
  have hrefundL1 :
      L1.get? "refund" =
        some (.int (Int.ofNat ((UInt256.sub (deposit + a.refund) value).toNat))) := by
    have hadd : (deposit + a.refund).toNat = deposit.toNat + a.refund.toNat := by
      rw [uadd_toNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hsubLe : value.toNat ≤ (deposit + a.refund).toNat := by
      rw [hadd]
      omega
    have hsub :
        (UInt256.sub (deposit + a.refund) value).toNat =
          deposit.toNat + a.refund.toNat - value.toNat := by
      rw [usub_toNat hsubLe, hadd]
    have hplaced :
        L1.get? "refund" =
          some (.int (Int.ofNat (a.refund.toNat + deposit.toNat - value.toNat))) := by
      simp [L1, scratch_revealRefundPlacedStoreOf]
    simpa [hsub, Nat.add_comm] using hplaced
  have hbidsL1 : L1.get? "bids" = none := by
    simpa [L1] using scratch_revealRefundPlacedStoreOf_bids_get L evm a.idx a.refund value
      secret deposit hbidsL
  have hvaluesL1 : L1.get? "values" = some (.array values) := by
    simpa [L1] using scratch_revealRefundPlacedStoreOf_values_get L evm a.idx a.refund value
      secret deposit values hvaluesL
  have hfakesL1 : L1.get? "fakes" = some (.array fakes) := by
    simpa [L1] using scratch_revealRefundPlacedStoreOf_fakes_get L evm a.idx a.refund value
      secret deposit fakes hfakesL
  have hsecretsL1 : L1.get? "secrets" = some (.array secrets) := by
    simpa [L1] using scratch_revealRefundPlacedStoreOf_secrets_get L evm a.idx a.refund value
      secret deposit secrets hsecretsL
  exact
    scratch_revealLoopAdvance_of_get
      (I := I) (g := g) (s0 := s0) (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
      (v := v) (k := k) (C := C) (loopLen := loopLen) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel)
      (newRefund := UInt256.sub (deposit + a.refund) value) (newFree := newFree)
      (memNext := memNext) (awNext := awNext) (values := values) (fakes := fakes)
      (secrets := secrets) (a := a) (L := L) (L1 := L1) (evm := evm) (evm1 := evm1)
      (accNext := accNext) hInvOrig (by simpa [L1] using hbodyOk) rdNext hiL1 hlenL1
      hrefundL1 hbidsL1 hvaluesL1 hfakesL1 hsecretsL1 henv1 hσ01 hgh1 hbl1 hcreated1
      hsub1 haccounts1 hawNext hawNextSmall hfpNext hreadNext hmemNext96 hmemNextLe
      hgapNext hnextFpNat

theorem scratch_revealLoopAdvance_refundPlaced_zeroBlinded_placeBidZero {I} {g : Sat256}
    {s0 : State} {σ₀ : AccountMap} {gh : BlockHeader} {bl : ProcessedBlocks}
    {A : Substate} {v k C : ℕ}
    {loopLen slot revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value secret deposit newFree : UInt256}
    {memNext : ByteArray} {awNext : UInt256}
    {values fakes secrets : List Value} {a : RevealLoopCursor} {L : Store}
    {evm : EVM.State}
    (hInv : RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A (v + 1) a L evm)
    (hbodyOk :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.ok
          { contract := blindAuctionContract,
            locals := scratch_revealRefundPlacedStoreOf L evm a.idx a.refund value secret deposit }
          (scratch_revealZeroBlindedState
            (scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value)
              evm.executionEnv.source) a.idx)))
    (rdNext : RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (a.idx + ⟨1⟩)
        (UInt256.sub (deposit + a.refund) value) loopLen revealEnd biddingEnd
        secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      memNext awNext ByteArray.empty
      (a.acc.1, sstoreAccountMap I.codeOwner
        (scratch_placeBidStoreBidderMap (scratch_placeBidStoreHighMap a.acc.2 I value) I
          (UInt256.ofNat I.source.val)) slot ⟨0⟩) k C)
    (hslot : slot = bidsElemSlot (.address I.source) (.int (Int.ofNat a.idx.toNat)))
    (hfit : a.refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hawNext : 3 ≤ awNext.toNat)
    (hawNextSmall : awNext.toNat * 32 < UInt256.size)
    (hfpNext :
      (if (⟨64⟩ : UInt256).toNat ≥ memNext.size ∨ (⟨64⟩ : UInt256) ≥ awNext * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (memNext.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        newFree)
    (hreadNext : memNext.readWithPadding 64 32 = UInt256.toByteArray newFree)
    (hmemNext96 : 96 ≤ memNext.size)
    (hmemNextLe : memNext.size ≤ newFree.toNat + 32)
    (hgapNext : newFree.toNat + 32 - memNext.size < USize.size)
    (hnextFpNat : newFree.toNat = a.fp.toNat + 97) :
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
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A v a' L2 evm2 ∧
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack a'.idx a'.refund loopLen revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        a'.mem a'.aw ByteArray.empty a'.acc k' C' := by
  rcases hInv with
    ⟨_hiL, _hlenL, _hrefundL, _hbidsL, _hvaluesL, _hfakesL, _hsecretsL,
      _hvariant, _hidxLe, henv, hσ0, hgh, hbl, hcreated, hsub, haccounts⟩
  let evmPB : EVM.State :=
    scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value) evm.executionEnv.source
  have hhighAccounts :
      accountMapEquiv (scratch_placeBidStoreHighMap a.acc.2 I value)
        (scratch_placeBidAfterHigh evm value).accountMap := by
    unfold scratch_placeBidStoreHighMap scratch_placeBidAfterHigh
    rw [storageStore_accountMap]
    simpa [henv] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ value haccounts
  have hwordEq :
      scratch_placeBidHighestBidderWord (scratch_placeBidStoreHighMap a.acc.2 I value) I =
        Solm.EVM.storageLoad (scratch_placeBidAfterHigh evm value)
          (scratch_placeBidAfterHigh evm value).executionEnv.codeOwner ⟨5⟩ := by
    have hword :=
      accountMapEquiv_storage_findD hhighAccounts I.codeOwner ⟨5⟩ (⟨0⟩ : UInt256)
    unfold scratch_placeBidHighestBidderWord
    rw [hword]
    simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      scratch_placeBidAfterHigh, storageStore_executionEnv, henv]
  have hpbAccounts :
      accountMapEquiv
        (scratch_placeBidStoreBidderMap (scratch_placeBidStoreHighMap a.acc.2 I value) I
          (UInt256.ofNat I.source.val))
        evmPB.accountMap := by
    unfold evmPB scratch_placeBidStoreBidderMap scratch_placeBidAfterBidder
    rw [storageStore_accountMap]
    rw [← hwordEq]
    simpa [scratch_placeBidAfterHigh, storageStore_executionEnv, henv] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨5⟩
        (SimpleAuction.simpleAuctionSetAddressWord
          (scratch_placeBidHighestBidderWord (scratch_placeBidStoreHighMap a.acc.2 I value) I)
          (UInt256.ofNat I.source.val)) hhighAccounts
  have haccountsNext :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (scratch_placeBidStoreBidderMap (scratch_placeBidStoreHighMap a.acc.2 I value) I
            (UInt256.ofNat I.source.val)) slot ⟨0⟩)
        (scratch_revealZeroBlindedState evmPB a.idx).accountMap := by
    unfold scratch_revealZeroBlindedState
    rw [storageStore_accountMap]
    simpa [evmPB, scratch_revealBidBlindedSlot, hslot, scratch_placeBidAfterBidder,
      scratch_placeBidAfterHigh, storageStore_executionEnv, henv, EVM.Word.ofNat] using
      accountMapEquiv_sstoreAccountMap I.codeOwner slot (⟨0⟩ : UInt256) hpbAccounts
  exact
    scratch_revealLoopAdvance_refundPlaced_of_get
      (I := I) (g := g) (s0 := s0) (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
      (v := v) (k := k) (C := C) (loopLen := loopLen) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (value := value) (secret := secret)
      (deposit := deposit) (newFree := newFree) (memNext := memNext) (awNext := awNext)
      (values := values) (fakes := fakes) (secrets := secrets) (a := a) (L := L)
      (evm := evm) (evm1 := scratch_revealZeroBlindedState evmPB a.idx)
      (accNext :=
        (a.acc.1, sstoreAccountMap I.codeOwner
          (scratch_placeBidStoreBidderMap (scratch_placeBidStoreHighMap a.acc.2 I value) I
            (UInt256.ofNat I.source.val)) slot ⟨0⟩))
      (by
        refine
          ⟨_hiL, _hlenL, _hrefundL, _hbidsL, _hvaluesL, _hfakesL, _hsecretsL,
            _hvariant, _hidxLe, henv, hσ0, hgh, hbl, hcreated, hsub, haccounts⟩)
      (by simpa [evmPB] using hbodyOk) rdNext hfit hdepositGe
      (by
        simpa [evmPB, scratch_revealZeroBlindedState, scratch_placeBidAfterBidder,
          scratch_placeBidAfterHigh, storageStore_executionEnv, henv] using henv)
      (by
        simpa [evmPB, scratch_revealZeroBlindedState, scratch_placeBidAfterBidder,
          scratch_placeBidAfterHigh, scratch_storageStore_σ0] using hσ0)
      (by
        simpa [evmPB, scratch_revealZeroBlindedState, scratch_placeBidAfterBidder,
          scratch_placeBidAfterHigh, scratch_storageStore_genesisBlockHeader] using hgh)
      (by
        simpa [evmPB, scratch_revealZeroBlindedState, scratch_placeBidAfterBidder,
          scratch_placeBidAfterHigh, scratch_storageStore_blocks] using hbl)
      (by
        simpa [evmPB, scratch_revealZeroBlindedState, scratch_placeBidAfterBidder,
          scratch_placeBidAfterHigh, storageStore_createdAccounts] using hcreated)
      (by
        simpa [evmPB, scratch_revealZeroBlindedState, scratch_placeBidAfterBidder,
          scratch_placeBidAfterHigh, scratch_storageStore_substate] using hsub)
      haccountsNext hawNext hawNextSmall hfpNext hreadNext hmemNext96 hmemNextLe
      hgapNext hnextFpNat

theorem scratch_revealLoopAdvance_refundPlaced_zeroBlinded_placeBidNonzero {I} {g : Sat256}
    {s0 : State} {σ₀ : AccountMap} {gh : BlockHeader} {bl : ProcessedBlocks}
    {A : Substate} {v k C : ℕ}
    {loopLen slot revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value secret deposit high old pending newFree : UInt256}
    {oldAddr : AccountAddress} {memNext : ByteArray} {awNext : UInt256}
    {values fakes secrets : List Value} {a : RevealLoopCursor} {L : Store}
    {evm : EVM.State}
    (hInv : RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A (v + 1) a L evm)
    (hbodyOk :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.ok
          { contract := blindAuctionContract,
            locals := scratch_revealRefundPlacedStoreOf L evm a.idx a.refund value secret deposit }
          (scratch_revealZeroBlindedState
            (scratch_placeBidAfterBidder
              (scratch_placeBidAfterHigh
                (scratch_placeBidAfterPending evm oldAddr
                  (UInt256.ofNat (pending.toNat + high.toNat))) value)
              evm.executionEnv.source) a.idx)))
    (rdNext : RD blindAuctionBytecode I g s0 ⟨1014⟩
      (scratch_revealEvmLoopStack (a.idx + ⟨1⟩)
        (UInt256.sub (deposit + a.refund) value) loopLen revealEnd biddingEnd
        secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
      memNext awNext ByteArray.empty
      (a.acc.1, sstoreAccountMap I.codeOwner
        (scratch_placeBidStoreBidderMap
          (scratch_placeBidStoreHighMap
            (scratch_placeBidStorePendingMap a.acc.2 I
              (scratch_placeBidHighestBidWord a.acc.2 I +
                scratch_placeBidPendingWord a.acc.2 I)) I value)
          I (UInt256.ofNat I.source.val)) slot ⟨0⟩) k C)
    (hslot : slot = bidsElemSlot (.address I.source) (.int (Int.ofNat a.idx.toNat)))
    (hhighWord : scratch_placeBidHighestBidWord a.acc.2 I = high)
    (holdWord : scratch_placeBidHighestBidderWord a.acc.2 I = old)
    (hpendingWord : scratch_placeBidPendingWord a.acc.2 I = pending)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hfit : a.refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hsum : pending.toNat + high.toNat < UInt256.size)
    (hawNext : 3 ≤ awNext.toNat)
    (hawNextSmall : awNext.toNat * 32 < UInt256.size)
    (hfpNext :
      (if (⟨64⟩ : UInt256).toNat ≥ memNext.size ∨ (⟨64⟩ : UInt256) ≥ awNext * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (memNext.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        newFree)
    (hreadNext : memNext.readWithPadding 64 32 = UInt256.toByteArray newFree)
    (hmemNext96 : 96 ≤ memNext.size)
    (hmemNextLe : memNext.size ≤ newFree.toNat + 32)
    (hgapNext : newFree.toNat + 32 - memNext.size < USize.size)
    (hnextFpNat : newFree.toNat = a.fp.toNat + 97) :
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
      RevealLoopInv loopLen values fakes secrets I σ₀ gh bl A v a' L2 evm2 ∧
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack a'.idx a'.refund loopLen revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        a'.mem a'.aw ByteArray.empty a'.acc k' C' := by
  rcases hInv with
    ⟨_hiL, _hlenL, _hrefundL, _hbidsL, _hvaluesL, _hfakesL, _hsecretsL,
      _hvariant, _hidxLe, henv, hσ0, hgh, hbl, hcreated, hsub, haccounts⟩
  let evmPending : EVM.State :=
    scratch_placeBidAfterPending evm oldAddr (UInt256.ofNat (pending.toNat + high.toNat))
  let evmPB : EVM.State :=
    scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evmPending value)
      evm.executionEnv.source
  have hpendingSlot :
      scratch_placeBidPendingSlot a.acc.2 I = pendingReturnsSlot (.address oldAddr) := by
    unfold scratch_placeBidPendingSlot
    simp [holdWord, holdAddr]
  have hsumWord :
      scratch_placeBidHighestBidWord a.acc.2 I + scratch_placeBidPendingWord a.acc.2 I =
        UInt256.ofNat (pending.toNat + high.toNat) := by
    apply u256_inj
    rw [uadd_toNat, hhighWord, hpendingWord,
      Nat.add_comm high.toNat pending.toNat,
      Nat.mod_eq_of_lt hsum, ulit_toNat' (pending.toNat + high.toNat) hsum]
  have hpendingAccounts :
      accountMapEquiv
        (scratch_placeBidStorePendingMap a.acc.2 I
          (scratch_placeBidHighestBidWord a.acc.2 I + scratch_placeBidPendingWord a.acc.2 I))
        evmPending.accountMap := by
    unfold evmPending scratch_placeBidStorePendingMap scratch_placeBidAfterPending
    rw [storageStore_accountMap]
    simpa [hpendingSlot, hsumWord, henv] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (scratch_placeBidPendingSlot a.acc.2 I)
        (scratch_placeBidHighestBidWord a.acc.2 I + scratch_placeBidPendingWord a.acc.2 I)
        haccounts
  have hhighAccounts :
      accountMapEquiv
        (scratch_placeBidStoreHighMap
          (scratch_placeBidStorePendingMap a.acc.2 I
            (scratch_placeBidHighestBidWord a.acc.2 I + scratch_placeBidPendingWord a.acc.2 I))
          I value)
        (scratch_placeBidAfterHigh evmPending value).accountMap := by
    have henvPending : evmPending.executionEnv = I := by
      simp [evmPending, scratch_placeBidAfterPending, storageStore_executionEnv, henv]
    unfold scratch_placeBidStoreHighMap scratch_placeBidAfterHigh
    rw [storageStore_accountMap]
    simpa [henvPending] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ value hpendingAccounts
  have hwordEq :
      scratch_placeBidHighestBidderWord
          (scratch_placeBidStoreHighMap
            (scratch_placeBidStorePendingMap a.acc.2 I
              (scratch_placeBidHighestBidWord a.acc.2 I + scratch_placeBidPendingWord a.acc.2 I))
            I value) I =
        Solm.EVM.storageLoad (scratch_placeBidAfterHigh evmPending value)
          (scratch_placeBidAfterHigh evmPending value).executionEnv.codeOwner ⟨5⟩ := by
    have hword :=
      accountMapEquiv_storage_findD hhighAccounts I.codeOwner ⟨5⟩ (⟨0⟩ : UInt256)
    unfold scratch_placeBidHighestBidderWord
    rw [hword]
    simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      scratch_placeBidAfterHigh, storageStore_executionEnv, evmPending,
      scratch_placeBidAfterPending, henv]
  have hpbAccounts :
      accountMapEquiv
        (scratch_placeBidStoreBidderMap
          (scratch_placeBidStoreHighMap
            (scratch_placeBidStorePendingMap a.acc.2 I
              (scratch_placeBidHighestBidWord a.acc.2 I + scratch_placeBidPendingWord a.acc.2 I))
            I value) I (UInt256.ofNat I.source.val))
        evmPB.accountMap := by
    unfold evmPB scratch_placeBidStoreBidderMap scratch_placeBidAfterBidder
    rw [storageStore_accountMap]
    rw [← hwordEq]
    simpa [scratch_placeBidAfterHigh, storageStore_executionEnv, evmPending,
      scratch_placeBidAfterPending, henv] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨5⟩
        (SimpleAuction.simpleAuctionSetAddressWord
          (scratch_placeBidHighestBidderWord
            (scratch_placeBidStoreHighMap
              (scratch_placeBidStorePendingMap a.acc.2 I
                (scratch_placeBidHighestBidWord a.acc.2 I +
                  scratch_placeBidPendingWord a.acc.2 I)) I value) I)
          (UInt256.ofNat I.source.val)) hhighAccounts
  have haccountsNext :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (scratch_placeBidStoreBidderMap
            (scratch_placeBidStoreHighMap
              (scratch_placeBidStorePendingMap a.acc.2 I
                (scratch_placeBidHighestBidWord a.acc.2 I +
                  scratch_placeBidPendingWord a.acc.2 I)) I value)
            I (UInt256.ofNat I.source.val)) slot ⟨0⟩)
        (scratch_revealZeroBlindedState evmPB a.idx).accountMap := by
    unfold scratch_revealZeroBlindedState
    rw [storageStore_accountMap]
    simpa [evmPB, evmPending, scratch_revealBidBlindedSlot, hslot,
      scratch_placeBidAfterBidder, scratch_placeBidAfterHigh, scratch_placeBidAfterPending,
      storageStore_executionEnv, henv, EVM.Word.ofNat] using
      accountMapEquiv_sstoreAccountMap I.codeOwner slot (⟨0⟩ : UInt256) hpbAccounts
  exact
    scratch_revealLoopAdvance_refundPlaced_of_get
      (I := I) (g := g) (s0 := s0) (σ₀ := σ₀) (gh := gh) (bl := bl) (A := A)
      (v := v) (k := k) (C := C) (loopLen := loopLen) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (value := value) (secret := secret)
      (deposit := deposit) (newFree := newFree) (memNext := memNext) (awNext := awNext)
      (values := values) (fakes := fakes) (secrets := secrets) (a := a) (L := L)
      (evm := evm) (evm1 := scratch_revealZeroBlindedState evmPB a.idx)
      (accNext :=
        (a.acc.1, sstoreAccountMap I.codeOwner
          (scratch_placeBidStoreBidderMap
            (scratch_placeBidStoreHighMap
              (scratch_placeBidStorePendingMap a.acc.2 I
                (scratch_placeBidHighestBidWord a.acc.2 I +
                  scratch_placeBidPendingWord a.acc.2 I)) I value)
            I (UInt256.ofNat I.source.val)) slot ⟨0⟩))
      (by
        refine
          ⟨_hiL, _hlenL, _hrefundL, _hbidsL, _hvaluesL, _hfakesL, _hsecretsL,
            _hvariant, _hidxLe, henv, hσ0, hgh, hbl, hcreated, hsub, haccounts⟩)
      (by simpa [evmPB, evmPending] using hbodyOk) rdNext hfit hdepositGe
      (by
        simpa [evmPB, evmPending, scratch_revealZeroBlindedState,
          scratch_placeBidAfterBidder, scratch_placeBidAfterHigh, scratch_placeBidAfterPending,
          storageStore_executionEnv, henv] using henv)
      (by
        simpa [evmPB, evmPending, scratch_revealZeroBlindedState,
          scratch_placeBidAfterBidder, scratch_placeBidAfterHigh, scratch_placeBidAfterPending,
          scratch_storageStore_σ0] using hσ0)
      (by
        simpa [evmPB, evmPending, scratch_revealZeroBlindedState,
          scratch_placeBidAfterBidder, scratch_placeBidAfterHigh, scratch_placeBidAfterPending,
          scratch_storageStore_genesisBlockHeader] using hgh)
      (by
        simpa [evmPB, evmPending, scratch_revealZeroBlindedState,
          scratch_placeBidAfterBidder, scratch_placeBidAfterHigh, scratch_placeBidAfterPending,
          scratch_storageStore_blocks] using hbl)
      (by
        simpa [evmPB, evmPending, scratch_revealZeroBlindedState,
          scratch_placeBidAfterBidder, scratch_placeBidAfterHigh, scratch_placeBidAfterPending,
          storageStore_createdAccounts] using hcreated)
      (by
        simpa [evmPB, evmPending, scratch_revealZeroBlindedState,
          scratch_placeBidAfterBidder, scratch_placeBidAfterHigh, scratch_placeBidAfterPending,
          scratch_storageStore_substate] using hsub)
      haccountsNext hawNext hawNextSmall hfpNext hreadNext hmemNext96 hmemNextLe
      hgapNext hnextFpNat

theorem scratch_revealLoopBody_hashMatch_placeBidFalse_fromPacked_pair {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {values fakes secrets : List Value}
    {slot i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd
      valuesLen valuesEnd sel value secret fakeWord blinded deposit high fp : UInt256}
    {fakeRaw : Value}
    (rd : RD blindAuctionBytecode I g s0 ⟨1207⟩
      [((⟨65⟩ : UInt256) + ((⟨32⟩ : UInt256) + fp)), secret, fakeWord, value, slot,
        i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hlenPacked :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
      (if fp.toNat ≥ mem5.size ∨ fp ≥ aw3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem5.readWithPadding fp.toNat 32))) =
        packedLen)
    (hhashPacked :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (mem5.readWithPadding base.toNat packedLen.toNat))) =
        uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray)))
    (hstore :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩) = blinded)
    (hflag :
      UInt256.eq blinded
          (uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray))) =
        ⟨1⟩)
    (hdepositEvm :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hperm : I.perm = true)
    (hbids : L.get? "bids" = none)
    (hvalues : L.get? "values" = some (.array values))
    (hfakes : L.get? "fakes" = some (.array fakes))
    (hsecrets : L.get? "secrets" = some (.array secrets))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : L.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hboundBids : i.toNat < curLen.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hfakeWord : fakeWord = (⟨0⟩ : UInt256))
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hplaceFalse : value.toNat ≤ high.toNat)
    (hplaceFalseEvm : value.toNat ≤ (scratch_placeBidHighestBidWord σ I).toNat) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.ok
          { contract := blindAuctionContract,
            locals :=
              (scratch_revealRefundAddedStoreOf L evm i refund value secret deposit false)
                |>.insert "ok" (.bool false) }
          (scratch_revealZeroBlindedState evm i)) ∧
      ∃ k' C',
        let base := (⟨32⟩ : UInt256) + fp
        let newFree := (⟨65⟩ : UInt256) + base
        let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
        let mem4 := scratch_revealPackedLenMem mem fp packedLen
        let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
        let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
        let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
        let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
        let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
        let aw5 := UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)
        RD blindAuctionBytecode I g s0 ⟨1014⟩
          (scratch_revealEvmLoopStack (i + ⟨1⟩) (deposit + refund) len revealEnd biddingEnd
            secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
          mem5 aw5 rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k' C' := by
  let base := (⟨32⟩ : UInt256) + fp
  let newFree := (⟨65⟩ : UInt256) + base
  let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
  let mem4 := scratch_revealPackedLenMem mem fp packedLen
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
  let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
  let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
  let aw5 := UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)
  have heq :
      EVM.Word.toBytesBE blinded =
        (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray)).toList := by
    exact scratch_revealPackedHash_eq_of_u256_eq_one
      (blinded := blinded) (value := value) (secret := secret) (fake := false) hflag
  have hhashEval :=
    scratch_evalExpr_revealPackedHash_of_secretStoreOf evm L i value secret false
  have hsrc :=
    scratch_revealLoopBody_ok_placeBid_false_of_get evm L values fakes secrets curLen refund i
      value secret blinded deposit high fakeRaw
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray)).toList
      hbids hvalues hfakes hsecrets hi hrefund hlen hboundBids hboundValues hboundFakes
      hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup hblinded hdeposit hhigh
      hhashEval heq hfit hdepositGe hplaceFalse
  obtain ⟨k1, C1, rd1235⟩ :=
    scratch_blindAuctionRevealX_loopBody_packed_suffix
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem) (aw := aw) (rdata := rdata) (cA := cA) (σ := σ)
      (secret := secret) (fakeWord := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (fp := fp)
      (hash :=
        uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray)))
      (blinded := blinded) (flag := ⟨1⟩)
      rd hfp hlenPacked hhashPacked hstore hflag
  obtain ⟨k2, C2, rd1247⟩ :=
    scratch_blindAuctionRevealX_hashGuard_match_to1247
      (I := I) (g := g) (s0 := s0) (k := k1) (C := C1)
      (rdata := rdata) (acc := (cA, σ))
      (secret := secret) (fake := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) rd1235
  obtain ⟨k3, C3, rd1265⟩ :=
    scratch_blindAuctionRevealX_refundAdd_toPlaceCond
      (I := I) (g := g) (s0 := s0) (k := k2) (C := C2)
      (rdata := rdata) (cA := cA) (σ := σ)
      (secret := secret) (fake := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (deposit := deposit) rd1247 hdepositEvm hfit
  obtain ⟨k4, C4, rdNext⟩ :=
    scratch_blindAuctionRevealX_placeCond_placeBid_false_toNext
      (I := I) (g := g) (s0 := s0) (k := k3) (C := C3)
      (rdata := rdata) (cA := cA) (σ := σ)
      (secret := secret) (value := value) (slot := slot) (i := i)
      (refund := deposit + refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (deposit := deposit)
      (by simpa [hfakeWord] using rd1265) hdepositEvm hdepositGe hplaceFalseEvm hperm
  exact ⟨hsrc, ⟨k4, C4, by
    simpa [base, newFree, packedLen, mem4, mem5, aw1, aw2, aw3, aw4, aw5] using rdNext⟩⟩

theorem scratch_revealLoopBody_hashMatch_placeBidTrueZero_fromPacked_pair {I}
    {g : Sat256} {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {values fakes secrets : List Value}
    {slot i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd
      valuesLen valuesEnd sel value secret fakeWord blinded deposit high old fp : UInt256}
    {fakeRaw : Value}
    (rd : RD blindAuctionBytecode I g s0 ⟨1207⟩
      [((⟨65⟩ : UInt256) + ((⟨32⟩ : UInt256) + fp)), secret, fakeWord, value, slot,
        i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hlenPacked :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
      (if fp.toNat ≥ mem5.size ∨ fp ≥ aw3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem5.readWithPadding fp.toNat 32))) =
        packedLen)
    (hhashPacked :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (mem5.readWithPadding base.toNat packedLen.toNat))) =
        uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray)))
    (hstore :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩) = blinded)
    (hflag :
      UInt256.eq blinded
          (uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray))) =
        ⟨1⟩)
    (hdepositEvm :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hperm : I.perm = true)
    (hbids : L.get? "bids" = none)
    (hvalues : L.get? "values" = some (.array values))
    (hfakes : L.get? "fakes" = some (.array fakes))
    (hsecrets : L.get? "secrets" = some (.array secrets))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : L.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hboundBids : i.toNat < curLen.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (hfakeWord : fakeWord = (⟨0⟩ : UInt256))
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hlt : high.toNat < value.toNat)
    (hzero : UInt256.land old solcAddrMask = ⟨0⟩)
    (hplaceTrueEvm : (scratch_placeBidHighestBidWord σ I).toNat < value.toNat)
    (hhighestBidderZeroEvm :
      UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask = ⟨0⟩) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.ok
          { contract := blindAuctionContract,
            locals := scratch_revealRefundPlacedStoreOf L evm i refund value secret deposit }
          (scratch_revealZeroBlindedState
            (scratch_placeBidAfterBidder (scratch_placeBidAfterHigh evm value)
              evm.executionEnv.source) i)) ∧
      ∃ k' C',
        let base := (⟨32⟩ : UInt256) + fp
        let newFree := (⟨65⟩ : UInt256) + base
        let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
        let mem4 := scratch_revealPackedLenMem mem fp packedLen
        let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
        let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
        let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
        let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
        let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
        let aw5 := UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)
        RD blindAuctionBytecode I g s0 ⟨1014⟩
          (scratch_revealEvmLoopStack (i + ⟨1⟩)
            (UInt256.sub (deposit + refund) value) len revealEnd biddingEnd
            secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
          mem5 aw5 rdata
          (cA, sstoreAccountMap I.codeOwner
            (scratch_placeBidStoreBidderMap (scratch_placeBidStoreHighMap σ I value) I
              (UInt256.ofNat I.source.val)) slot ⟨0⟩) k' C' := by
  let base := (⟨32⟩ : UInt256) + fp
  let newFree := (⟨65⟩ : UInt256) + base
  let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
  let mem4 := scratch_revealPackedLenMem mem fp packedLen
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
  let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
  let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
  let aw5 := UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)
  have heq :
      EVM.Word.toBytesBE blinded =
        (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray)).toList := by
    exact scratch_revealPackedHash_eq_of_u256_eq_one
      (blinded := blinded) (value := value) (secret := secret) (fake := false) hflag
  have hhashEval :=
    scratch_evalExpr_revealPackedHash_of_secretStoreOf evm L i value secret false
  have hsrc :=
    scratch_revealLoopBody_ok_placeBid_true_zero_of_get evm L values fakes secrets curLen refund i
      value secret blinded deposit high old fakeRaw
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray)).toList
      hbids hvalues hfakes hsecrets hi hrefund hlen hboundBids hboundValues hboundFakes
      hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup hblinded hdeposit hhigh
      hold hhashEval heq hfit hdepositGe hlt hzero
  obtain ⟨k1, C1, rd1235⟩ :=
    scratch_blindAuctionRevealX_loopBody_packed_suffix
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem) (aw := aw) (rdata := rdata) (cA := cA) (σ := σ)
      (secret := secret) (fakeWord := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (fp := fp)
      (hash :=
        uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray)))
      (blinded := blinded) (flag := ⟨1⟩)
      rd hfp hlenPacked hhashPacked hstore hflag
  obtain ⟨k2, C2, rd1247⟩ :=
    scratch_blindAuctionRevealX_hashGuard_match_to1247
      (I := I) (g := g) (s0 := s0) (k := k1) (C := C1)
      (rdata := rdata) (acc := (cA, σ))
      (secret := secret) (fake := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) rd1235
  obtain ⟨k3, C3, rd1265⟩ :=
    scratch_blindAuctionRevealX_refundAdd_toPlaceCond
      (I := I) (g := g) (s0 := s0) (k := k2) (C := C2)
      (rdata := rdata) (cA := cA) (σ := σ)
      (secret := secret) (fake := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (deposit := deposit) rd1247 hdepositEvm hfit
  have hrefundAdded :
      value.toNat ≤ (deposit + refund).toNat := by
    have hadd : (deposit + refund).toNat = deposit.toNat + refund.toNat := by
      rw [uadd_toNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hadd]
    omega
  obtain ⟨k4, C4, rdNext⟩ :=
    scratch_blindAuctionRevealX_placeCond_placeBid_true_zero_toNext
      (I := I) (g := g) (s0 := s0) (k := k3) (C := C3)
      (rdata := rdata) (cA := cA) (σ := σ)
      (secret := secret) (value := value) (slot := slot) (i := i)
      (refund := deposit + refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (deposit := deposit)
      (by simpa [hfakeWord] using rd1265) hdepositEvm hdepositGe hplaceTrueEvm
      hhighestBidderZeroEvm hrefundAdded hperm
  exact ⟨hsrc, ⟨k4, C4, by
    simpa [base, newFree, packedLen, mem4, mem5, aw1, aw2, aw3, aw4, aw5] using rdNext⟩⟩

theorem scratch_revealLoopBody_hashMatch_placeBidTrueNonzero_fromPacked_pair {I}
    {g : Sat256} {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {values fakes secrets : List Value}
    {slot i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd
      valuesLen valuesEnd sel value secret fakeWord blinded deposit high old pending fp : UInt256}
    {oldAddr : AccountAddress} {fakeRaw : Value}
    (rd : RD blindAuctionBytecode I g s0 ⟨1207⟩
      [((⟨65⟩ : UInt256) + ((⟨32⟩ : UInt256) + fp)), secret, fakeWord, value, slot,
        i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hlenPacked :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
      (if fp.toNat ≥ mem5.size ∨ fp ≥ aw3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem5.readWithPadding fp.toNat 32))) =
        packedLen)
    (hhashPacked :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (mem5.readWithPadding base.toNat packedLen.toNat))) =
        uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray)))
    (hstore :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩) = blinded)
    (hflag :
      UInt256.eq blinded
          (uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray))) =
        ⟨1⟩)
    (hdepositEvm :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (slot + ⟨1⟩) ⟨0⟩) = deposit)
    (hperm : I.perm = true)
    (hbids : L.get? "bids" = none)
    (hvalues : L.get? "values" = some (.array values))
    (hfakes : L.get? "fakes" = some (.array fakes))
    (hsecrets : L.get? "secrets" = some (.array secrets))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : L.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hboundBids : i.toNat < curLen.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhigh : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = high)
    (hold : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = old)
    (holdAddr : oldAddr = AccountAddress.ofNat (UInt256.land old solcAddrMask).toNat)
    (hpending :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (pendingReturnsSlot (.address oldAddr)) = pending)
    (hfakeWord : fakeWord = (⟨0⟩ : UInt256))
    (hfit : refund.toNat + deposit.toNat < UInt256.size)
    (hdepositGe : value.toNat ≤ deposit.toNat)
    (hlt : high.toNat < value.toNat)
    (hnonzero : UInt256.land old solcAddrMask ≠ ⟨0⟩)
    (hsum : pending.toNat + high.toNat < UInt256.size)
    (hplaceTrueEvm : (scratch_placeBidHighestBidWord σ I).toNat < value.toNat)
    (hhighestBidderNonzeroEvm :
      UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask ≠ ⟨0⟩)
    (hsumEvm :
      (scratch_placeBidPendingWord σ I).toNat +
        (scratch_placeBidHighestBidWord σ I).toNat < UInt256.size) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.ok
          { contract := blindAuctionContract,
            locals := scratch_revealRefundPlacedStoreOf L evm i refund value secret deposit }
          (scratch_revealZeroBlindedState
            (scratch_placeBidAfterBidder
              (scratch_placeBidAfterHigh
                (scratch_placeBidAfterPending evm oldAddr
                  (UInt256.ofNat (pending.toNat + high.toNat))) value)
              evm.executionEnv.source) i)) ∧
      ∃ k' C',
        let base := (⟨32⟩ : UInt256) + fp
        let newFree := (⟨65⟩ : UInt256) + base
        let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
        let mem4 := scratch_revealPackedLenMem mem fp packedLen
        let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
        let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
        let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
        let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
        let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
        let aw5 := UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)
        let key := UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask
        let awPB1 := UInt256.ofNat (MachineState.M aw5.toNat (⟨0⟩ : UInt256).toNat 32)
        let awPB2 := UInt256.ofNat (MachineState.M awPB1.toNat (⟨32⟩ : UInt256).toNat 32)
        let awPB3 := UInt256.ofNat (MachineState.M awPB2.toNat (⟨0⟩ : UInt256).toNat 64)
        RD blindAuctionBytecode I g s0 ⟨1014⟩
          (scratch_revealEvmLoopStack (i + ⟨1⟩)
            (UInt256.sub (deposit + refund) value) len revealEnd biddingEnd
            secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
          (scratch_placeBidPendingHashMem mem5 key) awPB3 rdata
          (cA, sstoreAccountMap I.codeOwner
            (scratch_placeBidStoreBidderMap
              (scratch_placeBidStoreHighMap
                (scratch_placeBidStorePendingMap σ I
                  (scratch_placeBidHighestBidWord σ I + scratch_placeBidPendingWord σ I)) I value)
              I (UInt256.ofNat I.source.val)) slot ⟨0⟩) k' C' := by
  let base := (⟨32⟩ : UInt256) + fp
  let newFree := (⟨65⟩ : UInt256) + base
  let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
  let mem4 := scratch_revealPackedLenMem mem fp packedLen
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
  let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
  let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
  let aw5 := UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)
  let key := UInt256.land (scratch_placeBidHighestBidderWord σ I) solcAddrMask
  let awPB1 := UInt256.ofNat (MachineState.M aw5.toNat (⟨0⟩ : UInt256).toNat 32)
  let awPB2 := UInt256.ofNat (MachineState.M awPB1.toNat (⟨32⟩ : UInt256).toNat 32)
  let awPB3 := UInt256.ofNat (MachineState.M awPB2.toNat (⟨0⟩ : UInt256).toNat 64)
  have heq :
      EVM.Word.toBytesBE blinded =
        (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray)).toList := by
    exact scratch_revealPackedHash_eq_of_u256_eq_one
      (blinded := blinded) (value := value) (secret := secret) (fake := false) hflag
  have hhashEval :=
    scratch_evalExpr_revealPackedHash_of_secretStoreOf evm L i value secret false
  have hsrc :=
    scratch_revealLoopBody_ok_placeBid_true_nonzero_of_get evm L values fakes secrets curLen
      refund i value secret blinded deposit high old pending oldAddr fakeRaw
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray)).toList
      hbids hvalues hfakes hsecrets hi hrefund hlen hboundBids hboundValues hboundFakes
      hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup hblinded hdeposit hhigh
      hold holdAddr hpending hhashEval heq hfit hdepositGe hlt hnonzero hsum
  obtain ⟨k1, C1, rd1235⟩ :=
    scratch_blindAuctionRevealX_loopBody_packed_suffix
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem) (aw := aw) (rdata := rdata) (cA := cA) (σ := σ)
      (secret := secret) (fakeWord := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (fp := fp)
      (hash :=
        uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray)))
      (blinded := blinded) (flag := ⟨1⟩)
      rd hfp hlenPacked hhashPacked hstore hflag
  obtain ⟨k2, C2, rd1247⟩ :=
    scratch_blindAuctionRevealX_hashGuard_match_to1247
      (I := I) (g := g) (s0 := s0) (k := k1) (C := C1)
      (rdata := rdata) (acc := (cA, σ))
      (secret := secret) (fake := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) rd1235
  obtain ⟨k3, C3, rd1265⟩ :=
    scratch_blindAuctionRevealX_refundAdd_toPlaceCond
      (I := I) (g := g) (s0 := s0) (k := k2) (C := C2)
      (rdata := rdata) (cA := cA) (σ := σ)
      (secret := secret) (fake := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (deposit := deposit) rd1247 hdepositEvm hfit
  have hrefundAdded :
      value.toNat ≤ (deposit + refund).toNat := by
    have hadd : (deposit + refund).toNat = deposit.toNat + refund.toNat := by
      rw [uadd_toNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hadd]
    omega
  obtain ⟨k4, C4, rdNext⟩ :=
    scratch_blindAuctionRevealX_placeCond_placeBid_true_nonzero_toNext
      (I := I) (g := g) (s0 := s0) (k := k3) (C := C3)
      (rdata := rdata) (cA := cA) (σ := σ)
      (secret := secret) (value := value) (slot := slot) (i := i)
      (refund := deposit + refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (deposit := deposit)
      (by simpa [hfakeWord] using rd1265) hdepositEvm hdepositGe hplaceTrueEvm
      hhighestBidderNonzeroEvm hsumEvm hrefundAdded hperm
  exact ⟨hsrc, ⟨k4, C4, by
    simpa [base, newFree, packedLen, mem4, mem5, aw1, aw2, aw3, aw4, aw5,
      key, awPB1, awPB2, awPB3] using rdNext⟩⟩

end BlindAuction
