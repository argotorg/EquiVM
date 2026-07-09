import Examples.UniswapV2Pair.MintFeeRuntimeSqrt

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
/- Runtime-only shared internal `_mint` routine: load `totalSupply` and enter checked addition. -/
theorem uniswapInternalMintRuntimeTotalSupplyAddEntry
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {value recipient ret : UInt256} {R : List UInt256}
    (rd8128 : RD uniswapV2PairBytecode ee g s0 ⟨8128⟩ (value :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨8515⟩
      (value :: uniswapSlotWord ⟨0⟩ σ ee :: ⟨8147⟩ :: value :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd8131 := evm_run rd8128 with [jumpdest, push1 ⟨0⟩]
  obtain ⟨k8132, C8132, rd8132₀⟩ := rd8131.sload (by native_decide) (by evm_ov)
  have rd8132 : RD uniswapV2PairBytecode ee g s0 ⟨8132⟩
      (uniswapSlotWord ⟨0⟩ σ ee :: value :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k8132 C8132 := by
    simpa [uniswapSlotWord] using rd8132₀
  have rd8515pre := evm_run rd8132 with [
    push2 ⟨8147⟩, swap1, dup3, push4 ⟨0xffffffff⟩, push2 ⟨8515⟩, and]
  have hpc8515 : UInt256.land (⟨8515⟩ : UInt256) ⟨0xffffffff⟩ = ⟨8515⟩ := by
    decide
  rw [hpc8515] at rd8515pre
  exact ⟨_, _, rd8515pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only shared internal `_mint` routine through checked totalSupply addition. -/
theorem uniswapInternalMintRuntimeTotalSupplyAddedEntry
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {value recipient ret totalSupply : UInt256} {R : List UInt256}
    (rd8515 : RD uniswapV2PairBytecode ee g s0 ⟨8515⟩
      (value :: totalSupply :: ⟨8147⟩ :: value :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hfit : totalSupply.toNat + value.toNat < UInt256.size)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨8147⟩
      ((totalSupply + value) :: value :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  exact RD.uniswapSafeMathAddSuccess rd8515 hfit (by jump_dest)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only shared internal `_mint` routine: store the new totalSupply. -/
theorem uniswapInternalMintRuntimeTotalSupplyStoredEntry
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {newSupply value recipient ret : UInt256} {R : List UInt256}
    (rd8147 : RD uniswapV2PairBytecode ee g s0 ⟨8147⟩
      (newSupply :: value :: recipient :: ret :: R) mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨8153⟩
      (⟨0⟩ :: value :: recipient :: ret :: R) mem aw rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨0⟩ newSupply) k' C' := by
  have rd8152 := evm_run rd8147 with [jumpdest, push1 ⟨0⟩, swap1, dup2]
  obtain ⟨_, _, rd8153⟩ := rd8152.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, rd8153⟩

noncomputable abbrev uniswapInternalMintBalanceHashMem
    (recipient : UInt256) (mem : ByteArray) : ByteArray :=
  twoWordHashMem (UInt256.land recipient solcAddrMask) ⟨1⟩ mem

noncomputable abbrev uniswapInternalMintBalanceHashSlot
    (recipient : UInt256) (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((uniswapInternalMintBalanceHashMem recipient mem).readWithPadding 0 64)))

noncomputable abbrev uniswapInternalMintLogMem (value : UInt256) (mem : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray value).write 0 mem 128 32

theorem uniswapInternalMintBalanceHashMem_size_of_ge64
    (recipient : UInt256) {mem : ByteArray} (hlo : 64 ≤ mem.size) :
    (uniswapInternalMintBalanceHashMem recipient mem).size = mem.size := by
  unfold uniswapInternalMintBalanceHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  have hword0 :
      ((UInt256.toByteArray (UInt256.land recipient solcAddrMask)).write 0 mem 0 32).size =
        mem.size := by
    exact toByteArray_write32_size_of_le mem (UInt256.land recipient solcAddrMask) 0
      mem.size mem.size rfl (by omega) (by omega)
  exact toByteArray_write32_size_of_le
    ((UInt256.toByteArray (UInt256.land recipient solcAddrMask)).write 0 mem 0 32)
    ⟨1⟩ 32 mem.size mem.size hword0 (by rw [hword0]; omega) (by omega)

theorem uniswapInternalMintBalanceHashMem_read64_of_ge96
    (recipient : UInt256) {mem : ByteArray}
    (hlo : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapInternalMintBalanceHashMem recipient mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapInternalMintBalanceHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  have hword0 :
      ((UInt256.toByteArray (UInt256.land recipient solcAddrMask)).write 0 mem 0 32).size =
        mem.size := by
    exact toByteArray_write32_size_of_le mem (UInt256.land recipient solcAddrMask) 0
      mem.size mem.size rfl (by omega) (by omega)
  have hword0In :
      64 + 32 ≤
        ((UInt256.toByteArray (UInt256.land recipient solcAddrMask)).write 0 mem 0 32).size := by
    rw [hword0]
    omega
  have hmemIn : 64 + 32 ≤ mem.size := by
    omega
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [hword0]; omega) (by omega) hword0In]
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by omega) (by omega) hmemIn]
  exact hread64

theorem uniswapInternalMintBalanceHashMem_read0_64_of_ge64
    (recipient : UInt256) {mem : ByteArray} (hlo : 64 ≤ mem.size) :
    (uniswapInternalMintBalanceHashMem recipient mem).readWithPadding 0 64 =
      UInt256.toByteArray (UInt256.land recipient solcAddrMask) ++ UInt256.toByteArray ⟨1⟩ := by
  have hsize := uniswapInternalMintBalanceHashMem_size_of_ge64 recipient (mem := mem) hlo
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
    (by rw [hsize]; omega)]
  have hleft :
      (uniswapInternalMintBalanceHashMem recipient mem).extract 0 32 =
        UInt256.toByteArray (UInt256.land recipient solcAddrMask) := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [hsize]; omega)]
    unfold uniswapInternalMintBalanceHashMem twoWordHashMem wordAt32Mem
    have hword0 :
        ((UInt256.toByteArray (UInt256.land recipient solcAddrMask)).write 0 mem 0 32).size =
          mem.size := by
      exact toByteArray_write32_size_of_le mem (UInt256.land recipient solcAddrMask) 0
        mem.size mem.size rfl (by omega) (by omega)
    have hword0In : 32 ≤ (wordAt0Mem (UInt256.land recipient solcAddrMask) mem).size := by
      simpa [wordAt0Mem, hword0] using (show 32 ≤ mem.size by omega)
    rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size]) hword0In (by omega)]
    unfold wordAt0Mem
    rw [write32_read_back _ _ 0 (by rw [toByteArray_size]) (by omega)]
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (UInt256.land recipient solcAddrMask)).size ≤ 32
      rw [toByteArray_size])
  have hright :
      (uniswapInternalMintBalanceHashMem recipient mem).extract 32 64 =
        UInt256.toByteArray ⟨1⟩ := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [hsize]; omega)]
    unfold uniswapInternalMintBalanceHashMem twoWordHashMem wordAt32Mem
    have hword0 :
        ((UInt256.toByteArray (UInt256.land recipient solcAddrMask)).write 0 mem 0 32).size =
          mem.size := by
      exact toByteArray_write32_size_of_le mem (UInt256.land recipient solcAddrMask) 0
        mem.size mem.size rfl (by omega) (by omega)
    have hword0In : 32 ≤ (wordAt0Mem (UInt256.land recipient solcAddrMask) mem).size := by
      simpa [wordAt0Mem, hword0] using (show 32 ≤ mem.size by omega)
    rw [write32_read_back _ _ 32 (by rw [toByteArray_size]) hword0In]
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  rw [show (uniswapInternalMintBalanceHashMem recipient mem).extract 0 64 =
      (uniswapInternalMintBalanceHashMem recipient mem).extract 0 32 ++
        (uniswapInternalMintBalanceHashMem recipient mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem uniswapInternalMintBalanceHashSlot_eq_mapSlot
    (recipient : UInt256) {mem : ByteArray} (hlo : 64 ≤ mem.size) :
    uniswapInternalMintBalanceHashSlot recipient mem =
      mapSlot (UInt256.land recipient solcAddrMask) ⟨1⟩ := by
  unfold uniswapInternalMintBalanceHashSlot mapSlot uInt256OfByteArray
  rw [uniswapInternalMintBalanceHashMem_read0_64_of_ge64 recipient hlo]
  exact mappingSlot_single (UInt256.land recipient solcAddrMask) ⟨1⟩

theorem accountMapEquiv_mintFunctionPostState_of_runtimeMintRecipient
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv} {mem : ByteArray}
    {liquidity recipientWord : UInt256} {recipient : AccountAddress}
    (hPost : accountMapEquiv σ evm.accountMap)
    (henv : evm.executionEnv = I)
    (hrecipient : recipient = AccountAddress.ofNat recipientWord.toNat)
    (hmem : 64 ≤ mem.size)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evm recipient liquidity < UInt256.size) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
        (uniswapInternalMintBalanceHashSlot recipientWord
          (uniswapInternalMintBalanceHashMem recipientWord mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
          (uniswapInternalMintBalanceHashSlot recipientWord mem) + liquidity))
      (mintFunctionPostState evm recipient liquidity).accountMap := by
  have htotalEq : mintFunctionTotalSupplyWord evm = uniswapSlotWord ⟨0⟩ σ I :=
    mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv hPost henv
  have hnewSupply :
      mintFunctionTotalSupplyNewWord evm liquidity =
        uniswapSlotWord ⟨0⟩ σ I + liquidity := by
    simpa [mintFunctionTotalSupplyNewWord, mintFunctionTotalSupplyNewNat, htotalEq]
      using u256_ofNat_toNat_add_eq_add_of_lt (uniswapSlotWord ⟨0⟩ σ I) liquidity
        (by simpa [mintFunctionTotalSupplyNewNat, htotalEq] using hfitSupply)
  have hafterTotal :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
        (mintFunctionAfterTotalSupplyState evm liquidity).accountMap := by
    have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
      (uniswapSlotWord ⟨0⟩ σ I + liquidity) hPost
    simpa [mintFunctionAfterTotalSupplyState, henv, storageStore_accountMap, hnewSupply]
      using hstore
  have henvAfter : (mintFunctionAfterTotalSupplyState evm liquidity).executionEnv = I := by
    simp [mintFunctionAfterTotalSupplyState, henv, storageStore_executionEnv]
  have hslotSource :
      mintFunctionToSlot recipient = mapSlot (UInt256.land recipientWord solcAddrMask) ⟨1⟩ := by
    subst recipient
    unfold mintFunctionToSlot balanceOfSlot mintFunctionToKey
    rw [keyValueToWord_address_ofNat_mask]
    rw [u256_land_comm solcAddrMask recipientWord]
  have hslotRuntime :
      uniswapInternalMintBalanceHashSlot recipientWord mem =
        mapSlot (UInt256.land recipientWord solcAddrMask) ⟨1⟩ := by
    exact uniswapInternalMintBalanceHashSlot_eq_mapSlot recipientWord hmem
  have hmemHashSize :
      64 ≤ (uniswapInternalMintBalanceHashMem recipientWord mem).size := by
    rw [uniswapInternalMintBalanceHashMem_size_of_ge64 recipientWord hmem]
    exact hmem
  have hslotRuntimeStore :
      uniswapInternalMintBalanceHashSlot recipientWord
          (uniswapInternalMintBalanceHashMem recipientWord mem) =
        mapSlot (UInt256.land recipientWord solcAddrMask) ⟨1⟩ := by
    exact uniswapInternalMintBalanceHashSlot_eq_mapSlot recipientWord hmemHashSize
  have hbalanceEq :
      mintFunctionToBalanceWord evm recipient liquidity =
        uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
          (uniswapInternalMintBalanceHashSlot recipientWord mem) := by
    have hword := accountMapEquiv_storage_findD hafterTotal I.codeOwner
      (mapSlot (UInt256.land recipientWord solcAddrMask) ⟨1⟩) ⟨0⟩
    simpa [mintFunctionToBalanceWord, uniswapCodeOwnerStorageWord, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, henv, henvAfter, hslotSource, hslotRuntime]
      using hword.symm
  have hnewBalance :
      mintFunctionToBalanceNewWord evm recipient liquidity =
        uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
            (uniswapInternalMintBalanceHashSlot recipientWord mem) + liquidity := by
    simpa [mintFunctionToBalanceNewWord, mintFunctionToBalanceNewNat, hbalanceEq]
      using u256_ofNat_toNat_add_eq_add_of_lt
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
          (uniswapInternalMintBalanceHashSlot recipientWord mem)) liquidity
        (by simpa [mintFunctionToBalanceNewNat, hbalanceEq] using hfitBalance)
  have hstoreBalance := accountMapEquiv_sstoreAccountMap I.codeOwner
    (mapSlot (UInt256.land recipientWord solcAddrMask) ⟨1⟩)
    (uniswapCodeOwnerStorageWord I
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
      (uniswapInternalMintBalanceHashSlot recipientWord mem) + liquidity)
    hafterTotal
  simpa [mintFunctionPostState, storageStore_accountMap, henv, henvAfter, hslotSource,
    hslotRuntimeStore, hnewBalance] using hstoreBalance

theorem accountMapEquiv_mintFunctionPostState_of_runtimeMint
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv} {mem : ByteArray}
    {liquidity : UInt256}
    (hPost : accountMapEquiv σ evm.accountMap)
    (henv : evm.executionEnv = I)
    (hmem : 64 ≤ mem.size)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat evm (AccountAddress.ofNat (mintToWord I).toNat)
        liquidity < UInt256.size) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
        (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
          (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem) + liquidity))
      (mintFunctionPostState evm (AccountAddress.ofNat (mintToWord I).toNat)
        liquidity).accountMap := by
  let recipient := AccountAddress.ofNat (mintToWord I).toNat
  have htotalEq : mintFunctionTotalSupplyWord evm = uniswapSlotWord ⟨0⟩ σ I :=
    mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv hPost henv
  have hnewSupply :
      mintFunctionTotalSupplyNewWord evm liquidity =
        uniswapSlotWord ⟨0⟩ σ I + liquidity := by
    simpa [mintFunctionTotalSupplyNewWord, mintFunctionTotalSupplyNewNat, htotalEq]
      using u256_ofNat_toNat_add_eq_add_of_lt (uniswapSlotWord ⟨0⟩ σ I) liquidity
        (by simpa [mintFunctionTotalSupplyNewNat, htotalEq] using hfitSupply)
  have hafterTotal :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
        (mintFunctionAfterTotalSupplyState evm liquidity).accountMap := by
    have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
      (uniswapSlotWord ⟨0⟩ σ I + liquidity) hPost
    simpa [mintFunctionAfterTotalSupplyState, henv, storageStore_accountMap, hnewSupply]
      using hstore
  have henvAfter : (mintFunctionAfterTotalSupplyState evm liquidity).executionEnv = I := by
    simp [mintFunctionAfterTotalSupplyState, henv, storageStore_executionEnv]
  have hslotSource :
      mintFunctionToSlot recipient = mapSlot (mintToMaskedWord I) ⟨1⟩ := by
    subst recipient
    unfold mintFunctionToSlot balanceOfSlot mintFunctionToKey
    change mapSlot (keyValueToWord (mintToKey I)) ⟨1⟩ = mapSlot (mintToMaskedWord I) ⟨1⟩
    rw [mintToKey_word_masked]
  have hslotRuntime :
      uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem =
        mapSlot (mintToMaskedWord I) ⟨1⟩ := by
    rw [uniswapInternalMintBalanceHashSlot_eq_mapSlot _ hmem]
    unfold mintToMaskedWord
    rw [u256_land_comm (UInt256.land solcAddrMask (mintToWord I)) solcAddrMask]
    rw [u256_land_solcAddrMask_idem_left]
  have hmemHashSize :
      64 ≤ (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) mem).size := by
    rw [uniswapInternalMintBalanceHashMem_size_of_ge64 (mintToMaskedWord I) hmem]
    exact hmem
  have hslotRuntimeStore :
      uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
          (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) mem) =
        mapSlot (mintToMaskedWord I) ⟨1⟩ := by
    rw [uniswapInternalMintBalanceHashSlot_eq_mapSlot _ hmemHashSize]
    unfold mintToMaskedWord
    rw [u256_land_comm (UInt256.land solcAddrMask (mintToWord I)) solcAddrMask]
    rw [u256_land_solcAddrMask_idem_left]
  have hbalanceEq :
      mintFunctionToBalanceWord evm recipient liquidity =
        uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem) := by
    have hword := accountMapEquiv_storage_findD hafterTotal I.codeOwner
      (mapSlot (mintToMaskedWord I) ⟨1⟩) ⟨0⟩
    simpa [mintFunctionToBalanceWord, uniswapCodeOwnerStorageWord, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, henv, henvAfter, hslotSource, hslotRuntime]
      using hword.symm
  have hnewBalance :
      mintFunctionToBalanceNewWord evm recipient liquidity =
        uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem) + liquidity := by
    simpa [mintFunctionToBalanceNewWord, mintFunctionToBalanceNewNat, hbalanceEq]
      using u256_ofNat_toNat_add_eq_add_of_lt
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem)) liquidity
        (by simpa [mintFunctionToBalanceNewNat, recipient, hbalanceEq] using hfitBalance)
  have hstoreBalance := accountMapEquiv_sstoreAccountMap I.codeOwner
    (mapSlot (mintToMaskedWord I) ⟨1⟩)
    (uniswapCodeOwnerStorageWord I
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
      (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem) + liquidity)
    hafterTotal
  simpa [mintFunctionPostState, storageStore_accountMap, henv, henvAfter, recipient,
    hslotSource, hslotRuntimeStore, hnewBalance] using hstoreBalance

theorem uniswapInternalMintDoubleBalanceHashMem_size_of_ge64
    (recipient : UInt256) {mem : ByteArray} (hlo : 64 ≤ mem.size) :
    (uniswapInternalMintBalanceHashMem recipient
      (uniswapInternalMintBalanceHashMem recipient mem)).size = mem.size := by
  have hinner := uniswapInternalMintBalanceHashMem_size_of_ge64 recipient (mem := mem) hlo
  have houter := uniswapInternalMintBalanceHashMem_size_of_ge64 recipient
    (mem := uniswapInternalMintBalanceHashMem recipient mem) (by rw [hinner]; exact hlo)
  rw [houter, hinner]

theorem uniswapInternalMintDoubleBalanceHashMem_read64_of_ge96
    (recipient : UInt256) {mem : ByteArray}
    (hlo : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapInternalMintBalanceHashMem recipient
      (uniswapInternalMintBalanceHashMem recipient mem)).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hsize :=
    uniswapInternalMintBalanceHashMem_size_of_ge64 recipient (mem := mem) (by omega)
  exact uniswapInternalMintBalanceHashMem_read64_of_ge96 recipient
    (by rw [hsize]; exact hlo)
    (uniswapInternalMintBalanceHashMem_read64_of_ge96 recipient hlo hread64)

theorem uniswapInternalMintLogMem_size_of_ge160
    (value : UInt256) {mem : ByteArray} (hlo : 160 ≤ mem.size) :
    (uniswapInternalMintLogMem value mem).size = mem.size := by
  unfold uniswapInternalMintLogMem
  exact toByteArray_write32_size_of_le mem value 128 mem.size mem.size rfl
    (by omega) (by omega)

theorem uniswapInternalMintLogMem_read64_of_ge160
    (value : UInt256) {mem : ByteArray}
    (hlo : 160 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapInternalMintLogMem value mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapInternalMintLogMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size]) (by omega) (by omega)]
  exact hread64

theorem uniswapInternalMintSuccessMem_size_of_ge160
    (recipient value : UInt256) {mem : ByteArray} (hlo : 160 ≤ mem.size) :
    (uniswapInternalMintLogMem value
      (uniswapInternalMintBalanceHashMem recipient
        (uniswapInternalMintBalanceHashMem recipient mem))).size = mem.size := by
  have hhash :=
    uniswapInternalMintDoubleBalanceHashMem_size_of_ge64 recipient (mem := mem) (by omega)
  rw [uniswapInternalMintLogMem_size_of_ge160 value (by rw [hhash]; exact hlo), hhash]

theorem uniswapInternalMintSuccessMem_read64_of_ge160
    (recipient value : UInt256) {mem : ByteArray}
    (hlo : 160 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (uniswapInternalMintLogMem value
      (uniswapInternalMintBalanceHashMem recipient
        (uniswapInternalMintBalanceHashMem recipient mem))).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hhash :=
    uniswapInternalMintDoubleBalanceHashMem_size_of_ge64 recipient (mem := mem) (by omega)
  exact uniswapInternalMintLogMem_read64_of_ge160 value
    (by rw [hhash]; exact hlo)
    (uniswapInternalMintDoubleBalanceHashMem_read64_of_ge96 recipient (by omega) hread64)

theorem uniswapInternalMintDoubleBalanceHashMem_mload64_of_ge160
    (recipient : UInt256) {mem : ByteArray}
    (hlo : 160 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (uniswapInternalMintBalanceHashMem recipient
            (uniswapInternalMintBalanceHashMem recipient mem)).size
        ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapInternalMintBalanceHashMem recipient
          (uniswapInternalMintBalanceHashMem recipient mem)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [uniswapInternalMintDoubleBalanceHashMem_size_of_ge64 recipient (by omega)];
        omega)
    (by native_decide)
    (uniswapInternalMintDoubleBalanceHashMem_read64_of_ge96 recipient (by omega) hread64)

theorem uniswapInternalMintSuccessMem_mload64_of_ge160
    (recipient value : UInt256) {mem : ByteArray}
    (hlo : 160 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (uniswapInternalMintLogMem value
            (uniswapInternalMintBalanceHashMem recipient
              (uniswapInternalMintBalanceHashMem recipient mem))).size
        ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapInternalMintLogMem value
          (uniswapInternalMintBalanceHashMem recipient
            (uniswapInternalMintBalanceHashMem recipient mem))).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [uniswapInternalMintSuccessMem_size_of_ge160 recipient value hlo]; omega)
    (by native_decide)
    (uniswapInternalMintSuccessMem_read64_of_ge160 recipient value hlo hread64)

set_option maxHeartbeats 1000000 in
/- Runtime-only shared internal `_mint` routine: load `balanceOf[recipient]` and enter checked
addition. -/
theorem uniswapInternalMintRuntimeRecipientBalanceAddEntry
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {value recipient ret : UInt256} {R : List UInt256}
    (rd8153 : RD uniswapV2PairBytecode ee g s0 ⟨8153⟩
      (⟨0⟩ :: value :: recipient :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨8515⟩
      (value :: uniswapCodeOwnerStorageWord ee σ
          (uniswapInternalMintBalanceHashSlot recipient mem) ::
        ⟨8190⟩ :: value :: recipient :: ret :: R)
      (uniswapInternalMintBalanceHashMem recipient mem) feeToStaticcallActiveWords rdata
      (cA, σ) k' C' := by
  let key := UInt256.land recipient solcAddrMask
  have rd8163pre := evm_run rd8153 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd8163pre
  have rd8164 := evm_run rd8163pre with [dup2]
  have rd8165 := rd8164.mstore 0 (wordAt0Mem key mem) feeToStaticcallActiveWords
    (by native_decide) mem_cost (by unfold key wordAt0Mem; rfl) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8170pre := evm_run rd8165 with [push1 ⟨1⟩, push1 ⟨32⟩]
  have rd8170 := rd8170pre.mstore 0 (uniswapInternalMintBalanceHashMem recipient mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost
    (by unfold uniswapInternalMintBalanceHashMem twoWordHashMem wordAt32Mem key; rfl)
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd8174 := evm_run rd8170 with [push1 ⟨64⟩, swap1]
  have rd8175 := rd8174.keccak256 0 (uniswapInternalMintBalanceHashSlot recipient mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost
    (by unfold uniswapInternalMintBalanceHashSlot; rfl) (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨k8175, C8175, rd8175₀⟩ := rd8175.sload (by native_decide) (by evm_ov)
  have rd8175' : RD uniswapV2PairBytecode ee g s0 ⟨8175⟩
      (uniswapCodeOwnerStorageWord ee σ (uniswapInternalMintBalanceHashSlot recipient mem) ::
        value :: recipient :: ret :: R)
      (uniswapInternalMintBalanceHashMem recipient mem) feeToStaticcallActiveWords rdata
      (cA, σ) k8175 C8175 := by
    simpa [uniswapCodeOwnerStorageWord, codeOwnerStorageWord] using rd8175₀
  have rd8515pre := evm_run rd8175' with [
    push2 ⟨8190⟩, swap1, dup3, push4 ⟨0xffffffff⟩, push2 ⟨8515⟩, and]
  have hpc8515 : UInt256.land (⟨8515⟩ : UInt256) ⟨0xffffffff⟩ = ⟨8515⟩ := by
    decide
  rw [hpc8515] at rd8515pre
  exact ⟨_, _, rd8515pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only shared internal `_mint` routine through checked recipient balance addition. -/
theorem uniswapInternalMintRuntimeRecipientBalanceAddedEntry
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {value recipient ret balance : UInt256} {R : List UInt256}
    (rd8515 : RD uniswapV2PairBytecode ee g s0 ⟨8515⟩
      (value :: balance :: ⟨8190⟩ :: value :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hfit : balance.toNat + value.toNat < UInt256.size)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨8190⟩
      ((balance + value) :: value :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  exact RD.uniswapSafeMathAddSuccess rd8515 hfit (by jump_dest)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
/- Runtime-only shared internal `_mint` routine: store the updated recipient balance. -/
theorem uniswapInternalMintRuntimeRecipientBalanceStoredEntry
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {newBalance value recipient ret : UInt256} {R : List UInt256}
    (rd8190 : RD uniswapV2PairBytecode ee g s0 ⟨8190⟩
      (newBalance :: value :: recipient :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨8222⟩
      (⟨32⟩ :: ⟨0⟩ :: UInt256.land recipient solcAddrMask :: ⟨64⟩ ::
        value :: recipient :: ret :: R)
      (uniswapInternalMintBalanceHashMem recipient mem) feeToStaticcallActiveWords rdata
      (cA, sstoreAccountMap ee.codeOwner σ
        (uniswapInternalMintBalanceHashSlot recipient mem) newBalance) k' C' := by
  let key := UInt256.land recipient solcAddrMask
  have rd8205pre := evm_run rd8190 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push1 ⟨0⟩, dup2, dup2]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd8205pre
  have rd8206 := rd8205pre.mstore 0 (wordAt0Mem key mem) feeToStaticcallActiveWords
    (by native_decide) mem_cost (by unfold key wordAt0Mem; rfl) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8212pre := evm_run rd8206 with [push1 ⟨1⟩, push1 ⟨32⟩, swap1, dup2]
  have rd8213 := rd8212pre.mstore 0 (uniswapInternalMintBalanceHashMem recipient mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost
    (by unfold uniswapInternalMintBalanceHashMem twoWordHashMem wordAt32Mem key; rfl)
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd8217 := evm_run rd8213 with [push1 ⟨64⟩, dup1, dup4]
  have rd8218 := rd8217.keccak256 0 (uniswapInternalMintBalanceHashSlot recipient mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost
    (by unfold uniswapInternalMintBalanceHashSlot; rfl) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8221 := evm_run rd8218 with [swap5, swap1, swap5]
  obtain ⟨_, _, rd8222⟩ := rd8221.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [key] using rd8222⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only shared internal `_mint` routine: emit `Transfer(0, recipient, value)` and jump
back to the caller. -/
theorem uniswapInternalMintRuntimeEmitAndJump
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {key value recipient ret : UInt256} {R : List UInt256}
    (rd8222 : RD uniswapV2PairBytecode ee g s0 ⟨8222⟩
      (⟨32⟩ :: ⟨0⟩ :: key :: ⟨64⟩ :: value :: recipient :: ret :: R)
      mem feeToStaticcallActiveWords rdata acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hlogMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (uniswapInternalMintLogMem value mem).size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapInternalMintLogMem value mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hperm : ee.perm = true)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ret R
      (uniswapInternalMintLogMem value mem) feeToStaticcallActiveWords rdata acc k' C' := by
  have rd8226 := evm_run rd8222 with [
    dup4,
    raw mload 0 ⟨128⟩ feeToStaticcallActiveWords (by native_decide)
      mem_cost hmload64 (by native_decide) (by evm_ov),
    dup6, dup2]
  have rd8227 := rd8226.mstore 0 (uniswapInternalMintLogMem value mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost
    (by unfold uniswapInternalMintLogMem; rfl) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8233 := evm_run rd8227 with [
    swap4,
    raw mload 0 ⟨128⟩ feeToStaticcallActiveWords (by native_decide)
      mem_cost hlogMload64 (by native_decide) (by evm_ov),
    swap3, swap4, swap2, swap3]
  have rd8266 := rd8233.pushConst uniswapTransferTopic (width := 32) (op := .PUSH32)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd8274 := evm_run rd8266 with [
    swap3, dup2, swap1, sub, swap1, swap2, add, swap1]
  have rd8275 := rd8274.log3 0 feeToStaticcallActiveWords (by native_decide) hperm
    mem_cost (by native_decide) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd8275 with [pop, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
/- Runtime-only shared internal `_mint` routine success path. -/
theorem uniswapInternalMintRuntimeSuccess
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {value recipient ret : UInt256} {R : List UInt256}
    (rd8128 : RD uniswapV2PairBytecode ee g s0 ⟨8128⟩
      (value :: recipient :: ret :: R) mem feeToStaticcallActiveWords rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σ ee).toNat + value.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord ee
        (sstoreAccountMap ee.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ ee + value))
        (uniswapInternalMintBalanceHashSlot recipient mem)).toNat + value.toNat <
          UInt256.size)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (uniswapInternalMintBalanceHashMem recipient
              (uniswapInternalMintBalanceHashMem recipient mem)).size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapInternalMintBalanceHashMem recipient
            (uniswapInternalMintBalanceHashMem recipient mem)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hlogMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (uniswapInternalMintLogMem value
              (uniswapInternalMintBalanceHashMem recipient
                (uniswapInternalMintBalanceHashMem recipient mem))).size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapInternalMintLogMem value
            (uniswapInternalMintBalanceHashMem recipient
              (uniswapInternalMintBalanceHashMem recipient mem))).readWithPadding
                (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ret R
      (uniswapInternalMintLogMem value
        (uniswapInternalMintBalanceHashMem recipient
          (uniswapInternalMintBalanceHashMem recipient mem)))
      feeToStaticcallActiveWords rdata
      (cA, sstoreAccountMap ee.codeOwner
        (sstoreAccountMap ee.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ ee + value))
        (uniswapInternalMintBalanceHashSlot recipient
          (uniswapInternalMintBalanceHashMem recipient mem))
        (uniswapCodeOwnerStorageWord ee
          (sstoreAccountMap ee.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ ee + value))
          (uniswapInternalMintBalanceHashSlot recipient mem) + value)) k' C' := by
  obtain ⟨_, _, rd8515Total⟩ :=
    uniswapInternalMintRuntimeTotalSupplyAddEntry rd8128 (by omega)
  obtain ⟨_, _, rd8147⟩ :=
    uniswapInternalMintRuntimeTotalSupplyAddedEntry rd8515Total htotalFit (by omega)
  obtain ⟨_, _, rd8153⟩ :=
    uniswapInternalMintRuntimeTotalSupplyStoredEntry rd8147 hperm (by omega)
  obtain ⟨_, _, rd8515Balance⟩ :=
    uniswapInternalMintRuntimeRecipientBalanceAddEntry rd8153 (by omega)
  obtain ⟨_, _, rd8190⟩ :=
    uniswapInternalMintRuntimeRecipientBalanceAddedEntry rd8515Balance hbalanceFit (by omega)
  obtain ⟨_, _, rd8222⟩ :=
    uniswapInternalMintRuntimeRecipientBalanceStoredEntry rd8190 hperm (by omega)
  exact uniswapInternalMintRuntimeEmitAndJump rd8222 hmload64 hlogMload64 hperm hret hov

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` positive-root branch where computed liquidity is nonzero and the
internal `_mint` call succeeds. -/
theorem uniswapMintFeeRuntimePositiveLiquidityMintReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {liquidity denominator numerator rootK rootKLast kLast feeTo amount0 amount1 balance0
      balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7999 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7999⟩
      [liquidity, denominator, numerator, rootKLast, rootK, kLast, feeTo, ⟨1⟩, reserve1,
        reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1,
        reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot feeTo mem)).toNat + liquidity.toNat <
          UInt256.size)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (uniswapInternalMintBalanceHashMem feeTo
              (uniswapInternalMintBalanceHashMem feeTo mem)).size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapInternalMintBalanceHashMem feeTo
            (uniswapInternalMintBalanceHashMem feeTo mem)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hlogMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (uniswapInternalMintLogMem liquidity
              (uniswapInternalMintBalanceHashMem feeTo
                (uniswapInternalMintBalanceHashMem feeTo mem))).size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapInternalMintLogMem liquidity
            (uniswapInternalMintBalanceHashMem feeTo
              (uniswapInternalMintBalanceHashMem feeTo mem))).readWithPadding
                (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      (uniswapInternalMintLogMem liquidity
        (uniswapInternalMintBalanceHashMem feeTo
          (uniswapInternalMintBalanceHashMem feeTo mem)))
      feeToStaticcallActiveWords rdata
      (cAFee, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot feeTo
          (uniswapInternalMintBalanceHashMem feeTo mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot feeTo mem) + liquidity)) k' C' := by
  obtain ⟨_, _, rd8128⟩ :=
    uniswapMintFeeRuntimePositiveLiquidityMintEntry rd7999 hliqNonzero
  obtain ⟨_, _, rd8014⟩ :=
    uniswapInternalMintRuntimeSuccess rd8128 hperm htotalFit hbalanceFit hmload64
      hlogMload64 (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact uniswapMintFeeRuntimeAfterInternalMintReturn rd8014

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` positive-root branch where the computed liquidity is zero. -/
theorem uniswapMintFeeRuntimePositiveComputedLiquidityZeroReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {denominator numerator rootK rootKLast kLast feeTo amount0 amount1 balance0 balance1
      reserve0 reserve1 toWord sel : UInt256}
    (rd7982 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7982⟩
      [denominator, ⟨0⟩, numerator, rootKLast, rootK, kLast, feeTo, ⟨1⟩, reserve1,
        reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1,
        reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hdenominatorNe : denominator ≠ ⟨0⟩)
    (hliqZero : UInt256.div numerator denominator = ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd7999⟩ :=
    uniswapMintFeeRuntimePositiveLiquidityEntry rd7982 hdenominatorNe
  exact uniswapMintFeeRuntimePositiveLiquidityZeroNoMintReturn rd7999 hliqZero

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` positive-root branch where computed liquidity is nonzero and internal
`_mint` succeeds. -/
theorem uniswapMintFeeRuntimePositiveComputedLiquidityMintReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {denominator numerator rootK rootKLast kLast feeTo amount0 amount1 balance0 balance1
      reserve0 reserve1 toWord sel : UInt256}
    (rd7982 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7982⟩
      [denominator, ⟨0⟩, numerator, rootKLast, rootK, kLast, feeTo, ⟨1⟩, reserve1,
        reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1,
        reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hdenominatorNe : denominator ≠ ⟨0⟩)
    (hliqNonzero : UInt256.div numerator denominator ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat + (UInt256.div numerator denominator).toNat <
        UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + UInt256.div numerator denominator))
        (uniswapInternalMintBalanceHashSlot feeTo mem)).toNat +
          (UInt256.div numerator denominator).toNat < UInt256.size)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (uniswapInternalMintBalanceHashMem feeTo
              (uniswapInternalMintBalanceHashMem feeTo mem)).size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapInternalMintBalanceHashMem feeTo
            (uniswapInternalMintBalanceHashMem feeTo mem)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hlogMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (uniswapInternalMintLogMem (UInt256.div numerator denominator)
              (uniswapInternalMintBalanceHashMem feeTo
                (uniswapInternalMintBalanceHashMem feeTo mem))).size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapInternalMintLogMem (UInt256.div numerator denominator)
            (uniswapInternalMintBalanceHashMem feeTo
              (uniswapInternalMintBalanceHashMem feeTo mem))).readWithPadding
                (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      (uniswapInternalMintLogMem (UInt256.div numerator denominator)
        (uniswapInternalMintBalanceHashMem feeTo
          (uniswapInternalMintBalanceHashMem feeTo mem)))
      feeToStaticcallActiveWords rdata
      (cAFee, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + UInt256.div numerator denominator))
        (uniswapInternalMintBalanceHashSlot feeTo
          (uniswapInternalMintBalanceHashMem feeTo mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + UInt256.div numerator denominator))
          (uniswapInternalMintBalanceHashSlot feeTo mem) +
            UInt256.div numerator denominator)) k' C' := by
  obtain ⟨_, _, rd7999⟩ :=
    uniswapMintFeeRuntimePositiveLiquidityEntry rd7982 hdenominatorNe
  exact uniswapMintFeeRuntimePositiveLiquidityMintReturn rd7999 hliqNonzero hperm
    htotalFit hbalanceFit hmload64 hlogMload64

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` positive-root branch through arithmetic to the computed-liquidity
branch point. -/
theorem uniswapMintFeeRuntimeAfterRootsPositiveComputedLiquidityEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {rootK rootKLast kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord
      sel : UInt256}
    (rd7899 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
      [rootKLast, ⟨0⟩, rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩,
        sel]
      mem aw rdata (cAFee, σFee) k C)
    (hrootGt : rootKLast.toNat < rootK.toNat)
    (hnumFit :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat * (UInt256.sub rootK rootKLast).toNat <
        UInt256.size)
    (hrootK5Fit : rootK.toNat * 5 < UInt256.size)
    (hdenFit : (UInt256.mul rootK ⟨5⟩).toNat + rootKLast.toNat < UInt256.size) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7982⟩
      [UInt256.mul rootK ⟨5⟩ + rootKLast, ⟨0⟩,
        UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I) (UInt256.sub rootK rootKLast),
        rootKLast, rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩,
        sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd6879⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSubEntry rd7899 hrootGt
  obtain ⟨_, _, rd6780Num⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSupplyMulEntry rd6879 hrootGt
  obtain ⟨_, _, rd7945⟩ :=
    uniswapMintFeeRuntimePositiveNumeratorEntry rd6780Num hnumFit
  obtain ⟨_, _, rd6780Den⟩ :=
    uniswapMintFeeRuntimePositiveDenominatorMulEntry rd7945
  obtain ⟨_, _, rd7970⟩ :=
    uniswapMintFeeRuntimePositiveDenominatorProductEntry rd6780Den hrootK5Fit
  obtain ⟨_, _, rd8515⟩ :=
    uniswapMintFeeRuntimePositiveDenominatorAddEntry rd7970
  exact uniswapMintFeeRuntimePositiveDenominatorEntry rd8515 hdenFit

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` positive-root branch where arithmetic computes zero liquidity. -/
theorem uniswapMintFeeRuntimeAfterRootsPositiveComputedLiquidityZeroReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {rootK rootKLast kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord
      sel : UInt256}
    (rd7899 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
      [rootKLast, ⟨0⟩, rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩,
        sel]
      mem aw rdata (cAFee, σFee) k C)
    (hrootGt : rootKLast.toNat < rootK.toNat)
    (hnumFit :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat * (UInt256.sub rootK rootKLast).toNat <
        UInt256.size)
    (hrootK5Fit : rootK.toNat * 5 < UInt256.size)
    (hdenFit : (UInt256.mul rootK ⟨5⟩).toNat + rootKLast.toNat < UInt256.size)
    (hdenominatorNe : UInt256.mul rootK ⟨5⟩ + rootKLast ≠ ⟨0⟩)
    (hliqZero :
      UInt256.div
          (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I) (UInt256.sub rootK rootKLast))
          (UInt256.mul rootK ⟨5⟩ + rootKLast) =
        ⟨0⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  obtain ⟨_, _, rd7982⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveComputedLiquidityEntry rd7899 hrootGt hnumFit
      hrootK5Fit hdenFit
  exact uniswapMintFeeRuntimePositiveComputedLiquidityZeroReturn rd7982 hdenominatorNe hliqZero

set_option maxHeartbeats 1000000 in
/- Runtime-only `_mintFee` positive-root branch where arithmetic computes nonzero liquidity and
internal `_mint` succeeds. -/
theorem uniswapMintFeeRuntimeAfterRootsPositiveComputedLiquidityMintReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {rootK rootKLast kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord
      sel : UInt256}
    (rd7899 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
      [rootKLast, ⟨0⟩, rootK, kLast, feeTo, ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩,
        amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩,
        sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hrootGt : rootKLast.toNat < rootK.toNat)
    (hnumFit :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat * (UInt256.sub rootK rootKLast).toNat <
        UInt256.size)
    (hrootK5Fit : rootK.toNat * 5 < UInt256.size)
    (hdenFit : (UInt256.mul rootK ⟨5⟩).toNat + rootKLast.toNat < UInt256.size)
    (hdenominatorNe : UInt256.mul rootK ⟨5⟩ + rootKLast ≠ ⟨0⟩)
    (hliqNonzero :
      UInt256.div
          (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I) (UInt256.sub rootK rootKLast))
          (UInt256.mul rootK ⟨5⟩ + rootKLast) ≠
        ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat +
          (UInt256.div
            (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I) (UInt256.sub rootK rootKLast))
            (UInt256.mul rootK ⟨5⟩ + rootKLast)).toNat <
        UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I +
            UInt256.div
              (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I) (UInt256.sub rootK rootKLast))
              (UInt256.mul rootK ⟨5⟩ + rootKLast)))
        (uniswapInternalMintBalanceHashSlot feeTo mem)).toNat +
          (UInt256.div
            (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I) (UInt256.sub rootK rootKLast))
            (UInt256.mul rootK ⟨5⟩ + rootKLast)).toNat <
        UInt256.size)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (uniswapInternalMintBalanceHashMem feeTo
              (uniswapInternalMintBalanceHashMem feeTo mem)).size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapInternalMintBalanceHashMem feeTo
            (uniswapInternalMintBalanceHashMem feeTo mem)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hlogMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (uniswapInternalMintLogMem
              (UInt256.div
                (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I) (UInt256.sub rootK rootKLast))
                (UInt256.mul rootK ⟨5⟩ + rootKLast))
              (uniswapInternalMintBalanceHashMem feeTo
                (uniswapInternalMintBalanceHashMem feeTo mem))).size
          ∨ (⟨64⟩ : UInt256) ≥ feeToStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapInternalMintLogMem
            (UInt256.div
              (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I) (UInt256.sub rootK rootKLast))
              (UInt256.mul rootK ⟨5⟩ + rootKLast))
            (uniswapInternalMintBalanceHashMem feeTo
              (uniswapInternalMintBalanceHashMem feeTo mem))).readWithPadding
                (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      (uniswapInternalMintLogMem
        (UInt256.div
          (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I) (UInt256.sub rootK rootKLast))
          (UInt256.mul rootK ⟨5⟩ + rootKLast))
        (uniswapInternalMintBalanceHashMem feeTo
          (uniswapInternalMintBalanceHashMem feeTo mem)))
      feeToStaticcallActiveWords rdata
      (cAFee, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I +
            UInt256.div
              (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I) (UInt256.sub rootK rootKLast))
              (UInt256.mul rootK ⟨5⟩ + rootKLast)))
        (uniswapInternalMintBalanceHashSlot feeTo
          (uniswapInternalMintBalanceHashMem feeTo mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I +
              UInt256.div
                (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I) (UInt256.sub rootK rootKLast))
                (UInt256.mul rootK ⟨5⟩ + rootKLast)))
          (uniswapInternalMintBalanceHashSlot feeTo mem) +
            UInt256.div
              (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I) (UInt256.sub rootK rootKLast))
              (UInt256.mul rootK ⟨5⟩ + rootKLast))) k' C' := by
  obtain ⟨_, _, rd7982⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveComputedLiquidityEntry rd7899 hrootGt hnumFit
      hrootK5Fit hdenFit
  exact uniswapMintFeeRuntimePositiveComputedLiquidityMintReturn rd7982 hdenominatorNe
    hliqNonzero hperm htotalFit hbalanceFit hmload64 hlogMload64


end UniswapV2Pair
