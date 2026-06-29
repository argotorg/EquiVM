import Examples.UniswapV2Pair.SkimCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## EVM trace prefix -/

/-- The optimized external wrapper for `skim(address)` accepts canonical calldata and jumps to the
    external skim routine at pc 5080. -/
theorem uniswapSkimX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5080⟩
      [skimToWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1308⟩ := RD.uniswapOneAddressExternalLenOk
    (entry := ⟨1286⟩) (ret := ⟨570⟩) (routine := ⟨5080⟩) hreach
    uniswap_one_address_external_entry_wf (by jump_dest) hsz36 hsize
  obtain ⟨_, _, rd5080⟩ := RD.uniswapOneAddressExternalMaskAndJump
    (entry := ⟨1286⟩) (ret := ⟨570⟩) (routine := ⟨5080⟩) (R := [sel]) rd1308
    uniswap_one_address_external_entry_wf
    (by simpa [skimToWord] using hcanonTo)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [skimToWord] using rd5080⟩

/-- The optimized external wrapper for `skim(address)` masks legacy-address calldata and jumps to
the external skim routine at pc 5080. -/
theorem uniswapSkimX_decoded_masked {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5080⟩
      [skimToMaskedWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1308⟩ := RD.uniswapOneAddressExternalLenOk
    (entry := ⟨1286⟩) (ret := ⟨570⟩) (routine := ⟨5080⟩) hreach
    uniswap_one_address_external_entry_wf (by jump_dest) hsz36 hsize
  obtain ⟨_, _, rd5080⟩ := RD.uniswapOneAddressExternalMaskAndJumpMasked
    (entry := ⟨1286⟩) (ret := ⟨570⟩) (routine := ⟨5080⟩) (R := [sel])
    rd1308 uniswap_one_address_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [skimToWord, skimToMaskedWord] using rd5080⟩

/-- After the external wrapper, `skim(address)` successfully enters the Uniswap lock. -/
theorem uniswapSkimX_lockEntered {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5161⟩
      [skimToWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd5080⟩ := uniswapSkimX_decoded
    (g := g) hsz36 hsize hcanonTo hreach
  obtain ⟨_, _, rd5161⟩ := RD.uniswapLockEnterOk
    (pc := ⟨5080⟩) (okPc := ⟨5155⟩) (R := [skimToWord I, ⟨570⟩, sel])
    rd5080 uniswap_lock_enter_ok_wf hperm hunlocked (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rd5161⟩

/-- After the masked external wrapper, `skim(address)` successfully enters the Uniswap lock. -/
theorem uniswapSkimX_lockEntered_masked {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5161⟩
      [skimToMaskedWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd5080⟩ := uniswapSkimX_decoded_masked
    (g := g) hsz36 hsize hreach
  obtain ⟨_, _, rd5161⟩ := RD.uniswapLockEnterOk
    (pc := ⟨5080⟩) (okPc := ⟨5155⟩) (R := [skimToMaskedWord I, ⟨570⟩, sel])
    rd5080 uniswap_lock_enter_ok_wf hperm hunlocked (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rd5161⟩

/-- Runtime-only `skim(address)` slice from selector dispatch through successful lock entry. -/
theorem uniswapSkimRuntimeLockEntered
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩) :
    ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5161⟩
      [skimToWord I, ⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩ rfl hsel
  exact uniswapSkimX_lockEntered
    (g := Sat256.ofUInt256 g) hsz36 hsize hcanonTo hperm hunlocked
    (uniswapReachSkimBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

/-- Runtime-only masked `skim(address)` slice from selector dispatch through successful lock
entry. -/
theorem uniswapSkimRuntimeLockEntered_masked
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩) :
    ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5161⟩
      [skimToMaskedWord I, ⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩ rfl hsel
  exact uniswapSkimX_lockEntered_masked
    (g := Sat256.ofUInt256 g) hsz36 hsize hperm hunlocked
    (uniswapReachSkimBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice from successful lock entry to the first
`token0.balanceOf(address(this))` code-existence guard. -/
theorem uniswapSkimRuntimeFirstBalanceOfExtcodesize
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩) :
    ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5257⟩
      [UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
          (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5325⟩, skimToWord I,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5330⟩,
        UInt256.land
          (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          solcAddrMask,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        skimToWord I, ⟨570⟩, uniswapSelWord I]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨_, _, rd5161⟩ :=
    uniswapSkimRuntimeLockEntered
      (g := g) hcode hsize hwv hsel hsz36 hcanonTo hperm hunlocked
  have rd5163 := evm_run rd5161 with [push1 ⟨6⟩]
  obtain ⟨k5164, C5164, rd5164₀⟩ := rd5163.sload (by native_decide) (by evm_ov)
  have rd5164 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5164⟩
      [token0Word, skimToWord I, ⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σLock) k5164 C5164 := by
    simpa [σLock, token0Word, uniswapSlotWord] using rd5164₀
  have rd5166 := evm_run rd5164 with [push1 ⟨7⟩]
  obtain ⟨k5167, C5167, rd5167₀⟩ := rd5166.sload (by native_decide) (by evm_ov)
  have rd5167 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5167⟩
      [token1Word, token0Word, skimToWord I, ⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σLock) k5167 C5167 := by
    simpa [σLock, token1Word, uniswapSlotWord] using rd5167₀
  have rd5169 := evm_run rd5167 with [push1 ⟨8⟩]
  obtain ⟨k5170, C5170, rd5170₀⟩ := rd5169.sload (by native_decide) (by evm_ov)
  have rd5170 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5170⟩
      [packedWord, token1Word, token0Word, skimToWord I, ⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σLock) k5170 C5170 := by
    simpa [σLock, packedWord, uniswapSlotWord] using rd5170₀
  have rd5183 := evm_run rd5170 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 balanceOfSelectorWord, push1 ⟨224⟩, shl, dup2]
  have rd5184 := rd5183.mstore 6 balanceOfThisSelectorMem (UInt256.ofNat 5)
    (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)
  have rd5189 := evm_run rd5184 with [
    uniswapAddress, push1 ⟨4⟩, dup3, add]
  have rd5190 := rd5189.mstore 3
    (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
    (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)
  have rd5192 := evm_run rd5190 with [
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (balanceOfThisCalldataMem_mload64 (UInt256.ofNat I.codeOwner.val))
      (by decide) (by evm_ov)]
  have rd5207₀ := evm_run rd5192 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap5, dup6, and, swap5, swap1, swap4, and, swap3]
  have rd5207 := rd5207₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd5207
  have rd5220 := evm_run rd5207 with [
    push2 ⟨5330⟩, swap3, dup6, swap3, dup8, swap3, push2 ⟨5325⟩, swap3]
  have rd5229 := evm_run rd5220 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, and, swap2]
  have rd5257₀ := evm_run rd5229 with [
    dup6, swap2, push4 balanceOfSelectorWord, swap2, push1 ⟨36⟩, dup1,
    dup3, add, swap3, push1 ⟨32⟩, swap3, swap1, swap2, swap1, dup3,
    swap1, sub, add, dup2, dup7, dup1]
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide,
    show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by decide,
    show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd5257₀
  exact ⟨_, _, by
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rd5257₀⟩

set_option maxHeartbeats 1000000 in
/-- Masked-address variant of the `skim(address)` slice from successful lock entry to the first
`token0.balanceOf(address(this))` code-existence guard. -/
theorem uniswapSkimRuntimeFirstBalanceOfExtcodesize_masked
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩) :
    ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5257⟩
      [UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
          (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5325⟩, skimToMaskedWord I,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5330⟩,
        UInt256.land
          (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          solcAddrMask,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        skimToMaskedWord I, ⟨570⟩, uniswapSelWord I]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨_, _, rd5161⟩ :=
    uniswapSkimRuntimeLockEntered_masked
      (g := g) hcode hsize hwv hsel hsz36 hperm hunlocked
  have rd5163 := evm_run rd5161 with [push1 ⟨6⟩]
  obtain ⟨k5164, C5164, rd5164₀⟩ := rd5163.sload (by native_decide) (by evm_ov)
  have rd5164 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5164⟩
      [token0Word, skimToMaskedWord I, ⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σLock) k5164 C5164 := by
    simpa [σLock, token0Word, uniswapSlotWord] using rd5164₀
  have rd5166 := evm_run rd5164 with [push1 ⟨7⟩]
  obtain ⟨k5167, C5167, rd5167₀⟩ := rd5166.sload (by native_decide) (by evm_ov)
  have rd5167 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5167⟩
      [token1Word, token0Word, skimToMaskedWord I, ⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σLock) k5167 C5167 := by
    simpa [σLock, token1Word, uniswapSlotWord] using rd5167₀
  have rd5169 := evm_run rd5167 with [push1 ⟨8⟩]
  obtain ⟨k5170, C5170, rd5170₀⟩ := rd5169.sload (by native_decide) (by evm_ov)
  have rd5170 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5170⟩
      [packedWord, token1Word, token0Word, skimToMaskedWord I, ⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σLock) k5170 C5170 := by
    simpa [σLock, packedWord, uniswapSlotWord] using rd5170₀
  have rd5183 := evm_run rd5170 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 balanceOfSelectorWord, push1 ⟨224⟩, shl, dup2]
  have rd5184 := rd5183.mstore 6 balanceOfThisSelectorMem (UInt256.ofNat 5)
    (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)
  have rd5189 := evm_run rd5184 with [
    uniswapAddress, push1 ⟨4⟩, dup3, add]
  have rd5190 := rd5189.mstore 3
    (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
    (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)
  have rd5192 := evm_run rd5190 with [
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (balanceOfThisCalldataMem_mload64 (UInt256.ofNat I.codeOwner.val))
      (by decide) (by evm_ov)]
  have rd5207₀ := evm_run rd5192 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap5, dup6, and, swap5, swap1, swap4, and, swap3]
  have rd5207 := rd5207₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd5207
  have rd5220 := evm_run rd5207 with [
    push2 ⟨5330⟩, swap3, dup6, swap3, dup8, swap3, push2 ⟨5325⟩, swap3]
  have rd5229 := evm_run rd5220 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, and, swap2]
  have rd5257₀ := evm_run rd5229 with [
    dup6, swap2, push4 balanceOfSelectorWord, swap2, push1 ⟨36⟩, dup1,
    dup3, add, swap3, push1 ⟨32⟩, swap3, swap1, swap2, swap1, dup3,
    swap1, sub, add, dup2, dup7, dup1]
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide,
    show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by decide,
    show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd5257₀
  exact ⟨_, _, by
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rd5257₀⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice through the first `balanceOf` code-existence guard when
`token0` has deployed code, stopping immediately before `GAS; STATICCALL`. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallReady
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5271⟩
      [UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
          (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5325⟩, skimToWord I,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5330⟩,
        UInt256.land
          (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          solcAddrMask,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        skimToWord I, ⟨570⟩, uniswapSelWord I]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨_, _, rd5257⟩ :=
    uniswapSkimRuntimeFirstBalanceOfExtcodesize
      (g := g) hcode hsize hwv hsel hsz36 hcanonTo hperm hunlocked
  obtain ⟨_, _, rd5271⟩ :=
    RD.uniswapExtcodesizeGuardOk (okPc := ⟨5269⟩) rd5257
      (by simpa [σLock, token0Word, token0Clean] using htoken0Code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rd5271⟩

set_option maxHeartbeats 1000000 in
/-- Masked-wrapper variant of the first `balanceOf` code-existence guard, stopping immediately
before `GAS; STATICCALL`. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallReady_masked
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5271⟩
      [UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
          (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5325⟩, skimToMaskedWord I,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5330⟩,
        UInt256.land
          (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          solcAddrMask,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        skimToMaskedWord I, ⟨570⟩, uniswapSelWord I]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨_, _, rd5257⟩ :=
    uniswapSkimRuntimeFirstBalanceOfExtcodesize_masked
      (g := g) hcode hsize hwv hsel hsz36 hperm hunlocked
  obtain ⟨_, _, rd5271⟩ :=
    RD.uniswapExtcodesizeGuardOk (okPc := ⟨5269⟩) rd5257
      (by simpa [σLock, token0Word, token0Clean] using htoken0Code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rd5271⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice through `GAS`, stopping at the first
`token0.balanceOf(address(this))` `STATICCALL`. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ gasWord k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5272⟩
      [gasWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
          (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5325⟩, skimToWord I,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5330⟩,
        UInt256.land
          (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          solcAddrMask,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        skimToWord I, ⟨570⟩, uniswapSelWord I]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨_, _, rd5257⟩ :=
    uniswapSkimRuntimeFirstBalanceOfExtcodesize
      (g := g) hcode hsize hwv hsel hsz36 hcanonTo hperm hunlocked
  obtain ⟨gasWord, _, _, rd5272⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (okPc := ⟨5269⟩) rd5257
      (by simpa [σLock, token0Word, token0Clean] using htoken0Code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨gasWord, _, _, by
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rd5272⟩

set_option maxHeartbeats 1000000 in
/-- Masked-wrapper variant through `GAS`, stopping at the first
`token0.balanceOf(address(this))` `STATICCALL`. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallEntry_masked
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ gasWord k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5272⟩
      [gasWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
          (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5325⟩, skimToMaskedWord I,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨5330⟩,
        UInt256.land
          (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
          solcAddrMask,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        skimToMaskedWord I, ⟨570⟩, uniswapSelWord I]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨_, _, rd5257⟩ :=
    uniswapSkimRuntimeFirstBalanceOfExtcodesize_masked
      (g := g) hcode hsize hwv hsel hsz36 hperm hunlocked
  obtain ⟨gasWord, _, _, rd5272⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (okPc := ⟨5269⟩) rd5257
      (by simpa [σLock, token0Word, token0Clean] using htoken0Code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨gasWord, _, _, by
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rd5272⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice through the first opaque
`token0.balanceOf(address(this))` `STATICCALL`, exposing the shared `Θ` result. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallMade
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5273⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            UInt256.land
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
              (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5325⟩, skimToWord I,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5330⟩,
            UInt256.land
              (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
              solcAddrMask,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            skimToWord I, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨_, _, _, rd5272⟩ :=
    uniswapSkimRuntimeFirstBalanceOfStaticcallEntry
      (g := g) hcode hsize hwv hsel hsz36 hcanonTo hperm hunlocked htoken0Code
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd5273, hoSize⟩ :=
    RD.uniswapStaticcall rd5272 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨cA', σ', z, o, A_in, callGas, k', C',
    by simpa [σLock, token0Word, token0Clean, initState] using hΘ,
    by
      simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
        reserve0Word, balanceOfThisStaticcallMem, balanceOfThisStaticcallActiveWords] using
        rd5273,
    hoSize⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice through the first `balanceOf` post-call status guard.
When the opaque `STATICCALL` fails, the high-level call success guard reverts. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallFailureGuard
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ (z = false →
        RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
      ∧ (z = true → o.size < 32 →
        RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨cA', σ', z, o, A_in, callGas, _k, _C, hΘ, rd5273, hoSize⟩ :=
    uniswapSkimRuntimeFirstBalanceOfStaticcallMade
      (g := g) hcode hsize hwv hsel hsz36 hcanonTo hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, ?_, ?_, ?_, hoSize⟩
  · simpa [σLock, token0Word, token0Clean] using hΘ
  · intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      simp [hz]
    have rdRev :=
      RD.uniswapCallSuccessGuardMissing (okPc := ⟨5289⟩) rd5273 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) hoSize
        (by simp only [List.length_cons, List.length_nil]; omega)
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rdRev
  · intro hz hshort
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    obtain ⟨_, _, rd5291⟩ :=
      RD.uniswapCallSuccessGuardOk (okPc := ⟨5289⟩) rd5273 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    have rdRev :=
      RD.uniswapBalanceOfReturnWordDecodeShortReverts
        (pc := ⟨5291⟩) (okPc := ⟨5311⟩) (self := UInt256.ofNat I.codeOwner.val)
        rd5291 hshort hoSize
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rdRev

set_option maxHeartbeats 1000000 in
/-- Masked-wrapper variant of the first opaque `token0.balanceOf(address(this))` `STATICCALL`,
exposing the shared `Θ` result. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallMade_masked
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5273⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            UInt256.land
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
              (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5325⟩, skimToMaskedWord I,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5330⟩,
            UInt256.land
              (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
              solcAddrMask,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            skimToMaskedWord I, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨_, _, _, rd5272⟩ :=
    uniswapSkimRuntimeFirstBalanceOfStaticcallEntry_masked
      (g := g) hcode hsize hwv hsel hsz36 hperm hunlocked htoken0Code
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd5273, hoSize⟩ :=
    RD.uniswapStaticcall rd5272 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨cA', σ', z, o, A_in, callGas, k', C',
    by simpa [σLock, token0Word, token0Clean, initState] using hΘ,
    by
      simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
        reserve0Word, balanceOfThisStaticcallMem, balanceOfThisStaticcallActiveWords] using
        rd5273,
    hoSize⟩

set_option maxHeartbeats 1000000 in
/-- Masked-wrapper variant of the first `balanceOf` post-call status guard. When the opaque
`STATICCALL` fails, the high-level call success guard reverts. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallFailureGuard_masked
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ (z = false →
        RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
      ∧ (z = true → o.size < 32 →
        RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨cA', σ', z, o, A_in, callGas, _k, _C, hΘ, rd5273, hoSize⟩ :=
    uniswapSkimRuntimeFirstBalanceOfStaticcallMade_masked
      (g := g) hcode hsize hwv hsel hsz36 hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, ?_, ?_, ?_, hoSize⟩
  · simpa [σLock, token0Word, token0Clean] using hΘ
  · intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      simp [hz]
    have rdRev :=
      RD.uniswapCallSuccessGuardMissing (okPc := ⟨5289⟩) rd5273 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) hoSize
        (by simp only [List.length_cons, List.length_nil]; omega)
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rdRev
  · intro hz hshort
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    obtain ⟨_, _, rd5291⟩ :=
      RD.uniswapCallSuccessGuardOk (okPc := ⟨5289⟩) rd5273 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    have rdRev :=
      RD.uniswapBalanceOfReturnWordDecodeShortReverts
        (pc := ⟨5291⟩) (okPc := ⟨5311⟩) (self := UInt256.ofNat I.codeOwner.val)
        rd5291 hshort hoSize
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rdRev

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` first `balanceOf` slice for the call-depth limit.

At depth 1024 the `STATICCALL` is not made, pushes status `0`, and the high-level call-success
guard reverts. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallDepthReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hperm : I.perm = true)
    (hdepth : I.depth = 1024)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨_, _, _, rd5272⟩ :=
    uniswapSkimRuntimeFirstBalanceOfStaticcallEntry
      (g := g) hcode hsize hwv hsel hsz36 hcanonTo hperm hunlocked htoken0Code
  obtain ⟨_, _, rd5273⟩ :=
    RD.uniswapStaticcallDepthLimit rd5272 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rdRev :=
    RD.uniswapCallSuccessGuardMissing (okPc := ⟨5289⟩) rd5273 rfl
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
    reserve0Word, balanceOfThisStaticcallMem, balanceOfThisStaticcallActiveWords] using rdRev

set_option maxHeartbeats 1000000 in
/-- Masked-wrapper variant of the first `balanceOf` call-depth-limit revert. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallDepthReverts_masked
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hdepth : I.depth = 1024)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨_, _, _, rd5272⟩ :=
    uniswapSkimRuntimeFirstBalanceOfStaticcallEntry_masked
      (g := g) hcode hsize hwv hsel hsz36 hperm hunlocked htoken0Code
  obtain ⟨_, _, rd5273⟩ :=
    RD.uniswapStaticcallDepthLimit rd5272 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rdRev :=
    RD.uniswapCallSuccessGuardMissing (okPc := ⟨5289⟩) rd5273 rfl
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
    reserve0Word, balanceOfThisStaticcallMem, balanceOfThisStaticcallActiveWords] using rdRev

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice through the first `balanceOf` post-call status guard.
When the opaque `STATICCALL` succeeds, control reaches the success path at pc 5291. -/
theorem uniswapSkimRuntimeFirstBalanceOfStaticcallSuccessGuard
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5273⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            UInt256.land
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
              (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5325⟩, skimToWord I,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5330⟩,
            UInt256.land
              (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
              solcAddrMask,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            skimToWord I, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true →
        ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5291⟩
          [⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            UInt256.land
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
              (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5325⟩, skimToWord I,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5330⟩,
            UInt256.land
              (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
              solcAddrMask,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            skimToWord I, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5273, hoSize⟩ :=
    uniswapSkimRuntimeFirstBalanceOfStaticcallMade
      (g := g) hcode hsize hwv hsel hsz36 hcanonTo hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5273, ?_, hoSize⟩
  intro hz
  have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
    rw [hz]
    decide
  obtain ⟨k', C', rd5291⟩ :=
    RD.uniswapCallSuccessGuardOk (okPc := ⟨5289⟩) rd5273 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨k', C', by
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rd5291⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice decoding the first successful `balanceOf` return word. -/
theorem uniswapSkimRuntimeFirstBalanceOfReturnWordDecoded
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5273⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            UInt256.land
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
              (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5325⟩, skimToWord I,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5330⟩,
            UInt256.land
              (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
              solcAddrMask,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            skimToWord I, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true → 32 ≤ o.size →
        ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5314⟩
          [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
            UInt256.land
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
              (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5325⟩, skimToWord I,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨5330⟩,
            UInt256.land
              (uniswapSlotWord ⟨7⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
              solcAddrMask,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            skimToWord I, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5273, hsucc, hoSize⟩ :=
    uniswapSkimRuntimeFirstBalanceOfStaticcallSuccessGuard
      (g := g) hcode hsize hwv hsel hsz36 hcanonTo hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5273, ?_, hoSize⟩
  intro hz ho32
  obtain ⟨_, _, rd5291⟩ := hsucc hz
  obtain ⟨k', C', rd5314⟩ :=
    RD.uniswapBalanceOfReturnWordDecodeOk
      (pc := ⟨5291⟩) (okPc := ⟨5311⟩) (self := UInt256.ofNat I.codeOwner.val)
      rd5291 ho32 hoSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by jump_dest) (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨k', C', by
    simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
      reserve0Word] using rd5314⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice showing that a successful first `balanceOf` call with
short ABI returndata reverts while decoding the return word. -/
theorem uniswapSkimRuntimeFirstBalanceOfReturnWordDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ (z = true → o.size < 32 →
        RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨cA', σ', z, o, A_in, callGas, _k, _C, hΘ, _rd5273, hsucc, hoSize⟩ :=
    uniswapSkimRuntimeFirstBalanceOfStaticcallSuccessGuard
      (g := g) hcode hsize hwv hsel hsz36 hcanonTo hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, hΘ, ?_, hoSize⟩
  intro hz hshort
  obtain ⟨_, _, rd5291⟩ := hsucc hz
  have rdRev :=
    RD.uniswapBalanceOfReturnWordDecodeShortReverts
      (pc := ⟨5291⟩) (okPc := ⟨5311⟩) (self := UInt256.ofNat I.codeOwner.val)
      rd5291 hshort hoSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
    reserve0Word] using rdRev

set_option maxHeartbeats 1000000 in
/-- Masked-wrapper variant of the first `balanceOf` short-return decode revert. -/
theorem uniswapSkimRuntimeFirstBalanceOfReturnWordDecodeShortReverts_masked
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
      ∧ (z = true → o.size < 32 →
        RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨cA', σ', z, o, A_in, callGas, _k, _C, hΘ, rd5273, hoSize⟩ :=
    uniswapSkimRuntimeFirstBalanceOfStaticcallMade_masked
      (g := g) hcode hsize hwv hsel hsz36 hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, hΘ, ?_, hoSize⟩
  intro hz hshort
  have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
    rw [hz]
    decide
  obtain ⟨_, _, rd5291⟩ :=
    RD.uniswapCallSuccessGuardOk (okPc := ⟨5289⟩) rd5273 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rdRev :=
    RD.uniswapBalanceOfReturnWordDecodeShortReverts
      (pc := ⟨5291⟩) (okPc := ⟨5311⟩) (self := UInt256.ofNat I.codeOwner.val)
      rd5291 hshort hoSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
    reserve0Word] using rdRev

set_option maxHeartbeats 1000000 in
/-- Runtime-only `skim(address)` slice showing that the first `balanceOf` guard reverts before
the external call when `token0` has no deployed code. -/
theorem uniswapSkimRuntimeFirstBalanceOfMissingCodeReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0NoCode :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨_, _, rd5257⟩ :=
    uniswapSkimRuntimeFirstBalanceOfExtcodesize
      (g := g) hcode hsize hwv hsel hsz36 hcanonTo hperm hunlocked
  have rdRev :=
    RD.uniswapExtcodesizeGuardMissing (okPc := ⟨5269⟩) rd5257
      (by simpa [σLock, token0Word, token0Clean] using htoken0NoCode)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
    reserve0Word] using rdRev

set_option maxHeartbeats 1000000 in
/-- Masked-address variant of the `skim(address)` first `balanceOf` guard revert when `token0`
has no deployed code. -/
theorem uniswapSkimRuntimeFirstBalanceOfMissingCodeReverts_masked
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (htoken0NoCode :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token1Word := uniswapSlotWord ⟨7⟩ σLock I
  let packedWord := uniswapSlotWord ⟨8⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let token1Clean := UInt256.land token1Word solcAddrMask
  let reserve0Word :=
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
      packedWord
  obtain ⟨_, _, rd5257⟩ :=
    uniswapSkimRuntimeFirstBalanceOfExtcodesize_masked
      (g := g) hcode hsize hwv hsel hsz36 hperm hunlocked
  have rdRev :=
    RD.uniswapExtcodesizeGuardMissing (okPc := ⟨5269⟩) rd5257
      (by simpa [σLock, token0Word, token0Clean] using htoken0NoCode)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [σLock, token0Word, token1Word, packedWord, token0Clean, token1Clean,
    reserve0Word] using rdRev

/-- After the external wrapper, `skim(address)` reverts when the Uniswap lock is already held. -/
theorem uniswapSkimX_locked {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd5080⟩ := uniswapSkimX_decoded
    (g := g) hsz36 hsize hcanonTo hreach
  exact RD.uniswapLockEnterLocked
    (pc := ⟨5080⟩) (okPc := ⟨5155⟩) (R := [skimToWord I, ⟨570⟩, sel])
    rd5080 uniswap_lock_enter_locked_wf hlocked
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- After the masked external wrapper, `skim(address)` reverts when the Uniswap lock is already
held. -/
theorem uniswapSkimX_locked_masked {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd5080⟩ := uniswapSkimX_decoded_masked
    (g := g) hsz36 hsize hreach
  exact RD.uniswapLockEnterLocked
    (pc := ⟨5080⟩) (okPc := ⟨5155⟩) (R := [skimToMaskedWord I, ⟨570⟩, sel])
    rd5080 uniswap_lock_enter_locked_wf hlocked
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- Short-calldata path for `skim(address)` from the dispatcher body entry.

This covers calldata with a selector present but fewer than one ABI word. The dispatcher-level
`calldatasize < 4` branch remains in `Correct.lean`.
-/
theorem uniswapSkimX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapOneAddressExternalShort
    (entry := ⟨1286⟩) (ret := ⟨570⟩) (routine := ⟨5080⟩)
    hreach uniswap_one_address_external_entry_wf hsz4 hsize hshort

end UniswapV2Pair
