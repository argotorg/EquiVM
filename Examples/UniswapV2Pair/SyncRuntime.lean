import Examples.UniswapV2Pair.ExternalCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `sync()` runtime trace prefix -/

/-- The optimized external wrapper for `sync()` jumps to the external sync routine at pc 6016. -/
theorem uniswapSyncX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6016⟩
      [⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact RD.uniswapGetterThunk
    (entry := ⟨1467⟩) (returnPc := ⟨570⟩) (routine := ⟨6016⟩)
    hreach uniswap_getter_entry_wf (by jump_dest)

/-- After the external wrapper, `sync()` successfully enters the Uniswap lock. -/
theorem uniswapSyncX_lockEntered {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6097⟩
      [⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  obtain ⟨_, _, rd6016⟩ := uniswapSyncX_decoded (g := g) hreach
  obtain ⟨_, _, rd6097⟩ := RD.uniswapLockEnterOk
    (pc := ⟨6016⟩) (okPc := ⟨6091⟩) (R := [⟨570⟩, sel])
    rd6016 uniswap_lock_enter_ok_wf hperm hunlocked (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rd6097⟩

/-- Runtime-only `sync()` slice from selector dispatch through successful lock entry. -/
theorem uniswapSyncRuntimeLockEntered
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩) :
    ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6097⟩
      [⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩ rfl hsel
  exact uniswapSyncX_lockEntered
    (g := Sat256.ofUInt256 g) hperm hunlocked
    (uniswapReachSyncBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice from successful lock entry to the first
`token0.balanceOf(address(this))` code-existence guard. -/
theorem uniswapSyncRuntimeFirstBalanceOfExtcodesize
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
    (hperm : I.perm = true)
    (hunlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩) :
    ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6160⟩
      [UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  obtain ⟨_, _, rd6097⟩ :=
    uniswapSyncRuntimeLockEntered
      (g := g) hcode hsize hwv hsel hperm hunlocked
  have rd6099 := evm_run rd6097 with [push1 ⟨6⟩]
  obtain ⟨k6100, C6100, rd6100₀⟩ := rd6099.sload (by native_decide) (by evm_ov)
  have rd6100 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6100⟩
      [token0Word, ⟨570⟩, uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σLock) k6100 C6100 := by
    simpa [σLock, token0Word, uniswapSlotWord] using rd6100₀
  have rd6113 := evm_run rd6100 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 balanceOfSelectorWord, push1 ⟨224⟩, shl, dup2]
  have rd6114 := rd6113.mstore 6 balanceOfThisSelectorMem (UInt256.ofNat 5)
    (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)
  have rd6119 := evm_run rd6114 with [
    uniswapAddress, push1 ⟨4⟩, dup3, add]
  have rd6120 := rd6119.mstore 3
    (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
    (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)
  have rd6125 := evm_run rd6120 with [
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (balanceOfThisCalldataMem_mload64 (UInt256.ofNat I.codeOwner.val))
      (by decide) (by evm_ov),
    push2 ⟨6363⟩, swap3]
  have rd6135₀ := evm_run rd6125 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and]
  have rd6135 := rd6135₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd6135
  have rd6160₀ := evm_run rd6135 with [
    swap2, push4 balanceOfSelectorWord, swap2, push1 ⟨36⟩, dup1, dup4, add,
    swap3, push1 ⟨32⟩, swap3, swap2, swap1, dup3, swap1, sub, add, dup2,
    dup7, dup1]
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide,
    show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by decide,
    show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd6160₀
  exact ⟨_, _, by simpa [σLock, token0Clean, token0Word] using rd6160₀⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice through the first `balanceOf` code-existence guard when
`token0` has deployed code, stopping immediately before `GAS; STATICCALL`. -/
theorem uniswapSyncRuntimeFirstBalanceOfStaticcallReady
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6174⟩
      [UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  obtain ⟨_, _, rd6160⟩ :=
    uniswapSyncRuntimeFirstBalanceOfExtcodesize
      (g := g) hcode hsize hwv hsel hperm hunlocked
  obtain ⟨_, _, rd6174⟩ :=
    RD.uniswapExtcodesizeGuardOk (okPc := ⟨6172⟩) rd6160
      (by simpa [σLock, token0Word, token0Clean] using htoken0Code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [σLock, token0Word, token0Clean] using rd6174⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice through `GAS`, stopping at the first
`token0.balanceOf(address(this))` `STATICCALL`. -/
theorem uniswapSyncRuntimeFirstBalanceOfStaticcallEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6175⟩
      [gasWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  obtain ⟨_, _, rd6160⟩ :=
    uniswapSyncRuntimeFirstBalanceOfExtcodesize
      (g := g) hcode hsize hwv hsel hperm hunlocked
  obtain ⟨gasWord, _, _, rd6175⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (okPc := ⟨6172⟩) rd6160
      (by simpa [σLock, token0Word, token0Clean] using htoken0Code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨gasWord, _, _, by simpa [σLock, token0Word, token0Clean] using rd6175⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice through the first opaque
`token0.balanceOf(address(this))` `STATICCALL`, exposing the shared `Θ` result. -/
theorem uniswapSyncRuntimeFirstBalanceOfStaticcallMade
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6176⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  obtain ⟨_, _, _, rd6175⟩ :=
    uniswapSyncRuntimeFirstBalanceOfStaticcallEntry
      (g := g) hcode hsize hwv hsel hperm hunlocked htoken0Code
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd6176, hoSize⟩ :=
    RD.uniswapStaticcall rd6175 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨cA', σ', z, o, A_in, callGas, k', C',
    by simpa [σLock, token0Word, token0Clean, initState] using hΘ,
    by
      simpa [σLock, token0Word, token0Clean, balanceOfThisStaticcallMem,
        balanceOfThisStaticcallActiveWords] using rd6176,
    hoSize⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice through the first `balanceOf` post-call status guard.
When the opaque `STATICCALL` succeeds, control reaches the success path at pc 6194. -/
theorem uniswapSyncRuntimeFirstBalanceOfStaticcallSuccessGuard
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6176⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true →
        ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6194⟩
          [⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, hoSize⟩ :=
    uniswapSyncRuntimeFirstBalanceOfStaticcallMade
      (g := g) hcode hsize hwv hsel hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, ?_, hoSize⟩
  intro hz
  have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
    rw [hz]
    decide
  obtain ⟨k', C', rd6194⟩ :=
    RD.uniswapCallSuccessGuardOk (okPc := ⟨6192⟩) rd6176 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨k', C', by simpa [σLock, token0Word, token0Clean] using rd6194⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice decoding the first successful `balanceOf` return word. -/
theorem uniswapSyncRuntimeFirstBalanceOfReturnWordDecoded
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6176⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true → 32 ≤ o.size →
        ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6217⟩
          [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, hsucc, hoSize⟩ :=
    uniswapSyncRuntimeFirstBalanceOfStaticcallSuccessGuard
      (g := g) hcode hsize hwv hsel hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, ?_, hoSize⟩
  intro hz ho32
  obtain ⟨_, _, rd6194⟩ := hsucc hz
  obtain ⟨k', C', rd6217⟩ :=
    RD.uniswapBalanceOfReturnWordDecodeOk
      (pc := ⟨6194⟩) (okPc := ⟨6214⟩) (self := UInt256.ofNat I.codeOwner.val)
      rd6194 ho32 hoSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by jump_dest) (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨k', C', by simpa [σLock, token0Word, token0Clean] using rd6217⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice reading `token1` from storage before the second
`balanceOf(address(this))` call is assembled. -/
theorem uniswapSyncRuntimeSecondBalanceOfToken1Sloaded
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6176⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true → 32 ≤ o.size →
        ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6220⟩
          [uniswapSlotWord ⟨7⟩ σ' I,
            UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, hdecoded, hoSize⟩ :=
    uniswapSyncRuntimeFirstBalanceOfReturnWordDecoded
      (g := g) hcode hsize hwv hsel hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, ?_, hoSize⟩
  intro hz ho32
  obtain ⟨_, _, rd6217⟩ := hdecoded hz ho32
  have rd6219 := evm_run rd6217 with [push1 ⟨7⟩]
  obtain ⟨k', C', rd6220⟩ := rd6219.sload (by native_decide) (by evm_ov)
  exact ⟨k', C', by simpa [σLock, token0Word, token0Clean, uniswapSlotWord] using rd6220⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice preparing the second `balanceOf(address(this))` selector
after `token1` has been loaded, stopping at the selector `MSTORE`. -/
theorem uniswapSyncRuntimeSecondBalanceOfSelectorReady
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6176⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true → 32 ≤ o.size →
        ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6233⟩
          [⟨128⟩, balanceOfSelectorShifted, ⟨128⟩, ⟨64⟩,
            uniswapSlotWord ⟨7⟩ σ' I,
            UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, hsload, hoSize⟩ :=
    uniswapSyncRuntimeSecondBalanceOfToken1Sloaded
      (g := g) hcode hsize hwv hsel hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, ?_, hoSize⟩
  intro hz ho32
  obtain ⟨_, _, rd6220⟩ := hsload hz ho32
  have rd6232 := evm_run rd6220 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ balanceOfThisStaticcallActiveWords (by decide)
      mem_cost
      (balanceOfThisStaticcallMem_mload64_of_size_ge
        (UInt256.ofNat I.codeOwner.val) o ho32 hoSize)
      (by decide) (by evm_ov),
    push4 balanceOfSelectorWord, push1 ⟨224⟩, shl, dup2]
  have rd6232' := rd6232
  rw [show (⟨6220⟩ : UInt256) + UInt256.ofNat 2 + (⟨1⟩ : UInt256) +
      (⟨1⟩ : UInt256) + UInt256.ofNat 5 + UInt256.ofNat 2 + (⟨1⟩ : UInt256) +
      (⟨1⟩ : UInt256) = ⟨6233⟩ from by decide] at rd6232'
  exact ⟨_, _, by simpa [balanceOfSelectorShifted] using rd6232'⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice rebuilding the second `balanceOf(address(this))` calldata
buffer after the first returned balance has been decoded. -/
theorem uniswapSyncRuntimeSecondBalanceOfCalldataRebuilt
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6176⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true → 32 ≤ o.size →
        ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6240⟩
          [⟨128⟩, ⟨64⟩, uniswapSlotWord ⟨7⟩ σ' I,
            UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, hready, hoSize⟩ :=
    uniswapSyncRuntimeSecondBalanceOfSelectorReady
      (g := g) hcode hsize hwv hsel hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, ?_, hoSize⟩
  intro hz ho32
  obtain ⟨_, _, rd6233⟩ := hready hz ho32
  have rd6234 := rd6233.mstore 0
    ((UInt256.toByteArray balanceOfSelectorShifted).write 0
      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o) 128 32)
    balanceOfThisStaticcallActiveWords
    (by native_decide) mem_cost (by rfl) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6239 := evm_run rd6234 with [uniswapAddress, push1 ⟨4⟩, dup3, add]
  have rd6240 := rd6239.mstore 0
    (balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o)
    balanceOfThisStaticcallActiveWords
    (by native_decide) mem_cost (by rfl) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [balanceOfThisRebuiltCalldataMem] using rd6240⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice cleaning the second `balanceOf` target address before the
second code-existence guard is assembled. -/
theorem uniswapSyncRuntimeSecondBalanceOfToken1Cleaned
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6176⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true → 32 ≤ o.size →
        ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6254⟩
          [⟨128⟩, ⟨128⟩, UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
            UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, hrebuilt, hoSize⟩ :=
    uniswapSyncRuntimeSecondBalanceOfCalldataRebuilt
      (g := g) hcode hsize hwv hsel hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, ?_, hoSize⟩
  intro hz ho32
  obtain ⟨_, _, rd6240⟩ := hrebuilt hz ho32
  have rd6242 := evm_run rd6240 with [
    swap1,
    raw mload 0 ⟨128⟩ balanceOfThisStaticcallActiveWords (by decide)
      mem_cost
      (balanceOfThisRebuiltCalldataMem_mload64_of_size_ge
        (UInt256.ofNat I.codeOwner.val) o ho32 hoSize)
      (by decide) (by evm_ov)]
  have rd6254₀ := evm_run rd6242 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap3, and, swap2]
  have rd6254 := rd6254₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd6254
  rw [uniswapULandComm (uniswapSlotWord ⟨7⟩ σ' I) solcAddrMask] at rd6254
  rw [show (⟨6240⟩ : UInt256) + (⟨1⟩ : UInt256) + (⟨1⟩ : UInt256) +
      UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + (⟨1⟩ : UInt256) +
      (⟨1⟩ : UInt256) + (⟨1⟩ : UInt256) + (⟨1⟩ : UInt256) +
      (⟨1⟩ : UInt256) + (⟨1⟩ : UInt256) = ⟨6254⟩ from by decide] at rd6254
  exact ⟨_, _, by simpa using rd6254⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice from the cleaned second `balanceOf` target to the
second `token1.balanceOf(address(this))` code-existence guard. -/
theorem uniswapSyncRuntimeSecondBalanceOfExtcodesize
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6176⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true → 32 ≤ o.size →
        ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6279⟩
          [UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
            UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
            ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
            UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, hcleaned, hoSize⟩ :=
    uniswapSyncRuntimeSecondBalanceOfToken1Cleaned
      (g := g) hcode hsize hwv hsel hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, ?_, hoSize⟩
  intro hz ho32
  obtain ⟨_, _, rd6254⟩ := hcleaned hz ho32
  have rd6279₀ := evm_run rd6254 with [
    push4 balanceOfSelectorWord, swap2, push1 ⟨36⟩, dup1, dup3, add,
    swap3, push1 ⟨32⟩, swap3, swap1, swap2, swap1, dup3, swap1, sub, add,
    dup2, dup7, dup1]
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide,
    show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by decide,
    show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd6279₀
  exact ⟨_, _, by simpa using rd6279₀⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice through the second `balanceOf` code-existence guard when
`token1` has deployed code after the first opaque call, stopping at the second `STATICCALL`. -/
theorem uniswapSyncRuntimeSecondBalanceOfStaticcallEntry
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6176⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true → 32 ≤ o.size →
        uniswapExtCodeSizeWord σ'
          (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I)) ≠ ⟨0⟩ →
        ∃ gasWord k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6294⟩
          [gasWord, UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
            ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
            UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, hguard, hoSize⟩ :=
    uniswapSyncRuntimeSecondBalanceOfExtcodesize
      (g := g) hcode hsize hwv hsel hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, ?_, hoSize⟩
  intro hz ho32 htoken1Code
  obtain ⟨_, _, rd6279⟩ := hguard hz ho32
  obtain ⟨gasWord, _, _, rd6294⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (okPc := ⟨6291⟩) rd6279 htoken1Code
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨gasWord, _, _, by simpa using rd6294⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice through the second opaque
`token1.balanceOf(address(this))` `STATICCALL`, exposing its shared `Θ` result. -/
theorem uniswapSyncRuntimeSecondBalanceOfStaticcallMade
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6176⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true → 32 ≤ o.size →
        uniswapExtCodeSizeWord σ'
          (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I)) ≠ ⟨0⟩ →
        ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
          (z1 : Bool) (o1 : ByteArray) (A_in1 : Substate) (callGas1 : UInt256)
          (k' C' : ℕ),
          (∃ (g'' : UInt256) (A' : Substate),
            (cA'', σ'', g'', A', z1, o1) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl
              σ' σ₀ A_in1
              (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
              (AccountAddress.ofUInt256
                (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I)))
              (toExecute σ'
                (AccountAddress.ofUInt256
                  (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I))))
              callGas1 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
              ((balanceOfThisRebuiltCalldataMem
                (UInt256.ofNat I.codeOwner.val) o).readWithPadding 128 36)
              (I.depth + 1) I.header false)
          ∧ RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6295⟩
            [(if z1 then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
              UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
              UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
              ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
            (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
            balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k' C'
          ∧ o1.size < UInt256.size)
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, hentry, hoSize⟩ :=
    uniswapSyncRuntimeSecondBalanceOfStaticcallEntry
      (g := g) hcode hsize hwv hsel hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, ?_, hoSize⟩
  intro hz ho32 htoken1Code
  obtain ⟨_, _, _, rd6294⟩ := hentry hz ho32 htoken1Code
  obtain ⟨cA'', σ'', z1, o1, A_in1, callGas1, k', C', hΘ1, rd6295, ho1Size⟩ :=
    RD.uniswapStaticcall rd6294 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨cA'', σ'', z1, o1, A_in1, callGas1, k', C',
    by simpa [balanceOfThisRebuiltStaticcallMem, initState] using hΘ1,
    by simpa [balanceOfThisRebuiltStaticcallMem, balanceOfThisStaticcallActiveWords] using rd6295,
    ho1Size⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice through the second `balanceOf` post-call status guard.
When the second opaque `STATICCALL` succeeds, control reaches the success path at pc 6313. -/
theorem uniswapSyncRuntimeSecondBalanceOfStaticcallSuccessGuard
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6176⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true → 32 ≤ o.size →
        uniswapExtCodeSizeWord σ'
          (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I)) ≠ ⟨0⟩ →
        ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
          (z1 : Bool) (o1 : ByteArray) (A_in1 : Substate) (callGas1 : UInt256)
          (k' C' : ℕ),
          (∃ (g'' : UInt256) (A' : Substate),
            (cA'', σ'', g'', A', z1, o1) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl
              σ' σ₀ A_in1
              (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
              (AccountAddress.ofUInt256
                (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I)))
              (toExecute σ'
                (AccountAddress.ofUInt256
                  (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I))))
              callGas1 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
              ((balanceOfThisRebuiltCalldataMem
                (UInt256.ofNat I.codeOwner.val) o).readWithPadding 128 36)
              (I.depth + 1) I.header false)
          ∧ RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6295⟩
            [(if z1 then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
              UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
              UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
              ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
            (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
            balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k' C'
          ∧ (z1 = true →
            ∃ k'' C'', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6313⟩
              [⟨164⟩, balanceOfSelectorWord,
                UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
                UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
                ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
              (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
              balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k'' C'')
          ∧ o1.size < UInt256.size)
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, hmade, hoSize⟩ :=
    uniswapSyncRuntimeSecondBalanceOfStaticcallMade
      (g := g) hcode hsize hwv hsel hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, ?_, hoSize⟩
  intro hz ho32 htoken1Code
  obtain ⟨cA'', σ'', z1, o1, A_in1, callGas1, k', C', hΘ1, rd6295, ho1Size⟩ :=
    hmade hz ho32 htoken1Code
  refine ⟨cA'', σ'', z1, o1, A_in1, callGas1, k', C', hΘ1, rd6295, ?_, ho1Size⟩
  intro hz1
  have hstatus : (if z1 then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
    rw [hz1]
    decide
  obtain ⟨k'', C'', rd6313⟩ :=
    RD.uniswapCallSuccessGuardOk (okPc := ⟨6311⟩) rd6295 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨k'', C'', by simpa using rd6313⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice through decoding the second successful
`token1.balanceOf(address(this))` return word. -/
theorem uniswapSyncRuntimeSecondBalanceOfReturnWordDecoded
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6176⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true → 32 ≤ o.size →
        uniswapExtCodeSizeWord σ'
          (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I)) ≠ ⟨0⟩ →
        ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
          (z1 : Bool) (o1 : ByteArray) (A_in1 : Substate) (callGas1 : UInt256)
          (k' C' : ℕ),
          (∃ (g'' : UInt256) (A' : Substate),
            (cA'', σ'', g'', A', z1, o1) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl
              σ' σ₀ A_in1
              (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
              (AccountAddress.ofUInt256
                (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I)))
              (toExecute σ'
                (AccountAddress.ofUInt256
                  (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I))))
              callGas1 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
              ((balanceOfThisRebuiltCalldataMem
                (UInt256.ofNat I.codeOwner.val) o).readWithPadding 128 36)
              (I.depth + 1) I.header false)
          ∧ RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6295⟩
            [(if z1 then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
              UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
              UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
              ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
            (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
            balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k' C'
          ∧ (z1 = true → 32 ≤ o1.size →
            ∃ k'' C'', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6336⟩
              [UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32)),
                UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
                ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
              (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
              balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k'' C'')
          ∧ o1.size < UInt256.size)
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, hmade, hoSize⟩ :=
    uniswapSyncRuntimeSecondBalanceOfStaticcallSuccessGuard
      (g := g) hcode hsize hwv hsel hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, ?_, hoSize⟩
  intro hz ho32 htoken1Code
  obtain ⟨cA'', σ'', z1, o1, A_in1, callGas1, k', C', hΘ1, rd6295, hguard, ho1Size⟩ :=
    hmade hz ho32 htoken1Code
  refine ⟨cA'', σ'', z1, o1, A_in1, callGas1, k', C', hΘ1, rd6295, ?_, ho1Size⟩
  intro hz1 ho132
  obtain ⟨_, _, rd6313⟩ := hguard hz1
  obtain ⟨k'', C'', rd6336⟩ :=
    RD.uniswapRebuiltBalanceOfReturnWordDecodeOk (okPc := ⟨6333⟩) rd6313
      ho32 hoSize ho132 ho1Size
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by jump_dest) (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨k'', C'', by simpa using rd6336⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only straight-line slice that loads slot 8 and unpacks the two uint112 reserves
before jumping into Uniswap's shared `_update` routine. -/
theorem uniswapSyncReserveSlotUnpack {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {balance1 balance0 : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    (h : RD uniswapV2PairBytecode ee g s0 ⟨6336⟩ (balance1 :: balance0 :: R)
      mem aw rdata (cA, σ) k C)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨6959⟩
      (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σ ee) reserve112Shift)
          reserve112Mask ::
        UInt256.land (uniswapSlotWord ⟨8⟩ σ ee) reserve112Mask ::
        balance1 :: balance0 :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd6338 := evm_run h with [push1 ⟨8⟩]
  obtain ⟨_, _, rd6339⟩ := rd6338.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd6362 := evm_run rd6339 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup1, dup3, and, swap2,
    push1 ⟨1⟩, push1 ⟨112⟩, shl, swap1, div, and, push2 ⟨6959⟩]
  have rd6959 := evm_run rd6362 with [jump (by jump_dest)]
  exact ⟨_, _, by simpa [uniswapSlotWord, reserve112Shift, reserve112Mask] using rd6959⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice through the reserve-slot unpack that prepares the shared
`_update(balance0,balance1,_reserve0,_reserve1)` routine. -/
theorem uniswapSyncRuntimeReserveSlotUnpacked
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6176⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ (z = true → 32 ≤ o.size →
        uniswapExtCodeSizeWord σ'
          (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I)) ≠ ⟨0⟩ →
        ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
          (z1 : Bool) (o1 : ByteArray) (A_in1 : Substate) (callGas1 : UInt256)
          (k' C' : ℕ),
          (∃ (g'' : UInt256) (A' : Substate),
            (cA'', σ'', g'', A', z1, o1) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl
              σ' σ₀ A_in1
              (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
              (AccountAddress.ofUInt256
                (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I)))
              (toExecute σ'
                (AccountAddress.ofUInt256
                  (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I))))
              callGas1 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
              ((balanceOfThisRebuiltCalldataMem
                (UInt256.ofNat I.codeOwner.val) o).readWithPadding 128 36)
              (I.depth + 1) I.header false)
          ∧ RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6295⟩
            [(if z1 then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
              UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
              UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
              ⟨6363⟩, ⟨570⟩, uniswapSelWord I]
            (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
            balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k' C'
          ∧ (z1 = true → 32 ≤ o1.size →
            ∃ k'' C'', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6959⟩
              (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σ'' I) reserve112Shift)
                  reserve112Mask ::
                UInt256.land (uniswapSlotWord ⟨8⟩ σ'' I) reserve112Mask ::
                UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32)) ::
                UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) ::
                ⟨6363⟩ :: ⟨570⟩ :: uniswapSelWord I :: [])
              (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
              balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k'' C'')
          ∧ o1.size < UInt256.size)
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, hmade, hoSize⟩ :=
    uniswapSyncRuntimeSecondBalanceOfReturnWordDecoded
      (g := g) hcode hsize hwv hsel hperm hdepth hunlocked htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd6176, ?_, hoSize⟩
  intro hz ho32 htoken1Code
  obtain ⟨cA'', σ'', z1, o1, A_in1, callGas1, k', C', hΘ1, rd6295, hdecode, ho1Size⟩ :=
    hmade hz ho32 htoken1Code
  refine ⟨cA'', σ'', z1, o1, A_in1, callGas1, k', C', hΘ1, rd6295, ?_, ho1Size⟩
  intro hz1 ho132
  obtain ⟨_, _, rd6336⟩ := hdecode hz1 ho132
  obtain ⟨k'', C'', rd6959⟩ := uniswapSyncReserveSlotUnpack rd6336
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨k'', C'', by simpa using rd6959⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `sync()` slice showing that the first `balanceOf` guard reverts before the
external call when `token0` has no deployed code. -/
theorem uniswapSyncRuntimeFirstBalanceOfMissingCodeReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩)
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
  let token0Clean := UInt256.land solcAddrMask token0Word
  obtain ⟨_, _, rd6160⟩ :=
    uniswapSyncRuntimeFirstBalanceOfExtcodesize
      (g := g) hcode hsize hwv hsel hperm hunlocked
  have rdRev :=
    RD.uniswapExtcodesizeGuardMissing (okPc := ⟨6172⟩) rd6160
      (by simpa [σLock, token0Word, token0Clean] using htoken0NoCode)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [σLock, token0Word, token0Clean] using rdRev

/-- After the external wrapper, `sync()` reverts when the Uniswap lock is already held. -/
theorem uniswapSyncX_locked {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hlocked :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1467⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd6016⟩ := uniswapSyncX_decoded (g := g) hreach
  exact RD.uniswapLockEnterLocked
    (pc := ⟨6016⟩) (okPc := ⟨6091⟩) (R := [⟨570⟩, sel])
    rd6016 uniswap_lock_enter_locked_wf hlocked
    (by simp only [List.length_cons, List.length_nil]; omega)
