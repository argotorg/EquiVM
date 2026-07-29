import Examples.UniswapV2Pair.MintSourceCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` slice from successful lock entry through the internal
`getReserves` routine. -/
theorem uniswapMintRuntimeReservesLoaded
    {cA gh bl σ σ₀ A I} {g : UInt256} {toWord sel : UInt256}
    (hlockEntered : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3368⟩
      [⟨0⟩, ⟨0⟩, toWord, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C) :
    ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3378⟩
      [reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, ⟨0⟩, ⟨0⟩, toWord, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  obtain ⟨_, _, rd3368⟩ := hlockEntered
  have rd2852 := evm_run rd3368 with [
    dup1, push2 ⟨3376⟩, push2 ⟨2852⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3376⟩ :=
    RD.uniswapGetReservesRoutine (ret := ⟨3376⟩)
      (R := [⟨0⟩, ⟨0⟩, ⟨0⟩, toWord, ⟨861⟩, sel])
      rd2852 (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3378 := evm_run rd3376 with [jumpdest, pop]
  exact ⟨_, _, by simpa [σLock] using rd3378⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` slice from loaded reserves to the first
`token0.balanceOf(address(this))` code-existence guard. -/
theorem uniswapMintRuntimeFirstBalanceOfExtcodesize
    {cA gh bl σ σ₀ A I} {g : UInt256} {toWord sel : UInt256}
    (hlockEntered : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3368⟩
      [⟨0⟩, ⟨0⟩, toWord, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C) :
    ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3448⟩
      [UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  obtain ⟨_, _, rd3378⟩ :=
    uniswapMintRuntimeReservesLoaded (g := g) hlockEntered
  have rd3380 := evm_run rd3378 with [push1 ⟨6⟩]
  obtain ⟨k3381, C3381, rd3381₀⟩ := rd3380.sload (by native_decide) (by evm_ov)
  have rd3381 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3381⟩
      [token0Word, reserve1Word σLock I, reserve0Word σLock I,
        ⟨0⟩, ⟨0⟩, ⟨0⟩, toWord, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σLock) k3381 C3381 := by
    simpa [σLock, token0Word, uniswapSlotWord] using rd3381₀
  have rd3394 := evm_run rd3381 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 balanceOfSelectorWord, push1 ⟨224⟩, shl, dup2]
  have rd3395 := rd3394.mstore 6 balanceOfThisSelectorMem (UInt256.ofNat 5)
    (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)
  have rd3400 := evm_run rd3395 with [
    address, push1 ⟨4⟩, dup3, add]
  have rd3401 := rd3400.mstore 3
    (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
    (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)
  have rd3423₀ := evm_run rd3401 with [
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (balanceOfThisCalldataMem_mload64 (UInt256.ofNat I.codeOwner.val))
      (by decide) (by evm_ov),
    swap4, swap6, pop, swap2, swap4, pop, push1 ⟨0⟩, swap3,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2, and]
  have rd3423 := rd3423₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd3423
  have rd3448₀ := evm_run rd3423 with [
    swap2, push4 balanceOfSelectorWord, swap2, push1 ⟨36⟩, dup1, dup4, add,
    swap3, push1 ⟨32⟩, swap3, swap2, swap1, dup3, swap1, sub, add, dup2,
    dup7, dup1]
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide,
    show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by decide,
    show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd3448₀
  rw [← u256_land_comm solcAddrMask] at rd3448₀
  norm_num at rd3448₀
  exact ⟨_, _, by simpa [σLock, token0Clean, token0Word] using rd3448₀⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` slice through the first `balanceOf` code-existence
guard when `token0` has deployed code, stopping immediately before `GAS; STATICCALL`. -/
theorem uniswapMintRuntimeFirstBalanceOfStaticcallReady
    {cA gh bl σ σ₀ A I} {g : UInt256} {toWord sel : UInt256}
    (hlockEntered : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3368⟩
      [⟨0⟩, ⟨0⟩, toWord, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C)
    (htoken0Code :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3462⟩
      [UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  obtain ⟨_, _, rd3448⟩ :=
    uniswapMintRuntimeFirstBalanceOfExtcodesize (g := g) hlockEntered
  obtain ⟨_, _, rd3462⟩ :=
    RD.solcExtcodesizeGuardOk (okPc := ⟨3460⟩) rd3448
      (by simpa [σLock, token0Word, token0Clean] using htoken0Code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [σLock, token0Word, token0Clean] using rd3462⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` slice through `GAS`, stopping at the first
`token0.balanceOf(address(this))` `STATICCALL`. -/
theorem uniswapMintRuntimeFirstBalanceOfStaticcallEntry
    {cA gh bl σ σ₀ A I} {g : UInt256} {toWord sel : UInt256}
    (hlockEntered : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3368⟩
      [⟨0⟩, ⟨0⟩, toWord, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C)
    (htoken0Code :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    ∃ gasWord k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3463⟩
      [gasWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)) (UInt256.ofNat 6)
      ByteArray.empty (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  obtain ⟨_, _, rd3448⟩ :=
    uniswapMintRuntimeFirstBalanceOfExtcodesize (g := g) hlockEntered
  obtain ⟨gasWord, _, _, rd3463⟩ :=
    RD.solcExtcodesizeGuardOkGas (okPc := ⟨3460⟩) rd3448
      (by simpa [σLock, token0Word, token0Clean] using htoken0Code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨gasWord, _, _, by simpa [σLock, token0Word, token0Clean] using rd3463⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` slice through the first opaque
`token0.balanceOf(address(this))` `STATICCALL`, exposing the shared `Θ` result. -/
theorem uniswapMintRuntimeFirstBalanceOfStaticcallMade
    {cA gh bl σ σ₀ A I} {g : UInt256} {toWord sel : UInt256}
    (hdepth : I.depth.val < 1024)
    (hlockEntered : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3368⟩
      [⟨0⟩, ⟨0⟩, toWord, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C)
    (htoken0Code :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
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
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3464⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨164⟩, balanceOfSelectorWord,
            UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
            ⟨0⟩,
            reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
            reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
            ⟨0⟩, toWord, ⟨861⟩, sel]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k C
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  obtain ⟨_, _, _, rd3463⟩ :=
    uniswapMintRuntimeFirstBalanceOfStaticcallEntry
      (g := g) hlockEntered htoken0Code
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd3464, hoSize⟩ :=
    RD.solcStaticcall rd3463 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨cA', σ', z, o, A_in, callGas, k', C',
    by simpa [σLock, token0Word, token0Clean, initState] using hΘ,
    by
      simpa [σLock, token0Word, token0Clean, balanceOfThisStaticcallMem,
        balanceOfThisStaticcallActiveWords] using rd3464,
    hoSize⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` branches after the first `balanceOf` call. -/
theorem uniswapMintRuntimeFirstBalanceOfResultBranches
    {cA gh bl σ σ₀ A I} {g : UInt256} {toWord sel : UInt256}
    (hdepth : I.depth.val < 1024)
    (hlockEntered : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3368⟩
      [⟨0⟩, ⟨0⟩, toWord, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C)
    (htoken0Code :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
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
      ∧ (z = true → 32 ≤ o.size →
        ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3505⟩
          [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
            ⟨0⟩,
            reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
            reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
            ⟨0⟩, toWord, ⟨861⟩, sel]
          (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
          balanceOfThisStaticcallActiveWords o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd3464, hoSize⟩ :=
    uniswapMintRuntimeFirstBalanceOfStaticcallMade
      (g := g) hdepth hlockEntered htoken0Code
  refine ⟨cA', σ', z, o, A_in, callGas, hΘ, ?_, ?_, ?_, hoSize⟩
  · intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      simp [hz]
    exact RD.solcCallSuccessGuardMissing (okPc := ⟨3480⟩) rd3464 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) hoSize
      (by simp only [List.length_cons, List.length_nil]; omega)
  · intro hz hshort
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    obtain ⟨_, _, rd3482⟩ :=
      RD.solcCallSuccessGuardOk (okPc := ⟨3480⟩) rd3464 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    exact RD.uniswapBalanceOfReturnWordDecodeShortReverts
      (pc := ⟨3482⟩) (okPc := ⟨3502⟩) (self := UInt256.ofNat I.codeOwner.val)
      rd3482 hshort hoSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  · intro hz ho32
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    obtain ⟨_, _, rd3482⟩ :=
      RD.solcCallSuccessGuardOk (okPc := ⟨3480⟩) rd3464 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    obtain ⟨k', C', rd3505⟩ :=
      RD.uniswapBalanceOfReturnWordDecodeOk
        (pc := ⟨3482⟩) (okPc := ⟨3502⟩) (self := UInt256.ofNat I.codeOwner.val)
        rd3482 ho32 hoSize
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by jump_dest) (by native_decide) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    exact ⟨k', C', by simpa [σLock, token0Word, token0Clean] using rd3505⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` reverts when `token0.balanceOf(address(this))` targets an
account without deployed code. -/
theorem uniswapMintRuntimeFirstBalanceOfMissingCodeReverts
    {cA gh bl σ σ₀ A I} {g : UInt256} {toWord sel : UInt256}
    (hlockEntered : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3368⟩
      [⟨0⟩, ⟨0⟩, toWord, ⟨861⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C)
    (htoken0NoCode :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := uniswapSlotWord ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  obtain ⟨_, _, rd3448⟩ :=
    uniswapMintRuntimeFirstBalanceOfExtcodesize (g := g) hlockEntered
  exact RD.solcExtcodesizeGuardMissing (okPc := ⟨3460⟩) rd3448
    (by simpa [σLock, token0Word, token0Clean] using htoken0NoCode)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` first `balanceOf` slice for the call-depth limit.

At depth 1024 the `STATICCALL` is not made, pushes status `0`, and the high-level
call-success guard reverts. -/
theorem uniswapMintRuntimeFirstBalanceOfStaticcallDepthReverts
    {cA gh bl σ σ₀ A I} {g : UInt256} {k C : ℕ}
    {gasArg target inOffset inSize outOffset outSize : UInt256}
    {t : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (rd3463 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3463⟩
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: t)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) k C)
    (hdepth : I.depth = 1024)
    (hovStatic : t.length + 1 ≤ 1024)
    (hovGuard : t.length + 5 ≤ 1024) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd3464⟩ :=
    RD.solcStaticcallDepthLimit rd3463 (by native_decide) hdepth hovStatic
  have rdRev :=
    RD.solcCallSuccessGuardMissing (okPc := ⟨3480⟩) rd3464 rfl
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by decide)
      hovGuard
  simpa using rdRev

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` slice from the first decoded `balanceOf` return word to the
second `token1.balanceOf(address(this))` code-existence guard. -/
theorem uniswapMintRuntimeSecondBalanceOfExtcodesizeFromFirst
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o : ByteArray} {k C : ℕ} {balance0 toWord sel : UInt256}
    (rd3505 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3505⟩
      [balance0, ⟨0⟩,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
      balanceOfThisStaticcallActiveWords o (cA', σ') k C)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3573⟩
      [UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
        UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
        ⟨0⟩, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o)
      balanceOfThisStaticcallActiveWords o (cA', σ') k' C' := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token1Word := uniswapSlotWord ⟨7⟩ σ' I
  let token1Clean := UInt256.land solcAddrMask token1Word
  have rd3507 := evm_run rd3505 with [push1 ⟨7⟩]
  obtain ⟨k3508, C3508, rd3508₀⟩ := rd3507.sload (by native_decide) (by evm_ov)
  have rd3508 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3508⟩
      [token1Word, balance0, ⟨0⟩, reserve1Word σLock I, reserve0Word σLock I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
      balanceOfThisStaticcallActiveWords o (cA', σ') k3508 C3508 := by
    simpa [σLock, token1Word, uniswapSlotWord] using rd3508₀
  have rd3520 := evm_run rd3508 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ balanceOfThisStaticcallActiveWords (by decide)
      mem_cost
      (balanceOfThisStaticcallMem_mload64_of_size_ge
        (UInt256.ofNat I.codeOwner.val) o ho32 hoSize)
      (by decide) (by evm_ov),
    push4 balanceOfSelectorWord, push1 ⟨224⟩, shl, dup2]
  have rd3522 := rd3520.mstore 0
    ((UInt256.toByteArray balanceOfSelectorShifted).write 0
      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o) 128 32)
    balanceOfThisStaticcallActiveWords
    (by native_decide) mem_cost (by rfl) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3527 := evm_run rd3522 with [address, push1 ⟨4⟩, dup3, add]
  have rd3528 := rd3527.mstore 0
    (balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o)
    balanceOfThisStaticcallActiveWords
    (by native_decide) mem_cost (by rfl) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3547₀ := evm_run rd3528 with [
    swap1,
    raw mload 0 ⟨128⟩ balanceOfThisStaticcallActiveWords (by decide)
      mem_cost
      (balanceOfThisRebuiltCalldataMem_mload64_of_size_ge
        (UInt256.ofNat I.codeOwner.val) o ho32 hoSize)
      (by decide) (by evm_ov),
    swap3, swap4, pop, push1 ⟨0⟩, swap3,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap3, and, swap2]
  have rd3547 := rd3547₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd3547
  rw [u256_land_comm token1Word solcAddrMask] at rd3547
  norm_num at rd3547
  have rd3573₀ := evm_run rd3547 with [
    push4 balanceOfSelectorWord, swap2, push1 ⟨36⟩, dup1, dup3, add,
    swap3, push1 ⟨32⟩, swap3, swap1, swap2, swap1, dup3, swap1, sub, add,
    dup2, dup7, dup1]
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by decide,
    show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by decide,
    show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ from by decide] at rd3573₀
  exact ⟨_, _, by simpa [σLock, token1Word, token1Clean] using rd3573₀⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` branches after the second `balanceOf` call. -/
theorem uniswapMintRuntimeSecondBalanceOfResultBranchesFromExtcodesize
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o : ByteArray} {k C : ℕ} {balance0 toWord sel : UInt256}
    (rd3573 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3573⟩
      [UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
        UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
        ⟨0⟩, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o)
      balanceOfThisStaticcallActiveWords o (cA', σ') k C)
    (hdepth : I.depth.val < 1024)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (htoken1Code :
      extCodeSizeWord σ'
        (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I)) ≠ ⟨0⟩) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z1 : Bool) (o1 : ByteArray) (A_in1 : Substate) (callGas1 : UInt256),
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
      ∧ (z1 = false →
        RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
      ∧ (z1 = true → o1.size < 32 →
        RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))
      ∧ (z1 = true → 32 ≤ o1.size →
        ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3630⟩
          [UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32)),
            ⟨0⟩, balance0,
            reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
            reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
            ⟨0⟩, toWord, ⟨861⟩, sel]
          (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
          balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k' C')
      ∧ o1.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd3588⟩ :=
    RD.solcExtcodesizeGuardOkGas (okPc := ⟨3585⟩) rd3573 htoken1Code
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cA'', σ'', z1, o1, A_in1, callGas1, k', C', hΘ1, rd3589, ho1Size⟩ :=
    RD.solcStaticcall rd3588 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨cA'', σ'', z1, o1, A_in1, callGas1, ?_, ?_, ?_, ?_, ho1Size⟩
  · simpa [balanceOfThisRebuiltStaticcallMem, initState] using hΘ1
  · intro hz1
    have hstatus : (if z1 then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      simp [hz1]
    exact RD.solcCallSuccessGuardMissing (okPc := ⟨3605⟩) rd3589 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) ho1Size
      (by simp only [List.length_cons, List.length_nil]; omega)
  · intro hz1 hshort
    have hstatus : (if z1 then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz1]
      decide
    obtain ⟨_, _, rd3607⟩ :=
      RD.solcCallSuccessGuardOk (okPc := ⟨3605⟩) rd3589 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    exact RD.uniswapRebuiltBalanceOfReturnWordDecodeShortReverts
      (pc := ⟨3607⟩) (okPc := ⟨3627⟩) (self := UInt256.ofNat I.codeOwner.val)
      rd3607 ho32 hoSize hshort ho1Size
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  · intro hz1 ho132
    have hstatus : (if z1 then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz1]
      decide
    obtain ⟨_, _, rd3607⟩ :=
      RD.solcCallSuccessGuardOk (okPc := ⟨3605⟩) rd3589 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    obtain ⟨k'', C'', rd3630⟩ :=
      RD.uniswapRebuiltBalanceOfReturnWordDecodeOk
        (pc := ⟨3607⟩) (okPc := ⟨3627⟩) (self := UInt256.ofNat I.codeOwner.val)
        rd3607 ho32 hoSize ho132 ho1Size
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by jump_dest) (by native_decide) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    exact ⟨k'', C'', rd3630⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` reverts when `token1.balanceOf(address(this))` targets an
account without deployed code. -/
theorem uniswapMintRuntimeSecondBalanceOfMissingCodeFromExtcodesize
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {o : ByteArray} {k C : ℕ} {balance0 toWord sel : UInt256}
    (rd3573 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3573⟩
      [UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
        UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
        ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩, ⟨164⟩, balanceOfSelectorWord,
        UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I),
        ⟨0⟩, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o)
      balanceOfThisStaticcallActiveWords o (cA', σ') k C)
    (htoken1NoCode :
      extCodeSizeWord σ'
        (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ' I)) = ⟨0⟩) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcExtcodesizeGuardMissing (okPc := ⟨3585⟩) rd3573 htoken1NoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` slice through the first checked subtraction,
`amount0 = balance0 - _reserve0`, on the non-underflow path. -/
theorem uniswapMintRuntimeAmount0SubSuccessFromBalances
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA'' : Batteries.RBSet AccountAddress compare} {σ'' : AccountMap}
    {o o1 : ByteArray} {k C : ℕ} {balance0 balance1 toWord sel : UInt256}
    (rd3630 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3630⟩
      [balance1, ⟨0⟩, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k C)
    (hle0 :
      (reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I).toNat ≤
        balance0.toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3661⟩
      [UInt256.sub balance0
          (reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k' C' := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let reserve0 := reserve0Word σLock I
  let reserve1 := reserve1Word σLock I
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 := by
    exact reserve112Mask_clean_of_lt reserve0 (by
      simpa [reserve0, reserve0Word] using reserve112Word_lt (getReservesSlotWord σLock I))
  have rd3657pre := evm_run rd3630 with [
    swap1, pop, push1 ⟨0⟩, push2 ⟨3658⟩, dup4, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨112⟩, shl, sub, dup8, and, push4 ⟨0xffffffff⟩, push2 ⟨6879⟩, and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ =
      reserve112Mask from by rfl,
    hclean0,
    show UInt256.land (⟨6879⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6879⟩ from by decide]
    at rd3657pre
  have rd6879 := rd3657pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3658⟩ :=
    RD.uniswapSafeMathSubSuccess rd6879
      (by simpa [σLock, reserve0] using hle0)
      (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3661 := evm_run rd3658 with [jumpdest, swap1, pop]
  exact ⟨_, _, by simpa [σLock, reserve0, reserve1] using rd3661⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` slice through the second checked subtraction,
`amount1 = balance1 - _reserve1`, on the non-underflow path. -/
theorem uniswapMintRuntimeAmount1SubSuccessFromAmount0
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA'' : Batteries.RBSet AccountAddress compare} {σ'' : AccountMap}
    {o o1 : ByteArray} {k C : ℕ} {amount0 balance0 balance1 toWord sel : UInt256}
    (rd3661 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3661⟩
      [amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k C)
    (hle1 :
      (reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I).toNat ≤
        balance1.toNat) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3690⟩
      [UInt256.sub balance1
          (reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I),
        amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k' C' := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let reserve0 := reserve0Word σLock I
  let reserve1 := reserve1Word σLock I
  have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 := by
    exact reserve112Mask_clean_of_lt reserve1 (by
      simpa [reserve1, reserve1Word] using
        reserve112Word_lt (UInt256.div (getReservesSlotWord σLock I) reserve112Shift))
  have rd3686pre := evm_run rd3661 with [
    push1 ⟨0⟩, push2 ⟨3687⟩, dup4, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨112⟩, shl, sub, dup8, and, push4 ⟨0xffffffff⟩, push2 ⟨6879⟩, and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ =
      reserve112Mask from by rfl,
    hclean1,
    show UInt256.land (⟨6879⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6879⟩ from by decide]
    at rd3686pre
  have rd6879 := rd3686pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd3687⟩ :=
    RD.uniswapSafeMathSubSuccess rd6879
      (by simpa [σLock, reserve1] using hle1)
      (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3690 := evm_run rd3687 with [jumpdest, swap1, pop]
  exact ⟨_, _, by simpa [σLock, reserve0, reserve1] using rd3690⟩

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` reverts when `amount0 = balance0 - _reserve0` underflows. -/
theorem uniswapMintRuntimeAmount0SubUnderflowFromBalances
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA'' : Batteries.RBSet AccountAddress compare} {σ'' : AccountMap}
    {o o1 : ByteArray} {k C : ℕ} {balance0 balance1 toWord sel : UInt256}
    (rd3630 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3630⟩
      [balance1, ⟨0⟩, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k C)
    (hlt0 :
      balance0.toNat <
        (reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I).toNat)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let reserve0 := reserve0Word σLock I
  let reserve1 := reserve1Word σLock I
  have hclean0 : UInt256.land reserve0 reserve112Mask = reserve0 := by
    exact reserve112Mask_clean_of_lt reserve0 (by
      simpa [reserve0, reserve0Word] using reserve112Word_lt (getReservesSlotWord σLock I))
  have rd3657pre := evm_run rd3630 with [
    swap1, pop, push1 ⟨0⟩, push2 ⟨3658⟩, dup4, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨112⟩, shl, sub, dup8, and, push4 ⟨0xffffffff⟩, push2 ⟨6879⟩, and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ =
      reserve112Mask from by rfl,
    hclean0,
    show UInt256.land (⟨6879⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6879⟩ from by decide]
    at rd3657pre
  have rd6879 := rd3657pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have hmem :
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1).size =
        164 :=
    balanceOfThisRebuiltStaticcallMem_size_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132 ho1Size
  have hread64 :
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    balanceOfThisRebuiltStaticcallMem_read64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132 ho1Size
  exact RD.uniswapSafeMathSubUnderflow_aw6_size164_shared rd6879
    (by simpa [σLock, reserve0] using hlt0) hmem hread64
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` reverts when `amount1 = balance1 - _reserve1` underflows. -/
theorem uniswapMintRuntimeAmount1SubUnderflowFromAmount0
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA'' : Batteries.RBSet AccountAddress compare} {σ'' : AccountMap}
    {o o1 : ByteArray} {k C : ℕ} {amount0 balance0 balance1 toWord sel : UInt256}
    (rd3661 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3661⟩
      [amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k C)
    (hlt1 :
      balance1.toNat <
        (reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I).toNat)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (ho132 : 32 ≤ o1.size) (ho1Size : o1.size < UInt256.size) :
    RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let reserve0 := reserve0Word σLock I
  let reserve1 := reserve1Word σLock I
  have hclean1 : UInt256.land reserve1 reserve112Mask = reserve1 := by
    exact reserve112Mask_clean_of_lt reserve1 (by
      simpa [reserve1, reserve1Word] using
        reserve112Word_lt (UInt256.div (getReservesSlotWord σLock I) reserve112Shift))
  have rd3686pre := evm_run rd3661 with [
    push1 ⟨0⟩, push2 ⟨3687⟩, dup4, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨112⟩, shl, sub, dup8, and, push4 ⟨0xffffffff⟩, push2 ⟨6879⟩, and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ =
      reserve112Mask from by rfl,
    hclean1,
    show UInt256.land (⟨6879⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6879⟩ from by decide]
    at rd3686pre
  have rd6879 := rd3686pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have hmem :
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1).size =
        164 :=
    balanceOfThisRebuiltStaticcallMem_size_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132 ho1Size
  have hread64 :
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    balanceOfThisRebuiltStaticcallMem_read64_of_size_ge
      (UInt256.ofNat I.codeOwner.val) o o1 ho32 hoSize ho132 ho1Size
  exact RD.uniswapSafeMathSubUnderflow_aw6_size164_shared rd6879
    (by simpa [σLock, reserve1] using hlt1) hmem hread64
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
/-- Runtime-only `mint(address)` slice from the two decoded amounts to the internal
`_mintFee` routine entry. -/
theorem uniswapMintRuntimeMintFeeEntryFromAmounts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cA'' : Batteries.RBSet AccountAddress compare} {σ'' : AccountMap}
    {o o1 : ByteArray} {k C : ℕ} {amount0 amount1 balance0 balance1 toWord sel : UInt256}
    (rd3690 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3690⟩
      [amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k C) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7696⟩
      [reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        reserve0Word (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      (balanceOfThisRebuiltStaticcallMem (UInt256.ofNat I.codeOwner.val) o o1)
      balanceOfThisStaticcallActiveWords o1 (cA'', σ'') k' C' := by
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  have rd7696 := evm_run rd3690 with [
    push1 ⟨0⟩, push2 ⟨3701⟩, dup8, dup8, push2 ⟨7696⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [σLock] using rd7696⟩


end UniswapV2Pair
