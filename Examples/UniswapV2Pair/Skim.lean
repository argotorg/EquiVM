import Examples.UniswapV2Pair.Common
import Examples.UniswapV2Pair.ExternalWrappers
import Examples.UniswapV2Pair.ExternalCalls
import Examples.UniswapV2Pair.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `skim(address)` source/ABI prefix -/

/-- The raw ABI word for `skim`'s `to` argument. -/
abbrev skimToWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev skimToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (skimToWord I).toNat)

abbrev skimStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "to" (skimToValue I)

abbrev skimBalanceValue (balance : UInt256) : Value :=
  uniswapUint256Value balance

abbrev skimBalanceStore (I : ExecutionEnv) (balance0 balance1 : UInt256) : Store :=
  uniswapBalanceOfStore (skimStore I) (skimBalanceValue balance0) (skimBalanceValue balance1)

def skimExcess0Word (evm : EVM.State) (balance0 : UInt256) : UInt256 :=
  UInt256.ofNat (balance0.toNat - (uniswapReserve0Word evm).toNat)

def skimExcess1Word (evm : EVM.State) (balance1 : UInt256) : UInt256 :=
  UInt256.ofNat (balance1.toNat - (uniswapReserve1Word evm).toNat)

abbrev skimExcess0Value (evm : EVM.State) (balance0 : UInt256) : Value :=
  .int (Int.ofNat (skimExcess0Word evm balance0).toNat)

abbrev skimExcess1Value (evm : EVM.State) (balance1 : UInt256) : Value :=
  .int (Int.ofNat (skimExcess1Word evm balance1).toNat)

abbrev skimExcess0Store (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) : Store :=
  (skimBalanceStore I balance0 balance1).insert "excess0" (skimExcess0Value evm balance0)

abbrev skimExcessStore (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) : Store :=
  (skimExcess0Store evm I balance0 balance1).insert "excess1"
    (skimExcess1Value evm balance1)

abbrev skimSafeTransfer0Store (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (success : Bool) (out : ByteArray) : Store :=
  ((skimExcessStore evm I balance0 balance1).insert "ok0" (.bool success)).insert "_ret0"
    (.bytes out)

abbrev skimSafeTransfer1Store (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (out0 : ByteArray) (success : Bool) (out1 : ByteArray) :
    Store :=
  uniswapLowLevelCallRequireStore
    (skimSafeTransfer0Store evm I balance0 balance1 true out0) "ok1" "_ret1" success out1

theorem skimBalanceStore_balance0 (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimBalanceStore I balance0 balance1).get? "balance0" =
      some (skimBalanceValue balance0) := by
  exact uniswapBalanceOfStore_balance0 (skimStore I) (skimBalanceValue balance0)
    (skimBalanceValue balance1)

theorem skimBalanceStore_balance1 (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimBalanceStore I balance0 balance1).get? "balance1" =
      some (skimBalanceValue balance1) := by
  exact uniswapBalanceOfStore_balance1 (skimStore I) (skimBalanceValue balance0)
    (skimBalanceValue balance1)

theorem skimExcess0Store_balance1 (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) :
    (skimExcess0Store evm I balance0 balance1).get? "balance1" =
      some (skimBalanceValue balance1) := by
  rw [skimExcess0Store, store_get_ne _ _ (by decide), skimBalanceStore_balance1]

theorem skimSafeTransfer0Store_ok0 (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (success : Bool) (out : ByteArray) :
    (skimSafeTransfer0Store evm I balance0 balance1 success out).get? "ok0" =
      some (.bool success) := by
  rw [skimSafeTransfer0Store, store_get_ne _ _ (by decide), store_get_self]

theorem evalExpr_skim_safeTransfer0_ok (storeEvm evalEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (success : Bool) (out : ByteArray) :
    evalExpr? config
      { contract := contract, locals := skimSafeTransfer0Store storeEvm I balance0 balance1 success out }
      evalEvm (.var "ok0") = .ok (.bool success) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [skimSafeTransfer0Store_ok0]

theorem uniswapDecode_skim_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (skimToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (skimTransition.params.map Param.name)
      (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I) := by
  show decodeCalldata ["to"] [addr] I.calldata = _
  simpa [skimStore, skimToValue, skimToWord, calldataWord]
    using decodeCalldata_address_ok (cd := I.calldata) (x := "to") hsz36 hbig hcanon

theorem uniswapDecode_skim_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (skimTransition.params.map Param.name)
      (transitionSignature skimTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["to"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_short (cd := I.calldata) (x := "to")
    hsz4 hshort

theorem uniswapDecode_skim_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (skimToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (skimTransition.params.map Param.name)
      (transitionSignature skimTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["to"] [addr] I.calldata = none
  simpa [addr, skimToWord, calldataWord]
    using decodeCalldata_address_none_noncanon (cd := I.calldata) (x := "to") hsz36 hbig hnc

theorem uniswapDecode_skim_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (skimTransition.params.map Param.name)
      (transitionSignature skimTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["to"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_huge (cd := I.calldata) (x := "to") hbig

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

/-! ## Source body slices -/

theorem uniswapSkimLockEnterPrefix (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩) :
    ExecBlock config { contract := contract, locals := skimStore I } evm lockEnter
      (.ok { contract := contract, locals := skimStore I } (uniswapLockEnteredState evm)) := by
  exact uniswapLockEnterPrefix evm (skimStore I) hwv (by simp [skimStore]) hunlocked

theorem uniswapSkimLockExitSuffix (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock config { contract := contract, locals := skimStore I } evm lockExit
      (.ok { contract := contract, locals := skimStore I } (uniswapLockExitedState evm)) := by
  exact uniswapLockExitSuffix evm (skimStore I) (by simp [skimStore])

abbrev skimBalanceCallsBody : List Stmt :=
  pairBalanceOfThisStmts "balance0" "balance1"

abbrev skimToken0GuardTrue (evm : EVM.State) (I : ExecutionEnv) : Prop :=
  evalExpr? config { contract := contract, locals := skimStore I } (uniswapLockEnteredState evm)
    (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true)

abbrev skimToken1GuardTrue (evm0 : EVM.State) (I : ExecutionEnv) (balance0 : Value) : Prop :=
  evalExpr? config { contract := contract, locals := (skimStore I).insert "balance0" balance0 }
    evm0 (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true)

theorem uniswapSkimBalanceOfCallsPrefix (evm evm0 evm1 : EVM.State) (I : ExecutionEnv)
    {out0 out1 : ByteArray} {balance0 balance1 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : skimToken1GuardTrue evm0 I balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some balance1) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++ skimBalanceCallsBody)
      (.ok (uniswapBalanceOfFrame (skimStore I) balance0 balance1) evm1) := by
  have hlock := uniswapSkimLockEnterPrefix evm I hwv hunlocked
  have hcalls := uniswapCheckedTokenBalanceOfThisCallsPrefix
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (evm1 := evm1) (locals := skimStore I)
    (balance0 := balance0) (balance1 := balance1)
    hguard0 hguard1 (by simp [skimStore]) (by simp [skimStore]) hcall0 hdec0 hcall1 hdec1
  simpa [skimBalanceCallsBody] using execBlock_append hlock hcalls

theorem uniswapSkimBalanceOfFirstCallFailure (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (false, evm0, out0)) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++ skimBalanceCallsBody)
      .reverted := by
  have hlock := uniswapSkimLockEnterPrefix evm I hwv hunlocked
  have hfail := uniswapCheckedTokenBalanceOfThisFirstCallFailure
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (locals := skimStore I)
    hguard0 (by simp [skimStore]) hcall0
  simpa [skimBalanceCallsBody] using execBlock_append hlock hfail

theorem uniswapSkimBalanceOfFirstCallDecodeRevert (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = none) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++ skimBalanceCallsBody)
      .reverted := by
  have hlock := uniswapSkimLockEnterPrefix evm I hwv hunlocked
  have hfail := uniswapCheckedTokenBalanceOfThisFirstCallDecodeRevert
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (locals := skimStore I)
    hguard0 (by simp [skimStore]) hcall0 hdec0
  simpa [skimBalanceCallsBody] using execBlock_append hlock hfail

theorem uniswapSkimBalanceOfSecondCallFailure (evm evm0 evm1 : EVM.State) (I : ExecutionEnv)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : skimToken1GuardTrue evm0 I balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1)) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++ skimBalanceCallsBody)
      .reverted := by
  have hlock := uniswapSkimLockEnterPrefix evm I hwv hunlocked
  have hfail := uniswapCheckedTokenBalanceOfThisSecondCallFailure
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (evm1 := evm1)
    (locals := skimStore I) (balance0 := balance0)
    hguard0 hguard1 (by simp [skimStore]) (by simp [skimStore]) hcall0 hdec0 hcall1
  simpa [skimBalanceCallsBody] using execBlock_append hlock hfail

theorem uniswapSkimBalanceOfSecondCallDecodeRevert (evm evm0 evm1 : EVM.State)
    (I : ExecutionEnv) {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : skimToken1GuardTrue evm0 I balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++ skimBalanceCallsBody)
      .reverted := by
  have hlock := uniswapSkimLockEnterPrefix evm I hwv hunlocked
  have hfail := uniswapCheckedTokenBalanceOfThisSecondCallDecodeRevert
    (evm := uniswapLockEnteredState evm) (evm0 := evm0) (evm1 := evm1)
    (locals := skimStore I) (balance0 := balance0)
    hguard0 hguard1 (by simp [skimStore]) (by simp [skimStore]) hcall0 hdec0 hcall1 hdec1
  simpa [skimBalanceCallsBody] using execBlock_append hlock hfail

theorem evalExpr_skim_excess0 (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256)
    (henough : (uniswapReserve0Word evm).toNat ≤ balance0.toNat) :
    evalExpr? config { contract := contract, locals := skimBalanceStore I balance0 balance1 } evm
      (.binary .sub (.var "balance0") (.storage reserve0Ref)) =
        .ok (skimExcess0Value evm balance0) := by
  have hsub :
      Int.ofNat balance0.toNat - Int.ofNat (uniswapReserve0Word evm).toNat =
        Int.ofNat (balance0.toNat - (uniswapReserve0Word evm).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat :
      (skimExcess0Word evm balance0).toNat =
        balance0.toNat - (uniswapReserve0Word evm).toNat := by
    unfold skimExcess0Word
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) balance0.val.isLt)
  have hreserve := evalExpr_uniswap_reserve0 evm (skimBalanceStore I balance0 balance1)
    (by simp [skimBalanceStore, uniswapBalanceOfStore, skimStore])
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, hreserve]
  rw [skimBalanceStore_balance0]
  simpa [skimBalanceValue, evalBinaryOp?, skimExcess0Value, htoNat] using hsub

theorem evalExpr_skim_excess1 (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256)
    (henough : (uniswapReserve1Word evm).toNat ≤ balance1.toNat) :
    evalExpr? config { contract := contract, locals := skimExcess0Store evm I balance0 balance1 }
      evm (.binary .sub (.var "balance1") (.storage reserve1Ref)) =
        .ok (skimExcess1Value evm balance1) := by
  have hsub :
      Int.ofNat balance1.toNat - Int.ofNat (uniswapReserve1Word evm).toNat =
        Int.ofNat (balance1.toNat - (uniswapReserve1Word evm).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat :
      (skimExcess1Word evm balance1).toNat =
        balance1.toNat - (uniswapReserve1Word evm).toNat := by
    unfold skimExcess1Word
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) balance1.val.isLt)
  have hreserve := evalExpr_uniswap_reserve1 evm (skimExcess0Store evm I balance0 balance1)
    (by simp [skimExcess0Store, skimBalanceStore, uniswapBalanceOfStore, skimStore])
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, hreserve]
  rw [skimExcess0Store_balance1]
  simpa [skimBalanceValue, evalBinaryOp?, skimExcess1Value, htoNat] using hsub

abbrev skimExcessPrefixBody : List Stmt :=
  [ .letDecl "excess0" (some uint256)
      (.binary .sub (.var "balance0") (.storage reserve0Ref)),
    .letDecl "excess1" (some uint256)
      (.binary .sub (.var "balance1") (.storage reserve1Ref)) ]

abbrev skimAfterBalanceBody : List Stmt :=
  skimExcessPrefixBody ++
    safeTransferStmts (.storage token0Ref) (.var "to") (.var "excess0") "ok0" "_ret0" ++
    safeTransferStmts (.storage token1Ref) (.var "to") (.var "excess1") "ok1" "_ret1" ++
    lockExit

abbrev skimAfterLockBody : List Stmt :=
  skimBalanceCallsBody ++ skimAfterBalanceBody

theorem uniswapSkimNonpayableSource (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := skimStore I } evm skimTransition.body
      .reverted := by
  have hlock := uniswapLockEnterNonpayableRevert evm (skimStore I) hwv
  simpa [skimTransition, skimAfterLockBody, skimAfterBalanceBody, skimBalanceCallsBody,
    skimExcessPrefixBody, List.append_assoc] using
    (execBlock_append_term (s2 := skimAfterLockBody) hlock (by intro f e h; cases h))

theorem uniswapSkimLockedSource (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩) :
    ExecBlock config { contract := contract, locals := skimStore I } evm skimTransition.body
      .reverted := by
  have hlock := uniswapLockEnterLockedRevert evm (skimStore I) hwv (by simp [skimStore]) hlocked
  simpa [skimTransition, skimAfterLockBody, skimAfterBalanceBody, skimBalanceCallsBody,
    skimExcessPrefixBody, List.append_assoc] using
    (execBlock_append_term (s2 := skimAfterLockBody) hlock (by intro f e h; cases h))

theorem uniswapSkimFirstCallFailureSource (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (false, evm0, out0)) :
    ExecBlock config { contract := contract, locals := skimStore I } evm skimTransition.body
      .reverted := by
  have hprefix := uniswapSkimBalanceOfFirstCallFailure evm evm0 I hwv hunlocked hguard0 hcall0
  simpa [skimTransition, skimBalanceCallsBody, skimAfterBalanceBody, skimExcessPrefixBody,
    List.append_assoc] using
    (execBlock_append_term (s2 := skimAfterBalanceBody) hprefix (by intro f e h; cases h))

theorem uniswapSkimFirstCallDecodeRevertSource (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = none) :
    ExecBlock config { contract := contract, locals := skimStore I } evm skimTransition.body
      .reverted := by
  have hprefix :=
    uniswapSkimBalanceOfFirstCallDecodeRevert evm evm0 I hwv hunlocked hguard0 hcall0 hdec0
  simpa [skimTransition, skimBalanceCallsBody, skimAfterBalanceBody, skimExcessPrefixBody,
    List.append_assoc] using
    (execBlock_append_term (s2 := skimAfterBalanceBody) hprefix (by intro f e h; cases h))

theorem uniswapSkimSecondCallFailureSource (evm evm0 evm1 : EVM.State) (I : ExecutionEnv)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : skimToken1GuardTrue evm0 I balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1)) :
    ExecBlock config { contract := contract, locals := skimStore I } evm skimTransition.body
      .reverted := by
  have hprefix :=
    uniswapSkimBalanceOfSecondCallFailure evm evm0 evm1 I hwv hunlocked
      hguard0 hcall0 hdec0 hguard1 hcall1
  simpa [skimTransition, skimBalanceCallsBody, skimAfterBalanceBody, skimExcessPrefixBody,
    List.append_assoc] using
    (execBlock_append_term (s2 := skimAfterBalanceBody) hprefix (by intro f e h; cases h))

theorem uniswapSkimSecondCallDecodeRevertSource (evm evm0 evm1 : EVM.State)
    (I : ExecutionEnv) {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : skimToken1GuardTrue evm0 I balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecBlock config { contract := contract, locals := skimStore I } evm skimTransition.body
      .reverted := by
  have hprefix := uniswapSkimBalanceOfSecondCallDecodeRevert
    evm evm0 evm1 I hwv hunlocked hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
  simpa [skimTransition, skimBalanceCallsBody, skimAfterBalanceBody, skimExcessPrefixBody,
    List.append_assoc] using
    (execBlock_append_term (s2 := skimAfterBalanceBody) hprefix (by intro f e h; cases h))

theorem uniswapSkimExcessPrefix (evm evm0 evm1 : EVM.State) (I : ExecutionEnv)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (skimBalanceValue balance0))
    (hguard1 : skimToken1GuardTrue evm0 I (skimBalanceValue balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some (skimBalanceValue balance1))
    (henough0 : (uniswapReserve0Word evm1).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word evm1).toNat ≤ balance1.toNat) :
    ExecBlock config { contract := contract, locals := skimStore I } evm
      (lockEnter ++ skimBalanceCallsBody ++ skimExcessPrefixBody)
      (.ok { contract := contract, locals := skimExcessStore evm1 I balance0 balance1 } evm1) := by
  have hbalances := uniswapSkimBalanceOfCallsPrefix
    (evm := evm) (evm0 := evm0) (evm1 := evm1) (I := I)
    (balance0 := skimBalanceValue balance0) (balance1 := skimBalanceValue balance1)
    hwv hunlocked hguard0 hcall0 hdec0 hguard1 hcall1 hdec1
  have hexcess :
      ExecBlock config
        { contract := contract, locals := skimBalanceStore I balance0 balance1 } evm1
        skimExcessPrefixBody
        (.ok { contract := contract, locals := skimExcessStore evm1 I balance0 balance1 } evm1) := by
    change ExecBlock config
      { contract := contract, locals := skimBalanceStore I balance0 balance1 } evm1
      [ .letDecl "excess0" (some uint256)
          (.binary .sub (.var "balance0") (.storage reserve0Ref)),
        .letDecl "excess1" (some uint256)
          (.binary .sub (.var "balance1") (.storage reserve1Ref)) ]
      (.ok { contract := contract, locals := skimExcessStore evm1 I balance0 balance1 } evm1)
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_skim_excess0 evm1 I balance0 balance1 henough0)) ?_
    exact ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_skim_excess1 evm1 I balance0 balance1 henough1))
      ExecBlock.nil
  simpa [skimBalanceStore] using execBlock_append hbalances hexcess

theorem uniswapSkimSafeTransfer0Success (evm evm' : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) {out : ByteArray}
    (hcall : callViaEVM evm (EVM.address (uniswapAddressAtSlot evm ⟨6⟩)) 0
      ByteArray.empty (true, evm', out)) :
    ExecBlock config { contract := contract, locals := skimExcessStore evm I balance0 balance1 } evm
      (safeTransferStmts (.storage token0Ref) (.var "to") (.var "excess0") "ok0" "_ret0")
      (.ok { contract := contract, locals := skimSafeTransfer0Store evm I balance0 balance1 true out }
        evm') := by
  change ExecBlock config
    { contract := contract, locals := skimExcessStore evm I balance0 balance1 } evm
    [ .lowLevelCall (.storage token0Ref) (.intLit 0) (.bytesLit ByteArray.empty) "ok0" "_ret0",
      .require (.var "ok0") ]
    (.ok { contract := contract, locals := skimSafeTransfer0Store evm I balance0 balance1 true out }
      evm')
  refine ExecBlock.consNormal
    (solm' := { contract := contract, locals := skimSafeTransfer0Store evm I balance0 balance1 true out })
    (evm' := evm') ?_ ?_
  · simpa [skimSafeTransfer0Store] using ExecStmt.lowLevelCallSuccess
      (evalExpr_uniswap_storage_address
        (ref := token0Ref) (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
        evm (skimExcessStore evm I balance0 balance1)
        (by simp [skimExcessStore, skimExcess0Store, skimBalanceStore, uniswapBalanceOfStore,
          skimStore, token0Ref])
        (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
        (by decide) (by rfl))
      (by simp [evalExpr?, pure])
      (by simp [evalExpr?, pure])
      hcall
  · exact ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_skim_safeTransfer0_ok evm evm' I balance0 balance1 true out))
      ExecBlock.nil

theorem uniswapSkimSafeTransfer0Failure (evm evm' : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) {out : ByteArray}
    (hcall : callViaEVM evm (EVM.address (uniswapAddressAtSlot evm ⟨6⟩)) 0
      ByteArray.empty (false, evm', out)) :
    ExecBlock config { contract := contract, locals := skimExcessStore evm I balance0 balance1 } evm
      (safeTransferStmts (.storage token0Ref) (.var "to") (.var "excess0") "ok0" "_ret0")
      .reverted := by
  change ExecBlock config
    { contract := contract, locals := skimExcessStore evm I balance0 balance1 } evm
    [ .lowLevelCall (.storage token0Ref) (.intLit 0) (.bytesLit ByteArray.empty) "ok0" "_ret0",
      .require (.var "ok0") ]
    .reverted
  refine ExecBlock.consNormal
    (solm' := { contract := contract, locals := skimSafeTransfer0Store evm I balance0 balance1 false out })
    (evm' := evm') ?_ ?_
  · simpa [skimSafeTransfer0Store] using ExecStmt.lowLevelCallFailure
      (evalExpr_uniswap_storage_address
        (ref := token0Ref) (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
        evm (skimExcessStore evm I balance0 balance1)
        (by simp [skimExcessStore, skimExcess0Store, skimBalanceStore, uniswapBalanceOfStore,
          skimStore, token0Ref])
        (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
        (by decide) (by rfl))
      (by simp [evalExpr?, pure])
      (by simp [evalExpr?, pure])
      hcall
  · exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_skim_safeTransfer0_ok evm evm' I balance0 balance1 false out))

theorem uniswapSkimSafeTransfer1Success (storeEvm evm evm' : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) {out0 out1 : ByteArray}
    (hcall : callViaEVM evm (EVM.address (uniswapAddressAtSlot evm ⟨7⟩)) 0
      ByteArray.empty (true, evm', out1)) :
    ExecBlock config
      { contract := contract, locals := skimSafeTransfer0Store storeEvm I balance0 balance1 true out0 }
      evm
      (safeTransferStmts (.storage token1Ref) (.var "to") (.var "excess1") "ok1" "_ret1")
      (.ok
        { contract := contract,
          locals := skimSafeTransfer1Store storeEvm I balance0 balance1 out0 true out1 }
        evm') := by
  change ExecBlock config
    { contract := contract, locals := skimSafeTransfer0Store storeEvm I balance0 balance1 true out0 }
    evm
    [ .lowLevelCall (.storage token1Ref) (.intLit 0) (.bytesLit ByteArray.empty) "ok1" "_ret1",
      .require (.var "ok1") ]
    (.ok
      { contract := contract,
        locals := skimSafeTransfer1Store storeEvm I balance0 balance1 out0 true out1 }
      evm')
  simpa [skimSafeTransfer1Store] using
    uniswapLowLevelCallRequireSuccess
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := skimSafeTransfer0Store storeEvm I balance0 balance1 true out0)
      (receiver := .storage token1Ref) (eth := .intLit 0)
      (cdata := .bytesLit ByteArray.empty) (okVar := "ok1") (dataVar := "_ret1")
      (target := uniswapAddressAtSlot evm ⟨7⟩) (sendVal := 0)
      (calldata := ByteArray.empty) (out := out1)
      (evalExpr_uniswap_storage_address
        (ref := token1Ref) (er := { base := "token1", steps := [] }) (slot := ⟨7⟩)
        evm (skimSafeTransfer0Store storeEvm I balance0 balance1 true out0)
        (by simp [skimSafeTransfer0Store, skimExcessStore, skimExcess0Store,
          skimBalanceStore, uniswapBalanceOfStore, skimStore, token1Ref])
        (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
        (by decide) (by rfl))
      (by simp [evalExpr?, pure])
      (by simp [evalExpr?, pure])
      hcall (by decide)

theorem uniswapSkimSafeTransfer1Failure (storeEvm evm evm' : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) {out0 out1 : ByteArray}
    (hcall : callViaEVM evm (EVM.address (uniswapAddressAtSlot evm ⟨7⟩)) 0
      ByteArray.empty (false, evm', out1)) :
    ExecBlock config
      { contract := contract, locals := skimSafeTransfer0Store storeEvm I balance0 balance1 true out0 }
      evm
      (safeTransferStmts (.storage token1Ref) (.var "to") (.var "excess1") "ok1" "_ret1")
      .reverted := by
  change ExecBlock config
    { contract := contract, locals := skimSafeTransfer0Store storeEvm I balance0 balance1 true out0 }
    evm
    [ .lowLevelCall (.storage token1Ref) (.intLit 0) (.bytesLit ByteArray.empty) "ok1" "_ret1",
      .require (.var "ok1") ]
    .reverted
  simpa [skimSafeTransfer1Store] using
    uniswapLowLevelCallRequireFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := skimSafeTransfer0Store storeEvm I balance0 balance1 true out0)
      (receiver := .storage token1Ref) (eth := .intLit 0)
      (cdata := .bytesLit ByteArray.empty) (okVar := "ok1") (dataVar := "_ret1")
      (target := uniswapAddressAtSlot evm ⟨7⟩) (sendVal := 0)
      (calldata := ByteArray.empty) (out := out1)
      (evalExpr_uniswap_storage_address
        (ref := token1Ref) (er := { base := "token1", steps := [] }) (slot := ⟨7⟩)
        evm (skimSafeTransfer0Store storeEvm I balance0 balance1 true out0)
        (by simp [skimSafeTransfer0Store, skimExcessStore, skimExcess0Store,
          skimBalanceStore, uniswapBalanceOfStore, skimStore, token1Ref])
        (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
        (by decide) (by rfl))
      (by simp [evalExpr?, pure])
      (by simp [evalExpr?, pure])
      hcall (by decide)

theorem uniswapSkimFirstSafeTransferFailureSource (evm evm0 evm1 evm2 : EVM.State)
    (I : ExecutionEnv) {out0 out1 out2 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (skimBalanceValue balance0))
    (hguard1 : skimToken1GuardTrue evm0 I (skimBalanceValue balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some (skimBalanceValue balance1))
    (henough0 : (uniswapReserve0Word evm1).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word evm1).toNat ≤ balance1.toNat)
    (htransfer0 : callViaEVM evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨6⟩)) 0
      ByteArray.empty (false, evm2, out2)) :
    ExecBlock config { contract := contract, locals := skimStore I } evm skimTransition.body
      .reverted := by
  have hprefix := uniswapSkimExcessPrefix
    (evm := evm) (evm0 := evm0) (evm1 := evm1) (I := I)
    (balance0 := balance0) (balance1 := balance1)
    hwv hunlocked hguard0 hcall0 hdec0 hguard1 hcall1 hdec1 henough0 henough1
  have hfail := uniswapSkimSafeTransfer0Failure
    (evm := evm1) (evm' := evm2) (I := I) balance0 balance1 htransfer0
  have hprefixFail := execBlock_append hprefix hfail
  simpa [skimTransition, skimBalanceCallsBody, skimAfterBalanceBody, skimExcessPrefixBody,
    List.append_assoc] using
    (execBlock_append_term
      (s2 := safeTransferStmts (.storage token1Ref) (.var "to") (.var "excess1") "ok1" "_ret1" ++
        lockExit)
      hprefixFail (by intro f e h; cases h))

theorem uniswapSkimSecondSafeTransferFailureSource (evm evm0 evm1 evm2 evm3 : EVM.State)
    (I : ExecutionEnv) {out0 out1 out2 out3 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (skimBalanceValue balance0))
    (hguard1 : skimToken1GuardTrue evm0 I (skimBalanceValue balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some (skimBalanceValue balance1))
    (henough0 : (uniswapReserve0Word evm1).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word evm1).toNat ≤ balance1.toNat)
    (htransfer0 : callViaEVM evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨6⟩)) 0
      ByteArray.empty (true, evm2, out2))
    (htransfer1 : callViaEVM evm2 (EVM.address (uniswapAddressAtSlot evm2 ⟨7⟩)) 0
      ByteArray.empty (false, evm3, out3)) :
    ExecBlock config { contract := contract, locals := skimStore I } evm skimTransition.body
      .reverted := by
  have hprefix := uniswapSkimExcessPrefix
    (evm := evm) (evm0 := evm0) (evm1 := evm1) (I := I)
    (balance0 := balance0) (balance1 := balance1)
    hwv hunlocked hguard0 hcall0 hdec0 hguard1 hcall1 hdec1 henough0 henough1
  have hfirst := uniswapSkimSafeTransfer0Success
    (evm := evm1) (evm' := evm2) (I := I) balance0 balance1 htransfer0
  have hsecond := uniswapSkimSafeTransfer1Failure
    (storeEvm := evm1) (evm := evm2) (evm' := evm3) (I := I)
    (out0 := out2) (out1 := out3)
    balance0 balance1 htransfer1
  have hthroughFirst := execBlock_append hprefix hfirst
  have hthroughSecond := execBlock_append hthroughFirst hsecond
  simpa [skimTransition, skimBalanceCallsBody, skimAfterBalanceBody, skimExcessPrefixBody,
    List.append_assoc] using
    (execBlock_append_term (s2 := lockExit) hthroughSecond (by intro f e h; cases h))

theorem uniswapSkimSuccessSource (evm evm0 evm1 evm2 evm3 : EVM.State)
    (I : ExecutionEnv) {out0 out1 out2 out3 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (skimBalanceValue balance0))
    (hguard1 : skimToken1GuardTrue evm0 I (skimBalanceValue balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some (skimBalanceValue balance1))
    (henough0 : (uniswapReserve0Word evm1).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word evm1).toNat ≤ balance1.toNat)
    (htransfer0 : callViaEVM evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨6⟩)) 0
      ByteArray.empty (true, evm2, out2))
    (htransfer1 : callViaEVM evm2 (EVM.address (uniswapAddressAtSlot evm2 ⟨7⟩)) 0
      ByteArray.empty (true, evm3, out3)) :
    ExecBlock config { contract := contract, locals := skimStore I } evm skimTransition.body
      (.ok
        { contract := contract,
          locals := skimSafeTransfer1Store evm1 I balance0 balance1 out2 true out3 }
        (uniswapLockExitedState evm3)) := by
  have hprefix := uniswapSkimExcessPrefix
    (evm := evm) (evm0 := evm0) (evm1 := evm1) (I := I)
    (balance0 := balance0) (balance1 := balance1)
    hwv hunlocked hguard0 hcall0 hdec0 hguard1 hcall1 hdec1 henough0 henough1
  have hfirst := uniswapSkimSafeTransfer0Success
    (evm := evm1) (evm' := evm2) (I := I) balance0 balance1 htransfer0
  have hsecond := uniswapSkimSafeTransfer1Success
    (storeEvm := evm1) (evm := evm2) (evm' := evm3) (I := I)
    (out0 := out2) (out1 := out3)
    balance0 balance1 htransfer1
  have hlock :
      ExecBlock config
        { contract := contract,
          locals := skimSafeTransfer1Store evm1 I balance0 balance1 out2 true out3 } evm3
        lockExit
        (.ok
          { contract := contract,
            locals := skimSafeTransfer1Store evm1 I balance0 balance1 out2 true out3 }
          (uniswapLockExitedState evm3)) := by
    exact uniswapLockExitSuffix evm3
      (skimSafeTransfer1Store evm1 I balance0 balance1 out2 true out3)
      (by simp [skimSafeTransfer1Store, skimSafeTransfer0Store, skimExcessStore,
        skimExcess0Store, skimBalanceStore, uniswapBalanceOfStore, skimStore,
        uniswapLowLevelCallRequireStore])
  have hthroughFirst := execBlock_append hprefix hfirst
  have hthroughSecond := execBlock_append hthroughFirst hsecond
  have hall := execBlock_append hthroughSecond hlock
  simpa [skimTransition, skimBalanceCallsBody, skimAfterBalanceBody, skimExcessPrefixBody,
    List.append_assoc] using hall

/-! ## `skim(address)` source-body wrappers -/

theorem uniswapSkimBodyReverts_nonpayable (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (uniswapSkimNonpayableSource evm I hwv)

theorem uniswapSkimBodyReverts_locked (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (uniswapSkimLockedSource evm I hwv hlocked)

theorem uniswapSkimBodyReverts_firstCallFailure (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (false, evm0, out0)) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSkimFirstCallFailureSource evm evm0 I hwv hunlocked hguard0 hcall0)

theorem uniswapSkimBodyReverts_firstCallDecode (evm evm0 : EVM.State) (I : ExecutionEnv)
    {out0 : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = none) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSkimFirstCallDecodeRevertSource evm evm0 I hwv hunlocked hguard0 hcall0 hdec0)

theorem uniswapSkimBodyReverts_secondCallFailure (evm evm0 evm1 : EVM.State)
    (I : ExecutionEnv) {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : skimToken1GuardTrue evm0 I balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1)) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSkimSecondCallFailureSource evm evm0 evm1 I hwv hunlocked
      hguard0 hcall0 hdec0 hguard1 hcall1)

theorem uniswapSkimBodyReverts_secondCallDecode (evm evm0 evm1 : EVM.State)
    (I : ExecutionEnv) {out0 out1 : ByteArray} {balance0 : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hguard1 : skimToken1GuardTrue evm0 I balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSkimSecondCallDecodeRevertSource evm evm0 evm1 I hwv hunlocked hguard0 hcall0 hdec0
      hguard1 hcall1 hdec1)

theorem uniswapSkimBodyReverts_firstSafeTransferFailure
    (evm evm0 evm1 evm2 : EVM.State) (I : ExecutionEnv)
    {out0 out1 out2 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (skimBalanceValue balance0))
    (hguard1 : skimToken1GuardTrue evm0 I (skimBalanceValue balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some (skimBalanceValue balance1))
    (henough0 : (uniswapReserve0Word evm1).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word evm1).toNat ≤ balance1.toNat)
    (htransfer0 : callViaEVM evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨6⟩)) 0
      ByteArray.empty (false, evm2, out2)) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSkimFirstSafeTransferFailureSource evm evm0 evm1 evm2 I hwv hunlocked hguard0
      hcall0 hdec0 hguard1 hcall1 hdec1 henough0 henough1 htransfer0)

theorem uniswapSkimBodyReverts_secondSafeTransferFailure
    (evm evm0 evm1 evm2 evm3 : EVM.State) (I : ExecutionEnv)
    {out0 out1 out2 out3 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (skimBalanceValue balance0))
    (hguard1 : skimToken1GuardTrue evm0 I (skimBalanceValue balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some (skimBalanceValue balance1))
    (henough0 : (uniswapReserve0Word evm1).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word evm1).toNat ≤ balance1.toNat)
    (htransfer0 : callViaEVM evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨6⟩)) 0
      ByteArray.empty (true, evm2, out2))
    (htransfer1 : callViaEVM evm2 (EVM.address (uniswapAddressAtSlot evm2 ⟨7⟩)) 0
      ByteArray.empty (false, evm3, out3)) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert
    (uniswapSkimSecondSafeTransferFailureSource evm evm0 evm1 evm2 evm3 I hwv hunlocked
      hguard0 hcall0 hdec0 hguard1 hcall1 hdec1 henough0 henough1 htransfer0 htransfer1)

theorem uniswapSkimBodyReturns (evm evm0 evm1 evm2 evm3 : EVM.State)
    (I : ExecutionEnv) {out0 out1 out2 out3 : ByteArray} {balance0 balance1 : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 : skimToken0GuardTrue evm I)
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some (skimBalanceValue balance0))
    (hguard1 : skimToken1GuardTrue evm0 I (skimBalanceValue balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some (skimBalanceValue balance1))
    (henough0 : (uniswapReserve0Word evm1).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word evm1).toNat ≤ balance1.toNat)
    (htransfer0 : callViaEVM evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨6⟩)) 0
      ByteArray.empty (true, evm2, out2))
    (htransfer1 : callViaEVM evm2 (EVM.address (uniswapAddressAtSlot evm2 ⟨7⟩)) 0
      ByteArray.empty (true, evm3, out3)) :
    ExecTransitionBody config contract evm (skimStore I) skimTransition.body
      (.returned
        { contract := contract,
          locals := skimSafeTransfer1Store evm1 I balance0 balance1 out2 true out3 }
        (uniswapLockExitedState evm3) none) := by
  exact ExecFuncBody.execBlockOK
    (uniswapSkimSuccessSource evm evm0 evm1 evm2 evm3 I hwv hunlocked hguard0 hcall0 hdec0
      hguard1 hcall1 hdec1 henough0 henough1 htransfer0 htransfer1)

/-! ## `skim(address)` refinement slices -/

theorem uniswapSkimBodyCoreRevert_locked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldata (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hlockedSolm :
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩ := by
    simpa [evmS] using
      (initState_codeOwner_storageLoad_ne_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (slot := ⟨12⟩) (val := ⟨1⟩) hAccounts hlocked)
  have hbody :
      ExecTransitionBody config contract evmS (skimStore I) skimTransition.body .reverted := by
    exact uniswapSkimBodyReverts_locked evmS I
      (by simp only [evmS, initState]; exact hwv)
      hlockedSolm
  exact (uniswapSkimX_locked (g := Sat256.ofUInt256 g)
      hsz36 hsize hcanonTo hlocked hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- Short-calldata decode-failure refinement slice for `skim(address)`.

The non-canonical and huge-calldata branches are intentionally not claimed here: the optimized
bytecode masks address words and uses an unsigned length check, while the current Solm ABI decoder
rejects those cases before execution.
-/
theorem uniswapSkimBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_skim_none_short (I := I) hsz4 hshort
  exact (uniswapSkimX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- Locked-revert `skim(address)` refinement slice, packaged from selector dispatch through the
body core. -/
theorem uniswapSkimBodyRevert_locked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩ rfl hsel
  exact uniswapSkimBodyCoreRevert_locked hcode hsize hwv hsz36 hcanonTo hlocked hdispatch
    (uniswapDecode_skim_ok hsz36 hbig hcanonTo)
    (uniswapReachSkimBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

/-- Short-calldata decode-failure `skim(address)` refinement slice, packaged from selector
dispatch through the body core. -/
theorem uniswapSkimBodyDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩ rfl hsel
  exact uniswapSkimBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hdispatch
    (uniswapReachSkimBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapSkimBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonTo : (skimToWord I).toNat < EVM.addressModulus
      · by_cases hlocked :
          (σ_evm.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠ ⟨1⟩
        · exact uniswapSkimBodyRevert_locked hcode hsize hwv hsel hsz36 hbig hcanonTo
            hlocked hdispatch hAccounts
        · sorry
      · sorry
    · sorry
  · exact uniswapSkimBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

end UniswapV2Pair
