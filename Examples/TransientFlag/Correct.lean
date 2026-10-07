import Examples.TransientFlag.Bytecode
import Examples.TransientFlag.Spec
import Examples.TransientFlag.SpecSyntax
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.EVMWord
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.SolmBody
import Reasoning.Stepping
import Reasoning.Reach
import Solm.Equiv
import Mathlib.Tactic.IntervalCases

/-!
# TransientFlag — correctness

The optimizer-on Cancun runtime of `TransientFlag` refines `flagContract`. `setFlag` is a
`TSTORE` of the calldata word at transient slot 0; `getFlag` is the matching `TLOAD`.
-/

set_option maxRecDepth 1000000

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

/-- The word `TLOAD` of slot 0 pushes for `owner`. -/
def flagWord (σ : AccountMap) (owner : AccountAddress) : UInt256 :=
  σ.get? owner |>.option ⟨0⟩ (fun ac => ac.tstorage.getD ⟨0⟩ ⟨0⟩)

/-- The Solm value of that word. -/
def flagValue (σ : AccountMap) (owner : AccountAddress) : Value :=
  .int (Int.ofNat (flagWord σ owner).toNat)

/-- The `uint256` argument word at calldata offset 4. -/
abbrev flagArg (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev flagArgValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (flagArg I).toNat)

abbrev flagArgStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "v" (flagArgValue I)

/-- Selectors in bytecode dispatch order: `setFlag`, then `getFlag`. -/
def flagSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xd4, 0x0c, 0x79, 0xf0]⟩
  | _ => ⟨#[0xf9, 0x63, 0x39, 0x30]⟩

/-- The first selector arm begins at pc 28. -/
abbrev flagFirstArmPc : UInt256 := ⟨28⟩

/-- Solm state after assigning a whole-slot transient `uint256`. -/
def flagAfterSet (evm : EVM.State) (val : UInt256) : EVM.State :=
  Solm.EVM.swapCodeOwnerMaps
    (Solm.EVM.storageStore (Solm.EVM.swapCodeOwnerMaps evm)
      evm.executionEnv.codeOwner ⟨0⟩ val)

theorem flagLoc_uint256 : TransientFlag.flagLoc = uint256Loc ⟨0⟩ := by
  rfl

theorem swap_executionEnv (evm : EVM.State) :
    (Solm.EVM.swapCodeOwnerMaps evm).executionEnv = evm.executionEnv := by
  simp only [Solm.EVM.swapCodeOwnerMaps, State.lookupAccount, State.setAccount]
  cases evm.accountMap.get? evm.executionEnv.codeOwner <;> simp [Option.option]

theorem swap_codeOwner (evm : EVM.State) :
    (Solm.EVM.swapCodeOwnerMaps evm).executionEnv.codeOwner = evm.executionEnv.codeOwner := by
  rw [swap_executionEnv]

theorem flagAfterSet_executionEnv (evm : EVM.State) (val : UInt256) :
    (flagAfterSet evm val).executionEnv = evm.executionEnv := by
  unfold flagAfterSet
  rw [swap_executionEnv, storageStore_executionEnv, swap_executionEnv]

/-- Reading persistent storage of the swapped code owner is the transient load. -/
theorem storageLoad_swap_eq_flagWord (evm : EVM.State) :
    Solm.EVM.storageLoad (Solm.EVM.swapCodeOwnerMaps evm) evm.executionEnv.codeOwner ⟨0⟩ =
      flagWord evm.accountMap evm.executionEnv.codeOwner := by
  unfold Solm.EVM.storageLoad Solm.EVM.swapCodeOwnerMaps flagWord State.lookupAccount
    Account.lookupStorage
  cases h : evm.accountMap.get? evm.executionEnv.codeOwner with
  | none => simp [-Std.ExtTreeMap.get?_eq_getElem?, h, Option.option]
  | some acc =>
      simp only [h, Option.option, State.setAccount, Std.ExtTreeMap.get?_eq_getElem?,
        Std.ExtTreeMap.getElem?_insert_self]

theorem transientLocLoad_flag (evm : EVM.State) :
    transientLocLoad evm TransientFlag.flagLoc =
      .int (Int.ofNat (flagWord evm.accountMap evm.executionEnv.codeOwner).toNat) := by
  rw [flagLoc_uint256, transientLocLoad, storageLocLoad_uint256, swap_codeOwner,
    storageLoad_swap_eq_flagWord]

theorem transientLocStore_flag (evm : EVM.State) (val : UInt256) :
    transientLocStore evm TransientFlag.flagLoc (.int (↑val.toNat)) =
      some (flagAfterSet evm val) := by
  rw [show (↑val.toNat : Int) = Int.ofNat val.toNat from rfl]
  rw [flagLoc_uint256]
  unfold transientLocStore flagAfterSet
  rw [storageLocStore_uint256, swap_codeOwner]
  rfl

/-- Swapping, storing the word, and swapping back is the `TSTORE` account map. -/
theorem flagAfterSet_accountMap (evm : EVM.State) (val : UInt256) :
    (flagAfterSet evm val).accountMap =
      tstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩ val := by
  cases hσ : evm.accountMap.get? evm.executionEnv.codeOwner with
  | none =>
      simp [-Std.ExtTreeMap.get?_eq_getElem?, flagAfterSet, tstoreAccountMap,
        Solm.EVM.swapCodeOwnerMaps, Solm.EVM.storageStore, State.lookupAccount, hσ, Option.option]
  | some acc =>
      set owner := evm.executionEnv.codeOwner
      simp only [owner] at hσ
      set swapped := { acc with storage := acc.tstorage, tstorage := acc.storage }
      set written := Account.updateStorage swapped ⟨0⟩ val
      set restored := { written with storage := written.tstorage, tstorage := written.storage }
      have hrest : restored = Account.updateTransientStorage acc ⟨0⟩ val := by
        simp only [restored, written, swapped, Account.updateStorage, Account.updateTransientStorage]
        by_cases hv : (val == (default : UInt256)) = true <;> simp [hv]
      have hswap1 : (Solm.EVM.swapCodeOwnerMaps evm).accountMap =
          evm.accountMap.insert owner swapped := by
        simp only [Solm.EVM.swapCodeOwnerMaps, State.lookupAccount, State.setAccount, hσ,
          Option.option, swapped, owner]
      have hstore :
          (Solm.EVM.storageStore (Solm.EVM.swapCodeOwnerMaps evm) owner ⟨0⟩ val).accountMap =
            (evm.accountMap.insert owner swapped).insert owner written := by
        have hs : (Solm.EVM.swapCodeOwnerMaps evm).accountMap.get? owner = some swapped := by
          rw [hswap1]
          simp [Std.ExtTreeMap.get?_eq_getElem?]
        simp only [Solm.EVM.storageStore, State.lookupAccount, hs, Option.option, State.setAccount]
        simp only [Account.updateStorage, written, hswap1, owner]
      have hswap2 : (flagAfterSet evm val).accountMap =
          ((evm.accountMap.insert owner swapped).insert owner written).insert owner restored := by
        have hs2 :
            (Solm.EVM.storageStore (Solm.EVM.swapCodeOwnerMaps evm) owner ⟨0⟩ val).accountMap.get?
              owner = some written := by
          rw [hstore]
          simp [Std.ExtTreeMap.get?_eq_getElem?]
        have hco :
            (Solm.EVM.storageStore (Solm.EVM.swapCodeOwnerMaps evm) owner ⟨0⟩ val).executionEnv.codeOwner
              = owner := by
          rw [storageStore_executionEnv, swap_codeOwner]
        unfold flagAfterSet
        rw [Solm.EVM.swapCodeOwnerMaps, State.lookupAccount, hco, hs2]
        simp only [Option.option, State.setAccount, hstore, restored, owner]
      rw [hswap2, extTreeMap_insert_insert_self, extTreeMap_insert_insert_self, hrest]
      simp only [tstoreAccountMap, hσ, Option.option, owner, Account.updateTransientStorage]

/-! ## Dispatcher -/

set_option maxRecDepth 1000000 in
theorem flagArmsWellFormed :
    ∀ j, j ≤ 1 → armWellFormed flagBytecode (nthArmPc flagBytecode flagFirstArmPc j) := by
  intro j hj
  interval_cases j
  all_goals exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem setFlagEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨3557587440⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if ((⟨#[0xd4, 0x0c, 0x79, 0xf0]⟩ : ByteArray) == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0xd4 0x0c 0x79 0xf0 ⟨3557587440⟩ (by decide)

theorem getFlagEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨4184029488⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if ((⟨#[0xf9, 0x63, 0x39, 0x30]⟩ : ByteArray) == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0xf9 0x63 0x39 0x30 ⟨4184029488⟩ (by decide)

theorem flagArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 2) :
    UInt256.eq (armSelNat flagBytecode (nthArmPc flagBytecode flagFirstArmPc j))
        (solcSelectorWord I)
      = if (flagSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j
  · exact setFlagEvmSelector hsz
  · exact getFlagEvmSelector hsz

theorem flagMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 2) (hsz : 4 ≤ I.calldata.size)
    (hsel : (flagSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq (armSelNat flagBytecode (nthArmPc flagBytecode flagFirstArmPc j))
        (solcSelectorWord I) = ⟨0⟩)
    ∧ UInt256.eq (armSelNat flagBytecode (nthArmPc flagBytecode flagFirstArmPc i))
        (solcSelectorWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = flagSelBytes i := (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [flagArmEq I hsz j (by omega), hci]
    interval_cases i
    · omega
    · interval_cases j
      decide
  · rw [flagArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem flagReachBody {σ σ₀ A I} {g : Sat256} (i : ℕ) (hi1 : i ≤ 1)
    (bodyPC : UInt256)
    (hcode : I.code = flagBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat flagBytecode (nthArmPc flagBytecode flagFirstArmPc j))
        (solcSelectorWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat flagBytecode (nthArmPc flagBytecode flagFirstArmPc i))
        (solcSelectorWord I) ≠ ⟨0⟩)
    (hjd : (D_J flagBytecode 0).contains bodyPC = true)
    (hbody : armTgt flagBytecode (nthArmPc flagBytecode flagFirstArmPc i) = bodyPC) :
    ∃ k C, RD flagBytecode I g (initState σ σ₀ g A I) bodyPC
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  exact solcDispatchReachBody
    (firstArmPc := flagFirstArmPc) (bodyPC := bodyPC) (i := i)
    hcode hwv hsz hsize (by solc_dispatch_prefix) (by jump_dest)
    (fun j hj => flagArmsWellFormed j (le_trans hj hi1)) heq0 htake hjd hbody

theorem flagDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg TransientFlag.flagContract cd = none := by
  rw [dispatchMsg_eq_dispatchList TransientFlag.flagContract cd (by rfl)]
  change dispatchList [TransientFlag.setFlagTransition, TransientFlag.getFlagTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl
    · rw [selectorOf, setFlagSelectorBytes]; rfl
    · rw [selectorOf, getFlagSelectorBytes]; rfl) h

theorem flagDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 2 → (flagSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg TransientFlag.flagContract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [TransientFlag.flagContract] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, setFlagSelectorBytes]; simpa [flagSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, getFlagSelectorBytes]; simpa [flagSelBytes] using hnm 1 (by omega)

theorem flagDispatch_set {cd : ByteArray}
    (hsel : ((⟨#[0xd4, 0x0c, 0x79, 0xf0]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg TransientFlag.flagContract cd = some TransientFlag.setFlagTransition := by
  apply dispatchMsg_eq_some_of_split (pre := []) (post := [TransientFlag.getFlagTransition])
  · rfl
  · intro t ht; cases ht
  · rw [selectorOf, setFlagSelectorBytes]; exact hsel

theorem flagDispatch_get {cd : ByteArray}
    (hf : ((⟨#[0xd4, 0x0c, 0x79, 0xf0]⟩ : ByteArray) == cd.extract 0 4) = false)
    (hg : ((⟨#[0xf9, 0x63, 0x39, 0x30]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg TransientFlag.flagContract cd = some TransientFlag.getFlagTransition := by
  apply dispatchMsg_eq_some_of_split
    (pre := [TransientFlag.setFlagTransition]) (post := [])
  · rfl
  · intro t ht
    simp at ht
    rcases ht with rfl
    rw [selectorOf, setFlagSelectorBytes]; exact hf
  · rw [selectorOf, getFlagSelectorBytes]; exact hg

theorem flagBodyReverts_nonPayable (t : TransitionDecl)
    (ht : t ∈ TransientFlag.flagContract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody flagConfig TransientFlag.flagContract evm locals t.body .reverted := by
  simp [TransientFlag.flagContract] at ht
  rcases ht with rfl | rfl <;> exact bodyReverts_nonPayable h

/-! ## Bytecode traces -/

theorem flagX_callvalue_ne {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flagBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev flagBytecode g (initState σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := solcGuardTgt flagBytecode) (opC := solcGuardTgtOp flagBytecode)
    (wC := solcGuardTgtWidth flagBytecode)
    (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    hwv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem flagX_short {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flagBytecode) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    RDrev flagBytecode g (initState σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt flagBytecode) (opC := solcGuardTgtOp flagBytecode)
    (wC := solcGuardTgtWidth flagBytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  exact solcCalldataShortRevert
    (bodyPc := solcDispatchBodyPc flagBytecode)
    (rtgt := solcCalldataRevertTgt flagBytecode)
    (opR := solcCalldataRevertTgtOp flagBytecode)
    (wR := solcCalldataRevertTgtWidth flagBytecode)
    h1 hsz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by jump_dest) (by decide) (by decide) (by decide)

theorem flagX_noMatch {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flagBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 2 → (flagSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev flagBytecode g (initState σ σ₀ g A I) := by
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat flagBytecode (nthArmPc flagBytecode flagFirstArmPc j))
        (solcSelectorWord I) = ⟨0⟩ := by
    intro j hj
    rw [flagArmEq I hsz j hj, hnm j hj]
    rfl
  have h0 := solcGuardPrologueRD (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt flagBytecode) (opC := solcGuardTgtOp flagBytecode)
    (wC := solcGuardTgtWidth flagBytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  obtain ⟨k2, C2, h2⟩ := solcCalldataOk
    (bodyPc := solcDispatchBodyPc flagBytecode)
    (selLoadTgt := solcCalldataRevertTgt flagBytecode)
    (opR := solcCalldataRevertTgtOp flagBytecode)
    (wR := solcCalldataRevertTgtWidth flagBytecode)
    h1 hsz hsize (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k3, C3, h3⟩ := solcSelectorLoad h2 (by decide) (by decide) (by decide) (by decide) (by simp)
  have h4 : RD flagBytecode I g (initState σ σ₀ g A I) flagFirstArmPc
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k3 C3 := by
    simpa [flagFirstArmPc, solcSelectorWord, solcFirstArmPcFromPrefix, solcSelectorLoadPc,
      solcCalldataJumpiPc, solcCalldataRevertPushPc, solcDispatchBodyPc] using h3
  have h5 := h4
    |>.selectorArmNotTakenAuto (flagArmsWellFormed 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flagArmsWellFormed 1 (by omega)) (heq0 1 (by omega)) (by simp)
  have h48 : ∃ k C, RD flagBytecode I g (initState σ σ₀ g A I) ⟨48⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
    refine ⟨k3 + 5 + 5, C3 + 22 + 22, ?_⟩
    simpa [flagFirstArmPc, nthArmPc, selArmNextPc, armTgtWidth, selArmJumpiPc,
      selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h5
  obtain ⟨_, _, h48rd⟩ := h48
  exact evm_run h48rd with [
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-- `setFlag` from its body entry when the argument word is present. -/
theorem flagX_set_success {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flagBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hmatch : (flagSelBytes 0 == I.calldata.extract 0 4) = true) :
    RDret flagBytecode g (initState σ σ₀ g A I)
      (tstoreAccountMap I.codeOwner σ ⟨0⟩ (flagArg I)) ByteArray.empty := by
  obtain ⟨heq0, htake⟩ := flagMatches 0 (by omega) (by omega : 4 ≤ I.calldata.size) hmatch
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, hreach⟩ := flagReachBody 0 (by omega) ⟨52⟩ hcode hwv hsz4 hsize heq0 htake
    (by jump_dest) (by decide)
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hbig hsize
  exact evm_run hreach with [
    jumpdest, push1 ⟨67⟩, push1 ⟨63⟩, calldatasize, push1 ⟨4⟩, push1 ⟨97⟩,
    jump (by jump_dest),
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push1 ⟨112⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, pop, calldataload, swap2, swap1, pop, jump (by jump_dest),
    jumpdest, push1 ⟨89⟩, jump (by jump_dest),
    jumpdest, dup1, dup1, push0, tstore hperm, pop, pop, jump (by jump_dest),
    jumpdest, stop ]

theorem flagX_set_shortarg {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flagBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hmatch : (flagSelBytes 0 == I.calldata.extract 0 4) = true) :
    RDrev flagBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨heq0, htake⟩ := flagMatches 0 (by omega) hsz4 hmatch
  obtain ⟨_, _, hreach⟩ := flagReachBody 0 (by omega) ⟨52⟩ hcode hwv hsz4 hsize heq0 htake
    (by jump_dest) (by decide)
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  exact evm_run hreach with [
    jumpdest, push1 ⟨67⟩, push1 ⟨63⟩, calldatasize, push1 ⟨4⟩, push1 ⟨97⟩,
    jump (by jump_dest),
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push1 ⟨112⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem flagX_set_hugearg {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flagBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hmatch : (flagSelBytes 0 == I.calldata.extract 0 4) = true) :
    RDrev flagBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨heq0, htake⟩ := flagMatches 0 (by omega) hsz4 hmatch
  obtain ⟨_, _, hreach⟩ := flagReachBody 0 (by omega) ⟨52⟩ hcode hwv hsz4 hsize heq0 htake
    (by jump_dest) (by decide)
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact evm_run hreach with [
    jumpdest, push1 ⟨67⟩, push1 ⟨63⟩, calldatasize, push1 ⟨4⟩, push1 ⟨97⟩,
    jump (by jump_dest),
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push1 ⟨112⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-- `getFlag` returns the transient word at slot 0. -/
theorem flagX_get_success {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flagBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size)     (hsize : I.calldata.size < UInt256.size)
    (hg : (flagSelBytes 1 == I.calldata.extract 0 4) = true) :
    RDret flagBytecode g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray (flagWord σ I.codeOwner)) := by
  obtain ⟨heq0, htake⟩ := flagMatches 1 (by omega) hsz hg
  obtain ⟨_, _, hreach⟩ := flagReachBody 1 (by omega) ⟨69⟩ hcode hwv hsz hsize heq0 htake
    (by jump_dest) (by decide)
  exact evm_run hreach with [
    jumpdest, push0, tload, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (solcReturnMem (flagWord σ I.codeOwner)) (UInt256.ofNat 5) (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide) mem_cost
      (solcReturnMem_mload64 (flagWord σ I.codeOwner))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (flagWord σ I.codeOwner)) (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128])
      (by evm_ov) ]

/-! ## Solm bodies -/

theorem flagArgStore_v (I : ExecutionEnv) :
    (flagArgStore I).get? "v" = some (flagArgValue I) := by
  simp [flagArgStore, flagArgValue]

theorem flagEvalArg (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? flagConfig { contract := TransientFlag.flagContract, locals := flagArgStore I }
        evm (.var "v") = .ok (flagArgValue I) := by
  simp only [evalExpr?, EvalResult.ofOption, flagArgStore_v]

theorem flagAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? flagConfig
        { contract := TransientFlag.flagContract, locals := flagArgStore I } evm
        .transient TransientFlag.flagRef (flagArgValue I) =
      .ok ({ contract := TransientFlag.flagContract, locals := flagArgStore I },
        flagAfterSet evm (flagArg I)) := by
  rw [assignStorageRef?]
  simp [resolveTransientStorageRef?, TransientFlag.flagRef,
    evalTransientStorageRef, evalTransientStorageRefSteps, bind, EvalResult.bind, pure,
    EvalResult.ofOption, storageTypeAt?, TransientFlag.flagContract, flagConfig, flagArgValue,
    transientLocStore_flag]

theorem setFlagBody (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody flagConfig TransientFlag.flagContract evm (flagArgStore I)
      TransientFlag.setFlagTransition.body
      (.returned { contract := TransientFlag.flagContract, locals := flagArgStore I }
        (flagAfterSet evm (flagArg I)) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (flagEvalArg evm I) (flagAssign evm I)) ?_
  exact ExecBlock.nil

theorem getFlagEval (evm : EVM.State) (locals : Store) :
    evalExpr? flagConfig { contract := TransientFlag.flagContract, locals := locals } evm
        (.transient TransientFlag.flagRef) =
      .ok (flagValue evm.accountMap evm.executionEnv.codeOwner) := by
  simp [evalExpr?, resolveTransientStorageRef?, TransientFlag.flagRef,
    evalTransientStorageRef, evalTransientStorageRefSteps,
    bind, EvalResult.bind, pure, EvalResult.ofOption, storageTypeAt?,
    TransientFlag.flagContract, readTransientStorage?, flagConfig, transientLocLoad_flag, flagValue]

theorem getFlagBody (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody flagConfig TransientFlag.flagContract evm locals
      TransientFlag.getFlagTransition.body
      (.returned { contract := TransientFlag.flagContract, locals := locals } evm
        (some [flagValue evm.accountMap evm.executionEnv.codeOwner])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns (getFlagEval evm locals)

theorem flagDecode_set_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata (TransientFlag.setFlagTransition.params.map Param.name)
        (transitionSignature TransientFlag.setFlagTransition).paramTypes I.calldata =
      some (flagArgStore I) := by
  show decodeCalldata ["v"] [TransientFlag.uint256] I.calldata = _
  simpa [TransientFlag.uint256, abiUInt256, flagArgStore, flagArgValue, flagArg, calldataWord]
    using decodeCalldata_uint256_ok (cd := I.calldata) (x := "v") hsz36 hbig

theorem flagDecode_set_none_short {I : ExecutionEnv} (hshort : I.calldata.size < 36) :
    decodeCalldata (TransientFlag.setFlagTransition.params.map Param.name)
        (transitionSignature TransientFlag.setFlagTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["v"] [TransientFlag.uint256] I.calldata = none
  simpa [TransientFlag.uint256, abiUInt256] using
    decodeCalldata_uint256_none_short (cd := I.calldata) (x := "v") hshort

theorem flagDecode_set_none_huge {I : ExecutionEnv} (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (TransientFlag.setFlagTransition.params.map Param.name)
        (transitionSignature TransientFlag.setFlagTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["v"] [TransientFlag.uint256] I.calldata = none
  simpa [TransientFlag.uint256, abiUInt256] using
    decodeCalldata_uint256_none_huge (cd := I.calldata) (x := "v") hbig

theorem flagDecode_get_ok {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (TransientFlag.getFlagTransition.params.map Param.name)
        (transitionSignature TransientFlag.getFlagTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem flagGetReturnEncoding (σ : AccountMap) (owner : AccountAddress) :
    encodeReturnValue? TransientFlag.uint256 (flagValue σ owner) =
      some (UInt256.toByteArray (flagWord σ owner)) :=
  uint256ReturnEncoding (flagWord σ owner)

/-! ## Coupling -/

theorem flagNoDispatch {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flagBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 2 → (flagSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor flagConfig TransientFlag.flagContract σ σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (flagX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm).reEquivNoDispatch
      hcode (flagDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (flagX_short (g := Sat256.ofUInt256 g) hcode hwv hshort).reEquivNoDispatch hcode
      (flagDispatch_none_short hshort)

theorem flagNonPayable {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flagBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor flagConfig TransientFlag.flagContract σ σ₀ g A I := by
  exact (flagX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg TransientFlag.flagContract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ TransientFlag.flagContract.transitions := by
          rw [dispatchMsg_eq_dispatchList TransientFlag.flagContract I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldata (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (flagBodyReverts_nonPayable t htmem
              (initState σ σ₀ (Sat256.ofUInt256 g) A I) callargs
              (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem flagReEquiv_callvalueZero {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flagBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) :
    runtimeEquivalenceFor flagConfig TransientFlag.flagContract σ σ₀ g A I := by
  by_cases hselShort : I.calldata.size < 4
  · exact (flagX_short (g := Sat256.ofUInt256 g) hcode hwv hselShort).reEquivNoDispatch
      hcode (flagDispatch_none_short hselShort)
  · have hsz4 : 4 ≤ I.calldata.size := by omega
    by_cases hf : (flagSelBytes 0 == I.calldata.extract 0 4) = true
    · have hd := flagDispatch_set (cd := I.calldata) hf
      by_cases hsz36 : 36 ≤ I.calldata.size
      · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
        · have hdec := flagDecode_set_ok (I := I) hsz36 hbig
          have hbody := setFlagBody
              (initState σ σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv)
          exact (flagX_set_success (g := Sat256.ofUInt256 g) hcode hwv hsz36 hbig hsize hperm
              hf).reEquivExecutionGen hcode hd hdec hbody
            (by
              symm
              simpa [initState] using
                flagAfterSet_accountMap (initState σ σ₀ (Sat256.ofUInt256 g) A I) (flagArg I))
            (returnEquiv.fallthrough rfl rfl (by native_decide))
        · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
          have hdec := flagDecode_set_none_huge (I := I) hbigge
          exact (flagX_set_hugearg (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hbigge
              hf).reEquivDecodingFailed hcode hd hdec
      · have hshort : I.calldata.size < 36 := by omega
        have hdec := flagDecode_set_none_short (I := I) hshort
        exact (flagX_set_shortarg (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hshort
            hf).reEquivDecodingFailed hcode hd hdec
    · rw [Bool.not_eq_true] at hf
      by_cases hg : (flagSelBytes 1 == I.calldata.extract 0 4) = true
      · have hd := flagDispatch_get (cd := I.calldata) hf hg
        have hdec := flagDecode_get_ok (I := I) hsz4
        have hbody := getFlagBody
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
            (by simp only [initState]; exact hwv)
        exact (flagX_get_success (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize
            hg).reEquivExecutionTransport hcode hd hdec hbody
          (by simp [initState])
          (returnEquiv_of_encode (flagGetReturnEncoding σ I.codeOwner))
      · rw [Bool.not_eq_true] at hg
        have hnm : ∀ i, i < 2 → (flagSelBytes i == I.calldata.extract 0 4) = false := by
          intro i hi
          interval_cases i
          · exact hf
          · exact hg
        exact flagNoDispatch hcode hsize hperm hwv hnm

/-- **Correctness of `TransientFlag`.** -/
theorem transientFlagCorrect : runtimeEquivalence flagConfig flagBytecode TransientFlag.flagContract := by
  refine ⟨fun σ σ₀ g A I hcode hsize hperm => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact flagReEquiv_callvalueZero hcode hsize hperm hwv
  · exact flagNonPayable hcode hwv
