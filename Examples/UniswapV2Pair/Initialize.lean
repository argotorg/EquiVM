import Examples.UniswapV2Pair.ExternalWrappers
import Examples.UniswapV2Pair.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `initialize(address,address)` success slice -/

abbrev initializeToken0Word (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev initializeToken1Word (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev initializeToken0Value (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (initializeToken0Word I).toNat)

abbrev initializeToken1Value (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (initializeToken1Word I).toNat)

abbrev initializeStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "_token0" (initializeToken0Value I)).insert "_token1"
    (initializeToken1Value I)

def initializeToken0State (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩)
      (initializeToken0Word I))

def initializePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  let evm0 := initializeToken0State evm I
  Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨7⟩
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨7⟩)
      (initializeToken1Word I))

abbrev initializeFactoryWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uniswapSlotWord ⟨5⟩ σ I

abbrev initializeToken0OldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uniswapSlotWord ⟨6⟩ σ I

abbrev initializeToken0StoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  setAddressOffset0Word (initializeToken0OldWord σ I) (initializeToken0Word I)

def initializeToken0Map (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨6⟩ (initializeToken0StoredWord σ I)

abbrev initializeToken1OldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uniswapSlotWord ⟨7⟩ (initializeToken0Map σ I) I

abbrev initializeToken1StoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  setAddressOffset0Word (initializeToken1OldWord σ I) (initializeToken1Word I)

def initializePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (initializeToken0Map σ I) ⟨7⟩
    (initializeToken1StoredWord σ I)

theorem initializeStore_token0 (I : ExecutionEnv) :
    (initializeStore I).get? "_token0" = some (initializeToken0Value I) := by
  rw [initializeStore, store_get_ne _ _ (by decide), store_get_self]

theorem initializeStore_token1 (I : ExecutionEnv) :
    (initializeStore I).get? "_token1" = some (initializeToken1Value I) := by
  rw [initializeStore, store_get_self]

theorem initializeStore_token0_getElem? (I : ExecutionEnv) :
    (initializeStore I)["_token0"]? = some (initializeToken0Value I) := by
  rw [← Std.HashMap.get?_eq_getElem?, initializeStore_token0]

theorem initializeStore_token1_getElem? (I : ExecutionEnv) :
    (initializeStore I)["_token1"]? = some (initializeToken1Value I) := by
  rw [← Std.HashMap.get?_eq_getElem?, initializeStore_token1]

theorem initializeStore_factory (I : ExecutionEnv) :
    (initializeStore I).get? "factory" = none := by
  rw [initializeStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem initializeStore_token0Base (I : ExecutionEnv) :
    (initializeStore I).get? "token0" = none := by
  rw [initializeStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem initializeStore_token1Base (I : ExecutionEnv) :
    (initializeStore I).get? "token1" = none := by
  rw [initializeStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_initialize_token0 (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := initializeStore I } evm
      (.var "_token0") = .ok (initializeToken0Value I) := by
  simp only [evalExpr?]
  rw [initializeStore_token0]
  rfl

theorem evalExpr_initialize_token1 (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := initializeStore I } evm
      (.var "_token1") = .ok (initializeToken1Value I) := by
  simp only [evalExpr?]
  rw [initializeStore_token1]
  rfl

theorem evalExpr_initialize_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := initializeStore I } evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_initialize_factory (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := initializeStore I } evm
      (.storage factoryRef) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
            solcAddrMask).toNat)) := by
  have hty : storageTypeAt? contract.storage
      ({ base := "factory", steps := [] } : EvaledStorageRef) = some addrSt := by
    decide
  rw [evalExpr_storage_scalar
    (er := ({ base := "factory", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨5⟩)
    (hbase := initializeStore_factory I)
    (her := by simp [evalStorageRef, evalStorageRefSteps, factoryRef, EvalResult.bind,
      bind, pure])
    (hty := hty)
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (uniswapStorageLocLoad_address_offset0 evm ⟨5⟩)

theorem evalExpr_initialize_factory_eq_sender_true (evm : EVM.State) (I : ExecutionEnv)
    (hfactory :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩) solcAddrMask =
        uniswapSourceWord evm.executionEnv) :
    evalExpr? config { contract := contract, locals := initializeStore I } evm
      (.binary .eq sender (.storage factoryRef)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_initialize_sender, evalExpr_initialize_factory, bind,
    EvalResult.bind, evalBinaryOp?]
  rw [uniswapMaskedAddress_eq_source_of_word_eq (I := evm.executionEnv) hfactory]
  simp [BEq.beq]

theorem initializeAssignToken0 (evm : EVM.State) (I : ExecutionEnv)
    (hcanon0 : (initializeToken0Word I).toNat < EVM.addressModulus) :
    assignStorageRef? config { contract := contract, locals := initializeStore I } evm
      .storage token0Ref (initializeToken0Value I) =
        .ok ({ contract := contract, locals := initializeStore I },
          initializeToken0State evm I) := by
  have her : evalStorageRef config { contract := contract, locals := initializeStore I } evm
      token0Ref = .ok { base := "token0", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "token0", steps := [] } : EvaledStorageRef) = some addrSt := by
    decide
  have hstore :
      storageLocStore evm (addrLoc ⟨6⟩) (initializeToken0Value I) =
        some (initializeToken0State evm I) := by
    simpa [initializeToken0State, initializeToken0Value, initializeToken0Word] using
      uniswapStorageLocStore_address_offset0 evm ⟨6⟩ (initializeToken0Word I) hcanon0
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := initializeStore I }) (evm := evm)
    (evm' := initializeToken0State evm I) (slot := token0Ref)
    (er := { base := "token0", steps := [] }) (ty := addrSt) (loc := addrLoc ⟨6⟩)
    (value := initializeToken0Value I) (initializeStore_token0Base I) her hty (by rfl)
    (by trivial) hstore

theorem initializeAssignToken1 (evm : EVM.State) (I : ExecutionEnv)
    (hcanon1 : (initializeToken1Word I).toNat < EVM.addressModulus) :
    assignStorageRef? config { contract := contract, locals := initializeStore I }
      (initializeToken0State evm I) .storage token1Ref (initializeToken1Value I) =
        .ok ({ contract := contract, locals := initializeStore I },
          initializePostState evm I) := by
  have her : evalStorageRef config { contract := contract, locals := initializeStore I }
      (initializeToken0State evm I) token1Ref =
        .ok { base := "token1", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "token1", steps := [] } : EvaledStorageRef) = some addrSt := by
    decide
  have hstore :
      storageLocStore (initializeToken0State evm I) (addrLoc ⟨7⟩)
          (initializeToken1Value I) =
        some (initializePostState evm I) := by
    simpa [initializePostState, initializeToken1Value, initializeToken1Word] using
      uniswapStorageLocStore_address_offset0 (initializeToken0State evm I) ⟨7⟩
        (initializeToken1Word I) hcanon1
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := initializeStore I })
    (evm := initializeToken0State evm I) (evm' := initializePostState evm I)
    (slot := token1Ref) (er := { base := "token1", steps := [] }) (ty := addrSt)
    (loc := addrLoc ⟨7⟩) (value := initializeToken1Value I)
    (initializeStore_token1Base I) her hty (by rfl) (by trivial) hstore

theorem uniswapDecode_initialize_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (initializeToken0Word I).toNat < EVM.addressModulus)
    (hcanon1 : (initializeToken1Word I).toNat < EVM.addressModulus) :
    decodeCalldata (initializeTransition.params.map Param.name)
      (transitionSignature initializeTransition).paramTypes I.calldata =
        some (initializeStore I) := by
  simpa [initializeTransition, initializeStore, initializeToken0Value, initializeToken1Value,
    initializeToken0Word, initializeToken1Word, addr] using
    (decodeCalldata_address_address_ok (cd := I.calldata) (x := "_token0") (y := "_token1")
      hsz68 hbig hcanon0 hcanon1)

theorem uniswapDecode_initialize_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (initializeTransition.params.map Param.name)
      (transitionSignature initializeTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["_token0", "_token1"] [addr, addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_address_none_short
    (cd := I.calldata) (x := "_token0") (y := "_token1") hsz4 hshort

theorem uniswapInitializeBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hfactory :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩) solcAddrMask =
        uniswapSourceWord evm.executionEnv)
    (hcanon0 : (initializeToken0Word I).toNat < EVM.addressModulus)
    (hcanon1 : (initializeToken1Word I).toNat < EVM.addressModulus) :
    ExecTransitionBody config contract evm (initializeStore I) initializeTransition.body
      (.returned { contract := contract, locals := initializeStore I }
        (initializePostState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_initialize_factory_eq_sender_true evm I hfactory)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_initialize_token0 evm I)
      (initializeAssignToken0 evm I hcanon0)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_initialize_token1 (initializeToken0State evm I) I)
      (initializeAssignToken1 evm I hcanon1)) ExecBlock.nil

/-! ## EVM success path -/

/-- The optimized external wrapper for `initialize(address,address)` accepts canonical calldata and
    jumps to the initialize routine at pc 3139 with continuation pc 570. -/
theorem uniswapInitializeX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanon0 : (initializeToken0Word I).toNat < EVM.addressModulus)
    (hcanon1 : (initializeToken1Word I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨979⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3139⟩
      [initializeToken1Word I, initializeToken0Word I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1001⟩ := RD.uniswapTwoAddressExternalLenOk
    (entry := ⟨979⟩) (ret := ⟨570⟩) (routine := ⟨3139⟩) hreach
    uniswap_two_address_external_entry_wf (by jump_dest) hsz68 hsize
  obtain ⟨_, _, rd3139⟩ := RD.uniswapTwoAddressExternalMaskAndJump
    (entry := ⟨979⟩) (ret := ⟨570⟩) (routine := ⟨3139⟩) (R := [sel]) rd1001
    uniswap_two_address_external_entry_wf
    (by simpa [initializeToken0Word] using hcanon0)
    (by simpa [initializeToken1Word] using hcanon1)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [initializeToken0Word, initializeToken1Word] using rd3139⟩

/-- Short-calldata path for `initialize(address,address)` from the dispatcher body entry.

This covers calldata with a selector present but fewer than two ABI words. The dispatcher-level
`calldatasize < 4` branch remains in `Correct.lean`.
-/
theorem uniswapInitializeX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨979⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapTwoAddressExternalShort
    (entry := ⟨979⟩) (ret := ⟨570⟩) (routine := ⟨3139⟩)
    hreach uniswap_two_address_external_entry_wf hsz4 hsize hshort

/-- EVM success path for `initialize(address,address)`.

This proves the exact success slice: canonical calldata, `msg.sender == factory`, and writable
storage.  The forbidden-sender revert string is left for a later revert-slice proof.
-/
theorem uniswapX_initialize_success {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hcanon0 : (initializeToken0Word I).toNat < EVM.addressModulus)
    (hcanon1 : (initializeToken1Word I).toNat < EVM.addressModulus)
    (hfactory :
      UInt256.land (initializeFactoryWord σ I) solcAddrMask = uniswapSourceWord I)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨979⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, initializePostMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd3139⟩ := uniswapInitializeX_decoded (g := g)
    hsz68 hsize hcanon0 hcanon1 hreach
  have rd3142 := evm_run rd3139 with [jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd3143₀⟩ := rd3142.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3143⟩ : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3143⟩
      [initializeFactoryWord σ I, initializeToken1Word I, initializeToken0Word I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [initializeFactoryWord, uniswapSlotWord, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using rd3143₀⟩
  have rd3154₀ := evm_run rd3143 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, caller, eq, push2 ⟨3225⟩]
  have rd3154 := rd3154₀
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hfactoryLeft :
      UInt256.land solcAddrMask (initializeFactoryWord σ I) = uniswapSourceWord I := by
    rw [u256_land_comm]
    exact hfactory
  rw [hmask, hfactoryLeft] at rd3154
  have hcallerEq :
      UInt256.eq (UInt256.ofNat I.source.val) (uniswapSourceWord I) ≠ ⟨0⟩ := by
    change UInt256.eq (uniswapSourceWord I) (uniswapSourceWord I) ≠ ⟨0⟩
    rw [uInt256_eq_self]
    decide
  have rd3225 := rd3154.jumpiT (by decide) hcallerEq (by jump_dest) (by evm_ov)
  have rd3229 := evm_run rd3225 with [jumpdest, push1 ⟨6⟩, dup1]
  obtain ⟨_, _, rd3230₀⟩ := rd3229.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3230⟩ : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3230⟩
      [initializeToken0OldWord σ I, ⟨6⟩, initializeToken1Word I, initializeToken0Word I,
        ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [initializeToken0OldWord, uniswapSlotWord, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using rd3230₀⟩
  have rd3256₀ := evm_run rd3230 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap4, dup5, and,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, swap2, dup3, and, lor,
    swap1, swap2]
  have hset0 :
      UInt256.lor
          (UInt256.land (UInt256.lnot solcAddrMask) (initializeToken0OldWord σ I))
          (UInt256.land solcAddrMask (initializeToken0Word I)) =
        initializeToken0StoredWord σ I := by
    unfold initializeToken0StoredWord setAddressOffset0Word
    rw [u256_land_comm (UInt256.lnot solcAddrMask) (initializeToken0OldWord σ I),
      u256_land_comm solcAddrMask (initializeToken0Word I)]
  have rd3256 := rd3256₀
  rw [hmask] at rd3256
  rw [hset0] at rd3256
  obtain ⟨_, _, rd3257₀⟩ := rd3256.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd3257⟩ : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3257⟩
      [UInt256.lnot solcAddrMask, initializeToken1Word I, solcAddrMask, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, initializeToken0Map σ I) k C := by
    exact ⟨_, _, by simpa [initializeToken0Map] using rd3257₀⟩
  have rd3260 := evm_run rd3257 with [push1 ⟨7⟩, dup1]
  obtain ⟨_, _, rd3261₀⟩ := rd3260.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3261⟩ : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3261⟩
      [initializeToken1OldWord σ I, ⟨7⟩, UInt256.lnot solcAddrMask, initializeToken1Word I,
        solcAddrMask, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, initializeToken0Map σ I) k C := by
    exact ⟨_, _, by
      simpa [initializeToken1OldWord, uniswapSlotWord, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using rd3261₀⟩
  have rd3268₀ := evm_run rd3261 with [swap3, swap1, swap4, and, swap2, and, lor, swap1]
  have hset1 :
      UInt256.lor
          (UInt256.land (initializeToken1OldWord σ I) (UInt256.lnot solcAddrMask))
          (UInt256.land solcAddrMask (initializeToken1Word I)) =
        initializeToken1StoredWord σ I := by
    unfold initializeToken1StoredWord setAddressOffset0Word
    rw [u256_land_comm solcAddrMask (initializeToken1Word I)]
  have rd3269 := rd3268₀
  rw [hset1] at rd3269
  obtain ⟨_, _, rd3270₀⟩ := rd3269.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd3270⟩ : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3270⟩ [⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, initializePostMap σ I) k C := by
    exact ⟨_, _, by simpa [initializePostMap] using rd3270₀⟩
  have rd570 := evm_run rd3270 with [jump (by jump_dest), jumpdest]
  exact rd570.stop (by decide) (by evm_ov)

/- Canonical-success refinement slice for `initialize(address,address)`.

The forbidden-sender revert string is intentionally left to a later revert-slice proof.
-/
set_option maxHeartbeats 2000000 in
theorem uniswapInitializeBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (_hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (initializeToken0Word I).toNat < EVM.addressModulus)
    (hcanon1 : (initializeToken1Word I).toNat < EVM.addressModulus)
    (hfactory :
      UInt256.land (initializeFactoryWord σ_evm I) solcAddrMask = uniswapSourceWord I)
    (hdispatch : dispatchMsg contract I.calldata = some initializeTransition)
    (hdecode :
      decodeCalldata (initializeTransition.params.map Param.name)
        (transitionSignature initializeTransition).paramTypes I.calldata =
          some (initializeStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨979⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hfactoryWord :
      initializeFactoryWord σ_evm I = initializeFactoryWord σ_solm I := by
    simpa [initializeFactoryWord, uniswapSlotWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hfactoryS :
      UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨5⟩)
          solcAddrMask =
        uniswapSourceWord evmS.executionEnv := by
    have hfactorySolm :
        UInt256.land (initializeFactoryWord σ_solm I) solcAddrMask = uniswapSourceWord I := by
      simpa [hfactoryWord] using hfactory
    simpa [evmS, initState, initializeFactoryWord, uniswapSlotWord] using
      hfactorySolm
  have hbody :
      ExecTransitionBody config contract evmS (initializeStore I) initializeTransition.body
        (.returned { contract := contract, locals := initializeStore I }
          (initializePostState evmS I) none) := by
    exact uniswapInitializeBodyReturns evmS I
      (by simp only [evmS, initState]; exact hwv) hfactoryS hcanon0 hcanon1
  have hold0 :
      initializeToken0OldWord σ_evm I = initializeToken0OldWord σ_solm I := by
    simpa [initializeToken0OldWord, uniswapSlotWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have hstored0 :
      initializeToken0StoredWord σ_evm I = initializeToken0StoredWord σ_solm I := by
    simp [initializeToken0StoredWord, hold0]
  have hmap0 :
      accountMapEquiv (initializeToken0Map σ_evm I) (initializeToken0Map σ_solm I) := by
    unfold initializeToken0Map
    rw [hstored0]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩
      (initializeToken0StoredWord σ_solm I) hAccounts
  have hold1 :
      initializeToken1OldWord σ_evm I = initializeToken1OldWord σ_solm I := by
    simpa [initializeToken1OldWord, uniswapSlotWord] using
      accountMapEquiv_storage_findD hmap0 I.codeOwner ⟨7⟩ ⟨0⟩
  have hstored1 :
      initializeToken1StoredWord σ_evm I = initializeToken1StoredWord σ_solm I := by
    simp [initializeToken1StoredWord, hold1]
  have hcreated :
      (cA, initializePostMap σ_evm I).1 =
        (initializePostState evmS I).createdAccounts := by
    simp [initializePostState, initializeToken0State, evmS, initState, storageStore_createdAccounts]
  have hAccountsPost :
      accountMapEquiv (initializePostMap σ_evm I)
        (initializePostState evmS I).accountMap := by
    unfold initializePostMap
    rw [hstored1]
    have hpostSolm :
        (initializePostState evmS I).accountMap =
          sstoreAccountMap I.codeOwner (initializeToken0Map σ_solm I) ⟨7⟩
            (initializeToken1StoredWord σ_solm I) := by
      simp [initializePostState, initializeToken0State, initializeToken0Map,
        initializeToken1StoredWord, initializeToken1OldWord, initializeToken0StoredWord,
        initializeToken0OldWord, evmS, initState, storageStore_accountMap,
        storageStore_executionEnv, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, uniswapSlotWord]
    rw [hpostSolm]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨7⟩
      (initializeToken1StoredWord σ_solm I) hmap0
  exact (uniswapX_initialize_success (g := Sat256.ofUInt256 g)
      hperm hsz68 hsize hcanon0 hcanon1 hfactory hreach)
    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody hcreated
      hAccountsPost (returnEquiv.void rfl rfl rfl)

/-- Short-calldata decode-failure refinement slice for `initialize(address,address)`.

The non-canonical and huge-calldata branches are intentionally not claimed here: the optimized
bytecode masks address words and uses an unsigned length check, while the current Solm ABI decoder
rejects those cases before execution.
-/
theorem uniswapInitializeBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some initializeTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨979⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_initialize_none_short (I := I) hsz4 hshort
  exact (uniswapInitializeX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- Canonical-success `initialize(address,address)` refinement slice, packaged from selector
dispatch through the body core. -/
theorem uniswapInitializeBodyOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x5c, 0xc9, 0x55]⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (initializeToken0Word I).toNat < EVM.addressModulus)
    (hcanon1 : (initializeToken1Word I).toNat < EVM.addressModulus)
    (hfactory :
      UInt256.land (initializeFactoryWord σ_evm I) solcAddrMask = uniswapSourceWord I)
    (hdispatch : dispatchMsg contract I.calldata = some initializeTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x48, 0x5c, 0xc9, 0x55]⟩ rfl hsel
  exact uniswapInitializeBodyCoreOk hcode hsize hperm hwv hsz68 hbig hcanon0 hcanon1
    hfactory hdispatch
    (uniswapDecode_initialize_ok hsz68 hbig hcanon0 hcanon1)
    (uniswapReachInitializeBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

/-- Short-calldata decode-failure `initialize(address,address)` refinement slice, packaged from
selector dispatch through the body core. -/
theorem uniswapInitializeBodyDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x48, 0x5c, 0xc9, 0x55]⟩)
    (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some initializeTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x48, 0x5c, 0xc9, 0x55]⟩ rfl hsel
  exact uniswapInitializeBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hdispatch
    (uniswapReachInitializeBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

end UniswapV2Pair
