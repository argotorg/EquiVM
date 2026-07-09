import Benchmarks.Dss.Cat.Trusted
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Memory
import Reasoning.Refinement
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Storage
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# MakerDAO/Sky DSS Cat shared proof foundation

Contract-wide selector, dispatcher-navigation, dispatch-failure, storage-word, ABI-decode, and
global revert facts used by the top-level runtime proof and the per-function body proofs.

The solc 0.6.12 dispatcher is a binary search tree over the 4-byte selector, structurally identical
to the other DSS contracts: a root split (pc 32), a high split (pc 43) and a low split (pc 152),
under which sit four arm groups of four selectors each.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cat

/-! ## Static-call code-preservation lift

The `.code`-projection peer of `typedCallViaEVM_static_accountStorageStateEq`
(`Reasoning/ExternalCall.lean`): a `perm = false` external call cannot create, destroy, or change
any account's code, so `(σ.findD a default).code` is preserved.  Built on the evmlean
`Theta_static_accountCode_eq`. -/

-- LIBRARY CANDIDATE: belongs alongside `callViaEVM_static_accountStorageStateEq` in
-- `Reasoning/ExternalCall.lean`; kept here to avoid editing `Reasoning/`.
theorem callViaEVM_static_accountCode_eq {evm evm' : EVM.State}
    {target : EVM.Address} {value : ℤ} {calldata : ByteArray}
    {z : Bool} {out : ByteArray}
    (hcall : callViaEVM evm target value calldata (z, evm', out) false) :
    accountCodeStateEq evm.accountMap evm'.accountMap := by
  cases hcall with
  | callMade _hvalue hTheta hevm' _hvalue' _hdepth =>
      rcases hTheta with ⟨_callGas, _A_in, hΘ⟩
      subst hevm'
      exact Theta_static_accountCode_eq hΘ.symm
  | callNotMade _hsubstate hevm' _hvalue =>
      subst hevm'
      exact accountCodeStateEq_refl evm.accountMap

-- LIBRARY CANDIDATE: mirror of `typedCallViaEVM_static_accountStorageStateEq` for `.code`.
theorem typedCallViaEVM_static_accountCode_eq {cfg : Config} {evm evm' : EVM.State}
    {target : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray}
    (hcall : typedCallViaEVM cfg evm target name 0 args (z, evm', out) false) :
    accountCodeStateEq evm.accountMap evm'.accountMap := by
  obtain ⟨_calldata, _hencode, hraw⟩ := hcall
  exact callViaEVM_static_accountCode_eq hraw

/-- `uniswapExtCodeSizeWord` reads only an account's `.code` (as `ofNat · .code.size`), so it is a
    function of `(σ.findD a default).code` — the projection `accountCodeStateEq` preserves. -/
theorem uniswapExtCodeSizeWord_eq_ofNat_findD (σ : AccountMap) (target : UInt256) :
    Reasoning.Theory.uniswapExtCodeSizeWord σ target
      = UInt256.ofNat (σ.findD (AccountAddress.ofUInt256 target) default).code.size := by
  unfold Reasoning.Theory.uniswapExtCodeSizeWord
  cases h : σ.find? (AccountAddress.ofUInt256 target) with
  | none => simp [Batteries.RBMap.findD, h, Option.option]; rfl
  | some acc => simp [Batteries.RBMap.findD, h, Option.option]

/-- Code preservation transfers to `uniswapExtCodeSizeWord`: static calls leave every account's
    `EXTCODESIZE` word unchanged. -/
theorem uniswapExtCodeSizeWord_eq_of_accountCodeStateEq {σ σ' : AccountMap} (target : UInt256)
    (h : accountCodeStateEq σ σ') :
    Reasoning.Theory.uniswapExtCodeSizeWord σ' target
      = Reasoning.Theory.uniswapExtCodeSizeWord σ target := by
  rw [uniswapExtCodeSizeWord_eq_ofNat_findD, uniswapExtCodeSizeWord_eq_ofNat_findD,
    (h (AccountAddress.ofUInt256 target)).symm]

/-! ## Selector helpers -/

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev catSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order (alphabetical). -/
def catSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x45, 0xcf, 0x22, 0x30]⟩  -- bite(bytes32,address)
  | 1 => ⟨#[0x75, 0x42, 0x15, 0xa1]⟩  -- box()
  | 2 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩  -- cage()
  | 3 => ⟨#[0xe6, 0x6d, 0x27, 0x9b]⟩  -- claw(uint256)
  | 4 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩  -- deny(address)
  | 5 => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩  -- file(bytes32,address)
  | 6 => ⟨#[0xeb, 0xec, 0xb3, 0x9d]⟩  -- file(bytes32,bytes32,address)
  | 7 => ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩  -- file(bytes32,bytes32,uint256)
  | 8 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩  -- file(bytes32,uint256)
  | 9 => ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩  -- ilks(bytes32)
  | 10 => ⟨#[0xa4, 0xfe, 0x8c, 0xaf]⟩ -- litter()
  | 11 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 12 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 13 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | 14 => ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩ -- vow()
  | _ => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩  -- wards(address)

/-! ## Dispatcher constants and prefix reachability -/

abbrev catRootSplitPc : UInt256 := ⟨32⟩
abbrev catHighSplitPc : UInt256 := ⟨43⟩
abbrev catHighHighFirstArmPc : UInt256 := ⟨54⟩
abbrev catHighLowJumpdestPc : UInt256 := ⟨102⟩
abbrev catHighLowFirstArmPc : UInt256 := ⟨103⟩
abbrev catLowJumpdestPc : UInt256 := ⟨151⟩
abbrev catLowSplitPc : UInt256 := ⟨152⟩
abbrev catLowHighFirstArmPc : UInt256 := ⟨163⟩
abbrev catLowLowJumpdestPc : UInt256 := ⟨211⟩
abbrev catLowLowFirstArmPc : UInt256 := ⟨212⟩
abbrev catDispatchBodyPc : UInt256 := ⟨18⟩
abbrev catSelectorLoadPc : UInt256 := ⟨26⟩
abbrev catDispatchRevertPc : UInt256 := ⟨256⟩

/-- Selectors reachable in the low-low arm group, ascending order. -/
def catLowLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩ -- file(bytes32,bytes32,uint256)
  | 1 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 2 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | _ => ⟨#[0x45, 0xcf, 0x22, 0x30]⟩ -- bite(bytes32,address)

/-- Selectors reachable in the low-high arm group, ascending order. -/
def catLowHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩ -- vow()
  | 1 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 2 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩ -- cage()
  | _ => ⟨#[0x75, 0x42, 0x15, 0xa1]⟩ -- box()

/-- Selectors reachable in the high-low arm group, ascending order. -/
def catHighLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 1 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 2 => ⟨#[0xa4, 0xfe, 0x8c, 0xaf]⟩ -- litter()
  | _ => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)

/-- Selectors reachable in the high-high arm group, ascending order. -/
def catHighHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ -- file(bytes32,address)
  | 1 => ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩ -- ilks(bytes32)
  | 2 => ⟨#[0xe6, 0x6d, 0x27, 0x9b]⟩ -- claw(uint256)
  | _ => ⟨#[0xeb, 0xec, 0xb3, 0x9d]⟩ -- file(bytes32,bytes32,address)

/-! ## Storage word helpers -/

def catSlotWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I slot

abbrev catAddressReturnWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (catSlotWord slot σ I) solcAddrMask

theorem catStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa [addrLoc, addressOffset0Loc] using storageLocLoad_address_offset0 evm slot

theorem catStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

/-! ## ABI decode helpers -/

theorem decodeCalldata_legacyUInt256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

theorem decodeCalldata_legacyUInt256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
    (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

/-! ## Simple storage getter cores

Word getters (`box`, `live`, `litter`) share the uint256 return encoder at pc 419; address getters
(`vat`, `vow`) share the address return encoder at pc 347. -/

theorem catUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)))
    (hloc : config.storage.layout er = fun _ => some (wordLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (catStorageLocLoad_uint256 evm slot))

theorem catAddressGetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (catStorageLocLoad_address_offset0 evm slot))

theorem catUint256GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot : UInt256}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf catBytecode entry ⟨419⟩ routine)
    (hgetter : solcWordSlotGetterWf catBytecode routine slot)
    (hroutine : (D_J catBytecode 0).contains routine = true)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (catSlotWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : catSlotWord slot σ_evm I = catSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (catSlotWord slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (catSlotWord slot σ_evm I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (catSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (catSlotWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (catSlotWord slot σ_evm I))
  have hret := RD.solcWordGetterExternal (code := catBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := ⟨419⟩) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine (by jump_dest)
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | native_decide)
  have hret' :
      RDret catBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (catSlotWord slot σ_evm I)) := by
    simpa [catSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem catAddressGetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot : UInt256}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf catBytecode entry ⟨347⟩ routine)
    (hgetter : solcAddressSlotGetterWf catBytecode routine slot)
    (hroutine : (D_J catBytecode 0).contains routine = true)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (catAddressReturnWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : catSlotWord slot σ_evm I = catSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.address (AccountAddress.ofNat (catAddressReturnWord slot σ_solm I).toNat)] =
        some [Value.address (AccountAddress.ofNat (catAddressReturnWord slot σ_evm I).toNat)] := by
    have hslot : catSlotWord slot σ_solm I = catSlotWord slot σ_evm I := hword.symm
    simp [catAddressReturnWord, hslot]
  have henc :
      returnEquiv (UInt256.toByteArray (catAddressReturnWord slot σ_evm I))
        (some [(.address (AccountAddress.ofNat (catAddressReturnWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    simpa [catAddressReturnWord] using
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (catSlotWord slot σ_evm I)))
  have hret := RD.solcAddressGetterExternal (code := catBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := ⟨347⟩) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine (by jump_dest)
    (by
      unfold solcReturnAddressFromMemWf
      repeat' first | apply And.intro | native_decide)
  have hret' :
      RDret catBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (catAddressReturnWord slot σ_evm I)) := by
    simpa [catAddressReturnWord, catSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

/-! ## Selector-word extraction and split/arm well-formedness -/

theorem catSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    catSelWord I = sel := by
  simpa [catSelWord, solcSelectorWord] using
    solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

theorem catRootSplitWellFormed :
    selectorSplitWellFormed catBytecode catRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem catHighSplitWellFormed :
    selectorSplitWellFormed catBytecode catHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem catLowSplitWellFormed :
    selectorSplitWellFormed catBytecode catLowSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem catLowLowArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed catBytecode
      (nthArmPc catBytecode catLowLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem catLowHighArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed catBytecode
      (nthArmPc catBytecode catLowHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem catHighLowArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed catBytecode
      (nthArmPc catBytecode catHighLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem catHighHighArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed catBytecode
      (nthArmPc catBytecode catHighHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem catLowLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat catBytecode (nthArmPc catBytecode catLowLowFirstArmPc j))
        (catSelWord I) =
      if (catLowLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem catLowHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat catBytecode (nthArmPc catBytecode catLowHighFirstArmPc j))
        (catSelWord I) =
      if (catLowHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem catHighLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat catBytecode (nthArmPc catBytecode catHighLowFirstArmPc j))
        (catSelWord I) =
      if (catHighLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem catHighHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat catBytecode (nthArmPc catBytecode catHighHighFirstArmPc j))
        (catSelWord I) =
      if (catHighHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

/-! ## Dispatcher navigation (reach the selected arm group / body) -/

theorem catReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        catRootSplitPc [catSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [catRootSplitPc, catSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := catBytecode)
      (bodyPc := catDispatchBodyPc) (loadPc := catSelectorLoadPc)
      (firstPc := catRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := catDispatchRevertPc) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem catReachLowSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        catLowSplitPc [catSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    catReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h151 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt catBytecode catRootSplitPc) [catSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) :=
    RD.selectorSplitTakenAuto h32 catRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h152 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      catLowSplitPc [catSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [catLowSplitPc, catLowJumpdestPc, catRootSplitPc, armTgt, pushAt]
      using h151.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h152⟩

theorem catReachHighSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) = ⟨0⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        catHighSplitPc [catSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    catReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      catHighSplitPc [catSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [catHighSplitPc, catRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 catRootSplitWellFormed hroot (by simp)
  exact ⟨_, _, h43⟩

theorem catReachLowLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat catBytecode catLowSplitPc) (catSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        catLowLowFirstArmPc [catSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k152, C152, h152⟩ :=
    catReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h211 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt catBytecode catLowSplitPc) [catSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k152 + 5) (C152 + 22) :=
    RD.selectorSplitTakenAuto h152 catLowSplitWellFormed hlow (by jump_dest) (by simp)
  have h212 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      catLowLowFirstArmPc [catSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k152 + 5 + 1) (C152 + 22 + 1) := by
    simpa [catLowLowFirstArmPc, catLowLowJumpdestPc, catLowSplitPc, armTgt, pushAt]
      using h211.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h212⟩

theorem catReachLowHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat catBytecode catLowSplitPc) (catSelWord I) = ⟨0⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        catLowHighFirstArmPc [catSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k152, C152, h152⟩ :=
    catReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h163 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      catLowHighFirstArmPc [catSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k152 + 5) (C152 + 22) := by
    simpa [catLowHighFirstArmPc, catLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h152 catLowSplitWellFormed hlow (by simp)
  exact ⟨_, _, h163⟩

theorem catReachHighLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat catBytecode catHighSplitPc) (catSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        catHighLowFirstArmPc [catSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    catReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h102 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt catBytecode catHighSplitPc) [catSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) :=
    RD.selectorSplitTakenAuto h43 catHighSplitWellFormed hhigh (by jump_dest) (by simp)
  have h103 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      catHighLowFirstArmPc [catSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5 + 1) (C43 + 22 + 1) := by
    simpa [catHighLowFirstArmPc, catHighLowJumpdestPc, catHighSplitPc, armTgt, pushAt]
      using h102.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h103⟩

theorem catReachHighHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat catBytecode catHighSplitPc) (catSelWord I) = ⟨0⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        catHighHighFirstArmPc [catSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    catReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h54 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      catHighHighFirstArmPc [catSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) := by
    simpa [catHighHighFirstArmPc, catHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 catHighSplitWellFormed hhigh (by simp)
  exact ⟨_, _, h54⟩

theorem catReachLowLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat catBytecode catLowSplitPc) (catSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowLowFirstArmPc j))
        (catSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowLowFirstArmPc i))
        (catSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J catBytecode 0).contains bodyPC = true)
    (hbody : armTgt catBytecode (nthArmPc catBytecode catLowLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    catReachLowLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => catLowLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem catReachLowHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat catBytecode catLowSplitPc) (catSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowHighFirstArmPc j))
        (catSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowHighFirstArmPc i))
        (catSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J catBytecode 0).contains bodyPC = true)
    (hbody : armTgt catBytecode (nthArmPc catBytecode catLowHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    catReachLowHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => catLowHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem catReachHighLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat catBytecode catHighSplitPc) (catSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighLowFirstArmPc j))
        (catSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighLowFirstArmPc i))
        (catSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J catBytecode 0).contains bodyPC = true)
    (hbody : armTgt catBytecode (nthArmPc catBytecode catHighLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    catReachHighLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => catHighLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem catReachHighHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat catBytecode catHighSplitPc) (catSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighHighFirstArmPc j))
        (catSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighHighFirstArmPc i))
        (catSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J catBytecode 0).contains bodyPC = true)
    (hbody : armTgt catBytecode (nthArmPc catBytecode catHighHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    catReachHighHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => catHighHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

/-! ## Global prologue reverts (nonpayable / short calldata) -/

theorem catX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have h12 := h0.push2 ⟨16⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.uniswapPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem catX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt catBytecode)
    (opC := solcGuardTgtOp catBytecode)
    (wC := solcGuardTgtWidth catBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest)
  have h256 := h1.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.push2 ⟨256⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length]; omega)
  exact RD.uniswapPush1Dup1Revert0 h256 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

/-! ## Dispatch-failure (`dispatchMsg = none`) and non-payable body facts -/

theorem catDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [biteTransition, boxTransition, cageTransition, clawTransition, denyTransition,
      fileAddressTransition, fileIlkFlipTransition, fileIlkUintTransition, fileUintTransition,
      ilksTransition, litterTransition, liveTransition, relyTransition, vatTransition,
      vowTransition, wardsTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, biteSelectorBytes, boxSelectorBytes, cageSelectorBytes,
        clawSelectorBytes, denySelectorBytes, fileAddressSelectorBytes,
        fileIlkFlipSelectorBytes, fileIlkUintSelectorBytes, fileUintSelectorBytes,
        ilksSelectorBytes, litterSelectorBytes, liveSelectorBytes, relySelectorBytes,
        vatSelectorBytes, vowSelectorBytes, wardsSelectorBytes]
      native_decide) h

theorem catDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 16 → (catSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, biteSelectorBytes]
    simpa [catSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, boxSelectorBytes]
    simpa [catSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, cageSelectorBytes]
    simpa [catSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, clawSelectorBytes]
    simpa [catSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, denySelectorBytes]
    simpa [catSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, fileAddressSelectorBytes]
    simpa [catSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, fileIlkFlipSelectorBytes]
    simpa [catSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, fileIlkUintSelectorBytes]
    simpa [catSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, fileUintSelectorBytes]
    simpa [catSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, ilksSelectorBytes]
    simpa [catSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, litterSelectorBytes]
    simpa [catSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, liveSelectorBytes]
    simpa [catSelBytes] using hnm 11 (by omega)
  · rw [selectorOf, relySelectorBytes]
    simpa [catSelBytes] using hnm 12 (by omega)
  · rw [selectorOf, vatSelectorBytes]
    simpa [catSelBytes] using hnm 13 (by omega)
  · rw [selectorOf, vowSelectorBytes]
    simpa [catSelBytes] using hnm 14 (by omega)
  · rw [selectorOf, wardsSelectorBytes]
    simpa [catSelBytes] using hnm 15 (by omega)

theorem catBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

/-! ## No-selector-match revert paths -/

theorem catJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256}
    {k C : ℕ}
    (h : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode catBytecode pc = some (.Push .PUSH2, some (catDispatchRevertPc, 2)))
    (hjump : decode catBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h256 := h.push2 catDispatchRevertPc hpush (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.uniswapPush1Dup1Revert0 h256 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem catLowLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) catLowLowFirstArmPc
      [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowLowFirstArmPc j))
        (catSelWord I) = ⟨0⟩) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h256 := h
    |>.selectorArmNotTakenAuto (catLowLowArmsWellFormed 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (catLowLowArmsWellFormed 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (catLowLowArmsWellFormed 2 (by omega)) (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (catLowLowArmsWellFormed 3 (by omega)) (heq0 3 (by omega)) (by simp)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.uniswapPush1Dup1Revert0 h256 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem catLowHighNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) catLowHighFirstArmPc
      [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowHighFirstArmPc j))
        (catSelWord I) = ⟨0⟩) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have htail := h
    |>.selectorArmNotTakenAuto (catLowHighArmsWellFormed 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (catLowHighArmsWellFormed 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (catLowHighArmsWellFormed 2 (by omega)) (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (catLowHighArmsWellFormed 3 (by omega)) (heq0 3 (by omega)) (by simp)
  exact catJumpToNoMatchRevert htail (by native_decide) (by native_decide)

theorem catHighLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) catHighLowFirstArmPc
      [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighLowFirstArmPc j))
        (catSelWord I) = ⟨0⟩) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have htail := h
    |>.selectorArmNotTakenAuto (catHighLowArmsWellFormed 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (catHighLowArmsWellFormed 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (catHighLowArmsWellFormed 2 (by omega)) (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (catHighLowArmsWellFormed 3 (by omega)) (heq0 3 (by omega)) (by simp)
  exact catJumpToNoMatchRevert htail (by native_decide) (by native_decide)

theorem catHighHighNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) catHighHighFirstArmPc
      [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighHighFirstArmPc j))
        (catSelWord I) = ⟨0⟩) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have htail := h
    |>.selectorArmNotTakenAuto (catHighHighArmsWellFormed 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (catHighHighArmsWellFormed 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (catHighHighArmsWellFormed 2 (by omega)) (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (catHighHighArmsWellFormed 3 (by omega)) (heq0 3 (by omega)) (by simp)
  exact catJumpToNoMatchRevert htail (by native_decide) (by native_decide)

theorem catX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 16 → (catSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLowLow : ∀ j, j < 4 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowLowFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [catLowLowArmEq I hsz 0 (by omega)]
      have hfalse : (catLowLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [catLowLowSelBytes, catSelBytes] using hnm 7 (by omega)
      rw [hfalse]; rfl
    · rw [catLowLowArmEq I hsz 1 (by omega)]
      have hfalse : (catLowLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [catLowLowSelBytes, catSelBytes] using hnm 8 (by omega)
      rw [hfalse]; rfl
    · rw [catLowLowArmEq I hsz 2 (by omega)]
      have hfalse : (catLowLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [catLowLowSelBytes, catSelBytes] using hnm 13 (by omega)
      rw [hfalse]; rfl
    · rw [catLowLowArmEq I hsz 3 (by omega)]
      have hfalse : (catLowLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [catLowLowSelBytes, catSelBytes] using hnm 0 (by omega)
      rw [hfalse]; rfl
  have heqLowHigh : ∀ j, j < 4 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowHighFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [catLowHighArmEq I hsz 0 (by omega)]
      have hfalse : (catLowHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [catLowHighSelBytes, catSelBytes] using hnm 14 (by omega)
      rw [hfalse]; rfl
    · rw [catLowHighArmEq I hsz 1 (by omega)]
      have hfalse : (catLowHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [catLowHighSelBytes, catSelBytes] using hnm 12 (by omega)
      rw [hfalse]; rfl
    · rw [catLowHighArmEq I hsz 2 (by omega)]
      have hfalse : (catLowHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [catLowHighSelBytes, catSelBytes] using hnm 2 (by omega)
      rw [hfalse]; rfl
    · rw [catLowHighArmEq I hsz 3 (by omega)]
      have hfalse : (catLowHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [catLowHighSelBytes, catSelBytes] using hnm 1 (by omega)
      rw [hfalse]; rfl
  have heqHighLow : ∀ j, j < 4 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighLowFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [catHighLowArmEq I hsz 0 (by omega)]
      have hfalse : (catHighLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [catHighLowSelBytes, catSelBytes] using hnm 11 (by omega)
      rw [hfalse]; rfl
    · rw [catHighLowArmEq I hsz 1 (by omega)]
      have hfalse : (catHighLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [catHighLowSelBytes, catSelBytes] using hnm 4 (by omega)
      rw [hfalse]; rfl
    · rw [catHighLowArmEq I hsz 2 (by omega)]
      have hfalse : (catHighLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [catHighLowSelBytes, catSelBytes] using hnm 10 (by omega)
      rw [hfalse]; rfl
    · rw [catHighLowArmEq I hsz 3 (by omega)]
      have hfalse : (catHighLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [catHighLowSelBytes, catSelBytes] using hnm 15 (by omega)
      rw [hfalse]; rfl
  have heqHighHigh : ∀ j, j < 4 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighHighFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [catHighHighArmEq I hsz 0 (by omega)]
      have hfalse : (catHighHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [catHighHighSelBytes, catSelBytes] using hnm 5 (by omega)
      rw [hfalse]; rfl
    · rw [catHighHighArmEq I hsz 1 (by omega)]
      have hfalse : (catHighHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [catHighHighSelBytes, catSelBytes] using hnm 9 (by omega)
      rw [hfalse]; rfl
    · rw [catHighHighArmEq I hsz 2 (by omega)]
      have hfalse : (catHighHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [catHighHighSelBytes, catSelBytes] using hnm 3 (by omega)
      rw [hfalse]; rfl
    · rw [catHighHighArmEq I hsz 3 (by omega)]
      have hfalse : (catHighHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [catHighHighSelBytes, catSelBytes] using hnm 6 (by omega)
      rw [hfalse]; rfl
  by_cases hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) ≠ ⟨0⟩
  · by_cases hlow : UInt256.gt (armSelNat catBytecode catLowSplitPc) (catSelWord I) ≠ ⟨0⟩
    · obtain ⟨_, _, hfirst⟩ :=
        catReachLowLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
      exact catLowLowNoMatchRevert hfirst heqLowLow
    · have hlow0 : UInt256.gt (armSelNat catBytecode catLowSplitPc) (catSelWord I) = ⟨0⟩ := by
        by_contra hne; exact hlow hne
      obtain ⟨_, _, hfirst⟩ :=
        catReachLowHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow0
      exact catLowHighNoMatchRevert hfirst heqLowHigh
  · have hroot0 : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) = ⟨0⟩ := by
      by_contra hne; exact hroot hne
    by_cases hhigh : UInt256.gt (armSelNat catBytecode catHighSplitPc) (catSelWord I) ≠ ⟨0⟩
    · obtain ⟨_, _, hfirst⟩ :=
        catReachHighLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hhigh
      exact catHighLowNoMatchRevert hfirst heqHighLow
    · have hhigh0 : UInt256.gt (armSelNat catBytecode catHighSplitPc) (catSelWord I) = ⟨0⟩ := by
        by_contra hne; exact hhigh hne
      obtain ⟨_, _, hfirst⟩ :=
        catReachHighHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hhigh0
      exact catHighHighNoMatchRevert hfirst heqHighHigh

end Benchmarks.Dss.Cat
