import Tests.Pipeline.VyperWrapper.Dispatch
import Reasoning.VyperBounded
import Reasoning.ExternalCall
import Reasoning.Immutables

variable {fork : Ethereum.Fork}

/-!
# Wrapper proof helpers

The typed-storage precondition (`storageWF`: the `hook` word is a canonical address), the frame of
a transition body, the immutable `TOKEN` as a value and as the code suffix, entry guards, the
first calldata word, the `shares` mapping slots and the hash scratch the bytecode builds for them,
calldata decoding, and frame-generic evaluation facts.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperBounded
open Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperWrapper

set_option maxRecDepth 2000000

/-- Every message call this contract makes from the account map `σ` leaves `hook` (slot 0) a
canonical address word.  `wrap` re-reads `hook` after `TOKEN.transferFrom`, so the spec's `address`
view of the slot must agree with the raw word after the callee ran; the contract's own `setHook`
only stores validated words, which this clause records for arbitrary (possibly re-entrant)
callees. -/
def hookStableAcrossCalls (fork : Ethereum.Fork) (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  ∀ (σ₀ : AccountMap) (A_in : Substate) (r : AccountAddress) (c : ToExecute) (callGas p v v' : UInt256)
    (d : ByteArray) (e : Fin 1025) (H : BlockHeader) (blob : List ByteArray) (blocks : ProcessedBlocks) (w : Bool)
    (σ' : AccountMap) (g' : UInt256) (A' : Substate) (z : Bool) (out : ByteArray),
    (σ', g', A', z, out) = Ethereum.EVM.Θ fork σ σ₀ A_in (AccountAddress.ofUInt256 (UInt256.ofNat
      I.codeOwner)) I.sender
      r c callGas p v v' d e H blob blocks w →
    (solcSlotWordAt ⟨0⟩ σ' I).toNat < EVM.addressModulus

/-- The storage precondition: `hook` (slot 0) holds a canonical address word (Vyper compares and
returns the raw word; the spec's `address` view agrees only for canonical words, and `setHook`,
the only writer, stores a validated word); the caller's `shares` slot is not slot 0 (hash
non-collision, so `wrap`'s `shares` store leaves `hook` alone); and `hook` stays canonical across
the external calls `wrap` makes, under every fork (`hookStableAcrossCalls`). -/
def storageWF : StorageWF := fun σ I =>
  (solcSlotWordAt ⟨0⟩ σ I).toNat < EVM.addressModulus ∧
  vyperMappingSlot (UInt256.ofNat 1) (.address I.source) ≠ ⟨0⟩ ∧
  ∀ fork, hookStableAcrossCalls fork σ I

/-- The frame of a transition body run with the deployed immutables. -/
abbrev frame (imms locals : Store) : Frame :=
  { contract := contract, locals := locals, immutables := restrictImmutables contract imms }

/-! ## The immutable `TOKEN` -/

theorem token_of_fit {imms : Store} (h : immutablesFit contract imms) :
    ∃ a : AccountAddress, imms.get? "TOKEN" = some (.address a) := by
  obtain ⟨v, hget, hfits⟩ := h ⟨"TOKEN", .address⟩ (by decide)
  cases v <;> simp [elemValueFits] at hfits
  exact ⟨_, hget⟩

theorem wordsOf_TOKEN {imms : Store} {a : AccountAddress}
    (hget : imms.get? "TOKEN" = some (.address a)) :
    wordsOf imms "TOKEN" = EVM.Word.ofNat a.toNat := by
  unfold wordsOf
  rw [hget]
  simp [scalarBytes?, valueToWord, uInt256OfByteArray_toByteArray]

/-- The immutable section is the single word of `TOKEN`. -/
theorem suffixWords_TOKEN (w : String → UInt256) :
    immutableLayout.suffixWords w = (w "TOKEN").toByteArray := by
  have hslots : immutableLayout.slots.map (fun slot => (slot.offset, (w slot.name).toByteArray)) =
      [] ++ (0, (w "TOKEN").toByteArray) :: [] := by rfl
  have hpatch : ∃ suffix, Stele.patchRuntime (ByteArray.zeroes immutableLayout.size)
      (immutableLayout.slots.map (fun slot => (slot.offset, (w slot.name).toByteArray))) =
      some suffix := by
    simp only [immutableLayout, List.map_cons, List.map_nil]
    simp [Stele.patchRuntime, Stele.spliceBytes?, ByteArray.size_append,
      ByteArray.size_extract, ByteArray_zeroes_size, toByteArray_size]
  have h := Layout.suffixWords_read_slot (layout := immutableLayout) (words := w) (name := "TOKEN")
    (offset := 0) (pre := []) (post := []) hslots (by decide) (by intro p hp; simp at hp) hpatch
  have hsize : (immutableLayout.suffixWords w).size = 32 := Layout.suffixWords_size _ _
  rw [readWithPadding_eq_extract _ _ (by rw [hsize]), Nat.zero_add, ← hsize,
    byteArray_extract_self] at h
  exact h

theorem evalImmutable_TOKEN {imms : Store} {a : AccountAddress}
    (hget : imms.get? "TOKEN" = some (.address a)) (locals : Store) (evm : EVM.State) :
    evalExpr? config (frame imms locals) evm (.immutable "TOKEN") = .ok (.address a) := by
  simp only [evalExpr?, frame]
  rw [Reasoning.Immutables.restrictImmutables_get? (contract := contract) (n := "TOKEN") (by decide), hget]
  rfl

/-- The storage word the summaries read is the layout word of the initial account map. -/
theorem slotWord_eq (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) :
    (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD slot ⟨0⟩)) =
      solcSlotWordAt slot σ I := rfl

/-! ## Entry guards and the first argument -/

abbrev argWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)

theorem argWord_eq (I : ExecutionEnv) : argWord I = calldataWord I.calldata 4 := by
  show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32) = _
  rw [ulit_toNat' 4 (by decide)]

theorem guard_ok {I : ExecutionEnv} (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    UInt256.lor I.weiValue (UInt256.lt (UInt256.ofNat I.calldata.size) (UInt256.ofNat 36)) =
      UInt256.ofNat 0 := by
  rw [hwv, calldataSizeGuardOk hsz hsize]; decide

theorem guard_short {I : ExecutionEnv} (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36) :
    UInt256.lor I.weiValue (UInt256.lt (UInt256.ofNat I.calldata.size) (UInt256.ofNat 36)) ≠
      UInt256.ofNat 0 := by
  rw [calldataSizeGuardShort hsize (by decide) hshort]
  exact u256_lor_ne_zero_right (by decide)

theorem guard_wv {I : ExecutionEnv} {x : UInt256} (hwv : I.weiValue ≠ ⟨0⟩) :
    UInt256.lor I.weiValue x ≠ UInt256.ofNat 0 := by
  rw [u256_lor_comm]; exact u256_lor_ne_zero_right hwv

theorem dispatchMem_size (m : Nat) (hm : m < 8) : (wrapperDispatchMem m).size = 32 := by
  interval_cases m <;> native_decide

/-! ## Address words -/

theorem word_roundtrip {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.ofNat (AccountAddress.ofNat w.toNat).val = w := by
  have h := keyValueToWord_address_of_canonical w hcanon
  rw [Reasoning.Theory.keyValueToWord_address] at h
  exact h

theorem addr_eq_iff_word {a : AccountAddress} {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    (a = AccountAddress.ofNat w.toNat) ↔ (UInt256.ofNat a.val = w) := by
  constructor
  · intro h
    subst h
    exact word_roundtrip hcanon
  · intro h
    rw [← h, ulit_toNat' _ (lt_trans a.isLt (by decide)), accountAddress_ofNat_val]

/-- A canonical word denotes the zero address exactly when it is zero. -/
theorem addrZero_iff_word {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    (AccountAddress.ofNat w.toNat = AccountAddress.ofNat 0) ↔ w = ⟨0⟩ := by
  rw [eq_comm, addr_eq_iff_word hcanon]
  constructor
  · intro h; rw [← h]; decide
  · intro h; rw [h]; decide

/-! ## The `shares` mapping -/

/-- The slot of `shares[a]`. -/
abbrev sharesSlot (a : AccountAddress) : UInt256 := vyperMappingSlot (UInt256.ofNat 1) (.address a)

/-- `keccak256(1 ++ caller)` of the scratch the bytecode writes over any memory of 64 bytes. -/
theorem keccak_caller_over (M : ByteArray) (hM : 64 ≤ M.size) (I : ExecutionEnv) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
      ((UInt256.ofNat 1).toByteArray.write 0 ((UInt256.ofNat I.source.val).toByteArray.write 0 M 32 32) 0 32) =
      sharesSlot I.source := by
  unfold keccakWord
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, ulit_toNat' 64 (by decide)]
  have h := wordAt0Mem_wordAt32Mem_vyperMappingSlot (UInt256.ofNat 1) (.address I.source) (mem := M) hM
  rw [Reasoning.Theory.keyValueToWord_address] at h
  exact h

/-- `keccak256(1 ++ w)` of the scratch written over any memory of 64 bytes, for a canonical `w`. -/
theorem keccak_addr_over (M : ByteArray) (hM : 64 ≤ M.size) (w : UInt256) (hcanon : w.toNat < EVM.addressModulus) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
      ((UInt256.ofNat 1).toByteArray.write 0 (w.toByteArray.write 0 M 32 32) 0 32) =
      sharesSlot (AccountAddress.ofNat w.toNat) := by
  unfold keccakWord
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, ulit_toNat' 64 (by decide)]
  have h := wordAt0Mem_wordAt32Mem_vyperMappingSlot (UInt256.ofNat 1) (.address (AccountAddress.ofNat w.toNat)) (mem := M) hM
  rwa [keyValueToWord_address_of_canonical w hcanon] at h

/-! ## Calldata decoding -/

theorem decodeMode_uint256_ok (name : Ident) (cd : ByteArray) (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.vyper [name] [abiUInt256] cd =
      some ((∅ : Store).insert name (uint256Value (calldataWord cd 4))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide), if_neg (by rw [htlen]; omega),
    decodeScalarWords_uint256_ok htake4]
  simp [decodeCalldata.insertValues, hword4] <;> rfl

theorem decodeMode_uint256_none_short (name : Ident) (cd : ByteArray) (hsz : 4 ≤ cd.size)
    (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.vyper [name] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide), if_neg (by rw [htlen]; omega),
    decodeScalarWords_uint256_none_short (by rw [List.length_drop, htlen]; omega)]

/-! ## Frame-generic evaluation -/

theorem evalVar (imms L : Store) (evm : EVM.State) (name : Ident) (v : Value)
    (h : L.get? name = some v) : evalExpr? config (frame imms L) evm (.var name) = .ok v := by
  rw [evalExpr?]
  show EvalResult.ofOption _ (L.get? name) = _
  rw [h]; rfl

theorem evalThis {cfg : Config} {stele : Frame} (evm : EVM.State) :
    evalExpr? cfg stele evm (.env .this) = .ok (.address evm.executionEnv.codeOwner) := by
  rw [evalExpr?]; rfl

abbrev hookRef : StorageRef := { base := "hook", steps := [] }
abbrev tsRef : StorageRef := { base := "totalShares", steps := [] }

/-- `hook` as the spec reads it: the address the raw word denotes. -/
theorem evalHookRead (imms L : Store) (evm : EVM.State) (hL : L.get? "hook" = none) :
    evalExpr? config (frame imms L) evm (.storage hookRef) =
      .ok (.address (AccountAddress.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)) := by
  rw [evalExpr_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl) (t := .address)
      (er := { base := "hook", steps := [] }) (loc := vyperWordLoc ⟨0⟩ .address) (hbase := hL)
      (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl),
    storageLocLoad_vyperWord]
  rfl

theorem evalAddrZero (imms L : Store) (evm : EVM.State) :
    evalExpr? config (frame imms L) evm (.cast (.intLit 0) (.elem .address)) = .ok (.address (AccountAddress.ofNat 0)) := by
  simp [evalExpr?, castValue?, EvalResult.bind, bind, pure, EvalResult.ofOption]

/-- `totalShares` as the spec reads it. -/
theorem evalTsRead (imms L : Store) (evm : EVM.State) (hL : L.get? "totalShares" = none) :
    evalExpr? config (frame imms L) evm (.storage tsRef) =
      .ok (uint256Value (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2))) := by
  rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "totalShares", steps := [] }) (physicalSlot := UInt256.ofNat 2) (hbase := hL)
      (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl)]

/-- `shares[msg.sender]` as the spec reads it. -/
theorem evalSharesCallerRead (imms L : Store) (evm : EVM.State) (hL : L.get? "shares" = none) :
    evalExpr? config (frame imms L) evm (.storage { base := "shares", steps := [.mindex (.env .caller)] }) =
      .ok (uint256Value (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (sharesSlot evm.executionEnv.source))) := by
  rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
      (er := { base := "shares", steps := [.mindex (.address evm.executionEnv.source)] })
      (physicalSlot := sharesSlot evm.executionEnv.source) (hbase := hL)
      (her := by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
        EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, envValue])
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, Syntax.contractSyntax])
      (hloc := rfl)]

end Tests.Pipeline.VyperWrapper
