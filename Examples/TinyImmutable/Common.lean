import Solm.Refine
import Reasoning.SolmBody
import Reasoning.WordArithmetic
import Examples.TinyImmutable.Selectors
import Examples.TinyImmutable.ImmutableCode
import Reasoning.Dispatch
import Reasoning.Initcode
import Reasoning.MemCascade
import Reasoning.Solc
import Reasoning.Immutables

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open TinyImmutable.Immutables

namespace TinyImmutable

set_option maxRecDepth 10000


@[simp] theorem tinyImmutableBytecode_size : tinyImmutableBytecode.size = 432 := by
  native_decide +revert

@[simp] theorem tinyImmutableCreationBytecode_size :
    tinyImmutableCreationBytecode.size = 634 := by
  native_decide +revert

/-- The immutables a contract deployed with `v` runs with. -/
def immStore (v : TinyImmutables) : Store :=
  ((∅ : Store).insert "owner" (.address v.owner)).insert "scale" (.int (Int.ofNat v.scale.toNat))

@[simp] theorem immStore_get_owner (v : TinyImmutables) :
    (immStore v).get? "owner" = some (.address v.owner) := by
  grind [immStore]

@[simp] theorem immStore_get_scale (v : TinyImmutables) :
    (immStore v).get? "scale" = some (.int (Int.ofNat v.scale.toNat)) := by
  grind [immStore]

@[simp] theorem wordsOf_immStore_owner (v : TinyImmutables) :
    wordsOf (immStore v) "owner" = EVM.Word.ofNat (↑v.owner : Nat) :=
  wordsOf_of_get (immStore_get_owner v) rfl

@[simp] theorem wordsOf_immStore_scale (v : TinyImmutables) :
    wordsOf (immStore v) "scale" = EVM.wordOfInt (Int.ofNat v.scale.toNat) :=
  wordsOf_of_get (immStore_get_scale v) rfl

def runtimeWrites (v : TinyImmutables) : List (Nat × UInt256) :=
  immutableLayout.writes (wordsOf (immStore v))

/-- The runtime deployed with the immutables `v`. -/
def deployedRuntime (v : TinyImmutables) : ByteArray :=
  immutableLayout.deployed tinyImmutableBytecode (immStore v)

abbrev tinyFirstArmPc : UInt256 := ⟨30⟩

theorem evalImmutable_owner (cfg : Config) (C : ContractDecl) (locals : Store) (evm : EVM.State)
    (v : TinyImmutables) :
    evalExpr? cfg { contract := C, locals := locals, immutables := immStore v } evm
      (.immutable "owner") = .ok (.address v.owner) := by
  simp only [evalExpr?, immStore_get_owner, EvalResult.ofOption]

theorem evalImmutable_scale (cfg : Config) (C : ContractDecl) (locals : Store) (evm : EVM.State)
    (v : TinyImmutables) :
    evalExpr? cfg { contract := C, locals := locals, immutables := immStore v } evm
      (.immutable "scale") = .ok (.int (Int.ofNat v.scale.toNat)) := by
  simp only [evalExpr?, immStore_get_scale, EvalResult.ofOption]

/-- Every patch site is a declared immutable. -/
theorem immutableLayout_keys :
    ∀ site ∈ immutableLayout.sites, site.2.2 ∈ contract.immutables.map (·.name) := by
  decide

/-- A well-typed immutables store runs as the store of some valuation. -/
theorem restrictImmutables_of_fit {imms : Store} (h : immutablesFit contract imms) :
    ∃ v, restrictImmutables contract imms = immStore v := by
  obtain ⟨vo, hvo, hfo⟩ := h ⟨"owner", .address⟩ (by simp [contract])
  obtain ⟨vs, hvs, hfs⟩ := h ⟨"scale", .int uint256Int⟩ (by simp [contract])
  simp only at hvo hvs
  cases vo <;> simp [elemValueFits] at hfo
  cases vs <;> simp [elemValueFits, uint256Int] at hfs
  rename_i a i
  have hword : (EVM.word i.toNat).toNat = i.toNat :=
    constructorUInt256Word_toNat i hfs.1 (by simpa [EVM.twoPow] using hfs.2)
  have hi : Int.ofNat i.toNat = i := Int.toNat_of_nonneg hfs.1
  exact ⟨⟨a, EVM.word i.toNat⟩,
    by simp only [restrictImmutables, contract, List.foldl, immStore, hvo, hvs, hword, hi]⟩

theorem ownerSelBytes_size : ownerSelBytes.size = 4 := rfl
theorem quoteSelBytes_size : quoteSelBytes.size = 4 := rfl
theorem scaleSelBytes_size : scaleSelBytes.size = 4 := rfl

theorem accountAddress_ofNat_toNat (a : AccountAddress) :
    AccountAddress.ofNat a.toNat = a := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [Fin.val_ofNat]
  exact Nat.mod_eq_of_lt a.isLt

theorem accountAddress_ofNat_val (a : AccountAddress) :
    AccountAddress.ofNat (↑a : Nat) = a :=
  accountAddress_ofNat_toNat a

theorem deployedRuntime_size (v : TinyImmutables) : (deployedRuntime v).size = 432 := by
  unfold deployedRuntime Layout.deployed
  exact writeCascade_size_of_base tinyImmutableBytecode (runtimeWrites v) (base := 432) (out := 432)
    (by native_decide)
    (by simp [runtimeWrites, Layout.writes, immutableLayout, immutableReferences, WriteGapsOk])
    (by simp [runtimeWrites, Layout.writes, immutableLayout, immutableReferences,
      writeCascadeSize])

theorem tinyDispatch_none_short (v : TinyImmutables) {cd : ByteArray}
    (hcd : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd]
  refine dispatchList_none_short transitions ?_ hcd
  intro t ht
  simp [transitions] at ht
  rcases ht with ht | ht | ht
  · subst t
    rw [ownerSelectorOf, ownerSelBytes_size]
  · subst t
    rw [quoteSelectorOf, quoteSelBytes_size]
  · subst t
    rw [scaleSelectorOf, scaleSelBytes_size]

theorem tinyDispatch_owner (v : TinyImmutables) {cd : ByteArray}
    (hmatch : (ownerSelBytes == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some ownerTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := []) (post := [quoteTransition, scaleTransition])
    (ti := ownerTransition) (cd := cd) (by rfl) ?_ ?_ ?_ (by rfl)
  · simp [contract, transitions]
  · intro t ht
    simp at ht
  · rw [ownerSelectorOf]
    exact hmatch

theorem tinyDispatch_quote (v : TinyImmutables) {cd : ByteArray}
    (howner : (ownerSelBytes == cd.extract 0 4) = false)
    (hmatch : (quoteSelBytes == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some quoteTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [ownerTransition]) (post := [scaleTransition])
    (ti := quoteTransition) (cd := cd) (by rfl) ?_ ?_ ?_ (by rfl)
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    subst t
    rw [ownerSelectorOf]
    exact howner
  · rw [quoteSelectorOf]
    exact hmatch

theorem tinyDispatch_scale (v : TinyImmutables) {cd : ByteArray}
    (howner : (ownerSelBytes == cd.extract 0 4) = false)
    (hquote : (quoteSelBytes == cd.extract 0 4) = false)
    (hmatch : (scaleSelBytes == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some scaleTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre := [ownerTransition, quoteTransition]) (post := [])
    (ti := scaleTransition) (cd := cd) (by rfl) ?_ ?_ ?_ (by rfl)
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with ht | ht
    · subst t
      rw [ownerSelectorOf]
      exact howner
    · subst t
      rw [quoteSelectorOf]
      exact hquote
  · rw [scaleSelectorOf]
    exact hmatch

theorem tinyDispatch_none_nomatch (v : TinyImmutables) {cd : ByteArray}
    (howner : (ownerSelBytes == cd.extract 0 4) = false)
    (hquote : (quoteSelBytes == cd.extract 0 4) = false)
    (hscale : (scaleSelBytes == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  refine dispatchMsg_none_of_all_ne (contract := contract) (cd := cd) (by rfl) (by rfl) ?_
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with ht | ht | ht
  · subst t
    rw [ownerSelectorOf]
    exact howner
  · subst t
    rw [quoteSelectorOf]
    exact hquote
  · subst t
    rw [scaleSelectorOf]
    exact hscale

theorem tinyOwnerSelector_size {I : ExecutionEnv}
    (hsel : (ownerSelBytes == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  rw [ownerSelBytes_size, ByteArray.size_extract] at hs
  omega

theorem tinyQuoteSelector_size {I : ExecutionEnv}
    (hsel : (quoteSelBytes == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  rw [quoteSelBytes_size, ByteArray.size_extract] at hs
  omega

theorem tinyScaleSelector_size {I : ExecutionEnv}
    (hsel : (scaleSelBytes == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  rw [scaleSelBytes_size, ByteArray.size_extract] at hs
  omega

/-- The patched runtime has the template's jump destinations: patch sites are push payloads,
    which the `D_J` scan skips. -/
theorem tinyPatchedValidJumps (v : TinyImmutables) :
    D_J (deployedRuntime v) 0 = D_J tinyImmutableBytecode 0 :=
  Layout.D_J_runtime (by native_decide) (by native_decide)

theorem tinyContains15 (v : TinyImmutables) :
    (D_J (deployedRuntime v) 0).contains ⟨15⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains63 (v : TinyImmutables) :
    (D_J (deployedRuntime v) 0).contains ⟨63⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains67 (v : TinyImmutables) :
    (D_J (deployedRuntime v) 0).contains ⟨67⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains106 (v : TinyImmutables) :
    (D_J (deployedRuntime v) 0).contains ⟨106⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains139 (v : TinyImmutables) :
    (D_J (deployedRuntime v) 0).contains ⟨139⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains148 (v : TinyImmutables) :
    (D_J (deployedRuntime v) 0).contains ⟨148⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains162 (v : TinyImmutables) :
    (D_J (deployedRuntime v) 0).contains ⟨162⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains167 (v : TinyImmutables) :
    (D_J (deployedRuntime v) 0).contains ⟨167⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains181 (v : TinyImmutables) :
    (D_J (deployedRuntime v) 0).contains ⟨181⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains220 (v : TinyImmutables) :
    (D_J (deployedRuntime v) 0).contains ⟨220⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains358 (v : TinyImmutables) :
    (D_J (deployedRuntime v) 0).contains ⟨358⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains396 (v : TinyImmutables) :
    (D_J (deployedRuntime v) 0).contains ⟨396⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains412 (v : TinyImmutables) :
    (D_J (deployedRuntime v) 0).contains ⟨412⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyOwnerEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨2376452955⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if (ownerSelBytes == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0x8d 0xa5 0xcb 0x5b ⟨2376452955⟩ (by decide)

theorem tinyQuoteEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨3978024812⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if (quoteSelBytes == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0xed 0x1b 0xd7 0x6c ⟨3978024812⟩ (by decide)

theorem tinyScaleEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨4112390170⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if (scaleSelBytes == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0xf5 0x1e 0x18 0x1a ⟨4112390170⟩ (by decide)

theorem tinyOwnerWord_canonical (v : TinyImmutables) :
    (EVM.Word.ofNat (↑v.owner : Nat)).toNat < EVM.addressModulus := by
  change (UInt256.ofNat v.owner.val).toNat < EVM.addressModulus
  rw [UInt256.toNat_ofNat_of_lt]
  · change v.owner.val < AccountAddress.size
    exact v.owner.isLt
  · exact lt_of_lt_of_le v.owner.isLt (by decide)

theorem tinyOwnerWord_toNat (v : TinyImmutables) :
    (EVM.Word.ofNat (↑v.owner : Nat)).toNat = (↑v.owner : Nat) := by
  change (UInt256.ofNat v.owner.val).toNat = v.owner.val
  rw [UInt256.toNat_ofNat_of_lt]
  exact lt_of_lt_of_le v.owner.isLt (by decide)

theorem tinyOwnerWord_clean (v : TinyImmutables) :
    UInt256.land (EVM.Word.ofNat (↑v.owner : Nat)) solcAddrMask =
      EVM.Word.ofNat (↑v.owner : Nat) :=
  solcAddrMask_clean (tinyOwnerWord_canonical v)

end TinyImmutable
