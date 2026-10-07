import Solm.Refine
import Examples.TinyImmutable.Selectors
import Examples.TinyImmutable.ImmutableCode
import Reasoning.Dispatch
import Reasoning.Initcode
import Reasoning.MemCascade
import Reasoning.Solc

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open TinyImmutable.Immutables

namespace TinyImmutable

set_option maxRecDepth 10000

@[simp] theorem wordBytesBEArray_size (w : UInt256) :
    ({ data := (EVM.Word.toBytesBE w).toArray } : ByteArray).size = 32 := by
  simpa using word_toBytesBE_toByteArray_size w

@[simp] theorem wordBytesBEArray_eq_toByteArray (w : UInt256) :
    ({ data := (EVM.Word.toBytesBE w).toArray } : ByteArray) = UInt256.toByteArray w := by
  apply ByteArray.ext
  have h := congrArg ByteArray.data (word_toBytesBE_toByteArray_eq_toByteArray w)
  simpa using h

@[simp] theorem tinyImmutableBytecode_size : tinyImmutableBytecode.size = 432 := by
  native_decide +revert

@[simp] theorem tinyImmutableCreationBytecode_size :
    tinyImmutableCreationBytecode.size = 634 := by
  native_decide +revert

def runtimeWrites (v : TinyImmutables) : List (Nat × UInt256) :=
  immutableLayout.writes (immutableWords v)

def patchedRuntime (v : TinyImmutables) : ByteArray :=
  immutableLayout.runtime tinyImmutableBytecode (immutableWords v)

abbrev tinyFirstArmPc : UInt256 := ⟨30⟩

/-- The immutables a contract deployed with `v` runs with. -/
def immStore (v : TinyImmutables) : Store :=
  ((∅ : Store).insert "owner" (.address v.owner)).insert "scale" (.int (Int.ofNat v.scale.toNat))

@[simp] theorem immStore_get_owner (v : TinyImmutables) :
    (immStore v).get? "owner" = some (.address v.owner) := by
  grind [immStore]

@[simp] theorem immStore_get_scale (v : TinyImmutables) :
    (immStore v).get? "scale" = some (.int (Int.ofNat v.scale.toNat)) := by
  grind [immStore]

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

/-- The valuation an immutables store holds (zero for a missing or ill-typed entry). -/
def immsOf (imms : Store) : TinyImmutables :=
  { owner := match imms.get? "owner" with
      | some (.address a) => a
      | _ => AccountAddress.ofNat 0
    scale := match imms.get? "scale" with
      | some (.int i) => EVM.word i.toNat
      | _ => ⟨0⟩ }

/-- The runtime code deployed for an immutables store: solc's template, patched. -/
def deployedRuntime (imms : Store) : ByteArray :=
  patchedRuntime (immsOf imms)

/-- A well-typed immutables store runs as the store of the valuation it holds. -/
theorem restrictImmutables_of_fit {imms : Store} (h : immutablesFit contract imms) :
    restrictImmutables contract imms = immStore (immsOf imms) := by
  obtain ⟨vo, hvo, hfo⟩ := h ⟨"owner", .address⟩ (by simp [contract])
  obtain ⟨vs, hvs, hfs⟩ := h ⟨"scale", .int uint256Int⟩ (by simp [contract])
  simp only at hvo hvs
  cases vo <;> simp [elemValueFits] at hfo
  cases vs <;> simp [elemValueFits, uint256Int] at hfs
  rename_i a i
  have hword : (EVM.word i.toNat).toNat = i.toNat :=
    constructorUInt256Word_toNat i hfs.1 (by simpa [EVM.twoPow] using hfs.2)
  have hi : Int.ofNat i.toNat = i := Int.toNat_of_nonneg hfs.1
  simp only [restrictImmutables, contract, List.foldl, immStore, immsOf, hvo, hvs, hword, hi]

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

theorem spliceBytes_toByteArray_eq_writeWord (mem : ByteArray) (off : Nat) (w : UInt256)
    (h : off + 32 ≤ mem.size) :
    spliceBytes? mem off (UInt256.toByteArray w) = some (writeWord mem off w) := by
  unfold spliceBytes? Reasoning.Theory.writeWord
  rw [toByteArray_size, if_pos h]
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  rw [toByteArray_extract_all]

theorem patchRuntime_eq_patchedRuntime (v : TinyImmutables) :
    patchRuntime tinyImmutableBytecode (patches v) = some (patchedRuntime v) := by
  simp [patchedRuntime, patchRuntime, patches, patchesFrom, offsets, immutableReferences,
    immutableLayout, Reasoning.Immutables.Layout.runtime, Reasoning.Immutables.Layout.writes,
    immutableWords, immValues, wordBytes?, valueToWord, List.lookup_cons]
  rw [spliceBytes_toByteArray_eq_writeWord tinyImmutableBytecode 186]
  · simp
    have hgap186 : 186 - tinyImmutableBytecode.size < USize.size := by
      rw [tinyImmutableBytecode_size]
      norm_num
    have hsize186 :
        (writeWord tinyImmutableBytecode 186
          (EVM.wordOfInt (Int.ofNat v.scale.toNat))).size = 432 := by
      rw [writeWord_size _ _ _ hgap186]
      rw [tinyImmutableBytecode_size]
      norm_num
    have h361 := spliceBytes_toByteArray_eq_writeWord
      (writeWord tinyImmutableBytecode 186 (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
      (EVM.wordOfInt (Int.ofNat v.scale.toNat))
      (by rw [hsize186]; norm_num)
    cases hsp361 : spliceBytes?
        (writeWord tinyImmutableBytecode 186 (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
        (UInt256.toByteArray (EVM.wordOfInt (Int.ofNat v.scale.toNat))) with
    | none =>
        rw [hsp361] at h361
        cases h361
    | some p361 =>
        rw [hsp361] at h361
        cases h361
        dsimp [Option.bind]
        have hgap361 :
            361 - (writeWord tinyImmutableBytecode 186
              (EVM.wordOfInt (Int.ofNat v.scale.toNat))).size < USize.size := by
          rw [hsize186]
          norm_num
        have hsize361 :
            (writeWord
              (writeWord tinyImmutableBytecode 186
                (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
              (EVM.wordOfInt (Int.ofNat v.scale.toNat))).size = 432 := by
          rw [writeWord_size _ _ _ hgap361]
          rw [hsize186]
          norm_num
        have h72 := spliceBytes_toByteArray_eq_writeWord
          (writeWord
            (writeWord tinyImmutableBytecode 186 (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
            (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 72
          (EVM.Word.ofNat (↑v.owner : Nat))
          (by rw [hsize361]; norm_num)
        cases hsp72 : spliceBytes?
            (writeWord
              (writeWord tinyImmutableBytecode 186 (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
              (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 72
            (UInt256.toByteArray (EVM.Word.ofNat (↑v.owner : Nat))) with
        | none =>
            rw [hsp72] at h72
            cases h72
        | some p72 =>
            rw [hsp72] at h72
            cases h72
            dsimp [Option.bind]
            have hgap72 :
                72 - (writeWord
                  (writeWord tinyImmutableBytecode 186
                    (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
                  (EVM.wordOfInt (Int.ofNat v.scale.toNat))).size < USize.size := by
              rw [hsize361]
              norm_num
            have hsize72 :
                (writeWord
                  (writeWord
                    (writeWord tinyImmutableBytecode 186
                      (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
                    (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 72
                  (EVM.Word.ofNat (↑v.owner : Nat))).size = 432 := by
              rw [writeWord_size _ _ _ hgap72]
              rw [hsize361]
              norm_num
            have h245 := spliceBytes_toByteArray_eq_writeWord
              (writeWord
                (writeWord
                  (writeWord tinyImmutableBytecode 186
                    (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
                  (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 72
                (EVM.Word.ofNat (↑v.owner : Nat))) 245
              (EVM.Word.ofNat (↑v.owner : Nat))
              (by rw [hsize72]; norm_num)
            cases hsp245 : spliceBytes?
                (writeWord
                  (writeWord
                    (writeWord tinyImmutableBytecode 186
                      (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
                    (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 72
                  (EVM.Word.ofNat (↑v.owner : Nat))) 245
                (UInt256.toByteArray (EVM.Word.ofNat (↑v.owner : Nat))) with
            | none =>
                rw [hsp245] at h245
                cases h245
            | some p245 =>
                rw [hsp245] at h245
                cases h245
                rfl
  · rw [tinyImmutableBytecode_size]
    norm_num

theorem code_eq_patchedRuntime_of_patch {v : TinyImmutables} {code : ByteArray}
    (hcode : patchRuntime tinyImmutableBytecode (patches v) = some code) :
    code = patchedRuntime v := by
  rw [patchRuntime_eq_patchedRuntime] at hcode
  cases hcode
  rfl

theorem patchedRuntime_size (v : TinyImmutables) : (patchedRuntime v).size = 432 := by
  unfold patchedRuntime
  exact writeCascade_size_of_base tinyImmutableBytecode (runtimeWrites v) (base := 432) (out := 432)
    (by native_decide)
    (by simp [runtimeWrites, Layout.writes, immutableLayout, immutableReferences, WriteGapsOk])
    (by simp [runtimeWrites, Layout.writes, immutableLayout, immutableReferences,
      writeCascadeSize])

theorem writeCascade_extract_preserved_len
    (mem : ByteArray) (writes : List (Nat × UInt256)) (read len : Nat)
    (hwin : WindowDisjointFromWrites mem.size read len writes)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hout : read + len ≤ (writeCascade mem writes).size)
    (hin : read + len ≤ mem.size) :
    (writeCascade mem writes).extract read (read + len) =
      mem.extract read (read + len) := by
  rw [← readWithPadding_eq_extract' (writeCascade mem writes) read len hpos hlen64 hout]
  rw [← readWithPadding_eq_extract' mem read len hpos hlen64 hin]
  exact writeCascade_read_preserved_len mem writes read len hwin hpos hlen64

theorem patchedRuntime_extract_preserved_len (v : TinyImmutables) (read len : Nat)
    (hwin : WindowDisjointFromWrites 432 read len (runtimeWrites v))
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) (hin : read + len ≤ 432) :
    (patchedRuntime v).extract read (read + len) =
      tinyImmutableBytecode.extract read (read + len) := by
  unfold patchedRuntime
  exact writeCascade_extract_preserved_len tinyImmutableBytecode (runtimeWrites v) read len
    (by simpa [tinyImmutableBytecode_size] using hwin) hpos hlen64
    (by change read + len ≤ (patchedRuntime v).size; rw [patchedRuntime_size v]; exact hin)
    (by rw [tinyImmutableBytecode_size]; exact hin)

theorem patchedRuntime_extract'_preserved_len (v : TinyImmutables) (read len : Nat)
    (hwin : WindowDisjointFromWrites 432 read len (runtimeWrites v))
    (hlen64 : read + len < 2 ^ 64) (hin : read + len ≤ 432) :
    (patchedRuntime v).extract' read (read + len) =
      tinyImmutableBytecode.extract' read (read + len) := by
  by_cases hpos : 0 < len
  · unfold ByteArray.extract'
    have hguard : (decide (read < 2 ^ 64) && decide (read + len < 2 ^ 64)) = true := by
      rw [decide_eq_true (by omega : read < 2 ^ 64), decide_eq_true hlen64]
      rfl
    rw [if_pos hguard, if_pos hguard]
    exact patchedRuntime_extract_preserved_len v read len hwin hpos (by omega) hin
  · have hlen0 : len = 0 := by omega
    subst hlen0
    simp [ByteArray.extract']

theorem get?_eq_of_extract_one (a b : ByteArray) (i : Nat) (ha : i < a.size) (hb : i < b.size)
    (h : a.extract i (i + 1) = b.extract i (i + 1)) :
    a.get? i = b.get? i := by
  unfold ByteArray.get?
  simp only [dif_pos ha, dif_pos hb]
  have h0 : (a.extract i (i + 1)).get? 0 = (b.extract i (i + 1)).get? 0 := by rw [h]
  unfold ByteArray.get? at h0
  have hsa : 0 < (a.extract i (i + 1)).size := by rw [ByteArray.size_extract]; omega
  have hsb : 0 < (b.extract i (i + 1)).size := by rw [ByteArray.size_extract]; omega
  simp only [dif_pos hsa, dif_pos hsb] at h0
  have hla : (a.extract i (i + 1)).get 0 hsa = a.get i ha := by
    change (a.extract i (i + 1))[0] = a[i]
    simpa using ByteArray.get_extract (a := a) (start := i) (stop := i + 1) (i := 0) hsa
  have hlb : (b.extract i (i + 1)).get 0 hsb = b.get i hb := by
    change (b.extract i (i + 1))[0] = b[i]
    simpa using ByteArray.get_extract (a := b) (start := i) (stop := i + 1) (i := 0) hsb
  rw [hla, hlb] at h0
  exact h0

theorem patchedRuntime_get?_preserved (v : TinyImmutables) (i : Nat)
    (hwin : WindowDisjointFromWrites 432 i 1 (runtimeWrites v)) (hi : i + 1 ≤ 432) :
    (patchedRuntime v).get? i = tinyImmutableBytecode.get? i := by
  exact get?_eq_of_extract_one (patchedRuntime v) tinyImmutableBytecode i
    (by rw [patchedRuntime_size v]; omega)
    (by rw [tinyImmutableBytecode_size]; omega)
    (patchedRuntime_extract_preserved_len v i 1 hwin (by norm_num) (by norm_num) hi)

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

syntax "tiny_parse_at " term "," term : tactic
macro_rules
  | `(tactic| tiny_parse_at $varg, $pc) =>
      `(tactic|
        (rw [patchedRuntime_get?_preserved $varg ($pc : Nat)
            (by norm_num [runtimeWrites, Layout.writes, immutableLayout, immutableReferences,
              WindowDisjointFromWrites])
            (by norm_num)];
          native_decide))

syntax "tiny_dj_step " term "," term "," term : tactic
macro_rules
  | `(tactic| tiny_dj_step $varg, $pc, $instr) =>
      `(tactic|
        (rw [D_J_aux_eq_some (patchedRuntime $varg) $pc _ $instr
            (by tiny_parse_at $varg, $pc)];
          simp [EVM.N, argOnNBytesOfInstr]))

theorem tinyPatchedValidJumps (v : TinyImmutables) :
    D_J (patchedRuntime v) 0 =
      #[⟨15⟩, ⟨63⟩, ⟨67⟩, ⟨106⟩, ⟨139⟩, ⟨148⟩, ⟨162⟩, ⟨167⟩, ⟨181⟩, ⟨220⟩,
        ⟨358⟩, ⟨396⟩, ⟨412⟩] := by
  unfold D_J
  tiny_dj_step v, 0, (.Push .PUSH1)
  tiny_dj_step v, 2, (.Push .PUSH1)
  tiny_dj_step v, 4, .MSTORE
  tiny_dj_step v, 5, .CALLVALUE
  tiny_dj_step v, 6, .DUP1
  tiny_dj_step v, 7, .ISZERO
  tiny_dj_step v, 8, (.Push .PUSH2)
  tiny_dj_step v, 11, .JUMPI
  tiny_dj_step v, 12, .PUSH0
  tiny_dj_step v, 13, .PUSH0
  tiny_dj_step v, 14, .REVERT
  tiny_dj_step v, 15, .JUMPDEST
  tiny_dj_step v, 16, .POP
  tiny_dj_step v, 17, (.Push .PUSH1)
  tiny_dj_step v, 19, .CALLDATASIZE
  tiny_dj_step v, 20, .LT
  tiny_dj_step v, 21, (.Push .PUSH2)
  tiny_dj_step v, 24, .JUMPI
  tiny_dj_step v, 25, .PUSH0
  tiny_dj_step v, 26, .CALLDATALOAD
  tiny_dj_step v, 27, (.Push .PUSH1)
  tiny_dj_step v, 29, .SHR
  tiny_dj_step v, 30, .DUP1
  tiny_dj_step v, 31, (.Push .PUSH4)
  tiny_dj_step v, 36, .EQ
  tiny_dj_step v, 37, (.Push .PUSH2)
  tiny_dj_step v, 40, .JUMPI
  tiny_dj_step v, 41, .DUP1
  tiny_dj_step v, 42, (.Push .PUSH4)
  tiny_dj_step v, 47, .EQ
  tiny_dj_step v, 48, (.Push .PUSH2)
  tiny_dj_step v, 51, .JUMPI
  tiny_dj_step v, 52, .DUP1
  tiny_dj_step v, 53, (.Push .PUSH4)
  tiny_dj_step v, 58, .EQ
  tiny_dj_step v, 59, (.Push .PUSH2)
  tiny_dj_step v, 62, .JUMPI
  tiny_dj_step v, 63, .JUMPDEST
  tiny_dj_step v, 64, .PUSH0
  tiny_dj_step v, 65, .PUSH0
  tiny_dj_step v, 66, .REVERT
  tiny_dj_step v, 67, .JUMPDEST
  tiny_dj_step v, 68, (.Push .PUSH2)
  tiny_dj_step v, 71, (.Push .PUSH32)
  tiny_dj_step v, 104, .DUP2
  tiny_dj_step v, 105, .JUMP
  tiny_dj_step v, 106, .JUMPDEST
  tiny_dj_step v, 107, (.Push .PUSH1)
  tiny_dj_step v, 109, .MLOAD
  tiny_dj_step v, 110, (.Push .PUSH20)
  tiny_dj_step v, 131, .SWAP1
  tiny_dj_step v, 132, .SWAP2
  tiny_dj_step v, 133, .AND
  tiny_dj_step v, 134, .DUP2
  tiny_dj_step v, 135, .MSTORE
  tiny_dj_step v, 136, (.Push .PUSH1)
  tiny_dj_step v, 138, .ADD
  tiny_dj_step v, 139, .JUMPDEST
  tiny_dj_step v, 140, (.Push .PUSH1)
  tiny_dj_step v, 142, .MLOAD
  tiny_dj_step v, 143, .DUP1
  tiny_dj_step v, 144, .SWAP2
  tiny_dj_step v, 145, .SUB
  tiny_dj_step v, 146, .SWAP1
  tiny_dj_step v, 147, .RETURN
  tiny_dj_step v, 148, .JUMPDEST
  tiny_dj_step v, 149, (.Push .PUSH2)
  tiny_dj_step v, 152, (.Push .PUSH2)
  tiny_dj_step v, 155, .CALLDATASIZE
  tiny_dj_step v, 156, (.Push .PUSH1)
  tiny_dj_step v, 158, (.Push .PUSH2)
  tiny_dj_step v, 161, .JUMP
  tiny_dj_step v, 162, .JUMPDEST
  tiny_dj_step v, 163, (.Push .PUSH2)
  tiny_dj_step v, 166, .JUMP
  tiny_dj_step v, 167, .JUMPDEST
  tiny_dj_step v, 168, (.Push .PUSH1)
  tiny_dj_step v, 170, .MLOAD
  tiny_dj_step v, 171, .SWAP1
  tiny_dj_step v, 172, .DUP2
  tiny_dj_step v, 173, .MSTORE
  tiny_dj_step v, 174, (.Push .PUSH1)
  tiny_dj_step v, 176, .ADD
  tiny_dj_step v, 177, (.Push .PUSH2)
  tiny_dj_step v, 180, .JUMP
  tiny_dj_step v, 181, .JUMPDEST
  tiny_dj_step v, 182, (.Push .PUSH2)
  tiny_dj_step v, 185, (.Push .PUSH32)
  tiny_dj_step v, 218, .DUP2
  tiny_dj_step v, 219, .JUMP
  tiny_dj_step v, 220, .JUMPDEST
  tiny_dj_step v, 221, .PUSH0
  tiny_dj_step v, 222, .CALLER
  tiny_dj_step v, 223, (.Push .PUSH20)
  tiny_dj_step v, 244, (.Push .PUSH32)
  tiny_dj_step v, 277, .AND
  tiny_dj_step v, 278, .EQ
  tiny_dj_step v, 279, (.Push .PUSH2)
  tiny_dj_step v, 282, .JUMPI
  tiny_dj_step v, 283, (.Push .PUSH1)
  tiny_dj_step v, 285, .MLOAD
  tiny_dj_step v, 286, (.Push .PUSH3)
  tiny_dj_step v, 290, (.Push .PUSH1)
  tiny_dj_step v, 292, .SHL
  tiny_dj_step v, 293, .DUP2
  tiny_dj_step v, 294, .MSTORE
  tiny_dj_step v, 295, (.Push .PUSH1)
  tiny_dj_step v, 297, (.Push .PUSH1)
  tiny_dj_step v, 299, .DUP3
  tiny_dj_step v, 300, .ADD
  tiny_dj_step v, 301, .MSTORE
  tiny_dj_step v, 302, (.Push .PUSH1)
  tiny_dj_step v, 304, (.Push .PUSH1)
  tiny_dj_step v, 306, .DUP3
  tiny_dj_step v, 307, .ADD
  tiny_dj_step v, 308, .MSTORE
  tiny_dj_step v, 309, (.Push .PUSH32)
  tiny_dj_step v, 342, (.Push .PUSH1)
  tiny_dj_step v, 344, .DUP3
  tiny_dj_step v, 345, .ADD
  tiny_dj_step v, 346, .MSTORE
  tiny_dj_step v, 347, (.Push .PUSH1)
  tiny_dj_step v, 349, .ADD
  tiny_dj_step v, 350, (.Push .PUSH1)
  tiny_dj_step v, 352, .MLOAD
  tiny_dj_step v, 353, .DUP1
  tiny_dj_step v, 354, .SWAP2
  tiny_dj_step v, 355, .SUB
  tiny_dj_step v, 356, .SWAP1
  tiny_dj_step v, 357, .REVERT
  tiny_dj_step v, 358, .JUMPDEST
  tiny_dj_step v, 359, .POP
  tiny_dj_step v, 360, (.Push .PUSH32)
  tiny_dj_step v, 393, .MUL
  tiny_dj_step v, 394, .SWAP1
  tiny_dj_step v, 395, .JUMP
  tiny_dj_step v, 396, .JUMPDEST
  tiny_dj_step v, 397, .PUSH0
  tiny_dj_step v, 398, (.Push .PUSH1)
  tiny_dj_step v, 400, .DUP3
  tiny_dj_step v, 401, .DUP5
  tiny_dj_step v, 402, .SUB
  tiny_dj_step v, 403, .SLT
  tiny_dj_step v, 404, .ISZERO
  tiny_dj_step v, 405, (.Push .PUSH2)
  tiny_dj_step v, 408, .JUMPI
  tiny_dj_step v, 409, .PUSH0
  tiny_dj_step v, 410, .PUSH0
  tiny_dj_step v, 411, .REVERT
  tiny_dj_step v, 412, .JUMPDEST
  tiny_dj_step v, 413, .POP
  tiny_dj_step v, 414, .CALLDATALOAD
  tiny_dj_step v, 415, .SWAP2
  tiny_dj_step v, 416, .SWAP1
  tiny_dj_step v, 417, .POP
  tiny_dj_step v, 418, .JUMP
  tiny_dj_step v, 419, .INVALID
  tiny_dj_step v, 420, .LOG1
  tiny_dj_step v, 421, (.Push .PUSH5)
  tiny_dj_step v, 427, .STOP
  tiny_dj_step v, 428, .ADDMOD
  tiny_dj_step v, 429, .INVALID
  tiny_dj_step v, 430, .STOP
  tiny_dj_step v, 431, .EXP
  rw [D_J_aux_ge_size (patchedRuntime v) 432 _ (by rw [patchedRuntime_size v])]
  native_decide

theorem tinyContains15 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨15⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains63 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨63⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains67 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨67⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains106 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨106⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains139 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨139⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains148 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨148⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains162 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨162⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains167 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨167⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains181 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨181⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains220 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨220⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains358 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨358⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains396 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨396⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains412 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨412⟩ = true := by
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
