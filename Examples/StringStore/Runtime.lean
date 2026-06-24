import Examples.StringStore.Append
import Examples.StringStore.Clear
import Examples.StringStore.CurrentLength
import Examples.StringStore.DropLast
import Examples.StringStore.Replace
import Examples.StringStore.Set
import Examples.StringStore.StoreRaw

/-!
# StringStore — runtime proof assembly

`Getters.lean` contains the completed runtime proof facts for dispatch failures, the constructor
prelude support needed by runtime calls, and the getter-style branches proved so far.  New runtime
branches should be added here or in smaller modules imported here, so edits do not force
re-elaboration of the completed getter proof body.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace StringStore

def appendToHistoryEmptyZeroBranch (σ_evm : AccountMap) (I : ExecutionEnv) : Prop :=
  I.calldata.size < 2 ^ 255 ∧
    uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩ ∧
    appendToHistoryExistingElementHeader σ_evm I I.calldata ⟨0⟩
      ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)) = ⟨0⟩

def appendToHistoryPayloadShortBranch (I : ExecutionEnv) : Prop :=
  I.calldata.size < 2 ^ 255 ∧
    ¬ ABI.solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ∧
    ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length ≠
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) ∧
    UInt256.gt
      (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
        UInt256.mul
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
      (UInt256.ofNat I.calldata.size) = ⟨1⟩

def appendToHistoryLengthHugeBranch (I : ExecutionEnv) : Prop :=
  I.calldata.size < 2 ^ 255 ∧
    ABI.solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat

axiom stringStoreSetRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz : 36 ≤ I.calldata.size)
    (hhuge : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlen : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I

axiom stringStoreAppendToHistoryRuntimeResidual
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz : 36 ≤ I.calldata.size)
    (hhuge : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlen : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hnotEmptyZero : ¬ appendToHistoryEmptyZeroBranch σ_evm I)
    (hnotLengthHuge : ¬ appendToHistoryLengthHugeBranch I)
    (hnotPayloadShort : ¬ appendToHistoryPayloadShortBranch I) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I

theorem stringStoreAppendToHistoryRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x7d, 0x4d, 0x56, 0x80]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz : 36 ≤ I.calldata.size)
    (hhuge : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlen : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hEmpty : appendToHistoryEmptyZeroBranch σ_evm I
  · exact stringStoreAppendToHistoryShortEmptyValidRuntime
      hcode hsize hperm hwv hsel hAccounts hsz hhuge hoff hlen
      hEmpty.1 hEmpty.2.1 hEmpty.2.2
  · by_cases hLengthHuge : appendToHistoryLengthHugeBranch I
    · exact stringStoreAppendToHistoryLengthHugeRuntime
        hcode hsize hperm hwv hsel hAccounts hsz hhuge hoff hlen
        hLengthHuge.1 hLengthHuge.2
    · by_cases hPayloadShort : appendToHistoryPayloadShortBranch I
      · exact stringStoreAppendToHistoryPayloadShortRuntime
          hcode hsize hperm hwv hsel hAccounts hsz hhuge hoff hlen
          hPayloadShort.1 hPayloadShort.2.1 hPayloadShort.2.2.1 hPayloadShort.2.2.2
      · exact stringStoreAppendToHistoryRuntimeResidual
          hcode hsize hperm hwv hsel hAccounts hsz hhuge hoff hlen
          hEmpty hLengthHuge hPayloadShort

axiom stringStoreReplaceFromHistoryRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x0f, 0x76, 0xd8, 0xb4]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz : 36 ≤ I.calldata.size)
    (hhuge : I.calldata.size < 2 ^ 255 + 4) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I

axiom stringStoreStoreRawRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x68, 0xb3, 0x91, 0x68]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz : 36 ≤ I.calldata.size)
    (hhuge : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlen : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I

/-! ## Runtime assembly

This theorem closes all global runtime cases that are already proved: non-payable calls,
short/no-match dispatch failures, `rawLength`, `historyLength`, and the completed `currentLength`
subcases.  The remaining storage/data-copy traces are named axioms above.
-/

set_option maxHeartbeats 1200000 in
theorem stringStoreRuntimeCorrect :
    runtimeEquivalence!?! stringStoreConfig stringStoreBytecode stringStoreContract := by
  refine runtimeEquivalence!?!.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · by_cases hsel_replace :
        (stringStoreSelBytes 2 == I.calldata.extract 0 4) = true
      · by_cases hreplaceShort : I.calldata.size < 36
        · exact stringStoreReplaceFromHistoryHeadShortRuntime hcode hsize hperm hwv
            (by simpa [stringStoreSelBytes, selIs]) hAccounts hsz hreplaceShort
        · by_cases hreplaceHuge : 2 ^ 255 + 4 ≤ I.calldata.size
          · exact stringStoreReplaceFromHistoryHeadHugeRuntime hcode hsize hperm hwv
              (by simpa [stringStoreSelBytes, selIs]) hAccounts hsz hreplaceHuge
          · exact stringStoreReplaceFromHistoryRuntime hcode hsize hperm hwv
              (by simpa [stringStoreSelBytes, selIs])
              hAccounts (by omega) (Nat.lt_of_not_ge hreplaceHuge)
      · by_cases hsel_drop :
          (stringStoreSelBytes 3 == I.calldata.extract 0 4) = true
        · exact stringStoreDropLastRuntime_of_nonzeroHistory
            hcode hsize hperm hwv (by simpa [stringStoreSelBytes, selIs]) hAccounts
        · by_cases hsel_set :
            (stringStoreSelBytes 0 == I.calldata.extract 0 4) = true
          · by_cases hsetShort : I.calldata.size < 36
            · exact stringStoreSetHeadShortRuntime hcode hsize hperm hwv
                (by simpa [stringStoreSelBytes, selIs]) hAccounts hsz hsetShort
            · by_cases hsetHuge : 2 ^ 255 + 4 ≤ I.calldata.size
              · exact stringStoreSetHeadHugeRuntime hcode hsize hperm hwv
                  (by simpa [stringStoreSelBytes, selIs]) hAccounts hsz hsetHuge
              · by_cases hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat
                · exact stringStoreSetOffsetHugeRuntime hcode hsize hperm hwv
                    (by simpa [stringStoreSelBytes, selIs]) hAccounts (by omega)
                    (Nat.lt_of_not_ge hsetHuge) hoff
                · by_cases hlenShort :
                    I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32
                  · exact stringStoreSetLengthShortRuntime hcode hsize hperm hwv
                      (by simpa [stringStoreSelBytes, selIs]) hAccounts (by omega)
                      (Nat.lt_of_not_ge hsetHuge) hoff hlenShort
                  · exact stringStoreSetRuntime hcode hsize hperm hwv
                      (by simpa [stringStoreSelBytes, selIs])
                      hAccounts (by omega) (Nat.lt_of_not_ge hsetHuge) hoff
                      (Nat.le_of_not_gt hlenShort)
          · by_cases hsel_store :
              (stringStoreSelBytes 6 == I.calldata.extract 0 4) = true
            · by_cases hstoreShort : I.calldata.size < 36
              · exact stringStoreStoreRawHeadShortRuntime hcode hsize hperm hwv
                  (by simpa [stringStoreSelBytes, selIs]) hAccounts hsz hstoreShort
              · by_cases hstoreHuge : 2 ^ 255 + 4 ≤ I.calldata.size
                · exact stringStoreStoreRawHeadHugeRuntime hcode hsize hperm hwv
                    (by simpa [stringStoreSelBytes, selIs]) hAccounts hsz hstoreHuge
                · by_cases hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat
                  · exact stringStoreStoreRawOffsetHugeRuntime hcode hsize hperm hwv
                      (by simpa [stringStoreSelBytes, selIs]) hAccounts (by omega)
                      (Nat.lt_of_not_ge hstoreHuge) hoff
                  · by_cases hlenShort :
                      I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32
                    · exact stringStoreStoreRawLengthShortRuntime hcode hsize hperm hwv
                        (by simpa [stringStoreSelBytes, selIs]) hAccounts (by omega)
                        (Nat.lt_of_not_ge hstoreHuge) hoff hlenShort
                    · exact stringStoreStoreRawRuntime hcode hsize hperm hwv
                        (by simpa [stringStoreSelBytes, selIs]) hAccounts (by omega)
                        (Nat.lt_of_not_ge hstoreHuge) hoff
                        (Nat.le_of_not_gt hlenShort)
            · by_cases hsel_raw :
                (stringStoreSelBytes 9 == I.calldata.extract 0 4) = true
              · exact stringStoreRawLengthRuntime hcode hsize hperm hwv
                  (by simpa [stringStoreSelBytes, selIs]) hAccounts
              · by_cases hsel_append :
                  (stringStoreSelBytes 1 == I.calldata.extract 0 4) = true
                · by_cases happendShort : I.calldata.size < 36
                  · exact stringStoreAppendToHistoryHeadShortRuntime hcode hsize hperm hwv
                      (by simpa [stringStoreSelBytes, selIs]) hAccounts hsz happendShort
                  · by_cases happendHuge : 2 ^ 255 + 4 ≤ I.calldata.size
                    · exact stringStoreAppendToHistoryHeadHugeRuntime hcode hsize hperm hwv
                        (by simpa [stringStoreSelBytes, selIs]) hAccounts hsz happendHuge
                    · by_cases hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat
                      · exact stringStoreAppendToHistoryOffsetHugeRuntime hcode hsize hperm hwv
                          (by simpa [stringStoreSelBytes, selIs]) hAccounts (by omega)
                          (Nat.lt_of_not_ge happendHuge) hoff
                      · by_cases hlenShort :
                          I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32
                        · exact stringStoreAppendToHistoryLengthShortRuntime hcode hsize hperm hwv
                            (by simpa [stringStoreSelBytes, selIs]) hAccounts (by omega)
                            (Nat.lt_of_not_ge happendHuge) hoff hlenShort
                        · exact stringStoreAppendToHistoryRuntime hcode hsize hperm hwv
                            (by simpa [stringStoreSelBytes, selIs]) hAccounts (by omega)
                            (Nat.lt_of_not_ge happendHuge) hoff
                            (Nat.le_of_not_gt hlenShort)
                · by_cases hsel_current :
                    (stringStoreSelBytes 7 == I.calldata.extract 0 4) = true
                  · exact stringStoreCurrentLengthRuntime hcode hsize hperm hwv
                      (by simpa [stringStoreSelBytes, selIs]) hAccounts
                  · by_cases hsel_clearCurrent :
                      (stringStoreSelBytes 4 == I.calldata.extract 0 4) = true
                    · exact stringStoreClearCurrentRuntime_of_nonzeroHeader
                        hcode hsize hperm hwv
                        (by simpa [stringStoreSelBytes, selIs]) hAccounts
                    · by_cases hsel_clearAll :
                      (stringStoreSelBytes 5 == I.calldata.extract 0 4) = true
                      · exact stringStoreClearAllRuntime_of_notAllZero
                          hcode hsize hperm hwv
                          (by simpa [stringStoreSelBytes, selIs]) hAccounts
                      · by_cases hsel_history :
                          (stringStoreSelBytes 8 == I.calldata.extract 0 4) = true
                        · exact stringStoreHistoryLengthRuntime hcode hsize hperm hwv
                            (by simpa [stringStoreSelBytes, selIs]) hAccounts
                        · have hset_false :
                              (stringStoreSelBytes 0 == I.calldata.extract 0 4) = false :=
                            bool_eq_false_of_not_true hsel_set
                          have happend_false :
                              (stringStoreSelBytes 1 == I.calldata.extract 0 4) = false :=
                            bool_eq_false_of_not_true hsel_append
                          have hreplace_false :
                              (stringStoreSelBytes 2 == I.calldata.extract 0 4) = false :=
                            bool_eq_false_of_not_true hsel_replace
                          have hdrop_false :
                              (stringStoreSelBytes 3 == I.calldata.extract 0 4) = false :=
                            bool_eq_false_of_not_true hsel_drop
                          have hclearCurrent_false :
                              (stringStoreSelBytes 4 == I.calldata.extract 0 4) = false :=
                            bool_eq_false_of_not_true hsel_clearCurrent
                          have hclearAll_false :
                              (stringStoreSelBytes 5 == I.calldata.extract 0 4) = false :=
                            bool_eq_false_of_not_true hsel_clearAll
                          have hstore_false :
                              (stringStoreSelBytes 6 == I.calldata.extract 0 4) = false :=
                            bool_eq_false_of_not_true hsel_store
                          have hcurrent_false :
                              (stringStoreSelBytes 7 == I.calldata.extract 0 4) = false :=
                            bool_eq_false_of_not_true hsel_current
                          have hhistory_false :
                              (stringStoreSelBytes 8 == I.calldata.extract 0 4) = false :=
                            bool_eq_false_of_not_true hsel_history
                          have hraw_false :
                              (stringStoreSelBytes 9 == I.calldata.extract 0 4) = false :=
                            bool_eq_false_of_not_true hsel_raw
                          exact stringStoreNoDispatch hcode hsize hperm hwv (by
                            intro i hi
                            interval_cases i
                            · simpa [stringStoreSelBytes] using hset_false
                            · simpa [stringStoreSelBytes] using happend_false
                            · simpa [stringStoreSelBytes] using hreplace_false
                            · simpa [stringStoreSelBytes] using hdrop_false
                            · simpa [stringStoreSelBytes] using hclearCurrent_false
                            · simpa [stringStoreSelBytes] using hclearAll_false
                            · simpa [stringStoreSelBytes] using hstore_false
                            · simpa [stringStoreSelBytes] using hcurrent_false
                            · simpa [stringStoreSelBytes] using hhistory_false
                            · simpa [stringStoreSelBytes] using hraw_false)
    · exact stringStoreShortRevert hcode hsize hperm hwv (by omega)
  · exact stringStoreNonPayable hcode hwv

end StringStore
