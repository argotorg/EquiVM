import Benchmarks.EAS.Attester.MultiSource
import Benchmarks.EAS.Attester.InnerArrayCopy
import Benchmarks.EAS.Attester.MultiRevokeMemory
import Benchmarks.EAS.Attester.MultiRevokeProgress
import Benchmarks.EAS.Attester.MultiRevokeEVM
import Benchmarks.EAS.Attester.MultiRevokePostCall
import Benchmarks.EAS.Attester.MultiRevokePostLoop
import Benchmarks.EAS.Attester.MultiRevokeContinuation
import Benchmarks.EAS.Attester.MultiRevokeLoopRun
import Benchmarks.EAS.Attester.MultiRevokeEncoderABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

/-! ## `multiRevoke(bytes32[],bytes32[][])` -/

theorem attesterDecode_multiRevoke_none_short (v : AttesterImmutables) {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  show decodeCalldata ["schemas", "schemaUids"] [bytes32Array, bytes32NestedArray]
      I.calldata = none
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hbig⟩; rw [htlen] at hbig; omega)]
  rw [if_neg (by rintro ⟨_, hbig⟩; rw [List.length_drop, htlen] at hbig; omega)]
  rw [if_neg (by rintro ⟨_, hbig⟩; rw [htlen] at hbig; omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32Array, bytes32NestedArray] = some 64 by native_decide]
  simp only [bind, Option.bind]
  have hargsShort : (I.calldata.toList.drop 4).length < 64 := by
    rw [List.length_drop, htlen]
    omega
  rw [if_pos hargsShort]

theorem attesterDecode_multiRevoke_none_huge (v : AttesterImmutables) {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  show decodeCalldata ["schemas", "schemaUids"] [bytes32Array, bytes32NestedArray]
      I.calldata = none
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_pos]
  · exact ⟨by native_decide, by rw [htlen]; omega⟩

theorem attesterDecode_multiRevoke_none_totalHuge (v : AttesterImmutables) {I : ExecutionEnv}
    (hbig : 2 ^ 255 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaUids"] [bytes32Array, bytes32NestedArray]
      I.calldata = none
  simpa [bytes32Array, bytes32NestedArray] using
    attesterDecodeCalldata_twoDynamicArrays_none_totalHuge
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaUids")
      (elem0 := bytes32) (elem1 := bytes32) hbig

theorem attesterDecode_multiRevoke_none_firstOffsetHuge (v : AttesterImmutables)
    {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hoff : solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaUids"] [bytes32Array, bytes32NestedArray]
      I.calldata = none
  simpa [bytes32Array, bytes32NestedArray] using
    attesterDecodeCalldata_twoDynamicArrays_none_firstOffsetHuge
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaUids")
      (elem0 := bytes32) (elem1 := bytes32) hsz68 hoff

theorem attesterDecode_multiRevoke_none_firstLengthShort (v : AttesterImmutables)
    {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaUids"] [bytes32Array, bytes32NestedArray]
      I.calldata = none
  simpa [bytes32Array, bytes32NestedArray] using
    attesterDecodeCalldata_twoDynamicArrays_none_firstLengthShort
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaUids")
      (elem0 := bytes32) (elem1 := bytes32) hsz68 hoffMax hshort

theorem attesterDecode_multiRevoke_none_firstLengthHuge (v : AttesterImmutables)
    {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenHuge : solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaUids"] [bytes32Array, bytes32NestedArray]
      I.calldata = none
  simpa [bytes32Array, bytes32NestedArray] using
    attesterDecodeCalldata_twoDynamicArrays_none_firstLengthHuge
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaUids")
      (elem0 := bytes32) (elem1 := bytes32) hsz68 hoffMax hlenWord hlenHuge

theorem attesterDecode_multiRevoke_none_firstPayloadShort (v : AttesterImmutables)
    {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload : I.calldata.size <
      4 + (calldataWord I.calldata 4).toNat + 32 +
        32 * (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaUids"] [bytes32Array, bytes32NestedArray]
      I.calldata = none
  simpa [bytes32Array, bytes32NestedArray] using
    attesterDecodeCalldata_twoDynamicArrays_none_firstBytes32PayloadShort
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaUids")
      (elem1 := bytes32) hsz68 hoffMax hlenWord hlenMax hpayload

theorem attesterDecode_multiRevoke_none_secondOffsetHuge (v : AttesterImmutables)
    {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hoff0Max : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlen0Max : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload0 :
      4 + (calldataWord I.calldata 4).toNat + 32 +
          32 * (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≤
        I.calldata.size)
    (hoff1Huge : solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaUids"] [bytes32Array, bytes32NestedArray]
      I.calldata = none
  simpa [bytes32Array, bytes32NestedArray] using
    attesterDecodeCalldata_twoDynamicArrays_none_secondOffsetHuge
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaUids")
      (elem1 := bytes32) hsz68 hoff0Max hlenWord hlen0Max hpayload0 hoff1Huge

theorem attesterDecode_multiRevoke_none_secondLengthShort (v : AttesterImmutables)
    {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hoff0Max : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlen0Word : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlen0Max : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload0 :
      4 + (calldataWord I.calldata 4).toNat + 32 +
          32 * (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≤
        I.calldata.size)
    (hoff1Max : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hshort1 : I.calldata.size < 4 + (calldataWord I.calldata 36).toNat + 32) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaUids"] [bytes32Array, bytes32NestedArray]
      I.calldata = none
  simpa [bytes32Array, bytes32NestedArray] using
    attesterDecodeCalldata_twoDynamicArrays_none_secondLengthShort
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaUids")
      (elem1 := bytes32) hsz68 hoff0Max hlen0Word hlen0Max hpayload0 hoff1Max hshort1

theorem attesterDecode_multiRevoke_none_secondLengthHuge (v : AttesterImmutables)
    {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hoff0Max : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlen0Word : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlen0Max : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload0 :
      4 + (calldataWord I.calldata 4).toNat + 32 +
          32 * (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≤
        I.calldata.size)
    (hoff1Max : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlen1Word : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlen1Huge : solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaUids"] [bytes32Array, bytes32NestedArray]
      I.calldata = none
  simpa [bytes32Array, bytes32NestedArray] using
    attesterDecodeCalldata_twoDynamicArrays_none_secondLengthHuge
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaUids")
      (elem1 := bytes32) hsz68 hoff0Max hlen0Word hlen0Max hpayload0 hoff1Max hlen1Word
      hlen1Huge

theorem attesterDecode_multiRevoke_none_secondPayloadShort (v : AttesterImmutables)
    {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hoff0Max : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlen0Word : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlen0Max : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload0 :
      4 + (calldataWord I.calldata 4).toNat + 32 +
          32 * (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≤
        I.calldata.size)
    (hoff1Max : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlen1Word : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlen1Max : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayload1 :
      I.calldata.size <
        4 + (calldataWord I.calldata 36).toNat + 32 +
          32 * (calldataWord I.calldata
            (4 + (calldataWord I.calldata 36).toNat)).toNat) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaUids"] [bytes32Array, bytes32NestedArray]
      I.calldata = none
  simpa [bytes32Array, bytes32NestedArray] using
    attesterDecodeCalldata_twoDynamicArrays_none_secondPayloadShort
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaUids")
      (elem1 := bytes32) hsz68 hoff0Max hlen0Word hlen0Max hpayload0 hoff1Max hlen1Word
      hlen1Max hpayload1

theorem attesterDecode_multiRevoke_some_shape (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs) :
    ∃ schemas schemaUids : List Value,
      callargs.get? "schemas" = some (.array schemas) ∧
      callargs.get? "schemaUids" = some (.array schemaUids) := by
  have hdec' :
      decodeCalldata ["schemas", "schemaUids"]
        [.dynamicArray bytes32, .dynamicArray (.dynamicArray bytes32)] I.calldata =
      some callargs := by
    simpa [decodeCalldataWithMode, config, multiRevokeTransition, transitionSignature,
      bytes32Array, bytes32NestedArray] using hdec
  exact attesterDecodeCalldata_twoDynamicArrays_shape
    (name0 := "schemas") (name1 := "schemaUids")
    (elem0 := bytes32) (elem1 := bytes32) (cd := I.calldata)
    (by native_decide) hdec'

theorem attesterDecode_multiRevoke_some_shape_lengths (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs) :
    ∃ schemas schemaUids : List Value,
      callargs.get? "schemas" = some (.array schemas) ∧
      callargs.get? "schemaUids" = some (.array schemaUids) ∧
      schemas.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ∧
      schemaUids.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat := by
  have hdec' :
      decodeCalldata ["schemas", "schemaUids"]
        [.dynamicArray bytes32, .dynamicArray (.dynamicArray bytes32)] I.calldata =
      some callargs := by
    simpa [decodeCalldataWithMode, config, multiRevokeTransition, transitionSignature,
      bytes32Array, bytes32NestedArray] using hdec
  exact attesterDecodeCalldata_twoDynamicArrays_lengths
    (name0 := "schemas") (name1 := "schemaUids")
    (elem1 := bytes32) (cd := I.calldata)
    (by native_decide) hdec'

theorem attesterDecode_multiRevoke_good_lengths_of_not_bad (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store}
    (hnotBad :
      ¬ ∃ callargs schemas schemaUids,
          decodeCalldataWithMode (config v).abiDecodeMode
              ((multiRevokeTransition v).params.map Param.name)
              (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
            some callargs ∧
          callargs.get? "schemas" = some (.array schemas) ∧
          callargs.get? "schemaUids" = some (.array schemaUids) ∧
          schemas.length =
            (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ∧
          schemaUids.length =
            (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ∧
          (schemas.length = 0 ∨ schemas.length ≠ schemaUids.length))
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs) :
    ∃ schemas schemaUids : List Value,
      callargs.get? "schemas" = some (.array schemas) ∧
      callargs.get? "schemaUids" = some (.array schemaUids) ∧
      schemas.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ∧
      schemaUids.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ∧
      schemas.length ≠ 0 ∧ schemas.length = schemaUids.length := by
  obtain ⟨schemas, schemaUids, hSchemas, hSchemaUids, hSchemasLen, hSchemaUidsLen⟩ :=
    attesterDecode_multiRevoke_some_shape_lengths v hdec
  have hnonzero : schemas.length ≠ 0 := by
    intro hzero
    exact hnotBad ⟨callargs, schemas, schemaUids, hdec, hSchemas, hSchemaUids,
      hSchemasLen, hSchemaUidsLen, Or.inl hzero⟩
  have heq : schemas.length = schemaUids.length := by
    by_contra hne
    exact hnotBad ⟨callargs, schemas, schemaUids, hdec, hSchemas, hSchemaUids,
      hSchemasLen, hSchemaUidsLen, Or.inr hne⟩
  exact ⟨schemas, schemaUids, hSchemas, hSchemaUids, hSchemasLen, hSchemaUidsLen,
    hnonzero, heq⟩

theorem attesterX_multiRevokeOuterArrayInitProgressWithFreeInvariant_raw
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (hoff0Max : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hoff1Max : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlen0Max : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hrawFirstNe :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hrawEq :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨192⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ a' k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        (attesterMultiRevokeOuterArrayInitExitStack I ⟨128⟩
          (attesterFirstArrayLengthWord I) a')
        (attesterMultiOuterArrayInitFinalMem a')
        (attesterMultiOuterArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k C := by
  have hnonzeroEvm :=
    attesterFirstArrayLengthWord_isZero_of_nat_ne_zero
      (I := I) hoff0Max hrawFirstNe
  have heqEvm :=
    attesterArrayLengthWords_eq_one_of_nat_eq
      (I := I) hoff0Max hoff1Max hrawEq
  have hguard :=
    attesterX_multiRevokeLengthGuardOk
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v hnonzeroEvm heqEvm hreach
  have halloc :=
    attesterX_multiRevokeAllocLengthMaxOk
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v hoff0Max hlen0Max hguard
  have hentry :=
    attesterX_multiRevokeOuterArrayInitEntry
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v hnonzeroEvm halloc
  have hlenNe : (attesterFirstArrayLengthWord I).toNat ≠ 0 := by
    rw [attesterFirstArrayLengthWord_toNat (I := I) hoff0Max]
    exact hrawFirstNe
  have hlenMax : (attesterFirstArrayLengthWord I).toNat ≤ solcMaxU64 := by
    rw [attesterFirstArrayLengthWord_toNat (I := I) hoff0Max]
    exact Nat.le_of_not_gt hlen0Max
  exact
    attesterX_multiRevokeOuterArrayInitProgressWithFreeInvariant
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v hlenNe hlenMax hentry

theorem attesterMultiRevokeBodySchemaGuardReverts (v : AttesterImmutables)
    (evm : EVM.State) (locals : Store) {schemas schemaUids : List Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hSchemas : locals.get? "schemas" = some (.array schemas))
    (hSchemaUids : locals.get? "schemaUids" = some (.array schemaUids))
    (hbad : schemas.length = 0 ∨ schemas.length ≠ schemaUids.length) :
    ExecTransitionBody (config v) (contract v) evm locals
      (multiRevokeTransition v).body .reverted := by
  have hSchemasElem : locals["schemas"]? = some (.array schemas) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hSchemas
  have hSchemaUidsElem (n : Nat) :
      (locals.insert "schemaLength" (.int (Int.ofNat n)))["schemaUids"]? =
        some (.array schemaUids) := by
    rw [Std.HashMap.getElem?_insert]
    simp
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hSchemaUids
  refine ExecFuncBody.execBlockRevert ?_
  simp [multiRevokeTransition, nonpayable]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int (Int.ofNat schemas.length)) ?_) ?_
  · simp [evalExpr?, lenLocal, localRef, hSchemasElem, readLocalPath?,
      EvalResult.bind, bind, pure]
  · refine ExecBlock.consRevert (ExecStmt.requireFalse ?_)
    exact attesterEvalMultiLengthGuardFalse (v := v) (evm := evm) (locals := locals)
      (secondName := "schemaUids") (schemas := schemas) (second := schemaUids)
      (hSchemaUidsElem schemas.length) hbad

theorem attesterMultiRevokeBodyFirstUidLengthZeroReverts (v : AttesterImmutables)
    (evm : EVM.State) (locals : Store) {schemas rest : List Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hSchemas : locals.get? "schemas" = some (.array schemas))
    (hSchemaUids : locals.get? "schemaUids" = some (.array (.array [] :: rest)))
    (hSchemasNe : schemas.length ≠ 0)
    (hSchemasLen : schemas.length = (.array [] :: rest).length) :
    ExecTransitionBody (config v) (contract v) evm locals
      (multiRevokeTransition v).body .reverted := by
  have hSchemasElem : locals["schemas"]? = some (.array schemas) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hSchemas
  refine ExecFuncBody.execBlockRevert ?_
  simp [multiRevokeTransition, nonpayable]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int (Int.ofNat schemas.length)) ?_) ?_
  · simp [evalExpr?, lenLocal, localRef, hSchemasElem, readLocalPath?,
      EvalResult.bind, bind, pure]
  · have hguard :
        evalExpr? (config v)
          { contract := contract v,
            locals := locals.insert "schemaLength" (.int (Int.ofNat schemas.length)) } evm
          (.binary .and
            (.binary .ne (.var "schemaLength") (.intLit 0))
            (.binary .eq (.var "schemaLength") (lenLocal "schemaUids"))) =
          .ok (.bool true) := by
      have hleft :
          evalExpr? (config v)
            { contract := contract v,
              locals := locals.insert "schemaLength" (.int (Int.ofNat schemas.length)) } evm
            (.binary .ne (.var "schemaLength") (.intLit 0)) =
          .ok (.bool true) := by
        simp [evalExpr?, evalBinaryOp?, hSchemasNe,
          EvalResult.bind, EvalResult.ofOption, bind, pure]
      have hright :
          evalExpr? (config v)
            { contract := contract v,
              locals := locals.insert "schemaLength" (.int (Int.ofNat schemas.length)) } evm
            (.binary .eq (.var "schemaLength") (lenLocal "schemaUids")) =
          .ok (.bool true) := by
        have hSchemaUidsElem :
            (locals.insert "schemaLength" (.int (Int.ofNat schemas.length)))["schemaUids"]? =
              some (.array (.array [] :: rest)) := by
          rw [Std.HashMap.getElem?_insert]
          simp
          rw [← Std.HashMap.get?_eq_getElem?]
          exact hSchemaUids
        have hSchemaUidsGet :
            (locals.insert "schemaLength" (.int (Int.ofNat schemas.length))).get?
                "schemaUids" =
              some (.array (.array [] :: rest)) := by
          simpa [Std.HashMap.get?_eq_getElem?] using hSchemaUidsElem
        have hvar :
            evalExpr? (config v)
              { contract := contract v,
                locals := locals.insert "schemaLength" (.int (Int.ofNat schemas.length)) } evm
              (.var "schemaLength") =
            .ok (.int (Int.ofNat schemas.length)) := by
          simp [evalExpr?, EvalResult.ofOption]
        have hlen :
            evalExpr? (config v)
              { contract := contract v,
                locals := locals.insert "schemaLength" (.int (Int.ofNat schemas.length)) } evm
              (lenLocal "schemaUids") =
            .ok (.int (Int.ofNat (.array [] :: rest).length)) := by
          simp only [evalExpr?, lenLocal, localRef, readLocalPath?, EvalResult.bind,
            bind, pure]
          rw [hSchemaUidsGet]
          rfl
        have hop :
            evalBinaryOp? .eq (.int (Int.ofNat schemas.length))
              (.int (Int.ofNat (.array [] :: rest).length)) = .ok (.bool true) := by
          simp [evalBinaryOp?, hSchemasLen]
        exact attesterEvalBinaryEq hvar hlen hop
      exact attesterEvalAndTrue hleft hright
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    let defaultRequest : Value :=
      .tuple [.fixedBytes bytes32Width (List.replicate 32 0), .array []]
    let multiRequests : Value :=
      .array (List.replicate schemas.length defaultRequest)
    have hmultiRequests :
        evalExpr? (config v)
          { contract := contract v,
            locals := locals.insert "schemaLength" (.int (Int.ofNat schemas.length)) } evm
          (.newArray multiRevocationRequestSt (.var "schemaLength")) =
        .ok multiRequests := by
      simp [multiRequests, defaultRequest, evalExpr?, multiRevocationRequestSt,
        revocationRequestDataSt, bytes32St, uint256St, bytes32Width,
        defaultValue?, defaultValues?, EvalResult.bind, EvalResult.ofOption, bind, pure]
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (value := multiRequests) hmultiRequests) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) ?_) ?_
    · simp [evalExpr?, pure]
    · refine ExecBlock.consRevert (ExecStmt.whileRevert ?_ ?_)
      · have hiEval :
            evalExpr? (config v)
              { contract := contract v,
                locals := (((locals.insert "schemaLength"
                  (.int (Int.ofNat schemas.length))).insert
                  "multiRequests" multiRequests).insert "i" (.int 0)) } evm
              (.var "i") = .ok (.int 0) := by
          simp [evalExpr?, EvalResult.ofOption, Std.HashMap.get?_eq_getElem?]
        have hschemaLengthEval :
            evalExpr? (config v)
              { contract := contract v,
                locals := (((locals.insert "schemaLength"
                  (.int (Int.ofNat schemas.length))).insert
                  "multiRequests" multiRequests).insert "i" (.int 0)) } evm
              (.var "schemaLength") = .ok (.int (Int.ofNat schemas.length)) := by
          simp [evalExpr?, EvalResult.ofOption, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem_insert]
        have hposNat : 0 < schemas.length := Nat.pos_of_ne_zero hSchemasNe
        have hpos : (0 : Int) < Int.ofNat schemas.length := by
          exact Int.natCast_pos.mpr hposNat
        have hop :
            evalBinaryOp? .lt (.int 0) (.int (Int.ofNat schemas.length)) =
              .ok (.bool true) := by
          simpa [evalBinaryOp?, hpos]
        exact attesterEvalBinaryLt hiEval hschemaLengthEval hop
      · refine ExecBlock.consNormal (ExecStmt.letDecl (value := .array []) ?_) ?_
        · have hbaseEval :
              evalExpr? (config v)
                { contract := contract v,
                  locals := (((locals.insert "schemaLength"
                    (.int (Int.ofNat schemas.length))).insert
                    "multiRequests" multiRequests).insert "i" (.int 0)) } evm
                (.var "schemaUids") = .ok (.array (.array [] :: rest)) := by
            have hSchemaUidsGet :
                ((((locals.insert "schemaLength" (.int (Int.ofNat schemas.length))).insert
                      "multiRequests" multiRequests).insert "i" (.int 0)).get?
                    "schemaUids") =
                  some (.array (.array [] :: rest)) := by
              rw [Std.HashMap.get?_eq_getElem?]
              rw [Std.HashMap.getElem?_insert]
              simp
              rw [Std.HashMap.getElem?_insert]
              simp
              rw [Std.HashMap.getElem?_insert]
              simp
              rw [← Std.HashMap.get?_eq_getElem?]
              exact hSchemaUids
            simp only [evalExpr?, EvalResult.ofOption]
            rw [hSchemaUidsGet]
          have hiEval :
              evalExpr? (config v)
                { contract := contract v,
                  locals := (((locals.insert "schemaLength"
                    (.int (Int.ofNat schemas.length))).insert
                    "multiRequests" multiRequests).insert "i" (.int 0)) } evm
                (.var "i") = .ok (.int 0) := by
            simp [evalExpr?, EvalResult.ofOption, Std.HashMap.get?_eq_getElem?]
          have hindex :
              evalIndex? (.array (.array [] :: rest)) (.int 0) = .ok (.array []) := by
            simp [evalIndex?, normalizeRawBoolWord?]
            rfl
          exact attesterEvalIndex hbaseEval hiEval hindex
        · refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) ?_) ?_
          · simp [evalExpr?, lenLocal, localRef, readLocalPath?,
              EvalResult.bind, bind, pure]
          · refine ExecBlock.consRevert (ExecStmt.requireFalse ?_)
            simp [evalExpr?, evalBinaryOp?,
              EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem attesterMultiRevokeBodySuccess (v : AttesterImmutables)
    (evm evm' : EVM.State) (locals : Store) {schemas schemaUids : List Value}
    {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hSchemas : locals.get? "schemas" = some (.array schemas))
    (hSchemaUids : locals.get? "schemaUids" = some (.array schemaUids))
    (hSchemasNe : schemas.length ≠ 0)
    (hSchemasBound : schemas.length < 2 ^ 256)
    (hLenEq : schemaUids.length = schemas.length)
    (hSchemaNorm : ∀ {idx schema}, lookupNth? schemas idx = some schema →
      normalizeRawBoolWord? schema = .ok schema)
    (hUidssOk : ∀ {idx value}, lookupNth? schemaUids idx = some value →
      ∃ uids,
        value = .array uids ∧
        uids.length ≠ 0 ∧
        uids.length < 2 ^ 256 ∧
        (∀ {j uid}, lookupNth? uids j = some uid →
          normalizeRawBoolWord? uid = .ok uid))
    (hguard :
      ∀ locals' : Store,
        locals'.get? "multiRequests" =
            some (.array
              (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) →
        evalExpr? (config v) { contract := contract v, locals := locals' } evm
          (.binary .gt (.extCodeSize (easExpr v)) (.intLit 0)) = .ok (.bool true))
    (hcall :
      ∀ locals' : Store,
        locals'.get? "multiRequests" =
            some (.array
              (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) →
        typedCallViaEVM (config v) evm (EVM.address v.eas) "multiRevoke" 0
          [.array (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)]
          (true, evm', out))
    (hdec : (config v).externalABI.decode? "multiRevoke" out = some []) :
    ∃ loopLocals : Store,
      loopLocals.get? "multiRequests" =
          some (.array
            (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) ∧
      ExecTransitionBody (config v) (contract v) evm locals
        (multiRevokeTransition v).body
        (.returned
          { contract := contract v,
            locals := loopLocals.insert "_multiRevoke" (collapseReturns []) } evm' none) := by
  let L1 := locals.insert "schemaLength" (.int (Int.ofNat schemas.length))
  have hschemaLengthExpr :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (lenLocal "schemas") = .ok (.int (Int.ofNat schemas.length)) :=
    attesterEvalLocalArrayLength hSchemas
  have hschemaLengthL1 :
      L1.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) := by
    simp [L1]
  have hschemaUidsL1 : L1.get? "schemaUids" = some (.array schemaUids) := by
    simpa [L1] using
      (attesterStoreGetInsertOfNe (locals := locals) (name := "schemaUids")
        (other := "schemaLength") (value := .int (Int.ofNat schemas.length))
        hSchemaUids (by decide))
  have hschemasL1 : L1.get? "schemas" = some (.array schemas) := by
    simpa [L1] using
      (attesterStoreGetInsertOfNe (locals := locals) (name := "schemas")
        (other := "schemaLength") (value := .int (Int.ofNat schemas.length))
        hSchemas (by decide))
  have hguardSchema :
      evalExpr? (config v) { contract := contract v, locals := L1 } evm
        (.binary .and
          (.binary .ne (.var "schemaLength") (.intLit 0))
          (.binary .eq (.var "schemaLength") (lenLocal "schemaUids"))) =
        .ok (.bool true) := by
    have hleft :
        evalExpr? (config v) { contract := contract v, locals := L1 } evm
          (.binary .ne (.var "schemaLength") (.intLit 0)) =
        .ok (.bool true) :=
      attesterEvalUInt256NeZeroTrue (attesterEvalVarOfGet hschemaLengthL1) hSchemasNe
    have hright :
        evalExpr? (config v) { contract := contract v, locals := L1 } evm
          (.binary .eq (.var "schemaLength") (lenLocal "schemaUids")) =
        .ok (.bool true) := by
      have hlenExpr :
          evalExpr? (config v) { contract := contract v, locals := L1 } evm
            (lenLocal "schemaUids") = .ok (.int (Int.ofNat schemaUids.length)) :=
        attesterEvalLocalArrayLength hschemaUidsL1
      have hop :
          evalBinaryOp? .eq (.int (Int.ofNat schemas.length))
            (.int (Int.ofNat schemaUids.length)) = .ok (.bool true) := by
        simp [evalBinaryOp?, hLenEq]
      exact attesterEvalBinaryEq (attesterEvalVarOfGet hschemaLengthL1) hlenExpr hop
    exact attesterEvalAndTrue hleft hright
  have hmultiRequestsExpr :
      evalExpr? (config v) { contract := contract v, locals := L1 } evm
        (.newArray multiRevocationRequestSt (.var "schemaLength")) =
      .ok (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault)) :=
    attesterEvalNewMultiRevokeRequestArray (attesterEvalVarOfGet hschemaLengthL1)
  let L2 := L1.insert "multiRequests"
    (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault))
  have hschemasL2 : L2.get? "schemas" = some (.array schemas) := by
    simpa [L2] using
      (attesterStoreGetInsertOfNe (locals := L1) (name := "schemas")
        (other := "multiRequests")
        (value := .array (List.replicate schemas.length attesterMultiRevokeRequestDefault))
        hschemasL1 (by decide))
  have hschemaUidsL2 : L2.get? "schemaUids" = some (.array schemaUids) := by
    simpa [L2] using
      (attesterStoreGetInsertOfNe (locals := L1) (name := "schemaUids")
        (other := "multiRequests")
        (value := .array (List.replicate schemas.length attesterMultiRevokeRequestDefault))
        hschemaUidsL1 (by decide))
  have hschemaLengthL2 :
      L2.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) := by
    simpa [L2] using
      (attesterStoreGetInsertOfNe (locals := L1) (name := "schemaLength")
        (other := "multiRequests")
        (value := .array (List.replicate schemas.length attesterMultiRevokeRequestDefault))
        hschemaLengthL1 (by decide))
  have hrequestsL2 :
      L2.get? "multiRequests" =
        some (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault)) := by
    simp [L2]
  let L3 := L2.insert "i" (.int 0)
  have hschemasL3 : L3.get? "schemas" = some (.array schemas) := by
    simpa [L3] using
      (attesterStoreGetInsertOfNe (locals := L2) (name := "schemas")
        (other := "i") (value := .int 0) hschemasL2 (by decide))
  have hschemaUidsL3 : L3.get? "schemaUids" = some (.array schemaUids) := by
    simpa [L3] using
      (attesterStoreGetInsertOfNe (locals := L2) (name := "schemaUids")
        (other := "i") (value := .int 0) hschemaUidsL2 (by decide))
  have hschemaLengthL3 :
      L3.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) := by
    simpa [L3] using
      (attesterStoreGetInsertOfNe (locals := L2) (name := "schemaLength")
        (other := "i") (value := .int 0) hschemaLengthL2 (by decide))
  have hrequestsL3 :
      L3.get? "multiRequests" =
        some (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault)) := by
    simpa [L3] using
      (attesterStoreGetInsertOfNe (locals := L2) (name := "multiRequests")
        (other := "i") (value := .int 0) hrequestsL2 (by decide))
  have hiL3 : L3.get? "i" = some (.int 0) := by
    simp [L3]
  obtain ⟨loopLocals, hloop, hrequestsDone, _hiDone⟩ :=
    attesterMultiRevokeOuterSourceLoop
      (imm := v) (evm := evm) (schemas := schemas) (schemaUids := schemaUids)
      (locals := L3) hSchemasBound hLenEq hSchemaNorm hUidssOk
      hschemasL3 hschemaUidsL3 hschemaLengthL3 hrequestsL3 hiL3
  have hargs :
      evalExprs? (config v) { contract := contract v, locals := loopLocals } evm
        [.var "multiRequests"] =
      .ok
        [.array (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)] := by
    have hrequestsDoneElem :
        loopLocals["multiRequests"]? =
          some (.array
            (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) := by
      rw [← Std.HashMap.get?_eq_getElem?]
      exact hrequestsDone
    simp [evalExprs?, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
      hrequestsDoneElem]
  have hiExpr :
      evalExpr? (config v) { contract := contract v, locals := L2 } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  refine ⟨loopLocals, hrequestsDone, ExecFuncBody.execBlockOK ?_⟩
  simp [multiRevokeTransition, nonpayable]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (by simpa [L1] using ExecStmt.letDecl hschemaLengthExpr) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSchema) ?_
  refine ExecBlock.consNormal (by simpa [L2] using ExecStmt.letDecl hmultiRequestsExpr) ?_
  refine ExecBlock.consNormal (by simpa [L3] using ExecStmt.letDecl hiExpr) ?_
  refine ExecBlock.consNormal hloop ?_
  exact checkedExternalCallSuccess
    (receiver := easExpr v) (retVar := "_multiRevoke") (name := "multiRevoke")
    (sendVal := 0) (args := [.var "multiRequests"])
    (hguard loopLocals hrequestsDone)
    (attesterEvalEasExpr v { contract := contract v, locals := loopLocals } evm)
    hargs (hcall loopLocals hrequestsDone) hdec

theorem attesterDecode_multiRevoke_return_ok (v : AttesterImmutables) (out : ByteArray) :
    (config v).externalABI.decode? "multiRevoke" out = some [] := by
  simp [config, attesterExternalABI, decodeVoid?]

theorem attesterMultiRevokeBodyLoopSuccess (v : AttesterImmutables)
    (evm evm' : EVM.State) (locals loopLocals : Store) {schemas schemaUids : List Value}
    {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hSchemas : locals.get? "schemas" = some (.array schemas))
    (hSchemaUids : locals.get? "schemaUids" = some (.array schemaUids))
    (hSchemasNe : schemas.length ≠ 0)
    (hLenEq : schemaUids.length = schemas.length)
    (hloop :
      ExecStmt (config v)
        { contract := contract v,
          locals :=
            (((locals.insert "schemaLength" (.int (Int.ofNat schemas.length))).insert
              "multiRequests"
              (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault))).insert
              "i" (.int 0)) } evm
        (.while attesterMultiRevokeOuterSourceLoopCond attesterMultiRevokeOuterSourceLoopBody)
        (.ok { contract := contract v, locals := loopLocals } evm))
    (hrequestsDone :
      loopLocals.get? "multiRequests" =
        some (.array (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)))
    (hguard :
      ∀ locals' : Store,
        locals'.get? "multiRequests" =
            some (.array
              (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) →
        evalExpr? (config v) { contract := contract v, locals := locals' } evm
          (.binary .gt (.extCodeSize (easExpr v)) (.intLit 0)) = .ok (.bool true))
    (hcall :
      ∀ locals' : Store,
        locals'.get? "multiRequests" =
            some (.array
              (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) →
        typedCallViaEVM (config v) evm (EVM.address v.eas) "multiRevoke" 0
          [.array (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)]
          (true, evm', out))
    (hdec : (config v).externalABI.decode? "multiRevoke" out = some []) :
    ExecTransitionBody (config v) (contract v) evm locals
      (multiRevokeTransition v).body
      (.returned
        { contract := contract v,
          locals := loopLocals.insert "_multiRevoke" (collapseReturns []) } evm' none) := by
  let L1 := locals.insert "schemaLength" (.int (Int.ofNat schemas.length))
  have hschemaLengthExpr :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (lenLocal "schemas") = .ok (.int (Int.ofNat schemas.length)) :=
    attesterEvalLocalArrayLength hSchemas
  have hschemaLengthL1 :
      L1.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) := by
    simp [L1]
  have hschemaUidsL1 : L1.get? "schemaUids" = some (.array schemaUids) := by
    simpa [L1] using
      (attesterStoreGetInsertOfNe (locals := locals) (name := "schemaUids")
        (other := "schemaLength") (value := .int (Int.ofNat schemas.length))
        hSchemaUids (by decide))
  have hguardSchema :
      evalExpr? (config v) { contract := contract v, locals := L1 } evm
        (.binary .and
          (.binary .ne (.var "schemaLength") (.intLit 0))
          (.binary .eq (.var "schemaLength") (lenLocal "schemaUids"))) =
        .ok (.bool true) := by
    have hleft :
        evalExpr? (config v) { contract := contract v, locals := L1 } evm
          (.binary .ne (.var "schemaLength") (.intLit 0)) =
        .ok (.bool true) :=
      attesterEvalUInt256NeZeroTrue (attesterEvalVarOfGet hschemaLengthL1) hSchemasNe
    have hright :
        evalExpr? (config v) { contract := contract v, locals := L1 } evm
          (.binary .eq (.var "schemaLength") (lenLocal "schemaUids")) =
        .ok (.bool true) := by
      have hlenExpr :
          evalExpr? (config v) { contract := contract v, locals := L1 } evm
            (lenLocal "schemaUids") = .ok (.int (Int.ofNat schemaUids.length)) :=
        attesterEvalLocalArrayLength hschemaUidsL1
      have hop :
          evalBinaryOp? .eq (.int (Int.ofNat schemas.length))
            (.int (Int.ofNat schemaUids.length)) = .ok (.bool true) := by
        simp [evalBinaryOp?, hLenEq]
      exact attesterEvalBinaryEq (attesterEvalVarOfGet hschemaLengthL1) hlenExpr hop
    exact attesterEvalAndTrue hleft hright
  have hmultiRequestsExpr :
      evalExpr? (config v) { contract := contract v, locals := L1 } evm
        (.newArray multiRevocationRequestSt (.var "schemaLength")) =
      .ok (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault)) :=
    attesterEvalNewMultiRevokeRequestArray (attesterEvalVarOfGet hschemaLengthL1)
  let L2 := L1.insert "multiRequests"
    (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault))
  have hiExpr :
      evalExpr? (config v) { contract := contract v, locals := L2 } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hargs :
      evalExprs? (config v) { contract := contract v, locals := loopLocals } evm
        [.var "multiRequests"] =
      .ok
        [.array (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)] := by
    have hrequestsDoneElem :
        loopLocals["multiRequests"]? =
          some (.array
            (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) := by
      rw [← Std.HashMap.get?_eq_getElem?]
      exact hrequestsDone
    simp [evalExprs?, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
      hrequestsDoneElem]
  refine ExecFuncBody.execBlockOK ?_
  simp [multiRevokeTransition, nonpayable]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (by simpa [L1] using ExecStmt.letDecl hschemaLengthExpr) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSchema) ?_
  refine ExecBlock.consNormal (by simpa [L2] using ExecStmt.letDecl hmultiRequestsExpr) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hiExpr) ?_
  refine ExecBlock.consNormal (by simpa [L1, L2] using hloop) ?_
  exact checkedExternalCallSuccess
    (receiver := easExpr v) (retVar := "_multiRevoke") (name := "multiRevoke")
    (sendVal := 0) (args := [.var "multiRequests"])
    (hguard loopLocals hrequestsDone)
    (attesterEvalEasExpr v { contract := contract v, locals := loopLocals } evm)
    hargs (hcall loopLocals hrequestsDone) hdec

theorem attesterMultiRevokeBodyLoopCallFailure (v : AttesterImmutables)
    (evm evm' : EVM.State) (locals loopLocals : Store) {schemas schemaUids : List Value}
    {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hSchemas : locals.get? "schemas" = some (.array schemas))
    (hSchemaUids : locals.get? "schemaUids" = some (.array schemaUids))
    (hSchemasNe : schemas.length ≠ 0)
    (hLenEq : schemaUids.length = schemas.length)
    (hloop :
      ExecStmt (config v)
        { contract := contract v,
          locals :=
            (((locals.insert "schemaLength" (.int (Int.ofNat schemas.length))).insert
              "multiRequests"
              (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault))).insert
              "i" (.int 0)) } evm
        (.while attesterMultiRevokeOuterSourceLoopCond attesterMultiRevokeOuterSourceLoopBody)
        (.ok { contract := contract v, locals := loopLocals } evm))
    (hrequestsDone :
      loopLocals.get? "multiRequests" =
        some (.array (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)))
    (hguard :
      ∀ locals' : Store,
        locals'.get? "multiRequests" =
            some (.array
              (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) →
        evalExpr? (config v) { contract := contract v, locals := locals' } evm
          (.binary .gt (.extCodeSize (easExpr v)) (.intLit 0)) = .ok (.bool true))
    (hcall :
      ∀ locals' : Store,
        locals'.get? "multiRequests" =
            some (.array
              (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) →
        typedCallViaEVM (config v) evm (EVM.address v.eas) "multiRevoke" 0
          [.array (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)]
          (false, evm', out)) :
    ExecTransitionBody (config v) (contract v) evm locals
      (multiRevokeTransition v).body .reverted := by
  let L1 := locals.insert "schemaLength" (.int (Int.ofNat schemas.length))
  have hschemaLengthExpr :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (lenLocal "schemas") = .ok (.int (Int.ofNat schemas.length)) :=
    attesterEvalLocalArrayLength hSchemas
  have hschemaLengthL1 :
      L1.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) := by
    simp [L1]
  have hschemaUidsL1 : L1.get? "schemaUids" = some (.array schemaUids) := by
    simpa [L1] using
      (attesterStoreGetInsertOfNe (locals := locals) (name := "schemaUids")
        (other := "schemaLength") (value := .int (Int.ofNat schemas.length))
        hSchemaUids (by decide))
  have hguardSchema :
      evalExpr? (config v) { contract := contract v, locals := L1 } evm
        (.binary .and
          (.binary .ne (.var "schemaLength") (.intLit 0))
          (.binary .eq (.var "schemaLength") (lenLocal "schemaUids"))) =
        .ok (.bool true) := by
    have hleft :
        evalExpr? (config v) { contract := contract v, locals := L1 } evm
          (.binary .ne (.var "schemaLength") (.intLit 0)) =
        .ok (.bool true) :=
      attesterEvalUInt256NeZeroTrue (attesterEvalVarOfGet hschemaLengthL1) hSchemasNe
    have hright :
        evalExpr? (config v) { contract := contract v, locals := L1 } evm
          (.binary .eq (.var "schemaLength") (lenLocal "schemaUids")) =
        .ok (.bool true) := by
      have hlenExpr :
          evalExpr? (config v) { contract := contract v, locals := L1 } evm
            (lenLocal "schemaUids") = .ok (.int (Int.ofNat schemaUids.length)) :=
        attesterEvalLocalArrayLength hschemaUidsL1
      have hop :
          evalBinaryOp? .eq (.int (Int.ofNat schemas.length))
            (.int (Int.ofNat schemaUids.length)) = .ok (.bool true) := by
        simp [evalBinaryOp?, hLenEq]
      exact attesterEvalBinaryEq (attesterEvalVarOfGet hschemaLengthL1) hlenExpr hop
    exact attesterEvalAndTrue hleft hright
  have hmultiRequestsExpr :
      evalExpr? (config v) { contract := contract v, locals := L1 } evm
        (.newArray multiRevocationRequestSt (.var "schemaLength")) =
      .ok (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault)) :=
    attesterEvalNewMultiRevokeRequestArray (attesterEvalVarOfGet hschemaLengthL1)
  let L2 := L1.insert "multiRequests"
    (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault))
  have hiExpr :
      evalExpr? (config v) { contract := contract v, locals := L2 } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hargs :
      evalExprs? (config v) { contract := contract v, locals := loopLocals } evm
        [.var "multiRequests"] =
      .ok
        [.array (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)] := by
    have hrequestsDoneElem :
        loopLocals["multiRequests"]? =
          some (.array
            (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) := by
      rw [← Std.HashMap.get?_eq_getElem?]
      exact hrequestsDone
    simp [evalExprs?, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
      hrequestsDoneElem]
  refine ExecFuncBody.execBlockRevert ?_
  simp [multiRevokeTransition, nonpayable]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (by simpa [L1] using ExecStmt.letDecl hschemaLengthExpr) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSchema) ?_
  refine ExecBlock.consNormal (by simpa [L2] using ExecStmt.letDecl hmultiRequestsExpr) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hiExpr) ?_
  refine ExecBlock.consNormal (by simpa [L1, L2] using hloop) ?_
  exact checkedExternalCallFailure
    (receiver := easExpr v) (retVar := "_multiRevoke") (name := "multiRevoke")
    (sendVal := 0) (args := [.var "multiRequests"])
    (hguard loopLocals hrequestsDone)
    (attesterEvalEasExpr v { contract := contract v, locals := loopLocals } evm)
    hargs (hcall loopLocals hrequestsDone)

theorem attesterMultiRevokeBodyLoopNoCode (v : AttesterImmutables)
    (evm : EVM.State) (locals loopLocals : Store) {schemas schemaUids : List Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hSchemas : locals.get? "schemas" = some (.array schemas))
    (hSchemaUids : locals.get? "schemaUids" = some (.array schemaUids))
    (hSchemasNe : schemas.length ≠ 0)
    (hLenEq : schemaUids.length = schemas.length)
    (hloop :
      ExecStmt (config v)
        { contract := contract v,
          locals :=
            (((locals.insert "schemaLength" (.int (Int.ofNat schemas.length))).insert
              "multiRequests"
              (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault))).insert
              "i" (.int 0)) } evm
        (.while attesterMultiRevokeOuterSourceLoopCond attesterMultiRevokeOuterSourceLoopBody)
        (.ok { contract := contract v, locals := loopLocals } evm))
    (hrequestsDone :
      loopLocals.get? "multiRequests" =
        some (.array (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)))
    (hguard :
      ∀ locals' : Store,
        locals'.get? "multiRequests" =
            some (.array
              (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) →
        evalExpr? (config v) { contract := contract v, locals := locals' } evm
          (.binary .gt (.extCodeSize (easExpr v)) (.intLit 0)) = .ok (.bool false)) :
    ExecTransitionBody (config v) (contract v) evm locals
      (multiRevokeTransition v).body .reverted := by
  let L1 := locals.insert "schemaLength" (.int (Int.ofNat schemas.length))
  have hschemaLengthExpr :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (lenLocal "schemas") = .ok (.int (Int.ofNat schemas.length)) :=
    attesterEvalLocalArrayLength hSchemas
  have hschemaLengthL1 :
      L1.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) := by
    simp [L1]
  have hschemaUidsL1 : L1.get? "schemaUids" = some (.array schemaUids) := by
    simpa [L1] using
      (attesterStoreGetInsertOfNe (locals := locals) (name := "schemaUids")
        (other := "schemaLength") (value := .int (Int.ofNat schemas.length))
        hSchemaUids (by decide))
  have hguardSchema :
      evalExpr? (config v) { contract := contract v, locals := L1 } evm
        (.binary .and
          (.binary .ne (.var "schemaLength") (.intLit 0))
          (.binary .eq (.var "schemaLength") (lenLocal "schemaUids"))) =
        .ok (.bool true) := by
    have hleft :
        evalExpr? (config v) { contract := contract v, locals := L1 } evm
          (.binary .ne (.var "schemaLength") (.intLit 0)) =
        .ok (.bool true) :=
      attesterEvalUInt256NeZeroTrue (attesterEvalVarOfGet hschemaLengthL1) hSchemasNe
    have hright :
        evalExpr? (config v) { contract := contract v, locals := L1 } evm
          (.binary .eq (.var "schemaLength") (lenLocal "schemaUids")) =
        .ok (.bool true) := by
      have hlenExpr :
          evalExpr? (config v) { contract := contract v, locals := L1 } evm
            (lenLocal "schemaUids") = .ok (.int (Int.ofNat schemaUids.length)) :=
        attesterEvalLocalArrayLength hschemaUidsL1
      have hop :
          evalBinaryOp? .eq (.int (Int.ofNat schemas.length))
            (.int (Int.ofNat schemaUids.length)) = .ok (.bool true) := by
        simp [evalBinaryOp?, hLenEq]
      exact attesterEvalBinaryEq (attesterEvalVarOfGet hschemaLengthL1) hlenExpr hop
    exact attesterEvalAndTrue hleft hright
  have hmultiRequestsExpr :
      evalExpr? (config v) { contract := contract v, locals := L1 } evm
        (.newArray multiRevocationRequestSt (.var "schemaLength")) =
      .ok (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault)) :=
    attesterEvalNewMultiRevokeRequestArray (attesterEvalVarOfGet hschemaLengthL1)
  let L2 := L1.insert "multiRequests"
    (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault))
  have hiExpr :
      evalExpr? (config v) { contract := contract v, locals := L2 } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  refine ExecFuncBody.execBlockRevert ?_
  simp [multiRevokeTransition, nonpayable]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (by simpa [L1] using ExecStmt.letDecl hschemaLengthExpr) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSchema) ?_
  refine ExecBlock.consNormal (by simpa [L2] using ExecStmt.letDecl hmultiRequestsExpr) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hiExpr) ?_
  refine ExecBlock.consNormal (by simpa [L1, L2] using hloop) ?_
  exact checkedExternalCallNoCode
    (receiver := easExpr v) (retVar := "_multiRevoke") (name := "multiRevoke")
    (sendVal := 0) (args := [.var "multiRequests"])
    (hguard loopLocals hrequestsDone)

theorem attesterMultiRevokeBodyLoopReverts (v : AttesterImmutables)
    (evm : EVM.State) (locals : Store) {schemas schemaUids : List Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hSchemas : locals.get? "schemas" = some (.array schemas))
    (hSchemaUids : locals.get? "schemaUids" = some (.array schemaUids))
    (hSchemasNe : schemas.length ≠ 0)
    (hLenEq : schemaUids.length = schemas.length)
    (hloop :
      ExecStmt (config v)
        { contract := contract v,
          locals :=
            (((locals.insert "schemaLength" (.int (Int.ofNat schemas.length))).insert
              "multiRequests"
              (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault))).insert
              "i" (.int 0)) } evm
        (.while attesterMultiRevokeOuterSourceLoopCond attesterMultiRevokeOuterSourceLoopBody)
        .reverted) :
    ExecTransitionBody (config v) (contract v) evm locals
      (multiRevokeTransition v).body .reverted := by
  let L1 := locals.insert "schemaLength" (.int (Int.ofNat schemas.length))
  have hschemaLengthExpr :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (lenLocal "schemas") = .ok (.int (Int.ofNat schemas.length)) :=
    attesterEvalLocalArrayLength hSchemas
  have hschemaLengthL1 :
      L1.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) := by
    simp [L1]
  have hschemaUidsL1 : L1.get? "schemaUids" = some (.array schemaUids) := by
    simpa [L1] using
      (attesterStoreGetInsertOfNe (locals := locals) (name := "schemaUids")
        (other := "schemaLength") (value := .int (Int.ofNat schemas.length))
        hSchemaUids (by decide))
  have hguardSchema :
      evalExpr? (config v) { contract := contract v, locals := L1 } evm
        (.binary .and
          (.binary .ne (.var "schemaLength") (.intLit 0))
          (.binary .eq (.var "schemaLength") (lenLocal "schemaUids"))) =
        .ok (.bool true) := by
    have hleft :
        evalExpr? (config v) { contract := contract v, locals := L1 } evm
          (.binary .ne (.var "schemaLength") (.intLit 0)) =
        .ok (.bool true) :=
      attesterEvalUInt256NeZeroTrue (attesterEvalVarOfGet hschemaLengthL1) hSchemasNe
    have hright :
        evalExpr? (config v) { contract := contract v, locals := L1 } evm
          (.binary .eq (.var "schemaLength") (lenLocal "schemaUids")) =
        .ok (.bool true) := by
      have hlenExpr :
          evalExpr? (config v) { contract := contract v, locals := L1 } evm
            (lenLocal "schemaUids") = .ok (.int (Int.ofNat schemaUids.length)) :=
        attesterEvalLocalArrayLength hschemaUidsL1
      have hop :
          evalBinaryOp? .eq (.int (Int.ofNat schemas.length))
            (.int (Int.ofNat schemaUids.length)) = .ok (.bool true) := by
        simp [evalBinaryOp?, hLenEq]
      exact attesterEvalBinaryEq (attesterEvalVarOfGet hschemaLengthL1) hlenExpr hop
    exact attesterEvalAndTrue hleft hright
  have hmultiRequestsExpr :
      evalExpr? (config v) { contract := contract v, locals := L1 } evm
        (.newArray multiRevocationRequestSt (.var "schemaLength")) =
      .ok (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault)) :=
    attesterEvalNewMultiRevokeRequestArray (attesterEvalVarOfGet hschemaLengthL1)
  let L2 := L1.insert "multiRequests"
    (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault))
  have hiExpr :
      evalExpr? (config v) { contract := contract v, locals := L2 } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  refine ExecFuncBody.execBlockRevert ?_
  simp [multiRevokeTransition, nonpayable]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (by simpa [L1] using ExecStmt.letDecl hschemaLengthExpr) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSchema) ?_
  refine ExecBlock.consNormal (by simpa [L2] using ExecStmt.letDecl hmultiRequestsExpr) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hiExpr) ?_
  simpa [L1, L2] using ExecBlock.consRevert hloop

set_option maxHeartbeats 1000000 in
theorem attesterMultiRevoke_postEncoder_fromDone
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (v : AttesterImmutables) {callargs LDone LStart : Store}
    {schemas schemaUids : List Value}
    {endPtr outerBase schemaLen secondLen secondPayload schemaPayload selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (hIcode : I.code = patchedRuntime v)
    (hd : dispatchMsg (contract v) I.calldata = some (multiRevokeTransition v))
    (hdec :
      decodeCalldataWithMode (config v).abiDecodeMode
          ((multiRevokeTransition v).params.map Param.name)
          (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
        some callargs)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hSchemas : callargs.get? "schemas" = some (.array schemas))
    (hSchemaUids : callargs.get? "schemaUids" = some (.array schemaUids))
    (hSchemasNe : schemas.length ≠ 0)
    (hLenEq : schemaUids.length = schemas.length)
    (hLStart :
      LStart =
        (((callargs.insert "schemaLength" (.int (Int.ofNat schemas.length))).insert
          "multiRequests"
          (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault))).insert
          "i" (.int 0)))
    (hloop :
      ExecStmt (config v) { contract := contract v, locals := LStart }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.while attesterMultiRevokeOuterSourceLoopCond attesterMultiRevokeOuterSourceLoopBody)
        (.ok { contract := contract v, locals := LDone }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
    (hrequestsDone :
      LDone.get? "multiRequests" =
        some (.array
          (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)))
    (rd775 :
      RD (patchedRuntime v) I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (⟨775⟩ : UInt256)
        [endPtr, attesterMultiRevokeSelectorLow, attesterMultiRevokeTargetWord v,
          outerBase, schemaLen, secondLen, secondPayload, schemaLen, schemaPayload,
          ⟨97⟩, selector]
        mem aw ByteArray.empty (cA, σ_evm) k C)
    (hcd :
      (config v).externalABI.encode? "multiRevoke"
          [.array (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)] =
        some
          (mem.readWithPadding (attesterMultiRevokeCallFree mem aw).toNat
            (UInt256.sub endPtr (attesterMultiRevokeCallFree mem aw)).toNat)) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let gS : Sat256 := Sat256.ofUInt256 g
  let evmEvm : EVM.State := initState cA gh bl σ_evm σ₀ gS A I
  let evmSolm : EVM.State := initState cA gh bl σ_solm σ₀ gS A I
  have hwvSolm : evmSolm.executionEnv.weiValue = ⟨0⟩ := by
    simpa [evmSolm, initState, gS] using hwv
  have hloopForBody :
      ExecStmt (config v)
        { contract := contract v,
          locals :=
            (((callargs.insert "schemaLength" (.int (Int.ofNat schemas.length))).insert
              "multiRequests"
              (.array (List.replicate schemas.length attesterMultiRevokeRequestDefault))).insert
              "i" (.int 0)) } evmSolm
        (.while attesterMultiRevokeOuterSourceLoopCond attesterMultiRevokeOuterSourceLoopBody)
        (.ok { contract := contract v, locals := LDone } evmSolm) := by
    simpa [evmSolm, gS, hLStart] using hloop
  obtain ⟨k787, C787, rd787⟩ :=
    attesterX_multiRevokeEncoderReturnToExtcodesize
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := gS) v rd775
  by_cases hcodeSizeEvm :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (attesterMultiRevokeTargetWord v) = ⟨0⟩
  · have hrdrev :=
      attesterX_multiRevokeNoCodeAtExtcodesize
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := gS) v rd787 hcodeSizeEvm (by simp)
    have hcodeSizeSolm :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (attesterMultiRevokeTargetWord v) = ⟨0⟩ :=
      attesterMultiRevokeCodeSize_zero_accountMapEquiv v hAccounts hcodeSizeEvm
    have hcodeSolmRaw :=
      attesterMultiRevokeEasCode_zero_of_codeSize_zero
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := gS) v hcodeSizeSolm
    have haddr : EVM.address v.eas = v.eas := by
      apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt v.eas.isLt
    have hcodeSolm :
        (UInt256.ofNat
          ((evmSolm.lookupAccount v.eas).option 0 (fun acc => acc.code.size))).toNat =
            0 := by
      simpa [evmSolm, haddr] using hcodeSolmRaw
    have hguard :
        ∀ locals' : Store,
          locals'.get? "multiRequests" =
              some (.array
                (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) →
          evalExpr? (config v) { contract := contract v, locals := locals' } evmSolm
            (.binary .gt (.extCodeSize (easExpr v)) (.intLit 0)) = .ok (.bool false) := by
      intro locals' _hrequests
      exact attesterMultiRevokeEvalExtCodeGuard_false v
        (attesterEvalEasExpr v { contract := contract v, locals := locals' } evmSolm)
        hcodeSolm
    have hbody :=
      attesterMultiRevokeBodyLoopNoCode v evmSolm callargs LDone
        hwvSolm hSchemas hSchemaUids hSchemasNe hLenEq hloopForBody
        hrequestsDone hguard
    exact hrdrev.reEquivExecutionRevert hIcode hd hdec hbody
  · have hcodeSizeSolmNe :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (attesterMultiRevokeTargetWord v) ≠ ⟨0⟩ :=
      attesterMultiRevokeCodeSize_ne_accountMapEquiv v hAccounts hcodeSizeEvm
    have hcodeSolmRaw :=
      attesterMultiRevokeEasCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := gS) v hcodeSizeSolmNe
    have haddr : EVM.address v.eas = v.eas := by
      apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt v.eas.isLt
    have hcodeSolm :
        0 < (UInt256.ofNat
          ((evmSolm.lookupAccount v.eas).option 0 (fun acc => acc.code.size))).toNat := by
      simpa [evmSolm, haddr] using hcodeSolmRaw
    have hguard :
        ∀ locals' : Store,
          locals'.get? "multiRequests" =
              some (.array
                (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) →
          evalExpr? (config v) { contract := contract v, locals := locals' } evmSolm
            (.binary .gt (.extCodeSize (easExpr v)) (.intLit 0)) = .ok (.bool true) := by
      intro locals' _hrequests
      exact attesterMultiRevokeEvalExtCodeGuard_true v
        (attesterEvalEasExpr v { contract := contract v, locals := locals' } evmSolm)
        hcodeSolm
    by_cases hdepth : I.depth.val < 1024
    · obtain ⟨cA', σ', z, o, A', k802, C802, rd802, hcallEvm, hosize⟩ :=
        attesterX_multiRevokeCallAtExtcodesize
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
          (A := A) (I := I) (g := gS) v
          (args := [.array
            (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)])
          rd787 hcodeSizeEvm (attesterMultiRevokeTarget_eq v) hcd hperm hdepth
          (by simp)
      let evmPostEvm : EVM.State :=
        { evmEvm with accountMap := σ', substate := A', createdAccounts := cA' }
      have hcallEvm' :
          typedCallViaEVM (config v) evmEvm (EVM.address v.eas) "multiRevoke" 0
            [.array
              (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)]
            (z, evmPostEvm, o) true := by
        simpa [evmEvm, evmPostEvm, gS] using hcallEvm
      obtain ⟨σSolmPost, ASolmPost, hcallSolm, hStateCall⟩ :=
        typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallEvm')
          (by simp [evmEvm, evmPostEvm, initState, gS]) hAccounts
      let evmPostSolm : EVM.State :=
        { evmSolm with
          accountMap := σSolmPost, substate := ASolmPost, createdAccounts := cA' }
      have hcallSolm' :
          typedCallViaEVM (config v) evmSolm (EVM.address v.eas) "multiRevoke" 0
            [.array
              (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)]
            (z, evmPostSolm, o) true := by
        simpa [evmPostSolm] using hcallSolm
      have hStateCall' : EVMStateEquiv evmPostEvm evmPostSolm := by
        simpa [evmPostSolm] using hStateCall
      cases z
      · simp only [Bool.false_eq_true, if_false] at rd802 hcallSolm'
        have hrdrev := attesterX_multiRevokePostRevert (v := v) rd802 hosize (by simp)
        have hbody :=
          attesterMultiRevokeBodyLoopCallFailure v evmSolm evmPostSolm
            callargs LDone hwvSolm hSchemas hSchemaUids hSchemasNe hLenEq
            hloopForBody hrequestsDone hguard (fun _ _ => hcallSolm')
        exact hrdrev.reEquivExecutionRevert hIcode hd hdec hbody
      · simp only [if_true] at rd802 hcallSolm'
        have hrdret := attesterX_multiRevokeSuccessStop (v := v) rd802
        have hretdec := attesterDecode_multiRevoke_return_ok v o
        have hbody :=
          attesterMultiRevokeBodyLoopSuccess v evmSolm evmPostSolm
            callargs LDone hwvSolm hSchemas hSchemaUids hSchemasNe hLenEq
            hloopForBody hrequestsDone hguard (fun _ _ => hcallSolm') hretdec
        have henc :
            returnEquiv ByteArray.empty none (multiRevokeTransition v).returnType := by
          rw [show (multiRevokeTransition v).returnType = [] by rfl]
          exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
        exact hrdret.reEquivExecutionGenEVMStateEquiv hIcode hd hdec hbody
          rfl (accountMapEquiv.refl σ') hStateCall' henc
    · have hdepth1024 : I.depth = 1024 := by
        apply Fin.ext
        have hlt := I.depth.isLt
        rw [not_lt] at hdepth
        omega
      have hrdrev :=
        attesterX_multiRevokeCallDepthLimitAtExtcodesize
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
          (A := A) (I := I) (g := gS) v rd787 hcodeSizeEvm hdepth1024
          (by simp)
      have hdepthInit : evmSolm.executionEnv.depth = 1024 := by
        simpa [evmSolm, initState, gS] using hdepth1024
      have hcallSolm :
          typedCallViaEVM (config v) evmSolm (EVM.address v.eas) "multiRevoke" 0
            [.array
              (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)]
            (false,
              { evmSolm with
                substate := (evmSolm.addAccessedAccount (EVM.address v.eas)).substate },
              ByteArray.empty)
            true :=
        callNotMade_depthLimit
          (cfg := config v) (evm := evmSolm) (tgt := EVM.address v.eas)
          (name := "multiRevoke")
          (args := [.array
            (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)])
          (callPerm := true) hcd hdepthInit
      have hbody :=
        attesterMultiRevokeBodyLoopCallFailure v evmSolm
          ({ evmSolm with
            substate := (evmSolm.addAccessedAccount (EVM.address v.eas)).substate })
          callargs LDone hwvSolm hSchemas hSchemaUids hSchemasNe hLenEq
          hloopForBody hrequestsDone hguard (fun _ _ => hcallSolm)
      exact hrdrev.reEquivExecutionRevert hIcode hd hdec hbody

set_option maxHeartbeats 1000000 in
theorem attesterMultiRevokeBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (v : AttesterImmutables) {code : ByteArray}
    (hpatch : patchRuntime attesterBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hpatched : code = patchedRuntime v := code_eq_patchedRuntime_of_patch hpatch
  have hIcode : I.code = patchedRuntime v := hcode.trans hpatched
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I attesterMultiRevokeSelBytes attesterMultiRevokeSelBytes_size
      hmultiRevoke
  have hd := attesterDispatch_multiRevoke v hmultiRevoke
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · by_cases hoff0 : solcMaxU64 < (calldataWord I.calldata 4).toNat
      · have hdec := attesterDecode_multiRevoke_none_firstOffsetHuge v hsz68 hoff0
        have hreach2128 :=
          attesterX_multiRevokeDecodeHeadOk
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g)
            v hIcode hwv hsz4 hsize hsz68 hsmall hmultiRevoke
        exact (attesterX_dynamic2FirstOffsetHugeReverts
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g)
            v hoff0 hreach2128)
          |>.reEquivDecodingFailed hIcode hd hdec
      · have hreach2128 :=
          attesterX_multiRevokeDecodeHeadOk
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g)
            v hIcode hwv hsz4 hsize hsz68 hsmall hmultiRevoke
        have hreach2149 :=
          attesterX_dynamic2FirstOffsetOk
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g)
            v hoff0 hreach2128
        have hreach2038 :=
          attesterX_dynamic2FirstArrayDecoderEntry
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g)
            v hreach2149
        by_cases hsizeSigned : I.calldata.size < 2 ^ 255
        · by_cases hlenWord :
            4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size
          · have _hreach2054 :=
              attesterX_dynamicArrayLengthGuardOk
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                (A := A) (I := I) (g := Sat256.ofUInt256 g)
                v hoff0 hsizeSigned hlenWord hreach2038
            by_cases hlenHuge : solcMaxU64 <
                (calldataWord I.calldata
                  (4 + (calldataWord I.calldata 4).toNat)).toNat
            · have hdec := attesterDecode_multiRevoke_none_firstLengthHuge
                v hsz68 hoff0 hlenWord hlenHuge
              exact (attesterX_dynamicArrayLengthMaxHugeReverts
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := Sat256.ofUInt256 g)
                  v hoff0 hlenHuge _hreach2054)
                |>.reEquivDecodingFailed hIcode hd hdec
            · have _hreach2076 :=
                attesterX_dynamicArrayLengthMaxOk
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := Sat256.ofUInt256 g)
                  v hoff0 hlenHuge _hreach2054
              by_cases hpayload :
                  4 + (calldataWord I.calldata 4).toNat + 32 +
                      32 * (calldataWord I.calldata
                        (4 + (calldataWord I.calldata 4).toNat)).toNat ≤
                    I.calldata.size
              · have hgt :=
                  attesterDynamicArrayPayloadGuardGtZero_of_ok
                    (I := I) hoff0 hlenHuge hsize hpayload
                have _hreach2102 :=
                  attesterX_dynamicArrayPayloadGuardOk
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := Sat256.ofUInt256 g)
                    v hgt _hreach2076
                have _hreach2161 :=
                  attesterX_dynamicArrayPayloadOkToFirstReturn
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := Sat256.ofUInt256 g)
                    v _hreach2102
                by_cases hoff1 : solcMaxU64 < (calldataWord I.calldata 36).toNat
                · have hdec := attesterDecode_multiRevoke_none_secondOffsetHuge
                    v hsz68 hoff0 hlenWord hlenHuge hpayload hoff1
                  exact (attesterX_dynamic2SecondOffsetHugeReverts
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := Sat256.ofUInt256 g)
                      v hoff1 _hreach2161)
                    |>.reEquivDecodingFailed hIcode hd hdec
                · have _hreach2191 :=
                    attesterX_dynamic2SecondOffsetOk
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := Sat256.ofUInt256 g)
                      v hoff1 _hreach2161
                  have _hreach2038Second :=
                    attesterX_dynamic2SecondArrayDecoderEntry
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := Sat256.ofUInt256 g)
                      v _hreach2191
                  by_cases hlen1Word :
                      4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size
                  · have _hreach2054Second :=
                      attesterX_secondArrayLengthGuardOk
                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                        (A := A) (I := I) (g := Sat256.ofUInt256 g)
                        v hoff1 hsizeSigned hlen1Word _hreach2038Second
                    by_cases hlen1Huge : solcMaxU64 <
                        (calldataWord I.calldata
                          (4 + (calldataWord I.calldata 36).toNat)).toNat
                    · have hdec := attesterDecode_multiRevoke_none_secondLengthHuge
                        v hsz68 hoff0 hlenWord hlenHuge hpayload hoff1 hlen1Word hlen1Huge
                      exact (attesterX_secondArrayLengthMaxHugeReverts
                          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                          (A := A) (I := I) (g := Sat256.ofUInt256 g)
                          v hoff1 hlen1Huge _hreach2054Second)
                        |>.reEquivDecodingFailed hIcode hd hdec
                    · have _hreach2076Second :=
                        attesterX_secondArrayLengthMaxOk
                          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                          (A := A) (I := I) (g := Sat256.ofUInt256 g)
                          v hoff1 hlen1Huge _hreach2054Second
                      by_cases hpayload1 :
                          4 + (calldataWord I.calldata 36).toNat + 32 +
                              32 * (calldataWord I.calldata
                                (4 + (calldataWord I.calldata 36).toNat)).toNat ≤
                            I.calldata.size
                      · have hgt :=
                          attesterSecondArrayPayloadGuardGtZero_of_ok
                            (I := I) hoff1 hlen1Huge hsize hpayload1
                        have _hreach2102Second :=
                          attesterX_secondArrayPayloadGuardOk
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                            (A := A) (I := I) (g := Sat256.ofUInt256 g)
                            v hgt _hreach2076Second
                        have _hreach2203 :=
                          attesterX_secondArrayPayloadOkToSecondReturn
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                            (A := A) (I := I) (g := Sat256.ofUInt256 g)
                            v _hreach2102Second
                        have _hreachDecoded :=
                          attesterX_dynamic2DecodeDone
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                            (A := A) (I := I) (g := Sat256.ofUInt256 g)
                            v (attesterMultiRevokeDecodedJumpdest v) _hreach2203
                        have _hreachBody :=
                          attesterX_multiRevokeDecodedToBody
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                            (A := A) (I := I) (g := Sat256.ofUInt256 g)
                            v _hreachDecoded
                        by_cases hbadDec :
                            ∃ callargs schemas schemaUids,
                              decodeCalldataWithMode (config v).abiDecodeMode
                                  ((multiRevokeTransition v).params.map Param.name)
                                  (transitionSignature (multiRevokeTransition v)).paramTypes
                                  I.calldata = some callargs ∧
                              callargs.get? "schemas" = some (.array schemas) ∧
                              callargs.get? "schemaUids" = some (.array schemaUids) ∧
                              schemas.length =
                                (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 4).toNat)).toNat ∧
                              schemaUids.length =
                                (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 36).toNat)).toNat ∧
                              (schemas.length = 0 ∨ schemas.length ≠ schemaUids.length)
                        · rcases hbadDec with
                            ⟨callargs, schemas, schemaUids, hdecFull, hSchemas, hSchemaUids,
                              hSchemasLen, hSchemaUidsLen, hbad⟩
                          have hwvSolm :
                              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.weiValue =
                                ⟨0⟩ := by
                            simpa [initState] using hwv
                          by_cases hzeroSchemas : schemas.length = 0
                          · have hrawZero :
                                (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 4).toNat)).toNat = 0 := by
                              omega
                            have hzeroEvm :=
                              attesterFirstArrayLengthWord_isZero_of_nat_eq_zero
                                (I := I) hoff0 hrawZero
                            have hrdrev :=
                              attesterX_multiRevokeLengthZeroReverts
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v hzeroEvm _hreachBody
                            have hbody :=
                              attesterMultiRevokeBodySchemaGuardReverts v
                                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                callargs hwvSolm hSchemas hSchemaUids (Or.inl hzeroSchemas)
                            exact hrdrev.reEquivExecutionRevert hIcode hd hdecFull hbody
                          · by_cases heqSchemas : schemas.length = schemaUids.length
                            · exfalso
                              rcases hbad with hzero | hne
                              · exact hzeroSchemas hzero
                              · exact hne heqSchemas
                            · have hrawFirstNe :
                                  (calldataWord I.calldata
                                    (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0 := by
                                intro hrawZero
                                exact hzeroSchemas (by omega)
                              have hrawNe :
                                  (calldataWord I.calldata
                                    (4 + (calldataWord I.calldata 36).toNat)).toNat ≠
                                    (calldataWord I.calldata
                                      (4 + (calldataWord I.calldata 4).toNat)).toNat := by
                                intro hrawEq
                                exact heqSchemas (by omega)
                              have hnonzeroEvm :=
                                attesterFirstArrayLengthWord_isZero_of_nat_ne_zero
                                  (I := I) hoff0 hrawFirstNe
                              have hneqEvm :=
                                attesterArrayLengthWords_eq_zero_of_nat_ne
                                  (I := I) hoff0 hoff1 hrawNe
                              have hrdrev :=
                                attesterX_multiRevokeLengthMismatchReverts
                                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                  (σ₀ := σ₀) (A := A) (I := I)
                                  (g := Sat256.ofUInt256 g) v hnonzeroEvm hneqEvm
                                  _hreachBody
                              have hbody :=
                                attesterMultiRevokeBodySchemaGuardReverts v
                                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                  callargs hwvSolm hSchemas hSchemaUids (Or.inr heqSchemas)
                              exact hrdrev.reEquivExecutionRevert hIcode hd hdecFull hbody
                        · have _hguardProgress :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiRevokeTransition v).params.map Param.name)
                                    (transitionSignature (multiRevokeTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ k C, RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  (⟨236⟩ : UInt256)
                                  [attesterFirstArrayLengthWord I,
                                    attesterSecondArrayLengthWord I,
                                    (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                    attesterFirstArrayLengthWord I,
                                    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                    ⟨97⟩, solcSelectorWord I]
                                  solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
                                  (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaUids, _hSchemas, _hSchemaUids,
                              hSchemasLen, hSchemaUidsLen, hnonzero, heqLen⟩ :=
                              attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            exact attesterX_multiRevokeLengthGuardOk_of_lengths
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) v hoff0 hoff1 hSchemasLen
                              hSchemaUidsLen hnonzero heqLen _hreachBody
                          have _hallocProgress :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiRevokeTransition v).params.map Param.name)
                                    (transitionSignature (multiRevokeTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ k C, RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  (⟨261⟩ : UInt256)
                                  [attesterFirstArrayLengthWord I, ⟨0⟩,
                                    attesterFirstArrayLengthWord I,
                                    attesterSecondArrayLengthWord I,
                                    (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                    attesterFirstArrayLengthWord I,
                                    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                    ⟨97⟩, solcSelectorWord I]
                                  solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
                                  (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            exact attesterX_multiRevokeAllocLengthMaxOk
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) v hoff0 hlenHuge
                              (_hguardProgress callargs hdecFull)
                          have _hinitProgress :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiRevokeTransition v).params.map Param.name)
                                    (transitionSignature (multiRevokeTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ k C, RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  (⟨291⟩ : UInt256)
                                  [((⟨32⟩ : UInt256) + ⟨128⟩),
                                    attesterFirstArrayLengthWord I, ⟨128⟩, ⟨0⟩,
                                    attesterFirstArrayLengthWord I,
                                    attesterSecondArrayLengthWord I,
                                    (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                    attesterFirstArrayLengthWord I,
                                    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                    ⟨97⟩, solcSelectorWord I]
                                  (attesterMultiOuterArrayAllocMem I) (UInt256.ofNat 5)
                                  ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaUids, _hSchemas, _hSchemaUids,
                              hSchemasLen, _hSchemaUidsLen, hnonzero, _heqLen⟩ :=
                              attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            have hrawFirstNe :
                                (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0 := by
                              intro hrawZero
                              exact hnonzero (by omega)
                            have hnonzeroEvm :=
                              attesterFirstArrayLengthWord_isZero_of_nat_ne_zero
                                (I := I) hoff0 hrawFirstNe
                            exact attesterX_multiRevokeOuterArrayInitEntry
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) v hnonzeroEvm
                              (_hallocProgress callargs hdecFull)
                          have _houterInitProgress :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiRevokeTransition v).params.map Param.name)
                                    (transitionSignature (multiRevokeTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨335⟩ : UInt256)
                                    (attesterMultiRevokeOuterArrayInitExitStack I
                                      ⟨128⟩ (attesterFirstArrayLengthWord I) a')
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaUids, _hSchemas, _hSchemaUids,
                              _hSchemasLen, _hSchemaUidsLen, hnonzero, _heqLen⟩ :=
                              attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            have hrawFirstNe :
                                (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0 := by
                              intro hrawZero
                              exact hnonzero (by omega)
                            have hlenNe :
                                (attesterFirstArrayLengthWord I).toNat ≠ 0 := by
                              rw [attesterFirstArrayLengthWord_toNat (I := I) hoff0]
                              exact hrawFirstNe
                            obtain ⟨k0, C0, rd0⟩ := _hinitProgress callargs hdecFull
                            exact attesterX_multiRevokeOuterArrayInitLoop
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) v
                              (slot := ((⟨32⟩ : UInt256) + ⟨128⟩))
                              (base := ⟨128⟩)
                              (len := attesterFirstArrayLengthWord I)
                              (mem := attesterMultiOuterArrayAllocMem I)
                              (aw := UInt256.ofNat 5) (k := k0) (C := C0) hlenNe rd0
                          have _houterInitProgressFree :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiRevokeTransition v).params.map Param.name)
                                    (transitionSignature (multiRevokeTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨335⟩ : UInt256)
                                    (attesterMultiRevokeOuterArrayInitExitStack I
                                      ⟨128⟩ (attesterFirstArrayLengthWord I) a')
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaUids, _hSchemas, _hSchemaUids,
                              hSchemasLen, _hSchemaUidsLen, hnonzero, _heqLen⟩ :=
                              attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            have hrawFirstNe :
                                (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0 := by
                              intro hrawZero
                              exact hnonzero (by omega)
                            have hlenNe :
                                (attesterFirstArrayLengthWord I).toNat ≠ 0 := by
                              rw [attesterFirstArrayLengthWord_toNat (I := I) hoff0]
                              exact hrawFirstNe
                            have hlenMaxWord :
                                (attesterFirstArrayLengthWord I).toNat ≤ solcMaxU64 := by
                              rw [attesterFirstArrayLengthWord_toNat (I := I) hoff0]
                              omega
                            exact attesterX_multiRevokeOuterArrayInitProgressWithFreeInvariant
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) v
                              hlenNe hlenMaxWord (_hinitProgress callargs hdecFull)
                          have _houterLoopFirstGuard :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiRevokeTransition v).params.map Param.name)
                                    (transitionSignature (multiRevokeTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨344⟩ : UInt256)
                                    (attesterMultiRevokeOuterArrayInitExitStack I
                                      ⟨128⟩ (attesterFirstArrayLengthWord I) a')
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaUids, _hSchemas, _hSchemaUids,
                              _hSchemasLen, _hSchemaUidsLen, hnonzero, _heqLen⟩ :=
                              attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            have hrawFirstNe :
                                (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0 := by
                              intro hrawZero
                              exact hnonzero (by omega)
                            have hlenNe :
                                (attesterFirstArrayLengthWord I).toNat ≠ 0 := by
                              rw [attesterFirstArrayLengthWord_toNat (I := I) hoff0]
                              exact hrawFirstNe
                            obtain ⟨a', k0, C0, hrem, rd0⟩ :=
                              _houterInitProgress callargs hdecFull
                            obtain ⟨k1, C1, rd1⟩ :=
                              attesterX_multiRevokeOuterSourceLoopFirstGuard
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v
                                (base := ⟨128⟩)
                                (len := attesterFirstArrayLengthWord I)
                                (mem := attesterMultiOuterArrayInitFinalMem a')
                                (aw := attesterMultiOuterArrayInitFinalAw a')
                                (k := k0) (C := C0) hlenNe
                                (by
                                  simpa [attesterMultiRevokeOuterArrayInitExitStack]
                                    using rd0)
                            exact ⟨a', k1, C1, hrem, by
                              simpa [attesterMultiRevokeOuterArrayInitExitStack]
                                using rd1⟩
                          have _houterLoopFirstGuardFree :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiRevokeTransition v).params.map Param.name)
                                    (transitionSignature (multiRevokeTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨344⟩ : UInt256)
                                    (attesterMultiRevokeOuterArrayInitExitStack I
                                      ⟨128⟩ (attesterFirstArrayLengthWord I) a')
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaUids, _hSchemas, _hSchemaUids,
                              _hSchemasLen, _hSchemaUidsLen, hnonzero, _heqLen⟩ :=
                              attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            have hrawFirstNe :
                                (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0 := by
                              intro hrawZero
                              exact hnonzero (by omega)
                            have hlenNe :
                                (attesterFirstArrayLengthWord I).toNat ≠ 0 := by
                              rw [attesterFirstArrayLengthWord_toNat (I := I) hoff0]
                              exact hrawFirstNe
                            exact attesterX_multiRevokeOuterSourceLoopFirstGuardWithInvariant
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) v
                              (attesterMultiRevokeOuterInitFreeInv I 0)
                              hlenNe (_houterInitProgressFree callargs hdecFull)
                          have _houterSecondArrayAccessCheck :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiRevokeTransition v).params.map Param.name)
                                    (transitionSignature (multiRevokeTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨355⟩ : UInt256)
                                    [⟨363⟩, ⟨1⟩, ⟨0⟩, attesterSecondArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
                                      attesterFirstArrayLengthWord I,
                                      attesterSecondArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      attesterFirstArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                      ⟨97⟩, solcSelectorWord I]
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaUids, _hSchemas, _hSchemaUids,
                              _hSchemasLen, hSchemaUidsLen, hnonzero, heqLen⟩ :=
                              attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            have hrawSecondNe :
                                (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0 := by
                              intro hrawZero
                              exact hnonzero (by
                                calc
                                  schemas.length = schemaUids.length := heqLen
                                  _ = (calldataWord I.calldata
                                      (4 + (calldataWord I.calldata 36).toNat)).toNat :=
                                    hSchemaUidsLen
                                  _ = 0 := hrawZero)
                            have hsecondLenNe :
                                (attesterSecondArrayLengthWord I).toNat ≠ 0 := by
                              rw [attesterSecondArrayLengthWord_toNat (I := I) hoff1]
                              exact hrawSecondNe
                            obtain ⟨a', k0, C0, hrem, rd0⟩ :=
                              _houterLoopFirstGuard callargs hdecFull
                            obtain ⟨k1, C1, rd1⟩ :=
                              attesterX_multiRevokeOuterSecondArrayAccessCheck
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v
                                (base := ⟨128⟩)
                                (len := attesterFirstArrayLengthWord I)
                                (mem := attesterMultiOuterArrayInitFinalMem a')
                                (aw := attesterMultiOuterArrayInitFinalAw a')
                                (k := k0) (C := C0) hsecondLenNe
                                (by
                                  simpa [attesterMultiRevokeOuterArrayInitExitStack]
                                    using rd0)
                            exact ⟨a', k1, C1, hrem, rd1⟩
                          have _houterSecondArrayAccessOk :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiRevokeTransition v).params.map Param.name)
                                    (transitionSignature (multiRevokeTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨363⟩ : UInt256)
                                    [⟨0⟩, attesterSecondArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
                                      attesterFirstArrayLengthWord I,
                                      attesterSecondArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      attesterFirstArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                      ⟨97⟩, solcSelectorWord I]
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaUids, _hSchemas, _hSchemaUids,
                              _hSchemasLen, hSchemaUidsLen, hnonzero, heqLen⟩ :=
                              attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            have hrawSecondNe :
                                (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0 := by
                              intro hrawZero
                              exact hnonzero (by
                                calc
                                  schemas.length = schemaUids.length := heqLen
                                  _ = (calldataWord I.calldata
                                      (4 + (calldataWord I.calldata 36).toNat)).toNat :=
                                    hSchemaUidsLen
                                  _ = 0 := hrawZero)
                            have hsecondLenNe :
                                (attesterSecondArrayLengthWord I).toNat ≠ 0 := by
                              rw [attesterSecondArrayLengthWord_toNat (I := I) hoff1]
                              exact hrawSecondNe
                            obtain ⟨a', k0, C0, hrem, rd0⟩ :=
                              _houterLoopFirstGuard callargs hdecFull
                            obtain ⟨k1, C1, rd1⟩ :=
                              attesterX_multiRevokeOuterSecondArrayAccessOk
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v
                                (base := ⟨128⟩)
                                (len := attesterFirstArrayLengthWord I)
                                (mem := attesterMultiOuterArrayInitFinalMem a')
                                (aw := attesterMultiOuterArrayInitFinalAw a')
                                (k := k0) (C := C0) hsecondLenNe
                                (by
                                  simpa [attesterMultiRevokeOuterArrayInitExitStack]
                                    using rd0)
                            exact ⟨a', k1, C1, hrem, rd1⟩
                          have _houterSecondArrayAccessOkFree :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiRevokeTransition v).params.map Param.name)
                                    (transitionSignature (multiRevokeTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨363⟩ : UInt256)
                                    [⟨0⟩, attesterSecondArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
                                      attesterFirstArrayLengthWord I,
                                      attesterSecondArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      attesterFirstArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                      ⟨97⟩, solcSelectorWord I]
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaUids, _hSchemas, _hSchemaUids,
                              _hSchemasLen, hSchemaUidsLen, hnonzero, heqLen⟩ :=
                              attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            have hrawSecondNe :
                                (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0 := by
                              intro hrawZero
                              exact hnonzero (by
                                calc
                                  schemas.length = schemaUids.length := heqLen
                                  _ = (calldataWord I.calldata
                                      (4 + (calldataWord I.calldata 36).toNat)).toNat :=
                                    hSchemaUidsLen
                                  _ = 0 := hrawZero)
                            have hsecondLenNe :
                                (attesterSecondArrayLengthWord I).toNat ≠ 0 := by
                              rw [attesterSecondArrayLengthWord_toNat (I := I) hoff1]
                              exact hrawSecondNe
                            exact attesterX_multiRevokeOuterSecondArrayAccessOkWithInvariant
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) v
                              (attesterMultiRevokeOuterInitFreeInv I 0)
                              hsecondLenNe
                              (_houterLoopFirstGuardFree callargs hdecFull)
                          have _hinnerDecoderEntry :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiRevokeTransition v).params.map Param.name)
                                    (transitionSignature (multiRevokeTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨2353⟩ : UInt256)
                                    [(UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩,
                                      ⟨128⟩, attesterFirstArrayLengthWord I,
                                      attesterSecondArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      attesterFirstArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                      ⟨97⟩, solcSelectorWord I]
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨a', k0, C0, hrem, rd0⟩ :=
                              _houterSecondArrayAccessOk callargs hdecFull
                            obtain ⟨k1, C1, rd1⟩ :=
                              attesterX_multiRevokeFirstInnerArrayDecoderEntryFromOuterSecond
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v
                                (mem := attesterMultiOuterArrayInitFinalMem a')
                                (aw := attesterMultiOuterArrayInitFinalAw a')
                                (k := k0) (C := C0) rd0
                            exact ⟨a', k1, C1, hrem, rd1⟩
                          have _hinnerDecoderEntryFree :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiRevokeTransition v).params.map Param.name)
                                    (transitionSignature (multiRevokeTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨2353⟩ : UInt256)
                                    [(UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩,
                                      ⟨128⟩, attesterFirstArrayLengthWord I,
                                      attesterSecondArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      attesterFirstArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                      ⟨97⟩, solcSelectorWord I]
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            exact attesterX_multiRevokeFirstInnerArrayDecoderEntryWithInvariant
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) v
                              (attesterMultiRevokeOuterInitFreeInv I 0)
                              (_houterSecondArrayAccessOkFree callargs hdecFull)
                          have _hinnerDecoderReturn :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiRevokeTransition v).params.map Param.name)
                                    (transitionSignature (multiRevokeTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨381⟩ : UInt256)
                                    [attesterFirstInnerArrayLengthWord I,
                                      attesterFirstInnerArrayStartWord I + ⟨32⟩,
                                      ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩,
                                      ⟨128⟩, attesterFirstArrayLengthWord I,
                                      attesterSecondArrayLengthWord I,
                                      attesterSecondArrayPayloadStartWord I,
                                      attesterFirstArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                      ⟨97⟩, solcSelectorWord I]
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaUids, _hSchemas, hSchemaUids,
                              _hSchemasLen, _hSchemaUidsLen, hnonzero, heqLen⟩ :=
                              attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            have hSchemaUidsNe : schemaUids.length ≠ 0 := by
                              intro hzero
                              exact hnonzero (by rw [heqLen, hzero])
                            obtain ⟨n, relativeOffset, inner, innerEnd, valuesRest, restEnd,
                                _hlen, _hlenMax, hreadFirst, hinner, _hrest,
                                _hshape, _hend⟩ :=
                              attesterDecode_multiRevoke_first_inner_decode v
                                hdecFull hSchemaUids hSchemaUidsNe
                            obtain ⟨hoffsetOk, hlenOk, hpayloadOk⟩ :=
                              attesterFirstInnerArrayGuardFacts_of_decode
                                (I := I) (elem := .bytes bytes32Width)
                                hoff1 hreadFirst
                                (by simpa [bytes32] using hinner)
                                hsizeSigned
                            obtain ⟨a', k0, C0, hrem, rd0⟩ :=
                              _hinnerDecoderEntry callargs hdecFull
                            obtain ⟨k1, C1, rd1⟩ :=
                              attesterX_multiRevokeFirstInnerArrayOffsetOk
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v hoffsetOk
                                (mem := attesterMultiOuterArrayInitFinalMem a')
                                (aw := attesterMultiOuterArrayInitFinalAw a')
                                (k := k0) (C := C0)
                                (by simpa [attesterSecondArrayPayloadStartWord] using rd0)
                            obtain ⟨k2, C2, rd2⟩ :=
                              attesterX_multiRevokeFirstInnerArrayLengthMaxOk
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v hlenOk
                                (mem := attesterMultiOuterArrayInitFinalMem a')
                                (aw := attesterMultiOuterArrayInitFinalAw a')
                                (k := k1) (C := C1) rd1
                            obtain ⟨k3, C3, rd3⟩ :=
                              attesterX_multiRevokeFirstInnerArrayPayloadOkToReturn
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v hpayloadOk
                                (mem := attesterMultiOuterArrayInitFinalMem a')
                                (aw := attesterMultiOuterArrayInitFinalAw a')
                                (k := k2) (C := C2) rd2
                            exact ⟨a', k3, C3, hrem, rd3⟩
                          have _hinnerDecoderReturnFree :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiRevokeTransition v).params.map Param.name)
                                    (transitionSignature (multiRevokeTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨381⟩ : UInt256)
                                    [attesterFirstInnerArrayLengthWord I,
                                      attesterFirstInnerArrayStartWord I + ⟨32⟩,
                                      ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩,
                                      ⟨128⟩, attesterFirstArrayLengthWord I,
                                      attesterSecondArrayLengthWord I,
                                      attesterSecondArrayPayloadStartWord I,
                                      attesterFirstArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                      ⟨97⟩, solcSelectorWord I]
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaUids, _hSchemas, hSchemaUids,
                              _hSchemasLen, _hSchemaUidsLen, hnonzero, heqLen⟩ :=
                              attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            have hSchemaUidsNe : schemaUids.length ≠ 0 := by
                              intro hzero
                              exact hnonzero (by rw [heqLen, hzero])
                            obtain ⟨n, relativeOffset, inner, innerEnd, valuesRest, restEnd,
                                _hlen, _hlenMax, hreadFirst, hinner, _hrest,
                                _hshape, _hend⟩ :=
                              attesterDecode_multiRevoke_first_inner_decode v
                                hdecFull hSchemaUids hSchemaUidsNe
                            obtain ⟨hoffsetOk, hlenOk, hpayloadOk⟩ :=
                              attesterFirstInnerArrayGuardFacts_of_decode
                                (I := I) (elem := .bytes bytes32Width)
                                hoff1 hreadFirst
                                (by simpa [bytes32] using hinner)
                                hsizeSigned
                            exact attesterX_multiRevokeFirstInnerArrayDecoderReturnWithInvariant
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) v
                              (attesterMultiRevokeOuterInitFreeInv I 0)
                              hoffsetOk hlenOk hpayloadOk
                              (_hinnerDecoderEntryFree callargs hdecFull)
                          by_cases hzeroBranch :
                              ∃ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiRevokeTransition v).params.map Param.name)
                                    (transitionSignature (multiRevokeTransition v)).paramTypes
                                    I.calldata = some callargs ∧
                                attesterFirstInnerArrayLengthWord I = ⟨0⟩
                          · rcases hzeroBranch with ⟨callargs, hdecFull, hinnerLenZeroWord⟩
                            obtain ⟨schemas, schemaUids, hSchemas, hSchemaUids,
                              _hSchemasLen, _hSchemaUidsLen, hnonzero, heqLen⟩ :=
                              attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            have hSchemaUidsNe : schemaUids.length ≠ 0 := by
                              intro hzero
                              exact hnonzero (by rw [heqLen, hzero])
                            obtain ⟨n, relativeOffset, inner, innerEnd, valuesRest, restEnd,
                                _hlen, _hlenMax, hreadFirst, hinner, _hrest,
                                hshape, _hend⟩ :=
                              attesterDecode_multiRevoke_first_inner_decode v
                                hdecFull hSchemaUids hSchemaUidsNe
                            have hinnerLenWord :
                                (attesterFirstInnerArrayLengthWord I).toNat = inner.length :=
                              attesterFirstInnerArrayLengthWord_toNat_of_decode
                                (I := I) (elem := .bytes bytes32Width)
                                hoff1 hreadFirst
                                (by simpa [bytes32] using hinner)
                                hsizeSigned
                            have hinnerLenZero : inner.length = 0 := by
                              rw [← hinnerLenWord]
                              simp [hinnerLenZeroWord]
                            have hinnerNil : inner = [] := by
                              simpa using hinnerLenZero
                            have hshapeEmpty : schemaUids = .array [] :: valuesRest := by
                              simpa [hinnerNil] using hshape
                            have hSchemaUidsEmpty :
                                callargs.get? "schemaUids" =
                                  some (.array (.array [] :: valuesRest)) := by
                              simpa [hshapeEmpty] using hSchemaUids
                            have hSchemasLenEmpty :
                                schemas.length = (.array [] :: valuesRest).length := by
                              calc
                                schemas.length = schemaUids.length := heqLen
                                _ = (.array [] :: valuesRest).length := by rw [hshapeEmpty]
                            obtain ⟨a', k3, C3, _hrem, rd3⟩ :=
                              _hinnerDecoderReturn callargs hdecFull
                            have hrdrev :=
                              attesterX_multiRevokeFirstInnerArrayLengthZeroReverts
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v
                                (mem := attesterMultiOuterArrayInitFinalMem a')
                                (aw := attesterMultiOuterArrayInitFinalAw a')
                                (k := k3) (C := C3)
                                hinnerLenZeroWord rd3
                            have hwvSolm :
                                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.weiValue =
                                  ⟨0⟩ := by
                              simpa [initState] using hwv
                            have hbody :=
                              attesterMultiRevokeBodyFirstUidLengthZeroReverts v
                                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                callargs hwvSolm hSchemas hSchemaUidsEmpty hnonzero
                                hSchemasLenEmpty
                            exact hrdrev.reEquivExecutionRevert hIcode hd hdecFull hbody
                          · have _hfirstInnerNonemptyProgress :
                                ∀ callargs,
                                  decodeCalldataWithMode (config v).abiDecodeMode
                                      ((multiRevokeTransition v).params.map Param.name)
                                      (transitionSignature (multiRevokeTransition v)).paramTypes
                                      I.calldata = some callargs →
                                  ∃ a' k C,
                                    a'.remaining = (⟨1⟩ : UInt256) ∧
                                    RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                      (⟨445⟩ : UInt256)
                                      [attesterFirstInnerArrayLengthWord I, ⟨0⟩,
                                        attesterFirstInnerArrayLengthWord I,
                                        attesterFirstInnerArrayLengthWord I,
                                        attesterFirstInnerArrayStartWord I + ⟨32⟩,
                                        ⟨0⟩, ⟨128⟩,
                                        attesterFirstArrayLengthWord I,
                                        attesterSecondArrayLengthWord I,
                                        attesterSecondArrayPayloadStartWord I,
                                        attesterFirstArrayLengthWord I,
                                        (UInt256.add ⟨4⟩
                                          (calldataWord I.calldata 4)) + ⟨32⟩,
                                        ⟨97⟩, solcSelectorWord I]
                                      (attesterMultiOuterArrayInitFinalMem a')
                                      (attesterMultiOuterArrayInitFinalAw a')
                                      ByteArray.empty (cA, σ_evm) k C := by
                              intro callargs hdecFull
                              obtain ⟨schemas, schemaUids, _hSchemas, hSchemaUids,
                                _hSchemasLen, _hSchemaUidsLen, hnonzero, heqLen⟩ :=
                                attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                  hbadDec hdecFull
                              have hSchemaUidsNe : schemaUids.length ≠ 0 := by
                                intro hzero
                                exact hnonzero (by rw [heqLen, hzero])
                              obtain ⟨n, relativeOffset, inner, innerEnd, valuesRest, restEnd,
                                  _hlen, _hlenMax, hreadFirst, hinner, _hrest,
                                  _hshape, _hend⟩ :=
                                attesterDecode_multiRevoke_first_inner_decode v
                                  hdecFull hSchemaUids hSchemaUidsNe
                              obtain ⟨_hoffsetOk, hlenOk, _hpayloadOk⟩ :=
                                attesterFirstInnerArrayGuardFacts_of_decode
                                  (I := I) (elem := .bytes bytes32Width)
                                  hoff1 hreadFirst
                                  (by simpa [bytes32] using hinner)
                                  hsizeSigned
                              have hinnerLenNeWord :
                                  attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩ := by
                                intro hzero
                                exact hzeroBranch ⟨callargs, hdecFull, hzero⟩
                              obtain ⟨a', k0, C0, hrem, rd0⟩ :=
                                _hinnerDecoderReturn callargs hdecFull
                              obtain ⟨k1, C1, rd1⟩ :=
                                attesterX_multiRevokeFirstInnerArrayNonemptyOk
                                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                  (σ₀ := σ₀) (A := A) (I := I)
                                  (g := Sat256.ofUInt256 g) v hinnerLenNeWord
                                  (mem := attesterMultiOuterArrayInitFinalMem a')
                                  (aw := attesterMultiOuterArrayInitFinalAw a')
                                  (k := k0) (C := C0) rd0
                              obtain ⟨k2, C2, rd2⟩ :=
                                attesterX_multiRevokeFirstInnerArrayLengthAllocMaxOk
                                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                  (σ₀ := σ₀) (A := A) (I := I)
                                  (g := Sat256.ofUInt256 g) v hlenOk
                                  (mem := attesterMultiOuterArrayInitFinalMem a')
                                  (aw := attesterMultiOuterArrayInitFinalAw a')
                                  (k := k1) (C := C1) rd1
                              exact ⟨a', k2, C2, hrem, rd2⟩
                            have _hfirstInnerNonemptyProgressFree :
                                ∀ callargs,
                                  decodeCalldataWithMode (config v).abiDecodeMode
                                      ((multiRevokeTransition v).params.map Param.name)
                                      (transitionSignature (multiRevokeTransition v)).paramTypes
                                      I.calldata = some callargs →
                                  ∃ a' k C,
                                    a'.remaining = (⟨1⟩ : UInt256) ∧
                                    attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
                                    RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                      (⟨445⟩ : UInt256)
                                      [attesterFirstInnerArrayLengthWord I, ⟨0⟩,
                                        attesterFirstInnerArrayLengthWord I,
                                        attesterFirstInnerArrayLengthWord I,
                                        attesterFirstInnerArrayStartWord I + ⟨32⟩,
                                        ⟨0⟩, ⟨128⟩,
                                        attesterFirstArrayLengthWord I,
                                        attesterSecondArrayLengthWord I,
                                        attesterSecondArrayPayloadStartWord I,
                                        attesterFirstArrayLengthWord I,
                                        (UInt256.add ⟨4⟩
                                          (calldataWord I.calldata 4)) + ⟨32⟩,
                                        ⟨97⟩, solcSelectorWord I]
                                      (attesterMultiOuterArrayInitFinalMem a')
                                      (attesterMultiOuterArrayInitFinalAw a')
                                      ByteArray.empty (cA, σ_evm) k C := by
                              intro callargs hdecFull
                              obtain ⟨schemas, schemaUids, _hSchemas, hSchemaUids,
                                _hSchemasLen, _hSchemaUidsLen, hnonzero, heqLen⟩ :=
                                attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                  hbadDec hdecFull
                              have hSchemaUidsNe : schemaUids.length ≠ 0 := by
                                intro hzero
                                exact hnonzero (by rw [heqLen, hzero])
                              obtain ⟨n, relativeOffset, inner, innerEnd, valuesRest, restEnd,
                                  _hlen, _hlenMax, hreadFirst, hinner, _hrest,
                                  _hshape, _hend⟩ :=
                                attesterDecode_multiRevoke_first_inner_decode v
                                  hdecFull hSchemaUids hSchemaUidsNe
                              obtain ⟨_hoffsetOk, hlenOk, _hpayloadOk⟩ :=
                                attesterFirstInnerArrayGuardFacts_of_decode
                                  (I := I) (elem := .bytes bytes32Width)
                                  hoff1 hreadFirst
                                  (by simpa [bytes32] using hinner)
                                  hsizeSigned
                              have hinnerLenNeWord :
                                  attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩ := by
                                intro hzero
                                exact hzeroBranch ⟨callargs, hdecFull, hzero⟩
                              exact attesterX_multiRevokeFirstInnerArrayNonemptyProgressWithInvariant
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v
                                (attesterMultiRevokeOuterInitFreeInv I 0)
                                hinnerLenNeWord hlenOk
                                (_hinnerDecoderReturnFree callargs hdecFull)
                            have _hfirstInnerAllocProgress :
                                ∀ callargs,
                                  decodeCalldataWithMode (config v).abiDecodeMode
                                      ((multiRevokeTransition v).params.map Param.name)
                                      (transitionSignature (multiRevokeTransition v)).paramTypes
                                      I.calldata = some callargs →
                                  ∃ a' k C,
                                    a'.remaining = (⟨1⟩ : UInt256) ∧
                                    RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                      (⟨475⟩ : UInt256)
                                      (((⟨32⟩ : UInt256) +
                                          attesterInnerArrayAllocFreeWord
                                            (attesterMultiOuterArrayInitFinalMem a')
                                            (attesterMultiOuterArrayInitFinalAw a')) ::
                                        attesterFirstInnerArrayLengthWord I ::
                                        attesterInnerArrayAllocFreeWord
                                          (attesterMultiOuterArrayInitFinalMem a')
                                          (attesterMultiOuterArrayInitFinalAw a') ::
                                        ⟨0⟩ ::
                                        attesterFirstInnerArrayLengthWord I ::
                                        attesterFirstInnerArrayLengthWord I ::
                                        (attesterFirstInnerArrayStartWord I + ⟨32⟩) ::
                                        [⟨0⟩, ⟨128⟩,
                                          attesterFirstArrayLengthWord I,
                                          attesterSecondArrayLengthWord I,
                                          attesterSecondArrayPayloadStartWord I,
                                          attesterFirstArrayLengthWord I,
                                          (UInt256.add ⟨4⟩
                                            (calldataWord I.calldata 4)) + ⟨32⟩,
                                          ⟨97⟩, solcSelectorWord I])
                                      (attesterInnerArrayAllocMem
                                        (attesterFirstInnerArrayLengthWord I)
                                        (attesterMultiOuterArrayInitFinalMem a')
                                        (attesterMultiOuterArrayInitFinalAw a'))
                                      (attesterInnerArrayAllocAw
                                        (attesterFirstInnerArrayLengthWord I)
                                        (attesterMultiOuterArrayInitFinalMem a')
                                        (attesterMultiOuterArrayInitFinalAw a'))
                                      ByteArray.empty (cA, σ_evm) k C := by
                              intro callargs hdecFull
                              have hinnerLenNeWord :
                                  attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩ := by
                                intro hzero
                                exact hzeroBranch ⟨callargs, hdecFull, hzero⟩
                              exact attesterX_multiRevokeFirstInnerArrayAllocProgress
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v hinnerLenNeWord
                                (_hfirstInnerNonemptyProgress callargs hdecFull)
                            have _hfirstInnerAllocProgressFree :
                                ∀ callargs,
                                  decodeCalldataWithMode (config v).abiDecodeMode
                                      ((multiRevokeTransition v).params.map Param.name)
                                      (transitionSignature (multiRevokeTransition v)).paramTypes
                                      I.calldata = some callargs →
                                  ∃ a' k C,
                                    a'.remaining = (⟨1⟩ : UInt256) ∧
                                    attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
                                    RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                      (⟨475⟩ : UInt256)
                                      (((⟨32⟩ : UInt256) +
                                          attesterInnerArrayAllocFreeWord
                                            (attesterMultiOuterArrayInitFinalMem a')
                                            (attesterMultiOuterArrayInitFinalAw a')) ::
                                        attesterFirstInnerArrayLengthWord I ::
                                        attesterInnerArrayAllocFreeWord
                                          (attesterMultiOuterArrayInitFinalMem a')
                                          (attesterMultiOuterArrayInitFinalAw a') ::
                                        ⟨0⟩ ::
                                        attesterFirstInnerArrayLengthWord I ::
                                        attesterFirstInnerArrayLengthWord I ::
                                        (attesterFirstInnerArrayStartWord I + ⟨32⟩) ::
                                        [⟨0⟩, ⟨128⟩,
                                          attesterFirstArrayLengthWord I,
                                          attesterSecondArrayLengthWord I,
                                          attesterSecondArrayPayloadStartWord I,
                                          attesterFirstArrayLengthWord I,
                                          (UInt256.add ⟨4⟩
                                            (calldataWord I.calldata 4)) + ⟨32⟩,
                                          ⟨97⟩, solcSelectorWord I])
                                      (attesterInnerArrayAllocMem
                                        (attesterFirstInnerArrayLengthWord I)
                                        (attesterMultiOuterArrayInitFinalMem a')
                                        (attesterMultiOuterArrayInitFinalAw a'))
                                      (attesterInnerArrayAllocAw
                                        (attesterFirstInnerArrayLengthWord I)
                                        (attesterMultiOuterArrayInitFinalMem a')
                                        (attesterMultiOuterArrayInitFinalAw a'))
                                      ByteArray.empty (cA, σ_evm) k C := by
                              intro callargs hdecFull
                              have hinnerLenNeWord :
                                  attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩ := by
                                intro hzero
                                exact hzeroBranch ⟨callargs, hdecFull, hzero⟩
                              exact attesterX_multiRevokeFirstInnerArrayAllocProgressWithInvariant
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v
                                (attesterMultiRevokeOuterInitFreeInv I 0)
                                hinnerLenNeWord
                                (_hfirstInnerNonemptyProgressFree callargs hdecFull)
                            have _hfirstInnerInitProgress :
                                ∀ callargs,
                                  decodeCalldataWithMode (config v).abiDecodeMode
                                      ((multiRevokeTransition v).params.map Param.name)
                                      (transitionSignature (multiRevokeTransition v)).paramTypes
                                      I.calldata = some callargs →
                                  ∃ a' b' k C,
                                    a'.remaining = (⟨1⟩ : UInt256) ∧
                                    b'.remaining = (⟨1⟩ : UInt256) ∧
                                    RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                      (⟨518⟩ : UInt256)
                                      (attesterMultiRevokeInnerArrayInitExitStack I
                                        (attesterInnerArrayAllocFreeWord
                                          (attesterMultiOuterArrayInitFinalMem a')
                                          (attesterMultiOuterArrayInitFinalAw a'))
                                        (attesterFirstInnerArrayLengthWord I)
                                        (attesterFirstInnerArrayStartWord I + ⟨32⟩)
                                        b')
                                      (attesterMultiRevokeInnerArrayInitFinalMem b')
                                      (attesterMultiRevokeInnerArrayInitFinalAw b')
                                      ByteArray.empty (cA, σ_evm) k C := by
                              intro callargs hdecFull
                              have hinnerLenNeWord :
                                  attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩ := by
                                intro hzero
                                exact hzeroBranch ⟨callargs, hdecFull, hzero⟩
                              exact attesterX_multiRevokeFirstInnerArrayInitProgress
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v hinnerLenNeWord
                                (_hfirstInnerAllocProgress callargs hdecFull)
                            have _hfirstInnerInitProgressFree :
                                ∀ callargs,
                                  decodeCalldataWithMode (config v).abiDecodeMode
                                      ((multiRevokeTransition v).params.map Param.name)
                                      (transitionSignature (multiRevokeTransition v)).paramTypes
                                      I.calldata = some callargs →
                                  ∃ a' b' k C,
                                    a'.remaining = (⟨1⟩ : UInt256) ∧
                                    attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
                                    b'.remaining = (⟨1⟩ : UInt256) ∧
                                    attesterMultiRevokeInnerInitReadInv I a' 0 b' ∧
                                    RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                      (⟨518⟩ : UInt256)
                                      (attesterMultiRevokeInnerArrayInitExitStack I
                                        (attesterInnerArrayAllocFreeWord
                                          (attesterMultiOuterArrayInitFinalMem a')
                                          (attesterMultiOuterArrayInitFinalAw a'))
                                        (attesterFirstInnerArrayLengthWord I)
                                        (attesterFirstInnerArrayStartWord I + ⟨32⟩)
                                        b')
                                      (attesterMultiRevokeInnerArrayInitFinalMem b')
                                      (attesterMultiRevokeInnerArrayInitFinalAw b')
                                      ByteArray.empty (cA, σ_evm) k C := by
                              intro callargs hdecFull
                              obtain ⟨schemas, schemaUids, _hSchemas, hSchemaUids,
                                _hSchemasLen, _hSchemaUidsLen, hnonzero, heqLen⟩ :=
                                attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                  hbadDec hdecFull
                              have hSchemaUidsNe : schemaUids.length ≠ 0 := by
                                intro hzero
                                exact hnonzero (by rw [heqLen, hzero])
                              obtain ⟨n, relativeOffset, inner, innerEnd, valuesRest, restEnd,
                                  _hlen, _hinnerMax, hreadFirst, hinner, _hrest,
                                  _hshape, _hend⟩ :=
                                attesterDecode_multiRevoke_first_inner_decode v
                                  hdecFull hSchemaUids hSchemaUidsNe
                              have hinnerLenNeWord :
                                  attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩ := by
                                intro hzero
                                exact hzeroBranch ⟨callargs, hdecFull, hzero⟩
                              have hinnerLenMaxWord :
                                  (attesterFirstInnerArrayLengthWord I).toNat ≤ solcMaxU64 :=
                                attesterFirstInnerArrayLengthWord_le_solcMaxU64_of_decode
                                  (I := I) (elem := .bytes bytes32Width)
                                  hoff1 hreadFirst
                                  (by simpa [bytes32] using hinner)
                                  hsizeSigned
                              exact attesterX_multiRevokeFirstInnerArrayInitProgressWithReadInvariant
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v
                                hinnerLenNeWord hinnerLenMaxWord
                                (_hfirstInnerAllocProgressFree callargs hdecFull)
                            have _hfirstInnerCopyProgressFree :
                                ∀ callargs,
                                  decodeCalldataWithMode (config v).abiDecodeMode
                                      ((multiRevokeTransition v).params.map Param.name)
                                      (transitionSignature (multiRevokeTransition v)).paramTypes
                                      I.calldata = some callargs →
                                  ∃ a' b' c' k C,
                                    a'.remaining = (⟨1⟩ : UInt256) ∧
                                    attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
                                    b'.remaining = (⟨1⟩ : UInt256) ∧
                                    attesterMultiRevokeInnerInitReadInv I a' 0 b' ∧
                                    c'.idx = attesterFirstInnerArrayLengthWord I ∧
                                    attesterMultiRevokeInnerCopyReadInv I a' b' 0 c' ∧
                                    RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                      (⟨608⟩ : UInt256)
                                      (attesterMultiRevokeInnerArrayCopyStack
                                        (attesterInnerArrayAllocFreeWord
                                          (attesterMultiOuterArrayInitFinalMem a')
                                          (attesterMultiOuterArrayInitFinalAw a'))
                                        (attesterFirstInnerArrayLengthWord I)
                                        (attesterFirstInnerArrayStartWord I + ⟨32⟩)
                                        [⟨0⟩, ⟨128⟩,
                                          attesterFirstArrayLengthWord I,
                                          attesterSecondArrayLengthWord I,
                                          attesterSecondArrayPayloadStartWord I,
                                          attesterFirstArrayLengthWord I,
                                          (UInt256.add ⟨4⟩
                                            (calldataWord I.calldata 4)) + ⟨32⟩,
                                          ⟨97⟩, solcSelectorWord I]
                                        c')
                                      c'.mem c'.aw
                                      ByteArray.empty (cA, σ_evm) k C := by
                              intro callargs hdecFull
                              exact attesterX_multiRevokeFirstInnerArrayCopyProgressWithReadStateInvariant
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v
                                (_hfirstInnerInitProgressFree callargs hdecFull)
                            have _hfirstOuterLoopProgressFree :
                                ∀ callargs,
                                  decodeCalldataWithMode (config v).abiDecodeMode
                                      ((multiRevokeTransition v).params.map Param.name)
                                      (transitionSignature (multiRevokeTransition v)).paramTypes
                                      I.calldata = some callargs →
                                  ∃ a' b' c' k C,
                                    a'.remaining = (⟨1⟩ : UInt256) ∧
                                    attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
                                    b'.remaining = (⟨1⟩ : UInt256) ∧
                                    attesterMultiRevokeInnerInitReadInv I a' 0 b' ∧
                                    c'.idx = attesterFirstInnerArrayLengthWord I ∧
                                    attesterMultiRevokeInnerCopyReadInv I a' b' 0 c' ∧
                                    RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                      (⟨335⟩ : UInt256)
                                      [attesterMultiRevokePostCopyNextIdx (⟨0⟩ : UInt256),
                                        ⟨128⟩, attesterFirstArrayLengthWord I,
                                        attesterSecondArrayLengthWord I,
                                        attesterSecondArrayPayloadStartWord I,
                                        attesterFirstArrayLengthWord I,
                                        (UInt256.add ⟨4⟩
                                          (calldataWord I.calldata 4)) + ⟨32⟩,
                                        ⟨97⟩, solcSelectorWord I]
                                      (attesterMultiRevokePostCopyOuterMem
                                        (attesterInnerArrayAllocFreeWord
                                          (attesterMultiOuterArrayInitFinalMem a')
                                          (attesterMultiOuterArrayInitFinalAw a'))
                                        ⟨128⟩ I
                                        ((UInt256.add ⟨4⟩
                                            (calldataWord I.calldata 4)) + ⟨32⟩)
                                        (⟨0⟩ : UInt256) c'.mem c'.aw)
                                      (attesterMultiRevokePostCopyOuterAw
                                        (attesterInnerArrayAllocFreeWord
                                          (attesterMultiOuterArrayInitFinalMem a')
                                          (attesterMultiOuterArrayInitFinalAw a'))
                                        ⟨128⟩ I
                                        ((UInt256.add ⟨4⟩
                                            (calldataWord I.calldata 4)) + ⟨32⟩)
                                        (⟨0⟩ : UInt256) c'.mem c'.aw)
                                      ByteArray.empty (cA, σ_evm) k C := by
                              intro callargs hdecFull
                              obtain ⟨schemas, schemaUids, _hSchemas, _hSchemaUids,
                                hSchemasLen, _hSchemaUidsLen, hnonzero, _heqLen⟩ :=
                                attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                  hbadDec hdecFull
                              have hrawFirstNe :
                                  (calldataWord I.calldata
                                    (4 + (calldataWord I.calldata 4).toNat)).toNat ≠
                                      0 := by
                                intro hrawZero
                                exact hnonzero (by omega)
                              have hlenNe :
                                  (attesterFirstArrayLengthWord I).toNat ≠ 0 := by
                                rw [attesterFirstArrayLengthWord_toNat (I := I) hoff0]
                                exact hrawFirstNe
                              have hidxSchema :
                                  UInt256.lt (⟨0⟩ : UInt256)
                                    (attesterFirstArrayLengthWord I) = ⟨1⟩ :=
                                attesterUInt256_lt_zero_of_toNat_ne_zero hlenNe
                              exact
                                attesterX_multiRevokeFirstInnerCopyToOuterLoopWithReadInvariant
                                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                  (σ₀ := σ₀) (A := A) (I := I)
                                  (g := Sat256.ofUInt256 g) v hidxSchema
                                  (_hfirstInnerCopyProgressFree callargs hdecFull)
                            by_cases hdecSome :
                                ∃ callargs,
                                  decodeCalldataWithMode (config v).abiDecodeMode
                                      ((multiRevokeTransition v).params.map Param.name)
                                      (transitionSignature (multiRevokeTransition v)).paramTypes
                                      I.calldata = some callargs
                            · rcases hdecSome with ⟨callargs, hdecFull⟩
                              obtain ⟨schemas, schemaUids, hSchemas, hSchemaUids,
                                hSchemasLen, hSchemaUidsLen, hSchemasNe, hLenEqRaw⟩ :=
                                attesterDecode_multiRevoke_good_lengths_of_not_bad v
                                  hbadDec hdecFull
                              have hSchemasLenMax : schemas.length ≤ solcMaxU64 := by
                                rw [hSchemasLen]
                                exact Nat.le_of_not_gt hlenHuge
                              have hSchemasBound : schemas.length < 2 ^ 256 := by
                                exact lt_of_le_of_lt hSchemasLenMax (by native_decide)
                              have hLenEq : schemaUids.length = schemas.length := hLenEqRaw.symm
                              have hSchemaNorm :
                                  ∀ {idx schema}, lookupNth? schemas idx = some schema →
                                    normalizeRawBoolWord? schema = .ok schema := by
                                intro idx schema hlookup
                                exact attesterDecode_multiRevoke_schema_norm v
                                  hdecFull hSchemas hlookup
                              have hUidssShape :
                                  ∀ {idx value}, lookupNth? schemaUids idx = some value →
                                    ∃ uids,
                                      value = .array uids ∧
                                      uids.length < 2 ^ 256 ∧
                                      (∀ {j uid}, lookupNth? uids j = some uid →
                                        normalizeRawBoolWord? uid = .ok uid) := by
                                intro idx value hlookup
                                exact attesterDecode_multiRevoke_schemaUids_shape v
                                  hdecFull hSchemaUids hlookup
                              obtain ⟨cursor, L, k0, C0, hL, hInv0, rd335⟩ :=
                                attesterX_multiRevokeOuterInitToLoopInv
                                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                  (σ₀ := σ₀) (A := A) (I := I)
                                  (g := Sat256.ofUInt256 g) v
                                  hSchemas hSchemaUids hSchemasLen hSchemaUidsLen
                                  hoff0 hoff1 hSchemasLenMax
                                  (_houterInitProgressFree callargs hdecFull)
                              have hInv0Solm :
                                  AttesterMultiRevokeOuterLoopInv cA σ_evm I schemas schemaUids
                                    schemas.length cursor L
                                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) := by
                                simpa [AttesterMultiRevokeOuterLoopInv] using hInv0
                              have hloopResult :=
                                AttesterMultiRevokeOuterLoopInv.run_or_revert
                                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                  (σ₀ := σ₀) (A := A) (I := I)
                                  (g := Sat256.ofUInt256 g) v
                                  (callargs := callargs) (schemas := schemas)
                                  (schemaUids := schemaUids)
                                  hdecFull hSchemas hSchemaUids hoff0 hoff1 hsizeSigned
                                  hSchemasBound hSchemasLenMax hLenEq
                                  hSchemaNorm hUidssShape
                                  hInv0Solm k0 C0 rd335
                              rcases hloopResult with hdone | hrev
                              · rcases hdone with
                                  ⟨aDone, LDone, evmDone, kDone, CDone,
                                    hloop, hInvDone, rd698⟩
                                have hdoneFacts :=
                                  AttesterMultiRevokeOuterLoopInv.done
                                    (cA := cA) (σ := σ_evm) (I := I)
                                    (schemas := schemas) (schemaUids := schemaUids)
                                    (a := aDone) (L := LDone) (evm := evmDone)
                                    hInvDone
                                have hUidssOk :
                                    ∀ {idx value}, lookupNth? schemaUids idx = some value →
                                      ∃ uids,
                                        value = .array uids ∧
                                        uids.length ≠ 0 ∧
                                        uids.length < 2 ^ 256 ∧
                                        (∀ {j uid}, lookupNth? uids j = some uid →
                                          normalizeRawBoolWord? uid = .ok uid) :=
                                  AttesterMultiRevokeOuterLoopInv.done_uidss_ok
                                    (cA := cA) (σ := σ_evm) (I := I)
                                    (schemas := schemas) (schemaUids := schemaUids)
                                    (a := aDone) (L := LDone) (evm := evmDone)
                                    hLenEq hInvDone
                                have hUidssArray :
                                    ∀ {idx value}, lookupNth? schemaUids idx = some value →
                                      ∃ uids, value = .array uids := by
                                  intro idx value hlookup
                                  rcases hUidssOk hlookup with
                                    ⟨uids, hvalue, _hne, _hbound, _hnorm⟩
                                  exact ⟨uids, hvalue⟩
                                have hrequestsAll :
                                    attesterMultiRevokeRequestValuesPrefix schemas.length
                                        schemas schemaUids =
                                      attesterMultiRevokeRequestValues schemas schemaUids :=
                                  attesterMultiRevokeRequestValuesPrefix_all
                                    hLenEq hUidssArray
                                obtain ⟨LDoneSolm, hloopSolm, hInvDoneSolm⟩ :=
                                  attesterMultiRevokeOuterSourceLoop_from_inv
                                    (imm := v)
                                    (evm :=
                                      initState cA gh bl σ_solm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                    (schemas := schemas) (schemaUids := schemaUids)
                                    hSchemasBound hLenEq hSchemaNorm hUidssOk
                                    schemas.length L
                                    (AttesterMultiRevokeOuterLoopInv.source hInv0Solm)
                                have hrequestsDoneSolm :
                                    LDoneSolm.get? "multiRequests" =
                                      some (.array
                                        (attesterMultiRevokeRequestValuesPrefix
                                          schemas.length schemas schemaUids)) := by
                                  rcases hInvDoneSolm with
                                    ⟨iDone, _hschemasDone, _hschemaUidsDone,
                                      _hschemaLengthDone, hrequestsDone,
                                      _hiDone, hvariantDone, _hleDone⟩
                                  have hiDoneLen : iDone = schemas.length := by
                                    omega
                                  simpa [hiDoneLen] using hrequestsDone
                                obtain ⟨k2422, C2422, rd2422⟩ :=
                                  attesterX_multiRevokeDoneToEncoder
                                    (cA := cA) (gh := gh) (bl := bl)
                                    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
                                    (g := Sat256.ofUInt256 g) v
                                    hInvDone rd698
                                have hloadEncoder :=
                                  attesterMultiRevokeEncoderPreambleLoad_fromDone
                                    (cA := cA) (σ := σ_evm) (I := I)
                                    (schemas := schemas) (schemaUids := schemaUids)
                                    (a := aDone) (L := LDone) (evm := evmDone)
                                    hInvDone
                                obtain ⟨k2460, C2460, rd2460⟩ :=
                                  attesterX_multiRevokeEncoderPreambleToOuterLoop
                                    (cA := cA) (gh := gh) (bl := bl)
                                    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
                                    (g := Sat256.ofUInt256 g) v
                                    hloadEncoder rd2422
                                let encoderTail : List UInt256 :=
                                  [attesterMultiRevokeSelectorLow,
                                    attesterMultiRevokeTargetWord v, ⟨128⟩,
                                    attesterFirstArrayLengthWord I,
                                    attesterSecondArrayLengthWord I,
                                    attesterSecondArrayPayloadStartWord I,
                                    attesterFirstArrayLengthWord I,
                                    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                    ⟨97⟩, solcSelectorWord I]
                                have hencoderTail : encoderTail.length ≤ 1000 := by
                                  simp [encoderTail]
                                have hencoderInnerTail : encoderTail.length + 9 ≤ 1000 := by
                                  simp [encoderTail]
                                obtain ⟨encDone, k775, C775, hencExact, hencIdx, rd775⟩ :=
                                  attesterX_multiRevokeEncoderLoopToReturnExactState
                                    (cA := cA) (gh := gh) (bl := bl)
                                    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
                                    (g := Sat256.ofUInt256 g) v
                                    (idx := (⟨0⟩ : UInt256))
                                    (srcHead := ⟨128⟩ + ⟨32⟩)
                                    (len := attesterFirstArrayLengthWord I)
                                    (dstHead :=
                                      ⟨4⟩ + attesterMultiRevokeCallFree aDone.mem aDone.aw +
                                        ⟨64⟩)
                                    (endPtr :=
                                      ⟨4⟩ + attesterMultiRevokeCallFree aDone.mem aDone.aw +
                                          (attesterFirstArrayLengthWord I).shiftLeft ⟨5⟩ +
                                        ⟨64⟩)
                                    (scratch := (⟨0⟩ : UInt256))
                                    (dst :=
                                      ⟨4⟩ + attesterMultiRevokeCallFree aDone.mem aDone.aw)
                                    (src := (⟨128⟩ : UInt256))
                                    (tail := encoderTail)
                                    (mem :=
                                      attesterMultiRevokeEncoderLengthMem
                                        (attesterMultiRevokeCallMemAfterSelector aDone.mem aDone.aw)
                                        (⟨4⟩ + attesterMultiRevokeCallFree aDone.mem aDone.aw)
                                        (attesterFirstArrayLengthWord I))
                                    (aw :=
                                      attesterMultiRevokeEncoderAwAfterLength
                                        (attesterMultiRevokeCallAwAfterSelector aDone.mem aDone.aw)
                                        (⟨4⟩ + attesterMultiRevokeCallFree aDone.mem aDone.aw)
                                        ⟨128⟩)
                                    (k := k2460) (C := C2460)
                                    hencoderTail hencoderInnerTail rfl
                                    (by
                                      simpa [encoderTail] using rd2460)
                                have hcd :
                                    (config v).externalABI.encode? "multiRevoke"
                                        [.array
                                          (attesterMultiRevokeRequestValuesPrefix
                                            schemas.length schemas schemaUids)] =
                                      some
                                        (encDone.mem.readWithPadding
                                          (attesterMultiRevokeCallFree
                                            encDone.mem encDone.aw).toNat
                                          (UInt256.sub encDone.endPtr
                                  (attesterMultiRevokeCallFree
                                              encDone.mem encDone.aw)).toNat) := by
                                  have hReadLayout :
                                      AttesterMultiRevokeRequestsReadLayoutBounded
                                        schemas schemaUids schemas.length aDone.mem
                                        aDone.outerBase
                                        (aDone.outerBase.toNat + 32 +
                                          32 * schemas.length)
                                        (attesterInnerArrayAllocFreeWord
                                          aDone.mem aDone.aw).toNat :=
                                    AttesterMultiRevokeOuterLoopInv.done_readLayout
                                      (cA := cA) (σ := σ_evm) (I := I)
                                      (schemas := schemas) (schemaUids := schemaUids)
                                      (a := aDone) (L := LDone) (evm := evmDone)
                                      hInvDone
                                  obtain ⟨words, hwords⟩ :=
                                    attesterMultiRevokeRequestArrayElemsWords?_some_of_readLayoutBounded
                                      (schemas := schemas) (schemaUids := schemaUids)
                                      (mem := aDone.mem) (outerBase := aDone.outerBase)
                                      (contentLo :=
                                        aDone.outerBase.toNat + 32 + 32 * schemas.length)
                                      (bound :=
                                        (attesterInnerArrayAllocFreeWord
                                          aDone.mem aDone.aw).toNat)
                                      hLenEq hUidssArray hReadLayout
                                  rw [hrequestsAll]
                                  rw [attesterExternalABIEncode_multiRevokeRequestArray]
                                  rw [hwords]
                                  simp
                                  exact ?_
                                exact
                                  attesterMultiRevoke_postEncoder_fromDone
                                    (cA := cA) (gh := gh) (bl := bl)
                                    (σ_evm := σ_evm) (σ_solm := σ_solm)
                                    (σ₀ := σ₀) (A := A) (I := I)
                                    (g := g) v
                                    (callargs := callargs) (LDone := LDoneSolm)
                                    (LStart := L) (schemas := schemas)
                                    (schemaUids := schemaUids)
                                    (endPtr := encDone.endPtr)
                                    (outerBase := ⟨128⟩)
                                    (schemaLen := attesterFirstArrayLengthWord I)
                                    (secondLen := attesterSecondArrayLengthWord I)
                                    (secondPayload := attesterSecondArrayPayloadStartWord I)
                                    (schemaPayload :=
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩)
                                    (selector := solcSelectorWord I)
                                    (mem := encDone.mem) (aw := encDone.aw)
                                    (k := k775) (C := C775)
                                    hIcode hd hdecFull hperm hwv hAccounts
                                    hSchemas hSchemaUids hSchemasNe hLenEq
                                    hL hloopSolm hrequestsDoneSolm
                                    (by
                                      simpa [encoderTail] using rd775)
                                    hcd
                              · have hbodyRev :
                                  ExecTransitionBody (config v) (contract v)
                                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                    callargs (multiRevokeTransition v).body .reverted := by
                                  subst L
                                  exact attesterMultiRevokeBodyLoopReverts v
                                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                    callargs hwv hSchemas hSchemaUids hSchemasNe hLenEq hrev.1
                                exact hrev.2.reEquivExecutionRevert hIcode hd hdecFull hbodyRev
                            · have hdecNone :
                                  decodeCalldataWithMode (config v).abiDecodeMode
                                      ((multiRevokeTransition v).params.map Param.name)
                                      (transitionSignature (multiRevokeTransition v)).paramTypes
                                      I.calldata = none := by
                                cases hdecMaybe :
                                    decodeCalldataWithMode (config v).abiDecodeMode
                                        ((multiRevokeTransition v).params.map Param.name)
                                        (transitionSignature (multiRevokeTransition v)).paramTypes
                                        I.calldata with
                                | none => rfl
                                | some callargs =>
                                    exact False.elim (hdecSome ⟨callargs, hdecMaybe⟩)
                              by_cases hrawZero :
                                  (calldataWord I.calldata
                                    (4 + (calldataWord I.calldata 4).toNat)).toNat = 0
                              · have hzeroEvm :=
                                  attesterFirstArrayLengthWord_isZero_of_nat_eq_zero
                                    (I := I) hoff0 hrawZero
                                have hrdrev :=
                                  attesterX_multiRevokeLengthZeroReverts
                                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                    (σ₀ := σ₀) (A := A) (I := I)
                                    (g := Sat256.ofUInt256 g) v hzeroEvm _hreachBody
                                exact hrdrev.reEquivDecodingFailed hIcode hd hdecNone
                              · by_cases hrawEq :
                                  (calldataWord I.calldata
                                    (4 + (calldataWord I.calldata 36).toNat)).toNat =
                                  (calldataWord I.calldata
                                    (4 + (calldataWord I.calldata 4).toNat)).toNat
                                · exact ?_
                                · have hnonzeroEvm :=
                                    attesterFirstArrayLengthWord_isZero_of_nat_ne_zero
                                      (I := I) hoff0 hrawZero
                                  have hneqEvm :=
                                    attesterArrayLengthWords_eq_zero_of_nat_ne
                                      (I := I) hoff0 hoff1 hrawEq
                                  have hrdrev :=
                                    attesterX_multiRevokeLengthMismatchReverts
                                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                      (σ₀ := σ₀) (A := A) (I := I)
                                      (g := Sat256.ofUInt256 g) v hnonzeroEvm hneqEvm
                                      _hreachBody
                                  exact hrdrev.reEquivDecodingFailed hIcode hd hdecNone
                      · have hpayload1Short :
                            I.calldata.size <
                              4 + (calldataWord I.calldata 36).toNat + 32 +
                                32 * (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 36).toNat)).toNat :=
                          by
                            omega
                        have hdec := attesterDecode_multiRevoke_none_secondPayloadShort
                          v hsz68 hoff0 hlenWord hlenHuge hpayload hoff1 hlen1Word
                          hlen1Huge hpayload1Short
                        have hgt :=
                          attesterSecondArrayPayloadGuardGtOne_of_short
                            (I := I) hoff1 hlen1Huge hsize hpayload1Short
                        exact (attesterX_secondArrayPayloadGuardReverts
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                            (A := A) (I := I) (g := Sat256.ofUInt256 g)
                            v hgt _hreach2076Second)
                          |>.reEquivDecodingFailed hIcode hd hdec
                  · have hshort1 :
                        I.calldata.size < 4 + (calldataWord I.calldata 36).toNat + 32 := by
                      omega
                    have hdec := attesterDecode_multiRevoke_none_secondLengthShort
                      v hsz68 hoff0 hlenWord hlenHuge hpayload hoff1 hshort1
                    have hslt :=
                      attesterSecondArrayLengthGuardSltZero_of_short
                        (I := I) hoff1 hsizeSigned hshort1
                    exact (attesterX_secondArrayLengthGuardReverts
                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                        (A := A) (I := I) (g := Sat256.ofUInt256 g)
                        v hslt _hreach2038Second)
                      |>.reEquivDecodingFailed hIcode hd hdec
              · have hpayloadShort :
                  I.calldata.size <
                    4 + (calldataWord I.calldata 4).toNat + 32 +
                      32 * (calldataWord I.calldata
                        (4 + (calldataWord I.calldata 4).toNat)).toNat := by
                  omega
                have hdec := attesterDecode_multiRevoke_none_firstPayloadShort
                  v hsz68 hoff0 hlenWord hlenHuge hpayloadShort
                have hgt :=
                  attesterDynamicArrayPayloadGuardGtOne_of_short
                    (I := I) hoff0 hlenHuge hsize hpayloadShort
                exact (attesterX_dynamicArrayPayloadGuardReverts
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := Sat256.ofUInt256 g)
                    v hgt _hreach2076)
                  |>.reEquivDecodingFailed hIcode hd hdec
          · have hshortLen :
                I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32 := by
              omega
            have hdec := attesterDecode_multiRevoke_none_firstLengthShort
              v hsz68 hoff0 hshortLen
            have hslt :=
              attesterDynamicArrayLengthGuardSltZero_of_short
                (I := I) hoff0 hsizeSigned hshortLen
            exact (attesterX_dynamicArrayLengthGuardReverts
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                (A := A) (I := I) (g := Sat256.ofUInt256 g)
                v hslt hreach2038)
              |>.reEquivDecodingFailed hIcode hd hdec
        · have hbigSigned : 2 ^ 255 ≤ I.calldata.size := by omega
          have hdec := attesterDecode_multiRevoke_none_totalHuge v hbigSigned
          have hslt :=
            attesterDynamicArrayLengthGuardSltZero_of_sizeHuge
              (I := I) hoff0 hbigSigned hsize
          exact (attesterX_dynamicArrayLengthGuardReverts
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g)
              v hslt hreach2038)
            |>.reEquivDecodingFailed hIcode hd hdec
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := attesterDecode_multiRevoke_none_huge v hbig
      exact (attesterX_multiRevokeDecodeHuge (g := Sat256.ofUInt256 g) v hIcode hwv hsz4
          hsize hbig hmultiRevoke)
        |>.reEquivDecodingFailed hIcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := attesterDecode_multiRevoke_none_short v hsz4 hshort
    exact (attesterX_multiRevokeDecodeShort (g := Sat256.ofUInt256 g) v hIcode hwv hsz4
        hsize hshort hmultiRevoke)
      |>.reEquivDecodingFailed hIcode hd hdec

end Benchmarks.EAS.Attester
