import Benchmarks.EAS.Attester.MultiSource
import Benchmarks.EAS.Attester.InnerArrayCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

/-! ## `multiAttest(bytes32[],uint256[][])` -/

theorem attesterDecode_multiAttest_none_short (v : AttesterImmutables) {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  show decodeCalldata ["schemas", "schemaInputs"] [bytes32Array, uint256NestedArray]
      I.calldata = none
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hbig⟩; rw [htlen] at hbig; omega)]
  rw [if_neg (by rintro ⟨_, hbig⟩; rw [List.length_drop, htlen] at hbig; omega)]
  rw [if_neg (by rintro ⟨_, hbig⟩; rw [htlen] at hbig; omega)]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32Array, uint256NestedArray] = some 64 by native_decide]
  simp only [bind, Option.bind]
  have hargsShort : (I.calldata.toList.drop 4).length < 64 := by
    rw [List.length_drop, htlen]
    omega
  rw [if_pos hargsShort]

theorem attesterDecode_multiAttest_none_huge (v : AttesterImmutables) {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  show decodeCalldata ["schemas", "schemaInputs"] [bytes32Array, uint256NestedArray]
      I.calldata = none
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_pos]
  · exact ⟨by native_decide, by rw [htlen]; omega⟩

theorem attesterDecode_multiAttest_none_totalHuge (v : AttesterImmutables) {I : ExecutionEnv}
    (hbig : 2 ^ 255 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaInputs"] [bytes32Array, uint256NestedArray]
      I.calldata = none
  simpa [bytes32Array, uint256NestedArray, uint256Array] using
    attesterDecodeCalldata_twoDynamicArrays_none_totalHuge
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaInputs")
      (elem0 := bytes32) (elem1 := uint256) hbig

theorem attesterDecode_multiAttest_none_firstOffsetHuge (v : AttesterImmutables)
    {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hoff : solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaInputs"] [bytes32Array, uint256NestedArray]
      I.calldata = none
  simpa [bytes32Array, uint256NestedArray, uint256Array] using
    attesterDecodeCalldata_twoDynamicArrays_none_firstOffsetHuge
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaInputs")
      (elem0 := bytes32) (elem1 := uint256) hsz68 hoff

theorem attesterDecode_multiAttest_none_firstLengthShort (v : AttesterImmutables)
    {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaInputs"] [bytes32Array, uint256NestedArray]
      I.calldata = none
  simpa [bytes32Array, uint256NestedArray, uint256Array] using
    attesterDecodeCalldata_twoDynamicArrays_none_firstLengthShort
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaInputs")
      (elem0 := bytes32) (elem1 := uint256) hsz68 hoffMax hshort

theorem attesterDecode_multiAttest_none_firstLengthHuge (v : AttesterImmutables)
    {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenHuge : solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaInputs"] [bytes32Array, uint256NestedArray]
      I.calldata = none
  simpa [bytes32Array, uint256NestedArray, uint256Array] using
    attesterDecodeCalldata_twoDynamicArrays_none_firstLengthHuge
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaInputs")
      (elem0 := bytes32) (elem1 := uint256) hsz68 hoffMax hlenWord hlenHuge

theorem attesterDecode_multiAttest_none_firstPayloadShort (v : AttesterImmutables)
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
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaInputs"] [bytes32Array, uint256NestedArray]
      I.calldata = none
  simpa [bytes32Array, uint256NestedArray, uint256Array] using
    attesterDecodeCalldata_twoDynamicArrays_none_firstBytes32PayloadShort
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaInputs")
      (elem1 := uint256) hsz68 hoffMax hlenWord hlenMax hpayload

theorem attesterDecode_multiAttest_none_secondOffsetHuge (v : AttesterImmutables)
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
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaInputs"] [bytes32Array, uint256NestedArray]
      I.calldata = none
  simpa [bytes32Array, uint256NestedArray, uint256Array] using
    attesterDecodeCalldata_twoDynamicArrays_none_secondOffsetHuge
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaInputs")
      (elem1 := uint256) hsz68 hoff0Max hlenWord hlen0Max hpayload0 hoff1Huge

theorem attesterDecode_multiAttest_none_secondLengthShort (v : AttesterImmutables)
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
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaInputs"] [bytes32Array, uint256NestedArray]
      I.calldata = none
  simpa [bytes32Array, uint256NestedArray, uint256Array] using
    attesterDecodeCalldata_twoDynamicArrays_none_secondLengthShort
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaInputs")
      (elem1 := uint256) hsz68 hoff0Max hlen0Word hlen0Max hpayload0 hoff1Max hshort1

theorem attesterDecode_multiAttest_none_secondLengthHuge (v : AttesterImmutables)
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
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaInputs"] [bytes32Array, uint256NestedArray]
      I.calldata = none
  simpa [bytes32Array, uint256NestedArray, uint256Array] using
    attesterDecodeCalldata_twoDynamicArrays_none_secondLengthHuge
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaInputs")
      (elem1 := uint256) hsz68 hoff0Max hlen0Word hlen0Max hpayload0 hoff1Max hlen1Word
      hlen1Huge

theorem attesterDecode_multiAttest_none_secondPayloadShort (v : AttesterImmutables)
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
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata = none := by
  show decodeCalldata ["schemas", "schemaInputs"] [bytes32Array, uint256NestedArray]
      I.calldata = none
  simpa [bytes32Array, uint256NestedArray, uint256Array] using
    attesterDecodeCalldata_twoDynamicArrays_none_secondPayloadShort
      (cd := I.calldata) (name0 := "schemas") (name1 := "schemaInputs")
      (elem1 := uint256) hsz68 hoff0Max hlen0Word hlen0Max hpayload0 hoff1Max hlen1Word
      hlen1Max hpayload1

theorem attesterDecode_multiAttest_some_shape (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata =
      some callargs) :
    ∃ schemas schemaInputs : List Value,
      callargs.get? "schemas" = some (.array schemas) ∧
      callargs.get? "schemaInputs" = some (.array schemaInputs) := by
  have hdec' :
      decodeCalldata ["schemas", "schemaInputs"]
        [.dynamicArray bytes32, .dynamicArray (.dynamicArray uint256)] I.calldata =
      some callargs := by
    simpa [decodeCalldataWithMode, config, multiAttestTransition, transitionSignature,
      bytes32Array, uint256NestedArray, uint256Array] using hdec
  exact attesterDecodeCalldata_twoDynamicArrays_shape
    (name0 := "schemas") (name1 := "schemaInputs")
    (elem0 := bytes32) (elem1 := uint256) (cd := I.calldata)
    (by native_decide) hdec'

theorem attesterDecode_multiAttest_some_shape_lengths (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata =
      some callargs) :
    ∃ schemas schemaInputs : List Value,
      callargs.get? "schemas" = some (.array schemas) ∧
      callargs.get? "schemaInputs" = some (.array schemaInputs) ∧
      schemas.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ∧
      schemaInputs.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat := by
  have hdec' :
      decodeCalldata ["schemas", "schemaInputs"]
        [.dynamicArray bytes32, .dynamicArray (.dynamicArray uint256)] I.calldata =
      some callargs := by
    simpa [decodeCalldataWithMode, config, multiAttestTransition, transitionSignature,
      bytes32Array, uint256NestedArray, uint256Array] using hdec
  exact attesterDecodeCalldata_twoDynamicArrays_lengths
    (name0 := "schemas") (name1 := "schemaInputs")
    (elem1 := uint256) (cd := I.calldata)
    (by native_decide) hdec'

theorem attesterDecode_multiAttest_good_lengths_of_not_bad (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store}
    (hnotBad :
      ¬ ∃ callargs schemas schemaInputs,
          decodeCalldataWithMode (config v).abiDecodeMode
              ((multiAttestTransition v).params.map Param.name)
              (transitionSignature (multiAttestTransition v)).paramTypes I.calldata =
            some callargs ∧
          callargs.get? "schemas" = some (.array schemas) ∧
          callargs.get? "schemaInputs" = some (.array schemaInputs) ∧
          schemas.length =
            (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ∧
          schemaInputs.length =
            (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ∧
          (schemas.length = 0 ∨ schemas.length ≠ schemaInputs.length))
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata =
      some callargs) :
    ∃ schemas schemaInputs : List Value,
      callargs.get? "schemas" = some (.array schemas) ∧
      callargs.get? "schemaInputs" = some (.array schemaInputs) ∧
      schemas.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ∧
      schemaInputs.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ∧
      schemas.length ≠ 0 ∧ schemas.length = schemaInputs.length := by
  obtain ⟨schemas, schemaInputs, hSchemas, hSchemaInputs, hSchemasLen, hSchemaInputsLen⟩ :=
    attesterDecode_multiAttest_some_shape_lengths v hdec
  have hnonzero : schemas.length ≠ 0 := by
    intro hzero
    exact hnotBad ⟨callargs, schemas, schemaInputs, hdec, hSchemas, hSchemaInputs,
      hSchemasLen, hSchemaInputsLen, Or.inl hzero⟩
  have heq : schemas.length = schemaInputs.length := by
    by_contra hne
    exact hnotBad ⟨callargs, schemas, schemaInputs, hdec, hSchemas, hSchemaInputs,
      hSchemasLen, hSchemaInputsLen, Or.inr hne⟩
  exact ⟨schemas, schemaInputs, hSchemas, hSchemaInputs, hSchemasLen, hSchemaInputsLen,
    hnonzero, heq⟩

theorem attesterMultiAttestBodySchemaGuardReverts (v : AttesterImmutables)
    (evm : EVM.State) (locals : Store) {schemas schemaInputs : List Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hSchemas : locals.get? "schemas" = some (.array schemas))
    (hSchemaInputs : locals.get? "schemaInputs" = some (.array schemaInputs))
    (hbad : schemas.length = 0 ∨ schemas.length ≠ schemaInputs.length) :
    ExecTransitionBody (config v) (contract v) evm locals
      (multiAttestTransition v).body .reverted := by
  have hSchemasElem : locals["schemas"]? = some (.array schemas) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hSchemas
  have hSchemaInputsElem (n : Nat) :
      (locals.insert "schemaLength" (.int (Int.ofNat n)))["schemaInputs"]? =
        some (.array schemaInputs) := by
    rw [Std.HashMap.getElem?_insert]
    simp
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hSchemaInputs
  refine ExecFuncBody.execBlockRevert ?_
  simp [multiAttestTransition, nonpayable]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int (Int.ofNat schemas.length)) ?_) ?_
  · simp [evalExpr?, lenLocal, localRef, hSchemasElem, readLocalPath?,
      EvalResult.bind, bind, pure]
  · refine ExecBlock.consRevert (ExecStmt.requireFalse ?_)
    exact attesterEvalMultiLengthGuardFalse (v := v) (evm := evm) (locals := locals)
      (secondName := "schemaInputs") (schemas := schemas) (second := schemaInputs)
      (hSchemaInputsElem schemas.length) hbad

theorem attesterMultiAttestBodyFirstInputLengthZeroReverts (v : AttesterImmutables)
    (evm : EVM.State) (locals : Store) {schemas rest : List Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hSchemas : locals.get? "schemas" = some (.array schemas))
    (hSchemaInputs : locals.get? "schemaInputs" = some (.array (.array [] :: rest)))
    (hSchemasNe : schemas.length ≠ 0)
    (hSchemasLen : schemas.length = (.array [] :: rest).length) :
    ExecTransitionBody (config v) (contract v) evm locals
      (multiAttestTransition v).body .reverted := by
  have hSchemasElem : locals["schemas"]? = some (.array schemas) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hSchemas
  refine ExecFuncBody.execBlockRevert ?_
  simp [multiAttestTransition, nonpayable]
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
            (.binary .eq (.var "schemaLength") (lenLocal "schemaInputs"))) =
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
            (.binary .eq (.var "schemaLength") (lenLocal "schemaInputs")) =
          .ok (.bool true) := by
        have hSchemaInputsElem :
            (locals.insert "schemaLength" (.int (Int.ofNat schemas.length)))["schemaInputs"]? =
              some (.array (.array [] :: rest)) := by
          rw [Std.HashMap.getElem?_insert]
          simp
          rw [← Std.HashMap.get?_eq_getElem?]
          exact hSchemaInputs
        have hSchemaInputsGet :
            (locals.insert "schemaLength" (.int (Int.ofNat schemas.length))).get?
                "schemaInputs" =
              some (.array (.array [] :: rest)) := by
          simpa [Std.HashMap.get?_eq_getElem?] using hSchemaInputsElem
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
              (lenLocal "schemaInputs") =
            .ok (.int (Int.ofNat (.array [] :: rest).length)) := by
          simp only [evalExpr?, lenLocal, localRef, readLocalPath?, EvalResult.bind,
            bind, pure]
          rw [hSchemaInputsGet]
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
          (.newArray multiAttestationRequestSt (.var "schemaLength")) =
        .ok multiRequests := by
      simp [multiRequests, defaultRequest, evalExpr?, multiAttestationRequestSt,
        attestationRequestDataSt, addrSt, uint64St, boolSt, bytes32St, uint256St,
        bytes32Width, defaultValue?, defaultValues?, EvalResult.bind,
        EvalResult.ofOption, bind, pure]
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
                (.var "schemaInputs") = .ok (.array (.array [] :: rest)) := by
            have hSchemaInputsGet :
                ((((locals.insert "schemaLength" (.int (Int.ofNat schemas.length))).insert
                      "multiRequests" multiRequests).insert "i" (.int 0)).get?
                    "schemaInputs") =
                  some (.array (.array [] :: rest)) := by
              rw [Std.HashMap.get?_eq_getElem?]
              rw [Std.HashMap.getElem?_insert]
              simp
              rw [Std.HashMap.getElem?_insert]
              simp
              rw [Std.HashMap.getElem?_insert]
              simp
              rw [← Std.HashMap.get?_eq_getElem?]
              exact hSchemaInputs
            simp only [evalExpr?, EvalResult.ofOption]
            rw [hSchemaInputsGet]
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

set_option maxHeartbeats 1000000 in
theorem attesterMultiAttestBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (v : AttesterImmutables) {code : ByteArray}
    (hpatch : patchRuntime attesterBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hpatched : code = patchedRuntime v := code_eq_patchedRuntime_of_patch hpatch
  have hIcode : I.code = patchedRuntime v := hcode.trans hpatched
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I attesterMultiAttestSelBytes attesterMultiAttestSelBytes_size
      hmultiAttest
  have hd := attesterDispatch_multiAttest v hmultiAttest
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · by_cases hoff0 : solcMaxU64 < (calldataWord I.calldata 4).toNat
      · have hdec := attesterDecode_multiAttest_none_firstOffsetHuge v hsz68 hoff0
        have hreach2128 :=
          attesterX_multiAttestDecodeHeadOk
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g)
            v hIcode hwv hsz4 hsize hsz68 hsmall hmultiRevoke hmultiAttest
        exact (attesterX_dynamic2FirstOffsetHugeReverts
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g)
            v hoff0 hreach2128)
          |>.reEquivDecodingFailed hIcode hd hdec
      · have hreach2128 :=
          attesterX_multiAttestDecodeHeadOk
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g)
            v hIcode hwv hsz4 hsize hsz68 hsmall hmultiRevoke hmultiAttest
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
            · have hdec := attesterDecode_multiAttest_none_firstLengthHuge
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
                · have hdec := attesterDecode_multiAttest_none_secondOffsetHuge
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
                    · have hdec := attesterDecode_multiAttest_none_secondLengthHuge
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
                            v (attesterMultiAttestDecodedJumpdest v) _hreach2203
                        have _hreachBody :=
                          attesterX_multiAttestDecodedToBody
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                            (A := A) (I := I) (g := Sat256.ofUInt256 g)
                            v _hreachDecoded
                        by_cases hbadDec :
                            ∃ callargs schemas schemaInputs,
                              decodeCalldataWithMode (config v).abiDecodeMode
                                  ((multiAttestTransition v).params.map Param.name)
                                  (transitionSignature (multiAttestTransition v)).paramTypes
                                  I.calldata = some callargs ∧
                              callargs.get? "schemas" = some (.array schemas) ∧
                              callargs.get? "schemaInputs" = some (.array schemaInputs) ∧
                              schemas.length =
                                (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 4).toNat)).toNat ∧
                              schemaInputs.length =
                                (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 36).toNat)).toNat ∧
                              (schemas.length = 0 ∨ schemas.length ≠ schemaInputs.length)
                        · rcases hbadDec with
                            ⟨callargs, schemas, schemaInputs, hdecFull, hSchemas, hSchemaInputs,
                              hSchemasLen, hSchemaInputsLen, hbad⟩
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
                              attesterX_multiAttestLengthZeroReverts
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v hzeroEvm _hreachBody
                            have hbody :=
                              attesterMultiAttestBodySchemaGuardReverts v
                                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                callargs hwvSolm hSchemas hSchemaInputs (Or.inl hzeroSchemas)
                            exact hrdrev.reEquivExecutionRevert hIcode hd hdecFull hbody
                          · by_cases heqSchemas : schemas.length = schemaInputs.length
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
                                attesterX_multiAttestLengthMismatchReverts
                                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                  (σ₀ := σ₀) (A := A) (I := I)
                                  (g := Sat256.ofUInt256 g) v hnonzeroEvm hneqEvm
                                  _hreachBody
                              have hbody :=
                                attesterMultiAttestBodySchemaGuardReverts v
                                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                  callargs hwvSolm hSchemas hSchemaInputs (Or.inr heqSchemas)
                              exact hrdrev.reEquivExecutionRevert hIcode hd hdecFull hbody
                        · have _hguardProgress :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiAttestTransition v).params.map Param.name)
                                    (transitionSignature (multiAttestTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ k C, RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  (⟨874⟩ : UInt256)
                                  [attesterFirstArrayLengthWord I, ⟨96⟩,
                                    attesterSecondArrayLengthWord I,
                                    (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                    attesterFirstArrayLengthWord I,
                                    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                    ⟨118⟩, solcSelectorWord I]
                                  solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
                                  (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaInputs, _hSchemas, _hSchemaInputs,
                              hSchemasLen, hSchemaInputsLen, hnonzero, heqLen⟩ :=
                              attesterDecode_multiAttest_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            exact attesterX_multiAttestLengthGuardOk_of_lengths
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) v hoff0 hoff1 hSchemasLen
                              hSchemaInputsLen hnonzero heqLen _hreachBody
                          have _hallocProgress :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiAttestTransition v).params.map Param.name)
                                    (transitionSignature (multiAttestTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ k C, RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  (⟨899⟩ : UInt256)
                                  [attesterFirstArrayLengthWord I, ⟨0⟩,
                                    attesterFirstArrayLengthWord I, ⟨96⟩,
                                    attesterSecondArrayLengthWord I,
                                    (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                    attesterFirstArrayLengthWord I,
                                    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                    ⟨118⟩, solcSelectorWord I]
                                  solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
                                  (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            exact attesterX_multiAttestAllocLengthMaxOk
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) v hoff0 hlenHuge
                              (_hguardProgress callargs hdecFull)
                          have _hinitProgress :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiAttestTransition v).params.map Param.name)
                                    (transitionSignature (multiAttestTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ k C, RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  (⟨929⟩ : UInt256)
                                  [((⟨32⟩ : UInt256) + ⟨128⟩),
                                    attesterFirstArrayLengthWord I, ⟨128⟩, ⟨0⟩,
                                    attesterFirstArrayLengthWord I, ⟨96⟩,
                                    attesterSecondArrayLengthWord I,
                                    (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                    attesterFirstArrayLengthWord I,
                                    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                    ⟨118⟩, solcSelectorWord I]
                                  (attesterMultiOuterArrayAllocMem I) (UInt256.ofNat 5)
                                  ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaInputs, _hSchemas, _hSchemaInputs,
                              hSchemasLen, _hSchemaInputsLen, hnonzero, _heqLen⟩ :=
                              attesterDecode_multiAttest_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            have hrawFirstNe :
                                (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0 := by
                              intro hrawZero
                              exact hnonzero (by omega)
                            have hnonzeroEvm :=
                              attesterFirstArrayLengthWord_isZero_of_nat_ne_zero
                                (I := I) hoff0 hrawFirstNe
                            exact attesterX_multiAttestOuterArrayInitEntry
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) v hnonzeroEvm
                              (_hallocProgress callargs hdecFull)
                          have _houterInitProgress :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiAttestTransition v).params.map Param.name)
                                    (transitionSignature (multiAttestTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨973⟩ : UInt256)
                                    (attesterMultiAttestOuterArrayInitExitStack I
                                      ⟨128⟩ (attesterFirstArrayLengthWord I) a')
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaInputs, _hSchemas, _hSchemaInputs,
                              _hSchemasLen, _hSchemaInputsLen, hnonzero, _heqLen⟩ :=
                              attesterDecode_multiAttest_good_lengths_of_not_bad v
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
                            exact attesterX_multiAttestOuterArrayInitLoop
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                              (σ₀ := σ₀) (A := A) (I := I)
                              (g := Sat256.ofUInt256 g) v
                              (slot := ((⟨32⟩ : UInt256) + ⟨128⟩))
                              (base := ⟨128⟩)
                              (len := attesterFirstArrayLengthWord I)
                              (mem := attesterMultiOuterArrayAllocMem I)
                              (aw := UInt256.ofNat 5) (k := k0) (C := C0) hlenNe rd0
                          have _houterLoopFirstGuard :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiAttestTransition v).params.map Param.name)
                                    (transitionSignature (multiAttestTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨982⟩ : UInt256)
                                    (attesterMultiAttestOuterArrayInitExitStack I
                                      ⟨128⟩ (attesterFirstArrayLengthWord I) a')
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaInputs, _hSchemas, _hSchemaInputs,
                              _hSchemasLen, _hSchemaInputsLen, hnonzero, _heqLen⟩ :=
                              attesterDecode_multiAttest_good_lengths_of_not_bad v
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
                              attesterX_multiAttestOuterSourceLoopFirstGuard
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v
                                (base := ⟨128⟩)
                                (len := attesterFirstArrayLengthWord I)
                                (mem := attesterMultiOuterArrayInitFinalMem a')
                                (aw := attesterMultiOuterArrayInitFinalAw a')
                                (k := k0) (C := C0) hlenNe
                                (by
                                  simpa [attesterMultiAttestOuterArrayInitExitStack]
                                    using rd0)
                            exact ⟨a', k1, C1, hrem, by
                              simpa [attesterMultiAttestOuterArrayInitExitStack]
                                using rd1⟩
                          have _houterSecondArrayAccessOk :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiAttestTransition v).params.map Param.name)
                                    (transitionSignature (multiAttestTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨1001⟩ : UInt256)
                                    [⟨0⟩, attesterSecondArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
                                      attesterFirstArrayLengthWord I, ⟨96⟩,
                                      attesterSecondArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      attesterFirstArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                      ⟨118⟩, solcSelectorWord I]
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaInputs, _hSchemas, _hSchemaInputs,
                              _hSchemasLen, hSchemaInputsLen, hnonzero, heqLen⟩ :=
                              attesterDecode_multiAttest_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            have hrawSecondNe :
                                (calldataWord I.calldata
                                  (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0 := by
                              intro hrawZero
                              exact hnonzero (by
                                calc
                                  schemas.length = schemaInputs.length := heqLen
                                  _ = (calldataWord I.calldata
                                      (4 + (calldataWord I.calldata 36).toNat)).toNat :=
                                    hSchemaInputsLen
                                  _ = 0 := hrawZero)
                            have hsecondLenNe :
                                (attesterSecondArrayLengthWord I).toNat ≠ 0 := by
                              rw [attesterSecondArrayLengthWord_toNat (I := I) hoff1]
                              exact hrawSecondNe
                            obtain ⟨a', k0, C0, hrem, rd0⟩ :=
                              _houterLoopFirstGuard callargs hdecFull
                            obtain ⟨k1, C1, rd1⟩ :=
                              attesterX_multiAttestOuterSecondArrayAccessOk
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v
                                (base := ⟨128⟩)
                                (len := attesterFirstArrayLengthWord I)
                                (mem := attesterMultiOuterArrayInitFinalMem a')
                                (aw := attesterMultiOuterArrayInitFinalAw a')
                                (k := k0) (C := C0) hsecondLenNe
                                (by
                                  simpa [attesterMultiAttestOuterArrayInitExitStack]
                                    using rd0)
                            exact ⟨a', k1, C1, hrem, rd1⟩
                          have _hinnerDecoderEntry :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiAttestTransition v).params.map Param.name)
                                    (transitionSignature (multiAttestTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨2353⟩ : UInt256)
                                    [(UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      ⟨1019⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩,
                                      ⟨128⟩, attesterFirstArrayLengthWord I, ⟨96⟩,
                                      attesterSecondArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
                                      attesterFirstArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                      ⟨118⟩, solcSelectorWord I]
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨a', k0, C0, hrem, rd0⟩ :=
                              _houterSecondArrayAccessOk callargs hdecFull
                            obtain ⟨k1, C1, rd1⟩ :=
                              attesterX_multiAttestFirstInnerArrayDecoderEntryFromOuterSecond
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v
                                (mem := attesterMultiOuterArrayInitFinalMem a')
                                (aw := attesterMultiOuterArrayInitFinalAw a')
                                (k := k0) (C := C0) rd0
                            exact ⟨a', k1, C1, hrem, rd1⟩
                          have _hinnerDecoderReturn :
                              ∀ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiAttestTransition v).params.map Param.name)
                                    (transitionSignature (multiAttestTransition v)).paramTypes
                                    I.calldata = some callargs →
                                ∃ a' k C,
                                  a'.remaining = (⟨1⟩ : UInt256) ∧
                                  RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    (⟨1019⟩ : UInt256)
                                    [attesterFirstInnerArrayLengthWord I,
                                      attesterFirstInnerArrayStartWord I + ⟨32⟩,
                                      ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩,
                                      ⟨128⟩, attesterFirstArrayLengthWord I, ⟨96⟩,
                                      attesterSecondArrayLengthWord I,
                                      attesterSecondArrayPayloadStartWord I,
                                      attesterFirstArrayLengthWord I,
                                      (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
                                      ⟨118⟩, solcSelectorWord I]
                                    (attesterMultiOuterArrayInitFinalMem a')
                                    (attesterMultiOuterArrayInitFinalAw a')
                                    ByteArray.empty (cA, σ_evm) k C := by
                            intro callargs hdecFull
                            obtain ⟨schemas, schemaInputs, _hSchemas, hSchemaInputs,
                              _hSchemasLen, _hSchemaInputsLen, hnonzero, heqLen⟩ :=
                              attesterDecode_multiAttest_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            have hSchemaInputsNe : schemaInputs.length ≠ 0 := by
                              intro hzero
                              exact hnonzero (by rw [heqLen, hzero])
                            obtain ⟨n, relativeOffset, inner, innerEnd, valuesRest, restEnd,
                                _hlen, _hlenMax, hreadFirst, hinner, _hrest,
                                _hshape, _hend⟩ :=
                              attesterDecode_multiAttest_first_inner_decode v
                                hdecFull hSchemaInputs hSchemaInputsNe
                            obtain ⟨hoffsetOk, hlenOk, hpayloadOk⟩ :=
                              attesterFirstInnerArrayGuardFacts_of_decode
                                (I := I) (elem := .int uint256Int)
                                hoff1 hreadFirst
                                (by simpa [uint256] using hinner)
                                hsizeSigned
                            obtain ⟨a', k0, C0, hrem, rd0⟩ :=
                              _hinnerDecoderEntry callargs hdecFull
                            obtain ⟨k1, C1, rd1⟩ :=
                              attesterX_multiAttestFirstInnerArrayOffsetOk
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v hoffsetOk
                                (mem := attesterMultiOuterArrayInitFinalMem a')
                                (aw := attesterMultiOuterArrayInitFinalAw a')
                                (k := k0) (C := C0)
                                (by simpa [attesterSecondArrayPayloadStartWord] using rd0)
                            obtain ⟨k2, C2, rd2⟩ :=
                              attesterX_multiAttestFirstInnerArrayLengthMaxOk
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v hlenOk
                                (mem := attesterMultiOuterArrayInitFinalMem a')
                                (aw := attesterMultiOuterArrayInitFinalAw a')
                                (k := k1) (C := C1) rd1
                            obtain ⟨k3, C3, rd3⟩ :=
                              attesterX_multiAttestFirstInnerArrayPayloadOkToReturn
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v hpayloadOk
                                (mem := attesterMultiOuterArrayInitFinalMem a')
                                (aw := attesterMultiOuterArrayInitFinalAw a')
                                (k := k2) (C := C2) rd2
                            exact ⟨a', k3, C3, hrem, rd3⟩
                          by_cases hzeroBranch :
                              ∃ callargs,
                                decodeCalldataWithMode (config v).abiDecodeMode
                                    ((multiAttestTransition v).params.map Param.name)
                                    (transitionSignature (multiAttestTransition v)).paramTypes
                                    I.calldata = some callargs ∧
                                attesterFirstInnerArrayLengthWord I = ⟨0⟩
                          · rcases hzeroBranch with ⟨callargs, hdecFull, hinnerLenZeroWord⟩
                            obtain ⟨schemas, schemaInputs, hSchemas, hSchemaInputs,
                              _hSchemasLen, _hSchemaInputsLen, hnonzero, heqLen⟩ :=
                              attesterDecode_multiAttest_good_lengths_of_not_bad v
                                hbadDec hdecFull
                            have hSchemaInputsNe : schemaInputs.length ≠ 0 := by
                              intro hzero
                              exact hnonzero (by rw [heqLen, hzero])
                            obtain ⟨n, relativeOffset, inner, innerEnd, valuesRest, restEnd,
                                _hlen, _hlenMax, hreadFirst, hinner, _hrest,
                                hshape, _hend⟩ :=
                              attesterDecode_multiAttest_first_inner_decode v
                                hdecFull hSchemaInputs hSchemaInputsNe
                            have hinnerLenWord :
                                (attesterFirstInnerArrayLengthWord I).toNat = inner.length :=
                              attesterFirstInnerArrayLengthWord_toNat_of_decode
                                (I := I) (elem := .int uint256Int)
                                hoff1 hreadFirst
                                (by simpa [uint256] using hinner)
                                hsizeSigned
                            have hinnerLenZero : inner.length = 0 := by
                              rw [← hinnerLenWord]
                              simp [hinnerLenZeroWord]
                            have hinnerNil : inner = [] := by
                              simpa using hinnerLenZero
                            have hshapeEmpty : schemaInputs = .array [] :: valuesRest := by
                              simpa [hinnerNil] using hshape
                            have hSchemaInputsEmpty :
                                callargs.get? "schemaInputs" =
                                  some (.array (.array [] :: valuesRest)) := by
                              simpa [hshapeEmpty] using hSchemaInputs
                            have hSchemasLenEmpty :
                                schemas.length = (.array [] :: valuesRest).length := by
                              calc
                                schemas.length = schemaInputs.length := heqLen
                                _ = (.array [] :: valuesRest).length := by rw [hshapeEmpty]
                            obtain ⟨a', k3, C3, _hrem, rd3⟩ :=
                              _hinnerDecoderReturn callargs hdecFull
                            have hrdrev :=
                              attesterX_multiAttestFirstInnerArrayLengthZeroReverts
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
                              attesterMultiAttestBodyFirstInputLengthZeroReverts v
                                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                callargs hwvSolm hSchemas hSchemaInputsEmpty hnonzero
                                hSchemasLenEmpty
                            exact hrdrev.reEquivExecutionRevert hIcode hd hdecFull hbody
                          · have _hfirstInnerNonemptyProgress :
                                ∀ callargs,
                                  decodeCalldataWithMode (config v).abiDecodeMode
                                      ((multiAttestTransition v).params.map Param.name)
                                      (transitionSignature (multiAttestTransition v)).paramTypes
                                      I.calldata = some callargs →
                                  ∃ a' k C,
                                    a'.remaining = (⟨1⟩ : UInt256) ∧
                                    RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                      (⟨1083⟩ : UInt256)
                                      [attesterFirstInnerArrayLengthWord I, ⟨0⟩,
                                        attesterFirstInnerArrayLengthWord I,
                                        attesterFirstInnerArrayLengthWord I,
                                        attesterFirstInnerArrayStartWord I + ⟨32⟩,
                                        ⟨0⟩, ⟨128⟩,
                                        attesterFirstArrayLengthWord I, ⟨96⟩,
                                        attesterSecondArrayLengthWord I,
                                        attesterSecondArrayPayloadStartWord I,
                                        attesterFirstArrayLengthWord I,
                                        (UInt256.add ⟨4⟩
                                          (calldataWord I.calldata 4)) + ⟨32⟩,
                                        ⟨118⟩, solcSelectorWord I]
                                      (attesterMultiOuterArrayInitFinalMem a')
                                      (attesterMultiOuterArrayInitFinalAw a')
                                      ByteArray.empty (cA, σ_evm) k C := by
                              intro callargs hdecFull
                              obtain ⟨schemas, schemaInputs, _hSchemas, hSchemaInputs,
                                _hSchemasLen, _hSchemaInputsLen, hnonzero, heqLen⟩ :=
                                attesterDecode_multiAttest_good_lengths_of_not_bad v
                                  hbadDec hdecFull
                              have hSchemaInputsNe : schemaInputs.length ≠ 0 := by
                                intro hzero
                                exact hnonzero (by rw [heqLen, hzero])
                              obtain ⟨n, relativeOffset, inner, innerEnd, valuesRest, restEnd,
                                  _hlen, _hlenMax, hreadFirst, hinner, _hrest,
                                  _hshape, _hend⟩ :=
                                attesterDecode_multiAttest_first_inner_decode v
                                  hdecFull hSchemaInputs hSchemaInputsNe
                              obtain ⟨_hoffsetOk, hlenOk, _hpayloadOk⟩ :=
                                attesterFirstInnerArrayGuardFacts_of_decode
                                  (I := I) (elem := .int uint256Int)
                                  hoff1 hreadFirst
                                  (by simpa [uint256] using hinner)
                                  hsizeSigned
                              have hinnerLenNeWord :
                                  attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩ := by
                                intro hzero
                                exact hzeroBranch ⟨callargs, hdecFull, hzero⟩
                              obtain ⟨a', k0, C0, hrem, rd0⟩ :=
                                _hinnerDecoderReturn callargs hdecFull
                              obtain ⟨k1, C1, rd1⟩ :=
                                attesterX_multiAttestFirstInnerArrayNonemptyOk
                                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                  (σ₀ := σ₀) (A := A) (I := I)
                                  (g := Sat256.ofUInt256 g) v hinnerLenNeWord
                                  (mem := attesterMultiOuterArrayInitFinalMem a')
                                  (aw := attesterMultiOuterArrayInitFinalAw a')
                                  (k := k0) (C := C0) rd0
                              obtain ⟨k2, C2, rd2⟩ :=
                                attesterX_multiAttestFirstInnerArrayLengthAllocMaxOk
                                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                  (σ₀ := σ₀) (A := A) (I := I)
                                  (g := Sat256.ofUInt256 g) v hlenOk
                                  (mem := attesterMultiOuterArrayInitFinalMem a')
                                  (aw := attesterMultiOuterArrayInitFinalAw a')
                                  (k := k1) (C := C1) rd1
                              exact ⟨a', k2, C2, hrem, rd2⟩
                            have _hfirstInnerAllocProgress :
                                ∀ callargs,
                                  decodeCalldataWithMode (config v).abiDecodeMode
                                      ((multiAttestTransition v).params.map Param.name)
                                      (transitionSignature (multiAttestTransition v)).paramTypes
                                      I.calldata = some callargs →
                                  ∃ a' k C,
                                    a'.remaining = (⟨1⟩ : UInt256) ∧
                                    RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                      (⟨1113⟩ : UInt256)
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
                                          attesterFirstArrayLengthWord I, ⟨96⟩,
                                          attesterSecondArrayLengthWord I,
                                          attesterSecondArrayPayloadStartWord I,
                                          attesterFirstArrayLengthWord I,
                                          (UInt256.add ⟨4⟩
                                            (calldataWord I.calldata 4)) + ⟨32⟩,
                                          ⟨118⟩, solcSelectorWord I])
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
                              exact attesterX_multiAttestFirstInnerArrayAllocProgress
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v hinnerLenNeWord
                                (_hfirstInnerNonemptyProgress callargs hdecFull)
                            have _hfirstInnerInitProgress :
                                ∀ callargs,
                                  decodeCalldataWithMode (config v).abiDecodeMode
                                      ((multiAttestTransition v).params.map Param.name)
                                      (transitionSignature (multiAttestTransition v)).paramTypes
                                      I.calldata = some callargs →
                                  ∃ a' b' k C,
                                    a'.remaining = (⟨1⟩ : UInt256) ∧
                                    b'.remaining = (⟨1⟩ : UInt256) ∧
                                    RD (patchedRuntime v) I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                      (⟨1181⟩ : UInt256)
                                      (attesterMultiAttestInnerArrayInitExitStack I
                                        (attesterInnerArrayAllocFreeWord
                                          (attesterMultiOuterArrayInitFinalMem a')
                                          (attesterMultiOuterArrayInitFinalAw a'))
                                        (attesterFirstInnerArrayLengthWord I)
                                        (attesterFirstInnerArrayStartWord I + ⟨32⟩)
                                        b')
                                      (attesterMultiAttestInnerArrayInitFinalMem b')
                                      (attesterMultiAttestInnerArrayInitFinalAw b')
                                      ByteArray.empty (cA, σ_evm) k C := by
                              intro callargs hdecFull
                              have hinnerLenNeWord :
                                  attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩ := by
                                intro hzero
                                exact hzeroBranch ⟨callargs, hdecFull, hzero⟩
                              exact attesterX_multiAttestFirstInnerArrayInitProgress
                                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
                                (σ₀ := σ₀) (A := A) (I := I)
                                (g := Sat256.ofUInt256 g) v hinnerLenNeWord
                                (_hfirstInnerAllocProgress callargs hdecFull)
                            sorry
                      · have hpayload1Short :
                          I.calldata.size <
                            4 + (calldataWord I.calldata 36).toNat + 32 +
                              32 * (calldataWord I.calldata
                                (4 + (calldataWord I.calldata 36).toNat)).toNat := by
                          omega
                        have hdec := attesterDecode_multiAttest_none_secondPayloadShort
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
                    have hdec := attesterDecode_multiAttest_none_secondLengthShort
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
                have hdec := attesterDecode_multiAttest_none_firstPayloadShort
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
            have hdec := attesterDecode_multiAttest_none_firstLengthShort
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
          have hdec := attesterDecode_multiAttest_none_totalHuge v hbigSigned
          have hslt :=
            attesterDynamicArrayLengthGuardSltZero_of_sizeHuge
              (I := I) hoff0 hbigSigned hsize
          exact (attesterX_dynamicArrayLengthGuardReverts
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g)
              v hslt hreach2038)
            |>.reEquivDecodingFailed hIcode hd hdec
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := attesterDecode_multiAttest_none_huge v hbig
      exact (attesterX_multiAttestDecodeHuge (g := Sat256.ofUInt256 g) v hIcode hwv hsz4
          hsize hbig hmultiRevoke hmultiAttest)
        |>.reEquivDecodingFailed hIcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := attesterDecode_multiAttest_none_short v hsz4 hshort
    exact (attesterX_multiAttestDecodeShort (g := Sat256.ofUInt256 g) v hIcode hwv hsz4
        hsize hshort hmultiRevoke hmultiAttest)
      |>.reEquivDecodingFailed hIcode hd hdec

end Benchmarks.EAS.Attester
