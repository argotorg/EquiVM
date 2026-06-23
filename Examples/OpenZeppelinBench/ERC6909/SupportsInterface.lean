import Examples.OpenZeppelinBench.ERC6909.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.ERC6909

/-! ## `supportsInterface(bytes4)` -/

def supportsInterfaceArgBytes (I : ExecutionEnv) : List UInt8 :=
  ((I.calldata.toList.drop 4).take 32).take 4

def supportsInterfaceArgWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes 4 32)

def supportsInterfaceStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "interfaceId" (.fixedBytes bytes4Width (supportsInterfaceArgBytes I))

def supportsInterfaceResult (I : ExecutionEnv) : Bool :=
  (supportsInterfaceArgBytes I == [0x0f, 0x63, 0x2f, 0xb3]) ||
    (supportsInterfaceArgBytes I == [0x01, 0xff, 0xc9, 0xa7])

def supportsInterfaceResultWord (I : ExecutionEnv) : UInt256 :=
  if supportsInterfaceResult I then ⟨1⟩ else ⟨0⟩

theorem erc6909SupportsInterfaceSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc6909Dispatch_supportsInterface {cd : ByteArray}
    (hsel : ((⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some supportsInterfaceTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition, isOperatorTransition,
      setOperatorTransition])
    (post := [transferTransition, transferFromTransition]) rfl ?_
    (by rw [selectorOf, erc6909SupportsInterfaceSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, erc6909AllowanceSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909ApproveSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909BalanceOfSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909IsOperatorSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909SetOperatorSelectorBytes, hcd]; decide

-- PROMOTE -> Common.lean / Reasoning.ABI: single fixed-bytes4 calldata decoder.
theorem erc6909Decode_supportsInterface_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hpad : zeroPadding? ((I.calldata.toList.drop 4).take 32) 4 28 = some ()) :
    decodeCalldata (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata =
        some (supportsInterfaceStore I) := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = some (supportsInterfaceStore I)
  unfold decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ I.calldata.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([bytes4].any isDynamicABIType = true ∧
      2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes4, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hnotHuge : ¬ ([bytes4].isEmpty = false ∧
      2 ^ 255 ≤ (I.calldata.toList.drop 4).length) := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnotHuge]
  have hread : readBytes? (I.calldata.toList.drop 4) 0 32 =
      some ((I.calldata.toList.drop 4).take 32) := by
    unfold readBytes?
    have hlen : (((I.calldata.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_pos hlen, List.drop_zero]
  have hblen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hnotArgShort : ¬ I.calldata.toList.length - 4 < 32 := by
    rw [htlen]
    omega
  simp [decodeCalldata.decodeArgs, decodeCalldata.insertValues, bytes4, ABI.decodeABIValues?,
    ABI.decodeABIValue?, isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread, hpad,
    supportsInterfaceStore, supportsInterfaceArgBytes, bytes4Width, hblen, hnotArgShort]

theorem erc6909Decode_supportsInterface_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = none
  unfold decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ I.calldata.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([bytes4].any isDynamicABIType = true ∧
      2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes4, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hnotHuge : ¬ ([bytes4].isEmpty = false ∧
      2 ^ 255 ≤ (I.calldata.toList.drop 4).length) := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnotHuge]
  have hread : readBytes? (I.calldata.toList.drop 4) 0 32 = none := by
    unfold readBytes?
    have hlen : ¬ (((I.calldata.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_neg hlen]
  simp [decodeCalldata.decodeArgs, bytes4, ABI.decodeABIValues?, ABI.decodeABIValue?,
    isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread]

theorem erc6909Decode_supportsInterface_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (supportsInterfaceTransition.params.map Param.name)
      (transitionSignature supportsInterfaceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["interfaceId"] [bytes4] I.calldata = none
  unfold decodeCalldata
  by_cases hlt4 : I.calldata.toList.length < 4
  · rw [if_pos hlt4]
  · rw [if_neg hlt4]
    have hnotDyn : ¬ ([bytes4].any isDynamicABIType = true ∧
        2 ^ 255 ≤ I.calldata.toList.length) := by
      simp [bytes4, isDynamicABIType]
    rw [if_neg hnotDyn]
    have hHuge :
        [bytes4].isEmpty = false ∧ 2 ^ 255 ≤ (I.calldata.toList.drop 4).length := by
      have htlen : I.calldata.toList.length = I.calldata.size := by
        rw [byteArray_toList_eq, Array.length_toList]
        rfl
      rw [List.length_drop, htlen]
      simp
      omega
    rw [if_pos hHuge]

theorem erc6909Decide_eq_list_beq_uint8 (xs ys : List UInt8) :
    decide (xs = ys) = (xs == ys) := by
  by_cases h : xs = ys
  · subst ys
    simp
  · have hb : (xs == ys) = false := by
      exact beq_eq_false_iff_ne.mpr h
    simp [h, hb]

theorem erc6909SupportsInterfaceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (supportsInterfaceStore I) supportsInterfaceTransition.body
      (.returned { contract := contract, locals := supportsInterfaceStore I } evm
        (some (.bool (supportsInterfaceResult I)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      simp [supportsInterfaceStore, supportsInterfaceResult, ierc6909Id, ierc165Id,
        evalExpr?, evalBinaryOp?, EvalResult.bind, EvalResult.ofOption, bind, BEq.beq,
        erc6909Decide_eq_list_beq_uint8])

end OpenZeppelinBench.ERC6909
