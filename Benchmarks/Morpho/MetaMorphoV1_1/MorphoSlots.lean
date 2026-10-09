import Benchmarks.Morpho.MetaMorphoV1_1.PackedSource

/-! Morpho's storage-slot calculations evaluated from the source helpers. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

-- LIBRARY CANDIDATE: pack two 32-byte values into the usual mapping-hash preimage.
theorem evalExpr_packedTwoWords {cfg : Config} {frame : Frame} {evm : EVM.State}
    {first second : Expr} {firstTy secondTy : ABIType} {firstValue secondValue : Value}
    {a b : UInt256}
    (ha : evalExpr? cfg frame evm first = .ok firstValue)
    (hb : evalExpr? cfg frame evm second = .ok secondValue)
    (hea : encodePackedValue? firstTy firstValue = some (EVM.Word.toBytesBE a))
    (heb : encodePackedValue? secondTy secondValue = some (EVM.Word.toBytesBE b)) :
    evalExpr? cfg frame evm (.abiEncodePacked [(firstTy, first), (secondTy, second)]) =
      .ok (.bytes (a.toByteArray ++ b.toByteArray)) := by
  have h := evalExpr_packed (evalPackedArgs_cons ha hea
    (evalPackedArgs_cons (args := []) (tail := []) hb heb
      (by simp only [evalPackedArgs?, pure])))
  simpa only [List.append_nil, List.toByteArray_append,
    word_toBytesBE_toByteArray_eq_toByteArray] using h

def positionSupplySharesSlotFunction : FunctionDecl := contract.functions[52]!

def positionSupplySharesSlotFrame (imms : Store) (id : UInt256) (user : AccountAddress) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert "user" (.address user)).insert "id" (wordBytes32Value id)
    immutables := imms }

def positionSupplySharesSlot (id : UInt256) (user : AccountAddress) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨2⟩ id) (UInt256.ofNat user.toNat)

theorem positionSupplySharesSlot_of_word (id user : UInt256) :
    positionSupplySharesSlot id (AccountAddress.ofNat user.toNat) =
      solcMappingSlot (solcMappingSlot ⟨2⟩ id) (UInt256.land solcAddrMask user) := by
  rw [positionSupplySharesSlot, accountAddress_ofNat_toNat_eq_mask, u256_ofNat_toNat]

theorem positionSupplySharesSlotBody (evm : EVM.State) (imms : Store)
    (id : UInt256) (user : AccountAddress) :
    ExecFuncBody config (positionSupplySharesSlotFrame imms id user) evm
      positionSupplySharesSlotFunction.body
      (.returned (positionSupplySharesSlotFrame imms id user) evm
        (some [wordBytes32Value (positionSupplySharesSlot id user)])) := by
  have hid : evalExpr? config (positionSupplySharesSlotFrame imms id user) evm (.var "id") =
      .ok (wordBytes32Value id) := by
    simp only [evalExpr?, positionSupplySharesSlotFrame, store_get_self, EvalResult.ofOption]
  have huser : evalExpr? config (positionSupplySharesSlotFrame imms id user) evm (.var "user") =
      .ok (.address user) := by
    simp only [evalExpr?, positionSupplySharesSlotFrame,
      store_get_ne _ _ (show ("id" == "user") = false from by decide),
      store_get_self, EvalResult.ofOption]
  have hu := evalExpr_addressToUint huser
  have hfit : user.toNat < UInt256.size := lt_of_lt_of_le user.isLt (by decide)
  have hunat : (UInt256.ofNat user.toNat).toNat = user.toNat :=
    UInt256.toNat_ofNat_of_lt hfit
  have huencode : encodePackedValue? abiUInt256 (.int (Int.ofNat user.toNat)) =
      some (EVM.Word.toBytesBE (UInt256.ofNat user.toNat)) := by
    simpa only [hunat] using encodePacked_uint256 (UInt256.ofNat user.toNat)
  have hinner := evalExpr_keccakWord (evalExpr_packedTwoWords hid
    (show evalExpr? config (positionSupplySharesSlotFrame imms id user) evm (.intLit 2) =
      .ok (uint256Value ⟨2⟩) by simp only [evalExpr?, uint256Value, pure]; rfl)
    (encodePacked_bytes32 id) (encodePacked_uint256 ⟨2⟩))
  have houter := evalExpr_keccakWord (evalExpr_packedTwoWords hu hinner huencode
    (encodePacked_bytes32 _))
  have hword := evalExpr_bytes32ToUint houter
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  apply evalExpr_uintToBytes32
  have hadd := checkedAddSourceOk hword
    (show evalExpr? config (positionSupplySharesSlotFrame imms id user) evm (.intLit 0) =
      .ok (uint256Value ⟨0⟩) by simp only [evalExpr?, uint256Value, pure]; rfl)
    (by simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.add_zero] using
      (positionSupplySharesSlot id user).val.isLt)
  simpa only [u256_add_zero] using hadd

theorem positionSupplySharesSlotCall (evm : EVM.State) (locals imms : Store)
    (id : UInt256) (user : AccountAddress) (retVar : Ident) (idExpr userExpr : Expr)
    (hid : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm idExpr = .ok (wordBytes32Value id))
    (huser : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm userExpr = .ok (.address user)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MorphoStorageLib_positionSupplySharesSlot" [idExpr, userExpr] retVar)
      (.ok
        { contract := contract
          locals := locals.insert retVar (wordBytes32Value (positionSupplySharesSlot id user))
          immutables := imms } evm) := by
  exact internalCallFunctionReturn
    (caller := { contract := contract, locals := locals, immutables := imms })
    (callee := positionSupplySharesSlotFunction)
    (value := some [wordBytes32Value (positionSupplySharesSlot id user)])
    (argVals := [wordBytes32Value id, .address user])
    (by simp [evalExprs?, hid, huser, bind, EvalResult.bind, pure]) rfl rfl
    (positionSupplySharesSlotBody evm imms id user)

end Benchmarks.Morpho.MetaMorphoV1_1
