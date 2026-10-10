import Benchmarks.UniswapV3.Pool.SourceExpressions
import Benchmarks.UniswapV3.Pool.PackedBytes

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

abbrev positionGetFunction : FunctionDecl := contract.functions[14]!

theorem positionGetLookup :
    lookupCallable? contract "Position_get" = some positionGetFunction.toCallable := rfl

def positionTick (w : UInt256) : Int :=
  normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat w.toNat)

def positionTickWord (w : UInt256) : UInt256 := UInt256.signextend (UInt256.ofNat 2) w

theorem positionTickWord_eq (w : UInt256) :
    positionTickWord w = EVM.wordOfInt (positionTick w) :=
  signextend_normalizeSint ⟨24, by decide⟩ (UInt256.ofNat 2) w (by decide) (by decide)

theorem positionTickWord_idem (w : UInt256) :
    positionTickWord (positionTickWord w) = positionTickWord w :=
  signextend_idem ⟨24, by decide⟩ (UInt256.ofNat 2) w (by decide) (by decide)

theorem positionTick_clean (w : UInt256) : positionTick (positionTickWord w) = positionTick w := by
  have hmod : Int.ofNat (positionTickWord w).toNat % Int.ofNat (EVM.twoPow 24) =
      Int.ofNat w.toNat % Int.ofNat (EVM.twoPow 24) := by
    rw [positionTickWord_eq]
    change Int.ofNat ((EVM.wordOfInt (positionTick w)).toNat % 2 ^ 24) =
      Int.ofNat (w.toNat % 2 ^ 24)
    unfold positionTick
    rw [wordOfInt_normalizeSint_mod]
  unfold positionTick
  rw [normalizeInt, hmod]
  rfl

def positionPackedBytes (owner : AccountAddress) (lower upper : UInt256) : ByteArray :=
  (EVM.word owner.val).toByteArray.extract 12 32 ++
    (positionTickWord lower).toByteArray.extract 29 32 ++
    (positionTickWord upper).toByteArray.extract 29 32

def positionKey (owner : AccountAddress) (lower upper : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (positionPackedBytes owner lower upper))

def positionGetLocals (owner : AccountAddress) (lower upper : UInt256) : Store :=
  (((∅ : Store).insert "tickUpper" (.int (positionTick upper))).insert "tickLower"
    (.int (positionTick lower))).insert "owner" (.address owner)

def positionGetFrame (imms : Store) (owner : AccountAddress) (lower upper : UInt256) : Frame :=
  { contract := contract, locals := positionGetLocals owner lower upper, immutables := imms }

theorem positionGetBind (owner : AccountAddress) (lower upper : UInt256) :
    bindParams? positionGetFunction.params
      [.address owner, .int (positionTick lower), .int (positionTick upper)] =
      some (positionGetLocals owner lower upper) := rfl

def positionPackedArgs : List (ABIType × Expr) :=
  [(.elem .address, .var "owner"),
   (.elem (.int (.sint ⟨24, by decide⟩)), .var "tickLower"),
   (.elem (.int (.sint ⟨24, by decide⟩)), .var "tickUpper")]

theorem evalPositionPackedArgs (imms : Store) (evm : EVM.State)
    (owner : AccountAddress) (lower upper : UInt256) :
    evalPackedArgs? config (positionGetFrame imms owner lower upper) evm positionPackedArgs =
      .ok (positionPackedBytes owner lower upper).toList := by
  have ho : evalExpr? config (positionGetFrame imms owner lower upper) evm
      (.var "owner") = .ok (.address owner) := evalExpr_var_get (by simp [positionGetFrame, positionGetLocals])
  have hl : evalExpr? config (positionGetFrame imms owner lower upper) evm
      (.var "tickLower") = .ok (.int (positionTick lower)) :=
    evalExpr_var_get (by simp [positionGetFrame, positionGetLocals, Std.HashMap.getElem_insert])
  have hu : evalExpr? config (positionGetFrame imms owner lower upper) evm
      (.var "tickUpper") = .ok (.int (positionTick upper)) :=
    evalExpr_var_get (by simp [positionGetFrame, positionGetLocals, Std.HashMap.getElem_insert])
  have henc (w : UInt256) :
      encodePackedValue? (.elem (.int (.sint ⟨24, by decide⟩))) (.int (positionTick w)) =
        some ((EVM.Word.toBytesBE (positionTickWord w)).drop 29) := by
    rw [positionTickWord_eq]
    exact encodePacked_sintCast ⟨24, by decide⟩ w
  have hargs := evalPackedArgs_cons ho (show encodePackedValue? (.elem .address) (.address owner) =
    some ((EVM.Word.toBytesBE (EVM.word owner.val)).drop 12) from rfl)
    (evalPackedArgs_cons hl (henc lower) (evalPackedArgs_single hu (henc upper)))
  simpa only [positionPackedArgs, positionPackedBytes, byteArray_toList_append,
    wordBytes_extract_suffix, List.append_assoc] using hargs

theorem positionGetReturns (imms : Store) (evm : EVM.State)
    (owner : AccountAddress) (lower upper : UInt256) :
    ExecFuncBody config (positionGetFrame imms owner lower upper) evm positionGetFunction.body
      (.returned (positionGetFrame imms owner lower upper) evm
        (some [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (positionKey owner lower upper))])) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  change evalExpr? config _ _ (.keccak256 (.abiEncodePacked positionPackedArgs)) = _
  simp only [evalExpr?, evalPositionPackedArgs, bind, EvalResult.bind, pure,
    byteArray_mk_toList_toArray]
  rw [positionKey, toBytesBE_keccak_uInt256OfByteArray]

end Benchmarks.UniswapV3.Pool
