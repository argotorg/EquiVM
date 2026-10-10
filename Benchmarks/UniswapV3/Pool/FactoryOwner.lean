import Benchmarks.UniswapV3.Pool.Calls
import Reasoning.ABIComposite
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 10000

abbrev factoryOwnerFunction : FunctionDecl := contract.functions[0]!

theorem factoryOwnerLookup :
    lookupCallable? contract "factoryOwner" = some factoryOwnerFunction.toCallable := rfl

def factoryOwnerCalldata : ByteArray := ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩

def factoryOwnerLocals (v : UniswapV3PoolImmutables) : Store :=
  (∅ : Store).insert "currentFactory" (.address v.factory)

def factoryOwnerCallLocals (v : UniswapV3PoolImmutables) (ok : Bool) (out : ByteArray) : Store :=
  ((factoryOwnerLocals v).insert "ownerSuccess" (.bool ok)).insert "ownerData" (.bytes out)

def factoryOwnerFrame (v : UniswapV3PoolImmutables) : Frame :=
  { contract := contract, locals := factoryOwnerLocals v, immutables := immStore v }

def factoryOwnerCallFrame (v : UniswapV3PoolImmutables) (ok : Bool) (out : ByteArray) : Frame :=
  { contract := contract, locals := factoryOwnerCallLocals v ok out, immutables := immStore v }

theorem evalFactoryOwnerReceiver (v : UniswapV3PoolImmutables) (evm : EVM.State) :
    evalExpr? config (factoryOwnerFrame v) evm (.var "currentFactory") =
      .ok (.address v.factory) := by
  simp [evalExpr?, factoryOwnerFrame, factoryOwnerLocals, EvalResult.ofOption]

theorem evalFactoryOwnerCodeGuard (v : UniswapV3PoolImmutables) (evm : EVM.State) :
    evalExpr? config (factoryOwnerFrame v) evm
      (.binary .gt (.extCodeSize (.var "currentFactory")) (.intLit 0)) =
      .ok (.bool (decide (0 < (extCodeSizeWord evm.accountMap (EVM.word v.factory.val)).toNat))) :=
  evalExpr_codeGuard_of_accounts_eq rfl (accountAddress_roundtrip v.factory).symm
    (evalFactoryOwnerReceiver v evm)

theorem factoryOwnerPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (hcode : extCodeSizeWord evm.accountMap (EVM.word v.factory.val) ≠ ⟨0⟩) :
    ABlock config evm { contract := contract, locals := ∅, immutables := immStore v }
      factoryOwnerFunction.body (factoryOwnerFrame v)
      [.lowLevelCall (.var "currentFactory") (.intLit 0) (.bytesLit factoryOwnerCalldata)
        "ownerSuccess" "ownerData" false,
       .require (.var "ownerSuccess"),
       .return [.abiDecode abiAddress (.var "ownerData")]] := by
  have hpos : 0 < (extCodeSizeWord evm.accountMap (EVM.word v.factory.val)).toNat := by
    by_contra h
    exact hcode (uint256_toNat_eq_zero (by omega))
  exact (ABlock.start.letStep (evalImmutable_factory config contract ∅ evm v)).requireStep
    (by simpa only [hpos, decide_true] using evalFactoryOwnerCodeGuard v evm)

theorem factoryOwnerCall (v : UniswapV3PoolImmutables) (evm evm' : EVM.State)
    (ok : Bool) (out : ByteArray)
    (hcall : callViaEVM evm v.factory 0 factoryOwnerCalldata (ok, evm', out) false) :
    ExecStmt config (factoryOwnerFrame v) evm
      (.lowLevelCall (.var "currentFactory") (.intLit 0) (.bytesLit factoryOwnerCalldata)
        "ownerSuccess" "ownerData" false)
      (.ok (factoryOwnerCallFrame v ok out) evm') :=
  lowLevelCallWithPermSource (evalFactoryOwnerReceiver v evm)
    (by simp only [evalExpr?, pure]) (by simp only [evalExpr?, pure]) hcall

theorem evalFactoryOwnerSuccess (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (ok : Bool) (out : ByteArray) :
    evalExpr? config (factoryOwnerCallFrame v ok out) evm (.var "ownerSuccess") =
      .ok (.bool ok) := by
  simp [evalExpr?, factoryOwnerCallFrame, factoryOwnerCallLocals, factoryOwnerLocals,
    EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem evalFactoryOwnerData (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (ok : Bool) (out : ByteArray) :
    evalExpr? config (factoryOwnerCallFrame v ok out) evm (.var "ownerData") =
      .ok (.bytes out) := by
  simp [evalExpr?, factoryOwnerCallFrame, factoryOwnerCallLocals, factoryOwnerLocals,
    EvalResult.ofOption]

theorem factoryOwnerReturns (v : UniswapV3PoolImmutables) (evm evm' : EVM.State)
    (out : ByteArray)
    (hcode : extCodeSizeWord evm.accountMap (EVM.word v.factory.val) ≠ ⟨0⟩)
    (hcall : callViaEVM evm v.factory 0 factoryOwnerCalldata (true, evm', out) false)
    (hout : 32 ≤ out.size) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := immStore v } evm
      factoryOwnerFunction.body
      (.returned (factoryOwnerCallFrame v true out) evm'
        (some [.address (AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32)))])) := by
  apply ExecFuncBody.execBlockRet
  apply (factoryOwnerPrefix v evm hcode).run
  refine ExecBlock.consNormal (factoryOwnerCall v evm evm' true out hcall) ?_
  apply (ABlock.start.requireStep (evalFactoryOwnerSuccess v evm' true out)).returns
  simp only [evalExpr?, evalFactoryOwnerData, bind, EvalResult.bind]
  exact congrArg (fun r : Option Value =>
    match r with | some val => EvalResult.ok val | none => .revert)
    (decodeReturnValue_legacyAddress_ok hout)

theorem factoryOwnerRevertsNoCode (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (hcode : extCodeSizeWord evm.accountMap (EVM.word v.factory.val) = ⟨0⟩) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := immStore v } evm
      factoryOwnerFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (ABlock.start.letStep (evalImmutable_factory config contract ∅ evm v)).requireRevert
  simpa only [hcode] using evalFactoryOwnerCodeGuard v evm

theorem factoryOwnerRevertsCall (v : UniswapV3PoolImmutables) (evm evm' : EVM.State)
    (out : ByteArray)
    (hcode : extCodeSizeWord evm.accountMap (EVM.word v.factory.val) ≠ ⟨0⟩)
    (hcall : callViaEVM evm v.factory 0 factoryOwnerCalldata (false, evm', out) false) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := immStore v } evm
      factoryOwnerFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (factoryOwnerPrefix v evm hcode).run
  refine ExecBlock.consNormal (factoryOwnerCall v evm evm' false out hcall) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalFactoryOwnerSuccess v evm' false out))

theorem factoryOwnerRevertsShort (v : UniswapV3PoolImmutables) (evm evm' : EVM.State)
    (out : ByteArray)
    (hcode : extCodeSizeWord evm.accountMap (EVM.word v.factory.val) ≠ ⟨0⟩)
    (hcall : callViaEVM evm v.factory 0 factoryOwnerCalldata (true, evm', out) false)
    (hout : out.size < 32) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := immStore v } evm
      factoryOwnerFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (factoryOwnerPrefix v evm hcode).run
  refine ExecBlock.consNormal (factoryOwnerCall v evm evm' true out hcall) ?_
  apply (ABlock.start.requireStep (evalFactoryOwnerSuccess v evm' true out)).run
  apply ExecBlock.consRevert
  apply ExecStmt.returnRevert
  simp only [evalExprs?, evalExpr?, evalFactoryOwnerData, bind, EvalResult.bind]
  rw [show decodeReturnValueWithMode? config.abiDecodeMode abiAddress out = none from
    decodeReturnValue_legacyAddress_none_short hout]

def factoryOwnerInputMem : ByteArray :=
  solcReturnMem (UInt256.shiftLeft (UInt256.ofNat 2376452955) (UInt256.ofNat 224))

theorem factoryOwnerInputMem_size : factoryOwnerInputMem.size = 160 :=
  solcReturnMem_size _

theorem factoryOwnerInputMem_read :
    factoryOwnerInputMem.readWithPadding 128 4 = factoryOwnerCalldata := by native_decide

theorem factoryOwnerInputMem_read64 :
    factoryOwnerInputMem.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray :=
  solcReturnMem_read64 _

theorem factoryOwnerInputMem_mload64 : memLoad ⟨64⟩ factoryOwnerInputMem = ⟨128⟩ :=
  solcReturnMem_mload64 _

def factoryOwnerOutputMem (out : ByteArray) : ByteArray :=
  callOutputMem factoryOwnerInputMem out ⟨128⟩ ⟨32⟩

theorem factoryOwnerOutputMem_size (out : ByteArray) (hb : out.size < UInt256.size) :
    (factoryOwnerOutputMem out).size = 160 := by
  rw [factoryOwnerOutputMem, callOutput32_size _ _ _ hb (by
    rw [factoryOwnerInputMem_size]; decide), factoryOwnerInputMem_size]

theorem factoryOwnerOutputMem_read64 (out : ByteArray) (hb : out.size < UInt256.size) :
    (factoryOwnerOutputMem out).readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray := by
  rw [factoryOwnerOutputMem, callOutput32_read_below _ _ _ _ hb (by
    rw [factoryOwnerInputMem_size]; decide) (by decide), factoryOwnerInputMem_read64]

theorem factoryOwnerOutputMem_mload64 (out : ByteArray) (hb : out.size < UInt256.size) :
    memLoad ⟨64⟩ (factoryOwnerOutputMem out) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [factoryOwnerOutputMem_size out hb]; decide)
    (factoryOwnerOutputMem_read64 out hb)

theorem factoryOwnerOutputMem_mload128 (out : ByteArray)
    (hb : out.size < UInt256.size) (hs : 32 ≤ out.size) :
    memLoad ⟨128⟩ (factoryOwnerOutputMem out) = calldataWord out 0 := by
  apply loadedWord_of_read
  · rw [factoryOwnerOutputMem_size out hb]; decide
  · exact callOutput32_read_word _ out ⟨128⟩ hb hs (by
      rw [factoryOwnerInputMem_size]; decide)

theorem factoryOwnerWord (out : ByteArray) (hs : 32 ≤ out.size) :
    EVM.word (AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32))).val =
      UInt256.land solcAddrMask (calldataWord out 0) := by
  have hw := congrArg fromByteArrayBigEndian (calldataWord_bytes hs)
  rw [fromByteArrayBigEndian_toByteArray] at hw
  rw [← hw, word_of_addressOfNat_eq_mask, u256_land_comm]

end Benchmarks.UniswapV3.Pool
