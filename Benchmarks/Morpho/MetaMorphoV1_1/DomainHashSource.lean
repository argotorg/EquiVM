import Benchmarks.Morpho.MetaMorphoV1_1.PackedSource
import Benchmarks.EAS.Attester.WordSequenceMemory

/-! The five-word EIP-712 domain preimage and its source hash helper. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

def domainTypeHash : UInt256 :=
  ⟨63076024560530113402979550242307453568063438748328787417531900361828837441551⟩

def domainWords (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv) : List UInt256 :=
  [domainTypeHash, v._hashedName, v._hashedVersion, UInt256.ofNat Ethereum.chainId,
    UInt256.ofNat I.codeOwner.val]

def domainHash (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (KEC (wordBytes (domainWords v I)))

def buildDomainFunction : FunctionDecl := contract.functions[45]!

def domainFrame (v : MetaMorphoV1_1Immutables) (locals : Store) : Frame :=
  ⟨contract, locals, immStore v⟩

def domainTypeHashExpr : Expr :=
  .fixedBytesLit abiBytes32Width
    [139, 115, 195, 198, 155, 184, 254, 61, 81, 46, 204, 76, 247, 89, 204, 121,
      35, 159, 123, 23, 155, 15, 250, 202, 169, 167, 93, 82, 43, 57, 64, 15]

theorem buildDomainBody (evm : State) (v : MetaMorphoV1_1Immutables) (locals : Store) :
    ExecFuncBody config (domainFrame v locals) evm buildDomainFunction.body
      (.returned (domainFrame v locals) evm
        (some [wordBytes32Value (domainHash v evm.executionEnv)])) := by
  have htype : evalExpr? config (domainFrame v locals) evm domainTypeHashExpr =
      .ok (wordBytes32Value domainTypeHash) := by
    simp only [domainTypeHashExpr, evalExpr?, pure]
    native_decide
  have hname := evalExpr_uintToBytes32
    (evalImmutable__hashedName config contract locals evm v)
  have hver := evalExpr_uintToBytes32
    (evalImmutable__hashedVersion config contract locals evm v)
  have hchain : evalExpr? config (domainFrame v locals) evm (.env .chainid) =
      .ok (uint256Value (UInt256.ofNat Ethereum.chainId)) := by
    simp only [evalExpr?]
    rfl
  have hself : evalExpr? config (domainFrame v locals) evm (.env .this) =
      .ok (.address evm.executionEnv.codeOwner) := by simp only [evalExpr?]; rfl
  have haddr := evalExpr_addressToWord hself
  have hpack := evalExpr_packed (evalPackedArgs_cons htype (encodePacked_bytes32 domainTypeHash)
    (evalPackedArgs_cons hname (encodePacked_bytes32 v._hashedName)
      (evalPackedArgs_cons hver (encodePacked_bytes32 v._hashedVersion)
        (evalPackedArgs_cons hchain (encodePacked_uint256 (UInt256.ofNat Ethereum.chainId))
          (evalPackedArgs_cons (args := []) (tail := []) haddr
            (encodePacked_uint256 (UInt256.ofNat evm.executionEnv.codeOwner.val))
            (by simp only [evalPackedArgs?, pure]))))))
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  apply evalExpr_keccakWord
  simpa only [domainHash, domainWords, wordBytes, List.toByteArray_append,
    word_toBytesBE_toByteArray_eq_toByteArray, List.append_nil, ByteArray.append_empty]
    using hpack

theorem buildDomainCall (evm : State) (v : MetaMorphoV1_1Immutables) (locals : Store)
    (retVar : Ident) :
    ExecStmt config (domainFrame v locals) evm (.internalCall "_buildDomainSeparator" [] retVar)
      (.ok (domainFrame v (locals.insert retVar (wordBytes32Value (domainHash v evm.executionEnv))))
        evm) := by
  exact internalCallFunctionReturn (callee := buildDomainFunction)
    (argVals := []) (value := some [wordBytes32Value (domainHash v evm.executionEnv)])
    (by simp only [evalExprs?, pure]) rfl rfl (buildDomainBody evm v ∅)

end Benchmarks.Morpho.MetaMorphoV1_1
