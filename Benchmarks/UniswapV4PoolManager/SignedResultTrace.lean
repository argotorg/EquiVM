import Benchmarks.UniswapV4PoolManager.IntWordABI
import Reasoning.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a trace for a source computation returning one signed ABI word.
def signedResultTrace (bits : BitWidth) (code : ByteArray) (g : Sat256) (s0 : State) : ExecResult → Prop
  | .returned _ evm (some [.int n]) =>
      ∃ word : UInt256, n = EVM.signed word ∧
        (-Int.ofNat (EVM.twoPow (bits.val-1)) ≤ EVM.signed word ∧
          EVM.signed word < Int.ofNat (EVM.twoPow (bits.val-1))) ∧
        RDret code g s0 evm.accountMap word.toByteArray
  | .reverted => RDrev code g s0
  | .staticViolation => RDstatic code g s0
  | _ => False

theorem signedReturnEncoding (bits : BitWidth) (w : UInt256)
    (hw : -Int.ofNat (EVM.twoPow (bits.val-1)) ≤ EVM.signed w ∧
      EVM.signed w < Int.ofNat (EVM.twoPow (bits.val-1))) :
    encodeReturnValue? (.elem (.int (.sint bits))) (.int (EVM.signed w)) = some w.toByteArray :=
  scalarReturnEncoding rfl
    (by simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]; rfl)
    (encodeSignedWord bits w hw)

theorem signedResultTrace_refinement {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {σ σ₀ A I} {g : UInt256} {code : ByteArray} {args imms : Store} {result : ExecResult} {bits : BitWidth}
    (hcode : I.code = code) (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some args)
    (hbody : ExecTransitionBody cfg contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) args t.body result imms)
    (htrace : signedResultTrace bits code (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) result)
    (htype : t.returnType = [.elem (.int (.sint bits))])
    (hfallback : contract.fallback = none) (hreceive : contract.receive = none) :
    runtimeRefinementFor cfg contract σ σ₀ g A I imms := by
  unfold signedResultTrace at htrace
  split at htrace
  · obtain ⟨word, rfl, hw, hr⟩ := htrace
    exact hr.reEquivExecutionGen hcode hd hdec hbody rfl
      (by rw [htype]; exact returnEquiv_of_encode (signedReturnEncoding bits word hw)) hfallback hreceive
  · exact htrace.reEquivExecutionRevert hcode hd hdec hbody hfallback hreceive
  · exact htrace.reEquivStaticHalt hcode hd hdec hbody hfallback hreceive
  · contradiction

end Benchmarks.UniswapV4PoolManager
