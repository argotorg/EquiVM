import Benchmarks.UniswapV4PoolManager.ProtocolSwapFeeSource
import Benchmarks.UniswapV4PoolManager.PoolSwapSyntax
import Benchmarks.UniswapV4PoolManager.WordConditionalSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapProtocolWord (packed : UInt256) (zeroForOne : Bool) : UInt256 :=
  if zeroForOne then protocolFeeZeroWord (slot0FeeField packed 184) else protocolFeeOneWord (slot0FeeField packed 184)

theorem poolSwapProtocolWord_bound (packed : UInt256) (zeroForOne : Bool) :
    (poolSwapProtocolWord packed zeroForOne).toNat < 2^16 := by
  cases zeroForOne
  · exact lt_of_lt_of_le (protocolFeeOneWord_bound (slot0FeeField_bound packed 184)) (by decide)
  · exact lt_of_lt_of_le (protocolFeeZeroWord_bound (slot0FeeField packed 184)) (by decide)

def poolSwapProtocolInitFrame (f : Frame) (packed : UInt256) (zeroForOne : Bool) : Frame :=
  let f1 := wordLocal f "__c0" (slot0FeeField packed 184)
  let f2 := wordLocal f1 "__c1" (protocolFeeZeroWord (slot0FeeField packed 184))
  let f3 := wordLocal f2 "__c2" (slot0FeeField packed 184)
  let f4 := wordLocal f3 "__c3" (protocolFeeOneWord (slot0FeeField packed 184))
  wordLocal f4 "protocolFee" (poolSwapProtocolWord packed zeroForOne)

theorem poolSwapProtocolInitFrame_contract (f : Frame) (packed : UInt256) (zeroForOne : Bool) :
    (poolSwapProtocolInitFrame f packed zeroForOne).contract = f.contract := by
  simp only [poolSwapProtocolInitFrame, wordLocal_contract]

theorem poolSwapProtocolInitFrame_get (f : Frame) (packed : UInt256) (zeroForOne : Bool) (key : Ident)
    (h0 : ("__c0" == key) = false) (h1 : ("__c1" == key) = false) (h2 : ("__c2" == key) = false)
    (h3 : ("__c3" == key) = false) (hp : ("protocolFee" == key) = false) :
    (poolSwapProtocolInitFrame f packed zeroForOne).locals.get? key = f.locals.get? key := by
  simp only [poolSwapProtocolInitFrame, wordLocal_get, h0, h1, h2, h3, hp, Bool.false_eq_true, if_false]

theorem poolSwapProtocolInitSource {f : Frame} {evm : State} {packed : UInt256} {zeroForOne : Bool}
    (hf : f.contract = contract) (hs : f.locals.get? "slot0Start" = some (wordBytes32Value packed))
    (hz : f.locals.get? "zeroForOne" = some (.bool zeroForOne)) :
    ExecBlock config f evm ((poolSwapFunction.body.drop 6).take 5)
      (.ok (poolSwapProtocolInitFrame f packed zeroForOne) evm) := by
  let f1 := wordLocal f "__c0" (slot0FeeField packed 184)
  let f2 := wordLocal f1 "__c1" (protocolFeeZeroWord (slot0FeeField packed 184))
  let f3 := wordLocal f2 "__c2" (slot0FeeField packed 184)
  let f4 := wordLocal f3 "__c3" (protocolFeeOneWord (slot0FeeField packed 184))
  have h0 : ExecStmt config f evm poolSwapFunction.body[6]! (.ok f1 evm) :=
    slot0GetProtocolCall hf (evalLocalValue hs) "__c0"
  have h1 : ExecStmt config f1 evm poolSwapFunction.body[7]! (.ok f2 evm) :=
    protocolFeeZeroCall (f := f1) hf (slot0FeeField_bound packed 184) (evalLocalValue (store_get_self _ _ _)) "__c1"
  have hs2 : f2.locals.get? "slot0Start" = some (wordBytes32Value packed) :=
    (store_get_ne2 _ _ _ (by decide : ("__c0" == "slot0Start") = false)
      (by decide : ("__c1" == "slot0Start") = false)).trans hs
  have h2 : ExecStmt config f2 evm poolSwapFunction.body[8]! (.ok f3 evm) :=
    slot0GetProtocolCall (f := f2) hf (evalLocalValue hs2) "__c2"
  have h3 : ExecStmt config f3 evm poolSwapFunction.body[9]! (.ok f4 evm) :=
    protocolFeeOneCall (f := f3) hf (slot0FeeField_bound packed 184) (evalLocalValue (store_get_self _ _ _)) "__c3"
  have hz4 : f4.locals.get? "zeroForOne" = some (.bool zeroForOne) :=
    (store_get_ne4 _ _ _ _ _ (by decide : ("__c0" == "zeroForOne") = false)
      (by decide : ("__c1" == "zeroForOne") = false) (by decide : ("__c2" == "zeroForOne") = false)
      (by decide : ("__c3" == "zeroForOne") = false)).trans hz
  have h14 : f4.locals.get? "__c1" = some (.int (Int.ofNat (protocolFeeZeroWord (slot0FeeField packed 184)).toNat)) :=
    (store_get_ne2 _ _ _ (by decide : ("__c2" == "__c1") = false)
      (by decide : ("__c3" == "__c1") = false)).trans (store_get_self _ _ _)
  have h4 : ExecStmt config f4 evm poolSwapFunction.body[10]! (.ok (poolSwapProtocolInitFrame f packed zeroForOne) evm) := by
    apply ExecStmt.letDecl
    have hz' : evalExpr? config f4 evm (.var "zeroForOne") = .ok (.bool (decide (zeroForOne = true))) := by
      simpa only [Bool.decide_coe] using evalLocalValue (cfg := config) (evm := evm) hz4
    exact evalWordConditional hz' (evalLocalValue h14) (evalLocalValue (store_get_self _ _ _))
  exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2
    (ExecBlock.consNormal h3 (execBlock_singleton h4))))

end Benchmarks.UniswapV4PoolManager
