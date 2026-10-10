import Benchmarks.UniswapV3.Pool.FlashCallbackCall
import Benchmarks.UniswapV3.Pool.FlashPrefix
import Benchmarks.UniswapV3.Pool.SafeTransferCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def flashCallbackFrame (frame : Frame) (target : AccountAddress) : Frame :=
  {frame with locals := frame.locals.insert "callback" (.address target)}

def flashCallbackDoneFrame (frame : Frame) (target : AccountAddress) : Frame :=
  {flashCallbackFrame frame target with
    locals := (flashCallbackFrame frame target).locals.insert "__c7" .unit}

theorem flashCallbackX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {frame : Frame} {k C : Nat}
    {aw p bal0 bal1 fee0 fee1 liquidity len start : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨6827⟩
      (bal1 :: bal0 :: fee1 :: fee0 :: liquidity :: len :: start :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true) (hm : HeapMemory mem aw p)
    (hf0 : frame.locals.get? "fee0" = some (.int (Int.ofNat fee0.toNat)))
    (hf1 : frame.locals.get? "fee1" = some (.int (Int.ofNat fee1.toNat)))
    (hd : frame.locals.get? "data" =
      some (.bytes (ee.calldata.extract start.toNat (start.toNat + len.toNat))))
    (hc : start.toNat + len.toNat ≤ ee.calldata.size) (hl : len.toNat ≤ 2 ^ 32)
    (hb : p.toNat + len.toNat + 164 ≤ 2 ^ 200) (hov : R.length + 21 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecBlock config frame evm ((flashTransition.body.drop 12).take 3) .reverted) ∨
    ∃ evm' σ' out aw' k' C', SourceState s0 ee σ' evm' ∧
      ExecBlock config frame evm ((flashTransition.body.drop 12).take 3)
        (.ok (flashCallbackDoneFrame frame ee.source) evm') ∧
      RD (deployedRuntime v) ee g s0 ⟨15572⟩
        (⟨6991⟩ :: ⟨0⟩ :: bal1 :: bal0 :: fee1 :: fee0 :: liquidity :: len :: start :: R)
        (flashCallbackMem mem p fee0 fee1 ee.calldata start len) aw' out σ' k' C' ∧
      HeapMemory (flashCallbackMem mem p fee0 fee1 ee.calldata start len) aw' p ∧
      MemoryPrefix mem (flashCallbackMem mem p fee0 fee1 ee.calldata start len) p.toNat := by
  have hlet : ExecStmt config frame evm (flashTransition.body[12]!)
      (.ok (flashCallbackFrame frame ee.source) evm) := by
    apply ExecStmt.letDecl
    simp only [evalExpr?, pure, envValue, hs.env]
  obtain ⟨aw1, k1, C1, rd1, hm1⟩ := flashCallbackBuildX (v := v) rd hm hc hb hov
  rcases flashCallbackCallX (v := v) (frame := flashCallbackFrame frame ee.source)
      rd1 hs hperm hm1 (by simp [flashCallbackFrame])
      (by simpa [flashCallbackFrame, Std.HashMap.getElem?_insert] using hf0) (by simpa [flashCallbackFrame, Std.HashMap.getElem?_insert] using hf1)
      (by simpa [flashCallbackFrame, Std.HashMap.getElem?_insert] using hd)
      (by rw [ByteArray.size_extract]; omega) (flashCallbackMem_read _ _ _ _ _ _ _ hc hl)
      hl hb (by simpa only [List.length_cons] using hov) with
    ⟨rdBad, hbad⟩ | ⟨evm', σ', out, aw', k', C', hs', hgood, rdGood, hm'⟩
  · exact Or.inl ⟨rdBad, ExecBlock.consNormal hlet hbad⟩
  · exact Or.inr ⟨evm', σ', out, aw', k', C', hs', ExecBlock.consNormal hlet hgood,
      rdGood, hm', callbackMem_prefix _ _ _ _ _ _ _ _ hc⟩

end Benchmarks.UniswapV3.Pool
