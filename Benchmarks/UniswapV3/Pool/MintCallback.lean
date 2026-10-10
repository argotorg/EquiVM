import Benchmarks.UniswapV3.Pool.MintCallbackCall
import Benchmarks.UniswapV3.Pool.MintCallValues
import Benchmarks.UniswapV3.Pool.SafeTransferCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def mintCallbackFrame (frame : Frame) (target : AccountAddress) : Frame :=
  {frame with locals := frame.locals.insert "callback" (.address target)}

def mintCallbackDoneFrame (frame : Frame) (target : AccountAddress) : Frame :=
  {mintCallbackFrame frame target with
    locals := (mintCallbackFrame frame target).locals.insert "__c4" .unit}

theorem mintCallbackX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {frame : Frame} {k C : Nat}
    {aw p bal0 bal1 amount0 amount1 junk1 junk0 len start : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨5966⟩
      (bal1 :: bal0 :: junk1 :: junk0 :: amount1 :: amount0 :: len :: start :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true) (hm : HeapMemory mem aw p)
    (hf0 : frame.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (hf1 : frame.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hd : frame.locals.get? "data" =
      some (.bytes (ee.calldata.extract start.toNat (start.toNat + len.toNat))))
    (hc : start.toNat + len.toNat ≤ ee.calldata.size) (hl : len.toNat ≤ 2 ^ 32)
    (hb : p.toNat + len.toNat + 164 ≤ 2 ^ 200) (hov : R.length + 22 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecBlock config frame evm ((mintTransition.body.drop 16).take 3) .reverted) ∨
    ∃ evm' σ' out aw' k' C', SourceState s0 ee σ' evm' ∧
      ExecBlock config frame evm ((mintTransition.body.drop 16).take 3)
        (.ok (mintCallbackDoneFrame frame ee.source) evm') ∧
      RD (deployedRuntime v) ee g s0 ⟨6116⟩
        (⟨0⟩ :: ((p + ⟨132⟩) + UInt256.ofNat (paddedSize len.toNat)) ::
          ⟨3544742295⟩ :: EVM.word ee.source.val :: bal1 :: bal0 :: junk1 :: junk0 :: amount1 :: amount0 :: len :: start :: R)
        (mintCallbackMem mem p amount0 amount1 ee.calldata start len) aw' out σ' k' C' ∧
      HeapMemory (mintCallbackMem mem p amount0 amount1 ee.calldata start len) aw' p ∧
      MemoryPrefix mem (mintCallbackMem mem p amount0 amount1 ee.calldata start len) p.toNat := by
  have hlet : ExecStmt config frame evm (mintTransition.body[16]!)
      (.ok (mintCallbackFrame frame ee.source) evm) := by
    apply ExecStmt.letDecl
    simp only [evalExpr?, pure, envValue, hs.env]
  obtain ⟨aw1, k1, C1, rd1, hm1⟩ := mintCallbackBuildX (v := v) rd hm hc hb hov
  rcases mintCallbackCallX (v := v) (frame := mintCallbackFrame frame ee.source)
      rd1 hs hperm hm1 (by simp [mintCallbackFrame])
      (by simpa [mintCallbackFrame, Std.HashMap.getElem?_insert] using hf0) (by simpa [mintCallbackFrame, Std.HashMap.getElem?_insert] using hf1)
      (by simpa [mintCallbackFrame, Std.HashMap.getElem?_insert] using hd)
      (by rw [ByteArray.size_extract]; omega) (mintCallbackMem_read _ _ _ _ _ _ _ hc hl)
      hl hb (by simpa only [List.length_cons] using hov) with
    ⟨rdBad, hbad⟩ | ⟨evm', σ', out, aw', k', C', hs', hgood, rdGood, hm'⟩
  · exact Or.inl ⟨rdBad, ExecBlock.consNormal hlet hbad⟩
  · exact Or.inr ⟨evm', σ', out, aw', k', C', hs', ExecBlock.consNormal hlet hgood,
      rdGood, hm', callbackMem_prefix _ _ _ _ _ _ _ _ hc⟩

theorem MintCallValues.callback {frame : Frame} {a : MintArgs}
    {amount0 amount1 before0 before1 : UInt256}
    (hv : MintCallValues frame.locals a amount0 amount1 before0 before1)
    (target : AccountAddress) :
    MintCallValues (mintCallbackDoneFrame frame target).locals a amount0 amount1 before0 before1 :=
  (hv.insert "callback" (.address target) (by decide)).insert "__c4" .unit (by decide)

end Benchmarks.UniswapV3.Pool
