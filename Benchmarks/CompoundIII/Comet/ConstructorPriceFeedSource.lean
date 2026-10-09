import Benchmarks.CompoundIII.Comet.ConstructorPriceFeedCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def constructorSourcePriceFeed (c : ConstructorConfig) (w feed : UInt256) : Frame :=
  { constructorSourceDecimals c w with locals :=
      (constructorSourceDecimals c w).locals.insert "__c1" (.int (Int.ofNat feed.toNat)) }

theorem constructorSource_priceFeed (c : ConstructorConfig) (w : UInt256) (evm : EVM.State) :
    evalExpr? config (constructorSourceDecimals c w) evm
      (.field (.var "config") "baseTokenPriceFeed") = .ok (.address c.baseTokenPriceFeed) := by
  simp only [evalExpr?, constructorSourceDecimals, constructorSourceConfig,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption,
    bind, EvalResult.bind]
  rfl

theorem constructorSource_priceFeedGuard (c : ConstructorConfig) (w feed : UInt256)
    (evm : EVM.State) :
    evalExpr? config (constructorSourcePriceFeed c w feed) evm
      (.binary .eq (.var "__c1") (.intLit 8)) = .ok (.bool (decide (feed = ⟨8⟩))) := by
  simp only [evalExpr?, constructorSourcePriceFeed, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, EvalResult.ofOption, pure, bind, EvalResult.bind, evalBinaryOp?]
  change EvalResult.ok (Value.bool (Value.int (Int.ofNat feed.toNat) == Value.int 8)) = _
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq]
  constructor
  · intro he
    apply u256_inj
    change feed.toNat = 8
    exact Int.ofNat.inj he
  · intro he
    rw [he]
    rfl

theorem constructorSourcePriceFeed_exec {c : ConstructorConfig} {w : UInt256}
    {evm evm' evm'' : EVM.State} {feed : ByteArray}
    (hp : ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 7)
      (.ok (constructorSourceDecimals c w) evm'))
    (hc : callViaEVM evm' c.baseTokenPriceFeed 0 decimalsPayload (true, evm'', feed) false)
    (hhi : feed.size < 2^255) (hvalid : DecimalsReturnValid feed) :
    ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 8)
      (.ok (constructorSourcePriceFeed c w (calldataWord feed 0)) evm'') := by
  change ExecBlock config _ _ (contract.ctor.body.take 7 ++
    [.externalCall (.field (.var "config") "baseTokenPriceFeed") "decimals" (.intLit 0) []
      "__c1" (perm := false)]) _
  apply execBlockAppendOk hp
  exact .consNormal (decimals_source_ok (constructorSource_priceFeed c w evm') hc hhi hvalid) .nil

theorem constructorSourcePriceFeedChecked_exec {c : ConstructorConfig} {w : UInt256}
    {evm evm' evm'' : EVM.State} {feed : ByteArray}
    (hp : ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 7)
      (.ok (constructorSourceDecimals c w) evm'))
    (hc : callViaEVM evm' c.baseTokenPriceFeed 0 decimalsPayload (true, evm'', feed) false)
    (hhi : feed.size < 2^255) (hlo : 32 ≤ feed.size) (hword : calldataWord feed 0 = ⟨8⟩) :
    ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 9)
      (.ok (constructorSourcePriceFeed c w (calldataWord feed 0)) evm'') := by
  have hd := constructorSourcePriceFeed_exec hp hc hhi ⟨hlo, by rw [hword]; decide⟩
  change ExecBlock config _ _ (contract.ctor.body.take 8 ++
    [.require (.binary .eq (.var "__c1") (.intLit 8))]) _
  apply execBlockAppendOk hd
  exact .consNormal (.requireTrue (by
    rw [constructorSource_priceFeedGuard, decide_eq_true hword])) .nil

theorem constructorSourcePriceFeedChecked_revert {c : ConstructorConfig} {w : UInt256}
    {evm evm' evm'' : EVM.State} {z : Bool} {feed : ByteArray}
    (hp : ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 7)
      (.ok (constructorSourceDecimals c w) evm'))
    (hc : callViaEVM evm' c.baseTokenPriceFeed 0 decimalsPayload (z, evm'', feed) false)
    (hhi : feed.size < 2^255)
    (hvalid : ¬ (z = true ∧ 32 ≤ feed.size ∧ calldataWord feed 0 = ⟨8⟩)) :
    ExecBlock config (constructorSourceEntry c) evm contract.ctor.body .reverted := by
  by_cases hdecode : z = true ∧ DecimalsReturnValid feed
  · rcases hdecode with ⟨rfl, hdecode⟩
    have hd := constructorSourcePriceFeed_exec hp hc hhi hdecode
    rw [← List.take_append_drop 8 contract.ctor.body]
    apply execBlockAppendOk hd
    exact .consRevert (.requireFalse (by
      rw [constructorSource_priceFeedGuard,
        decide_eq_false (fun hw ↦ hvalid ⟨rfl, hdecode.1, hw⟩)]))
  · rw [← List.take_append_drop 7 contract.ctor.body]
    apply execBlockAppendOk hp
    exact .consRevert (decimals_source_revert (constructorSource_priceFeed c w evm') hc hhi hdecode)

end Benchmarks.CompoundIII.Comet
