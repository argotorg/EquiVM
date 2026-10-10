import Benchmarks.UniswapV3.Pool.CollectProtocolAmountsTrace
import Benchmarks.UniswapV3.Pool.CollectProtocolFactory
import Benchmarks.UniswapV3.Pool.CollectProtocolFinish

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem collectProtocolPaymentsBodyX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm0 evm : EVM.State} {k C : Nat} {aw p amount0 amount1 junk req0 req1 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (recipient : AccountAddress) (locals : Store)
    (rd : RD (deployedRuntime v) ee g s0 ⟨9062⟩
      (amount1 :: junk :: amount0 :: req1 :: req0 :: EVM.word recipient.val :: ⟨690⟩ :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hprefix : ExecBlock config (collectProtocolFrame v recipient req0 req1) evm0
      (collectProtocolTransition.body.take 9)
      (.ok {contract := contract, locals := locals, immutables := immStore v} evm))
    (hvalues : CollectProtocolValues locals recipient amount0 amount1)
    (hfit0 : amount0.toNat < 2 ^ 128) (hfit1 : amount1.toNat < 2 ^ 128)
    (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 140 ≤ 2 ^ 200) (hov : R.length + 26 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecTransitionBody config contract evm0 (collectProtocolLocals recipient req0 req1)
        collectProtocolTransition.body .reverted (immStore v)) ∨
    ∃ (evm' : EVM.State) (locals' : Store) (final0 final1 : UInt256),
      ExecTransitionBody config contract evm0 (collectProtocolLocals recipient req0 req1)
        collectProtocolTransition.body
        (.returned {contract := contract, locals := locals', immutables := immStore v}
          (storeSlot0Unlocked evm' true)
          (some [.int (Int.ofNat final0.toNat), .int (Int.ofNat final1.toNat)])) (immStore v) ∧
      final0.toNat < 2 ^ 128 ∧ final1.toNat < 2 ^ 128 ∧
      RDret (deployedRuntime v) g s0 (storeSlot0Unlocked evm' true).accountMap
        (final0.toByteArray ++ final1.toByteArray) := by
  rcases collectProtocolPaymentX (v := v) false recipient locals rd hs hperm hvalues hfit0 hfit1
      hm hmem hzero (by omega) (by evm_ov) with
    ⟨rdRev, hpay0⟩ | ⟨evm1, σ1, locals1, a0, a1, out1, mem1, aw1, p1, k1, C1,
      hs1, hpay0, hvalues1, hfit01, hfit11, rd1, hm1, hmem1, hz1, hn1⟩
  · exact Or.inl ⟨rdRev, collectProtocolSourceRevert0 v evm0 evm recipient req0 req1 _ hprefix hpay0⟩
  · rcases collectProtocolPaymentX (v := v) (junk := ⟨0⟩) true recipient locals1 rd1 hs1 hperm
        hvalues1 hfit01 hfit11 hm1 hmem1 hz1 (by omega) (by evm_ov) with
      ⟨rdRev, hpay1⟩ | ⟨evm2, σ2, locals2, final0, final1, out2, mem2, aw2, p2, k2, C2,
        hs2, hpay1, hvalues2, hfit02, hfit12, rd2, hm2, hmem2, hz2, hn2⟩
    · exact Or.inl ⟨rdRev, collectProtocolSourceRevert1 v evm0 evm evm1 recipient req0 req1
        _ _ hprefix hpay0 hpay1⟩
    · exact Or.inr ⟨evm2, locals2, final0, final1,
        collectProtocolSourceReturn v evm0 evm evm1 evm2 recipient req0 req1 final0 final1
          locals locals1 locals2 hprefix hpay0 hpay1 hvalues2,
        hfit02, hfit12, collectProtocolFinishX (v := v) rd2 hs2 hperm hfit02 hfit12 hm2
          (by omega) (by evm_ov)⟩

end Benchmarks.UniswapV3.Pool
