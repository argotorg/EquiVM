import Benchmarks.UniswapV3.Pool.CollectPaymentsTrace
import Benchmarks.UniswapV3.Pool.CollectPositionTrace
import Benchmarks.UniswapV3.Pool.CollectFinish

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem collectPaymentsBodyX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm0 evm : EVM.State} {k C : Nat}
    {aw p key lower upper amount0 amount1 junk req0 req1 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (recipient : AccountAddress) (locals : Store)
    (rd : RD (deployedRuntime v) ee g s0 ⟨7762⟩
      (amount1 :: solcMappingSlot ⟨7⟩ key :: junk :: amount0 :: req1 :: req0 ::
        positionTickWord upper :: positionTickWord lower :: EVM.word recipient.val :: ⟨690⟩ :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hprefix : ExecBlock config (collectFrame v recipient lower upper req0 req1) evm0
      (collectTransition.body.take 9)
      (.ok {contract := contract, locals := locals, immutables := immStore v} evm))
    (hvalues : CollectValues locals recipient lower upper key amount0 amount1)
    (hfit0 : amount0.toNat < 2 ^ 128) (hfit1 : amount1.toNat < 2 ^ 128)
    (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 140 ≤ 2 ^ 200) (hov : R.length + 29 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecTransitionBody config contract evm0 (collectLocals recipient lower upper req0 req1)
        collectTransition.body .reverted (immStore v)) ∨
    ∃ (evm' : EVM.State) (locals' : Store),
      ExecTransitionBody config contract evm0 (collectLocals recipient lower upper req0 req1)
        collectTransition.body
        (.returned {contract := contract, locals := locals', immutables := immStore v}
          (storeSlot0Unlocked evm' true)
          (some [.int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat)])) (immStore v) ∧
      RDret (deployedRuntime v) g s0 (storeSlot0Unlocked evm' true).accountMap
        (amount0.toByteArray ++ amount1.toByteArray) := by
  rcases collectPaymentX (v := v) false recipient locals rd hs hperm hvalues hfit0 hfit1
      hm hmem hzero (by omega) (by evm_ov) with
    ⟨rdRev, hpay0⟩ | ⟨evm1, σ1, locals1, out1, mem1, aw1, p1, k1, C1,
      hs1, hpay0, hvalues1, rd1, hm1, hmem1, hz1, hn1⟩
  · exact Or.inl ⟨rdRev, collectSourceRevert0 v evm0 evm recipient lower upper req0 req1 _ hprefix hpay0⟩
  · rcases collectPaymentX (v := v) (junk := ⟨0⟩) true recipient locals1 rd1 hs1 hperm
        hvalues1 hfit0 hfit1 hm1 hmem1 hz1 (by omega) (by evm_ov) with
      ⟨rdRev, hpay1⟩ | ⟨evm2, σ2, locals2, out2, mem2, aw2, p2, k2, C2,
        hs2, hpay1, hvalues2, rd2, hm2, hmem2, hz2, hn2⟩
    · exact Or.inl ⟨rdRev, collectSourceRevert1 v evm0 evm evm1 recipient lower upper req0 req1
        _ _ hprefix hpay0 hpay1⟩
    · exact Or.inr ⟨evm2, locals2,
        collectSourceReturn v evm0 evm evm1 evm2 recipient lower upper req0 req1 key amount0 amount1
          locals locals1 locals2 hprefix hpay0 hpay1 hvalues2,
        collectFinishX (v := v) recipient rd2 hs2 hperm hfit0 hfit1 hm2 (by omega) (by evm_ov)⟩

end Benchmarks.UniswapV3.Pool
