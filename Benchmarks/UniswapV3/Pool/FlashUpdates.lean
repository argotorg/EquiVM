import Benchmarks.UniswapV3.Pool.FlashUpdate
import Benchmarks.UniswapV3.Pool.FlashValues
import Benchmarks.UniswapV3.Pool.FlashPaidTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem flashUpdatesX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat}
    {aw paid1 paid0 after1 after0 before1 before0 fee1 fee0 liquidity amount0 amount1 : UInt256}
    {recipient : AccountAddress} {mem rdata : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables} (locals : Store)
    (rd : RD (deployedRuntime v) ee g s0
      (if paid0 = ⟨0⟩ then flashUpdateExit false else flashProtocolEntry false)
      (flashUpdateRest paid1 paid0 after1 after0 before1 before0 fee1 fee0 liquidity R)
      mem aw rdata σ k C) (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hcore : FlashCoreValues locals recipient amount0 amount1 liquidity)
    (hp0 : locals.get? "paid0" = some (.int (Int.ofNat paid0.toNat)))
    (hp1 : locals.get? "paid1" = some (.int (Int.ofNat paid1.toNat)))
    (hliquidity : liquidity.toNat < 2 ^ 128) (hov : R.length + 27 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
        ((flashTransition.body.drop 23).take 2) .reverted) ∨
    ∃ evm' σ' locals' k' C', SourceState s0 ee σ' evm' ∧
      ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
        ((flashTransition.body.drop 23).take 2)
        (.ok {contract := contract, locals := locals', immutables := immStore v} evm') ∧
      RD (deployedRuntime v) ee g s0 ⟨7421⟩
        (flashUpdateRest paid1 paid0 after1 after0 before1 before0 fee1 fee0 liquidity R)
        mem aw rdata σ' k' C' ∧ FlashCoreValues locals' recipient amount0 amount1 liquidity ∧
      locals'.get? "paid0" = some (.int (Int.ofNat paid0.toNat)) ∧
      locals'.get? "paid1" = some (.int (Int.ofNat paid1.toNat)) := by
  rcases flashUpdateX (v := v) locals false rd hs hperm hp0 hcore.liquidity hcore.slot0
      hcore.protocolFees hcore.growth0 hliquidity hov with
    ⟨rdBad, hbad⟩ | ⟨evm1, σ1, locals1, k1, C1, hs1, hsource0, rd1, hkeep0⟩
  · exact Or.inl ⟨rdBad, ExecBlock.consRevert hbad⟩
  · have hcore1 := hcore.update hkeep0
    have hp01 : locals1.get? "paid0" = some (.int (Int.ofNat paid0.toNat)) := by
      rw [hkeep0 "paid0" (by decide) (by decide) (by decide)]; exact hp0
    have hp11 : locals1.get? "paid1" = some (.int (Int.ofNat paid1.toNat)) := by
      rw [hkeep0 "paid1" (by decide) (by decide) (by decide)]; exact hp1
    obtain ⟨_, _, rdGuard1⟩ := flashSecondGuardX (v := v) rd1
      (by simp only [List.length_cons]; omega)
    rcases flashUpdateX (v := v) locals1 true rdGuard1 hs1 hperm hp11 hcore1.liquidity hcore1.slot0
        hcore1.protocolFees hcore1.growth1 hliquidity hov with
      ⟨rdBad, hbad⟩ | ⟨evm2, σ2, locals2, k2, C2, hs2, hsource1, rd2, hkeep1⟩
    · exact Or.inl ⟨rdBad, ExecBlock.consNormal hsource0 (ExecBlock.consRevert hbad)⟩
    · refine Or.inr ⟨evm2, σ2, locals2, k2, C2, hs2,
        ExecBlock.consNormal hsource0 (ExecBlock.consNormal hsource1 ExecBlock.nil),
        rd2, hcore1.update hkeep1, ?_, ?_⟩
      · rw [hkeep1 "paid0" (by decide) (by decide) (by decide)]; exact hp01
      · rw [hkeep1 "paid1" (by decide) (by decide) (by decide)]; exact hp11

end Benchmarks.UniswapV3.Pool
