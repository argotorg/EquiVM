import Benchmarks.UniswapV3.Pool.FlashUpdateSource
import Benchmarks.UniswapV3.Pool.FlashGrowthTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem flashUpdateX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat}
    {aw paid1 paid0 after1 after0 before1 before0 fee1 fee0 liquidity : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (locals : Store) (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0
      (if (if second then paid1 else paid0) = ⟨0⟩ then flashUpdateExit second
        else flashProtocolEntry second)
      (flashUpdateRest paid1 paid0 after1 after0 before1 before0 fee1 fee0 liquidity R)
      mem aw rdata σ k C) (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hp : locals.get? (flashPaidName second) =
      some (.int (Int.ofNat (if second then paid1 else paid0).toNat)))
    (hl : locals.get? "_liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hslot : locals.get? "slot0" = none) (hfees : locals.get? "protocolFees" = none)
    (hbase : locals.get? (feeGrowthName second) = none)
    (hliquidity : liquidity.toNat < 2 ^ 128) (hov : R.length + 27 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
        (flashUpdateStmt second) .reverted) ∨
    ∃ evm' σ' locals' k' C', SourceState s0 ee σ' evm' ∧
      ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
        (flashUpdateStmt second)
        (.ok {contract := contract, locals := locals', immutables := immStore v} evm') ∧
      RD (deployedRuntime v) ee g s0 (flashUpdateExit second)
        (flashUpdateRest paid1 paid0 after1 after0 before1 before0 fee1 fee0 liquidity R)
        mem aw rdata σ' k' C' ∧ FlashUpdatePreserves second locals locals' := by
  by_cases hz : (if second then paid1 else paid0) = ⟨0⟩
  · rw [if_pos hz] at rd
    refine Or.inr ⟨evm, σ, locals, k, C, hs, ?_, rd, flashUpdatePreserves_refl second locals⟩
    exact flashUpdateSkip locals (immStore v) evm second (by simpa only [hz] using hp)
  · rw [if_neg hz] at rd
    obtain ⟨hsFees, hsourceFees, kFees, CFees, rdFees⟩ :=
      flashProtocolX (v := v) locals second rd hs hperm hp hslot hfees
        (by simp only [List.length_cons]; omega)
    let paid := if second then paid1 else paid0
    let divisor := poolProtocolDivisor second σ ee
    let fees := poolProtocolFees paid divisor
    let frame := flashProtocolFrame locals (immStore v) second paid divisor
    have hp' : frame.locals.get? (flashPaidName second) = some (.int (Int.ofNat paid.toNat)) := by
      cases second <;>
        simpa [frame, flashProtocolFrame, flashProtocolFeesName, flashProtocolName,
          flashPaidName, paid, Std.HashMap.getElem?_insert] using hp
    have hf' : frame.locals.get? (flashProtocolFeesName second) =
        some (.int (Int.ofNat fees.toNat)) := by simp [frame, flashProtocolFrame, fees]
    have hl' : frame.locals.get? "_liquidity" = some (.int (Int.ofNat liquidity.toNat)) := by
      cases second <;>
        simpa [frame, flashProtocolFrame, flashProtocolFeesName, flashProtocolName,
          Std.HashMap.getElem?_insert] using hl
    have hb' : frame.locals.get? (feeGrowthName second) = none := by
      cases second <;>
        simpa [frame, flashProtocolFrame, flashProtocolFeesName, flashProtocolName,
          feeGrowthName, Std.HashMap.getElem?_insert] using hbase
    have hguard : evalExpr? config {contract := contract, locals := locals, immutables := immStore v}
        evm (.binary .gt (.var (flashPaidName second)) (.intLit 0)) = .ok (.bool true) := by
      have hpos : 0 < paid.toNat := Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h))
      simpa only [hpos, decide_true] using evalFlashUpdateGuard locals (immStore v) evm second paid hp
    rcases flashGrowthX (v := v) frame.locals second rdFees hsFees hperm hp' hf' hl' hb'
        hliquidity hov with ⟨rdBad, hbad⟩ | ⟨hsDone, hsourceDone, kDone, CDone, rdDone⟩
    · exact Or.inl ⟨rdBad, ExecStmt.iteTrue hguard (execBlock_append_ok hsourceFees hbad)⟩
    · refine Or.inr ⟨_, _, _, kDone, CDone, hsDone,
        ExecStmt.iteTrue hguard (execBlock_append_ok hsourceFees hsourceDone), rdDone, ?_⟩
      exact flashUpdatePreserves_frames locals (immStore v) second paid divisor liquidity

end Benchmarks.UniswapV3.Pool
