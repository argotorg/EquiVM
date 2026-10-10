import Benchmarks.CompoundIII.Comet.AbsorbTrace
import Benchmarks.CompoundIII.Comet.AbsorbBeforePointsSource
import Benchmarks.CompoundIII.Comet.AbsorbAfterAccountsSource
import Benchmarks.CompoundIII.Comet.InternalBlockComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def absorbBody : List Stmt := absorbBeforePointsBlock ++ absorbAfterAccountsBlock

theorem absorbTransition_body : absorbTransition.body = calldataPrologue absorbBody := rfl

theorem absorb_source {v cd addr evm result} (ht : AbsorbTrace v cd addr evm result)
    {accounts : List Value} {endOffset : Nat}
    (hread : Solc0815.decodeAddressArrayElems? (absorbArrayLength cd) (cd.toList.drop 4)
      (absorbArrayOffset cd + 32) = some (accounts, endOffset))
    (hlen : accounts.length = absorbArrayLength cd) (hn : absorbArrayLength cd < 2^64)
    (frame : Frame) (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (ha : frame.locals.get? "absorber" = some (.address addr))
    (hac : frame.locals.get? "accounts" = some (.array accounts))
    (hp : frame.locals.get? "liquidatorPoints" = none) :
    internalBlockResult config frame evm absorbBody result := by
  have hnword : (UInt256.ofNat (absorbArrayLength cd)).toNat = absorbArrayLength cd :=
    UInt256.toNat_ofNat_of_lt (lt_trans hn (by decide))
  cases ht with
  | reverted ht =>
    have hb := absorbBeforePoints_source ht addr ⟨0⟩ hread hlen hn frame hc hi ha hac hp
    exact execBlock_append_term hb (by intro _ _ he; cases he)
  | staticViolation ht =>
    have hb := absorbBeforePoints_source ht addr ⟨0⟩ hread hlen hn frame hc hi ha hac hp
    exact execBlock_append_term hb (by intro _ _ he; cases he)
  | @finished evm' startGas endGas ht =>
    obtain ⟨f1, hb, hf⟩ := absorbBeforePoints_source ht addr startGas hread hlen hn
      frame hc hi ha hac hp
    exact (absorbAfterAccounts_source f1 evm' addr (UInt256.ofNat (absorbArrayLength cd))
      startGas endGas accounts hf.contract hf.absorber hf.accounts hf.gas hf.points
      (by rw [hnword]; exact hlen) (by rw [hnword]; exact hn)).prependBlock hb

theorem absorbPublic_source {v cd evm result}
    (ht : AbsorbTrace v cd (AccountAddress.ofNat (calldataWord cd 4).toNat) evm result)
    {accounts : List Value} {endOffset : Nat}
    (hread : Solc0815.decodeAddressArrayElems? (absorbArrayLength cd) (cd.toList.drop 4)
      (absorbArrayOffset cd + 32) = some (accounts, endOffset))
    (hlen : accounts.length = absorbArrayLength cd) (hn : absorbArrayLength cd < 2^64)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < 2^255 + 4) :
    internalSourceResult config
      { contract := contract, locals := absorbCalldataArgs cd accounts, immutables := immStore v }
      evm absorbTransition.body result := by
  rw [absorbTransition_body]
  let frame := calldataLocalFrame
    { contract := contract, locals := absorbCalldataArgs cd accounts, immutables := immStore v } evm
  have ha : frame.locals.get? "absorber" = some (.address (AccountAddress.ofNat (calldataWord cd 4).toNat)) := by
    simp only [frame, calldataLocalFrame, absorbCalldataArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
    rfl
  have hac : frame.locals.get? "accounts" = some (.array accounts) := by
    simp only [frame, calldataLocalFrame, absorbCalldataArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
    rfl
  have hp : frame.locals.get? "liquidatorPoints" = none := by
    simp [frame, calldataLocalFrame, absorbCalldataArgs]
  have hb := absorb_source ht hread hlen hn frame rfl rfl ha hac hp
  cases result with
  | ok evm' =>
    obtain ⟨final, hb⟩ := hb
    exact ⟨final, ExecFuncBody.execBlockOK ((calldataPrologue_ok hv hhi).run hb)⟩
  | reverted => exact ExecFuncBody.execBlockRevert ((calldataPrologue_ok hv hhi).run hb)
  | staticViolation => exact ExecFuncBody.execBlockStatic ((calldataPrologue_ok hv hhi).run hb)

end Benchmarks.CompoundIII.Comet
