import Benchmarks.Dss.Clipper.KickSourceIncentive

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 1000000
set_option linter.unusedTactic false

/-! Source-side completion of the optional `kick` incentive payment. -/

theorem clipperKickLocalsSuckRet_get_locked (evmLock evmTop : EVM.State)
    (I : ExecutionEnv) (feedPrice top : UInt256) :
    (clipperKickLocalsSuckRet evmLock evmTop I feedPrice top).get? "locked" = none := by
  simp [clipperKickLocalsSuckRet, clipperKickLocalsCoin,
    clipperKickLocalsCoinNew, clipperKickLocalsChipCoin,
    clipperKickLocalsCoinZero, clipperKickLocalsChip, clipperKickLocalsTip,
    clipperKickLocalsTop, clipperKickLocalsFeedPrice,
    clipperKickLocalsActivePos, clipperKickLocalsId, clipperKickStore]

theorem clipperKickLocalsSuckRet_get_id (evmLock evmTop : EVM.State)
    (I : ExecutionEnv) (feedPrice top : UInt256) :
    (clipperKickLocalsSuckRet evmLock evmTop I feedPrice top).get? "id" =
      some (.int (Int.ofNat (clipperKickSourceIdWord evmLock).toNat)) := by
  simp only [clipperKickLocalsSuckRet, clipperKickLocalsCoin,
    clipperKickLocalsCoinNew, clipperKickLocalsChipCoin,
    clipperKickLocalsCoinZero, clipperKickLocalsChip, clipperKickLocalsTip,
    clipperKickLocalsTop, clipperKickLocalsFeedPrice,
    clipperKickLocalsActivePos, clipperKickLocalsId]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem clipperKickIncentiveWmulReverts (v : ClipperImmutables)
    (evmLock evmTop : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256)
    (hactive : clipperRedoTipSolmWord evmTop ≠ ⟨0⟩ ∨
      clipperRedoChipSolmWord evmTop ≠ ⟨0⟩)
    (hover : UInt256.size ≤ (clipperKickTabWord I).toNat *
      (clipperRedoChipSolmWord evmTop).toNat) :
    ExecBlock (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top }
      evmTop
      [ .ite clipperKickIncentiveCond (clipperKickIncentiveBody v) [],
        .assign .storage lockedRef (.intLit 0), .return [.var "id"] ]
      .reverted := by
  have hbody : ExecBlock (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top }
      evmTop (clipperKickIncentiveBody v) .reverted := by
    simpa [clipperKickIncentiveBody] using ExecBlock.consRevert
      (clipperKickWmulCallReverts v evmLock evmTop I feedPrice top hover)
  have hite := ExecStmt.iteTrue (elseB := [])
    (clipperEvalKickIncentiveActive v evmLock evmTop evmTop I feedPrice top hactive)
    hbody
  exact ExecBlock.consRevert hite

theorem clipperKickIncentiveAddReverts (v : ClipperImmutables)
    (evmLock evmTop : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256)
    (hactive : clipperRedoTipSolmWord evmTop ≠ ⟨0⟩ ∨
      clipperRedoChipSolmWord evmTop ≠ ⟨0⟩)
    (hmul : (clipperKickTabWord I).toNat *
      (clipperRedoChipSolmWord evmTop).toNat < UInt256.size)
    (hover : UInt256.size ≤ (clipperRedoTipSolmWord evmTop).toNat +
      (clipperKickSourceChipCoinWord evmTop I).toNat) :
    ExecBlock (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top }
      evmTop
      [ .ite clipperKickIncentiveCond (clipperKickIncentiveBody v) [],
        .assign .storage lockedRef (.intLit 0), .return [.var "id"] ]
      .reverted := by
  have hmulStmt :=
    clipperKickWmulCallReturns v evmLock evmTop I feedPrice top hmul
  have hadd :=
    clipperKickCheckedAddCoinReverts v evmLock evmTop I feedPrice top hover
  have hbody : ExecBlock (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top }
      evmTop (clipperKickIncentiveBody v) .reverted := by
    simpa [clipperKickIncentiveBody] using ExecBlock.consNormal hmulStmt
      (execBlock_append_term hadd (by intro frame state h; cases h))
  have hite := ExecStmt.iteTrue (elseB := [])
    (clipperEvalKickIncentiveActive v evmLock evmTop evmTop I feedPrice top hactive)
    hbody
  exact ExecBlock.consRevert hite

theorem clipperKickIncentiveSuckReverts (v : ClipperImmutables)
    (evmLock evmTop : EVM.State) (I : ExecutionEnv) (feedPrice top : UInt256)
    (hactive : clipperRedoTipSolmWord evmTop ≠ ⟨0⟩ ∨
      clipperRedoChipSolmWord evmTop ≠ ⟨0⟩)
    (hmul : (clipperKickTabWord I).toNat *
      (clipperRedoChipSolmWord evmTop).toNat < UInt256.size)
    (hadd : (clipperRedoTipSolmWord evmTop).toNat +
      (clipperKickSourceChipCoinWord evmTop I).toNat < UInt256.size)
    (hsuck : ExecBlock (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoin evmLock evmTop I feedPrice top }
      evmTop (checkedExternalCallStmts (vatExpr v) "suck" (.intLit 0)
        [.storage vowRef, .var "kpr", .var "coin"] "_suckRet") .reverted) :
    ExecBlock (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top }
      evmTop
      [ .ite clipperKickIncentiveCond (clipperKickIncentiveBody v) [],
        .assign .storage lockedRef (.intLit 0), .return [.var "id"] ]
      .reverted := by
  have hmulStmt :=
    clipperKickWmulCallReturns v evmLock evmTop I feedPrice top hmul
  have haddBlock := clipperKickCheckedAddCoin v evmLock evmTop I feedPrice top hadd
  have hcoinStmt := clipperKickAssignCoin v evmLock evmTop I feedPrice top
  have hbody : ExecBlock (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top }
      evmTop (clipperKickIncentiveBody v) .reverted := by
    simpa [clipperKickIncentiveBody] using ExecBlock.consNormal hmulStmt
      (execBlock_append haddBlock
        (ExecBlock.consNormal hcoinStmt hsuck))
  have hite := ExecStmt.iteTrue (elseB := [])
    (clipperEvalKickIncentiveActive v evmLock evmTop evmTop I feedPrice top hactive)
    hbody
  exact ExecBlock.consRevert hite

theorem clipperKickIncentiveSucceeds (v : ClipperImmutables)
    (evmLock evmTop evmAfter : EVM.State) (I : ExecutionEnv)
    (feedPrice top : UInt256)
    (hactive : clipperRedoTipSolmWord evmTop ≠ ⟨0⟩ ∨
      clipperRedoChipSolmWord evmTop ≠ ⟨0⟩)
    (hmul : (clipperKickTabWord I).toNat *
      (clipperRedoChipSolmWord evmTop).toNat < UInt256.size)
    (hadd : (clipperRedoTipSolmWord evmTop).toNat +
      (clipperKickSourceChipCoinWord evmTop I).toNat < UInt256.size)
    (hsuck : ExecBlock (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoin evmLock evmTop I feedPrice top }
      evmTop (checkedExternalCallStmts (vatExpr v) "suck" (.intLit 0)
        [.storage vowRef, .var "kpr", .var "coin"] "_suckRet")
      (.ok (Frame.mk (contract v)
        (clipperKickLocalsSuckRet evmLock evmTop I feedPrice top)) evmAfter)) :
    ExecBlock (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top }
      evmTop
      [ .ite clipperKickIncentiveCond (clipperKickIncentiveBody v) [],
        .assign .storage lockedRef (.intLit 0), .return [.var "id"] ]
      (.returned
        { contract := contract v,
          locals := clipperKickLocalsSuckRet evmLock evmTop I feedPrice top }
        (Solm.EVM.storageStore evmAfter evmAfter.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)
        (some [.int (Int.ofNat (clipperKickSourceIdWord evmLock).toNat)])) := by
  have hmulStmt :=
    clipperKickWmulCallReturns v evmLock evmTop I feedPrice top hmul
  have haddBlock := clipperKickCheckedAddCoin v evmLock evmTop I feedPrice top hadd
  have hcoinStmt := clipperKickAssignCoin v evmLock evmTop I feedPrice top
  have hbody : ExecBlock (config v)
      { contract := contract v,
        locals := clipperKickLocalsCoinZero evmLock evmTop I feedPrice top }
      evmTop (clipperKickIncentiveBody v)
      (.ok (Frame.mk (contract v)
        (clipperKickLocalsSuckRet evmLock evmTop I feedPrice top)) evmAfter) := by
    simpa [clipperKickIncentiveBody] using ExecBlock.consNormal hmulStmt
      (execBlock_append haddBlock
        (ExecBlock.consNormal hcoinStmt hsuck))
  have hite := ExecStmt.iteTrue (elseB := [])
    (clipperEvalKickIncentiveActive v evmLock evmTop evmTop I feedPrice top hactive)
    hbody
  have htail := clipperKickUnlockReturn v evmLock evmTop evmAfter I feedPrice top
    (clipperKickLocalsSuckRet evmLock evmTop I feedPrice top)
    (clipperKickLocalsSuckRet_get_locked evmLock evmTop I feedPrice top)
    (clipperKickLocalsSuckRet_get_id evmLock evmTop I feedPrice top)
  exact ExecBlock.consNormal hite htail

end Benchmarks.Dss.Clipper
