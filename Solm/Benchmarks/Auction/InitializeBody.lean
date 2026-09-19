import Solm.Benchmarks.Auction.InitializeSourceStores

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

def initializePrefixStatements : List Stmt :=
  [nonpayable,
    .require (.binary .or (.storage initializingRef) (.unary .not (.storage initializedRef))),
    .letDecl "isTopLevelCall" (some boolTy) (.unary .not (.storage initializingRef)),
    .ite (.var "isTopLevelCall")
      [.assign .storage initializingRef (.boolLit true),
        .assign .storage initializedRef (.boolLit true)] []]

theorem initializePrefixSource (evm : EVM.State) (args : InitializeArgs)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hg : initializingWord evm.accountMap evm.executionEnv ≠ ⟨0⟩ ∨
      initializedWord evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecBlock auctionConfig { contract := auctionContract, locals := args.locals } evm
      initializePrefixStatements
      (.ok { contract := auctionContract, locals := args.bodyLocals (initializeTop evm) }
        (initializerEnteredState evm)) := by
  apply ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
  apply ExecBlock.consNormal (ExecStmt.requireTrue
    (evalInitializerGuardTrue evm args.locals
      (by simp [InitializeArgs.locals]) (by simp [InitializeArgs.locals]) hg))
  apply ExecBlock.consNormal (ExecStmt.letDecl
    (readNotInitializing evm args.locals (by simp [InitializeArgs.locals])))
  exact ExecBlock.consNormal
    (initializerBeginSource evm (args.bodyLocals (initializeTop evm))
      (by simp [InitializeArgs.bodyLocals, InitializeArgs.locals])
      (by simp [InitializeArgs.bodyLocals, InitializeArgs.locals])
      (by simp [InitializeArgs.bodyLocals])) ExecBlock.nil

theorem initializeBody (evm : EVM.State) (args : InitializeArgs)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hc : args.canonical)
    (hg : initializingWord evm.accountMap evm.executionEnv ≠ ⟨0⟩ ∨
      initializedWord evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm args.locals initializeTransition.body
      (.returned { contract := auctionContract, locals := args.bodyLocals (initializeTop evm) }
        (initializeFinalState args evm) none) := by
  have hp := initializePrefixSource evm args hwv hg
  generalize hE : initializerEnteredState evm = evmE at hp
  have hs := initializeSetupSource evmE (args.bodyLocals (initializeTop evm))
    (by simp [InitializeArgs.bodyLocals, InitializeArgs.locals])
    (by simp [InitializeArgs.bodyLocals, InitializeArgs.locals])
    (by simp [InitializeArgs.bodyLocals, InitializeArgs.locals])
  generalize hB : initializerOwnerState (initializerStatusState (initializerPauseState evmE)) =
    evmB at hs
  have hBfull : initializeBaseState evm = evmB := by
    rw [initializeBaseState, hE, hB]
  have henvB : evmB.executionEnv = evm.executionEnv := by
    rw [← hBfull]; exact initializeBaseState_env evm
  have hBp : pausedWord evmB.accountMap evmB.executionEnv = ⟨0⟩ := by
    have heq := initializeBaseState_accounts (σ := evm.accountMap) (evm := evm)
      (accountMapEquiv.refl _)
    rw [hBfull] at heq
    rw [henvB, ← pausedWord_equiv heq]
    exact initializeBaseMap_unpaused _ _
  have hpa := pauseBlock evmB (args.bodyLocals (initializeTop evm))
    (by simp [InitializeArgs.bodyLocals, InitializeArgs.locals]) hBp
  generalize hP : Solm.EVM.storageStore evmB evmB.executionEnv.codeOwner ⟨51⟩
    (pauseWord (Solm.EVM.storageLoad evmB evmB.executionEnv.codeOwner ⟨51⟩)) = evmP at hpa
  have hPfull : initializePausedState evm = evmP := by
    rw [initializePausedState, hBfull]; exact hP
  have ha := initializeParamsSource evmP args (initializeTop evm) hc
  generalize hA : args.storeState evmP = evmA at ha
  have he := initializerExitSource evmA (args.bodyLocals (initializeTop evm)) (initializeTop evm)
    (by simp [InitializeArgs.bodyLocals, InitializeArgs.locals])
    (by simp [InitializeArgs.bodyLocals])
  rw [initializeFinalState, hPfull, hA]
  exact ExecFuncBody.execBlockOK
    (execBlock_append hp (execBlock_append hs (execBlock_append hpa (execBlock_append ha he))))

theorem initializeBodyReverts (evm : EVM.State) (args : InitializeArgs)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hi : initializingWord evm.accountMap evm.executionEnv = ⟨0⟩)
    (hz : initializedWord evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm args.locals initializeTransition.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact nonpayableSecondRequireReverts hwv
    (evalInitializerGuardFalse evm args.locals
      (by simp [InitializeArgs.locals]) (by simp [InitializeArgs.locals]) hi hz)

end Auction
