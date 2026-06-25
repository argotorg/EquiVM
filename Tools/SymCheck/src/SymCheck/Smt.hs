{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module SymCheck.Smt
  ( SmtQueryPolicy(..)
  , defaultSmtQueryPolicy
  , SmtQueryOutcome(..)
  , BranchQueryOutcome(..)
  , checkSatWithPolicy
  , checkBranchWithPolicy
  ) where

import Control.Monad (when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (ReaderT)
import Control.Monad.Trans.State.Strict qualified as State
import Data.Monoid (Any(..))
import Data.Text qualified as T
import EVM.Effects qualified as Effects
import EVM.Solvers qualified as Solvers
import EVM.Traversals (foldTerm, mapExprM)
import EVM.Types
import System.IO (hPutStrLn, stderr)

data SmtQueryPolicy = SmtQueryPolicy
  { allowWeakening :: Bool
  , notifyWeakening :: Bool
  } deriving (Eq, Show)

defaultSmtQueryPolicy :: SmtQueryPolicy
defaultSmtQueryPolicy =
  SmtQueryPolicy
    { allowWeakening = True
    , notifyWeakening = True
    }

data SmtQueryOutcome = SmtQueryOutcome
  { smtResult :: SMTResult
  , weakened :: Bool
  } deriving (Eq, Show)

data BranchQueryOutcome = BranchQueryOutcome
  { branchCondition :: BranchCondition
  , usedWeakening :: Bool
  } deriving (Show)

checkSatWithPolicy
  :: SmtQueryPolicy
  -> Solvers.SolverGroup
  -> String
  -> [Prop]
  -> ReaderT Effects.Env IO SmtQueryOutcome
checkSatWithPolicy policy solverGroup label props = do
  exact <- Solvers.checkSatWithProps solverGroup props
  if not policy.allowWeakening || not (containsUnsupportedSmtTerms props) || isDecisive exact
    then pure SmtQueryOutcome {smtResult = exact, weakened = False}
    else do
      let weakenedProps = weakenProps props
      when policy.notifyWeakening $
        liftIO $
          hPutStrLn stderr $
            "note: weakened SMT query for "
              <> label
              <> " because symbolic-size CopySlice is not SMT-encodable"
      weakenedResult <- Solvers.checkSatWithProps solverGroup weakenedProps
      pure SmtQueryOutcome {smtResult = weakenedResult, weakened = True}

checkBranchWithPolicy
  :: SmtQueryPolicy
  -> Solvers.SolverGroup
  -> Prop
  -> Prop
  -> ReaderT Effects.Env IO BranchQueryOutcome
checkBranchWithPolicy policy solverGroup branchcondition pathconditions = do
  let props = [pathconditions .&& branchcondition]
  condOutcome <- checkSatWithPolicy policy solverGroup "branch feasibility" props
  case condOutcome.smtResult of
    Qed ->
      pure $ BranchQueryOutcome (Case False) condOutcome.weakened
    Cex {} -> checkNegated condOutcome.weakened
    Unknown {} ->
      if condOutcome.weakened
        then checkNegated True
        else pure (BranchQueryOutcome UnknownBranch False)
    Error {} ->
      if condOutcome.weakened
        then checkNegated True
        else pure (BranchQueryOutcome UnknownBranch False)
  where
    checkNegated usedWeakeningOnCond = do
      let propsNeg = [pathconditions .&& PNeg branchcondition]
      negOutcome <- checkSatWithPolicy policy solverGroup "branch negation" propsNeg
      case negOutcome.smtResult of
        Qed -> pure $ BranchQueryOutcome (Case True) (usedWeakeningOnCond || negOutcome.weakened)
        _ ->
          pure $
            BranchQueryOutcome
              UnknownBranch
              (usedWeakeningOnCond || negOutcome.weakened)

isDecisive :: SMTResult -> Bool
isDecisive = \case
  Qed -> True
  Cex {} -> True
  Unknown {} -> False
  Error {} -> False

containsUnsupportedSmtTerms :: [Prop] -> Bool
containsUnsupportedSmtTerms =
  getAny . foldMap (foldTerm unsupportedExpr mempty)
  where
    unsupportedExpr :: Expr a -> Any
    unsupportedExpr = \case
      CopySlice _ _ size _ _ | not (isLiteralWord size) -> Any True
      _ -> Any False

weakenProps :: [Prop] -> [Prop]
weakenProps props =
  fst (State.runState (traverse weakenProp props) 0)

weakenProp :: Prop -> State.State Int Prop
weakenProp = \case
  PBool value0 -> pure (PBool value0)
  PEq lhs rhs -> PEq <$> weakenExpr lhs <*> weakenExpr rhs
  PLT lhs rhs -> PLT <$> weakenExpr lhs <*> weakenExpr rhs
  PGT lhs rhs -> PGT <$> weakenExpr lhs <*> weakenExpr rhs
  PLEq lhs rhs -> PLEq <$> weakenExpr lhs <*> weakenExpr rhs
  PGEq lhs rhs -> PGEq <$> weakenExpr lhs <*> weakenExpr rhs
  PNeg prop -> PNeg <$> weakenProp prop
  PAnd lhs rhs -> PAnd <$> weakenProp lhs <*> weakenProp rhs
  POr lhs rhs -> POr <$> weakenProp lhs <*> weakenProp rhs
  PImpl lhs rhs -> PImpl <$> weakenProp lhs <*> weakenProp rhs

weakenExpr :: Expr a -> State.State Int (Expr a)
weakenExpr = mapExprM $ \case
  CopySlice _ _ size _ _
    | not (isLiteralWord size) -> do
        n <- State.get
        State.put (n + 1)
        pure (AbstractBuf (T.pack ("smt_weakened_buf_" <> show n)))
  expr -> pure expr

isLiteralWord :: Expr EWord -> Bool
isLiteralWord = \case
  Lit _ -> True
  _ -> False
