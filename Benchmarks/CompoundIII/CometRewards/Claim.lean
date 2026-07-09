import Benchmarks.CompoundIII.CometRewards.Common
import Benchmarks.CompoundIII.CometRewards.GetRewardOwed
import Benchmarks.CompoundIII.CometRewards.WithdrawToken

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.CompoundIII.CometRewards

end Benchmarks.CompoundIII.CometRewards

theorem Reasoning.Reach.swap9_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP9, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
    (hov : t.length + 10 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
       else .ok (stSwap s (jj :: b :: c :: d :: e :: f :: gg :: hh :: ii :: a :: t),
        .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP9, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap9 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t).length - 10
        + 10 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem Reasoning.Reach.RD.swap9
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP9, .none)) (hov : t.length + 10 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (jj :: b :: c :: d :: e :: f :: gg :: hh :: ii :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => Reasoning.Reach.swap9_xstep hc hp hdec hs hov)

namespace Benchmarks.CompoundIII.CometRewards

/-! ## `claim(address,address,bool)` ABI setup -/

abbrev claimCometWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev claimSrcWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev claimShouldAccrueWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev claimCometValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (claimCometWord I).toNat)

abbrev claimSrcValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (claimSrcWord I).toNat)

abbrev claimShouldAccrueValue (I : ExecutionEnv) : Value :=
  wordToElem .bool (claimShouldAccrueWord I)

abbrev claimStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "comet" (claimCometValue I)).insert "src"
    (claimSrcValue I)).insert "shouldAccrue" (claimShouldAccrueValue I)

abbrev claimFrame (evm : EVM.State) (I : ExecutionEnv) : Frame :=
  { contract := contract,
    locals := (claimStore I).insert "__calldata" (.bytes evm.executionEnv.calldata) }

abbrev claimArgs (I : ExecutionEnv) : List Value :=
  [claimCometValue I, claimSrcValue I, claimShouldAccrueValue I]

abbrev claimInternalArgs (I : ExecutionEnv) : List Value :=
  [claimCometValue I, claimSrcValue I, claimSrcValue I, claimShouldAccrueValue I]

abbrev claimInternalStore (I : ExecutionEnv) : Store :=
  ((((∅ : Store).insert "shouldAccrue" (claimShouldAccrueValue I)).insert "to"
    (claimSrcValue I)).insert "src" (claimSrcValue I)).insert "comet" (claimCometValue I)

abbrev claimInternalAfterTokenLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (claimInternalStore I).insert "token"
    (getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I))

abbrev claimInternalAfterRescaleLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (claimInternalAfterTokenLocals evm I).insert "rescaleFactor"
    (getRewardOwedRescaleValueFromSlot0 (getRewardOwedSlot0Load evm I))

abbrev claimInternalAfterShouldLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (claimInternalAfterRescaleLocals evm I).insert "shouldUpscale"
    (getRewardOwedShouldUpscaleValueFromSlot0 (getRewardOwedSlot0Load evm I))

abbrev claimInternalConfigLocals (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (claimInternalAfterShouldLocals evm I).insert "multiplier"
    (getRewardOwedMultiplierValue (getRewardOwedMultiplierLoad evm I))

abbrev claimInternalAfterClaimedLocals
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) : Store :=
  (claimInternalConfigLocals evm I).insert "claimed"
    (.int (Int.ofNat (getRewardOwedClaimedLoad evmClaimed I).toNat))

abbrev claimInternalAfterInternalLocals
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) : Store :=
  (claimInternalAfterClaimedLocals evm evmClaimed I).insert "accrued"
    (.int (Int.ofNat accruedNat))

abbrev claimInternalOwedNat (evmClaimed : EVM.State) (I : ExecutionEnv)
    (accruedNat : ℕ) : ℕ :=
  accruedNat - (getRewardOwedClaimedLoad evmClaimed I).toNat

abbrev claimInternalAfterOwedLocals
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) : Store :=
  (claimInternalAfterInternalLocals evm evmClaimed I accruedNat).insert "owed"
    (.int (Int.ofNat (claimInternalOwedNat evmClaimed I accruedNat)))

abbrev claimTransferTarget (slot0 : UInt256) : AccountAddress :=
  AccountAddress.ofNat (rewardConfigTokenFromSlot0 slot0).toNat

abbrev claimTransferArgs (I : ExecutionEnv) (amount : UInt256) : List Value :=
  [claimSrcValue I, .int (Int.ofNat amount.toNat)]

abbrev claimDoTransferOutStore
    (I : ExecutionEnv) (slot0 amount : UInt256) : Store :=
  (((∅ : Store).insert "amount" (.int (Int.ofNat amount.toNat))).insert "to"
    (claimSrcValue I)).insert "token" (getRewardOwedTokenValueFromSlot0 slot0)

abbrev claimTransferCallStore (I : ExecutionEnv) (slot0 amount : UInt256)
    (success : Bool) : Store :=
  (claimDoTransferOutStore I slot0 amount).insert "success" (.bool success)

theorem claimStore_comet (I : ExecutionEnv) :
    (claimStore I).get? "comet" = some (claimCometValue I) := by
  rw [claimStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem claimStore_src (I : ExecutionEnv) :
    (claimStore I).get? "src" = some (claimSrcValue I) := by
  rw [claimStore, store_get_ne _ _ (by decide), store_get_self]

theorem claimStore_shouldAccrue (I : ExecutionEnv) :
    (claimStore I).get? "shouldAccrue" = some (claimShouldAccrueValue I) := by
  rw [claimStore, store_get_self]

theorem claimFrame_comet (evm : EVM.State) (I : ExecutionEnv) :
    (claimFrame evm I).locals.get? "comet" = some (claimCometValue I) := by
  rw [claimFrame]
  rw [store_get_ne _ _ (by decide), claimStore_comet]

theorem claimFrame_src (evm : EVM.State) (I : ExecutionEnv) :
    (claimFrame evm I).locals.get? "src" = some (claimSrcValue I) := by
  rw [claimFrame]
  rw [store_get_ne _ _ (by decide), claimStore_src]

theorem claimFrame_shouldAccrue (evm : EVM.State) (I : ExecutionEnv) :
    (claimFrame evm I).locals.get? "shouldAccrue" = some (claimShouldAccrueValue I) := by
  rw [claimFrame]
  rw [store_get_ne _ _ (by decide), claimStore_shouldAccrue]

theorem evalExpr_claim_comet_of {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (hcomet : locals.get? "comet" = some (claimCometValue I)) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "comet") =
      .ok (claimCometValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [hcomet]

theorem evalExpr_claim_src_of {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : locals.get? "src" = some (claimSrcValue I)) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "src") =
      .ok (claimSrcValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [hsrc]

theorem evalExpr_claim_shouldAccrue_of {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hshould : locals.get? "shouldAccrue" = some (claimShouldAccrueValue I)) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "shouldAccrue") =
      .ok (claimShouldAccrueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [hshould]

theorem evalExprs_claim_internalArgs_frame (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config (claimFrame evm I) evm
      [.var "comet", .var "src", .var "src", .var "shouldAccrue"] =
        .ok (claimInternalArgs I) := by
  simp only [claimInternalArgs, evalExprs?, evalExpr_claim_comet_of evm I
    (claimFrame_comet evm I), evalExpr_claim_src_of evm I (claimFrame_src evm I),
    evalExpr_claim_shouldAccrue_of evm I (claimFrame_shouldAccrue evm I),
    EvalResult.bind, bind]
  rfl

theorem bindParams_claimInternal (I : ExecutionEnv) :
    bindParams? claimInternalFunction.params (claimInternalArgs I) =
      some (claimInternalStore I) := by
  simp [claimInternalFunction, claimInternalArgs, claimCometValue, claimSrcValue,
    claimShouldAccrueValue, claimInternalStore, bindParams?]

theorem lookupCallable_claimInternal :
    lookupCallable? contract "claimInternal" = some claimInternalFunction.toCallable := by
  rfl

theorem claimInternalStore_comet (I : ExecutionEnv) :
    (claimInternalStore I).get? "comet" = some (claimCometValue I) := by
  rw [claimInternalStore, store_get_self]

theorem claimInternalStore_src (I : ExecutionEnv) :
    (claimInternalStore I).get? "src" = some (claimSrcValue I) := by
  rw [claimInternalStore, store_get_ne _ _ (by decide), store_get_self]

theorem claimInternalStore_shouldAccrue (I : ExecutionEnv) :
    (claimInternalStore I).get? "shouldAccrue" = some (claimShouldAccrueValue I) := by
  rw [claimInternalStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem claimInternalStore_no_rewardConfig (I : ExecutionEnv) :
    (claimInternalStore I).get? "rewardConfig" = none := by
  rw [claimInternalStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem claimInternalAfterTokenLocals_comet (evm : EVM.State) (I : ExecutionEnv) :
    (claimInternalAfterTokenLocals evm I).get? "comet" = some (claimCometValue I) := by
  rw [claimInternalAfterTokenLocals, store_get_ne _ _ (by decide),
    claimInternalStore_comet]

theorem claimInternalAfterTokenLocals_no_rewardConfig
    (evm : EVM.State) (I : ExecutionEnv) :
    (claimInternalAfterTokenLocals evm I).get? "rewardConfig" = none := by
  rw [claimInternalAfterTokenLocals, store_get_ne _ _ (by decide),
    claimInternalStore_no_rewardConfig]

theorem claimInternalAfterRescaleLocals_comet (evm : EVM.State) (I : ExecutionEnv) :
    (claimInternalAfterRescaleLocals evm I).get? "comet" = some (claimCometValue I) := by
  rw [claimInternalAfterRescaleLocals, store_get_ne _ _ (by decide),
    claimInternalAfterTokenLocals_comet]

theorem claimInternalAfterRescaleLocals_no_rewardConfig
    (evm : EVM.State) (I : ExecutionEnv) :
    (claimInternalAfterRescaleLocals evm I).get? "rewardConfig" = none := by
  rw [claimInternalAfterRescaleLocals, store_get_ne _ _ (by decide),
    claimInternalAfterTokenLocals_no_rewardConfig]

theorem claimInternalAfterShouldLocals_comet (evm : EVM.State) (I : ExecutionEnv) :
    (claimInternalAfterShouldLocals evm I).get? "comet" = some (claimCometValue I) := by
  rw [claimInternalAfterShouldLocals, store_get_ne _ _ (by decide),
    claimInternalAfterRescaleLocals_comet]

theorem claimInternalAfterShouldLocals_no_rewardConfig
    (evm : EVM.State) (I : ExecutionEnv) :
    (claimInternalAfterShouldLocals evm I).get? "rewardConfig" = none := by
  rw [claimInternalAfterShouldLocals, store_get_ne _ _ (by decide),
    claimInternalAfterRescaleLocals_no_rewardConfig]

theorem claimInternalConfigLocals_token (evm : EVM.State) (I : ExecutionEnv) :
    (claimInternalConfigLocals evm I).get? "token" =
      some (getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I)) := by
  rw [claimInternalConfigLocals, store_get_ne _ _ (by decide),
    claimInternalAfterShouldLocals, store_get_ne _ _ (by decide),
    claimInternalAfterRescaleLocals, store_get_ne _ _ (by decide),
    claimInternalAfterTokenLocals, store_get_self]

theorem claimInternalConfigLocals_comet (evm : EVM.State) (I : ExecutionEnv) :
    (claimInternalConfigLocals evm I).get? "comet" = some (claimCometValue I) := by
  rw [claimInternalConfigLocals, store_get_ne _ _ (by decide),
    claimInternalAfterShouldLocals_comet]

theorem claimInternalConfigLocals_src (evm : EVM.State) (I : ExecutionEnv) :
    (claimInternalConfigLocals evm I).get? "src" = some (claimSrcValue I) := by
  rw [claimInternalConfigLocals, claimInternalAfterShouldLocals,
    claimInternalAfterRescaleLocals, claimInternalAfterTokenLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  exact claimInternalStore_src I

theorem claimInternalConfigLocals_rescaleFactor (evm : EVM.State) (I : ExecutionEnv) :
    (claimInternalConfigLocals evm I).get? "rescaleFactor" =
      some (getRewardOwedRescaleValueFromSlot0 (getRewardOwedSlot0Load evm I)) := by
  rw [claimInternalConfigLocals, claimInternalAfterShouldLocals,
    claimInternalAfterRescaleLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem claimInternalConfigLocals_shouldUpscale (evm : EVM.State) (I : ExecutionEnv) :
    (claimInternalConfigLocals evm I).get? "shouldUpscale" =
      some (getRewardOwedShouldUpscaleValueFromSlot0 (getRewardOwedSlot0Load evm I)) := by
  rw [claimInternalConfigLocals, claimInternalAfterShouldLocals]
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem claimInternalConfigLocals_multiplier (evm : EVM.State) (I : ExecutionEnv) :
    (claimInternalConfigLocals evm I).get? "multiplier" =
      some (getRewardOwedMultiplierValue (getRewardOwedMultiplierLoad evm I)) := by
  rw [claimInternalConfigLocals, store_get_self]

theorem claimInternalConfigLocals_shouldAccrue (evm : EVM.State) (I : ExecutionEnv) :
    (claimInternalConfigLocals evm I).get? "shouldAccrue" =
      some (claimShouldAccrueValue I) := by
  rw [claimInternalConfigLocals, claimInternalAfterShouldLocals,
    claimInternalAfterRescaleLocals, claimInternalAfterTokenLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  exact claimInternalStore_shouldAccrue I

theorem claimInternalConfigLocals_no_rewardsClaimed (evm : EVM.State) (I : ExecutionEnv) :
    (claimInternalConfigLocals evm I).get? "rewardsClaimed" = none := by
  rw [claimInternalConfigLocals, claimInternalAfterShouldLocals,
    claimInternalAfterRescaleLocals, claimInternalAfterTokenLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  rw [claimInternalStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem claimInternalAfterClaimedLocals_comet
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) :
    (claimInternalAfterClaimedLocals evm evmClaimed I).get? "comet" =
      some (claimCometValue I) := by
  rw [claimInternalAfterClaimedLocals, store_get_ne _ _ (by decide),
    claimInternalConfigLocals_comet]

theorem claimInternalAfterClaimedLocals_src
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) :
    (claimInternalAfterClaimedLocals evm evmClaimed I).get? "src" =
      some (claimSrcValue I) := by
  rw [claimInternalAfterClaimedLocals, store_get_ne _ _ (by decide),
    claimInternalConfigLocals_src]

theorem claimInternalAfterClaimedLocals_rescaleFactor
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) :
    (claimInternalAfterClaimedLocals evm evmClaimed I).get? "rescaleFactor" =
      some (getRewardOwedRescaleValueFromSlot0 (getRewardOwedSlot0Load evm I)) := by
  rw [claimInternalAfterClaimedLocals, store_get_ne _ _ (by decide),
    claimInternalConfigLocals_rescaleFactor]

theorem claimInternalAfterClaimedLocals_shouldUpscale
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) :
    (claimInternalAfterClaimedLocals evm evmClaimed I).get? "shouldUpscale" =
      some (getRewardOwedShouldUpscaleValueFromSlot0 (getRewardOwedSlot0Load evm I)) := by
  rw [claimInternalAfterClaimedLocals, store_get_ne _ _ (by decide),
    claimInternalConfigLocals_shouldUpscale]

theorem claimInternalAfterClaimedLocals_multiplier
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) :
    (claimInternalAfterClaimedLocals evm evmClaimed I).get? "multiplier" =
      some (getRewardOwedMultiplierValue (getRewardOwedMultiplierLoad evm I)) := by
  rw [claimInternalAfterClaimedLocals, store_get_ne _ _ (by decide),
    claimInternalConfigLocals_multiplier]

theorem claimInternalAfterInternalLocals_accrued
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    (claimInternalAfterInternalLocals evm evmClaimed I accruedNat).get? "accrued" =
      some (.int (Int.ofNat accruedNat)) := by
  rw [claimInternalAfterInternalLocals, store_get_self]

theorem claimInternalAfterInternalLocals_claimed
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    (claimInternalAfterInternalLocals evm evmClaimed I accruedNat).get? "claimed" =
      some (.int (Int.ofNat (getRewardOwedClaimedLoad evmClaimed I).toNat)) := by
  rw [claimInternalAfterInternalLocals, store_get_ne _ _ (by decide)]
  rw [claimInternalAfterClaimedLocals, store_get_self]

theorem claimInternalAfterInternalLocals_comet
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    (claimInternalAfterInternalLocals evm evmClaimed I accruedNat).get? "comet" =
      some (claimCometValue I) := by
  rw [claimInternalAfterInternalLocals, store_get_ne _ _ (by decide),
    claimInternalAfterClaimedLocals_comet]

theorem claimInternalAfterInternalLocals_src
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    (claimInternalAfterInternalLocals evm evmClaimed I accruedNat).get? "src" =
      some (claimSrcValue I) := by
  rw [claimInternalAfterInternalLocals, store_get_ne _ _ (by decide),
    claimInternalAfterClaimedLocals_src]

theorem claimInternalAfterInternalLocals_token
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    (claimInternalAfterInternalLocals evm evmClaimed I accruedNat).get? "token" =
      some (getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I)) := by
  rw [claimInternalAfterInternalLocals, store_get_ne _ _ (by decide)]
  rw [claimInternalAfterClaimedLocals, store_get_ne _ _ (by decide),
    claimInternalConfigLocals_token]

theorem claimInternalAfterInternalLocals_no_rewardsClaimed
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    (claimInternalAfterInternalLocals evm evmClaimed I accruedNat).get? "rewardsClaimed" =
      none := by
  rw [claimInternalAfterInternalLocals, store_get_ne _ _ (by decide)]
  rw [claimInternalAfterClaimedLocals, store_get_ne _ _ (by decide),
    claimInternalConfigLocals_no_rewardsClaimed]

theorem claimInternalAfterOwedLocals_token
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    (claimInternalAfterOwedLocals evm evmClaimed I accruedNat).get? "token" =
      some (getRewardOwedTokenValueFromSlot0 (getRewardOwedSlot0Load evm I)) := by
  rw [claimInternalAfterOwedLocals, store_get_ne _ _ (by decide),
    claimInternalAfterInternalLocals_token]

theorem claimInternalAfterOwedLocals_to
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    (claimInternalAfterOwedLocals evm evmClaimed I accruedNat).get? "to" =
      some (claimSrcValue I) := by
  rw [claimInternalAfterOwedLocals, store_get_ne _ _ (by decide)]
  rw [claimInternalAfterInternalLocals, store_get_ne _ _ (by decide)]
  rw [claimInternalAfterClaimedLocals, store_get_ne _ _ (by decide),
    claimInternalConfigLocals]
  rw [store_get_ne _ _ (by decide), claimInternalAfterShouldLocals]
  rw [store_get_ne _ _ (by decide), claimInternalAfterRescaleLocals]
  rw [store_get_ne _ _ (by decide), claimInternalAfterTokenLocals]
  rw [store_get_ne _ _ (by decide), claimInternalStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem claimInternalAfterOwedLocals_owed
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ) :
    (claimInternalAfterOwedLocals evm evmClaimed I accruedNat).get? "owed" =
      some (.int (Int.ofNat (claimInternalOwedNat evmClaimed I accruedNat))) := by
  rw [claimInternalAfterOwedLocals, store_get_self]

theorem claimDoTransferOutStore_token (I : ExecutionEnv) (slot0 amount : UInt256) :
    (claimDoTransferOutStore I slot0 amount).get? "token" =
      some (getRewardOwedTokenValueFromSlot0 slot0) := by
  rw [claimDoTransferOutStore, store_get_self]

theorem claimDoTransferOutStore_to (I : ExecutionEnv) (slot0 amount : UInt256) :
    (claimDoTransferOutStore I slot0 amount).get? "to" = some (claimSrcValue I) := by
  rw [claimDoTransferOutStore, store_get_ne _ _ (by decide), store_get_self]

theorem claimDoTransferOutStore_amount (I : ExecutionEnv) (slot0 amount : UInt256) :
    (claimDoTransferOutStore I slot0 amount).get? "amount" =
      some (.int (Int.ofNat amount.toNat)) := by
  rw [claimDoTransferOutStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem claimTransferCallStore_success
    (I : ExecutionEnv) (slot0 amount : UInt256) (success : Bool) :
    (claimTransferCallStore I slot0 amount success).get? "success" =
      some (.bool success) := by
  rw [claimTransferCallStore, store_get_self]

theorem evalStorageRef_claim_rewardsClaimed_of {locals : Store}
    (evm : EVM.State) (I : ExecutionEnv)
    (hcomet : locals.get? "comet" = some (claimCometValue I))
    (hsrc : locals.get? "src" = some (claimSrcValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (rewardsClaimedRef (.var "comet") (.var "src")) =
      .ok { base := "rewardsClaimed",
            steps := [.mindex (.address (AccountAddress.ofNat
                        (claimCometWord I).toNat)),
                      .mindex (.address (AccountAddress.ofNat
                        (claimSrcWord I).toNat))] } := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, rewardsClaimedRef,
    evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
    Std.HashMap.get?_eq_getElem?]
  rw [← Std.HashMap.get?_eq_getElem?, hcomet]
  rw [← Std.HashMap.get?_eq_getElem?, hsrc]

theorem evalExpr_claim_claimed_of {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv)
    (hcomet : locals.get? "comet" = some (claimCometValue I))
    (hsrc : locals.get? "src" = some (claimSrcValue I))
    (hbase : locals.get? "rewardsClaimed" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (rewardsClaimedRef (.var "comet") (.var "src"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (getRewardOwedRewardsClaimedSlotOf I)).toNat)) := by
  have her := evalStorageRef_claim_rewardsClaimed_of evm I hcomet hsrc
  have hty : storageTypeAt? contract.storage
      { base := "rewardsClaimed",
        steps := [.mindex (.address (AccountAddress.ofNat (claimCometWord I).toNat)),
                  .mindex (.address (AccountAddress.ofNat (claimSrcWord I).toNat))] } =
      some (.elem (.int uint256Int)) := by
    simp [storageTypeAt?, contract, storageDecls, List.find?, List.foldlM, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "rewardsClaimed",
        steps := [.mindex (.address (AccountAddress.ofNat (claimCometWord I).toNat)),
                  .mindex (.address (AccountAddress.ofNat (claimSrcWord I).toNat))] } =
      fun _ => some (fieldLoc (getRewardOwedRewardsClaimedSlotOf I) 0 32
        (by decide) (.int uint256Int)) := by
    rfl
  rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  exact cometRewardsStorageLocLoad_uint256 evm (getRewardOwedRewardsClaimedSlotOf I)

theorem evalExpr_claim_claimed_config (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract, locals := claimInternalConfigLocals evm I } evm
      (.storage (rewardsClaimedRef (.var "comet") (.var "src"))) =
      .ok (.int (Int.ofNat (getRewardOwedClaimedLoad evm I).toNat)) := by
  exact evalExpr_claim_claimed_of evm I
    (claimInternalConfigLocals_comet evm I)
    (claimInternalConfigLocals_src evm I)
    (claimInternalConfigLocals_no_rewardsClaimed evm I)

theorem evalExprs_claim_getRewardAccrued_args_of {locals : Store} (evm : EVM.State)
    (I : ExecutionEnv) (slot0 multiplier : UInt256)
    (hcomet : locals.get? "comet" = some (claimCometValue I))
    (hsrc : locals.get? "src" = some (claimSrcValue I))
    (hrescale :
      locals.get? "rescaleFactor" =
        some (.int (Int.ofNat (rewardConfigRescaleFromSlot0 slot0).toNat)))
    (hshould :
      locals.get? "shouldUpscale" =
        some (wordToElem .bool (rewardConfigShouldUpscaleRawFromSlot0 slot0)))
    (hmult : locals.get? "multiplier" = some (.int (Int.ofNat multiplier.toNat))) :
    evalExprs? config { contract := contract, locals := locals } evm
      [.var "comet", .var "src", .var "rescaleFactor",
        .var "shouldUpscale", .var "multiplier"] =
      .ok (getRewardAccruedArgs I slot0 multiplier) := by
  simp only [getRewardAccruedArgs, evalExprs?,
    evalExpr_claim_comet_of evm I hcomet,
    evalExpr_claim_src_of evm I hsrc, EvalResult.bind, bind,
    evalExpr?, EvalResult.ofOption]
  rw [hrescale, hshould, hmult]
  simp [claimCometValue, claimCometWord, claimSrcValue, claimSrcWord,
    getRewardOwedCometValue, getRewardOwedCometWord, getRewardOwedAccountValue,
    getRewardOwedAccountWord]
  rfl

theorem evalExprs_claim_getRewardAccruedArgs_afterClaimed
    (evm evmClaimed : EVM.State) (I : ExecutionEnv) :
    evalExprs? config
      { contract := contract, locals := claimInternalAfterClaimedLocals evm evmClaimed I }
      evmClaimed
      [.var "comet", .var "src", .var "rescaleFactor",
        .var "shouldUpscale", .var "multiplier"] =
      .ok (getRewardAccruedArgs I (getRewardOwedSlot0Load evm I)
        (getRewardOwedMultiplierLoad evm I)) := by
  exact evalExprs_claim_getRewardAccrued_args_of evmClaimed I
    (getRewardOwedSlot0Load evm I) (getRewardOwedMultiplierLoad evm I)
    (claimInternalAfterClaimedLocals_comet evm evmClaimed I)
    (claimInternalAfterClaimedLocals_src evm evmClaimed I)
    (claimInternalAfterClaimedLocals_rescaleFactor evm evmClaimed I)
    (claimInternalAfterClaimedLocals_shouldUpscale evm evmClaimed I)
    (claimInternalAfterClaimedLocals_multiplier evm evmClaimed I)

theorem evalExpr_claimInternal_shouldAccrue_false
    (evm : EVM.State) (I : ExecutionEnv)
    (hzero : claimShouldAccrueWord I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := claimInternalConfigLocals evm I }
      evm (.var "shouldAccrue") = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [claimInternalConfigLocals_shouldAccrue]
  simp [claimShouldAccrueValue, wordToElem, hzero]

theorem evalExpr_claimInternal_shouldAccrue_true
    (evm : EVM.State) (I : ExecutionEnv)
    (hone : claimShouldAccrueWord I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := claimInternalConfigLocals evm I }
      evm (.var "shouldAccrue") = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [claimInternalConfigLocals_shouldAccrue]
  simp [claimShouldAccrueValue, wordToElem, hone]

theorem evalExpr_claimInternal_accrued_gt_claimed_false
    (evm evmClaimed evmRun : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ)
    (hle : accruedNat ≤ (getRewardOwedClaimedLoad evmClaimed I).toNat) :
    evalExpr? config
      { contract := contract, locals := claimInternalAfterInternalLocals evm evmClaimed I accruedNat }
      evmRun (.binary .gt (.var "accrued") (.var "claimed")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [claimInternalAfterInternalLocals_accrued,
    claimInternalAfterInternalLocals_claimed]
  have hgtFalse :
      ¬ (↑(getRewardOwedClaimedLoad evmClaimed I).toNat : Int) < ↑accruedNat := by
    intro hgt
    exact (not_lt_of_ge hle) (by exact_mod_cast hgt)
  simp [evalBinaryOp?, hgtFalse]

theorem evalExpr_claimInternal_accrued_gt_claimed_true
    (evm evmClaimed evmRun : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ)
    (hlt : (getRewardOwedClaimedLoad evmClaimed I).toNat < accruedNat) :
    evalExpr? config
      { contract := contract, locals := claimInternalAfterInternalLocals evm evmClaimed I accruedNat }
      evmRun (.binary .gt (.var "accrued") (.var "claimed")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [claimInternalAfterInternalLocals_accrued,
    claimInternalAfterInternalLocals_claimed]
  have hgtTrue :
      (↑(getRewardOwedClaimedLoad evmClaimed I).toNat : Int) < ↑accruedNat := by
    exact_mod_cast hlt
  simp [evalBinaryOp?, hgtTrue]

theorem evalExpr_claimInternal_owed_at
    (evm evmClaimed evmRun : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ)
    (hlt : (getRewardOwedClaimedLoad evmClaimed I).toNat < accruedNat) :
    evalExpr? config
      { contract := contract, locals := claimInternalAfterInternalLocals evm evmClaimed I accruedNat }
      evmRun (.binary .sub (.var "accrued") (.var "claimed")) =
      .ok (.int (Int.ofNat (claimInternalOwedNat evmClaimed I accruedNat))) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [claimInternalAfterInternalLocals_accrued,
    claimInternalAfterInternalLocals_claimed]
  have hsub :
      (↑accruedNat - ↑(getRewardOwedClaimedLoad evmClaimed I).toNat : Int) =
        ↑(accruedNat - (getRewardOwedClaimedLoad evmClaimed I).toNat) := by
    omega
  simp [evalBinaryOp?, claimInternalOwedNat, hsub]

theorem evalExprs_claim_transferArgs_afterOwed
    (evm evmClaimed evmRun : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ)
    {amount : UInt256}
    (hamount : amount.toNat = claimInternalOwedNat evmClaimed I accruedNat) :
    evalExprs? config
      { contract := contract, locals := claimInternalAfterOwedLocals evm evmClaimed I accruedNat }
      evmRun [.var "to", .var "owed"] =
      .ok (claimTransferArgs I amount) := by
  simp only [claimTransferArgs, evalExprs?, evalExpr?, EvalResult.ofOption,
    EvalResult.bind, bind]
  rw [claimInternalAfterOwedLocals_to, claimInternalAfterOwedLocals_owed]
  rw [hamount]
  rfl

theorem evalExpr_claimDoTransferOut_var_token
    (evm : EVM.State) (I : ExecutionEnv) (slot0 amount : UInt256) :
    evalExpr? config { contract := contract, locals := claimDoTransferOutStore I slot0 amount }
      evm (.var "token") = .ok (getRewardOwedTokenValueFromSlot0 slot0) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [claimDoTransferOutStore_token]

theorem evalExpr_claimDoTransferOut_var_to
    (evm : EVM.State) (I : ExecutionEnv) (slot0 amount : UInt256) :
    evalExpr? config { contract := contract, locals := claimDoTransferOutStore I slot0 amount }
      evm (.var "to") = .ok (claimSrcValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [claimDoTransferOutStore_to]

theorem evalExpr_claimDoTransferOut_var_amount
    (evm : EVM.State) (I : ExecutionEnv) (slot0 amount : UInt256) :
    evalExpr? config { contract := contract, locals := claimDoTransferOutStore I slot0 amount }
      evm (.var "amount") = .ok (.int (Int.ofNat amount.toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [claimDoTransferOutStore_amount]

theorem evalExprs_claimDoTransferOut_transfer_args
    (evm : EVM.State) (I : ExecutionEnv) (slot0 amount : UInt256) :
    evalExprs? config { contract := contract, locals := claimDoTransferOutStore I slot0 amount }
      evm [.var "to", .var "amount"] = .ok (claimTransferArgs I amount) := by
  simp only [claimTransferArgs, evalExprs?, evalExpr_claimDoTransferOut_var_to,
    evalExpr_claimDoTransferOut_var_amount, EvalResult.bind, bind]
  rfl

theorem bindParams_claimDoTransferOut
    (I : ExecutionEnv) (slot0 amount : UInt256) :
    bindParams? doTransferOutFunction.params
      [getRewardOwedTokenValueFromSlot0 slot0, claimSrcValue I,
        .int (Int.ofNat amount.toNat)] =
      some (claimDoTransferOutStore I slot0 amount) := by
  simp [doTransferOutFunction, getRewardOwedTokenValueFromSlot0, claimDoTransferOutStore,
    claimSrcValue, bindParams?]

theorem evalExpr_claimTransfer_success
    (evm : EVM.State) (I : ExecutionEnv) (slot0 amount : UInt256) (success : Bool) :
    evalExpr? config
      { contract := contract, locals := claimTransferCallStore I slot0 amount success } evm
      (.var "success") = .ok (.bool success) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [claimTransferCallStore_success]

theorem assignRewardsClaimed_afterInternal
    (evm evmClaimed evmRun : EVM.State) (I : ExecutionEnv) (accruedNat : ℕ)
    (haccrued : accruedNat < UInt256.size) :
    assignStorageRef? config
      { contract := contract, locals := claimInternalAfterInternalLocals evm evmClaimed I accruedNat }
      evmRun .storage (rewardsClaimedRef (.var "comet") (.var "src"))
      (.int (Int.ofNat accruedNat)) =
      .ok
        ({ contract := contract,
            locals := claimInternalAfterInternalLocals evm evmClaimed I accruedNat },
          Solm.EVM.storageStore evmRun evmRun.executionEnv.codeOwner
            (getRewardOwedRewardsClaimedSlotOf I) (UInt256.ofNat accruedNat)) := by
  let er : EvaledStorageRef :=
    { base := "rewardsClaimed",
      steps := [.mindex (.address (AccountAddress.ofNat (claimCometWord I).toNat)),
        .mindex (.address (AccountAddress.ofNat (claimSrcWord I).toNat))] }
  let loc : StorageLoc := uint256Loc (getRewardOwedRewardsClaimedSlotOf I)
  have her :
      evalStorageRef config
        { contract := contract,
          locals := claimInternalAfterInternalLocals evm evmClaimed I accruedNat } evmRun
        (rewardsClaimedRef (.var "comet") (.var "src")) = .ok er := by
    simpa [er] using evalStorageRef_claim_rewardsClaimed_of evmRun I
      (claimInternalAfterInternalLocals_comet evm evmClaimed I accruedNat)
      (claimInternalAfterInternalLocals_src evm evmClaimed I accruedNat)
  have hty :
      storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, storageTypeAt?, contract, storageDecls, List.find?, List.foldlM,
      storageTypeStep?]
  have hloc : config.storage.layout er = fun _ => some loc := by
    rfl
  have hstore :
      storageLocStore evmRun loc (.int (Int.ofNat accruedNat)) =
        some (Solm.EVM.storageStore evmRun evmRun.executionEnv.codeOwner
          (getRewardOwedRewardsClaimedSlotOf I) (UInt256.ofNat accruedNat)) := by
    have hvalToNat : (UInt256.ofNat accruedNat).toNat = accruedNat :=
      UInt256.toNat_ofNat_of_lt haccrued
    simpa [loc, hvalToNat] using
      storageLocStore_uint256 evmRun (getRewardOwedRewardsClaimedSlotOf I)
      (UInt256.ofNat accruedNat)
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm :=
      { contract := contract, locals := claimInternalAfterInternalLocals evm evmClaimed I accruedNat })
    (evm := evmRun)
    (evm' := Solm.EVM.storageStore evmRun evmRun.executionEnv.codeOwner
      (getRewardOwedRewardsClaimedSlotOf I) (UInt256.ofNat accruedNat))
    (slot := rewardsClaimedRef (.var "comet") (.var "src")) (er := er)
    (ty := .elem (.int uint256Int)) (loc := loc)
    (value := .int (Int.ofNat accruedNat))
    (claimInternalAfterInternalLocals_no_rewardsClaimed evm evmClaimed I accruedNat)
    her hty hloc (by trivial) hstore

theorem claimDoTransferOutBodyReverts_callFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) (slot0 amount : UInt256) {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (claimTransferTarget slot0))
        "transfer" 0 (claimTransferArgs I amount) (false, evm', out) true) :
    ExecFuncBody config
      { contract := contract, locals := claimDoTransferOutStore I slot0 amount }
      evm doTransferOutFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config
    { contract := contract, locals := claimDoTransferOutStore I slot0 amount } evm
    [ .externalCall (.var "token") "transfer" (.intLit 0)
        [.var "to", .var "amount"] "success",
      .require (.var "success") ] .reverted
  exact ExecBlock.consRevert
    (ExecStmt.externalCallFailure
      (evalExpr_claimDoTransferOut_var_token evm I slot0 amount)
      (by simp [evalExpr?, pure])
      (evalExprs_claimDoTransferOut_transfer_args evm I slot0 amount)
      hcall)

theorem claimDoTransferOutBodyReverts_decode
    (evm evm' : EVM.State) (I : ExecutionEnv) (slot0 amount : UInt256) {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (claimTransferTarget slot0))
        "transfer" 0 (claimTransferArgs I amount) (true, evm', out) true)
    (hdec : config.externalABI.decode? "transfer" out = none) :
    ExecFuncBody config
      { contract := contract, locals := claimDoTransferOutStore I slot0 amount }
      evm doTransferOutFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config
    { contract := contract, locals := claimDoTransferOutStore I slot0 amount } evm
    [ .externalCall (.var "token") "transfer" (.intLit 0)
        [.var "to", .var "amount"] "success",
      .require (.var "success") ] .reverted
  exact ExecBlock.consRevert
    (ExecStmt.externalCallReturnDecodeRevert
      (evalExpr_claimDoTransferOut_var_token evm I slot0 amount)
      (by simp [evalExpr?, pure])
      (evalExprs_claimDoTransferOut_transfer_args evm I slot0 amount)
      hcall hdec)

set_option maxHeartbeats 1000000 in
theorem claimDoTransferOutBodyReverts_false
    (evm evm' : EVM.State) (I : ExecutionEnv) (slot0 amount : UInt256) {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (claimTransferTarget slot0))
        "transfer" 0 (claimTransferArgs I amount) (true, evm', out) true)
    (hdec : config.externalABI.decode? "transfer" out = some [.bool false]) :
    ExecFuncBody config
      { contract := contract, locals := claimDoTransferOutStore I slot0 amount }
      evm doTransferOutFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config
    { contract := contract, locals := claimDoTransferOutStore I slot0 amount } evm
    [ .externalCall (.var "token") "transfer" (.intLit 0)
        [.var "to", .var "amount"] "success",
      .require (.var "success") ] .reverted
  refine ExecBlock.consNormal
    (solm' :=
      { contract := contract,
        locals := (claimDoTransferOutStore I slot0 amount).insert "success"
          (collapseReturns [.bool false]) })
    (evm' := evm') ?_ ?_
  · exact ExecStmt.externalCallSuccess
      (cfg := config)
      (solm := { contract := contract, locals := claimDoTransferOutStore I slot0 amount })
      (evm := evm)
      (receiver := .var "token") (target := claimTransferTarget slot0)
      (eth := .intLit 0) (sendVal := 0)
      (args := [.var "to", .var "amount"]) (argVals := claimTransferArgs I amount)
      (name := "transfer") (retVar := "success")
      (evm' := evm') (out := out) (perm := true) (value := [.bool false])
      (evalExpr_claimDoTransferOut_var_token evm I slot0 amount)
      (by simp [evalExpr?, pure])
      (evalExprs_claimDoTransferOut_transfer_args evm I slot0 amount)
      hcall hdec
  · simpa [claimTransferCallStore, collapseReturns] using
      (ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_claimTransfer_success evm' I slot0 amount false)))

set_option maxHeartbeats 1000000 in
theorem claimDoTransferOutBodyReturns_true
    (evm evm' : EVM.State) (I : ExecutionEnv) (slot0 amount : UInt256) {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (claimTransferTarget slot0))
        "transfer" 0 (claimTransferArgs I amount) (true, evm', out) true)
    (hdec : config.externalABI.decode? "transfer" out = some [.bool true]) :
    ExecFuncBody config
      { contract := contract, locals := claimDoTransferOutStore I slot0 amount }
      evm doTransferOutFunction.body
      (.returned
        { contract := contract, locals := claimTransferCallStore I slot0 amount true }
        evm' none) := by
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config
    { contract := contract, locals := claimDoTransferOutStore I slot0 amount } evm
    [ .externalCall (.var "token") "transfer" (.intLit 0)
        [.var "to", .var "amount"] "success",
      .require (.var "success") ]
    (.ok { contract := contract, locals := claimTransferCallStore I slot0 amount true } evm')
  refine ExecBlock.consNormal
    (solm' :=
      { contract := contract,
        locals := (claimDoTransferOutStore I slot0 amount).insert "success"
          (collapseReturns [.bool true]) })
    (evm' := evm') ?_ ?_
  · exact ExecStmt.externalCallSuccess
      (cfg := config)
      (solm := { contract := contract, locals := claimDoTransferOutStore I slot0 amount })
      (evm := evm)
      (receiver := .var "token") (target := claimTransferTarget slot0)
      (eth := .intLit 0) (sendVal := 0)
      (args := [.var "to", .var "amount"]) (argVals := claimTransferArgs I amount)
      (name := "transfer") (retVar := "success")
      (evm' := evm') (out := out) (perm := true) (value := [.bool true])
      (evalExpr_claimDoTransferOut_var_token evm I slot0 amount)
      (by simp [evalExpr?, pure])
      (evalExprs_claimDoTransferOut_transfer_args evm I slot0 amount)
      hcall hdec
  · simpa [claimTransferCallStore, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_claimTransfer_success evm' I slot0 amount true))
        ExecBlock.nil)

/-! ## `claimInternal` reward-config scratch memory -/

noncomputable abbrev claimRewardConfigHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (claimCometWord I) ⟨1⟩ solcFreePtrMem

noncomputable abbrev claimConfigAllocMem (I : ExecutionEnv) : ByteArray :=
  writeWord (claimRewardConfigHashMem I) 64 (⟨256⟩ : UInt256)

noncomputable abbrev claimConfigTokenMem (I : ExecutionEnv) (slot0 : UInt256) : ByteArray :=
  writeWord (claimConfigAllocMem I) 128 (rewardConfigTokenFromSlot0 slot0)

noncomputable abbrev claimConfigRescaleMem (I : ExecutionEnv) (slot0 : UInt256) : ByteArray :=
  writeWord (claimConfigTokenMem I slot0) 160 (rewardConfigRescaleFromSlot0 slot0)

noncomputable abbrev claimConfigShouldMem (I : ExecutionEnv) (slot0 : UInt256) : ByteArray :=
  writeWord (claimConfigRescaleMem I slot0) 192 (rewardConfigShouldUpscaleFromSlot0 slot0)

noncomputable abbrev claimConfigMultiplierMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) : ByteArray :=
  writeWord (claimConfigShouldMem I slot0) 224 multiplier

noncomputable abbrev claimInvalidRewardConfigSelectorMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) : ByteArray :=
  writeWord (claimConfigMultiplierMem I slot0 multiplier) 256
    (UInt256.shiftLeft (⟨1311535579⟩ : UInt256) ⟨225⟩)

noncomputable abbrev claimInvalidRewardConfigArgMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) : ByteArray :=
  writeWord (claimInvalidRewardConfigSelectorMem I slot0 multiplier) 260 (claimCometWord I)

noncomputable abbrev claimClaimedInnerHashMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) : ByteArray :=
  twoWordHashMem (UInt256.land (claimCometWord I) solcAddrMask) ⟨2⟩
    (claimConfigMultiplierMem I slot0 multiplier)

noncomputable abbrev claimClaimedOuterHashMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) : ByteArray :=
  twoWordHashMem (UInt256.land (claimSrcWord I) solcAddrMask)
    (solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask))
    (claimClaimedInnerHashMem I slot0 multiplier)

noncomputable abbrev claimBaseTrackingSelectorMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) : ByteArray :=
  writeWord (claimClaimedOuterHashMem I slot0 multiplier) 256
    (UInt256.shiftLeft (⟨719776253⟩ : UInt256) ⟨226⟩)

noncomputable abbrev claimBaseTrackingCalldataMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) : ByteArray :=
  writeWord (claimBaseTrackingSelectorMem I slot0 multiplier) 260 (claimSrcWord I)

abbrev claimBaseTrackingCallPc : UInt256 := getRewardOwedBaseTrackingCallPc

abbrev claimBaseTrackingCallSize : UInt256 := getRewardOwedBaseTrackingCallSize

abbrev claimBaseTrackingCallAw : UInt256 := UInt256.ofNat 10

abbrev claimBaseTrackingPostCallTail (I : ExecutionEnv) (claimed : UInt256) : List UInt256 :=
  [ ⟨128⟩,
    ⟨256⟩,
    ⟨3432⟩,
    ⟨128⟩,
    ⟨0⟩,
    claimSrcWord I,
    solcAddrMask,
    ⟨32⟩,
    claimed,
    UInt256.land (claimSrcWord I) solcAddrMask,
    UInt256.land (claimCometWord I) solcAddrMask,
    ⟨64⟩,
    ⟨1001⟩,
    ⟨64⟩,
    ⟨0⟩ ]

abbrev claimBaseTrackingPostCallStack (I : ExecutionEnv) (z : Bool) (claimed : UInt256) :
    List UInt256 :=
  (if z then ⟨1⟩ else ⟨0⟩) :: claimBaseTrackingPostCallTail I claimed

noncomputable abbrev claimBaseTrackingPostCallMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (baseOut : ByteArray) : ByteArray :=
  baseOut.write 0 (claimBaseTrackingCalldataMem I slot0 multiplier) 256
    (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat

noncomputable abbrev claimBaseTrackingPostDecodeMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (baseOut : ByteArray) : ByteArray :=
  writeWord (claimBaseTrackingPostCallMem I slot0 multiplier baseOut) 64
    (⟨288⟩ : UInt256)

abbrev claimRewardsClaimedBaseSlot : UInt256 :=
  ⟨16344734836896974401298970600416103014985972868941485175496275033332075043944⟩

noncomputable abbrev claimTransferInnerHashMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (baseOut : ByteArray) : ByteArray :=
  twoWordHashMem (UInt256.land (claimCometWord I) solcAddrMask) ⟨2⟩
    (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)

noncomputable abbrev claimTransferOuterHashMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (baseOut : ByteArray) : ByteArray :=
  twoWordHashMem (UInt256.land (claimSrcWord I) solcAddrMask)
    (solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask))
    (claimTransferInnerHashMem I slot0 multiplier baseOut)

noncomputable abbrev claimTransferSelectorMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (baseOut : ByteArray) : ByteArray :=
  (UInt256.toByteArray withdrawTokenTransferSelectorShifted).write 0
    (claimTransferOuterHashMem I slot0 multiplier baseOut) 288 32

noncomputable abbrev claimTransferArgsMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (baseOut : ByteArray)
    (recipient : UInt256) : ByteArray :=
  (UInt256.toByteArray recipient).write 0
    (claimTransferSelectorMem I slot0 multiplier baseOut) 292 32

noncomputable abbrev claimTransferCalldataMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (baseOut : ByteArray)
    (recipient value : UInt256) : ByteArray :=
  (UInt256.toByteArray value).write 0
    (claimTransferArgsMem I slot0 multiplier baseOut recipient) 324 32

abbrev claimTransferCallPc : UInt256 := withdrawTokenTransferCallPc

abbrev claimTransferCallSize : UInt256 := withdrawTokenTransferCallSize

abbrev claimTransferCallAw : UInt256 := UInt256.ofNat 12

abbrev claimTransferPostCallTail (I : ExecutionEnv) (amount : UInt256) : List UInt256 :=
  [ ⟨288⟩,
    claimSrcWord I,
    amount,
    ⟨3531⟩,
    ⟨128⟩,
    solcAddrMask,
    claimSrcWord I,
    solcAddrMask,
    ⟨32⟩,
    claimRewardsClaimedBaseSlot,
    UInt256.land (claimSrcWord I) solcAddrMask,
    amount,
    ⟨64⟩,
    ⟨1001⟩,
    ⟨64⟩,
    ⟨0⟩ ]

abbrev claimTransferPostCallStack (z : Bool) (I : ExecutionEnv) (amount : UInt256) :
    List UInt256 :=
  (if z then ⟨1⟩ else ⟨0⟩) :: claimTransferPostCallTail I amount

noncomputable abbrev claimTransferPostCallMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (baseOut out : ByteArray)
    (amount : UInt256) : ByteArray :=
  out.write 0
    (claimTransferCalldataMem I slot0 multiplier baseOut (claimSrcWord I) amount)
    288 (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat

abbrev claimTransferPostCallAw : UInt256 :=
  UInt256.ofNat (MachineState.M claimTransferCallAw.toNat (⟨288⟩ : UInt256).toNat
    (⟨32⟩ : UInt256).toNat)

theorem claimTransferTarget_eq_targetWord (slot0 : UInt256) :
    EVM.address (claimTransferTarget slot0) =
      AccountAddress.ofUInt256 (UInt256.land solcAddrMask (rewardConfigTokenFromSlot0 slot0)) := by
  have hclean :
      UInt256.land solcAddrMask (rewardConfigTokenFromSlot0 slot0) =
        rewardConfigTokenFromSlot0 slot0 := by
    rw [u256_land_comm solcAddrMask (rewardConfigTokenFromSlot0 slot0)]
    exact rewardConfigTokenFromSlot0_clean slot0
  rw [hclean, accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [claimTransferTarget, EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt (AccountAddress.ofNat (rewardConfigTokenFromSlot0 slot0).toNat).isLt

noncomputable abbrev claimBaseTrackingPostShortDecodeMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (baseOut : ByteArray) : ByteArray :=
  (UInt256.toByteArray ((⟨256⟩ : UInt256) +
    UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat baseOut.size + ⟨31⟩))).write 0
      (claimBaseTrackingPostCallMem I slot0 multiplier baseOut) 64 32

abbrev claimBaseTrackingPostCallAw : UInt256 :=
  UInt256.ofNat (MachineState.M
    (MachineState.M claimBaseTrackingCallAw.toNat
      (⟨256⟩ : UInt256).toNat claimBaseTrackingCallSize.toNat)
    (⟨256⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat)

abbrev claimBaseTrackingReturnWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

theorem claimRewardConfigHashMem_size (I : ExecutionEnv) :
    (claimRewardConfigHashMem I).size = 96 := by
  unfold claimRewardConfigHashMem
  rw [twoWordHashMem_size_of_ge]
  · exact solcFreePtrMem_size
  · rw [solcFreePtrMem_size]
    decide

theorem claimRewardConfigHashMem_keccakSlot (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((claimRewardConfigHashMem I).readWithPadding 0 64))) =
      solcMappingSlot ⟨1⟩ (claimCometWord I) := by
  unfold claimRewardConfigHashMem
  exact twoWordHashMem_solcMappingSlot_of_ge ⟨1⟩ (claimCometWord I)
    (by rw [solcFreePtrMem_size]; decide)

theorem claimRewardConfigHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (claimRewardConfigHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((claimRewardConfigHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  have hread :
      (claimRewardConfigHashMem I).readWithPadding 64 32 =
        UInt256.toByteArray (⟨128⟩ : UInt256) := by
    simpa [claimRewardConfigHashMem] using
      (twoWordHashMem_read64_of_ge (mem := solcFreePtrMem) (key := claimCometWord I)
        (slot := ⟨1⟩) (by rw [solcFreePtrMem_size])).trans solcFreePtrMem_read64
  rw [if_neg]
  · rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hread,
      fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]
  · rw [claimRewardConfigHashMem_size]
    native_decide

theorem claimConfigAllocMem_size (I : ExecutionEnv) :
    (claimConfigAllocMem I).size = 96 := by
  unfold claimConfigAllocMem
  rw [writeWord_size]
  · rw [claimRewardConfigHashMem_size]
    native_decide
  · rw [claimRewardConfigHashMem_size]
    native_decide

theorem claimConfigAllocMem_read64 (I : ExecutionEnv) :
    (claimConfigAllocMem I).readWithPadding 64 32 =
      UInt256.toByteArray (⟨256⟩ : UInt256) := by
  simpa [claimConfigAllocMem] using
    writeWord_read_back (claimRewardConfigHashMem I) 64 (⟨256⟩ : UInt256)
      (by rw [claimRewardConfigHashMem_size]; native_decide)

theorem claimConfigTokenMem_size (I : ExecutionEnv) (slot0 : UInt256) :
    (claimConfigTokenMem I slot0).size = 160 := by
  unfold claimConfigTokenMem
  rw [writeWord_size]
  · rw [claimConfigAllocMem_size]
    native_decide
  · rw [claimConfigAllocMem_size]
    native_decide

theorem claimConfigRescaleMem_size (I : ExecutionEnv) (slot0 : UInt256) :
    (claimConfigRescaleMem I slot0).size = 192 := by
  unfold claimConfigRescaleMem
  rw [writeWord_size]
  · rw [claimConfigTokenMem_size]
    native_decide
  · rw [claimConfigTokenMem_size]
    native_decide

theorem claimConfigShouldMem_size (I : ExecutionEnv) (slot0 : UInt256) :
    (claimConfigShouldMem I slot0).size = 224 := by
  unfold claimConfigShouldMem
  rw [writeWord_size]
  · rw [claimConfigRescaleMem_size]
    native_decide
  · rw [claimConfigRescaleMem_size]
    native_decide

theorem claimConfigMultiplierMem_size (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (claimConfigMultiplierMem I slot0 multiplier).size = 256 := by
  unfold claimConfigMultiplierMem
  rw [writeWord_size]
  · rw [claimConfigShouldMem_size]
    native_decide
  · rw [claimConfigShouldMem_size]
    native_decide

theorem claimConfigTokenMem_read64 (I : ExecutionEnv) (slot0 : UInt256) :
    (claimConfigTokenMem I slot0).readWithPadding 64 32 =
      UInt256.toByteArray (⟨256⟩ : UInt256) := by
  simpa [claimConfigTokenMem] using
    writeWord_read_preserved (claimConfigAllocMem I) 128 64
      (rewardConfigTokenFromSlot0 slot0)
      (by rw [claimConfigAllocMem_size]; native_decide)
      (by
        left
        rw [claimConfigAllocMem_size]
        constructor <;> norm_num)
      |>.trans (claimConfigAllocMem_read64 I)

theorem claimConfigRescaleMem_read64 (I : ExecutionEnv) (slot0 : UInt256) :
    (claimConfigRescaleMem I slot0).readWithPadding 64 32 =
      UInt256.toByteArray (⟨256⟩ : UInt256) := by
  simpa [claimConfigRescaleMem] using
    writeWord_read_preserved (claimConfigTokenMem I slot0) 160 64
      (rewardConfigRescaleFromSlot0 slot0)
      (by rw [claimConfigTokenMem_size]; native_decide)
      (by
        left
        rw [claimConfigTokenMem_size]
        constructor <;> norm_num)
      |>.trans (claimConfigTokenMem_read64 I slot0)

theorem claimConfigShouldMem_read64 (I : ExecutionEnv) (slot0 : UInt256) :
    (claimConfigShouldMem I slot0).readWithPadding 64 32 =
      UInt256.toByteArray (⟨256⟩ : UInt256) := by
  simpa [claimConfigShouldMem] using
    writeWord_read_preserved (claimConfigRescaleMem I slot0) 192 64
      (rewardConfigShouldUpscaleFromSlot0 slot0)
      (by rw [claimConfigRescaleMem_size]; native_decide)
      (by
        left
        rw [claimConfigRescaleMem_size]
        constructor <;> norm_num)
      |>.trans (claimConfigRescaleMem_read64 I slot0)

theorem claimConfigMultiplierMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (claimConfigMultiplierMem I slot0 multiplier).readWithPadding 64 32 =
      UInt256.toByteArray (⟨256⟩ : UInt256) := by
  simpa [claimConfigMultiplierMem] using
    writeWord_read_preserved (claimConfigShouldMem I slot0) 224 64 multiplier
      (by rw [claimConfigShouldMem_size]; native_decide)
      (by
        left
        rw [claimConfigShouldMem_size]
        constructor <;> norm_num)
      |>.trans (claimConfigShouldMem_read64 I slot0)

theorem claimConfigMultiplierMem_mload64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (claimConfigMultiplierMem I slot0 multiplier).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((claimConfigMultiplierMem I slot0 multiplier).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨256⟩ := by
  rw [if_neg]
  · rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, claimConfigMultiplierMem_read64,
      fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]
  · rw [claimConfigMultiplierMem_size]
    native_decide

theorem claimClaimedInnerHashMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (claimClaimedInnerHashMem I slot0 multiplier).readWithPadding 64 32 =
      UInt256.toByteArray (⟨256⟩ : UInt256) := by
  unfold claimClaimedInnerHashMem
  rw [twoWordHashMem_read64_of_ge]
  · exact claimConfigMultiplierMem_read64 I slot0 multiplier
  · rw [claimConfigMultiplierMem_size]
    decide

theorem claimClaimedInnerHashMem_size_ge256
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    256 ≤ (claimClaimedInnerHashMem I slot0 multiplier).size := by
  unfold claimClaimedInnerHashMem
  rw [twoWordHashMem_size_of_ge]
  · rw [claimConfigMultiplierMem_size]
  · rw [claimConfigMultiplierMem_size]
    decide

theorem claimClaimedOuterHashMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (claimClaimedOuterHashMem I slot0 multiplier).readWithPadding 64 32 =
      UInt256.toByteArray (⟨256⟩ : UInt256) := by
  unfold claimClaimedOuterHashMem
  rw [twoWordHashMem_read64_of_ge]
  · exact claimClaimedInnerHashMem_read64 I slot0 multiplier
  · exact le_trans (by norm_num) <| claimClaimedInnerHashMem_size_ge256 I slot0 multiplier

theorem claimClaimedOuterHashMem_size_ge256
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    256 ≤ (claimClaimedOuterHashMem I slot0 multiplier).size := by
  unfold claimClaimedOuterHashMem
  rw [twoWordHashMem_size_of_ge]
  · exact claimClaimedInnerHashMem_size_ge256 I slot0 multiplier
  · exact le_trans (by norm_num) <| claimClaimedInnerHashMem_size_ge256 I slot0 multiplier

theorem claimClaimedOuterHashMem_mload64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (claimClaimedOuterHashMem I slot0 multiplier).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((claimClaimedOuterHashMem I slot0 multiplier).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨256⟩ := by
  apply mloadWordValue_of_readWithPadding
  · simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      (lt_of_lt_of_le (by norm_num : 64 < 256) <|
        claimClaimedOuterHashMem_size_ge256 I slot0 multiplier)
  · native_decide
  · exact claimClaimedOuterHashMem_read64 I slot0 multiplier

theorem claimClaimedOuterHashMem_keccakSlot
    (I : ExecutionEnv) (slot0 multiplier : UInt256)
    (hcanonComet : (claimCometWord I).toNat < EVM.addressModulus)
    (hcanonSrc : (claimSrcWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((claimClaimedOuterHashMem I slot0 multiplier)
          |>.readWithPadding 0 64))) =
      getRewardOwedRewardsClaimedSlotOf I := by
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((claimClaimedOuterHashMem I slot0 multiplier)
            |>.readWithPadding 0 64))) =
        solcMappingSlot
          (solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask))
          (UInt256.land (claimSrcWord I) solcAddrMask) := by
    unfold claimClaimedOuterHashMem
    exact twoWordHashMem_solcMappingSlot_of_ge
      (solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask))
      (UInt256.land (claimSrcWord I) solcAddrMask)
      (le_trans (by norm_num) <| claimClaimedInnerHashMem_size_ge256 I slot0 multiplier)
  rw [hhash]
  rw [solcAddrMask_clean
      (by simpa [claimCometWord, calldataWord] using hcanonComet)]
  rw [solcAddrMask_clean
      (by simpa [claimSrcWord, calldataWord] using hcanonSrc)]
  rw [getRewardOwedRewardsClaimedSlotOf_eq_solc I
    (by simpa [getRewardOwedCometWord, claimCometWord] using hcanonComet)
    (by simpa [getRewardOwedAccountWord, claimSrcWord] using hcanonSrc)]

theorem claimBaseTrackingSelectorMem_size_ge288
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    288 ≤ (claimBaseTrackingSelectorMem I slot0 multiplier).size := by
  unfold claimBaseTrackingSelectorMem
  have hsize := writeWord_size
    (claimClaimedOuterHashMem I slot0 multiplier) 256
    (UInt256.shiftLeft (⟨719776253⟩ : UInt256) ⟨226⟩)
    (by
      have hge := claimClaimedOuterHashMem_size_ge256 I slot0 multiplier
      have hle : 256 - (claimClaimedOuterHashMem I slot0 multiplier).size = 0 := by
        omega
      rw [hle]
      native_decide)
  rw [hsize]
  exact le_max_right _ _

theorem claimBaseTrackingCalldataMem_size_ge292
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    292 ≤ (claimBaseTrackingCalldataMem I slot0 multiplier).size := by
  unfold claimBaseTrackingCalldataMem
  have hsize := writeWord_size
    (claimBaseTrackingSelectorMem I slot0 multiplier) 260 (claimSrcWord I)
    (by
      have hge := claimBaseTrackingSelectorMem_size_ge288 I slot0 multiplier
      have hle : 260 - (claimBaseTrackingSelectorMem I slot0 multiplier).size = 0 := by
        omega
      rw [hle]
      native_decide)
  rw [hsize]
  have hge := claimBaseTrackingSelectorMem_size_ge288 I slot0 multiplier
  omega

theorem claimBaseTrackingCalldataMem_read256_4
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (claimBaseTrackingCalldataMem I slot0 multiplier).readWithPadding 256 4 =
      baseTrackingAccruedSelector := by
  unfold claimBaseTrackingCalldataMem
  unfold Reasoning.Theory.writeWord
  rw [write32_read_below_len _ _ 260 256 4 (by rw [toByteArray_size])
      (by
        have hge := claimBaseTrackingSelectorMem_size_ge288 I slot0 multiplier
        omega)
      (by norm_num)
      (by
        have hge := claimBaseTrackingSelectorMem_size_ge288 I slot0 multiplier
        omega)
      (by norm_num) (by norm_num)]
  unfold claimBaseTrackingSelectorMem
  rw [writeWord_read_window
      (claimClaimedOuterHashMem I slot0 multiplier) 256 0 4
      (UInt256.shiftLeft (⟨719776253⟩ : UInt256) ⟨226⟩)
      (by norm_num) (by norm_num) (by norm_num)
      (by
        have hge := claimClaimedOuterHashMem_size_ge256 I slot0 multiplier
        have hle : 256 - (claimClaimedOuterHashMem I slot0 multiplier).size = 0 := by
          omega
        rw [hle]
        native_decide)]
  native_decide

theorem claimBaseTrackingCalldataMem_read260_32
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (claimBaseTrackingCalldataMem I slot0 multiplier).readWithPadding 260 32 =
      UInt256.toByteArray (claimSrcWord I) := by
  unfold claimBaseTrackingCalldataMem
  unfold Reasoning.Theory.writeWord
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by
        have hge := claimBaseTrackingSelectorMem_size_ge288 I slot0 multiplier
        omega)]
  exact toByteArray_extract_all (claimSrcWord I)

theorem claimBaseTrackingCalldataMem_read256_36
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (claimBaseTrackingCalldataMem I slot0 multiplier).readWithPadding 256 36 =
      baseTrackingAccruedSelector ++ UInt256.toByteArray (claimSrcWord I) := by
  rw [byteArray_readWithPadding_split _ 256 4 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by exact claimBaseTrackingCalldataMem_size_ge292 I slot0 multiplier)]
  rw [claimBaseTrackingCalldataMem_read256_4 I slot0 multiplier,
    claimBaseTrackingCalldataMem_read260_32 I slot0 multiplier]

set_option maxHeartbeats 1000000 in
theorem claimBaseTrackingCalldataMem_encode_args
    (I : ExecutionEnv) (slot0 multiplier : UInt256)
    (hcanonSrc : (claimSrcWord I).toNat < EVM.addressModulus) :
    config.externalABI.encode? "baseTrackingAccrued" (getRewardAccruedBaseTrackingArgs I) =
      some ((claimBaseTrackingCalldataMem I slot0 multiplier)
        |>.readWithPadding 256 claimBaseTrackingCallSize.toNat) := by
  rw [show claimBaseTrackingCallSize.toNat = 36 from rfl]
  rw [claimBaseTrackingCalldataMem_read256_36 I slot0 multiplier]
  change compoundRewardsExternalABI.encode? "baseTrackingAccrued"
      (getRewardAccruedBaseTrackingArgs I) =
    some (baseTrackingAccruedSelector ++ UInt256.toByteArray (claimSrcWord I))
  have haccountWord :
      EVM.word (AccountAddress.ofNat (claimSrcWord I).toNat).val = claimSrcWord I := by
    change UInt256.ofNat (AccountAddress.ofNat (claimSrcWord I).toNat).val = claimSrcWord I
    have haddr :
        (AccountAddress.ofNat (claimSrcWord I).toNat).val = (claimSrcWord I).toNat := by
      have hcanonAddr : (claimSrcWord I).toNat < AccountAddress.size := by
        simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanonSrc
      unfold AccountAddress.ofNat
      exact Nat.mod_eq_of_lt hcanonAddr
    rw [haddr]
    exact u256_ofNat_toNat (claimSrcWord I)
  unfold compoundRewardsExternalABI ABI.encodeCallWithSelector? ABI.encodeABIValues?
  simp [getRewardAccruedBaseTrackingArgs, getRewardOwedAccountValue, getRewardOwedAccountWord,
    claimSrcValue, claimSrcWord, addr, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
    ABI.isDynamicABIType, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.encodeABIValuesFrom?,
    haccountWord, word_toBytesBE_toByteArray_eq_toByteArray]

theorem claimBaseTrackingSelectorMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (claimBaseTrackingSelectorMem I slot0 multiplier).readWithPadding 64 32 =
      UInt256.toByteArray (⟨256⟩ : UInt256) := by
  unfold claimBaseTrackingSelectorMem
  exact (writeWord_read_preserved
    (claimClaimedOuterHashMem I slot0 multiplier) 256 64
    (UInt256.shiftLeft (⟨719776253⟩ : UInt256) ⟨226⟩)
    (by
      have hge := claimClaimedOuterHashMem_size_ge256 I slot0 multiplier
      have hle : 256 - (claimClaimedOuterHashMem I slot0 multiplier).size = 0 := by
        omega
      rw [hle]
      native_decide)
    (by
      have hge := claimClaimedOuterHashMem_size_ge256 I slot0 multiplier
      left
      constructor <;> omega)
    ).trans (claimClaimedOuterHashMem_read64 I slot0 multiplier)

theorem claimBaseTrackingCalldataMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (claimBaseTrackingCalldataMem I slot0 multiplier).readWithPadding 64 32 =
      UInt256.toByteArray (⟨256⟩ : UInt256) := by
  unfold claimBaseTrackingCalldataMem
  exact (writeWord_read_preserved
    (claimBaseTrackingSelectorMem I slot0 multiplier) 260 64 (claimSrcWord I)
    (by
      have hge := claimBaseTrackingSelectorMem_size_ge288 I slot0 multiplier
      have hle : 260 - (claimBaseTrackingSelectorMem I slot0 multiplier).size = 0 := by
        omega
      rw [hle]
      native_decide)
    (by
      have hge := claimBaseTrackingSelectorMem_size_ge288 I slot0 multiplier
      left
      constructor <;> omega)
    ).trans (claimBaseTrackingSelectorMem_read64 I slot0 multiplier)

theorem claimBaseTrackingPostCallMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).readWithPadding 64 32 =
      UInt256.toByteArray (⟨256⟩ : UInt256) := by
  unfold claimBaseTrackingPostCallMem
  by_cases hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat = 0
  · rw [hlen, byteArray_write_len_zero]
    exact claimBaseTrackingCalldataMem_read64 I slot0 multiplier
  · have hsrc :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat ≤ baseOut.size :=
      getRewardOwedPostCallLen_le_out_size hbaseSize
    rw [write_read_below_gen_extend baseOut
      (claimBaseTrackingCalldataMem I slot0 multiplier) 256
      (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat 64
      hlen hsrc
      (by
        have hge := claimBaseTrackingCalldataMem_size_ge292 I slot0 multiplier
        omega)
      (by norm_num)]
    exact claimBaseTrackingCalldataMem_read64 I slot0 multiplier

theorem claimBaseTrackingPostCallMem_size_ge256
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    256 ≤ (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size := by
  unfold claimBaseTrackingPostCallMem
  by_cases hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat = 0
  · rw [hlen, byteArray_write_len_zero]
    have hge := claimBaseTrackingCalldataMem_size_ge292 I slot0 multiplier
    omega
  · have hsrc :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat ≤ baseOut.size :=
      getRewardOwedPostCallLen_le_out_size hbaseSize
    let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat
    let base := claimBaseTrackingCalldataMem I slot0 multiplier
    have hdest : 256 ≤ base.size := by
      have hge := claimBaseTrackingCalldataMem_size_ge292 I slot0 multiplier
      simpa [base] using le_trans (by norm_num : 256 ≤ 292) hge
    by_cases hin : 256 + len ≤ base.size
    · rw [write_eq_gen baseOut base 256 len (by simpa [len] using hlen)
        (by simpa [len] using hsrc) hin]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract]
      omega
    · have hext : base.size < 256 + len := Nat.lt_of_not_ge hin
      rw [write_eq_gen_extend baseOut base 256 len (by simpa [len] using hlen)
        (by simpa [len] using hsrc) hdest hext]
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega

theorem claimBaseTrackingPostCallMem_read256_of_size_ge
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).readWithPadding 256 32 =
      baseOut.extract 0 32 := by
  unfold claimBaseTrackingPostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := baseOut.size)
      (by decide) hout32 hbaseSize
  rw [hlen]
  exact write32_read_back baseOut
    (claimBaseTrackingCalldataMem I slot0 multiplier)
    256 hout32
    (by
      have hge := claimBaseTrackingCalldataMem_size_ge292 I slot0 multiplier
      omega)

theorem claimBaseTrackingPostCallMem_size_ge288
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    288 ≤ (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size := by
  unfold claimBaseTrackingPostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := baseOut.size)
      (by decide) hout32 hbaseSize
  rw [hlen]
  rw [write32_eq baseOut (claimBaseTrackingCalldataMem I slot0 multiplier)
    256 hout32
    (by
      have hge := claimBaseTrackingCalldataMem_size_ge292 I slot0 multiplier
      omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract]
  have hbase := claimBaseTrackingCalldataMem_size_ge292 I slot0 multiplier
  omega

theorem claimBaseTrackingPostCallMem_size_ge292
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    292 ≤ (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size := by
  unfold claimBaseTrackingPostCallMem
  by_cases hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat = 0
  · rw [hlen, byteArray_write_len_zero]
    exact claimBaseTrackingCalldataMem_size_ge292 I slot0 multiplier
  · have hsrc :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat ≤ baseOut.size :=
      getRewardOwedPostCallLen_le_out_size hbaseSize
    let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat
    let base := claimBaseTrackingCalldataMem I slot0 multiplier
    have hbase292 : 292 ≤ base.size := by
      simpa [base] using claimBaseTrackingCalldataMem_size_ge292 I slot0 multiplier
    have hdest : 256 ≤ base.size := le_trans (by norm_num) hbase292
    by_cases hin : 256 + len ≤ base.size
    · rw [write_eq_gen baseOut base 256 len (by simpa [len] using hlen)
        (by simpa [len] using hsrc) hin]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract]
      omega
    · have hext : base.size < 256 + len := Nat.lt_of_not_ge hin
      rw [write_eq_gen_extend baseOut base 256 len (by simpa [len] using hlen)
        (by simpa [len] using hsrc) hdest hext]
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega

theorem claimBaseTrackingPostCallMem_mload256_haw :
    ¬ (⟨256⟩ : UInt256) ≥ claimBaseTrackingPostCallAw * ⟨32⟩ := by
  native_decide

theorem claimBaseTrackingPostDecodeMem_read256_of_size_ge
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).readWithPadding 256 32 =
      baseOut.extract 0 32 := by
  unfold claimBaseTrackingPostDecodeMem
  rw [writeWord_read_preserved]
  · exact claimBaseTrackingPostCallMem_read256_of_size_ge
      I slot0 multiplier hout32 hbaseSize
  · have hge := claimBaseTrackingPostCallMem_size_ge288
      I slot0 multiplier hout32 hbaseSize
    have hle :
        64 - (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size = 0 := by
      omega
    rw [hle]
    native_decide
  · right
    have hge := claimBaseTrackingPostCallMem_size_ge288
      I slot0 multiplier hout32 hbaseSize
    constructor <;> omega

theorem claimBaseTrackingPostDecodeMem_mload256_of_size_ge
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨256⟩ : UInt256).toNat ≥
          (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).size
        ∨ (⟨256⟩ : UInt256) ≥ claimBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
          |>.readWithPadding (⟨256⟩ : UInt256).toNat 32))) =
      claimBaseTrackingReturnWord baseOut := by
  trans UInt256.ofNat
    (fromByteArrayBigEndian
      ((claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).readWithPadding
        (⟨256⟩ : UInt256).toNat 32))
  · exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
      (aw := claimBaseTrackingPostCallAw)
      (off := ⟨256⟩)
      (memSize := (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).size)
      rfl
      (by
        rw [show (⟨256⟩ : UInt256).toNat = 256 from by decide]
        unfold claimBaseTrackingPostDecodeMem
        rw [writeWord_size]
        · have hsz := claimBaseTrackingPostCallMem_size_ge288
            I slot0 multiplier hout32 hbaseSize
          omega
        · have hsz := claimBaseTrackingPostCallMem_size_ge288
            I slot0 multiplier hout32 hbaseSize
          have hle :
              64 - (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size = 0 := by
            omega
          rw [hle]
          native_decide)
      claimBaseTrackingPostCallMem_mload256_haw
  · rw [show (⟨256⟩ : UInt256).toNat = 256 from by decide,
      claimBaseTrackingPostDecodeMem_read256_of_size_ge
        I slot0 multiplier hout32 hbaseSize]

theorem claimBaseTrackingPostCallMem_read_below256
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) {read : ℕ} (hbelow : read + 32 ≤ 256) :
    (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).readWithPadding read 32 =
      (claimBaseTrackingCalldataMem I slot0 multiplier).readWithPadding read 32 := by
  unfold claimBaseTrackingPostCallMem
  by_cases hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat = 0
  · rw [hlen, byteArray_write_len_zero]
  · have hsrc :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat ≤ baseOut.size :=
      getRewardOwedPostCallLen_le_out_size hbaseSize
    rw [write_read_below_gen_extend baseOut
      (claimBaseTrackingCalldataMem I slot0 multiplier) 256
      (min (⟨32⟩ : UInt256) (UInt256.ofNat baseOut.size)).toNat read
      hlen hsrc
      (by
        have hge := claimBaseTrackingCalldataMem_size_ge292 I slot0 multiplier
        omega)
      hbelow]

theorem claimConfigMultiplierMem_read128
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (claimConfigMultiplierMem I slot0 multiplier).readWithPadding 128 32 =
      UInt256.toByteArray (rewardConfigTokenFromSlot0 slot0) := by
  unfold claimConfigMultiplierMem
  rw [writeWord_read_preserved]
  · unfold claimConfigShouldMem
    rw [writeWord_read_preserved]
    · unfold claimConfigRescaleMem
      rw [writeWord_read_preserved]
      · unfold claimConfigTokenMem
        exact writeWord_read_back (claimConfigAllocMem I) 128
          (rewardConfigTokenFromSlot0 slot0)
          (by rw [claimConfigAllocMem_size]; native_decide)
      · rw [claimConfigTokenMem_size]
        native_decide
      · left
        rw [claimConfigTokenMem_size]
        constructor <;> norm_num
    · rw [claimConfigRescaleMem_size]
      native_decide
    · left
      rw [claimConfigRescaleMem_size]
      constructor <;> norm_num
  · rw [claimConfigShouldMem_size]
    native_decide
  · left
    rw [claimConfigShouldMem_size]
    constructor <;> norm_num

theorem claimConfigMultiplierMem_read160
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (claimConfigMultiplierMem I slot0 multiplier).readWithPadding 160 32 =
      UInt256.toByteArray (rewardConfigRescaleFromSlot0 slot0) := by
  unfold claimConfigMultiplierMem
  rw [writeWord_read_preserved]
  · unfold claimConfigShouldMem
    rw [writeWord_read_preserved]
    · unfold claimConfigRescaleMem
      exact writeWord_read_back (claimConfigTokenMem I slot0) 160
        (rewardConfigRescaleFromSlot0 slot0)
        (by rw [claimConfigTokenMem_size]; native_decide)
    · rw [claimConfigRescaleMem_size]
      native_decide
    · left
      rw [claimConfigRescaleMem_size]
      constructor <;> norm_num
  · rw [claimConfigShouldMem_size]
    native_decide
  · left
    rw [claimConfigShouldMem_size]
    constructor <;> norm_num

theorem claimConfigMultiplierMem_read192
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (claimConfigMultiplierMem I slot0 multiplier).readWithPadding 192 32 =
      UInt256.toByteArray (rewardConfigShouldUpscaleFromSlot0 slot0) := by
  unfold claimConfigMultiplierMem
  rw [writeWord_read_preserved]
  · unfold claimConfigShouldMem
    exact writeWord_read_back (claimConfigRescaleMem I slot0) 192
      (rewardConfigShouldUpscaleFromSlot0 slot0)
      (by rw [claimConfigRescaleMem_size]; native_decide)
  · rw [claimConfigShouldMem_size]
    native_decide
  · left
    rw [claimConfigShouldMem_size]
    constructor <;> norm_num

theorem claimConfigMultiplierMem_read224
    (I : ExecutionEnv) (slot0 multiplier : UInt256) :
    (claimConfigMultiplierMem I slot0 multiplier).readWithPadding 224 32 =
      UInt256.toByteArray multiplier := by
  unfold claimConfigMultiplierMem
  exact writeWord_read_back (claimConfigShouldMem I slot0) 224 multiplier
    (by rw [claimConfigShouldMem_size]; native_decide)

theorem claimBaseTrackingCalldataMem_read_config
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {read : ℕ}
    (hbelow : read + 32 ≤ 256) (habove : 64 ≤ read) {val : UInt256}
    (hcfg :
      (claimConfigMultiplierMem I slot0 multiplier).readWithPadding read 32 =
        UInt256.toByteArray val) :
    (claimBaseTrackingCalldataMem I slot0 multiplier).readWithPadding read 32 =
      UInt256.toByteArray val := by
  unfold claimBaseTrackingCalldataMem
  rw [writeWord_read_preserved]
  · unfold claimBaseTrackingSelectorMem
    rw [writeWord_read_preserved]
    · unfold claimClaimedOuterHashMem
      rw [twoWordHashMem_read_above64_of_ge]
      · unfold claimClaimedInnerHashMem
        rw [twoWordHashMem_read_above64_of_ge]
        · exact hcfg
        · have hge := claimConfigMultiplierMem_size I slot0 multiplier
          omega
        · exact habove
      · have hge := claimClaimedInnerHashMem_size_ge256 I slot0 multiplier
        omega
      · exact habove
    · have hge := claimClaimedOuterHashMem_size_ge256 I slot0 multiplier
      have hle : 256 - (claimClaimedOuterHashMem I slot0 multiplier).size = 0 := by
        omega
      rw [hle]
      native_decide
    · left
      have hge := claimClaimedOuterHashMem_size_ge256 I slot0 multiplier
      constructor <;> omega
  · have hge := claimBaseTrackingSelectorMem_size_ge288 I slot0 multiplier
    have hle : 260 - (claimBaseTrackingSelectorMem I slot0 multiplier).size = 0 := by
      omega
    rw [hle]
    native_decide
  · left
    have hge := claimBaseTrackingSelectorMem_size_ge288 I slot0 multiplier
    constructor <;> omega

theorem claimBaseTrackingPostDecodeMem_read_config
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) {read : ℕ}
    (hbelow : read + 32 ≤ 256) (habove : 96 ≤ read) {val : UInt256}
    (hcfg :
      (claimConfigMultiplierMem I slot0 multiplier).readWithPadding read 32 =
        UInt256.toByteArray val) :
    (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).readWithPadding read 32 =
      UInt256.toByteArray val := by
  unfold claimBaseTrackingPostDecodeMem
  rw [writeWord_read_preserved]
  · rw [claimBaseTrackingPostCallMem_read_below256 I slot0 multiplier hbaseSize hbelow]
    exact claimBaseTrackingCalldataMem_read_config I slot0 multiplier hbelow
      (by omega) hcfg
  · have hge := claimBaseTrackingPostCallMem_size_ge256 I slot0 multiplier hbaseSize
    have hle :
        64 - (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size = 0 := by
      omega
    rw [hle]
    native_decide
  · right
    have hge := claimBaseTrackingPostCallMem_size_ge256 I slot0 multiplier hbaseSize
    constructor <;> omega

theorem claimBaseTrackingPostDecodeMem_read128
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).readWithPadding 128 32 =
      UInt256.toByteArray (rewardConfigTokenFromSlot0 slot0) :=
  claimBaseTrackingPostDecodeMem_read_config I slot0 multiplier hbaseSize
    (by norm_num) (by norm_num) (claimConfigMultiplierMem_read128 I slot0 multiplier)

theorem claimBaseTrackingPostDecodeMem_read160
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).readWithPadding 160 32 =
      UInt256.toByteArray (rewardConfigRescaleFromSlot0 slot0) :=
  claimBaseTrackingPostDecodeMem_read_config I slot0 multiplier hbaseSize
    (by norm_num) (by norm_num) (claimConfigMultiplierMem_read160 I slot0 multiplier)

theorem claimBaseTrackingPostDecodeMem_read192
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).readWithPadding 192 32 =
      UInt256.toByteArray (rewardConfigShouldUpscaleFromSlot0 slot0) :=
  claimBaseTrackingPostDecodeMem_read_config I slot0 multiplier hbaseSize
    (by norm_num) (by norm_num) (claimConfigMultiplierMem_read192 I slot0 multiplier)

theorem claimBaseTrackingPostDecodeMem_read224
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).readWithPadding 224 32 =
      UInt256.toByteArray multiplier :=
  claimBaseTrackingPostDecodeMem_read_config I slot0 multiplier hbaseSize
    (by norm_num) (by norm_num) (claimConfigMultiplierMem_read224 I slot0 multiplier)

theorem claimBaseTrackingPostDecodeMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).readWithPadding 64 32 =
      UInt256.toByteArray (⟨288⟩ : UInt256) := by
  unfold claimBaseTrackingPostDecodeMem
  exact writeWord_read_back (claimBaseTrackingPostCallMem I slot0 multiplier baseOut) 64
    (⟨288⟩ : UInt256)
    (by
      have hge := claimBaseTrackingPostCallMem_size_ge256 I slot0 multiplier hbaseSize
      have hle : 64 - (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size = 0 := by
        omega
      rw [hle]
      native_decide)

theorem claimBaseTrackingPostDecodeMem_mload64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).size
        ∨ (⟨64⟩ : UInt256) ≥ claimBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
          |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨288⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := claimBaseTrackingPostCallAw)
    (v := ⟨288⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      unfold claimBaseTrackingPostDecodeMem
      rw [writeWord_size]
      · have hge := claimBaseTrackingPostCallMem_size_ge256 I slot0 multiplier hbaseSize
        omega
      · have hge := claimBaseTrackingPostCallMem_size_ge256 I slot0 multiplier hbaseSize
        have hle :
            64 - (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size = 0 := by
          omega
        rw [hle]
        native_decide)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      exact claimBaseTrackingPostDecodeMem_read64 I slot0 multiplier hbaseSize)

theorem claimBaseTrackingPostDecodeMem_size_ge292
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    292 ≤ (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).size := by
  unfold claimBaseTrackingPostDecodeMem
  rw [writeWord_size]
  · have hge := claimBaseTrackingPostCallMem_size_ge292 I slot0 multiplier hbaseSize
    omega
  · have hge := claimBaseTrackingPostCallMem_size_ge292 I slot0 multiplier hbaseSize
    have hle :
        64 - (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size = 0 := by
      omega
    rw [hle]
    native_decide

theorem claimTransferInnerHashMem_size_ge292
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    292 ≤ (claimTransferInnerHashMem I slot0 multiplier baseOut).size := by
  unfold claimTransferInnerHashMem
  rw [twoWordHashMem_size_of_ge]
  · exact claimBaseTrackingPostDecodeMem_size_ge292 I slot0 multiplier hbaseSize
  · have hge := claimBaseTrackingPostDecodeMem_size_ge292 I slot0 multiplier hbaseSize
    omega

theorem claimTransferOuterHashMem_size_ge292
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    292 ≤ (claimTransferOuterHashMem I slot0 multiplier baseOut).size := by
  unfold claimTransferOuterHashMem
  rw [twoWordHashMem_size_of_ge]
  · exact claimTransferInnerHashMem_size_ge292 I slot0 multiplier hbaseSize
  · have hge := claimTransferInnerHashMem_size_ge292 I slot0 multiplier hbaseSize
    omega

theorem claimTransferInnerHashMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    (claimTransferInnerHashMem I slot0 multiplier baseOut).readWithPadding 64 32 =
      UInt256.toByteArray (⟨288⟩ : UInt256) := by
  unfold claimTransferInnerHashMem
  rw [twoWordHashMem_read64_of_ge]
  · exact claimBaseTrackingPostDecodeMem_read64 I slot0 multiplier hbaseSize
  · have hge := claimBaseTrackingPostDecodeMem_size_ge292 I slot0 multiplier hbaseSize
    omega

theorem claimTransferOuterHashMem_read64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    (claimTransferOuterHashMem I slot0 multiplier baseOut).readWithPadding 64 32 =
      UInt256.toByteArray (⟨288⟩ : UInt256) := by
  unfold claimTransferOuterHashMem
  rw [twoWordHashMem_read64_of_ge]
  · exact claimTransferInnerHashMem_read64 I slot0 multiplier hbaseSize
  · have hge := claimTransferInnerHashMem_size_ge292 I slot0 multiplier hbaseSize
    omega

theorem claimTransferOuterHashMem_mload64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (claimTransferOuterHashMem I slot0 multiplier baseOut).size
        ∨ (⟨64⟩ : UInt256) ≥ claimBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((claimTransferOuterHashMem I slot0 multiplier baseOut)
          |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨288⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := claimBaseTrackingPostCallAw)
    (v := ⟨288⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      have hge := claimTransferOuterHashMem_size_ge292 I slot0 multiplier hbaseSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      exact claimTransferOuterHashMem_read64 I slot0 multiplier hbaseSize)

theorem claimTransferSelectorMem_size_ge320
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    320 ≤ (claimTransferSelectorMem I slot0 multiplier baseOut).size := by
  unfold claimTransferSelectorMem
  exact toByteArray_write_size_ge_off_add32 withdrawTokenTransferSelectorShifted
    (claimTransferOuterHashMem I slot0 multiplier baseOut) 288
    (lt_of_le_of_lt (Nat.sub_le 288 _) (by native_decide))

theorem claimTransferArgsMem_size_ge324
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (recipient : UInt256) (hbaseSize : baseOut.size < UInt256.size) :
    324 ≤ (claimTransferArgsMem I slot0 multiplier baseOut recipient).size := by
  unfold claimTransferArgsMem
  exact toByteArray_write_size_ge_off_add32 recipient
    (claimTransferSelectorMem I slot0 multiplier baseOut) 292
    (lt_of_le_of_lt (Nat.sub_le 292 _) (by native_decide))

theorem claimTransferCalldataMem_size_ge356
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (recipient value : UInt256) (hbaseSize : baseOut.size < UInt256.size) :
    356 ≤ (claimTransferCalldataMem I slot0 multiplier baseOut recipient value).size := by
  unfold claimTransferCalldataMem
  exact toByteArray_write_size_ge_off_add32 value
    (claimTransferArgsMem I slot0 multiplier baseOut recipient) 324
    (lt_of_le_of_lt (Nat.sub_le 324 _) (by native_decide))

theorem claimTransferCalldataMem_read288_4
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (recipient value : UInt256) (hbaseSize : baseOut.size < UInt256.size) :
    (claimTransferCalldataMem I slot0 multiplier baseOut recipient value).readWithPadding
      288 4 = transferSelector := by
  unfold claimTransferCalldataMem
  rw [write32_read_below_len _ _ 324 288 4 (by rw [toByteArray_size])
      (by exact claimTransferArgsMem_size_ge324 I slot0 multiplier recipient hbaseSize)
      (by omega)
      (by
        have hge := claimTransferArgsMem_size_ge324 I slot0 multiplier recipient hbaseSize
        omega)
      (by norm_num) (by norm_num)]
  unfold claimTransferArgsMem
  rw [write32_read_below_len _ _ 292 288 4 (by rw [toByteArray_size])
      (by
        have hge := claimTransferSelectorMem_size_ge320 I slot0 multiplier hbaseSize
        omega)
      (by omega)
      (by
        have hge := claimTransferSelectorMem_size_ge320 I slot0 multiplier hbaseSize
        omega)
      (by norm_num) (by norm_num)]
  unfold claimTransferSelectorMem
  rw [write32_read_prefix_len _ _ 288 4 (by rw [toByteArray_size])
      (by
        have hge := claimTransferOuterHashMem_size_ge292 I slot0 multiplier hbaseSize
        omega)
      (by norm_num) (by norm_num) (by norm_num)]
  native_decide

theorem claimTransferCalldataMem_read292_32
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (recipient value : UInt256) (hbaseSize : baseOut.size < UInt256.size) :
    (claimTransferCalldataMem I slot0 multiplier baseOut recipient value).readWithPadding
      292 32 = UInt256.toByteArray recipient := by
  unfold claimTransferCalldataMem
  rw [write32_read_below _ _ 324 292 (by rw [toByteArray_size])
      (by exact claimTransferArgsMem_size_ge324 I slot0 multiplier recipient hbaseSize)
      (by omega)]
  unfold claimTransferArgsMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by
        have hge := claimTransferSelectorMem_size_ge320 I slot0 multiplier hbaseSize
        omega)]
  exact toByteArray_extract_all recipient

theorem claimTransferCalldataMem_read324_32
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (recipient value : UInt256) (hbaseSize : baseOut.size < UInt256.size) :
    (claimTransferCalldataMem I slot0 multiplier baseOut recipient value).readWithPadding
      324 32 = UInt256.toByteArray value := by
  unfold claimTransferCalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by exact claimTransferArgsMem_size_ge324 I slot0 multiplier recipient hbaseSize)]
  exact toByteArray_extract_all value

theorem claimTransferCalldataMem_read288_68
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (recipient value : UInt256) (hbaseSize : baseOut.size < UInt256.size) :
    (claimTransferCalldataMem I slot0 multiplier baseOut recipient value).readWithPadding
      288 68 =
        transferSelector ++ UInt256.toByteArray recipient ++ UInt256.toByteArray value := by
  rw [byteArray_readWithPadding_split _ 288 4 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by exact claimTransferCalldataMem_size_ge356 I slot0 multiplier recipient value hbaseSize)]
  rw [byteArray_readWithPadding_split _ 292 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by exact claimTransferCalldataMem_size_ge356 I slot0 multiplier recipient value hbaseSize)]
  rw [claimTransferCalldataMem_read288_4 I slot0 multiplier recipient value hbaseSize,
    claimTransferCalldataMem_read292_32 I slot0 multiplier recipient value hbaseSize,
    claimTransferCalldataMem_read324_32 I slot0 multiplier recipient value hbaseSize,
    ByteArray.append_assoc]

theorem claimTransferCalldataMem_encode
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (recipient : AccountAddress) (value : UInt256)
    (hbaseSize : baseOut.size < UInt256.size) :
    config.externalABI.encode? "transfer"
        [.address recipient, .int (Int.ofNat value.toNat)] =
      some ((claimTransferCalldataMem I slot0 multiplier baseOut
        (UInt256.ofNat recipient.val) value).readWithPadding 288 68) := by
  rw [claimTransferCalldataMem_read288_68 I slot0 multiplier
    (UInt256.ofNat recipient.val) value hbaseSize]
  change compoundRewardsExternalABI.encode? "transfer"
      [.address recipient, .int (Int.ofNat value.toNat)] =
    some (transferSelector ++
      (UInt256.ofNat recipient.val).toByteArray ++ UInt256.toByteArray value)
  have hvalueWord : EVM.word value.toNat = value := by
    exact u256_ofNat_toNat value
  have hrecipientWord : EVM.word recipient.val = UInt256.ofNat recipient.val := by
    apply u256_inj
    rfl
  have hvalueLt : value.toNat < EVM.twoPow 256 := by
    change value.val.val < UInt256.size
    exact value.val.isLt
  unfold compoundRewardsExternalABI ABI.encodeCallWithSelector? ABI.encodeABIValues?
  simp [addr, uint256, uint256Int, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
    ABI.isDynamicABIType, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.encodeABIValuesFrom?,
    hvalueLt, hrecipientWord, hvalueWord, word_toBytesBE_toByteArray_eq_toByteArray]
  rw [ByteArray.append_assoc]

set_option maxHeartbeats 1000000 in
theorem claimTransferCalldataMem_encode_args
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (amount : UInt256) (hbaseSize : baseOut.size < UInt256.size)
    (hcanonSrc : (claimSrcWord I).toNat < EVM.addressModulus) :
    config.externalABI.encode? "transfer" (claimTransferArgs I amount) =
      some ((claimTransferCalldataMem I slot0 multiplier baseOut
        (claimSrcWord I) amount).readWithPadding 288 claimTransferCallSize.toNat) := by
  have hsz : claimTransferCallSize.toNat = 68 := by
    unfold claimTransferCallSize
    rw [withdrawTokenTransferCallSize_eq]
    rfl
  rw [hsz]
  have hround :
      UInt256.ofNat (AccountAddress.ofNat (claimSrcWord I).toNat).val =
        claimSrcWord I :=
    u256_of_accountAddress_ofNat_toNat_of_canonical hcanonSrc
  have henc := claimTransferCalldataMem_encode
    (I := I) (slot0 := slot0) (multiplier := multiplier)
    (baseOut := baseOut)
    (recipient := AccountAddress.ofNat (claimSrcWord I).toNat)
    (value := amount) hbaseSize
  change config.externalABI.encode? "transfer"
      [.address (AccountAddress.ofNat (claimSrcWord I).toNat),
        .int (Int.ofNat amount.toNat)] =
    some ((claimTransferCalldataMem I slot0 multiplier baseOut
      (claimSrcWord I) amount).readWithPadding 288 68)
  rw [hround] at henc
  exact henc

theorem claimBaseTrackingPostDecodeMem_mload128
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).size
        ∨ (⟨128⟩ : UInt256) ≥ claimBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
          |>.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      rewardConfigTokenFromSlot0 slot0 := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := claimBaseTrackingPostCallAw)
    (v := rewardConfigTokenFromSlot0 slot0)
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      unfold claimBaseTrackingPostDecodeMem
      rw [writeWord_size]
      · have hge := claimBaseTrackingPostCallMem_size_ge288
          I slot0 multiplier hout32 hbaseSize
        omega
      · have hge := claimBaseTrackingPostCallMem_size_ge288
          I slot0 multiplier hout32 hbaseSize
        have hle :
            64 - (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size = 0 := by
          omega
        rw [hle]
        native_decide)
    (by native_decide)
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      exact claimBaseTrackingPostDecodeMem_read128 I slot0 multiplier hbaseSize)

theorem claimBaseTrackingPostDecodeMem_mload160
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨160⟩ : UInt256).toNat ≥
          (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).size
        ∨ (⟨160⟩ : UInt256) ≥ claimBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
          |>.readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
      rewardConfigRescaleFromSlot0 slot0 := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨160⟩ : UInt256)) (aw := claimBaseTrackingPostCallAw)
    (v := rewardConfigRescaleFromSlot0 slot0)
    (by
      rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]
      unfold claimBaseTrackingPostDecodeMem
      rw [writeWord_size]
      · have hge := claimBaseTrackingPostCallMem_size_ge288
          I slot0 multiplier hout32 hbaseSize
        omega
      · have hge := claimBaseTrackingPostCallMem_size_ge288
          I slot0 multiplier hout32 hbaseSize
        have hle :
            64 - (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size = 0 := by
          omega
        rw [hle]
        native_decide)
    (by native_decide)
    (by
      rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]
      exact claimBaseTrackingPostDecodeMem_read160 I slot0 multiplier hbaseSize)

theorem claimBaseTrackingPostDecodeMem_mload192
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨192⟩ : UInt256).toNat ≥
          (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).size
        ∨ (⟨192⟩ : UInt256) ≥ claimBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
          |>.readWithPadding (⟨192⟩ : UInt256).toNat 32))) =
      rewardConfigShouldUpscaleFromSlot0 slot0 := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨192⟩ : UInt256)) (aw := claimBaseTrackingPostCallAw)
    (v := rewardConfigShouldUpscaleFromSlot0 slot0)
    (by
      rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]
      unfold claimBaseTrackingPostDecodeMem
      rw [writeWord_size]
      · have hge := claimBaseTrackingPostCallMem_size_ge288
          I slot0 multiplier hout32 hbaseSize
        omega
      · have hge := claimBaseTrackingPostCallMem_size_ge288
          I slot0 multiplier hout32 hbaseSize
        have hle :
            64 - (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size = 0 := by
          omega
        rw [hle]
        native_decide)
    (by native_decide)
    (by
      rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]
      exact claimBaseTrackingPostDecodeMem_read192 I slot0 multiplier hbaseSize)

theorem claimBaseTrackingPostDecodeMem_mload224
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨224⟩ : UInt256).toNat ≥
          (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut).size
        ∨ (⟨224⟩ : UInt256) ≥ claimBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
          |>.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
      multiplier := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨224⟩ : UInt256)) (aw := claimBaseTrackingPostCallAw)
    (v := multiplier)
    (by
      rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
      unfold claimBaseTrackingPostDecodeMem
      rw [writeWord_size]
      · have hge := claimBaseTrackingPostCallMem_size_ge288
          I slot0 multiplier hout32 hbaseSize
        omega
      · have hge := claimBaseTrackingPostCallMem_size_ge288
          I slot0 multiplier hout32 hbaseSize
        have hle :
            64 - (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size = 0 := by
          omega
        rw [hle]
        native_decide)
    (by native_decide)
    (by
      rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
      exact claimBaseTrackingPostDecodeMem_read224 I slot0 multiplier hbaseSize)

theorem claimBaseTrackingPostCallMem_mload64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut : ByteArray}
    (hbaseSize : baseOut.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size
        ∨ (⟨64⟩ : UInt256) ≥ claimBaseTrackingPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((claimBaseTrackingPostCallMem I slot0 multiplier baseOut)
          |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨256⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := claimBaseTrackingPostCallAw)
    (v := ⟨256⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      have hge := claimBaseTrackingPostCallMem_size_ge256 I slot0 multiplier hbaseSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      exact claimBaseTrackingPostCallMem_read64 I slot0 multiplier hbaseSize)

theorem cometRewardsDecode_claim_ok {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (claimCometWord I).toNat < EVM.addressModulus)
    (hcanonSrc : (claimSrcWord I).toNat < EVM.addressModulus)
    (hbool : claimShouldAccrueWord I = ⟨0⟩ ∨ claimShouldAccrueWord I = ⟨1⟩) :
    decodeCalldataWithMode config.abiDecodeMode (claimTransition.params.map Param.name)
      (transitionSignature claimTransition).paramTypes I.calldata = some (claimStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "src", "shouldAccrue"]
    [addr, addr, boolTy] I.calldata = _
  change decodeCalldata ["comet", "src", "shouldAccrue"]
    [.elem .address, .elem .address, .elem .bool] I.calldata =
      some ((((∅ : Store).insert "comet"
        (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "src"
        (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))).insert
        "shouldAccrue" (wordToElem .bool (calldataWord I.calldata 68)))
  simpa [claimCometWord, claimSrcWord, claimShouldAccrueWord, calldataWord] using
    decodeCalldata_address_address_bool_ok (cd := I.calldata)
      (x := "comet") (y := "src") (z := "shouldAccrue") hsz100 hbig hcanonComet
      hcanonSrc hbool

theorem cometRewardsDecode_claim_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (claimTransition.params.map Param.name)
      (transitionSignature claimTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "src", "shouldAccrue"]
    [addr, addr, boolTy] I.calldata = none
  change decodeCalldata ["comet", "src", "shouldAccrue"]
    [.elem .address, .elem .address, .elem .bool] I.calldata = none
  exact decodeCalldata_address_address_bool_none_short
    (cd := I.calldata) (x := "comet") (y := "src") (z := "shouldAccrue") hsz4 hshort

theorem cometRewardsDecode_claim_none_noncanon_comet {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncComet : ¬ (claimCometWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (claimTransition.params.map Param.name)
      (transitionSignature claimTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "src", "shouldAccrue"]
    [addr, addr, boolTy] I.calldata = none
  change decodeCalldata ["comet", "src", "shouldAccrue"]
    [.elem .address, .elem .address, .elem .bool] I.calldata = none
  simpa [claimCometWord, calldataWord] using
    decodeCalldata_address_address_bool_none_noncanon0
      (cd := I.calldata) (x := "comet") (y := "src") (z := "shouldAccrue")
      hsz100 hbig hncComet

theorem cometRewardsDecode_claim_none_noncanon_src {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (claimCometWord I).toNat < EVM.addressModulus)
    (hncSrc : ¬ (claimSrcWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (claimTransition.params.map Param.name)
      (transitionSignature claimTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "src", "shouldAccrue"]
    [addr, addr, boolTy] I.calldata = none
  change decodeCalldata ["comet", "src", "shouldAccrue"]
    [.elem .address, .elem .address, .elem .bool] I.calldata = none
  simpa [claimCometWord, claimSrcWord, calldataWord] using
    decodeCalldata_address_address_bool_none_noncanon1
      (cd := I.calldata) (x := "comet") (y := "src") (z := "shouldAccrue")
      hsz100 hbig hcanonComet hncSrc

theorem cometRewardsDecode_claim_none_noncanon_bool {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (claimCometWord I).toNat < EVM.addressModulus)
    (hcanonSrc : (claimSrcWord I).toNat < EVM.addressModulus)
    (hnz : claimShouldAccrueWord I ≠ ⟨0⟩) (hno : claimShouldAccrueWord I ≠ ⟨1⟩) :
    decodeCalldataWithMode config.abiDecodeMode (claimTransition.params.map Param.name)
      (transitionSignature claimTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "src", "shouldAccrue"]
    [addr, addr, boolTy] I.calldata = none
  change decodeCalldata ["comet", "src", "shouldAccrue"]
    [.elem .address, .elem .address, .elem .bool] I.calldata = none
  simpa [claimCometWord, claimSrcWord, claimShouldAccrueWord, calldataWord] using
    decodeCalldata_address_address_bool_none_noncanon2
      (cd := I.calldata) (x := "comet") (y := "src") (z := "shouldAccrue")
      hsz100 hbig hcanonComet hcanonSrc hnz hno

theorem cometRewardsDecode_claim_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (claimTransition.params.map Param.name)
      (transitionSignature claimTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "src", "shouldAccrue"]
    [addr, addr, boolTy] I.calldata = none
  change decodeCalldata ["comet", "src", "shouldAccrue"]
    [.elem .address, .elem .address, .elem .bool] I.calldata = none
  exact decodeCalldata_address_address_bool_none_huge
    (cd := I.calldata) (x := "comet") (y := "src") (z := "shouldAccrue") hbig

theorem cometRewardsClaimSelector_size {I : ExecutionEnv}
    (hsel : selIs I (cometRewardsSelBytes 8)) :
    4 ≤ I.calldata.size :=
  calldata_size_ge_of_selIs I (cometRewardsSelBytes 8) rfl hsel

theorem cometRewardsDispatch_claim {cd : ByteArray}
    (hsel : (cometRewardsSelBytes 8 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some claimTransition := by
  refine dispatchMsg_eq_some_of_split
    (pre := [])
    (post := [claimToTransition, getRewardOwedTransition, governorTransition,
      rewardConfigTransition, rewardsClaimedTransition, setRewardConfigTransition,
      setRewardConfigWithMultiplierTransition, setRewardsClaimedTransition,
      transferGovernorTransition, withdrawTokenTransition])
    rfl rfl ?_ (by rw [selectorOf, claimSelectorBytes]; exact hsel)
  intro t ht
  simp at ht

theorem cometRewardsClaimCalldataCheckOk {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨96⟩ = ⟨0⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨96⟩ = ⟨0⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 (by omega) hsize]
  simpa using
    solcCalldataStaticLenCheckOk (sz := I.calldata.size) (words := 3)
      (by simpa using hsz100) hhi hsize

theorem cometRewardsClaimCalldataCheckShort {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨96⟩ = ⟨1⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨96⟩ = ⟨1⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 hsz4 hsize]
  simpa using
    solcCalldataStaticLenCheckShort (sz := I.calldata.size) (words := 3)
      hsz4 (by simpa using hshort) hsize (by norm_num)

theorem cometRewardsClaimCalldataCheckHuge {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨96⟩ = ⟨1⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨96⟩ = ⟨1⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 (by omega) hsize]
  simpa using
    solcCalldataStaticLenCheckHuge (sz := I.calldata.size) (words := 3)
      hbig hsize (by norm_num)

theorem cometRewardsClaimX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) claimPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsClaimCalldataCheckShort (I := I) hsz4 hsize hshort
  obtain ⟨_, _, rd942⟩ := hreach
  have rd951 := evm_run rd942 with [jumpdest, pop, pop, pop, callvalue]
  rw [hwv] at rd951
  have rd963 := evm_run rd951 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    push1 ⟨96⟩, calldatasize, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd963
  rw [hslt] at rd963
  exact evm_run rd963 with [
    push2 ⟨670⟩, jumpiT (by decide) (by native_decide),
    jumpdest, pop, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsClaimX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) claimPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsClaimCalldataCheckHuge (I := I) hsize hbig
  obtain ⟨_, _, rd942⟩ := hreach
  have rd951 := evm_run rd942 with [jumpdest, pop, pop, pop, callvalue]
  rw [hwv] at rd951
  have rd963 := evm_run rd951 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    push1 ⟨96⟩, calldatasize, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd963
  rw [hslt] at rd963
  exact evm_run rd963 with [
    push2 ⟨670⟩, jumpiT (by decide) (by native_decide),
    jumpdest, pop, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsClaimX_dec2831_comet {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) claimPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2831⟩
      [⟨970⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt := cometRewardsClaimCalldataCheckOk (I := I) hsz100 hsize hhi
  obtain ⟨_, _, rd942⟩ := hreach
  have rd951 := evm_run rd942 with [jumpdest, pop, pop, pop, callvalue]
  rw [hwv] at rd951
  have rd963 := evm_run rd951 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    push1 ⟨96⟩, calldatasize, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd963
  rw [hslt] at rd963
  exact ⟨_, _, evm_run rd963 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    push2 ⟨970⟩, push2 ⟨2831⟩, jump (by native_decide)]⟩

theorem cometRewardsClaimX_dec970_comet {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (claimCometWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) claimPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨970⟩
      [claimCometWord I, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2831⟩ :=
    cometRewardsClaimX_dec2831_comet (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz100 hsize hhi
      hreach
  exact ⟨_, _, evm_run rd2831 with [
    jumpdest, push1 ⟨4⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, dup3, sub,
    push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land
            (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
            solcAddrMask =
          uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) := by
        exact solcAddrMask_clean (by
          simpa [claimCometWord, calldataWord] using hcanonComet)
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean]
      exact u256_sub_self _),
    jump (by native_decide)]⟩

theorem cometRewardsClaimX_dec2853_src {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (claimCometWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) claimPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2853⟩
      [⟨978⟩, claimCometWord I, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd970⟩ :=
    cometRewardsClaimX_dec970_comet (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz100 hsize hhi hcanonComet hreach
  exact ⟨_, _, evm_run rd970 with [
    jumpdest, push2 ⟨978⟩, push2 ⟨2853⟩, jump (by native_decide)]⟩

theorem cometRewardsClaimX_dec978_src {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (claimCometWord I).toNat < EVM.addressModulus)
    (hcanonSrc : (claimSrcWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) claimPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨978⟩
      [claimSrcWord I, claimCometWord I, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2853⟩ :=
    cometRewardsClaimX_dec2853_src (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz100 hsize hhi hcanonComet hreach
  exact ⟨_, _, evm_run rd2853 with [
    jumpdest, push1 ⟨36⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, dup3, sub,
    push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land
            (uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32))
            solcAddrMask =
          uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32) := by
        exact solcAddrMask_clean (by
          simpa [claimSrcWord, calldataWord] using hcanonSrc)
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean]
      exact u256_sub_self _),
    jump (by native_decide)]⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimX_noncanon_comet {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (claimCometWord I)
      (UInt256.land (claimCometWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) claimPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2831⟩ :=
    cometRewardsClaimX_dec2831_comet (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz100 hsize hhi
      hreach
  exact evm_run rd2831 with [
    jumpdest, push1 ⟨4⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, dup3, sub,
    push2 ⟨1004⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      exact u256_sub_ne_zero_of_ne (by
        intro heq
        have hclean :
            UInt256.eq (claimCometWord I)
              (UInt256.land (claimCometWord I) solcAddrMask) = ⟨1⟩ := by
          have heq' : claimCometWord I =
              UInt256.land (claimCometWord I) solcAddrMask := by
            simpa [claimCometWord, calldataWord] using heq
          rw [← heq']
          exact uInt256_eq_self _
        rw [hclean] at hnc
        exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hnc))
      (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimX_noncanon_src {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (claimCometWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (claimSrcWord I)
      (UInt256.land (claimSrcWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) claimPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2853⟩ :=
    cometRewardsClaimX_dec2853_src (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz100 hsize hhi hcanonComet hreach
  exact evm_run rd2853 with [
    jumpdest, push1 ⟨36⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, dup3, sub,
    push2 ⟨1004⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      exact u256_sub_ne_zero_of_ne (by
        intro heq
        have hclean :
            UInt256.eq (claimSrcWord I)
              (UInt256.land (claimSrcWord I) solcAddrMask) = ⟨1⟩ := by
          have heq' : claimSrcWord I =
              UInt256.land (claimSrcWord I) solcAddrMask := by
            simpa [claimSrcWord, calldataWord] using heq
          rw [← heq']
          exact uInt256_eq_self _
        rw [hclean] at hnc
        exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hnc))
      (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimX_noncanon_bool {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (claimCometWord I).toNat < EVM.addressModulus)
    (hcanonSrc : (claimSrcWord I).toNat < EVM.addressModulus)
    (hnz : claimShouldAccrueWord I ≠ ⟨0⟩) (hno : claimShouldAccrueWord I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) claimPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let word : UInt256 := claimShouldAccrueWord I
  have hnzWord : word ≠ ⟨0⟩ := by simpa [word] using hnz
  have hnoWord : word ≠ ⟨1⟩ := by simpa [word] using hno
  have hiszero : UInt256.isZero word = ⟨0⟩ := isZero_eq_zero_of_ne hnzWord
  have hsub : UInt256.sub word (UInt256.isZero (UInt256.isZero word)) ≠ ⟨0⟩ := by
    rw [hiszero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by native_decide]
    exact u256_sub_ne_zero_of_ne hnoWord
  obtain ⟨_, _, rd978⟩ :=
    cometRewardsClaimX_dec978_src (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz100 hsize hhi hcanonComet hcanonSrc hreach
  have rd992 := evm_run rd978 with [
    jumpdest, push1 ⟨68⟩, calldataload, swap1, dup2, iszero, iszero, dup3, sub]
  exact evm_run rd992 with [
    push2 ⟨1004⟩,
    jumpiT (by simpa [word, claimShouldAccrueWord, calldataWord] using hsub) (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsClaimX_dec3298_internal {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (claimCometWord I).toNat < EVM.addressModulus)
    (hcanonSrc : (claimSrcWord I).toNat < EVM.addressModulus)
    (hbool : claimShouldAccrueWord I = ⟨0⟩ ∨ claimShouldAccrueWord I = ⟨1⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) claimPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3298⟩
      [claimCometWord I, claimSrcWord I, claimSrcWord I, claimShouldAccrueWord I, ⟨1001⟩,
        ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hboolSub :
      UInt256.sub (claimShouldAccrueWord I)
          (UInt256.isZero (UInt256.isZero (claimShouldAccrueWord I))) = ⟨0⟩ := by
    rcases hbool with hzero | hone
    · rw [hzero]
      native_decide
    · rw [hone]
      native_decide
  obtain ⟨_, _, rd978⟩ :=
    cometRewardsClaimX_dec978_src (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz100 hsize hhi hcanonComet hcanonSrc hreach
  have rd992₀ := evm_run rd978 with [
    jumpdest, push1 ⟨68⟩, calldataload, swap1, dup2, iszero, iszero, dup3, sub]
  have rd992 := rd992₀
  have hboolSub' :
      UInt256.sub (uInt256OfByteArray (I.calldata.readBytes (⟨68⟩ : UInt256).toNat 32))
          (UInt256.isZero
            (UInt256.isZero
              (uInt256OfByteArray (I.calldata.readBytes (⟨68⟩ : UInt256).toNat 32)))) =
        ⟨0⟩ := by
    simpa [claimShouldAccrueWord, calldataWord] using hboolSub
  rw [hboolSub'] at rd992
  exact ⟨_, _, evm_run rd992 with [
    push2 ⟨1004⟩, jumpiNT (by native_decide),
    dup1, push2 ⟨1001⟩, swap4, push2 ⟨3298⟩, jump (by native_decide)]⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_tokenZero_of_reach {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonComet : (claimCometWord I).toNat < EVM.addressModulus)
    (htokenZero : rewardConfigTokenFromSlot0 (getRewardOwedRewardConfigSlot0Word σ I) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3298⟩
      [claimCometWord I, claimSrcWord I, claimSrcWord I, claimShouldAccrueWord I, ⟨1001⟩,
        ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3298⟩ := hreach
  have hslot : getRewardOwedRewardConfigSlotOf I =
      solcMappingSlot ⟨1⟩ (claimCometWord I) := by
    simpa [getRewardOwedCometWord, claimCometWord] using
      getRewardOwedRewardConfigSlotOf_eq_solc I
        (by simpa [getRewardOwedCometWord, claimCometWord] using hcanonComet)
  let slot0 := getRewardOwedRewardConfigSlot0Word σ I
  let multiplier := getRewardOwedMultiplierWord σ I
  have rd3327pre := evm_run rd3298 with [
    jumpdest, push1 ⟨0⟩, push1 ⟨1⟩, dup1, push1 ⟨160⟩, shl, sub, dup1,
    dup4, and, swap5, dup6, dup4,
    raw mstore 0 (wordAt0Mem (claimCometWord I) solcFreePtrMem) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide, solcAddrMask_clean hcanonComet]
        unfold wordAt0Mem
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, swap3, push1 ⟨1⟩, dup5,
    raw mstore 0 (claimRewardConfigHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost
      (by
        unfold claimRewardConfigHashMem twoWordHashMem wordAt32Mem wordAt0Mem
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap8, dup9, dup3]
  have rd3327 := rd3327pre.keccak256 0 (solcMappingSlot ⟨1⟩ (claimCometWord I))
    (UInt256.ofNat 3) (by decide) mem_cost (claimRewardConfigHashMem_keccakSlot I)
    (by decide) (by evm_ov)
  rw [← hslot] at rd3327
  have rd3330 := evm_run rd3327 with [swap1, dup10]
  have rd3330' := evm_run rd3330 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (claimRewardConfigHashMem_mload64 I) (by decide) (by evm_ov)]
  have rd3340 := evm_run rd3330' with [
    swap2, push2 ⟨3340⟩, dup4, push2 ⟨3025⟩, jump (by jump_dest),
    jumpdest, push1 ⟨128⟩, dup2, add, swap1, dup2, lt,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt, lor,
    push2 ⟨3003⟩, jumpiNT (by native_decide),
    push1 ⟨64⟩,
    raw mstore 0 (claimConfigAllocMem I) (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold claimConfigAllocMem claimRewardConfigHashMem twoWordHashMem wordAt32Mem wordAt0Mem
        rfl)
      (by decide) (by evm_ov),
    jump (by jump_dest), jumpdest]
  have rdAfterSloadPre := evm_run rd3340 with [push1 ⟨1⟩, dup2]
  obtain ⟨_, _, rdAfterSload⟩ := rdAfterSloadPre.sload (by decide) (by evm_ov)
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) _
    (getRewardOwedRewardConfigSlot0Word σ I :: _) (claimConfigAllocMem I)
    (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at rdAfterSload
  rw [show getRewardOwedRewardConfigSlot0Word σ I = slot0 from rfl] at rdAfterSload
  have rdBeforeMultiplier := evm_run rdAfterSload with [
    swap2, push1 ⟨255⟩, dup9, dup5, and, swap4, dup5, dup8,
    raw mstore 6 (claimConfigTokenMem I slot0) (UInt256.ofNat 5) (by decide) mem_cost
      (by
        unfold claimConfigTokenMem claimConfigAllocMem claimRewardConfigHashMem
        unfold twoWordHashMem wordAt32Mem wordAt0Mem
        unfold rewardConfigTokenFromSlot0 slot0
        rfl)
      (by decide) (by evm_ov),
    dup4, dup1, push1 ⟨64⟩, shl, sub, dup2, push1 ⟨160⟩, shr, and,
    dup12, dup9, add,
    raw mstore 3 (claimConfigRescaleMem I slot0) (UInt256.ofNat 6) (by decide)
      mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩ =
          UInt256.ofNat (2 ^ 64 - 1) from by native_decide]
        unfold claimConfigRescaleMem claimConfigTokenMem claimConfigAllocMem
        unfold claimRewardConfigHashMem twoWordHashMem wordAt32Mem wordAt0Mem
        unfold rewardConfigRescaleFromSlot0
        unfold rewardConfigTokenFromSlot0 slot0
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨224⟩, shr, and, iszero, iszero, dup14, dup7, add,
    raw mstore 3 (claimConfigShouldMem I slot0) (UInt256.ofNat 7) (by decide)
      mem_cost
      (by
        unfold claimConfigShouldMem claimConfigRescaleMem claimConfigTokenMem
        unfold claimConfigAllocMem claimRewardConfigHashMem twoWordHashMem wordAt32Mem wordAt0Mem
        unfold rewardConfigShouldUpscaleFromSlot0
        unfold rewardConfigShouldUpscaleRawFromSlot0 rewardConfigRescaleFromSlot0
        unfold rewardConfigTokenFromSlot0 slot0
        rfl)
      (by decide) (by evm_ov),
    add]
  obtain ⟨_, _, rdAfterMultiplier⟩ := rdBeforeMultiplier.sload (by decide) (by evm_ov)
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) _
    (getRewardOwedMultiplierWord σ I :: _) (claimConfigShouldMem I slot0)
    (UInt256.ofNat 7) ByteArray.empty (cA, σ) _ _ at rdAfterMultiplier
  rw [show getRewardOwedMultiplierWord σ I = multiplier from rfl] at rdAfterMultiplier
  have rd3387 := evm_run rdAfterMultiplier with [
    push1 ⟨96⟩, dup5, add,
    raw mstore 3 (claimConfigMultiplierMem I slot0 multiplier) (UInt256.ofNat 8)
      (by decide) mem_cost
      (by
        unfold claimConfigMultiplierMem claimConfigShouldMem claimConfigRescaleMem
        unfold claimConfigTokenMem claimConfigAllocMem claimRewardConfigHashMem
        unfold twoWordHashMem wordAt32Mem wordAt0Mem
        unfold rewardConfigShouldUpscaleFromSlot0 rewardConfigShouldUpscaleRawFromSlot0
        unfold rewardConfigRescaleFromSlot0 rewardConfigTokenFromSlot0 slot0 multiplier
        rfl)
      (by decide) (by evm_ov),
    iszero]
  have htokenZeroSlot : rewardConfigTokenFromSlot0 slot0 = ⟨0⟩ := by
    simpa [slot0] using htokenZero
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) _
    (UInt256.isZero (rewardConfigTokenFromSlot0 slot0) :: _)
    (claimConfigMultiplierMem I slot0 multiplier) (UInt256.ofNat 8)
    ByteArray.empty (cA, σ) _ _ at rd3387
  rw [htokenZeroSlot] at rd3387
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) _
    (⟨1⟩ :: _) (claimConfigMultiplierMem I slot0 multiplier)
    (UInt256.ofNat 8) ByteArray.empty (cA, σ) _ _ at rd3387
  have rd3636 := evm_run rd3387 with [
    push2 ⟨3636⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd3656 := evm_run rd3636 with [
    jumpdest, dup10,
    raw mload 0 ⟨256⟩ (UInt256.ofNat 8) (by decide) mem_cost
      (claimConfigMultiplierMem_mload64 I slot0 multiplier) (by decide) (by evm_ov),
    push4 ⟨1311535579⟩, push1 ⟨225⟩, shl, dup2,
    raw mstore 3 (claimInvalidRewardConfigSelectorMem I slot0 multiplier) (UInt256.ofNat 9)
      (by decide) mem_cost
      (by
        unfold claimInvalidRewardConfigSelectorMem claimConfigMultiplierMem claimConfigShouldMem
        unfold claimConfigRescaleMem claimConfigTokenMem claimConfigAllocMem
        unfold claimRewardConfigHashMem twoWordHashMem wordAt32Mem wordAt0Mem
        unfold rewardConfigShouldUpscaleFromSlot0
        unfold rewardConfigShouldUpscaleRawFromSlot0 rewardConfigRescaleFromSlot0
        unfold rewardConfigTokenFromSlot0 slot0 multiplier
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨4⟩, dup2, add, dup11, swap1,
    raw mstore 3 (claimInvalidRewardConfigArgMem I slot0 multiplier) (UInt256.ofNat 10)
      (by decide) mem_cost
      (by
        unfold claimInvalidRewardConfigArgMem claimInvalidRewardConfigSelectorMem
        unfold claimConfigMultiplierMem claimConfigShouldMem claimConfigRescaleMem
        unfold claimConfigTokenMem claimConfigAllocMem claimRewardConfigHashMem
        unfold twoWordHashMem wordAt32Mem wordAt0Mem
        unfold rewardConfigShouldUpscaleFromSlot0 rewardConfigShouldUpscaleRawFromSlot0
        unfold rewardConfigRescaleFromSlot0 rewardConfigTokenFromSlot0 slot0 multiplier
        rw [show ((⟨256⟩ : UInt256) + ⟨4⟩).toNat = 260 from by native_decide]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide, solcAddrMask_clean hcanonComet]
        unfold Reasoning.Theory.writeWord
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, swap1]
  exact evm_run rd3656 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_noAccrue_call_baseTracking
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonComet : (claimCometWord I).toNat < EVM.addressModulus)
    (hcanonSrc : (claimSrcWord I).toNat < EVM.addressModulus)
    (htokenNZ :
      rewardConfigTokenFromSlot0 (getRewardOwedRewardConfigSlot0Word σ I) ≠ ⟨0⟩)
    (hshouldZero : claimShouldAccrueWord I = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3298⟩
      [claimCometWord I, claimSrcWord I, claimSrcWord I, claimShouldAccrueWord I, ⟨1001⟩,
        ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ gasArg k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) claimBaseTrackingCallPc
      (gasArg :: UInt256.land (claimCometWord I) solcAddrMask ::
        ⟨256⟩ :: claimBaseTrackingCallSize :: ⟨256⟩ :: ⟨32⟩ ::
        claimBaseTrackingPostCallTail I (getRewardOwedClaimedWord σ I))
      (claimBaseTrackingCalldataMem I (getRewardOwedRewardConfigSlot0Word σ I)
        (getRewardOwedMultiplierWord σ I))
      claimBaseTrackingCallAw ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3298⟩ := hreach
  have hslot : getRewardOwedRewardConfigSlotOf I =
      solcMappingSlot ⟨1⟩ (claimCometWord I) := by
    simpa [getRewardOwedCometWord, claimCometWord] using
      getRewardOwedRewardConfigSlotOf_eq_solc I
        (by simpa [getRewardOwedCometWord, claimCometWord] using hcanonComet)
  let slot0 := getRewardOwedRewardConfigSlot0Word σ I
  let multiplier := getRewardOwedMultiplierWord σ I
  have rd3327pre := evm_run rd3298 with [
    jumpdest, push1 ⟨0⟩, push1 ⟨1⟩, dup1, push1 ⟨160⟩, shl, sub, dup1,
    dup4, and, swap5, dup6, dup4,
    raw mstore 0 (wordAt0Mem (claimCometWord I) solcFreePtrMem) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide, solcAddrMask_clean hcanonComet]
        unfold wordAt0Mem
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, swap3, push1 ⟨1⟩, dup5,
    raw mstore 0 (claimRewardConfigHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost
      (by
        unfold claimRewardConfigHashMem twoWordHashMem wordAt32Mem wordAt0Mem
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, swap8, dup9, dup3]
  have rd3327 := rd3327pre.keccak256 0 (solcMappingSlot ⟨1⟩ (claimCometWord I))
    (UInt256.ofNat 3) (by decide) mem_cost (claimRewardConfigHashMem_keccakSlot I)
    (by decide) (by evm_ov)
  rw [← hslot] at rd3327
  have rd3330 := evm_run rd3327 with [swap1, dup10]
  have rd3330' := evm_run rd3330 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost (claimRewardConfigHashMem_mload64 I) (by decide) (by evm_ov)]
  have rd3340 := evm_run rd3330' with [
    swap2, push2 ⟨3340⟩, dup4, push2 ⟨3025⟩, jump (by jump_dest),
    jumpdest, push1 ⟨128⟩, dup2, add, swap1, dup2, lt,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt, lor,
    push2 ⟨3003⟩, jumpiNT (by native_decide),
    push1 ⟨64⟩,
    raw mstore 0 (claimConfigAllocMem I) (UInt256.ofNat 3) (by decide) mem_cost
      (by
        unfold claimConfigAllocMem claimRewardConfigHashMem twoWordHashMem wordAt32Mem wordAt0Mem
        rfl)
      (by decide) (by evm_ov),
    jump (by jump_dest), jumpdest]
  have rdAfterSloadPre := evm_run rd3340 with [push1 ⟨1⟩, dup2]
  obtain ⟨_, _, rdAfterSload⟩ := rdAfterSloadPre.sload (by decide) (by evm_ov)
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) _
    (getRewardOwedRewardConfigSlot0Word σ I :: _) (claimConfigAllocMem I)
    (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at rdAfterSload
  rw [show getRewardOwedRewardConfigSlot0Word σ I = slot0 from rfl] at rdAfterSload
  have rdBeforeMultiplier := evm_run rdAfterSload with [
    swap2, push1 ⟨255⟩, dup9, dup5, and, swap4, dup5, dup8,
    raw mstore 6 (claimConfigTokenMem I slot0) (UInt256.ofNat 5) (by decide) mem_cost
      (by
        unfold claimConfigTokenMem claimConfigAllocMem claimRewardConfigHashMem
        unfold twoWordHashMem wordAt32Mem wordAt0Mem
        unfold rewardConfigTokenFromSlot0 slot0
        rfl)
      (by decide) (by evm_ov),
    dup4, dup1, push1 ⟨64⟩, shl, sub, dup2, push1 ⟨160⟩, shr, and,
    dup12, dup9, add,
    raw mstore 3 (claimConfigRescaleMem I slot0) (UInt256.ofNat 6) (by decide)
      mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩ =
          UInt256.ofNat (2 ^ 64 - 1) from by native_decide]
        unfold claimConfigRescaleMem claimConfigTokenMem claimConfigAllocMem
        unfold claimRewardConfigHashMem twoWordHashMem wordAt32Mem wordAt0Mem
        unfold rewardConfigRescaleFromSlot0
        unfold rewardConfigTokenFromSlot0 slot0
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨224⟩, shr, and, iszero, iszero, dup14, dup7, add,
    raw mstore 3 (claimConfigShouldMem I slot0) (UInt256.ofNat 7) (by decide)
      mem_cost
      (by
        unfold claimConfigShouldMem claimConfigRescaleMem claimConfigTokenMem
        unfold claimConfigAllocMem claimRewardConfigHashMem twoWordHashMem wordAt32Mem wordAt0Mem
        unfold rewardConfigShouldUpscaleFromSlot0
        unfold rewardConfigShouldUpscaleRawFromSlot0 rewardConfigRescaleFromSlot0
        unfold rewardConfigTokenFromSlot0 slot0
        rfl)
      (by decide) (by evm_ov),
    add]
  obtain ⟨_, _, rdAfterMultiplier⟩ := rdBeforeMultiplier.sload (by decide) (by evm_ov)
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) _
    (getRewardOwedMultiplierWord σ I :: _) (claimConfigShouldMem I slot0)
    (UInt256.ofNat 7) ByteArray.empty (cA, σ) _ _ at rdAfterMultiplier
  rw [show getRewardOwedMultiplierWord σ I = multiplier from rfl] at rdAfterMultiplier
  have rd3387 := evm_run rdAfterMultiplier with [
    push1 ⟨96⟩, dup5, add,
    raw mstore 3 (claimConfigMultiplierMem I slot0 multiplier) (UInt256.ofNat 8)
      (by decide) mem_cost
      (by
        unfold claimConfigMultiplierMem claimConfigShouldMem claimConfigRescaleMem
        unfold claimConfigTokenMem claimConfigAllocMem claimRewardConfigHashMem
        unfold twoWordHashMem wordAt32Mem wordAt0Mem
        unfold rewardConfigShouldUpscaleFromSlot0 rewardConfigShouldUpscaleRawFromSlot0
        unfold rewardConfigRescaleFromSlot0 rewardConfigTokenFromSlot0 slot0 multiplier
        rfl)
      (by decide) (by evm_ov),
    iszero]
  have htokenNZSlot : rewardConfigTokenFromSlot0 slot0 ≠ ⟨0⟩ := by
    simpa [slot0] using htokenNZ
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) _
    (UInt256.isZero (rewardConfigTokenFromSlot0 slot0) :: _)
    (claimConfigMultiplierMem I slot0 multiplier) (UInt256.ofNat 8)
    ByteArray.empty (cA, σ) _ _ at rd3387
  rw [isZero_eq_zero_of_ne htokenNZSlot] at rd3387
  change RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) _
    (⟨0⟩ :: _) (claimConfigMultiplierMem I slot0 multiplier)
    (UInt256.ofNat 8) ByteArray.empty (cA, σ) _ _ at rd3387
  have rd3396 := evm_run rd3387 with [
    push2 ⟨3636⟩, jumpiNT (by native_decide),
    push2 ⟨3556⟩, jumpiNT (by simpa [hshouldZero])]
  have rd3400 := evm_run rd3396 with [
    jumpdest, dup8, dup3,
    raw mstore 0
      (wordAt0Mem (UInt256.land (claimCometWord I) solcAddrMask)
        (claimConfigMultiplierMem I slot0 multiplier))
      (UInt256.ofNat 8) (by native_decide) mem_cost
      (by
        unfold wordAt0Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3404 := evm_run rd3400 with [
    push1 ⟨2⟩, dup6,
    raw mstore 0 (claimClaimedInnerHashMem I slot0 multiplier)
      (UInt256.ofNat 8) (by native_decide) mem_cost
      (by
        unfold claimClaimedInnerHashMem twoWordHashMem wordAt32Mem wordAt0Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have hinnerHash :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((claimClaimedInnerHashMem I slot0 multiplier)
            |>.readWithPadding 0 64))) =
        solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask) := by
    unfold claimClaimedInnerHashMem
    exact twoWordHashMem_solcMappingSlot_of_ge ⟨2⟩
      (UInt256.land (claimCometWord I) solcAddrMask)
      (by rw [claimConfigMultiplierMem_size]; decide)
  have rd3411pre := evm_run rd3404 with [push2 ⟨3432⟩, dup2, dup11, dup5]
  have rd3411 := rd3411pre.keccak256 0
    (solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask))
    (UInt256.ofNat 8) (by native_decide) mem_cost
    hinnerHash (by native_decide) (by evm_ov)
  have rd3419 := evm_run rd3411 with [
    swap9, dup7, dup2, and, swap10, dup11, push1 ⟨0⟩,
    raw mstore 0
      (wordAt0Mem (UInt256.land (claimSrcWord I) solcAddrMask)
        (claimClaimedInnerHashMem I slot0 multiplier))
      (UInt256.ofNat 8) (by native_decide) mem_cost
      (by
        unfold wordAt0Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3421 := evm_run rd3419 with [
    dup9,
    raw mstore 0 (claimClaimedOuterHashMem I slot0 multiplier)
      (UInt256.ofNat 8) (by native_decide) mem_cost
      (by
        unfold claimClaimedOuterHashMem twoWordHashMem wordAt32Mem wordAt0Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have houterHash := claimClaimedOuterHashMem_keccakSlot I slot0 multiplier
    hcanonComet hcanonSrc
  have rd3426pre := (evm_run rd3421 with [dup12, push1 ⟨0⟩]).keccak256 0
    (getRewardOwedRewardsClaimedSlotOf I)
    (UInt256.ofNat 8) (by native_decide) mem_cost
    houterHash (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3427₀⟩ := rd3426pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3427⟩ : ∃ k1 C1, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3427⟩
      [getRewardOwedClaimedWord σ I, claimSrcWord I, ⟨128⟩, ⟨3432⟩, ⟨128⟩,
        ⟨0⟩, claimSrcWord I, solcAddrMask, ⟨32⟩, claimCometWord I,
        UInt256.land (claimSrcWord I) solcAddrMask,
        UInt256.land (claimCometWord I) solcAddrMask, ⟨64⟩, ⟨1001⟩, ⟨64⟩, ⟨0⟩]
      (claimClaimedOuterHashMem I slot0 multiplier)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k1 C1 := by
    exact ⟨_, _, by
      simpa [getRewardOwedClaimedWord] using rd3427₀⟩
  have rd3679 := evm_run rd3427 with [swap9, push2 ⟨3679⟩, jump (by jump_dest)]
  have rd3682 := evm_run rd3679 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨256⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (claimClaimedOuterHashMem_mload64 I slot0 multiplier)
      (by native_decide) (by evm_ov)]
  have rd3692 := evm_run rd3682 with [
    push4 ⟨719776253⟩, push1 ⟨226⟩, shl, dup2,
    raw mstore 3 (claimBaseTrackingSelectorMem I slot0 multiplier)
      (UInt256.ofNat 9) (by native_decide) mem_cost
      (by
        unfold claimBaseTrackingSelectorMem
        rfl)
      (by native_decide) (by evm_ov)]
  have hcleanSrc :
      UInt256.land solcAddrMask (claimSrcWord I) = claimSrcWord I := by
    rw [u256_land_comm]
    exact solcAddrMask_clean hcanonSrc
  have rd3708 := evm_run rd3692 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap3, dup4, and,
    push1 ⟨4⟩, dup3, add,
    raw mstore 3 (claimBaseTrackingCalldataMem I slot0 multiplier)
      claimBaseTrackingCallAw (by native_decide) mem_cost
      (by
        rw [show ((⟨256⟩ : UInt256) + ⟨4⟩).toNat = 260 from by native_decide]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [hcleanSrc]
        unfold claimBaseTrackingCalldataMem claimBaseTrackingSelectorMem
        rfl)
      (by native_decide) (by evm_ov)]
  obtain ⟨gasArg, rd3723⟩ := evm_run rd3708 with [
    swap3, swap2, push1 ⟨32⟩, swap2, dup5, swap2, push1 ⟨36⟩,
    swap2, dup4, swap2, and, gas]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by decide] at rd3723
  rw [u256_land_comm solcAddrMask (claimCometWord I)] at rd3723
  exact ⟨gasArg, _, _, by
    simpa [claimBaseTrackingCallPc, claimBaseTrackingCallSize, claimBaseTrackingPostCallTail,
      claimBaseTrackingCallAw] using rd3723⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_noAccrue_call_baseTracking_made
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hcanonComet : (claimCometWord I).toNat < EVM.addressModulus)
    (hcanonSrc : (claimSrcWord I).toNat < EVM.addressModulus)
    (hdepth : I.depth.val < 1024)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (htokenNZ :
      rewardConfigTokenFromSlot0 (getRewardOwedRewardConfigSlot0Word σ_evm I) ≠ ⟨0⟩)
    (hshouldZero : claimShouldAccrueWord I = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ_evm σ₀ g A I) ⟨3298⟩
      [claimCometWord I, claimSrcWord I, claimSrcWord I, claimShouldAccrueWord I, ⟨1001⟩,
        ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    ∃ cA' σ'_evm σ'_solm A'_solm z baseOut k' C',
      typedCallViaEVM config
        (initState cA gh bl σ_solm σ₀ g A I)
        (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (z,
          { initState cA gh bl σ_solm σ₀ g A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          baseOut) false ∧
      accountMapEquiv σ'_evm σ'_solm ∧
      RD cometRewardsBytecode I g (initState cA gh bl σ_evm σ₀ g A I)
        (claimBaseTrackingCallPc + ⟨1⟩)
        (claimBaseTrackingPostCallStack I z (getRewardOwedClaimedWord σ_evm I))
        (claimBaseTrackingPostCallMem I (getRewardOwedRewardConfigSlot0Word σ_evm I)
          (getRewardOwedMultiplierWord σ_evm I) baseOut)
        claimBaseTrackingPostCallAw baseOut (cA', σ'_evm) k' C' ∧
      baseOut.size < UInt256.size ∧
      baseOut.size < 2 ^ 255 := by
  let slot0 := getRewardOwedRewardConfigSlot0Word σ_evm I
  let multiplier := getRewardOwedMultiplierWord σ_evm I
  obtain ⟨gasArg, k0, C0, rd3723⟩ :=
    cometRewardsClaimInternalX_noAccrue_call_baseTracking
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcanonComet hcanonSrc htokenNZ
      hshouldZero hreach
  have rd3723Call :
      RD cometRewardsBytecode I g (initState cA gh bl σ_evm σ₀ g A I)
        claimBaseTrackingCallPc
        (gasArg :: UInt256.land (claimCometWord I) solcAddrMask ::
          ⟨256⟩ :: claimBaseTrackingCallSize :: ⟨256⟩ :: ⟨32⟩ ::
          claimBaseTrackingPostCallTail I (getRewardOwedClaimedWord σ_evm I))
        (claimBaseTrackingCalldataMem I slot0 multiplier)
        claimBaseTrackingCallAw ByteArray.empty (cA, σ_evm) k0 C0 := by
    simpa [slot0, multiplier, claimBaseTrackingPostCallTail] using rd3723
  have hdecCall :
      decode cometRewardsBytecode claimBaseTrackingCallPc =
        some (.STATICCALL, .none) := by
    unfold claimBaseTrackingCallPc getRewardOwedBaseTrackingCallPc
    native_decide
  obtain ⟨cA', σ'_evm, z, baseOut, A_in, callGas, k', C', hΘ, rd3724,
      _houtSize⟩ :=
    RD.uniswapStaticcall (t :=
        claimBaseTrackingPostCallTail I (getRewardOwedClaimedWord σ_evm I))
      rd3723Call hdecCall hdepth
      (by simp [claimBaseTrackingPostCallTail])
  obtain ⟨g'', A'_evm, hΘeq⟩ := hΘ
  let evmEBase : EVM.State := initState cA gh bl σ_evm σ₀ g A I
  let evmSBase : EVM.State := initState cA gh bl σ_solm σ₀ g A I
  have houtSmall : baseOut.size < 2 ^ 138 := by
    exact Theta_returnData_size_lt_2pow138_of_eq
      (blob := I.blobVersionedHashes) (cA := cA)
      (gh := (initState cA gh bl σ_evm σ₀ g A I).genesisBlockHeader)
      (blocks := (initState cA gh bl σ_evm σ₀ g A I).blocks)
      (σ := σ_evm)
      (σ₀ := (initState cA gh bl σ_evm σ₀ g A I).σ₀)
      (A := A_in)
      (s := AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner))
      (o := I.sender)
      (r := AccountAddress.ofUInt256 (UInt256.land (claimCometWord I) solcAddrMask))
      (c := toExecute σ_evm
        (AccountAddress.ofUInt256 (UInt256.land (claimCometWord I) solcAddrMask)))
      (g := callGas) (p := UInt256.ofNat I.gasPrice)
      (v := ⟨0⟩) (v' := ⟨0⟩)
      (d := (claimBaseTrackingCalldataMem I slot0 multiplier)
        |>.readWithPadding 256 claimBaseTrackingCallSize.toNat)
      (e := I.depth + 1) (H := I.header) (w := false)
      hΘeq
      (by exact Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)
  have houtUInt : baseOut.size < UInt256.size := by
    have hsz : UInt256.size = 2 ^ 256 := by decide
    omega
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hEq
    rw [hEq] at hdepth
    exact absurd hdepth (by decide)
  have hdepthNe : evmEBase.executionEnv.depth ≠ 1024 := by
    simpa [evmEBase, initState] using hdepthNeI
  have htgt :
      EVM.address (getRewardOwedCometTarget I) =
        AccountAddress.ofUInt256 (UInt256.land (claimCometWord I) solcAddrMask) := by
    simpa [getRewardOwedCometWord, claimCometWord] using
      getRewardOwedCometTarget_eq_targetWord I
        (by simpa [getRewardOwedCometWord, claimCometWord] using hcanonComet)
  have hcd := claimBaseTrackingCalldataMem_encode_args I slot0 multiplier hcanonSrc
  have hcallE :
      typedCallViaEVM config evmEBase
        (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (z,
          { evmEBase with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          baseOut) false := by
    refine callCoincides
      (cfg := config) (evm := evmEBase)
      (name := "baseTrackingAccrued") (args := getRewardAccruedBaseTrackingArgs I)
      (tgt := EVM.address (getRewardOwedCometTarget I))
      (targetWord := UInt256.land (claimCometWord I) solcAddrMask)
      (cA' := cA') (σ' := σ'_evm) (A' := A'_evm) (A_in := A_in)
      (z := z) (o := baseOut) (g'' := g'') (callGas := callGas)
      (mem := claimBaseTrackingCalldataMem I slot0 multiplier)
      (inOff := ⟨256⟩) (inSize := claimBaseTrackingCallSize)
      (callPerm := false)
      hdepthNe htgt hcd ?_
    simpa [evmEBase, initState] using hΘeq
  obtain ⟨σ'_solm, A'_solm, hcallSolm, hPostAccounts'⟩ :=
    typedCallViaEVM_accountMapEquiv
      (evm_solm := evmSBase) hcallE
      (by simpa [evmEBase, evmSBase, initState] using hAccounts)
      (by simp [evmEBase, evmSBase, initState])
      (by simp [evmEBase, evmSBase, initState])
      (by simp [evmEBase, evmSBase, initState])
      (by simp [evmEBase, evmSBase, initState])
      (by simp [evmEBase, evmSBase, initState])
      (by simp [evmEBase, evmSBase, initState])
  exact ⟨cA', σ'_evm, σ'_solm, A'_solm, z, baseOut, k', C',
    by
      simpa [evmSBase, initState] using hcallSolm,
    hPostAccounts',
    by
      simpa [claimBaseTrackingPostCallStack, claimBaseTrackingPostCallTail,
        claimBaseTrackingPostCallMem, claimBaseTrackingPostCallAw, claimBaseTrackingCallSize,
        slot0, multiplier] using rd3724,
    houtUInt,
    by omega⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_after_baseTracking_failure
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier claimed : UInt256} {baseOut : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (claimBaseTrackingCallPc + ⟨1⟩)
      (claimBaseTrackingPostCallStack I false claimed)
      (claimBaseTrackingPostCallMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C)
    (hbaseSize : baseOut.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd3724 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3724⟩
      (⟨0⟩ :: claimBaseTrackingPostCallTail I claimed)
      (claimBaseTrackingPostCallMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C := by
    simpa [claimBaseTrackingCallPc, claimBaseTrackingPostCallStack,
      claimBaseTrackingPostCallTail] using rd
  have rd3876 := evm_run rd3724 with [
    swap2, dup3, iszero, push2 ⟨3876⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd3879 := evm_run rd3876 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨256⟩ claimBaseTrackingPostCallAw (by native_decide)
      mem_cost
      (claimBaseTrackingPostCallMem_mload64 I slot0 multiplier hbaseSize)
      (by native_decide) (by evm_ov)]
  let rdsz : UInt256 := UInt256.ofNat baseOut.size
  have hrdsz_toNat : rdsz.toNat = baseOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hbaseSize
  have rd3883pre := evm_run rd3879 with [returndatasize, push1 ⟨0⟩, dup3]
  let mem2 : ByteArray :=
    baseOut.write 0
      (claimBaseTrackingPostCallMem I slot0 multiplier baseOut)
      256 rdsz.toNat
  let aw2 : UInt256 :=
    UInt256.ofNat (MachineState.M claimBaseTrackingPostCallAw.toNat 256 rdsz.toNat)
  have rd3884 := RD.returndatacopy
    (Cₘ aw2 - Cₘ claimBaseTrackingPostCallAw) mem2 aw2 rd3883pre
    (by native_decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hrdsz_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2, rdsz]
      change
        Cₘ (UInt256.ofNat
            (MachineState.M claimBaseTrackingPostCallAw.toNat 256
              (UInt256.ofNat baseOut.size).toNat)) -
          Cₘ claimBaseTrackingPostCallAw =
        Cₘ (UInt256.ofNat
            (MachineState.M claimBaseTrackingPostCallAw.toNat 256
              (UInt256.ofNat baseOut.size).toNat)) -
          Cₘ claimBaseTrackingPostCallAw
      rfl)
    (by rfl)
    (by rfl)
    (by simp)
  have rd3886 := evm_run rd3884 with [returndatasize, swap1]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M aw2.toNat 256 rdsz.toNat)) - Cₘ aw2)
    rd3886 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, rdsz]
      change
        Cₘ (UInt256.ofNat
            (MachineState.M aw2.toNat 256 (UInt256.ofNat baseOut.size).toNat)) -
          Cₘ aw2 =
        Cₘ (UInt256.ofNat
            (MachineState.M aw2.toNat 256 (UInt256.ofNat baseOut.size).toNat)) -
          Cₘ aw2
      rfl)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_noAccrue_callDepthLimit
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonComet : (claimCometWord I).toNat < EVM.addressModulus)
    (hcanonSrc : (claimSrcWord I).toNat < EVM.addressModulus)
    (htokenNZ :
      rewardConfigTokenFromSlot0 (getRewardOwedRewardConfigSlot0Word σ I) ≠ ⟨0⟩)
    (hshouldZero : claimShouldAccrueWord I = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3298⟩
      [claimCometWord I, claimSrcWord I, claimSrcWord I, claimShouldAccrueWord I, ⟨1001⟩,
        ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨gasArg, k0, C0, rd3723⟩ :=
    cometRewardsClaimInternalX_noAccrue_call_baseTracking
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcanonComet hcanonSrc htokenNZ
      hshouldZero hreach
  let slot0 := getRewardOwedRewardConfigSlot0Word σ I
  let multiplier := getRewardOwedMultiplierWord σ I
  have rd3723Call :
      RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
        claimBaseTrackingCallPc
        (gasArg :: UInt256.land (claimCometWord I) solcAddrMask ::
          ⟨256⟩ :: claimBaseTrackingCallSize :: ⟨256⟩ :: ⟨32⟩ ::
          claimBaseTrackingPostCallTail I (getRewardOwedClaimedWord σ I))
        (claimBaseTrackingCalldataMem I slot0 multiplier)
        claimBaseTrackingCallAw ByteArray.empty (cA, σ) k0 C0 := by
    simpa [slot0, multiplier, claimBaseTrackingPostCallTail] using rd3723
  have hdecCall :
      decode cometRewardsBytecode claimBaseTrackingCallPc =
        some (.STATICCALL, .none) := by
    unfold claimBaseTrackingCallPc getRewardOwedBaseTrackingCallPc
    native_decide
  have hdepthInit :
      (initState cA gh bl σ σ₀ g A I).executionEnv.depth = 1024 := by
    simpa [initState] using hdepth
  obtain ⟨k', C', rdPost₀⟩ :=
    RD.uniswapStaticcallDepthLimit
      (t := claimBaseTrackingPostCallTail I (getRewardOwedClaimedWord σ I))
      rd3723Call hdecCall hdepthInit (by simp [claimBaseTrackingPostCallTail])
  have rdPost :
      RD cometRewardsBytecode I g
        (initState cA gh bl σ σ₀ g A I)
        (claimBaseTrackingCallPc + ⟨1⟩)
        (claimBaseTrackingPostCallStack I false (getRewardOwedClaimedWord σ I))
        (claimBaseTrackingPostCallMem I slot0 multiplier ByteArray.empty)
        claimBaseTrackingPostCallAw ByteArray.empty (cA, σ) k' C' := by
    simpa [claimBaseTrackingPostCallStack, claimBaseTrackingPostCallTail,
      claimBaseTrackingPostCallMem, claimBaseTrackingPostCallAw, claimBaseTrackingCallSize,
      slot0, multiplier] using rdPost₀
  exact cometRewardsClaimInternalX_after_baseTracking_failure
    (slot0 := slot0) (multiplier := multiplier)
    (claimed := getRewardOwedClaimedWord σ I) rdPost (by simp [UInt256.size])

set_option maxHeartbeats 2000000 in
theorem cometRewardsClaimInternalX_after_baseTracking_short_revert
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier claimed : UInt256} {baseOut : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (claimBaseTrackingCallPc + ⟨1⟩)
      (claimBaseTrackingPostCallStack I true claimed)
      (claimBaseTrackingPostCallMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C)
    (hshort : baseOut.size < 32) (hbaseSize : baseOut.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let rdsz : UInt256 := UInt256.ofNat baseOut.size
  have hrdsz_toNat : rdsz.toNat = baseOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hbaseSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨1⟩ := by
    apply ugt_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hshort
  have rd3724 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3724⟩
      (⟨1⟩ :: claimBaseTrackingPostCallTail I claimed)
      (claimBaseTrackingPostCallMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C := by
    simpa [claimBaseTrackingCallPc, claimBaseTrackingPostCallStack,
      claimBaseTrackingPostCallTail] using rd
  have rd3855₀ := evm_run rd3724 with [
    swap2, dup3, iszero, push2 ⟨3876⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap3, push2 ⟨3844⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push2 ⟨3869⟩, swap2, swap3, pop, push1 ⟨32⟩,
    returndatasize, dup2, gt]
  have rd3855 := rd3855₀
  rw [show UInt256.ofNat baseOut.size = rdsz from rfl, hgt] at rd3855
  let rounded : UInt256 :=
    UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat baseOut.size + ⟨31⟩)
  let ptr : UInt256 := (⟨256⟩ : UInt256) + rounded
  have hroundedLe : rounded.toNat ≤ baseOut.size + 31 := by
    unfold rounded
    rw [uland_toNat]
    refine le_trans Nat.and_le_right ?_
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hbaseSize,
      show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    exact Nat.mod_le _ _
  have hptr_toNat : ptr.toNat = 256 + rounded.toNat := by
    unfold ptr
    rw [uadd_toNat, show (⟨256⟩ : UInt256).toNat = 256 from by decide]
    exact Nat.mod_eq_of_lt (by
      have hroundSmall : rounded.toNat < 64 := by omega
      have hsz : UInt256.size = 2 ^ 256 := by decide
      omega)
  have hltPtr : UInt256.lt ptr (⟨256⟩ : UInt256) = ⟨0⟩ := by
    apply ult_zero
    rw [hptr_toNat, show (⟨256⟩ : UInt256).toNat = 256 from by decide]
    omega
  have hmax64 :
      (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩).toNat =
        18446744073709551615 := by
    native_decide
  have hgtPtr :
      UInt256.gt ptr (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    rw [hptr_toNat, hmax64]
    omega
  have hallocOk :
      UInt256.lor (UInt256.lt ptr (⟨256⟩ : UInt256))
        (UInt256.gt ptr (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)) = ⟨0⟩ := by
    rw [hltPtr, hgtPtr]
    native_decide
  have rd3071 := evm_run rd3855 with [
    push2 ⟨734⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, returndatasize, push2 ⟨709⟩, jump (by jump_dest),
    jumpdest, push2 ⟨719⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩,
    jumpiNT (by simpa [ptr, rounded] using hallocOk), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0
      (claimBaseTrackingPostShortDecodeMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw
      (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
      (by native_decide) (by evm_ov)]
  have rd3106 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, swap1, push2 ⟨3106⟩,
    jump (by jump_dest)]
  have hlenCheck :
      UInt256.slt (UInt256.sub ((⟨256⟩ : UInt256) + rdsz) ⟨256⟩) ⟨32⟩ =
        ⟨1⟩ := by
    simpa [rdsz] using
      solcReturnStaticLenCheckShort (base := 256) (words := 1) (by simpa using hshort)
        (by norm_num [UInt256.size])
        (by
          have hsz : UInt256.size = 2 ^ 256 := by decide
          omega)
        (by norm_num)
  have rd3114₀ := evm_run rd3106 with [
    jumpdest, swap1, dup2, push1 ⟨32⟩, swap2, sub, slt]
  have rd3114 := rd3114₀
  rw [hlenCheck] at rd3114
  have rd1004 := evm_run rd3114 with [
    push2 ⟨1004⟩, jumpiT (by native_decide) (by jump_dest)]
  exact evm_run rd1004 with [
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem cometRewardsClaimInternalX_after_baseTracking_noncanon_revert
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier claimed : UInt256} {baseOut : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (claimBaseTrackingCallPc + ⟨1⟩)
      (claimBaseTrackingPostCallStack I true claimed)
      (claimBaseTrackingPostCallMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hbase64 : ¬ (claimBaseTrackingReturnWord baseOut).toNat < EVM.twoPow 64) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let baseWord : UInt256 := claimBaseTrackingReturnWord baseOut
  have hbase64' : ¬ baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  let rdsz : UInt256 := UInt256.ofNat baseOut.size
  have hrdsz_toNat : rdsz.toNat = baseOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hbaseSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hout32
  have rd3724 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3724⟩
      (⟨1⟩ :: claimBaseTrackingPostCallTail I claimed)
      (claimBaseTrackingPostCallMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C := by
    simpa [claimBaseTrackingCallPc, claimBaseTrackingPostCallStack,
      claimBaseTrackingPostCallTail] using rd
  have rd3855₀ := evm_run rd3724 with [
    swap2, dup3, iszero, push2 ⟨3876⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap3, push2 ⟨3844⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push2 ⟨3869⟩, swap2, swap3, pop, push1 ⟨32⟩,
    returndatasize, dup2, gt]
  have rd3855 := rd3855₀
  rw [show UInt256.ofNat baseOut.size = rdsz from rfl, hgt] at rd3855
  have rd3071 := evm_run rd3855 with [
    push2 ⟨734⟩, jumpiNT (by native_decide),
    push2 ⟨719⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide),
    push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0
      (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw
      (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold claimBaseTrackingPostDecodeMem Reasoning.Theory.writeWord
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3106 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, swap1, push2 ⟨3106⟩,
    jump (by jump_dest), jumpdest, swap1, dup2, push1 ⟨32⟩, swap2, sub,
    slt, push2 ⟨1004⟩, jumpiNT (by native_decide)]
  have rd3129 := evm_run rd3106 with [
    raw mload 0 baseWord claimBaseTrackingPostCallAw (by native_decide)
      mem_cost
      (by
        simpa [baseWord] using
          claimBaseTrackingPostDecodeMem_mload256_of_size_ge
            I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup2, and, dup2, sub]
  have hnotClean : UInt256.land baseWord uint64Mask ≠ baseWord :=
    uint64Mask_not_clean hbase64'
  have hneq :
      baseWord ≠
        UInt256.land baseWord
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) := by
    intro hEq
    exact hnotClean (by simpa [uint64Mask] using hEq.symm)
  have hsub :
      UInt256.sub baseWord
        (UInt256.land baseWord
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) ≠ ⟨0⟩ :=
    u256_sub_ne_zero_of_ne hneq
  have rd1004 := evm_run rd3129 with [
    push2 ⟨1004⟩, jumpiT hsub (by jump_dest)]
  exact evm_run rd1004 with [
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem cometRewardsClaimInternalX_after_baseTracking_decode_ok
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier claimed : UInt256} {baseOut : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (claimBaseTrackingCallPc + ⟨1⟩)
      (claimBaseTrackingPostCallStack I true claimed)
      (claimBaseTrackingPostCallMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hbase64 : (claimBaseTrackingReturnWord baseOut).toNat < EVM.twoPow 64) :
    ∃ k' C', RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3740⟩
      [⟨128⟩, claimBaseTrackingReturnWord baseOut, ⟨3432⟩,
        ⟨128⟩, ⟨0⟩, claimSrcWord I, solcAddrMask, ⟨32⟩, claimed,
        UInt256.land (claimSrcWord I) solcAddrMask,
        UInt256.land (claimCometWord I) solcAddrMask, ⟨64⟩, ⟨1001⟩, ⟨64⟩, ⟨0⟩]
      (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k' C' := by
  let baseWord : UInt256 := claimBaseTrackingReturnWord baseOut
  have hbase64' : baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  let rdsz : UInt256 := UInt256.ofNat baseOut.size
  have hrdsz_toNat : rdsz.toNat = baseOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hbaseSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hout32
  have rd3724 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3724⟩
      (⟨1⟩ :: claimBaseTrackingPostCallTail I claimed)
      (claimBaseTrackingPostCallMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C := by
    simpa [claimBaseTrackingCallPc, claimBaseTrackingPostCallStack,
      claimBaseTrackingPostCallTail] using rd
  have rd3855₀ := evm_run rd3724 with [
    swap2, dup3, iszero, push2 ⟨3876⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap3, push2 ⟨3844⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push2 ⟨3869⟩, swap2, swap3, pop, push1 ⟨32⟩,
    returndatasize, dup2, gt]
  have rd3855 := rd3855₀
  rw [show UInt256.ofNat baseOut.size = rdsz from rfl, hgt] at rd3855
  have rd3071 := evm_run rd3855 with [
    push2 ⟨734⟩, jumpiNT (by native_decide),
    push2 ⟨719⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide),
    push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0
      (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw
      (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold claimBaseTrackingPostDecodeMem Reasoning.Theory.writeWord
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3106 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, swap1, push2 ⟨3106⟩,
    jump (by jump_dest), jumpdest, swap1, dup2, push1 ⟨32⟩, swap2, sub,
    slt, push2 ⟨1004⟩, jumpiNT (by native_decide)]
  have rd3129 := evm_run rd3106 with [
    raw mload 0 baseWord claimBaseTrackingPostCallAw (by native_decide)
      mem_cost
      (by
        simpa [baseWord] using
          claimBaseTrackingPostDecodeMem_mload256_of_size_ge
            I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup2, and, dup2, sub]
  have hclean : UInt256.land baseWord uint64Mask = baseWord :=
    uint64Mask_clean hbase64'
  have hcleanExpanded :
      UInt256.land baseWord
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = baseWord := by
    simpa [uint64Mask] using hclean
  have hsub :
      UInt256.sub baseWord
        (UInt256.land baseWord
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) = ⟨0⟩ := by
    rw [hcleanExpanded]
    exact u256_sub_self baseWord
  have rd3129zero := rd3129
  rw [hsub] at rd3129zero
  have rd3869 := evm_run rd3129zero with [
    push2 ⟨1004⟩, jumpiNT (by native_decide), swap1, jump (by jump_dest)]
  have rd3739 := evm_run rd3869 with [
    jumpdest, swap1, codesize, push2 ⟨3738⟩, jump (by jump_dest),
    jumpdest, pop]
  exact ⟨_, _, by
    simpa [baseWord, claimBaseTrackingReturnWord] using rd3739⟩

set_option maxHeartbeats 2000000 in
theorem cometRewardsClaimInternalX_getRewardAccrued_upscale_success
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {baseOut : ByteArray}
    {claimed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3740⟩
      [⟨128⟩, claimBaseTrackingReturnWord baseOut, ⟨3432⟩,
        ⟨128⟩, ⟨0⟩, claimSrcWord I, solcAddrMask, ⟨32⟩, claimed,
        UInt256.land (claimSrcWord I) solcAddrMask,
        UInt256.land (claimCometWord I) solcAddrMask, ⟨64⟩, ⟨1001⟩, ⟨64⟩, ⟨0⟩]
      (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hbase64 : (claimBaseTrackingReturnWord baseOut).toNat < EVM.twoPow 64)
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 slot0 ≠ ⟨0⟩)
    (hscaled :
      getRewardAccruedScaledNat multiplier
        (getRewardAccruedUpscaledNat slot0 (claimBaseTrackingReturnWord baseOut)) <
          UInt256.size) :
    ∃ k' C', RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3432⟩
      [ UInt256.ofNat
          (getRewardAccruedReturnNat multiplier
            (getRewardAccruedUpscaledNat slot0 (claimBaseTrackingReturnWord baseOut))),
        ⟨128⟩, ⟨0⟩, claimSrcWord I, solcAddrMask, ⟨32⟩, claimed,
        UInt256.land (claimSrcWord I) solcAddrMask,
        UInt256.land (claimCometWord I) solcAddrMask, ⟨64⟩, ⟨1001⟩, ⟨64⟩, ⟨0⟩]
      (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k' C' := by
  let baseWord : UInt256 := claimBaseTrackingReturnWord baseOut
  let upNat : ℕ := getRewardAccruedUpscaledNat slot0 baseWord
  let scaledNat : ℕ := getRewardAccruedScaledNat multiplier upNat
  have hbase64' : baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  have hup : upNat < UInt256.size := by
    simpa [upNat, baseWord] using
      getRewardAccruedUpscaledNat_lt_size_of_base64
        (slot0 := slot0) (accrued := baseWord) hbase64'
  have hrescale64 : (rewardConfigRescaleFromSlot0 slot0).toNat < EVM.twoPow 64 := by
    simpa [rewardConfigRescaleFromSlot0, EVM.twoPow] using
      rewardConfigRescaleWord_lt slot0
  have hbaseClean :
      UInt256.land baseWord
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = baseWord := by
    simpa [uint64Mask] using uint64Mask_clean hbase64'
  have hbaseCleanLeft :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)
        baseWord = baseWord := by
    rw [u256_land_comm]
    exact hbaseClean
  have hrescaleClean :
      UInt256.land (rewardConfigRescaleFromSlot0 slot0)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) =
        rewardConfigRescaleFromSlot0 slot0 := by
    simpa [uint64Mask] using uint64Mask_clean hrescale64
  have hshouldWord :
      rewardConfigShouldUpscaleFromSlot0 slot0 = ⟨1⟩ :=
    rewardConfigShouldUpscaleFromSlot0_eq_one_of_raw_ne_zero hshould
  have hshouldIsZero :
      UInt256.isZero (rewardConfigShouldUpscaleFromSlot0 slot0) = ⟨0⟩ := by
    rw [hshouldWord]
    native_decide
  have hfirstMulLt :
      baseWord.toNat * (rewardConfigRescaleFromSlot0 slot0).toNat < UInt256.size := by
    simpa [upNat, baseWord, getRewardAccruedUpscaledNat] using hup
  have hfirstFlag :
      UInt256.land
          (UInt256.gt (rewardConfigRescaleFromSlot0 slot0)
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) baseWord))
          (UInt256.isZero (UInt256.isZero baseWord)) = ⟨0⟩ :=
    checkedMulOverflowFlag_zero baseWord (rewardConfigRescaleFromSlot0 slot0) hfirstMulLt
  have hfirstFlagLeft :
      UInt256.land (UInt256.isZero (UInt256.isZero baseWord))
          (UInt256.gt (rewardConfigRescaleFromSlot0 slot0)
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) baseWord)) = ⟨0⟩ := by
    rw [u256_land_comm]
    exact hfirstFlag
  have hfirstMulWord :
      UInt256.mul baseWord (rewardConfigRescaleFromSlot0 slot0) = UInt256.ofNat upNat := by
    simpa [upNat, baseWord, getRewardAccruedUpscaledNat] using
      u256_mul_eq_ofNat_of_lt baseWord (rewardConfigRescaleFromSlot0 slot0) hfirstMulLt
  have hupWordToNat : (UInt256.ofNat upNat).toNat = upNat :=
    UInt256.toNat_ofNat_of_lt hup
  have hsecondMulLt :
      (UInt256.ofNat upNat).toNat * multiplier.toNat < UInt256.size := by
    simpa [hupWordToNat, upNat, baseWord, scaledNat] using hscaled
  have hsecondFlag :
      UInt256.land
          (UInt256.gt multiplier
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat upNat)))
          (UInt256.isZero (UInt256.isZero (UInt256.ofNat upNat))) = ⟨0⟩ :=
    checkedMulOverflowFlag_zero (UInt256.ofNat upNat) multiplier hsecondMulLt
  have hsecondFlagLeft :
      UInt256.land (UInt256.isZero (UInt256.isZero (UInt256.ofNat upNat)))
          (UInt256.gt multiplier
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat upNat))) =
        ⟨0⟩ := by
    rw [u256_land_comm]
    exact hsecondFlag
  have hsecondMulWord :
      UInt256.mul (UInt256.ofNat upNat) multiplier = UInt256.ofNat scaledNat := by
    calc
      UInt256.mul (UInt256.ofNat upNat) multiplier =
          UInt256.ofNat ((UInt256.ofNat upNat).toNat * multiplier.toNat) :=
        u256_mul_eq_ofNat_of_lt (UInt256.ofNat upNat) multiplier hsecondMulLt
      _ = UInt256.ofNat scaledNat := by
        simp [scaledNat, getRewardAccruedScaledNat, hupWordToNat]
  have hdivWord :
      UInt256.div (UInt256.ofNat scaledNat) (⟨1000000000000000000⟩ : UInt256) =
        UInt256.ofNat (getRewardAccruedReturnNat multiplier upNat) := by
    simpa [scaledNat, getRewardAccruedReturnNat] using
      u256_div_factorScale_ofNat (n := scaledNat)
        (by simpa [scaledNat, upNat, baseWord] using hscaled)
  have rd3758 := evm_run rd with [
    push1 ⟨64⟩, dup2, add,
    raw mload 0 (rewardConfigShouldUpscaleFromSlot0 slot0)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (claimBaseTrackingPostDecodeMem_mload192 I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, swap3, dup4, and,
    swap3, swap1, iszero]
  have rd3758' := rd3758
  rw [hbaseCleanLeft, hshouldIsZero] at rd3758'
  have rd3769pre := evm_run rd3758' with [
    push2 ⟨3808⟩, jumpiNT (by native_decide),
    swap1, push1 ⟨96⟩, push2 ⟨3794⟩]
  have rd3769 := rd3769pre.pushConst (⟨1000000000000000000⟩ : UInt256)
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd3671 := evm_run rd3769 with [
    swap5, push2 ⟨3804⟩, swap5, push1 ⟨32⟩, dup6, add,
    raw mload 0 (rewardConfigRescaleFromSlot0 slot0)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (claimBaseTrackingPostDecodeMem_mload160 I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    and, swap1, push2 ⟨3660⟩, jump (by jump_dest),
    jumpdest, dup1, push1 ⟨0⟩, not, div, dup3, gt, dup2, iszero, iszero, and]
  have rd3671' := rd3671
  rw [hrescaleClean, hfirstFlagLeft] at rd3671'
  have rd3794 := evm_run rd3671' with [
    push2 ⟨3252⟩, jumpiNT (by native_decide), mul, swap1, jump (by jump_dest),
    jumpdest]
  have rd3794' := rd3794
  rw [hfirstMulWord] at rd3794'
  have rd3671₂ := evm_run rd3794' with [
    swap2, jumpdest, add,
    raw mload 0 multiplier claimBaseTrackingPostCallAw
      (by native_decide) mem_cost
      (claimBaseTrackingPostDecodeMem_mload224 I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    swap1, push2 ⟨3660⟩, jump (by jump_dest),
    jumpdest, dup1, push1 ⟨0⟩, not, div, dup3, gt, dup2, iszero, iszero, and]
  have rd3671₂' := rd3671₂
  rw [hsecondFlagLeft] at rd3671₂'
  have rd3804 := evm_run rd3671₂' with [
    push2 ⟨3252⟩, jumpiNT (by native_decide), mul, swap1, jump (by jump_dest),
    jumpdest]
  have rd3804' := rd3804
  rw [hsecondMulWord] at rd3804'
  have rd3432 := evm_run rd3804' with [
    div, swap1, jump (by jump_dest)]
  rw [hdivWord] at rd3432
  exact ⟨_, _, by
    simpa [baseWord, upNat, scaledNat, claimBaseTrackingReturnWord] using rd3432⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_panic12_from3161
    {cA gh bl σ σ₀ A I} {g : Sat256} {mem rdata : ByteArray}
    {stack : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3161⟩
      stack mem claimBaseTrackingPostCallAw rdata acc k C)
    (hov : stack.length + 2 ≤ 1024) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        setRewardConfigPanicSelector := by
    rfl
  have rd3172₀ := evm_run rd with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push1 ⟨0⟩]
  have rd3172 := rd3172₀
  rw [hsel] at rd3172
  have rd3173 := evm_run rd3172 with [
    raw mstore 0 (setRewardConfigPanicMem0 mem)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov)]
  have rd3178 := evm_run rd3173 with [
    push1 ⟨18⟩, push1 ⟨4⟩,
    raw mstore 0 (setRewardConfigPanicMem ⟨18⟩ mem)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨36⟩, push1 ⟨0⟩]
  exact evm_run rd3178 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_panic11_from3252
    {cA gh bl σ σ₀ A I} {g : Sat256} {mem rdata : ByteArray}
    {stack : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3252⟩
      stack mem claimBaseTrackingPostCallAw rdata acc k C)
    (hov : stack.length + 2 ≤ 1024) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        setRewardConfigPanicSelector := by
    rfl
  have rd3263₀ := evm_run rd with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push1 ⟨0⟩]
  have rd3263 := rd3263₀
  rw [hsel] at rd3263
  have rd3264 := evm_run rd3263 with [
    raw mstore 0 (setRewardConfigPanicMem0 mem)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov)]
  have rd3269 := evm_run rd3264 with [
    push1 ⟨17⟩, push1 ⟨4⟩,
    raw mstore 0 (setRewardConfigPanicMem ⟨17⟩ mem)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨36⟩, push1 ⟨0⟩]
  exact evm_run rd3269 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem cometRewardsClaimInternalX_getRewardAccrued_upscale_overflow_revert
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {baseOut : ByteArray}
    {claimed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3740⟩
      [⟨128⟩, claimBaseTrackingReturnWord baseOut, ⟨3432⟩,
        ⟨128⟩, ⟨0⟩, claimSrcWord I, solcAddrMask, ⟨32⟩, claimed,
        UInt256.land (claimSrcWord I) solcAddrMask,
        UInt256.land (claimCometWord I) solcAddrMask, ⟨64⟩, ⟨1001⟩, ⟨64⟩, ⟨0⟩]
      (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hbase64 : (claimBaseTrackingReturnWord baseOut).toNat < EVM.twoPow 64)
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 slot0 ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤ getRewardAccruedScaledNat multiplier
        (getRewardAccruedUpscaledNat slot0 (claimBaseTrackingReturnWord baseOut))) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let baseWord : UInt256 := claimBaseTrackingReturnWord baseOut
  let upNat : ℕ := getRewardAccruedUpscaledNat slot0 baseWord
  have hbase64' : baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  have hup : upNat < UInt256.size := by
    simpa [upNat, baseWord] using
      getRewardAccruedUpscaledNat_lt_size_of_base64
        (slot0 := slot0) (accrued := baseWord) hbase64'
  have hrescale64 : (rewardConfigRescaleFromSlot0 slot0).toNat < EVM.twoPow 64 := by
    simpa [rewardConfigRescaleFromSlot0, EVM.twoPow] using
      rewardConfigRescaleWord_lt slot0
  have hbaseClean :
      UInt256.land baseWord
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = baseWord := by
    simpa [uint64Mask] using uint64Mask_clean hbase64'
  have hbaseCleanLeft :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)
        baseWord = baseWord := by
    rw [u256_land_comm]
    exact hbaseClean
  have hrescaleClean :
      UInt256.land (rewardConfigRescaleFromSlot0 slot0)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) =
        rewardConfigRescaleFromSlot0 slot0 := by
    simpa [uint64Mask] using uint64Mask_clean hrescale64
  have hshouldWord :
      rewardConfigShouldUpscaleFromSlot0 slot0 = ⟨1⟩ :=
    rewardConfigShouldUpscaleFromSlot0_eq_one_of_raw_ne_zero hshould
  have hshouldIsZero :
      UInt256.isZero (rewardConfigShouldUpscaleFromSlot0 slot0) = ⟨0⟩ := by
    rw [hshouldWord]
    native_decide
  have hfirstMulLt :
      baseWord.toNat * (rewardConfigRescaleFromSlot0 slot0).toNat < UInt256.size := by
    simpa [upNat, baseWord, getRewardAccruedUpscaledNat] using hup
  have hfirstFlag :
      UInt256.land (UInt256.isZero (UInt256.isZero baseWord))
          (UInt256.gt (rewardConfigRescaleFromSlot0 slot0)
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) baseWord)) = ⟨0⟩ := by
    rw [u256_land_comm]
    exact checkedMulOverflowFlag_zero baseWord (rewardConfigRescaleFromSlot0 slot0)
      hfirstMulLt
  have hfirstMulWord :
      UInt256.mul baseWord (rewardConfigRescaleFromSlot0 slot0) = UInt256.ofNat upNat := by
    simpa [upNat, baseWord, getRewardAccruedUpscaledNat] using
      u256_mul_eq_ofNat_of_lt baseWord (rewardConfigRescaleFromSlot0 slot0) hfirstMulLt
  have hupWordToNat : (UInt256.ofNat upNat).toNat = upNat :=
    UInt256.toNat_ofNat_of_lt hup
  have hsecondOver :
      UInt256.size ≤ (UInt256.ofNat upNat).toNat * multiplier.toNat := by
    simpa [hupWordToNat, upNat, baseWord, getRewardAccruedScaledNat] using hover
  have hsecondFlag :
      UInt256.land (UInt256.isZero (UInt256.isZero (UInt256.ofNat upNat)))
          (UInt256.gt multiplier
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat upNat))) =
        ⟨1⟩ :=
    checkedMulOverflowFlag_one (UInt256.ofNat upNat) multiplier hsecondOver
  have rd3758 := evm_run rd with [
    push1 ⟨64⟩, dup2, add,
    raw mload 0 (rewardConfigShouldUpscaleFromSlot0 slot0)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (claimBaseTrackingPostDecodeMem_mload192 I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, swap3, dup4, and,
    swap3, swap1, iszero]
  have rd3758' := rd3758
  rw [hbaseCleanLeft, hshouldIsZero] at rd3758'
  have rd3769pre := evm_run rd3758' with [
    push2 ⟨3808⟩, jumpiNT (by native_decide),
    swap1, push1 ⟨96⟩, push2 ⟨3794⟩]
  have rd3769 := rd3769pre.pushConst (⟨1000000000000000000⟩ : UInt256)
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd3671 := evm_run rd3769 with [
    swap5, push2 ⟨3804⟩, swap5, push1 ⟨32⟩, dup6, add,
    raw mload 0 (rewardConfigRescaleFromSlot0 slot0)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (claimBaseTrackingPostDecodeMem_mload160 I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    and, swap1, push2 ⟨3660⟩, jump (by jump_dest),
    jumpdest, dup1, push1 ⟨0⟩, not, div, dup3, gt, dup2, iszero, iszero, and]
  have rd3671' := rd3671
  rw [hrescaleClean, hfirstFlag] at rd3671'
  have rd3794 := evm_run rd3671' with [
    push2 ⟨3252⟩, jumpiNT (by native_decide), mul, swap1, jump (by jump_dest),
    jumpdest]
  have rd3794' := rd3794
  rw [hfirstMulWord] at rd3794'
  have rd3671₂ := evm_run rd3794' with [
    swap2, jumpdest, add,
    raw mload 0 multiplier claimBaseTrackingPostCallAw
      (by native_decide) mem_cost
      (claimBaseTrackingPostDecodeMem_mload224 I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    swap1, push2 ⟨3660⟩, jump (by jump_dest),
    jumpdest, dup1, push1 ⟨0⟩, not, div, dup3, gt, dup2, iszero, iszero, and]
  have rd3671₂' := rd3671₂
  rw [hsecondFlag] at rd3671₂'
  have rd3252 := evm_run rd3671₂' with [
    push2 ⟨3252⟩, jumpiT (by native_decide) (by jump_dest)]
  exact cometRewardsClaimInternalX_panic11_from3252 rd3252 (by simp)

set_option maxHeartbeats 2000000 in
theorem cometRewardsClaimInternalX_getRewardAccrued_downscale_success
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {baseOut : ByteArray}
    {claimed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3740⟩
      [⟨128⟩, claimBaseTrackingReturnWord baseOut, ⟨3432⟩,
        ⟨128⟩, ⟨0⟩, claimSrcWord I, solcAddrMask, ⟨32⟩, claimed,
        UInt256.land (claimSrcWord I) solcAddrMask,
        UInt256.land (claimCometWord I) solcAddrMask, ⟨64⟩, ⟨1001⟩, ⟨64⟩, ⟨0⟩]
      (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hbase64 : (claimBaseTrackingReturnWord baseOut).toNat < EVM.twoPow 64)
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 slot0 = ⟨0⟩)
    (hrescaleNZ : rewardConfigRescaleFromSlot0 slot0 ≠ ⟨0⟩)
    (hscaled :
      getRewardAccruedScaledNat multiplier
        (getRewardAccruedDownscaledNat slot0 (claimBaseTrackingReturnWord baseOut)) <
          UInt256.size) :
    ∃ k' C', RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3432⟩
      [ UInt256.ofNat
          (getRewardAccruedReturnNat multiplier
            (getRewardAccruedDownscaledNat slot0 (claimBaseTrackingReturnWord baseOut))),
        ⟨128⟩, ⟨0⟩, claimSrcWord I, solcAddrMask, ⟨32⟩, claimed,
        UInt256.land (claimSrcWord I) solcAddrMask,
        UInt256.land (claimCometWord I) solcAddrMask, ⟨64⟩, ⟨1001⟩, ⟨64⟩, ⟨0⟩]
      (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k' C' := by
  let baseWord : UInt256 := claimBaseTrackingReturnWord baseOut
  let downNat : ℕ := getRewardAccruedDownscaledNat slot0 baseWord
  let scaledNat : ℕ := getRewardAccruedScaledNat multiplier downNat
  have hbase64' : baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  have hbaseClean :
      UInt256.land baseWord
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = baseWord := by
    simpa [uint64Mask] using uint64Mask_clean hbase64'
  have hbaseCleanLeft :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)
        baseWord = baseWord := by
    rw [u256_land_comm]
    exact hbaseClean
  have hrescale64 : (rewardConfigRescaleFromSlot0 slot0).toNat < EVM.twoPow 64 := by
    simpa [rewardConfigRescaleFromSlot0, EVM.twoPow] using
      rewardConfigRescaleWord_lt slot0
  have hrescaleClean :
      UInt256.land (rewardConfigRescaleFromSlot0 slot0)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) =
        rewardConfigRescaleFromSlot0 slot0 := by
    simpa [uint64Mask] using uint64Mask_clean hrescale64
  have hshouldWord :
      rewardConfigShouldUpscaleFromSlot0 slot0 = ⟨0⟩ :=
    rewardConfigShouldUpscaleFromSlot0_eq_zero_of_raw_zero hshould
  have hshouldIsZero :
      UInt256.isZero (rewardConfigShouldUpscaleFromSlot0 slot0) = ⟨1⟩ := by
    rw [hshouldWord]
    native_decide
  have hrescaleIsZero : UInt256.isZero (rewardConfigRescaleFromSlot0 slot0) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hrescaleNZ
  have hdownWord :
      UInt256.div baseWord (rewardConfigRescaleFromSlot0 slot0) = UInt256.ofNat downNat := by
    simpa [downNat, baseWord, getRewardAccruedDownscaledNat] using
      u256_div_eq_ofNat baseWord (rewardConfigRescaleFromSlot0 slot0)
  have hdownLt : downNat < UInt256.size := by
    have hle : downNat ≤ baseWord.toNat := by
      simpa [downNat, getRewardAccruedDownscaledNat] using
        Nat.div_le_self baseWord.toNat (rewardConfigRescaleFromSlot0 slot0).toNat
    exact lt_of_le_of_lt hle baseWord.val.isLt
  have hdownWordToNat : (UInt256.ofNat downNat).toNat = downNat :=
    UInt256.toNat_ofNat_of_lt hdownLt
  have hsecondMulLt :
      (UInt256.ofNat downNat).toNat * multiplier.toNat < UInt256.size := by
    simpa [hdownWordToNat, downNat, baseWord, scaledNat] using hscaled
  have hsecondFlag :
      UInt256.land
          (UInt256.gt multiplier
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat downNat)))
          (UInt256.isZero (UInt256.isZero (UInt256.ofNat downNat))) = ⟨0⟩ :=
    checkedMulOverflowFlag_zero (UInt256.ofNat downNat) multiplier hsecondMulLt
  have hsecondFlagLeft :
      UInt256.land (UInt256.isZero (UInt256.isZero (UInt256.ofNat downNat)))
          (UInt256.gt multiplier
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat downNat))) =
        ⟨0⟩ := by
    rw [u256_land_comm]
    exact hsecondFlag
  have hsecondMulWord :
      UInt256.mul (UInt256.ofNat downNat) multiplier = UInt256.ofNat scaledNat := by
    calc
      UInt256.mul (UInt256.ofNat downNat) multiplier =
          UInt256.ofNat ((UInt256.ofNat downNat).toNat * multiplier.toNat) :=
        u256_mul_eq_ofNat_of_lt (UInt256.ofNat downNat) multiplier hsecondMulLt
      _ = UInt256.ofNat scaledNat := by
        simp [scaledNat, getRewardAccruedScaledNat, hdownWordToNat]
  have hdivWord :
      UInt256.div (UInt256.ofNat scaledNat) (⟨1000000000000000000⟩ : UInt256) =
        UInt256.ofNat (getRewardAccruedReturnNat multiplier downNat) := by
    simpa [scaledNat, getRewardAccruedReturnNat] using
      u256_div_factorScale_ofNat (n := scaledNat)
        (by simpa [scaledNat, downNat, baseWord] using hscaled)
  have rd3758 := evm_run rd with [
    push1 ⟨64⟩, dup2, add,
    raw mload 0 (rewardConfigShouldUpscaleFromSlot0 slot0)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (claimBaseTrackingPostDecodeMem_mload192 I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, swap3, dup4, and,
    swap3, swap1, iszero]
  have rd3758' := rd3758
  rw [hbaseCleanLeft, hshouldIsZero] at rd3758'
  have rd3817 := evm_run rd3758' with [
    push2 ⟨3808⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push1 ⟨32⟩, dup3, add,
    raw mload 0 (rewardConfigRescaleFromSlot0 slot0)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (claimBaseTrackingPostDecodeMem_mload160 I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    and, swap1, dup2, iszero]
  have rd3817' := rd3817
  rw [hrescaleClean, hrescaleIsZero] at rd3817'
  have rd3827pre := evm_run rd3817' with [
    push2 ⟨3161⟩, jumpiNT (by native_decide),
    push1 ⟨96⟩, push2 ⟨3804⟩, swap3]
  have rd3828 := rd3827pre.pushConst (⟨1000000000000000000⟩ : UInt256)
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd3796 := evm_run rd3828 with [
    swap5, div, swap2, push2 ⟨3796⟩, jump (by jump_dest), jumpdest]
  have rd3796' := rd3796
  rw [hdownWord] at rd3796'
  have rd3671₂ := evm_run rd3796' with [
    add,
    raw mload 0 multiplier claimBaseTrackingPostCallAw
      (by native_decide) mem_cost
      (claimBaseTrackingPostDecodeMem_mload224 I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    swap1, push2 ⟨3660⟩, jump (by jump_dest),
    jumpdest, dup1, push1 ⟨0⟩, not, div, dup3, gt, dup2, iszero, iszero, and]
  have rd3671₂' := rd3671₂
  rw [hsecondFlagLeft] at rd3671₂'
  have rd3804 := evm_run rd3671₂' with [
    push2 ⟨3252⟩, jumpiNT (by native_decide), mul, swap1, jump (by jump_dest),
    jumpdest]
  have rd3804' := rd3804
  rw [hsecondMulWord] at rd3804'
  have rd3432 := evm_run rd3804' with [
    div, swap1, jump (by jump_dest)]
  rw [hdivWord] at rd3432
  exact ⟨_, _, by
    simpa [baseWord, downNat, scaledNat, claimBaseTrackingReturnWord] using rd3432⟩

set_option maxHeartbeats 2000000 in
theorem cometRewardsClaimInternalX_getRewardAccrued_downscale_zero_revert
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {baseOut : ByteArray}
    {claimed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3740⟩
      [⟨128⟩, claimBaseTrackingReturnWord baseOut, ⟨3432⟩,
        ⟨128⟩, ⟨0⟩, claimSrcWord I, solcAddrMask, ⟨32⟩, claimed,
        UInt256.land (claimSrcWord I) solcAddrMask,
        UInt256.land (claimCometWord I) solcAddrMask, ⟨64⟩, ⟨1001⟩, ⟨64⟩, ⟨0⟩]
      (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hbase64 : (claimBaseTrackingReturnWord baseOut).toNat < EVM.twoPow 64)
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 slot0 = ⟨0⟩)
    (hrescaleZero : rewardConfigRescaleFromSlot0 slot0 = ⟨0⟩) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let baseWord : UInt256 := claimBaseTrackingReturnWord baseOut
  have hbase64' : baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  have hbaseClean :
      UInt256.land baseWord
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = baseWord := by
    simpa [uint64Mask] using uint64Mask_clean hbase64'
  have hbaseCleanLeft :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)
        baseWord = baseWord := by
    rw [u256_land_comm]
    exact hbaseClean
  have hrescaleClean :
      UInt256.land (rewardConfigRescaleFromSlot0 slot0)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) =
        rewardConfigRescaleFromSlot0 slot0 := by
    rw [hrescaleZero]
    native_decide
  have hshouldWord :
      rewardConfigShouldUpscaleFromSlot0 slot0 = ⟨0⟩ :=
    rewardConfigShouldUpscaleFromSlot0_eq_zero_of_raw_zero hshould
  have hshouldIsZero :
      UInt256.isZero (rewardConfigShouldUpscaleFromSlot0 slot0) = ⟨1⟩ := by
    rw [hshouldWord]
    native_decide
  have hrescaleIsZero : UInt256.isZero (rewardConfigRescaleFromSlot0 slot0) = ⟨1⟩ := by
    rw [hrescaleZero]
    native_decide
  have rd3758 := evm_run rd with [
    push1 ⟨64⟩, dup2, add,
    raw mload 0 (rewardConfigShouldUpscaleFromSlot0 slot0)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (claimBaseTrackingPostDecodeMem_mload192 I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, swap3, dup4, and,
    swap3, swap1, iszero]
  have rd3758' := rd3758
  rw [hbaseCleanLeft, hshouldIsZero] at rd3758'
  have rd3817 := evm_run rd3758' with [
    push2 ⟨3808⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push1 ⟨32⟩, dup3, add,
    raw mload 0 (rewardConfigRescaleFromSlot0 slot0)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (claimBaseTrackingPostDecodeMem_mload160 I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    and, swap1, dup2, iszero]
  have rd3817' := rd3817
  rw [hrescaleClean, hrescaleIsZero] at rd3817'
  have rd3161 := evm_run rd3817' with [
    push2 ⟨3161⟩, jumpiT (by native_decide) (by jump_dest)]
  exact cometRewardsClaimInternalX_panic12_from3161 rd3161 (by simp)

set_option maxHeartbeats 2000000 in
theorem cometRewardsClaimInternalX_getRewardAccrued_downscale_overflow_revert
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier : UInt256} {baseOut : ByteArray}
    {claimed : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3740⟩
      [⟨128⟩, claimBaseTrackingReturnWord baseOut, ⟨3432⟩,
        ⟨128⟩, ⟨0⟩, claimSrcWord I, solcAddrMask, ⟨32⟩, claimed,
        UInt256.land (claimSrcWord I) solcAddrMask,
        UInt256.land (claimCometWord I) solcAddrMask, ⟨64⟩, ⟨1001⟩, ⟨64⟩, ⟨0⟩]
      (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C)
    (hout32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hbase64 : (claimBaseTrackingReturnWord baseOut).toNat < EVM.twoPow 64)
    (hshould : rewardConfigShouldUpscaleRawFromSlot0 slot0 = ⟨0⟩)
    (hrescaleNZ : rewardConfigRescaleFromSlot0 slot0 ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤ getRewardAccruedScaledNat multiplier
        (getRewardAccruedDownscaledNat slot0 (claimBaseTrackingReturnWord baseOut))) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let baseWord : UInt256 := claimBaseTrackingReturnWord baseOut
  let downNat : ℕ := getRewardAccruedDownscaledNat slot0 baseWord
  have hbase64' : baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  have hbaseClean :
      UInt256.land baseWord
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = baseWord := by
    simpa [uint64Mask] using uint64Mask_clean hbase64'
  have hbaseCleanLeft :
      UInt256.land
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)
        baseWord = baseWord := by
    rw [u256_land_comm]
    exact hbaseClean
  have hrescale64 : (rewardConfigRescaleFromSlot0 slot0).toNat < EVM.twoPow 64 := by
    simpa [rewardConfigRescaleFromSlot0, EVM.twoPow] using
      rewardConfigRescaleWord_lt slot0
  have hrescaleClean :
      UInt256.land (rewardConfigRescaleFromSlot0 slot0)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) =
        rewardConfigRescaleFromSlot0 slot0 := by
    simpa [uint64Mask] using uint64Mask_clean hrescale64
  have hshouldWord :
      rewardConfigShouldUpscaleFromSlot0 slot0 = ⟨0⟩ :=
    rewardConfigShouldUpscaleFromSlot0_eq_zero_of_raw_zero hshould
  have hshouldIsZero :
      UInt256.isZero (rewardConfigShouldUpscaleFromSlot0 slot0) = ⟨1⟩ := by
    rw [hshouldWord]
    native_decide
  have hrescaleIsZero : UInt256.isZero (rewardConfigRescaleFromSlot0 slot0) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hrescaleNZ
  have hdownWord :
      UInt256.div baseWord (rewardConfigRescaleFromSlot0 slot0) = UInt256.ofNat downNat := by
    simpa [downNat, baseWord, getRewardAccruedDownscaledNat] using
      u256_div_eq_ofNat baseWord (rewardConfigRescaleFromSlot0 slot0)
  have hdownLt : downNat < UInt256.size := by
    have hle : downNat ≤ baseWord.toNat := by
      simpa [downNat, getRewardAccruedDownscaledNat] using
        Nat.div_le_self baseWord.toNat (rewardConfigRescaleFromSlot0 slot0).toNat
    exact lt_of_le_of_lt hle baseWord.val.isLt
  have hdownWordToNat : (UInt256.ofNat downNat).toNat = downNat :=
    UInt256.toNat_ofNat_of_lt hdownLt
  have hsecondOver :
      UInt256.size ≤ (UInt256.ofNat downNat).toNat * multiplier.toNat := by
    simpa [hdownWordToNat, downNat, baseWord, getRewardAccruedScaledNat] using hover
  have hsecondFlag :
      UInt256.land (UInt256.isZero (UInt256.isZero (UInt256.ofNat downNat)))
          (UInt256.gt multiplier
            (UInt256.div (UInt256.lnot (⟨0⟩ : UInt256)) (UInt256.ofNat downNat))) =
        ⟨1⟩ :=
    checkedMulOverflowFlag_one (UInt256.ofNat downNat) multiplier hsecondOver
  have rd3758 := evm_run rd with [
    push1 ⟨64⟩, dup2, add,
    raw mload 0 (rewardConfigShouldUpscaleFromSlot0 slot0)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (claimBaseTrackingPostDecodeMem_mload192 I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, swap3, dup4, and,
    swap3, swap1, iszero]
  have rd3758' := rd3758
  rw [hbaseCleanLeft, hshouldIsZero] at rd3758'
  have rd3817 := evm_run rd3758' with [
    push2 ⟨3808⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push1 ⟨32⟩, dup3, add,
    raw mload 0 (rewardConfigRescaleFromSlot0 slot0)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (claimBaseTrackingPostDecodeMem_mload160 I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    and, swap1, dup2, iszero]
  have rd3817' := rd3817
  rw [hrescaleClean, hrescaleIsZero] at rd3817'
  have rd3827pre := evm_run rd3817' with [
    push2 ⟨3161⟩, jumpiNT (by native_decide),
    push1 ⟨96⟩, push2 ⟨3804⟩, swap3]
  have rd3828 := rd3827pre.pushConst (⟨1000000000000000000⟩ : UInt256)
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd3796 := evm_run rd3828 with [
    swap5, div, swap2, push2 ⟨3796⟩, jump (by jump_dest), jumpdest]
  have rd3796' := rd3796
  rw [hdownWord] at rd3796'
  have rd3671₂ := evm_run rd3796' with [
    add,
    raw mload 0 multiplier claimBaseTrackingPostCallAw
      (by native_decide) mem_cost
      (claimBaseTrackingPostDecodeMem_mload224 I slot0 multiplier hout32 hbaseSize)
      (by native_decide) (by evm_ov),
    swap1, push2 ⟨3660⟩, jump (by jump_dest),
    jumpdest, dup1, push1 ⟨0⟩, not, div, dup3, gt, dup2, iszero, iszero, and]
  have rd3671₂' := rd3671₂
  rw [hsecondFlag] at rd3671₂'
  have rd3252 := evm_run rd3671₂' with [
    push2 ⟨3252⟩, jumpiT (by native_decide) (by jump_dest)]
  exact cometRewardsClaimInternalX_panic11_from3252 rd3252 (by simp)

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_after_getRewardAccrued_no_transfer
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier accrued claimed : UInt256} {baseOut : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3432⟩
      [ accrued, ⟨128⟩, ⟨0⟩, claimSrcWord I, solcAddrMask, ⟨32⟩, claimed,
        UInt256.land (claimSrcWord I) solcAddrMask,
        UInt256.land (claimCometWord I) solcAddrMask, ⟨64⟩, ⟨1001⟩, ⟨64⟩, ⟨0⟩]
      (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C)
    (hle : accrued.toNat ≤ claimed.toNat) (hbaseSize : baseOut.size < UInt256.size) :
    RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) acc ByteArray.empty := by
  have hgtWord : UInt256.gt accrued claimed = ⟨0⟩ := ugt_zero hle
  have rd3436₀ := evm_run rd with [jumpdest, dup7, dup2, gt]
  have rd3436 := rd3436₀
  rw [hgtWord] at rd3436
  have rd1001 := evm_run rd3436 with [
    push2 ⟨3452⟩, jumpiNT (by native_decide),
    jumpdest, pop, pop, pop, pop, pop, pop, pop, pop, pop, pop,
    jump (by jump_dest), jumpdest]
  have rd1003 := evm_run rd1001 with [
    raw mload 0 ⟨288⟩ claimBaseTrackingPostCallAw (by native_decide)
      mem_cost (claimBaseTrackingPostDecodeMem_mload64 I slot0 multiplier hbaseSize)
      (by native_decide) (by evm_ov)]
  exact RD.ret 0 ByteArray.empty rd1003 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        claimBaseTrackingPostCallAw]
      native_decide)
    (by exact byteArray_readWithPadding_zero _ 288)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_after_getRewardAccrued_to_transfer
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier accrued claimed : UInt256} {baseOut : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3432⟩
      [ accrued, ⟨128⟩, ⟨0⟩, claimSrcWord I, solcAddrMask, ⟨32⟩, claimed,
        UInt256.land (claimSrcWord I) solcAddrMask,
        UInt256.land (claimCometWord I) solcAddrMask, ⟨64⟩, ⟨1001⟩, ⟨64⟩, ⟨0⟩]
      (claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C)
    (hperm : I.perm = true)
    (hcanonComet : (claimCometWord I).toNat < EVM.addressModulus)
    (hcanonSrc : (claimSrcWord I).toNat < EVM.addressModulus)
    (hbaseSize : baseOut.size < UInt256.size)
    (hlt : claimed.toNat < accrued.toNat) :
    ∃ k' C',
      RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3915⟩
        [ rewardConfigTokenFromSlot0 slot0,
          claimSrcWord I,
          accrued.sub claimed,
          ⟨3531⟩,
          ⟨128⟩,
          solcAddrMask,
          claimSrcWord I,
          solcAddrMask,
          ⟨32⟩,
          claimRewardsClaimedBaseSlot,
          UInt256.land (claimSrcWord I) solcAddrMask,
          accrued.sub claimed,
          ⟨64⟩,
          ⟨1001⟩,
          ⟨64⟩,
          ⟨0⟩ ]
        (claimTransferOuterHashMem I slot0 multiplier baseOut)
        claimBaseTrackingPostCallAw baseOut
        (acc.1,
          sstoreAccountMap I.codeOwner acc.2 (getRewardOwedRewardsClaimedSlotOf I)
            accrued)
        k' C' := by
  have hgtWord : UInt256.gt accrued claimed = ⟨1⟩ := ugt_one hlt
  have rd3436₀ := evm_run rd with [jumpdest, dup7, dup2, gt]
  have rd3436 := rd3436₀
  rw [hgtWord] at rd3436
  have rd3452 := evm_run rd3436 with [
    push2 ⟨3452⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  have rd3459 := evm_run rd3452 with [
    dup10, dup6, swap4, push2 ⟨3498⟩]
  have rd3492pre :=
    RD.pushConst (op := .PUSH32) (width := 32) rd3459 claimRewardsClaimedBaseSlot
      (by decide) (by native_decide)
      (by evm_ov)
  have rd3241 := evm_run rd3492pre with [
    swap10, dup5, push2 ⟨3241⟩, jump (by jump_dest)]
  have rd3245₀ := evm_run rd3241 with [jumpdest, dup2, dup2, lt]
  have hltWord : UInt256.lt accrued claimed = ⟨0⟩ := ult_zero (le_of_lt hlt)
  have rd3245 := rd3245₀
  rw [hltWord] at rd3245
  have rd3498 := evm_run rd3245 with [
    push2 ⟨3252⟩, jumpiNT (by native_decide),
    sub, swap1, jump (by jump_dest), jumpdest]
  let postDecodeMem := claimBaseTrackingPostDecodeMem I slot0 multiplier baseOut
  let innerMem := claimTransferInnerHashMem I slot0 multiplier baseOut
  let outerMem := claimTransferOuterHashMem I slot0 multiplier baseOut
  have hpostDecodeSize64 : 64 ≤ postDecodeMem.size := by
    dsimp [postDecodeMem, claimBaseTrackingPostDecodeMem]
    rw [writeWord_size]
    · have hge := claimBaseTrackingPostCallMem_size_ge256 I slot0 multiplier hbaseSize
      omega
    · have hge := claimBaseTrackingPostCallMem_size_ge256 I slot0 multiplier hbaseSize
      have hle :
          64 - (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size = 0 := by
        omega
      rw [hle]
      native_decide
  have rd3501 := evm_run rd3498 with [
    swap11, dup2,
    raw mstore 0
      (wordAt0Mem (UInt256.land (claimCometWord I) solcAddrMask) postDecodeMem)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (by
        dsimp [postDecodeMem]
        unfold wordAt0Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3505 := evm_run rd3501 with [
    push1 ⟨2⟩, dup9,
    raw mstore 0 innerMem claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (by
        dsimp [innerMem, claimTransferInnerHashMem, postDecodeMem]
        unfold twoWordHashMem wordAt32Mem wordAt0Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have hinnerHash :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC (innerMem.readWithPadding 0 64))) =
        solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask) := by
    dsimp [innerMem, claimTransferInnerHashMem]
    exact twoWordHashMem_solcMappingSlot_of_ge ⟨2⟩
      (UInt256.land (claimCometWord I) solcAddrMask) hpostDecodeSize64
  have rd3506 := rd3505.keccak256 0
    (solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask))
    claimBaseTrackingPostCallAw (by native_decide) mem_cost
    hinnerHash (by native_decide) (by evm_ov)
  have rd3510 := evm_run rd3506 with [
    dup9, push1 ⟨0⟩,
    raw mstore 0
      (wordAt0Mem (UInt256.land (claimSrcWord I) solcAddrMask) innerMem)
      claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (by
        dsimp [innerMem]
        unfold wordAt0Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3512 := evm_run rd3510 with [
    dup7,
    raw mstore 0 outerMem claimBaseTrackingPostCallAw (by native_decide) mem_cost
      (by
        dsimp [outerMem, claimTransferOuterHashMem, innerMem, claimTransferInnerHashMem]
        unfold twoWordHashMem wordAt32Mem wordAt0Mem
        rfl)
      (by native_decide) (by evm_ov)]
  have hinnerMemSize64 : 64 ≤ innerMem.size := by
    dsimp [innerMem, claimTransferInnerHashMem]
    rw [twoWordHashMem_size_of_ge
      (UInt256.land (claimCometWord I) solcAddrMask) ⟨2⟩ hpostDecodeSize64]
    exact hpostDecodeSize64
  have houterHashRaw :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC (outerMem.readWithPadding 0 64))) =
        solcMappingSlot
          (solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask))
          (UInt256.land (claimSrcWord I) solcAddrMask) := by
    dsimp [outerMem, claimTransferOuterHashMem]
    exact twoWordHashMem_solcMappingSlot_of_ge
      (solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask))
      (UInt256.land (claimSrcWord I) solcAddrMask) hinnerMemSize64
  have houterHash :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC (outerMem.readWithPadding 0 64))) =
        getRewardOwedRewardsClaimedSlotOf I := by
    rw [houterHashRaw]
    rw [solcAddrMask_clean
      (by simpa [claimCometWord, calldataWord] using hcanonComet)]
    rw [solcAddrMask_clean
      (by simpa [claimSrcWord, calldataWord] using hcanonSrc)]
    rw [getRewardOwedRewardsClaimedSlotOf_eq_solc I
      (by simpa [getRewardOwedCometWord, claimCometWord] using hcanonComet)
      (by simpa [getRewardOwedAccountWord, claimSrcWord] using hcanonSrc)]
  have rd3516pre := (evm_run rd3512 with [dup10, push1 ⟨0⟩]).keccak256 0
    (getRewardOwedRewardsClaimedSlotOf I)
    claimBaseTrackingPostCallAw (by native_decide) mem_cost
    houterHash (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3518⟩ := rd3516pre.sstore hperm (by native_decide) (by evm_ov)
  have hpostDecodeSize160 : 160 ≤ postDecodeMem.size := by
    dsimp [postDecodeMem, claimBaseTrackingPostDecodeMem]
    rw [writeWord_size]
    · have hge := claimBaseTrackingPostCallMem_size_ge256 I slot0 multiplier hbaseSize
      omega
    · have hge := claimBaseTrackingPostCallMem_size_ge256 I slot0 multiplier hbaseSize
      have hle :
          64 - (claimBaseTrackingPostCallMem I slot0 multiplier baseOut).size = 0 := by
        omega
      rw [hle]
      native_decide
  have hinnerMemSize160 : 160 ≤ innerMem.size := by
    dsimp [innerMem, claimTransferInnerHashMem]
    rw [twoWordHashMem_size_of_ge
      (UInt256.land (claimCometWord I) solcAddrMask) ⟨2⟩ hpostDecodeSize64]
    exact hpostDecodeSize160
  have houterMemSize160 : 160 ≤ outerMem.size := by
    dsimp [outerMem, claimTransferOuterHashMem]
    rw [twoWordHashMem_size_of_ge
      (UInt256.land (claimSrcWord I) solcAddrMask)
      (solcMappingSlot ⟨2⟩ (UInt256.land (claimCometWord I) solcAddrMask))
      hinnerMemSize64]
    exact hinnerMemSize160
  have houterMem_read128 :
      outerMem.readWithPadding 128 32 =
        UInt256.toByteArray (rewardConfigTokenFromSlot0 slot0) := by
    dsimp [outerMem, claimTransferOuterHashMem, innerMem, claimTransferInnerHashMem,
      postDecodeMem]
    rw [twoWordHashMem_read_above64_of_ge]
    · rw [twoWordHashMem_read_above64_of_ge]
      · exact claimBaseTrackingPostDecodeMem_read128 I slot0 multiplier hbaseSize
      · exact hpostDecodeSize160
      · norm_num
    · exact hinnerMemSize160
    · norm_num
  have houterMem_mload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ outerMem.size
          ∨ (⟨128⟩ : UInt256) ≥ claimBaseTrackingPostCallAw * ⟨32⟩ then
        ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (outerMem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        rewardConfigTokenFromSlot0 slot0 := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨128⟩ : UInt256)) (aw := claimBaseTrackingPostCallAw)
      (v := rewardConfigTokenFromSlot0 slot0)
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        omega)
      (by native_decide)
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        exact houterMem_read128)
  have rd3530 := evm_run rd3518 with [
    push2 ⟨3531⟩, dup9, dup5, dup5, dup5,
    raw mload 0 (rewardConfigTokenFromSlot0 slot0) claimBaseTrackingPostCallAw
      (by native_decide) mem_cost houterMem_mload128 (by native_decide) (by evm_ov),
    and, push2 ⟨3915⟩, jump (by jump_dest)]
  have htokenClean := rewardConfigTokenFromSlot0_clean slot0
  rw [htokenClean] at rd3530
  exact ⟨_, _, by
    simpa [outerMem, innerMem, postDecodeMem, claimTransferOuterHashMem,
      claimTransferInnerHashMem] using rd3530⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_call_transfer_from3915
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier amount : UInt256} {baseOut : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3915⟩
      [ rewardConfigTokenFromSlot0 slot0,
        claimSrcWord I,
        amount,
        ⟨3531⟩,
        ⟨128⟩,
        solcAddrMask,
        claimSrcWord I,
        solcAddrMask,
        ⟨32⟩,
        claimRewardsClaimedBaseSlot,
        UInt256.land (claimSrcWord I) solcAddrMask,
        amount,
        ⟨64⟩,
        ⟨1001⟩,
        ⟨64⟩,
        ⟨0⟩ ]
      (claimTransferOuterHashMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut acc k C)
    (hcanonSrc : (claimSrcWord I).toNat < EVM.addressModulus)
    (hbaseSize : baseOut.size < UInt256.size) :
    ∃ gasArg k' C',
      RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
        claimTransferCallPc
        (gasArg :: UInt256.land solcAddrMask (rewardConfigTokenFromSlot0 slot0) ::
          ⟨0⟩ :: ⟨288⟩ :: claimTransferCallSize :: ⟨288⟩ :: ⟨32⟩ ::
          claimTransferPostCallTail I amount)
        (claimTransferCalldataMem I slot0 multiplier baseOut (claimSrcWord I) amount)
        claimTransferCallAw baseOut acc k' C' := by
  have hcleanTo :
      UInt256.land (claimSrcWord I) solcAddrMask = claimSrcWord I := by
    exact solcAddrMask_clean (by simpa [claimSrcWord, calldataWord] using hcanonSrc)
  have rd3932 := evm_run rd with [
    jumpdest, push1 ⟨32⟩, push1 ⟨64⟩,
    raw mload 0 ⟨288⟩ claimBaseTrackingPostCallAw (by native_decide)
      mem_cost (claimTransferOuterHashMem_mload64 I slot0 multiplier hbaseSize)
      (by native_decide) (by evm_ov),
    dup1, swap3, push4 ⟨2835717307⟩, push1 ⟨224⟩, shl, dup3,
    raw mstore 0 (claimTransferSelectorMem I slot0 multiplier baseOut)
      (UInt256.ofNat 10) (by native_decide) mem_cost
      (by
        rw [show (⟨288⟩ : UInt256).toNat = 288 from by decide])
      (by native_decide) (by evm_ov)]
  have rd3949 := evm_run rd3932 with [
    dup2, push1 ⟨0⟩, dup2, push2 ⟨3950⟩, dup10, dup10, push1 ⟨4⟩, dup5,
    add, push2 ⟨3888⟩, jump (by native_decide)]
  have rd3901₀ := evm_run rd3949 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2, and,
    dup2]
  have rd3901 := rd3901₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd3901
  have rd3902 := evm_run rd3901 with [
    raw mstore 3 (claimTransferArgsMem I slot0 multiplier baseOut (claimSrcWord I))
      (UInt256.ofNat 11) (by decide) mem_cost
      (by
        rw [show (⟨288⟩ : UInt256) + ⟨4⟩ = ⟨292⟩ from by decide,
          show (⟨292⟩ : UInt256).toNat = 292 from by decide]
        unfold claimTransferArgsMem
        rw [hcleanTo])
      (by native_decide) (by evm_ov)]
  have rd3913 := evm_run rd3902 with [
    push1 ⟨32⟩, dup2, add, swap2, swap1, swap2,
    raw mstore 3 (claimTransferCalldataMem I slot0 multiplier baseOut (claimSrcWord I) amount)
      claimTransferCallAw (by decide) mem_cost
      (by
        rw [show (⟨288⟩ : UInt256) + ⟨4⟩ + ⟨32⟩ = ⟨324⟩ from by decide,
          show (⟨324⟩ : UInt256).toNat = 324 from by decide])
      (by native_decide) (by evm_ov),
    push1 ⟨64⟩, add, swap1]
  have rd3962₀ := evm_run rd3913 with [
    jump (by native_decide), jumpdest, sub, swap3, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, and]
  have rd3962 := rd3962₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd3962
  obtain ⟨gasArg, rd3963⟩ := evm_run rd3962 with [gas]
  exact ⟨gasArg, _, _, by
    simpa [claimTransferCallPc, claimTransferCallSize, claimTransferPostCallTail,
      claimTransferCallAw] using rd3963⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_call_transfer_made_from3915
    {cA gh bl σ₀ σ_start A I} {g : UInt256}
    {cAcur : Batteries.RBSet AccountAddress compare} {σcur_evm : AccountMap}
    {slot0 multiplier amount : UInt256} {baseOut : ByteArray} {k C : ℕ}
    (evmSolm : EVM.State)
    (hperm : I.perm = true)
    (hcanonSrc : (claimSrcWord I).toNat < EVM.addressModulus)
    (hdepth : I.depth.val < 1024)
    (hbaseSize : baseOut.size < UInt256.size)
    (hAccounts : accountMapEquiv σcur_evm evmSolm.accountMap)
    (hCreated : evmSolm.createdAccounts = cAcur)
    (hGenesis : evmSolm.genesisBlockHeader = gh)
    (hBlocks : evmSolm.blocks = bl)
    (hOriginal : evmSolm.σ₀ = σ₀)
    (hEnv : evmSolm.executionEnv = I)
    (rd3915 : RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_start σ₀ (Sat256.ofUInt256 g) A I) ⟨3915⟩
      [ rewardConfigTokenFromSlot0 slot0,
        claimSrcWord I,
        amount,
        ⟨3531⟩,
        ⟨128⟩,
        solcAddrMask,
        claimSrcWord I,
        solcAddrMask,
        ⟨32⟩,
        claimRewardsClaimedBaseSlot,
        UInt256.land (claimSrcWord I) solcAddrMask,
        amount,
        ⟨64⟩,
        ⟨1001⟩,
        ⟨64⟩,
        ⟨0⟩ ]
      (claimTransferOuterHashMem I slot0 multiplier baseOut)
      claimBaseTrackingPostCallAw baseOut (cAcur, σcur_evm) k C) :
    ∃ cA' σ'_evm σ'_solm A'_solm z out k' C',
      typedCallViaEVM config evmSolm
        (EVM.address (claimTransferTarget slot0)) "transfer" 0
        (claimTransferArgs I amount)
        (z,
          { evmSolm with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          out) true ∧
      accountMapEquiv σ'_evm σ'_solm ∧
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_start σ₀ (Sat256.ofUInt256 g) A I)
        (claimTransferCallPc + ⟨1⟩) (claimTransferPostCallStack z I amount)
        (claimTransferPostCallMem I slot0 multiplier baseOut out amount)
        claimTransferPostCallAw out (cA', σ'_evm) k' C' ∧
      out.size < 2 ^ 255 := by
  obtain ⟨gasArg, k0, C0, rd3963⟩ :=
    cometRewardsClaimInternalX_call_transfer_from3915
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_start) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) (slot0 := slot0) (multiplier := multiplier)
      (amount := amount) (baseOut := baseOut) rd3915 hcanonSrc hbaseSize
  have rd3963Call :
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_start σ₀ (Sat256.ofUInt256 g) A I)
        claimTransferCallPc
        (gasArg :: UInt256.land solcAddrMask (rewardConfigTokenFromSlot0 slot0) ::
          ⟨0⟩ :: ⟨288⟩ :: claimTransferCallSize :: ⟨288⟩ :: ⟨32⟩ ::
          claimTransferPostCallTail I amount)
        (claimTransferCalldataMem I slot0 multiplier baseOut (claimSrcWord I) amount)
        claimTransferCallAw baseOut (cAcur, σcur_evm) k0 C0 := by
    simpa [claimTransferPostCallTail] using rd3963
  have hdecCall :
      decode cometRewardsBytecode claimTransferCallPc = some (.CALL, .none) := by
    unfold claimTransferCallPc
    rw [withdrawTokenTransferCallPc_eq]
    native_decide
  obtain ⟨cA', σ'_evm, z, out, A_in, callGas, k', C', hΘ, rd3964, houtSize⟩ :=
    RD.call (t := claimTransferPostCallTail I amount) rd3963Call hdecCall hdepth
      (by simp [claimTransferPostCallTail])
  obtain ⟨g'', A'_evm, hΘeq⟩ := hΘ
  let evmEvm : EVM.State :=
    initState cAcur gh bl σcur_evm σ₀ (Sat256.ofUInt256 g) evmSolm.substate I
  have houtSmall : out.size < 2 ^ 138 := by
    exact Theta_returnData_size_lt_2pow138_of_eq
      (blob := I.blobVersionedHashes) (cA := cAcur)
      (gh :=
        (initState cA gh bl σ_start σ₀ (Sat256.ofUInt256 g) A I).genesisBlockHeader)
      (blocks := (initState cA gh bl σ_start σ₀ (Sat256.ofUInt256 g) A I).blocks)
      (σ := σcur_evm)
      (σ₀ := (initState cA gh bl σ_start σ₀ (Sat256.ofUInt256 g) A I).σ₀)
      (A := A_in)
      (s := AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner))
      (o := I.sender)
      (r := AccountAddress.ofUInt256
        (UInt256.land solcAddrMask (rewardConfigTokenFromSlot0 slot0)))
      (c := toExecute σcur_evm
        (AccountAddress.ofUInt256
          (UInt256.land solcAddrMask (rewardConfigTokenFromSlot0 slot0))))
      (g := callGas) (p := UInt256.ofNat I.gasPrice)
      (v := ⟨0⟩) (v' := ⟨0⟩)
      (d := (claimTransferCalldataMem I slot0 multiplier baseOut (claimSrcWord I) amount)
        |>.readWithPadding (⟨288⟩ : UInt256).toNat claimTransferCallSize.toNat)
      (e := I.depth + 1) (H := I.header) (w := I.perm)
      hΘeq
      (by exact Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)
  have houtSign : out.size < 2 ^ 255 := by omega
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hEq
    rw [hEq] at hdepth
    exact absurd hdepth (by decide)
  have hdepthNe : evmEvm.executionEnv.depth ≠ 1024 := by
    simpa [evmEvm, initState] using hdepthNeI
  have htgt := claimTransferTarget_eq_targetWord slot0
  have hcd :=
    claimTransferCalldataMem_encode_args
      I slot0 multiplier amount hbaseSize hcanonSrc
  have hcallE :
      typedCallViaEVM config evmEvm
        (EVM.address (claimTransferTarget slot0)) "transfer" 0
        (claimTransferArgs I amount)
        (z,
          { evmEvm with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          out) true := by
    refine callCoincides
      (cfg := config) (evm := evmEvm)
      (name := "transfer") (args := claimTransferArgs I amount)
      (tgt := EVM.address (claimTransferTarget slot0))
      (targetWord := UInt256.land solcAddrMask (rewardConfigTokenFromSlot0 slot0))
      (cA' := cA') (σ' := σ'_evm) (A' := A'_evm) (A_in := A_in)
      (z := z) (o := out) (g'' := g'') (callGas := callGas)
      (mem := claimTransferCalldataMem I slot0 multiplier baseOut (claimSrcWord I) amount)
      (inOff := ⟨288⟩) (inSize := claimTransferCallSize)
      (callPerm := true)
      hdepthNe htgt hcd ?_
    simpa [evmEvm, initState, hperm] using hΘeq
  obtain ⟨σ'_solm, A'_solm, hcallSolm, hPostAccounts⟩ :=
    typedCallViaEVM_accountMapEquiv
      (evm_solm := evmSolm) hcallE
      (by simpa [evmEvm, initState] using hAccounts)
      (by simp [evmEvm, initState, hOriginal])
      (by simp [evmEvm, initState, hCreated])
      (by simp [evmEvm, initState, hGenesis])
      (by simp [evmEvm, initState, hBlocks])
      (by simp [evmEvm, initState])
      (by simp [evmEvm, initState, hEnv])
  exact ⟨cA', σ'_evm, σ'_solm, A'_solm, z, out, k', C',
    hcallSolm, hPostAccounts, by
      simpa [claimTransferPostCallStack, claimTransferPostCallTail,
        claimTransferPostCallMem, claimTransferPostCallAw, claimTransferCallSize]
        using rd3964,
    houtSign⟩

theorem claimTransferPostCallMem_read288_of_size_ge
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut out : ByteArray}
    (amount : UInt256) (hbaseSize : baseOut.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (claimTransferPostCallMem I slot0 multiplier baseOut out amount).readWithPadding 288 32 =
      out.extract 0 32 := by
  unfold claimTransferPostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size)
      (by decide) hout32 houtSize
  rw [hlen]
  exact write32_read_back out
    (claimTransferCalldataMem I slot0 multiplier baseOut (claimSrcWord I) amount)
    288 hout32
    (by
      have hge :=
        claimTransferCalldataMem_size_ge356 I slot0 multiplier (claimSrcWord I) amount
          hbaseSize
      omega)

theorem claimTransferPostCallMem_size_ge320
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut out : ByteArray}
    (amount : UInt256) (hbaseSize : baseOut.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    320 ≤ (claimTransferPostCallMem I slot0 multiplier baseOut out amount).size := by
  unfold claimTransferPostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size)
      (by decide) hout32 houtSize
  rw [hlen]
  rw [write32_eq out
    (claimTransferCalldataMem I slot0 multiplier baseOut (claimSrcWord I) amount)
    288 hout32
    (by
      have hge :=
        claimTransferCalldataMem_size_ge356 I slot0 multiplier (claimSrcWord I) amount
          hbaseSize
      omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract]
  have hbase :=
    claimTransferCalldataMem_size_ge356 I slot0 multiplier (claimSrcWord I) amount
      hbaseSize
  omega

theorem claimTransferPostCallMem_mload288_haw :
    ¬ (⟨288⟩ : UInt256) ≥ claimTransferPostCallAw * ⟨32⟩ := by
  native_decide

theorem claimTransferPostCallMem_mload288_of_size_ge
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut out : ByteArray}
    (amount : UInt256) (hbaseSize : baseOut.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (if (⟨288⟩ : UInt256).toNat ≥
          (claimTransferPostCallMem I slot0 multiplier baseOut out amount).size
        ∨ (⟨288⟩ : UInt256) ≥ claimTransferPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((claimTransferPostCallMem I slot0 multiplier baseOut out amount)
          |>.readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := claimTransferPostCallMem I slot0 multiplier baseOut out amount)
    (aw := claimTransferPostCallAw)
    (off := ⟨288⟩)
    (memSize := (claimTransferPostCallMem I slot0 multiplier baseOut out amount).size)
    rfl
    (by
      rw [show (⟨288⟩ : UInt256).toNat = 288 from by decide]
      exact lt_of_lt_of_le (by omega)
        (claimTransferPostCallMem_size_ge320
          I slot0 multiplier amount hbaseSize hout32 houtSize))
    claimTransferPostCallMem_mload288_haw
    |>.trans (by
      rw [show (⟨288⟩ : UInt256).toNat = 288 from by decide,
        claimTransferPostCallMem_read288_of_size_ge
          I slot0 multiplier amount hbaseSize hout32 houtSize])

noncomputable abbrev claimTransferPostDecodeMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (baseOut out : ByteArray)
    (amount : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨320⟩ : UInt256)).write 0
    (claimTransferPostCallMem I slot0 multiplier baseOut out amount) 64 32

theorem claimTransferPostDecodeMem_read288_of_size_ge
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut out : ByteArray}
    (amount : UInt256) (hbaseSize : baseOut.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (claimTransferPostDecodeMem I slot0 multiplier baseOut out amount).readWithPadding 288 32 =
      out.extract 0 32 := by
  unfold claimTransferPostDecodeMem
  rw [write32_read_above (UInt256.toByteArray (⟨320⟩ : UInt256))
    (claimTransferPostCallMem I slot0 multiplier baseOut out amount) 64 288
    (by rw [toByteArray_size])
    (by
      have hge := claimTransferPostCallMem_size_ge320
        I slot0 multiplier amount hbaseSize hout32 houtSize
      omega)
    (by omega)
    (by
      have hge := claimTransferPostCallMem_size_ge320
        I slot0 multiplier amount hbaseSize hout32 houtSize
      omega)]
  exact claimTransferPostCallMem_read288_of_size_ge
    I slot0 multiplier amount hbaseSize hout32 houtSize

theorem claimTransferPostDecodeMem_mload288_of_size_ge
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut out : ByteArray}
    (amount : UInt256) (hbaseSize : baseOut.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (if (⟨288⟩ : UInt256).toNat ≥
          (claimTransferPostDecodeMem I slot0 multiplier baseOut out amount).size
        ∨ (⟨288⟩ : UInt256) ≥ claimTransferPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((claimTransferPostDecodeMem I slot0 multiplier baseOut out amount)
          |>.readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := claimTransferPostDecodeMem I slot0 multiplier baseOut out amount)
    (aw := claimTransferPostCallAw) (off := ⟨288⟩)
    (memSize := (claimTransferPostDecodeMem I slot0 multiplier baseOut out amount).size)
    rfl
    (by
      rw [show (⟨288⟩ : UInt256).toNat = 288 from by decide]
      unfold claimTransferPostDecodeMem
      rw [write32_eq (UInt256.toByteArray (⟨320⟩ : UInt256))
        (claimTransferPostCallMem I slot0 multiplier baseOut out amount) 64
        (by rw [toByteArray_size])
        (by
          have hge := claimTransferPostCallMem_size_ge320
            I slot0 multiplier amount hbaseSize hout32 houtSize
          omega)]
      simp
      have hsz := claimTransferPostCallMem_size_ge320
        I slot0 multiplier amount hbaseSize hout32 houtSize
      omega)
    claimTransferPostCallMem_mload288_haw
    |>.trans (by
      rw [show (⟨288⟩ : UInt256).toNat = 288 from by decide,
        claimTransferPostDecodeMem_read288_of_size_ge
          I slot0 multiplier amount hbaseSize hout32 houtSize])

theorem claimTransferPostDecodeMem_mload64
    (I : ExecutionEnv) (slot0 multiplier : UInt256) {baseOut out : ByteArray}
    (amount : UInt256) (hbaseSize : baseOut.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (claimTransferPostDecodeMem I slot0 multiplier baseOut out amount).size
        ∨ (⟨64⟩ : UInt256) ≥ claimTransferPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((claimTransferPostDecodeMem I slot0 multiplier baseOut out amount)
          |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨320⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := claimTransferPostCallAw) (v := ⟨320⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      unfold claimTransferPostDecodeMem
      rw [write32_eq (UInt256.toByteArray (⟨320⟩ : UInt256))
        (claimTransferPostCallMem I slot0 multiplier baseOut out amount) 64
        (by rw [toByteArray_size])
        (by
          have hge := claimTransferPostCallMem_size_ge320
            I slot0 multiplier amount hbaseSize hout32 houtSize
          omega)]
      simp
      have hsz := claimTransferPostCallMem_size_ge320
        I slot0 multiplier amount hbaseSize hout32 houtSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      unfold claimTransferPostDecodeMem
      rw [write32_read_back _ _ 64 (by rw [toByteArray_size])
        (by
          have hge := claimTransferPostCallMem_size_ge320
            I slot0 multiplier amount hbaseSize hout32 houtSize
          omega)]
      rw [show (UInt256.toByteArray (⟨320⟩ : UInt256)).extract 0 32 =
          UInt256.toByteArray (⟨320⟩ : UInt256) by
        rw [show 32 = (UInt256.toByteArray (⟨320⟩ : UInt256)).size by
          rw [toByteArray_size]]
        exact byteArray_extract_self _])

noncomputable abbrev claimTransferPostShortDecodeMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (baseOut out : ByteArray)
    (amount : UInt256) : ByteArray :=
  (UInt256.toByteArray ((⟨288⟩ : UInt256) +
    UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat out.size + ⟨31⟩))).write 0
      (claimTransferPostCallMem I slot0 multiplier baseOut out amount) 64 32

noncomputable abbrev claimTransferOutFailedSelectorMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (baseOut out : ByteArray)
    (amount : UInt256) : ByteArray :=
  (UInt256.toByteArray withdrawTokenTransferOutFailedSelectorShifted).write 0
    (claimTransferPostDecodeMem I slot0 multiplier baseOut out amount) 320 32

noncomputable abbrev claimTransferOutFailedArgsMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (baseOut out : ByteArray)
    (amount : UInt256) : ByteArray :=
  (UInt256.toByteArray (UInt256.land (claimSrcWord I) solcAddrMask)).write 0
    (claimTransferOutFailedSelectorMem I slot0 multiplier baseOut out amount) 324 32

noncomputable abbrev claimTransferOutFailedMem
    (I : ExecutionEnv) (slot0 multiplier : UInt256) (baseOut out : ByteArray)
    (amount : UInt256) : ByteArray :=
  (UInt256.toByteArray amount).write 0
    (claimTransferOutFailedArgsMem I slot0 multiplier baseOut out amount) 356 32

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_after_transfer_failure
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier amount : UInt256} {baseOut out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (claimTransferCallPc + ⟨1⟩) (claimTransferPostCallStack false I amount)
      (claimTransferPostCallMem I slot0 multiplier baseOut out amount)
      claimTransferPostCallAw out acc k C)
    (houtSize : out.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd3964 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3964⟩ (claimTransferPostCallStack false I amount)
      (claimTransferPostCallMem I slot0 multiplier baseOut out amount)
      claimTransferPostCallAw out acc k C := by
    unfold claimTransferCallPc at rd
    simpa [withdrawTokenTransferCallPc_eq] using rd
  have rd3876 := evm_run rd3964 with [
    swap1, dup2, iszero, push2 ⟨3876⟩,
    jumpiT (by native_decide) (by jump_dest)]
  let fp : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥
          (claimTransferPostCallMem I slot0 multiplier baseOut out amount).size
        ∨ (⟨64⟩ : UInt256) ≥ claimTransferPostCallAw * ⟨32⟩ then
      ⟨0⟩
    else
      UInt256.ofNat (fromByteArrayBigEndian
        ((claimTransferPostCallMem I slot0 multiplier baseOut out amount)
          |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtSize
  have rd3880pre := evm_run rd3876 with [jumpdest, push1 ⟨64⟩]
  have rd3880 := RD.mload 0 fp claimTransferPostCallAw rd3880pre (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        claimTransferPostCallAw, claimTransferCallSize]
      native_decide)
    (by rfl)
    (by native_decide)
    (by simp)
  have rd3884pre := evm_run rd3880 with [returndatasize, push1 ⟨0⟩, dup3]
  let mem2 : ByteArray :=
    out.write 0 (claimTransferPostCallMem I slot0 multiplier baseOut out amount)
      fp.toNat rdsz.toNat
  let aw2 : UInt256 :=
    UInt256.ofNat (MachineState.M claimTransferPostCallAw.toNat fp.toNat rdsz.toNat)
  have rd3885 := RD.returndatacopy
    (Cₘ aw2 - Cₘ claimTransferPostCallAw) mem2 aw2 rd3884pre (by native_decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hrdsz_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2, rdsz])
    (by rfl)
    (by rfl)
    (by simp)
  have rd3887 := evm_run rd3885 with [returndatasize, swap1]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M aw2.toNat fp.toNat rdsz.toNat)) - Cₘ aw2)
    rd3887 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, rdsz])
    (by simp)

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_after_transfer_toBoolCheck
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier amount : UInt256} {baseOut out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (claimTransferCallPc + ⟨1⟩) (claimTransferPostCallStack true I amount)
      (claimTransferPostCallMem I slot0 multiplier baseOut out amount)
      claimTransferPostCallAw out acc k C)
    (hbaseSize : baseOut.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    ∃ k' C', RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3287⟩
      (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) :: ⟨4044⟩ ::
        claimSrcWord I :: amount :: ⟨3531⟩ :: ⟨128⟩ :: solcAddrMask ::
        claimSrcWord I :: solcAddrMask :: ⟨32⟩ :: claimRewardsClaimedBaseSlot ::
        UInt256.land (claimSrcWord I) solcAddrMask :: amount :: ⟨64⟩ :: ⟨1001⟩ ::
        ⟨64⟩ :: ⟨0⟩ :: [])
      (claimTransferPostDecodeMem I slot0 multiplier baseOut out amount)
      claimTransferPostCallAw out acc k' C' := by
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hout32
  have rd3964 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3964⟩ (claimTransferPostCallStack true I amount)
      (claimTransferPostCallMem I slot0 multiplier baseOut out amount)
      claimTransferPostCallAw out acc k C := by
    unfold claimTransferCallPc at rd
    simpa [withdrawTokenTransferCallPc_eq] using rd
  have rd4031₀ := evm_run rd3964 with [
    swap1, dup2, iszero, push2 ⟨3876⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap2, push2 ⟨4020⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push2 ⟨4044⟩, swap2, pop, push1 ⟨32⟩, returndatasize, dup2, gt]
  have rd4031 := rd4031₀
  rw [show UInt256.ofNat out.size = rdsz from rfl, hgt] at rd4031
  have rd3071 := evm_run rd4031 with [
    push2 ⟨2249⟩, jumpiNT (by native_decide),
    push2 ⟨2235⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2, add,
    swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt, swap1, dup3,
    lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (claimTransferPostDecodeMem I slot0 multiplier baseOut out amount)
      claimTransferPostCallAw
      (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold claimTransferPostDecodeMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3274 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, swap1, push2 ⟨3274⟩,
    jump (by jump_dest)]
  have rd3286 := evm_run rd3274 with [
    jumpdest, swap1, dup2, push1 ⟨32⟩, swap2, sub, slt, push2 ⟨1004⟩,
    jumpiNT (by native_decide)]
  exact ⟨_, _, evm_run rd3286 with [
    raw mload 0 (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
      claimTransferPostCallAw (by native_decide) mem_cost
      (claimTransferPostDecodeMem_mload288_of_size_ge
        I slot0 multiplier amount hbaseSize hout32 houtSize)
      (by native_decide) (by evm_ov)]⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_after_transfer_short_revert
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier amount : UInt256} {baseOut out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (claimTransferCallPc + ⟨1⟩) (claimTransferPostCallStack true I amount)
      (claimTransferPostCallMem I slot0 multiplier baseOut out amount)
      claimTransferPostCallAw out acc k C)
    (hshort : out.size < 32) (houtSize : out.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨1⟩ := by
    apply ugt_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hshort
  have rd3964 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3964⟩ (claimTransferPostCallStack true I amount)
      (claimTransferPostCallMem I slot0 multiplier baseOut out amount)
      claimTransferPostCallAw out acc k C := by
    unfold claimTransferCallPc at rd
    simpa [withdrawTokenTransferCallPc_eq] using rd
  have rd4031₀ := evm_run rd3964 with [
    swap1, dup2, iszero, push2 ⟨3876⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap2, push2 ⟨4020⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push2 ⟨4044⟩, swap2, pop, push1 ⟨32⟩, returndatasize, dup2, gt]
  have rd4031 := rd4031₀
  rw [show UInt256.ofNat out.size = rdsz from rfl, hgt] at rd4031
  let rounded : UInt256 :=
    UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat out.size + ⟨31⟩)
  let ptr : UInt256 := (⟨288⟩ : UInt256) + rounded
  have hroundedLe : rounded.toNat ≤ out.size + 31 := by
    unfold rounded
    rw [uland_toNat]
    refine le_trans Nat.and_le_right ?_
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt houtSize,
      show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    exact Nat.mod_le _ _
  have hptr_toNat : ptr.toNat = 288 + rounded.toNat := by
    unfold ptr
    rw [uadd_toNat, show (⟨288⟩ : UInt256).toNat = 288 from by decide]
    exact Nat.mod_eq_of_lt (by
      have hroundSmall : rounded.toNat < 64 := by omega
      have hsz : UInt256.size = 2 ^ 256 := by decide
      omega)
  have hltPtr : UInt256.lt ptr (⟨288⟩ : UInt256) = ⟨0⟩ := by
    apply ult_zero
    rw [hptr_toNat, show (⟨288⟩ : UInt256).toNat = 288 from by decide]
    omega
  have hmax64 :
      (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩).toNat =
        18446744073709551615 := by
    native_decide
  have hgtPtr :
      UInt256.gt ptr (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    rw [hptr_toNat, hmax64]
    omega
  have hallocOk :
      UInt256.lor (UInt256.lt ptr (⟨288⟩ : UInt256))
        (UInt256.gt ptr (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)) = ⟨0⟩ := by
    rw [hltPtr, hgtPtr]
    native_decide
  have rd3071 := evm_run rd4031 with [
    push2 ⟨2249⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, returndatasize, push2 ⟨2225⟩, jump (by jump_dest),
    jumpdest, push2 ⟨2235⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2, add,
    swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt, swap1, dup3,
    lt, lor, push2 ⟨3003⟩, jumpiNT (by simpa [ptr, rounded] using hallocOk),
    push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (claimTransferPostShortDecodeMem I slot0 multiplier baseOut out amount)
      claimTransferPostCallAw
      (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
      (by native_decide) (by evm_ov)]
  have rd3274 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, swap1, push2 ⟨3274⟩,
    jump (by jump_dest)]
  have hlenCheck :
      UInt256.slt (UInt256.sub ((⟨288⟩ : UInt256) + rdsz) ⟨288⟩) ⟨32⟩ = ⟨1⟩ := by
    simpa [rdsz] using
      solcReturnStaticLenCheckShort (base := 288) (words := 1) (by simpa using hshort)
        (by norm_num [UInt256.size])
        (by
          have hsz : UInt256.size = 2 ^ 256 := by decide
          omega)
        (by norm_num)
  have rd3282₀ := evm_run rd3274 with [
    jumpdest, swap1, dup2, push1 ⟨32⟩, swap2, sub, slt]
  have rd3282 := rd3282₀
  rw [hlenCheck] at rd3282
  have rd1004 := evm_run rd3282 with [
    push2 ⟨1004⟩, jumpiT (by native_decide) (by jump_dest)]
  exact evm_run rd1004 with [
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_after_transfer_noncanon_revert
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier amount : UInt256} {baseOut out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (claimTransferCallPc + ⟨1⟩) (claimTransferPostCallStack true I amount)
      (claimTransferPostCallMem I slot0 multiplier baseOut out amount)
      claimTransferPostCallAw out acc k C)
    (hbaseSize : baseOut.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size)
    (hnz : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨0⟩)
    (hno : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨1⟩) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let word : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
  have hnzWord : word ≠ ⟨0⟩ := by simpa [word] using hnz
  have hnoWord : word ≠ ⟨1⟩ := by simpa [word] using hno
  have hiszero : UInt256.isZero word = ⟨0⟩ := isZero_eq_zero_of_ne hnzWord
  have hsub : UInt256.sub word (UInt256.isZero (⟨0⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by native_decide]
    exact u256_sub_ne_zero_of_ne hnoWord
  obtain ⟨kBool, CBool, rd3287₀⟩ :=
    cometRewardsClaimInternalX_after_transfer_toBoolCheck
      (slot0 := slot0) (multiplier := multiplier) (amount := amount)
      rd hbaseSize hout32 houtSize
  have rd3287 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3287⟩
      (word :: ⟨4044⟩ :: claimSrcWord I :: amount :: ⟨3531⟩ :: ⟨128⟩ ::
        solcAddrMask :: claimSrcWord I :: solcAddrMask :: ⟨32⟩ ::
        claimRewardsClaimedBaseSlot :: UInt256.land (claimSrcWord I) solcAddrMask ::
        amount :: ⟨64⟩ :: ⟨1001⟩ :: ⟨64⟩ :: ⟨0⟩ :: [])
      (claimTransferPostDecodeMem I slot0 multiplier baseOut out amount)
      claimTransferPostCallAw out acc kBool CBool := by
    simpa [word] using rd3287₀
  have rd3292 := evm_run rd3287 with [dup1, iszero, iszero, dup2, sub]
  rw [hiszero] at rd3292
  have rd1004 := evm_run rd3292 with [
    push2 ⟨1004⟩, jumpiT hsub (by jump_dest)]
  exact evm_run rd1004 with [
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_after_transfer_false_revert
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier amount : UInt256} {baseOut out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (claimTransferCallPc + ⟨1⟩) (claimTransferPostCallStack true I amount)
      (claimTransferPostCallMem I slot0 multiplier baseOut out amount)
      claimTransferPostCallAw out acc k C)
    (hbaseSize : baseOut.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3287₀⟩ :=
    cometRewardsClaimInternalX_after_transfer_toBoolCheck
      (slot0 := slot0) (multiplier := multiplier) (amount := amount)
      rd hbaseSize hout32 houtSize
  have rd3287 := rd3287₀
  rw [hword] at rd3287
  have rd3988 := evm_run rd3287 with [
    dup1, iszero, iszero, dup2, sub, push2 ⟨1004⟩, jumpiNT (by native_decide),
    swap1, jump (by jump_dest), jumpdest, codesize, push2 ⟨3978⟩, jump (by jump_dest),
    jumpdest, pop, iszero, push2 ⟨3988⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd3994 := evm_run rd3988 with [jumpdest, push2 ⟨4016⟩, push1 ⟨64⟩]
  have rd3995 := evm_run rd3994 with [
    raw mload 0 ⟨320⟩ claimTransferPostCallAw (by native_decide)
      mem_cost (claimTransferPostDecodeMem_mload64
        I slot0 multiplier amount hbaseSize hout32 houtSize)
      (by native_decide) (by evm_ov)]
  have rd4007 := evm_run rd3995 with [
    swap3, dup4, swap3, push4 withdrawTokenTransferOutFailedSelectorWord,
    push1 ⟨224⟩, shl, dup5,
    raw mstore 0 (claimTransferOutFailedSelectorMem I slot0 multiplier baseOut out amount)
      claimTransferPostCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨320⟩ : UInt256).toNat = 320 from by decide])
      (by native_decide) (by evm_ov)]
  have rd3901 := evm_run rd4007 with [
    push1 ⟨4⟩, dup5, add, push2 ⟨3888⟩, jump (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2,
    and, dup2]
  have rd3902 := evm_run rd3901 with [
    raw mstore 0 (claimTransferOutFailedArgsMem I slot0 multiplier baseOut out amount)
      claimTransferPostCallAw (by native_decide) mem_cost
      (by
        rw [show ((⟨320⟩ : UInt256) + ⟨4⟩).toNat = 324 from by native_decide]
        unfold claimTransferOutFailedArgsMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3909 := evm_run rd3902 with [
    push1 ⟨32⟩, dup2, add, swap2, swap1, swap2,
    raw mstore (Cₘ (UInt256.ofNat 13) - Cₘ claimTransferPostCallAw)
      (claimTransferOutFailedMem I slot0 multiplier baseOut out amount) (UInt256.ofNat 13)
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          claimTransferPostCallAw]
        native_decide)
      (by
        rw [show ((⟨320⟩ : UInt256) + ⟨4⟩ + ⟨32⟩).toNat = 356 from by native_decide])
      (by native_decide) (by evm_ov)]
  exact evm_run rd3909 with [
    push1 ⟨64⟩, add, swap1, jump (by jump_dest), jumpdest, sub, swap1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsClaimInternalX_after_transfer_true_return
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {slot0 multiplier amount : UInt256} {baseOut out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (claimTransferCallPc + ⟨1⟩) (claimTransferPostCallStack true I amount)
      (claimTransferPostCallMem I slot0 multiplier baseOut out amount)
      claimTransferPostCallAw out acc k C)
    (hbaseSize : baseOut.size < UInt256.size)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨1⟩) :
    RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) acc ByteArray.empty := by
  obtain ⟨_, _, rd3287₀⟩ :=
    cometRewardsClaimInternalX_after_transfer_toBoolCheck
      (slot0 := slot0) (multiplier := multiplier) (amount := amount)
      rd hbaseSize hout32 houtSize
  have rd3287 := rd3287₀
  rw [hword] at rd3287
  have rd3978 := evm_run rd3287 with [
    dup1, iszero, iszero, dup2, sub, push2 ⟨1004⟩, jumpiNT (by native_decide),
    swap1, jump (by jump_dest), jumpdest, codesize, push2 ⟨3978⟩, jump (by jump_dest)]
  have rd3531 := evm_run rd3978 with [
    jumpdest, pop, iszero, push2 ⟨3988⟩, jumpiNT (by native_decide),
    pop, pop, jump (by jump_dest), jumpdest]
  have rd1001 := evm_run rd3531 with [
    pop, pop, pop, pop, pop, pop, pop, pop, pop,
    jump (by jump_dest), jumpdest]
  have rd1003 := evm_run rd1001 with [
    raw mload 0 ⟨320⟩ claimTransferPostCallAw (by native_decide)
      mem_cost (claimTransferPostDecodeMem_mload64
        I slot0 multiplier amount hbaseSize hout32 houtSize)
      (by native_decide) (by evm_ov)]
  exact RD.ret 0 ByteArray.empty rd1003 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, claimTransferPostCallAw]
      native_decide)
    (by exact byteArray_readWithPadding_zero _ 320)
    (by simp)

theorem cometRewardsClaimInternalBodyReverts_tokenZero (evm : EVM.State) (I : ExecutionEnv)
    (hz : rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evm I) = ⟨0⟩) :
    ExecFuncBody config { contract := contract, locals := claimInternalStore I } evm
      claimInternalFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [claimInternalFunction, checkedExternalCallStmts, claimInternalConfigLocals,
    claimInternalAfterShouldLocals, claimInternalAfterRescaleLocals,
    claimInternalAfterTokenLocals] using
    (((((ABlock.start.letStep
      (evalExpr_getRewardOwed_token_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalStore_comet I)
        (claimInternalStore_no_rewardConfig I))).letStep
      (evalExpr_getRewardOwed_rescale_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalAfterTokenLocals_comet evm I)
        (claimInternalAfterTokenLocals_no_rewardConfig evm I))).letStep
      (evalExpr_getRewardOwed_shouldUpscale_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalAfterRescaleLocals_comet evm I)
        (claimInternalAfterRescaleLocals_no_rewardConfig evm I))).letStep
      (evalExpr_getRewardOwed_multiplier_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalAfterShouldLocals_comet evm I)
        (claimInternalAfterShouldLocals_no_rewardConfig evm I))).requireRevert
      (evalExpr_getRewardOwed_token_ne_zero_false_of evm (getRewardOwedSlot0Load evm I)
        (claimInternalConfigLocals_token evm I) hz))

theorem cometRewardsClaimInternalBodyReverts_noAccrue_getRewardAccrued
    (evm evmBase : EVM.State) (I : ExecutionEnv) {baseOut : ByteArray}
    (hnz : rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evm I) ≠ ⟨0⟩)
    (hshouldZero : claimShouldAccrueWord I = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (false, evmBase, baseOut) false) :
    ExecFuncBody config { contract := contract, locals := claimInternalStore I } evm
      claimInternalFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hinner :
      ExecFuncBody config
        { contract := contract,
          locals := getRewardAccruedStore I (getRewardOwedSlot0Load evm I)
            (getRewardOwedMultiplierLoad evm I) }
        evm getRewardAccruedFunction.body .reverted := by
    exact getRewardAccruedBodyReverts_callFailure evm evmBase I
      (getRewardOwedSlot0Load evm I) (getRewardOwedMultiplierLoad evm I) hcallBase
  have hrest :
      ExecBlock config { contract := contract, locals := claimInternalConfigLocals evm I }
        evm
        [ .ite (.var "shouldAccrue")
            (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
              [.var "src"] "_accrued")
            [],
          .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "src"))),
          .internalCall "getRewardAccrued"
            [.var "comet", .var "src", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier"] "accrued",
          .ite (.binary .gt (.var "accrued") (.var "claimed"))
            [ .letDecl "owed" (some uint256)
                (.binary .sub (.var "accrued") (.var "claimed")),
              .assign .storage (rewardsClaimedRef (.var "comet") (.var "src"))
                (.var "accrued"),
              .internalCall "doTransferOut" [.var "token", .var "to", .var "owed"]
                "_sent" ]
            [] ]
        .reverted := by
    refine ExecBlock.consNormal
      (solm' := { contract := contract, locals := claimInternalConfigLocals evm I })
      (evm' := evm) ?hite ?_
    · exact ExecStmt.iteFalse
        (evalExpr_claimInternal_shouldAccrue_false evm I hshouldZero)
        ExecBlock.nil
    refine ExecBlock.consNormal
      (solm' := { contract := contract, locals := claimInternalAfterClaimedLocals evm evm I })
      (evm' := evm) ?hclaimed ?_
    · exact ExecStmt.letDecl (evalExpr_claim_claimed_config evm I)
    refine ExecBlock.consRevert ?_
    exact internalCallFunctionRevert
      (cfg := config)
      (caller :=
        { contract := contract,
          locals := claimInternalAfterClaimedLocals evm evm I })
      (evm := evm)
      (name := "getRewardAccrued") (retVar := "accrued")
      (args := [.var "comet", .var "src", .var "rescaleFactor",
        .var "shouldUpscale", .var "multiplier"])
      (argVals := getRewardAccruedArgs I (getRewardOwedSlot0Load evm I)
        (getRewardOwedMultiplierLoad evm I))
      (callee := getRewardAccruedFunction)
      (locals := getRewardAccruedStore I (getRewardOwedSlot0Load evm I)
        (getRewardOwedMultiplierLoad evm I))
      (evalExprs_claim_getRewardAccruedArgs_afterClaimed evm evm I)
      lookupCallable_getRewardAccrued
      (bindParams_getRewardAccrued I (getRewardOwedSlot0Load evm I)
        (getRewardOwedMultiplierLoad evm I))
      hinner
  simpa [claimInternalFunction, checkedExternalCallStmts, claimInternalConfigLocals,
    claimInternalAfterShouldLocals, claimInternalAfterRescaleLocals,
    claimInternalAfterTokenLocals] using
    (((((ABlock.start.letStep
      (evalExpr_getRewardOwed_token_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalStore_comet I)
        (claimInternalStore_no_rewardConfig I))).letStep
      (evalExpr_getRewardOwed_rescale_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalAfterTokenLocals_comet evm I)
        (claimInternalAfterTokenLocals_no_rewardConfig evm I))).letStep
      (evalExpr_getRewardOwed_shouldUpscale_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalAfterRescaleLocals_comet evm I)
        (claimInternalAfterRescaleLocals_no_rewardConfig evm I))).letStep
      (evalExpr_getRewardOwed_multiplier_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalAfterShouldLocals_comet evm I)
        (claimInternalAfterShouldLocals_no_rewardConfig evm I))).requireStep
      (evalExpr_getRewardOwed_token_ne_zero_true_of evm (getRewardOwedSlot0Load evm I)
        (claimInternalConfigLocals_token evm I) hnz)).run hrest

theorem cometRewardsClaimInternalBodyReverts_noAccrue_getRewardAccrued_decode
    (evm evmBase : EVM.State) (I : ExecutionEnv) {baseOut : ByteArray}
    (hnz : rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evm I) ≠ ⟨0⟩)
    (hshouldZero : claimShouldAccrueWord I = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm (EVM.address (getRewardOwedCometTarget I))
        "baseTrackingAccrued" 0 (getRewardAccruedBaseTrackingArgs I)
        (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseTrackingAccrued" baseOut = none) :
    ExecFuncBody config { contract := contract, locals := claimInternalStore I } evm
      claimInternalFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hinner :
      ExecFuncBody config
        { contract := contract,
          locals := getRewardAccruedStore I (getRewardOwedSlot0Load evm I)
            (getRewardOwedMultiplierLoad evm I) }
        evm getRewardAccruedFunction.body .reverted := by
    exact getRewardAccruedBodyReverts_decode evm evmBase I
      (getRewardOwedSlot0Load evm I) (getRewardOwedMultiplierLoad evm I)
      hcallBase hdecBase
  have hrest :
      ExecBlock config { contract := contract, locals := claimInternalConfigLocals evm I }
        evm
        [ .ite (.var "shouldAccrue")
            (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
              [.var "src"] "_accrued")
            [],
          .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "src"))),
          .internalCall "getRewardAccrued"
            [.var "comet", .var "src", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier"] "accrued",
          .ite (.binary .gt (.var "accrued") (.var "claimed"))
            [ .letDecl "owed" (some uint256)
                (.binary .sub (.var "accrued") (.var "claimed")),
              .assign .storage (rewardsClaimedRef (.var "comet") (.var "src"))
                (.var "accrued"),
              .internalCall "doTransferOut" [.var "token", .var "to", .var "owed"]
                "_sent" ]
            [] ]
        .reverted := by
    refine ExecBlock.consNormal
      (solm' := { contract := contract, locals := claimInternalConfigLocals evm I })
      (evm' := evm) ?hite ?_
    · exact ExecStmt.iteFalse
        (evalExpr_claimInternal_shouldAccrue_false evm I hshouldZero)
        ExecBlock.nil
    refine ExecBlock.consNormal
      (solm' := { contract := contract, locals := claimInternalAfterClaimedLocals evm evm I })
      (evm' := evm) ?hclaimed ?_
    · exact ExecStmt.letDecl (evalExpr_claim_claimed_config evm I)
    refine ExecBlock.consRevert ?_
    exact internalCallFunctionRevert
      (cfg := config)
      (caller :=
        { contract := contract,
          locals := claimInternalAfterClaimedLocals evm evm I })
      (evm := evm)
      (name := "getRewardAccrued") (retVar := "accrued")
      (args := [.var "comet", .var "src", .var "rescaleFactor",
        .var "shouldUpscale", .var "multiplier"])
      (argVals := getRewardAccruedArgs I (getRewardOwedSlot0Load evm I)
        (getRewardOwedMultiplierLoad evm I))
      (callee := getRewardAccruedFunction)
      (locals := getRewardAccruedStore I (getRewardOwedSlot0Load evm I)
        (getRewardOwedMultiplierLoad evm I))
      (evalExprs_claim_getRewardAccruedArgs_afterClaimed evm evm I)
      lookupCallable_getRewardAccrued
      (bindParams_getRewardAccrued I (getRewardOwedSlot0Load evm I)
        (getRewardOwedMultiplierLoad evm I))
      hinner
  simpa [claimInternalFunction, checkedExternalCallStmts, claimInternalConfigLocals,
    claimInternalAfterShouldLocals, claimInternalAfterRescaleLocals,
    claimInternalAfterTokenLocals] using
    (((((ABlock.start.letStep
      (evalExpr_getRewardOwed_token_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalStore_comet I)
        (claimInternalStore_no_rewardConfig I))).letStep
      (evalExpr_getRewardOwed_rescale_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalAfterTokenLocals_comet evm I)
        (claimInternalAfterTokenLocals_no_rewardConfig evm I))).letStep
      (evalExpr_getRewardOwed_shouldUpscale_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalAfterRescaleLocals_comet evm I)
        (claimInternalAfterRescaleLocals_no_rewardConfig evm I))).letStep
      (evalExpr_getRewardOwed_multiplier_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalAfterShouldLocals_comet evm I)
        (claimInternalAfterShouldLocals_no_rewardConfig evm I))).requireStep
      (evalExpr_getRewardOwed_token_ne_zero_true_of evm (getRewardOwedSlot0Load evm I)
        (claimInternalConfigLocals_token evm I) hnz)).run hrest

theorem cometRewardsClaimInternalBodyReverts_noAccrue_getRewardAccrued_inner
    (evm : EVM.State) (I : ExecutionEnv)
    (hnz : rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evm I) ≠ ⟨0⟩)
    (hshouldZero : claimShouldAccrueWord I = ⟨0⟩)
    (hinner :
      ExecFuncBody config
        { contract := contract,
          locals := getRewardAccruedStore I (getRewardOwedSlot0Load evm I)
            (getRewardOwedMultiplierLoad evm I) }
        evm getRewardAccruedFunction.body .reverted) :
    ExecFuncBody config { contract := contract, locals := claimInternalStore I } evm
      claimInternalFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hrest :
      ExecBlock config { contract := contract, locals := claimInternalConfigLocals evm I }
        evm
        [ .ite (.var "shouldAccrue")
            (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
              [.var "src"] "_accrued")
            [],
          .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "src"))),
          .internalCall "getRewardAccrued"
            [.var "comet", .var "src", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier"] "accrued",
          .ite (.binary .gt (.var "accrued") (.var "claimed"))
            [ .letDecl "owed" (some uint256)
                (.binary .sub (.var "accrued") (.var "claimed")),
              .assign .storage (rewardsClaimedRef (.var "comet") (.var "src"))
                (.var "accrued"),
              .internalCall "doTransferOut" [.var "token", .var "to", .var "owed"]
                "_sent" ]
            [] ]
        .reverted := by
    refine ExecBlock.consNormal
      (solm' := { contract := contract, locals := claimInternalConfigLocals evm I })
      (evm' := evm) ?hite ?_
    · exact ExecStmt.iteFalse
        (evalExpr_claimInternal_shouldAccrue_false evm I hshouldZero)
        ExecBlock.nil
    refine ExecBlock.consNormal
      (solm' := { contract := contract, locals := claimInternalAfterClaimedLocals evm evm I })
      (evm' := evm) ?hclaimed ?_
    · exact ExecStmt.letDecl (evalExpr_claim_claimed_config evm I)
    refine ExecBlock.consRevert ?_
    exact internalCallFunctionRevert
      (cfg := config)
      (caller :=
        { contract := contract,
          locals := claimInternalAfterClaimedLocals evm evm I })
      (evm := evm)
      (name := "getRewardAccrued") (retVar := "accrued")
      (args := [.var "comet", .var "src", .var "rescaleFactor",
        .var "shouldUpscale", .var "multiplier"])
      (argVals := getRewardAccruedArgs I (getRewardOwedSlot0Load evm I)
        (getRewardOwedMultiplierLoad evm I))
      (callee := getRewardAccruedFunction)
      (locals := getRewardAccruedStore I (getRewardOwedSlot0Load evm I)
        (getRewardOwedMultiplierLoad evm I))
      (evalExprs_claim_getRewardAccruedArgs_afterClaimed evm evm I)
      lookupCallable_getRewardAccrued
      (bindParams_getRewardAccrued I (getRewardOwedSlot0Load evm I)
        (getRewardOwedMultiplierLoad evm I))
      hinner
  simpa [claimInternalFunction, checkedExternalCallStmts, claimInternalConfigLocals,
    claimInternalAfterShouldLocals, claimInternalAfterRescaleLocals,
    claimInternalAfterTokenLocals] using
    (((((ABlock.start.letStep
      (evalExpr_getRewardOwed_token_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalStore_comet I)
        (claimInternalStore_no_rewardConfig I))).letStep
      (evalExpr_getRewardOwed_rescale_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalAfterTokenLocals_comet evm I)
        (claimInternalAfterTokenLocals_no_rewardConfig evm I))).letStep
      (evalExpr_getRewardOwed_shouldUpscale_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalAfterRescaleLocals_comet evm I)
        (claimInternalAfterRescaleLocals_no_rewardConfig evm I))).letStep
      (evalExpr_getRewardOwed_multiplier_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalAfterShouldLocals_comet evm I)
        (claimInternalAfterShouldLocals_no_rewardConfig evm I))).requireStep
      (evalExpr_getRewardOwed_token_ne_zero_true_of evm (getRewardOwedSlot0Load evm I)
        (claimInternalConfigLocals_token evm I) hnz)).run hrest

theorem cometRewardsClaimInternalBodyReturns_noAccrue_noTransfer
    (evm evmBase : EVM.State) (I : ExecutionEnv) {accruedNat : ℕ}
    {calleeSolm : Frame}
    (hnz : rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evm I) ≠ ⟨0⟩)
    (hshouldZero : claimShouldAccrueWord I = ⟨0⟩)
    (hinner :
      ExecFuncBody config
        { contract := contract,
          locals := getRewardAccruedStore I (getRewardOwedSlot0Load evm I)
            (getRewardOwedMultiplierLoad evm I) }
        evm getRewardAccruedFunction.body
        (.returned calleeSolm evmBase (some [.int (Int.ofNat accruedNat)])))
    (hle : accruedNat ≤ (getRewardOwedClaimedLoad evm I).toNat) :
    ExecFuncBody config { contract := contract, locals := claimInternalStore I } evm
      claimInternalFunction.body
      (.returned
        { contract := contract, locals := claimInternalAfterInternalLocals evm evm I accruedNat }
        evmBase none) := by
  refine ExecFuncBody.execBlockOK ?_
  have hrest :
      ExecBlock config { contract := contract, locals := claimInternalConfigLocals evm I }
        evm
        [ .ite (.var "shouldAccrue")
            (checkedExternalCallStmts (.var "comet") "accrueAccount" (.intLit 0)
              [.var "src"] "_accrued")
            [],
          .letDecl "claimed" (some uint256)
            (.storage (rewardsClaimedRef (.var "comet") (.var "src"))),
          .internalCall "getRewardAccrued"
            [.var "comet", .var "src", .var "rescaleFactor",
              .var "shouldUpscale", .var "multiplier"] "accrued",
          .ite (.binary .gt (.var "accrued") (.var "claimed"))
            [ .letDecl "owed" (some uint256)
                (.binary .sub (.var "accrued") (.var "claimed")),
              .assign .storage (rewardsClaimedRef (.var "comet") (.var "src"))
                (.var "accrued"),
              .internalCall "doTransferOut" [.var "token", .var "to", .var "owed"]
                "_sent" ]
            [] ]
        (.ok
          { contract := contract, locals := claimInternalAfterInternalLocals evm evm I accruedNat }
          evmBase) := by
    refine ExecBlock.consNormal
      (solm' := { contract := contract, locals := claimInternalConfigLocals evm I })
      (evm' := evm) ?hite ?_
    · exact ExecStmt.iteFalse
        (evalExpr_claimInternal_shouldAccrue_false evm I hshouldZero)
        ExecBlock.nil
    refine ExecBlock.consNormal
      (solm' := { contract := contract, locals := claimInternalAfterClaimedLocals evm evm I })
      (evm' := evm) ?hclaimed ?_
    · exact ExecStmt.letDecl (evalExpr_claim_claimed_config evm I)
    refine ExecBlock.consNormal
      (solm' :=
        { contract := contract, locals := claimInternalAfterInternalLocals evm evm I accruedNat })
      (evm' := evmBase) ?hinternal ?_
    · simpa [resumeAfterInternalCall, claimInternalAfterInternalLocals, collapseReturns]
        using internalCallFunctionReturn
        (cfg := config)
        (caller :=
          { contract := contract,
            locals := claimInternalAfterClaimedLocals evm evm I })
        (evm := evm) (calleeEvm := evmBase)
        (name := "getRewardAccrued") (retVar := "accrued")
        (args := [.var "comet", .var "src", .var "rescaleFactor",
          .var "shouldUpscale", .var "multiplier"])
        (argVals := getRewardAccruedArgs I (getRewardOwedSlot0Load evm I)
          (getRewardOwedMultiplierLoad evm I))
        (callee := getRewardAccruedFunction)
        (locals := getRewardAccruedStore I (getRewardOwedSlot0Load evm I)
          (getRewardOwedMultiplierLoad evm I))
        (calleeSolm := calleeSolm)
        (value := some [.int (Int.ofNat accruedNat)])
        (evalExprs_claim_getRewardAccruedArgs_afterClaimed evm evm I)
        lookupCallable_getRewardAccrued
        (bindParams_getRewardAccrued I (getRewardOwedSlot0Load evm I)
          (getRewardOwedMultiplierLoad evm I))
        hinner
    refine ExecBlock.consNormal
      (solm' :=
        { contract := contract, locals := claimInternalAfterInternalLocals evm evm I accruedNat })
      (evm' := evmBase) ?hiteClaim ?_
    · exact ExecStmt.iteFalse
        (evalExpr_claimInternal_accrued_gt_claimed_false evm evm evmBase I accruedNat hle)
        ExecBlock.nil
    exact ExecBlock.nil
  simpa [claimInternalFunction, checkedExternalCallStmts, claimInternalConfigLocals,
    claimInternalAfterShouldLocals, claimInternalAfterRescaleLocals,
    claimInternalAfterTokenLocals] using
    (((((ABlock.start.letStep
      (evalExpr_getRewardOwed_token_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalStore_comet I)
        (claimInternalStore_no_rewardConfig I))).letStep
      (evalExpr_getRewardOwed_rescale_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalAfterTokenLocals_comet evm I)
        (claimInternalAfterTokenLocals_no_rewardConfig evm I))).letStep
      (evalExpr_getRewardOwed_shouldUpscale_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalAfterRescaleLocals_comet evm I)
        (claimInternalAfterRescaleLocals_no_rewardConfig evm I))).letStep
      (evalExpr_getRewardOwed_multiplier_of evm I
        (by
          simpa [claimCometValue, claimCometWord, getRewardOwedCometValue,
            getRewardOwedCometWord] using claimInternalAfterShouldLocals_comet evm I)
        (claimInternalAfterShouldLocals_no_rewardConfig evm I))).requireStep
      (evalExpr_getRewardOwed_token_ne_zero_true_of evm (getRewardOwedSlot0Load evm I)
        (claimInternalConfigLocals_token evm I) hnz)).run hrest

theorem cometRewardsClaimBodyReverts_internal
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hinner :
      ExecFuncBody config { contract := contract, locals := claimInternalStore I } evm
        claimInternalFunction.body .reverted) :
    ExecTransitionBody config contract evm (claimStore I)
      claimTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (claimFrame evm I) evm
        (.internalCall "claimInternal"
          [.var "comet", .var "src", .var "src", .var "shouldAccrue"] "_claim")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := claimFrame evm I) (evm := evm)
      (name := "claimInternal") (retVar := "_claim")
      (args := [.var "comet", .var "src", .var "src", .var "shouldAccrue"])
      (argVals := claimInternalArgs I) (callee := claimInternalFunction)
      (locals := claimInternalStore I)
      (evalExprs_claim_internalArgs_frame evm I)
      (by simpa [claimFrame] using lookupCallable_claimInternal)
      (bindParams_claimInternal I)
      (by simpa [claimFrame] using hinner)
  simpa [claimTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    ((((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      change evalExpr? config { contract := contract, locals := claimStore I } evm
        (.env .msgData) = .ok (.bytes evm.executionEnv.calldata)
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (claimStore I) hsize)).run
          (ExecBlock.consRevert hstmt))

theorem cometRewardsClaimBodyReturns_internal
    (evm evm' : EVM.State) (I : ExecutionEnv) {calleeSolm : Frame}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hinner :
      ExecFuncBody config { contract := contract, locals := claimInternalStore I } evm
        claimInternalFunction.body (.returned calleeSolm evm' none)) :
    ExecTransitionBody config contract evm (claimStore I)
      claimTransition.body
      (.returned (resumeAfterInternalCall (claimFrame evm I) "_claim" none) evm' none) := by
  refine ExecFuncBody.execBlockOK ?_
  have hstmt :
      ExecStmt config (claimFrame evm I) evm
        (.internalCall "claimInternal"
          [.var "comet", .var "src", .var "src", .var "shouldAccrue"] "_claim")
        (.ok (resumeAfterInternalCall (claimFrame evm I) "_claim" none) evm') := by
    exact internalCallFunctionReturn
      (cfg := config) (caller := claimFrame evm I) (evm := evm)
      (calleeEvm := evm') (name := "claimInternal") (retVar := "_claim")
      (args := [.var "comet", .var "src", .var "src", .var "shouldAccrue"])
      (argVals := claimInternalArgs I) (callee := claimInternalFunction)
      (locals := claimInternalStore I) (calleeSolm := calleeSolm)
      (value := none)
      (evalExprs_claim_internalArgs_frame evm I)
      (by simpa [claimFrame] using lookupCallable_claimInternal)
      (bindParams_claimInternal I)
      (by simpa [claimFrame] using hinner)
  simpa [claimTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    ((((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      change evalExpr? config { contract := contract, locals := claimStore I } evm
        (.env .msgData) = .ok (.bytes evm.executionEnv.calldata)
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (claimStore I) hsize)).run
          (ExecBlock.consNormal hstmt ExecBlock.nil))

set_option maxHeartbeats 2000000 in
/-- `claim(address,address,bool)` body, reached at pc 942. -/
theorem cometRewardsClaimBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cometRewardsBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cometRewardsSelBytes 8))
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) claimPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz4 := cometRewardsClaimSelector_size hsel
  have hd := cometRewardsDispatch_claim (cd := I.calldata) hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonComet : (claimCometWord I).toNat < EVM.addressModulus
      · by_cases hcanonSrc : (claimSrcWord I).toNat < EVM.addressModulus
        · by_cases hzero : claimShouldAccrueWord I = ⟨0⟩
          · have hdec := cometRewardsDecode_claim_ok
              (I := I) hsz100 hhi hcanonComet hcanonSrc (Or.inl hzero)
            have hslotWord :
                getRewardOwedRewardConfigSlot0Word σ_evm I =
                  getRewardOwedRewardConfigSlot0Word σ_solm I :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner
                (getRewardOwedRewardConfigSlotOf I) ⟨0⟩
            by_cases htokenZero :
                rewardConfigTokenFromSlot0
                  (getRewardOwedRewardConfigSlot0Word σ_evm I) = ⟨0⟩
            · let evmSolm : EVM.State :=
                initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
              have htokenZeroSolm :
                  rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evmSolm I) = ⟨0⟩ := by
                have hload :
                    getRewardOwedSlot0Load evmSolm I =
                      getRewardOwedRewardConfigSlot0Word σ_solm I := by
                  simp [evmSolm, getRewardOwedSlot0Load, getRewardOwedRewardConfigSlot0Word,
                    initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
                rw [hload, ← hslotWord]
                exact htokenZero
              have hbody :
                  ExecTransitionBody config contract evmSolm (claimStore I)
                    claimTransition.body .reverted := by
                exact cometRewardsClaimBodyReverts_internal evmSolm I
                  (by simp only [evmSolm, initState]; exact hwv)
                  (by simp only [evmSolm, initState]; exact hhi)
                  (cometRewardsClaimInternalBodyReverts_tokenZero evmSolm I htokenZeroSolm)
              have hreach3298 :=
                cometRewardsClaimX_dec3298_internal (g := Sat256.ofUInt256 g)
                  hwv hsz100 hsize hhi hcanonComet hcanonSrc (Or.inl hzero) hreach
              exact (cometRewardsClaimInternalX_tokenZero_of_reach
                  (g := Sat256.ofUInt256 g) hcanonComet htokenZero hreach3298)
                |>.reEquivExecutionRevert hcode hd hdec hbody
            · let evmSolm : EVM.State :=
                initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
              have htokenNZSolm :
                  rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evmSolm I) ≠ ⟨0⟩ := by
                have hload :
                    getRewardOwedSlot0Load evmSolm I =
                      getRewardOwedRewardConfigSlot0Word σ_solm I := by
                  simp [evmSolm, getRewardOwedSlot0Load, getRewardOwedRewardConfigSlot0Word,
                    initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
                rw [hload, ← hslotWord]
                exact htokenZero
              have hreach3298 :=
                cometRewardsClaimX_dec3298_internal (g := Sat256.ofUInt256 g)
                  hwv hsz100 hsize hhi hcanonComet hcanonSrc (Or.inl hzero) hreach
              by_cases hdepth : I.depth.val < 1024
              · obtain ⟨cA', σ'_evm, σ'_solm, A'_solm, z, baseOut, k', C',
                    hcallBaseSolm, hPostAccounts, rdBasePost, hbaseOutSize, hbaseOutHi⟩ :=
                  cometRewardsClaimInternalX_noAccrue_call_baseTracking_made
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                    (g := Sat256.ofUInt256 g)
                    hcanonComet hcanonSrc hdepth hAccounts htokenZero hzero hreach3298
                let evmBase : EVM.State :=
                  { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σ'_solm
                      substate := A'_solm
                      createdAccounts := cA' }
                cases z
                · have hinner :
                      ExecFuncBody config
                        { contract := contract, locals := claimInternalStore I }
                        evmSolm claimInternalFunction.body .reverted := by
                    exact cometRewardsClaimInternalBodyReverts_noAccrue_getRewardAccrued
                      evmSolm evmBase I htokenNZSolm hzero
                      (by simpa [evmSolm, evmBase] using hcallBaseSolm)
                  have hbody :
                      ExecTransitionBody config contract evmSolm (claimStore I)
                        claimTransition.body .reverted := by
                    exact cometRewardsClaimBodyReverts_internal evmSolm I
                      (by simp only [evmSolm, initState]; exact hwv)
                      (by simp only [evmSolm, initState]; exact hhi)
                      hinner
                  have hrev :
                      RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                    exact cometRewardsClaimInternalX_after_baseTracking_failure
                      (slot0 := getRewardOwedRewardConfigSlot0Word σ_evm I)
                      (multiplier := getRewardOwedMultiplierWord σ_evm I)
                      (claimed := getRewardOwedClaimedWord σ_evm I)
                      rdBasePost hbaseOutSize
                  exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                · by_cases hbaseShort : baseOut.size < 32
                  · have hdecBase :=
                      cometRewardsBaseTrackingAccrued_decode_none_short
                        (out := baseOut) hbaseShort
                    have hinner :
                        ExecFuncBody config
                          { contract := contract, locals := claimInternalStore I }
                          evmSolm claimInternalFunction.body .reverted := by
                      exact
                        cometRewardsClaimInternalBodyReverts_noAccrue_getRewardAccrued_decode
                          evmSolm evmBase I htokenNZSolm hzero
                          (by simpa [evmSolm, evmBase] using hcallBaseSolm)
                          hdecBase
                    have hbody :
                        ExecTransitionBody config contract evmSolm (claimStore I)
                          claimTransition.body .reverted := by
                      exact cometRewardsClaimBodyReverts_internal evmSolm I
                        (by simp only [evmSolm, initState]; exact hwv)
                        (by simp only [evmSolm, initState]; exact hhi)
                        hinner
                    have hrev :
                        RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                      exact cometRewardsClaimInternalX_after_baseTracking_short_revert
                        (slot0 := getRewardOwedRewardConfigSlot0Word σ_evm I)
                        (multiplier := getRewardOwedMultiplierWord σ_evm I)
                        (claimed := getRewardOwedClaimedWord σ_evm I)
                        rdBasePost hbaseShort hbaseOutSize
                    exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                  · have hbase32 : 32 ≤ baseOut.size := Nat.le_of_not_gt hbaseShort
                    by_cases hbaseWord :
                        fromByteArrayBigEndian (baseOut.extract 0 32) < EVM.twoPow 64
                    · let baseAccrued : UInt256 := claimBaseTrackingReturnWord baseOut
                      have hbaseToNat :
                          baseAccrued.toNat =
                            fromByteArrayBigEndian (baseOut.extract 0 32) := by
                        simpa [baseAccrued, claimBaseTrackingReturnWord] using
                          UInt256.toNat_ofNat_of_lt
                            (fromByteArrayBigEndian_extract0_32_lt hbase32)
                      have hbase64 : baseAccrued.toNat < EVM.twoPow 64 := by
                        rw [hbaseToNat]
                        exact hbaseWord
                      have hdecBase :
                          config.externalABI.decode? "baseTrackingAccrued" baseOut =
                            some [.int (Int.ofNat baseAccrued.toNat)] := by
                        rw [hbaseToNat]
                        exact cometRewardsBaseTrackingAccrued_decode_ok
                          (out := baseOut) hbase32 hbaseOutHi hbaseWord
                      let slotE := getRewardOwedRewardConfigSlot0Word σ_evm I
                      let mulE := getRewardOwedMultiplierWord σ_evm I
                      let claimedE := getRewardOwedClaimedWord σ_evm I
                      have hslotLoadSolm :
                          getRewardOwedSlot0Load evmSolm I =
                            getRewardOwedRewardConfigSlot0Word σ_solm I := by
                        simp [evmSolm, getRewardOwedSlot0Load,
                          getRewardOwedRewardConfigSlot0Word, initState,
                          Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
                      have hslotLoadEvm :
                          getRewardOwedSlot0Load evmSolm I = slotE := by
                        rw [hslotLoadSolm, ← hslotWord]
                      have hmulWord :
                          getRewardOwedMultiplierWord σ_evm I =
                            getRewardOwedMultiplierWord σ_solm I := by
                        simpa [getRewardOwedMultiplierWord] using
                          accountMapEquiv_storage_findD hAccounts I.codeOwner
                            (getRewardOwedRewardConfigSlotOf I + (⟨1⟩ : UInt256)) ⟨0⟩
                      have hmulLoadSolm :
                          getRewardOwedMultiplierLoad evmSolm I =
                            getRewardOwedMultiplierWord σ_solm I := by
                        simp [evmSolm, getRewardOwedMultiplierLoad,
                          getRewardOwedMultiplierWord, initState,
                          Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
                      have hmulLoadEvm :
                          getRewardOwedMultiplierLoad evmSolm I = mulE := by
                        rw [hmulLoadSolm, ← hmulWord]
                      have hclaimedWord :
                          getRewardOwedClaimedWord σ_evm I =
                            getRewardOwedClaimedWord σ_solm I :=
                        accountMapEquiv_storage_findD hAccounts I.codeOwner
                          (getRewardOwedRewardsClaimedSlotOf I) ⟨0⟩
                      have hclaimedLoadSolm :
                          getRewardOwedClaimedLoad evmSolm I =
                            getRewardOwedClaimedWord σ_solm I := by
                        simp [evmSolm, getRewardOwedClaimedLoad,
                          getRewardOwedClaimedWord, initState,
                          Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
                      have hclaimedLoadEvm :
                          getRewardOwedClaimedLoad evmSolm I = claimedE := by
                        rw [hclaimedLoadSolm, ← hclaimedWord]
                      obtain ⟨_, _, rd3740⟩ :=
                        cometRewardsClaimInternalX_after_baseTracking_decode_ok
                          (slot0 := slotE) (multiplier := mulE) (claimed := claimedE)
                          rdBasePost hbase32 hbaseOutSize
                          (by simpa [baseAccrued] using hbase64)
                      by_cases hshould :
                          rewardConfigShouldUpscaleRawFromSlot0 slotE ≠ ⟨0⟩
                      · let upNat := getRewardAccruedUpscaledNat slotE baseAccrued
                        let accruedNat := getRewardAccruedReturnNat mulE upNat
                        have hup : upNat < UInt256.size := by
                          simpa [upNat] using
                            getRewardAccruedUpscaledNat_lt_size_of_base64
                              (slot0 := slotE) (accrued := baseAccrued) hbase64
                        by_cases hscaled :
                            getRewardAccruedScaledNat mulE upNat < UInt256.size
                        · have hinnerAccrued :
                              ExecFuncBody config
                                { contract := contract,
                                  locals := getRewardAccruedStore I
                                    (getRewardOwedSlot0Load evmSolm I)
                                    (getRewardOwedMultiplierLoad evmSolm I) }
                                evmSolm getRewardAccruedFunction.body
                                (.returned
                                  (getRewardAccruedAfterAssignedScaledFrame I
                                    (getRewardOwedSlot0Load evmSolm I)
                                    (getRewardOwedMultiplierLoad evmSolm I)
                                    baseAccrued
                                    (getRewardAccruedUpscaledNat
                                      (getRewardOwedSlot0Load evmSolm I) baseAccrued))
                                  evmBase
                                  (some [.int (Int.ofNat accruedNat)])) := by
                            simpa [hslotLoadEvm, hmulLoadEvm, upNat, accruedNat] using
                              getRewardAccruedBodyReturns_upscale
                                evmSolm evmBase I slotE mulE baseAccrued
                                (by simpa [evmSolm, evmBase] using hcallBaseSolm)
                                hdecBase hshould hup hscaled
                          obtain ⟨_, _, rd3432⟩ :=
                            cometRewardsClaimInternalX_getRewardAccrued_upscale_success
                              (slot0 := slotE) (multiplier := mulE) (claimed := claimedE)
                              rd3740 hbase32 hbaseOutSize
                              (by simpa [baseAccrued] using hbase64)
                              hshould hscaled
                          have haccruedNatLt : accruedNat < UInt256.size := by
                            dsimp [accruedNat, getRewardAccruedReturnNat]
                            exact lt_of_le_of_lt (Nat.div_le_self _ _) hscaled
                          by_cases hleClaimed : accruedNat ≤ claimedE.toNat
                          · have hinnerClaim :
                                ExecFuncBody config
                                  { contract := contract, locals := claimInternalStore I }
                                  evmSolm claimInternalFunction.body
                                  (.returned
                                    { contract := contract,
                                      locals :=
                                        claimInternalAfterInternalLocals evmSolm evmSolm I
                                          accruedNat }
                                    evmBase none) := by
                              exact
                                cometRewardsClaimInternalBodyReturns_noAccrue_noTransfer
                                  evmSolm evmBase I htokenNZSolm hzero hinnerAccrued
                                  (by
                                    rw [hclaimedLoadEvm]
                                    exact hleClaimed)
                            have hbody :
                                ExecTransitionBody config contract evmSolm (claimStore I)
                                  claimTransition.body
                                  (.returned
                                    (resumeAfterInternalCall (claimFrame evmSolm I) "_claim" none)
                                    evmBase none) := by
                              exact cometRewardsClaimBodyReturns_internal evmSolm evmBase I
                                (by simp only [evmSolm, initState]; exact hwv)
                                (by simp only [evmSolm, initState]; exact hhi)
                                hinnerClaim
                            have hret :=
                              cometRewardsClaimInternalX_after_getRewardAccrued_no_transfer
                                (slot0 := slotE) (multiplier := mulE)
                                (accrued := UInt256.ofNat accruedNat)
                                (claimed := claimedE)
                                (by simpa [upNat, accruedNat, baseAccrued] using rd3432)
                                (by
                                  rw [UInt256.toNat_ofNat_of_lt haccruedNatLt]
                                  exact hleClaimed)
                                hbaseOutSize
                            exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                              (by simp [evmBase])
                              (by simpa [evmBase] using hPostAccounts)
                              (returnEquiv.fallthrough rfl rfl (by native_decide))
                          · sorry
                        · have hinnerAccrued :
                              ExecFuncBody config
                                { contract := contract,
                                  locals := getRewardAccruedStore I
                                    (getRewardOwedSlot0Load evmSolm I)
                                    (getRewardOwedMultiplierLoad evmSolm I) }
                                evmSolm getRewardAccruedFunction.body .reverted := by
                            exact getRewardAccruedBodyReverts_upscale_scaledOverflow
                              evmSolm evmBase I
                              (getRewardOwedSlot0Load evmSolm I)
                              (getRewardOwedMultiplierLoad evmSolm I)
                              baseAccrued
                              (by simpa [evmSolm, evmBase] using hcallBaseSolm)
                              hdecBase
                              (by simpa [hslotLoadEvm] using hshould)
                              (by simpa [hslotLoadEvm, upNat] using hup)
                              (by
                                rw [hslotLoadEvm, hmulLoadEvm]
                                simpa [upNat] using Nat.le_of_not_gt hscaled)
                          have hinnerClaim :
                              ExecFuncBody config
                                { contract := contract, locals := claimInternalStore I }
                                evmSolm claimInternalFunction.body .reverted := by
                            exact
                              cometRewardsClaimInternalBodyReverts_noAccrue_getRewardAccrued_inner
                                evmSolm I htokenNZSolm hzero hinnerAccrued
                          have hbody :
                              ExecTransitionBody config contract evmSolm (claimStore I)
                                claimTransition.body .reverted := by
                            exact cometRewardsClaimBodyReverts_internal evmSolm I
                              (by simp only [evmSolm, initState]; exact hwv)
                              (by simp only [evmSolm, initState]; exact hhi)
                              hinnerClaim
                          have hrev :
                              RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
                                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                            exact
                              cometRewardsClaimInternalX_getRewardAccrued_upscale_overflow_revert
                                (slot0 := slotE) (multiplier := mulE) (claimed := claimedE)
                                rd3740 hbase32 hbaseOutSize
                                (by simpa [baseAccrued] using hbase64)
                                hshould (Nat.le_of_not_gt hscaled)
                          exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                      · have hshouldZero :
                            rewardConfigShouldUpscaleRawFromSlot0 slotE = ⟨0⟩ := by
                          by_contra hz
                          exact hshould hz
                        by_cases hrescaleZero :
                            rewardConfigRescaleFromSlot0 slotE = ⟨0⟩
                        · have hinnerAccrued :
                              ExecFuncBody config
                                { contract := contract,
                                  locals := getRewardAccruedStore I
                                    (getRewardOwedSlot0Load evmSolm I)
                                    (getRewardOwedMultiplierLoad evmSolm I) }
                                evmSolm getRewardAccruedFunction.body .reverted := by
                            exact getRewardAccruedBodyReverts_downscale_zero
                              evmSolm evmBase I
                              (getRewardOwedSlot0Load evmSolm I)
                              (getRewardOwedMultiplierLoad evmSolm I)
                              baseAccrued
                              (by simpa [evmSolm, evmBase] using hcallBaseSolm)
                              hdecBase
                              (by simpa [hslotLoadEvm] using hshouldZero)
                              (by simpa [hslotLoadEvm] using hrescaleZero)
                          have hinnerClaim :
                              ExecFuncBody config
                                { contract := contract, locals := claimInternalStore I }
                                evmSolm claimInternalFunction.body .reverted := by
                            exact
                              cometRewardsClaimInternalBodyReverts_noAccrue_getRewardAccrued_inner
                                evmSolm I htokenNZSolm hzero hinnerAccrued
                          have hbody :
                              ExecTransitionBody config contract evmSolm (claimStore I)
                                claimTransition.body .reverted := by
                            exact cometRewardsClaimBodyReverts_internal evmSolm I
                              (by simp only [evmSolm, initState]; exact hwv)
                              (by simp only [evmSolm, initState]; exact hhi)
                              hinnerClaim
                          have hrev :
                              RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
                                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                            exact
                              cometRewardsClaimInternalX_getRewardAccrued_downscale_zero_revert
                                (slot0 := slotE) (multiplier := mulE) (claimed := claimedE)
                                rd3740 hbase32 hbaseOutSize
                                (by simpa [baseAccrued] using hbase64)
                                hshouldZero hrescaleZero
                          exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                        · let downNat := getRewardAccruedDownscaledNat slotE baseAccrued
                          let accruedNat := getRewardAccruedReturnNat mulE downNat
                          by_cases hscaled :
                              getRewardAccruedScaledNat mulE downNat < UInt256.size
                          · have hinnerAccrued :
                                ExecFuncBody config
                                  { contract := contract,
                                    locals := getRewardAccruedStore I
                                      (getRewardOwedSlot0Load evmSolm I)
                                      (getRewardOwedMultiplierLoad evmSolm I) }
                                  evmSolm getRewardAccruedFunction.body
                                  (.returned
                                    (getRewardAccruedAfterAssignedScaledFrame I
                                      (getRewardOwedSlot0Load evmSolm I)
                                      (getRewardOwedMultiplierLoad evmSolm I)
                                      baseAccrued
                                      (getRewardAccruedDownscaledNat
                                        (getRewardOwedSlot0Load evmSolm I) baseAccrued))
                                    evmBase
                                    (some [.int (Int.ofNat accruedNat)])) := by
                              simpa [hslotLoadEvm, hmulLoadEvm, downNat, accruedNat] using
                                getRewardAccruedBodyReturns_downscale
                                  evmSolm evmBase I slotE mulE baseAccrued
                                  (by simpa [evmSolm, evmBase] using hcallBaseSolm)
                                  hdecBase hshouldZero hrescaleZero hscaled
                            obtain ⟨_, _, rd3432⟩ :=
                              cometRewardsClaimInternalX_getRewardAccrued_downscale_success
                                (slot0 := slotE) (multiplier := mulE) (claimed := claimedE)
                                rd3740 hbase32 hbaseOutSize
                                (by simpa [baseAccrued] using hbase64)
                                hshouldZero hrescaleZero hscaled
                            have haccruedNatLt : accruedNat < UInt256.size := by
                              dsimp [accruedNat, getRewardAccruedReturnNat]
                              exact lt_of_le_of_lt (Nat.div_le_self _ _) hscaled
                            by_cases hleClaimed : accruedNat ≤ claimedE.toNat
                            · have hinnerClaim :
                                  ExecFuncBody config
                                    { contract := contract, locals := claimInternalStore I }
                                    evmSolm claimInternalFunction.body
                                    (.returned
                                      { contract := contract,
                                        locals :=
                                          claimInternalAfterInternalLocals evmSolm evmSolm I
                                            accruedNat }
                                      evmBase none) := by
                                exact
                                  cometRewardsClaimInternalBodyReturns_noAccrue_noTransfer
                                    evmSolm evmBase I htokenNZSolm hzero hinnerAccrued
                                    (by
                                      rw [hclaimedLoadEvm]
                                      exact hleClaimed)
                              have hbody :
                                  ExecTransitionBody config contract evmSolm (claimStore I)
                                    claimTransition.body
                                    (.returned
                                      (resumeAfterInternalCall
                                        (claimFrame evmSolm I) "_claim" none)
                                      evmBase none) := by
                                exact cometRewardsClaimBodyReturns_internal evmSolm evmBase I
                                  (by simp only [evmSolm, initState]; exact hwv)
                                  (by simp only [evmSolm, initState]; exact hhi)
                                  hinnerClaim
                              have hret :=
                                cometRewardsClaimInternalX_after_getRewardAccrued_no_transfer
                                  (slot0 := slotE) (multiplier := mulE)
                                  (accrued := UInt256.ofNat accruedNat)
                                  (claimed := claimedE)
                                  (by simpa [downNat, accruedNat, baseAccrued] using rd3432)
                                  (by
                                    rw [UInt256.toNat_ofNat_of_lt haccruedNatLt]
                                    exact hleClaimed)
                                  hbaseOutSize
                              exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                                (by simp [evmBase])
                                (by simpa [evmBase] using hPostAccounts)
                                (returnEquiv.fallthrough rfl rfl (by native_decide))
                            · sorry
                          · have hinnerAccrued :
                                ExecFuncBody config
                                  { contract := contract,
                                    locals := getRewardAccruedStore I
                                      (getRewardOwedSlot0Load evmSolm I)
                                      (getRewardOwedMultiplierLoad evmSolm I) }
                                  evmSolm getRewardAccruedFunction.body .reverted := by
                              exact getRewardAccruedBodyReverts_downscale_scaledOverflow
                                evmSolm evmBase I
                                (getRewardOwedSlot0Load evmSolm I)
                                (getRewardOwedMultiplierLoad evmSolm I)
                                baseAccrued
                                (by simpa [evmSolm, evmBase] using hcallBaseSolm)
                                hdecBase
                                (by simpa [hslotLoadEvm] using hshouldZero)
                                (by simpa [hslotLoadEvm] using hrescaleZero)
                                (by
                                  rw [hslotLoadEvm, hmulLoadEvm]
                                  simpa [downNat] using Nat.le_of_not_gt hscaled)
                            have hinnerClaim :
                                ExecFuncBody config
                                  { contract := contract, locals := claimInternalStore I }
                                  evmSolm claimInternalFunction.body .reverted := by
                              exact
                                cometRewardsClaimInternalBodyReverts_noAccrue_getRewardAccrued_inner
                                  evmSolm I htokenNZSolm hzero hinnerAccrued
                            have hbody :
                                ExecTransitionBody config contract evmSolm (claimStore I)
                                  claimTransition.body .reverted := by
                              exact cometRewardsClaimBodyReverts_internal evmSolm I
                                (by simp only [evmSolm, initState]; exact hwv)
                                (by simp only [evmSolm, initState]; exact hhi)
                                hinnerClaim
                            have hrev :
                                RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                              exact
                                cometRewardsClaimInternalX_getRewardAccrued_downscale_overflow_revert
                                  (slot0 := slotE) (multiplier := mulE) (claimed := claimedE)
                                  rd3740 hbase32 hbaseOutSize
                                  (by simpa [baseAccrued] using hbase64)
                                  hshouldZero hrescaleZero (Nat.le_of_not_gt hscaled)
                            exact hrev.reEquivExecutionRevert hcode hd hdec hbody
                    · have hdecBase :=
                        cometRewardsBaseTrackingAccrued_decode_none_noncanon
                          (out := baseOut) hbase32 hbaseOutHi hbaseWord
                      have hinner :
                          ExecFuncBody config
                            { contract := contract, locals := claimInternalStore I }
                            evmSolm claimInternalFunction.body .reverted := by
                        exact
                          cometRewardsClaimInternalBodyReverts_noAccrue_getRewardAccrued_decode
                            evmSolm evmBase I htokenNZSolm hzero
                            (by simpa [evmSolm, evmBase] using hcallBaseSolm)
                            hdecBase
                      have hbody :
                          ExecTransitionBody config contract evmSolm (claimStore I)
                            claimTransition.body .reverted := by
                        exact cometRewardsClaimBodyReverts_internal evmSolm I
                          (by simp only [evmSolm, initState]; exact hwv)
                          (by simp only [evmSolm, initState]; exact hhi)
                          hinner
                      have hreturnToNat :
                          (claimBaseTrackingReturnWord baseOut).toNat =
                            fromByteArrayBigEndian (baseOut.extract 0 32) := by
                        simpa [claimBaseTrackingReturnWord] using
                          UInt256.toNat_ofNat_of_lt
                            (fromByteArrayBigEndian_extract0_32_lt hbase32)
                      have hbaseNo :
                          ¬ (claimBaseTrackingReturnWord baseOut).toNat < EVM.twoPow 64 := by
                        intro hlt
                        exact hbaseWord (by rw [← hreturnToNat]; exact hlt)
                      have hrev :
                          RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
                        exact cometRewardsClaimInternalX_after_baseTracking_noncanon_revert
                          (slot0 := getRewardOwedRewardConfigSlot0Word σ_evm I)
                          (multiplier := getRewardOwedMultiplierWord σ_evm I)
                          (claimed := getRewardOwedClaimedWord σ_evm I)
                          rdBasePost hbase32 hbaseOutSize hbaseNo
                      exact hrev.reEquivExecutionRevert hcode hd hdec hbody
              · have hdepth1024 : I.depth = 1024 :=
                  Fin.ext (by
                    have hlt := I.depth.isLt
                    have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hdepth
                    omega)
                let evmFail : EVM.State :=
                  { evmSolm with
                      substate :=
                        (evmSolm.addAccessedAccount
                          (EVM.address (getRewardOwedCometTarget I))).substate }
                have hcallS :
                    typedCallViaEVM config evmSolm
                      (EVM.address (getRewardOwedCometTarget I)) "baseTrackingAccrued" 0
                      (getRewardAccruedBaseTrackingArgs I)
                      (false, evmFail, ByteArray.empty) false := by
                  exact callNotMade_depthLimit
                    (cfg := config) (evm := evmSolm)
                    (tgt := EVM.address (getRewardOwedCometTarget I))
                    (name := "baseTrackingAccrued")
                    (args := getRewardAccruedBaseTrackingArgs I)
                    (calldata :=
                      (claimBaseTrackingCalldataMem I
                        (getRewardOwedRewardConfigSlot0Word σ_solm I)
                        (getRewardOwedMultiplierWord σ_solm I)).readWithPadding
                          256 claimBaseTrackingCallSize.toNat)
                    (callPerm := false)
                    (claimBaseTrackingCalldataMem_encode_args I
                      (getRewardOwedRewardConfigSlot0Word σ_solm I)
                      (getRewardOwedMultiplierWord σ_solm I) hcanonSrc)
                    (by simpa [evmSolm, initState] using hdepth1024)
                have hinner :
                    ExecFuncBody config
                      { contract := contract, locals := claimInternalStore I }
                      evmSolm claimInternalFunction.body .reverted := by
                  exact cometRewardsClaimInternalBodyReverts_noAccrue_getRewardAccrued
                    evmSolm evmFail I htokenNZSolm hzero hcallS
                have hbody :
                    ExecTransitionBody config contract evmSolm (claimStore I)
                      claimTransition.body .reverted := by
                  exact cometRewardsClaimBodyReverts_internal evmSolm I
                    (by simp only [evmSolm, initState]; exact hwv)
                    (by simp only [evmSolm, initState]; exact hhi)
                    hinner
                exact (cometRewardsClaimInternalX_noAccrue_callDepthLimit
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := Sat256.ofUInt256 g)
                    hcanonComet hcanonSrc htokenZero hzero hreach3298 hdepth1024)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
          · by_cases hone : claimShouldAccrueWord I = ⟨1⟩
            · have hdec := cometRewardsDecode_claim_ok
                (I := I) hsz100 hhi hcanonComet hcanonSrc (Or.inr hone)
              have hslotWord :
                  getRewardOwedRewardConfigSlot0Word σ_evm I =
                    getRewardOwedRewardConfigSlot0Word σ_solm I :=
                accountMapEquiv_storage_findD hAccounts I.codeOwner
                  (getRewardOwedRewardConfigSlotOf I) ⟨0⟩
              by_cases htokenZero :
                  rewardConfigTokenFromSlot0
                    (getRewardOwedRewardConfigSlot0Word σ_evm I) = ⟨0⟩
              · let evmSolm : EVM.State :=
                  initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                have htokenZeroSolm :
                    rewardConfigTokenFromSlot0 (getRewardOwedSlot0Load evmSolm I) = ⟨0⟩ := by
                  have hload :
                      getRewardOwedSlot0Load evmSolm I =
                        getRewardOwedRewardConfigSlot0Word σ_solm I := by
                    simp [evmSolm, getRewardOwedSlot0Load, getRewardOwedRewardConfigSlot0Word,
                      initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
                  rw [hload, ← hslotWord]
                  exact htokenZero
                have hbody :
                    ExecTransitionBody config contract evmSolm (claimStore I)
                      claimTransition.body .reverted := by
                  exact cometRewardsClaimBodyReverts_internal evmSolm I
                    (by simp only [evmSolm, initState]; exact hwv)
                    (by simp only [evmSolm, initState]; exact hhi)
                    (cometRewardsClaimInternalBodyReverts_tokenZero evmSolm I htokenZeroSolm)
                have hreach3298 :=
                  cometRewardsClaimX_dec3298_internal (g := Sat256.ofUInt256 g)
                    hwv hsz100 hsize hhi hcanonComet hcanonSrc (Or.inr hone) hreach
                exact (cometRewardsClaimInternalX_tokenZero_of_reach
                    (g := Sat256.ofUInt256 g) hcanonComet htokenZero hreach3298)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
              · sorry
            · have hdec := cometRewardsDecode_claim_none_noncanon_bool
                (I := I) hsz100 hhi hcanonComet hcanonSrc hzero hone
              exact (cometRewardsClaimX_noncanon_bool (g := Sat256.ofUInt256 g)
                  hwv hsz100 hsize hhi hcanonComet hcanonSrc hzero hone hreach)
                |>.reEquivDecodingFailed hcode hd hdec
        · have hdec := cometRewardsDecode_claim_none_noncanon_src
            (I := I) hsz100 hhi hcanonComet hcanonSrc
          have hnc : UInt256.eq (claimSrcWord I)
              (UInt256.land (claimSrcWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne
              (fun he => hcanonSrc (solcAddrCanonical_of_clean he))
          exact (cometRewardsClaimX_noncanon_src (g := Sat256.ofUInt256 g)
              hwv hsz100 hsize hhi hcanonComet hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := cometRewardsDecode_claim_none_noncanon_comet
          (I := I) hsz100 hhi hcanonComet
        have hnc : UInt256.eq (claimCometWord I)
            (UInt256.land (claimCometWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne
            (fun he => hcanonComet (solcAddrCanonical_of_clean he))
        exact (cometRewardsClaimX_noncanon_comet (g := Sat256.ofUInt256 g)
            hwv hsz100 hsize hhi hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := cometRewardsDecode_claim_none_huge (I := I) hbig
      exact (cometRewardsClaimX_hugearg (g := Sat256.ofUInt256 g)
          hwv hsize hbig hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 100 := by omega
    have hdec := cometRewardsDecode_claim_none_short (I := I) hsz4 hshort
    exact (cometRewardsClaimX_shortarg (g := Sat256.ofUInt256 g)
        hwv hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.CompoundIII.CometRewards
