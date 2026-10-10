import Benchmarks.UniswapV4PoolManager.AccountDeltaSource
import Benchmarks.UniswapV4PoolManager.DeltaCountTrace
import Benchmarks.UniswapV4PoolManager.Signed128
import Benchmarks.UniswapV4PoolManager.SignedAddTrace
import Benchmarks.UniswapV4PoolManager.ReachCost

/-! Bytecode refinement of the shared currency accounting routine. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

def currencyDeltaMemory (target currency : AccountAddress) (mem : ByteArray) : ByteArray :=
  twoWordHashMem (accountWord target) (accountWord currency) mem

theorem currencyDeltaValue_signed (evm : EVM.State) (target currency : AccountAddress) :
    currencyDeltaValue evm target currency = EVM.signed (transientWord evm (currencyDeltaSlot target currency)) :=
  (signed_eq_normalize _).symm

theorem applyDeltaPost_accountMap {evm : EVM.State} {I : ExecutionEnv} {delta : Int}
    (hI : evm.executionEnv = I) (hd : int256Fits delta) (target currency : AccountAddress) :
    (applyDeltaPost evm target currency delta).accountMap =
      tstoreAccountMap I.codeOwner evm.accountMap (currencyDeltaSlot target currency)
        (transientWord evm (currencyDeltaSlot target currency) + EVM.wordOfInt delta) := by
  rw [applyDeltaPost, transientStore_accountMap, hI, currencyDeltaValue_signed,
    ← signed_wordOfInt hd, wordOfInt_signed_add, wordOfInt_signed]

theorem accountDeltaStaticTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {value slot : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 3 ≤ 1024) (hperm : I.perm = false)
    (h : RD (deployedRuntime v) I g s0 ⟨12594⟩ (value :: slot :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  have r1 := h.jumpdest
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨12594⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨12595⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨12596⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact tstoreStatic r3 hperm
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨12597⟩ : UInt256), UInt8.ofNat 93, .TSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

theorem accountDeltaPrepareCostTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw deltaWord ret currencyWord : UInt256} {target currency : AccountAddress}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 9 ≤ 1024) (hI : evm.executionEnv = I)
    (hcurrency : UInt256.land currencyWord solcAddrMask = accountWord currency)
    (hcanonical : UInt256.signextend ⟨15⟩ deltaWord = deltaWord) (hnz : deltaWord ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨12528⟩
      (currencyWord :: deltaWord :: accountWord target :: ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', C+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ⟨15145⟩
      (transientWord evm (currencyDeltaSlot target currency) :: deltaWord :: ⟨12594⟩ ::
       currencyDeltaSlot target currency :: transientWord evm (currencyDeltaSlot target currency) :: ret :: R)
      (currencyDeltaMemory target currency mem) aw' rdata evm.accountMap k' C' := by
  have hguard := poolManagerBlocks.poolManager_block_12528_fallthrough
    (by simp only [List.length_cons]; omega)
    (by change UInt256.isZero (UInt256.signextend ⟨15⟩ deltaWord) = ⟨0⟩
        rw [hcanonical]; exact isZero_eq_zero_of_ne hnz) h
  change RD (deployedRuntime v) I g s0 ⟨12541⟩
    (currencyWord :: accountWord target :: UInt256.signextend ⟨15⟩ deltaWord :: ret :: R)
    mem aw rdata evm.accountMap _ _ at hguard
  rw [hcanonical] at hguard
  have hjSlot : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12582) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  let aw' := M (M (M aw ⟨0⟩ ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64)
  have hslot := poolManagerBlocks.poolManager_block_12541
    (by simp only [List.length_cons]; omega) hjSlot hguard
  have hm : poolManagerBlocks.poolManager_block_12541_memory
      (mem := mem) (x0 := currencyWord) (x1 := accountWord target) =
      currencyDeltaMemory target currency mem := by
    change twoWordHashMem (UInt256.land (accountWord target) solcAddrMask)
      (UInt256.land currencyWord solcAddrMask) mem = _
    rw [solcAddrMask_clean (accountWord_canonical target), hcurrency]
    rfl
  change RD (deployedRuntime v) I g s0 ⟨12582⟩
    (keccakWord ⟨0⟩ ⟨64⟩ (poolManagerBlocks.poolManager_block_12541_memory
      (mem := mem) (x0 := currencyWord) (x1 := accountWord target)) :: deltaWord :: ret :: R)
    (poolManagerBlocks.poolManager_block_12541_memory
      (mem := mem) (x0 := currencyWord) (x1 := accountWord target)) aw' rdata evm.accountMap _ _ at hslot
  rw [hm] at hslot
  have hhash : keccakWord ⟨0⟩ ⟨64⟩ (currencyDeltaMemory target currency mem) = currencyDeltaSlot target currency :=
    mappingMemory_slot_any _ _ _
  rw [hhash] at hslot
  have hjAdd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 15145) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have hadd := poolManagerBlocks.poolManager_block_12582
    (by simp only [List.length_cons]; omega) hjAdd hslot
  change RD (deployedRuntime v) I g s0 ⟨15145⟩
    (codeOwnerTransientWord I evm.accountMap (currencyDeltaSlot target currency) :: deltaWord :: ⟨12594⟩ ::
      currencyDeltaSlot target currency :: codeOwnerTransientWord I evm.accountMap (currencyDeltaSlot target currency) :: ret :: R)
    (currencyDeltaMemory target currency mem) aw' rdata evm.accountMap _ _ at hadd
  rw [← transientWord_accountMap hI] at hadd
  refine ⟨_, _, _, ?_, hadd⟩
  dsimp only [aw', memExpansionCost]
  omega

theorem accountDeltaPrepareTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw deltaWord ret currencyWord : UInt256} {target currency : AccountAddress}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 9 ≤ 1024) (hI : evm.executionEnv = I)
    (hcurrency : UInt256.land currencyWord solcAddrMask = accountWord currency)
    (hcanonical : UInt256.signextend ⟨15⟩ deltaWord = deltaWord) (hnz : deltaWord ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨12528⟩
      (currencyWord :: deltaWord :: accountWord target :: ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨15145⟩
      (transientWord evm (currencyDeltaSlot target currency) :: deltaWord :: ⟨12594⟩ ::
       currencyDeltaSlot target currency :: transientWord evm (currencyDeltaSlot target currency) :: ret :: R)
      (currencyDeltaMemory target currency mem) aw' rdata evm.accountMap k' C' := by
  obtain ⟨aw1, k1, C1, _, hr⟩ := accountDeltaPrepareCostTrace v hstack hI hcurrency hcanonical hnz h
  exact ⟨aw1, k1, C1, hr⟩

def accountDeltaTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (evm : EVM.State) (target currency : AccountAddress) (delta : Int) (ret : UInt256)
    (R : List UInt256) (mem rdata : ByteArray) : Prop :=
  if delta = 0 then
    ∃ aw k C, RD (deployedRuntime v) I g s0 ret R mem aw rdata evm.accountMap k C
  else if int256Fits (currencyDeltaValue evm target currency + delta) then
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else
    ∃ aw k C, RD (deployedRuntime v) I g s0 ret R (currencyDeltaMemory target currency mem) aw rdata
      (accountDeltaPost evm target currency delta).accountMap k C
  else RDrev (deployedRuntime v) g s0

def accountDeltaCostTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (evm : EVM.State) (target currency : AccountAddress) (delta : Int) (ret : UInt256)
    (R : List UInt256) (mem rdata : ByteArray) (aw₀ : UInt256) (C₀ : Nat) : Prop :=
  if delta = 0 then
    ∃ aw k C, C₀+Cₘ aw ≤ C+Cₘ aw₀ ∧ RD (deployedRuntime v) I g s0 ret R mem aw rdata evm.accountMap k C
  else if int256Fits (currencyDeltaValue evm target currency + delta) then
    if I.perm = false then RDstatic (deployedRuntime v) g s0 else
    ∃ aw k C, C₀+Cₘ aw ≤ C+Cₘ aw₀ ∧ RD (deployedRuntime v) I g s0 ret R (currencyDeltaMemory target currency mem) aw rdata
      (accountDeltaPost evm target currency delta).accountMap k C
  else RDrev (deployedRuntime v) g s0

theorem accountDeltaWordCostTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw ret currencyWord : UInt256} {target currency : AccountAddress} {delta : Int}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 9 ≤ 1024) (hI : evm.executionEnv = I)
    (hcurrency : UInt256.land currencyWord solcAddrMask = accountWord currency)
    (hlo : -(2^127 : Int) ≤ delta) (hhi : delta < 2^127)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12528⟩
      (currencyWord :: EVM.wordOfInt delta :: accountWord target :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    accountDeltaCostTraceResult v I g s0 evm target currency delta ret R mem rdata aw C := by
  classical
  have hd : int256Fits delta := by constructor <;> omega
  have hcanonical := signextend128_wordOfInt hlo hhi
  generalize hdword : EVM.wordOfInt delta = deltaWord at h hcanonical
  rw [accountDeltaCostTraceResult]
  by_cases hz : delta = 0
  · rw [if_pos hz]
    have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12787) = true := by
      rw [deployedRuntime_jumps]; jump_dest
    have hzero := poolManagerBlocks.poolManager_block_12528_taken
      (by simp only [List.length_cons]; omega)
      (by change UInt256.isZero (UInt256.signextend ⟨15⟩ deltaWord) ≠ ⟨0⟩
          rw [hcanonical, ← hdword, hz]; decide) hj h
    have hdone := poolManagerBlocks.poolManager_block_12787
      (by change R.length + 4 ≤ 1024; omega) hret hzero
    exact ⟨_, _, _, by omega, hdone⟩
  · rw [if_neg hz]
    have hnz : deltaWord ≠ (⟨0⟩ : UInt256) := by
      rw [← hdword]; exact (wordOfInt_eq_zero_iff hd).not.mpr hz
    have hprep := accountDeltaPrepareCostTrace
      (I := I) (g := g) (s0 := s0) (mem := mem) (rdata := rdata) (aw := aw) (k := k) (C := C) (R := R)
      (target := target) (currency := currency) (deltaWord := deltaWord) (ret := ret)
      (evm := evm) v hstack hI hcurrency hcanonical hnz h
    have hsum : EVM.signed (transientWord evm (currencyDeltaSlot target currency)) +
        EVM.signed deltaWord = currencyDeltaValue evm target currency + delta := by
      rw [← currencyDeltaValue_signed, ← hdword, signed_wordOfInt hd]
    generalize hnext : currencyDeltaValue evm target currency + delta = nextValue at ⊢
    by_cases hfitValue : int256Fits nextValue
    · rw [if_pos hfitValue]
      have hfit : int256Fits (currencyDeltaValue evm target currency + delta) := by
        rw [hnext]; exact hfitValue
      obtain ⟨aw', k', C', hprepCost, hadd⟩ := hprep
      have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12594) = true := by
        rw [deployedRuntime_jumps]; jump_dest
      obtain ⟨k'', C'', hsumCost, hstore⟩ := RD_retainCost (fun budget start hr =>
        checkedSignedAddPass v (by simp only [List.length_cons]; omega)
          (by rw [hsum]; exact hfit) hj hr) hadd
      by_cases hp : I.perm = false
      · rw [if_pos hp]
        exact accountDeltaStaticTrace v (by simp only [List.length_cons]; omega) hp hstore
      · rw [if_neg hp]
        have hp' : I.perm = true := Bool.eq_true_of_not_eq_false hp
        let previous := transientWord evm (currencyDeltaSlot target currency)
        let next := currencyDeltaValue evm target currency + delta
        let evm1 := applyDeltaPost evm target currency delta
        have hI1 : evm1.executionEnv = I := (transientStore_executionEnv _ _ _ _).trans hI
        have hmap := applyDeltaPost_accountMap hI hd target currency
        rw [hdword] at hmap
        have hword : previous + deltaWord = EVM.wordOfInt next := by
          rw [← wordOfInt_signed_add, hsum]
        by_cases hn : next = 0
        · have hzero : previous + deltaWord = (⟨0⟩ : UInt256) := by rw [hword, hn]; rfl
          have hstored := poolManagerBlocks.poolManager_block_12594_fallthrough
            (by simp only [List.length_cons]; omega) hp' hzero hstore
          change RD (deployedRuntime v) I g s0 ⟨12602⟩ (previous :: ret :: R)
            (currencyDeltaMemory target currency mem) aw' rdata
            (tstoreAccountMap I.codeOwner evm.accountMap (currencyDeltaSlot target currency)
              (previous + deltaWord)) _ _ at hstored
          rw [← hmap] at hstored
          obtain ⟨kf, Cf, hcountCost, hdone⟩ := RD_retainCost (fun budget start hr =>
            decrementDeltaCountTrace v (by omega) hI1 hp' hret hr) hstored
          rw [accountDeltaPost, if_neg hz, if_pos hn]
          exact ⟨_, _, _, by omega, hdone⟩
        · have hnword : previous + deltaWord ≠ (⟨0⟩ : UInt256) := by
            rw [hword]; exact fun he => hn ((wordOfInt_eq_zero_iff hfit).mp he)
          have hjPrev : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12707) = true := by
            rw [deployedRuntime_jumps]; jump_dest
          have hstored := poolManagerBlocks.poolManager_block_12594_taken
            (by simp only [List.length_cons]; omega) hp' hnword hjPrev hstore
          change RD (deployedRuntime v) I g s0 ⟨12707⟩ (previous :: ret :: R)
            (currencyDeltaMemory target currency mem) aw' rdata
            (tstoreAccountMap I.codeOwner evm.accountMap (currencyDeltaSlot target currency)
              (previous + deltaWord)) _ _ at hstored
          rw [← hmap] at hstored
          rw [accountDeltaPost, if_neg hz, if_neg hn]
          by_cases hpv : currencyDeltaValue evm target currency = 0
          · rw [if_pos hpv]
            have hpw : previous = (⟨0⟩ : UInt256) := (signed_eq_zero_iff previous).mp
              ((currencyDeltaValue_signed evm target currency).symm.trans hpv)
            have hjInc : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12714) = true := by
              rw [deployedRuntime_jumps]; jump_dest
            have hinc := poolManagerBlocks.poolManager_block_12707_taken
              (by simp only [List.length_cons]; omega) (by rw [hpw]; decide) hjInc hstored
            obtain ⟨kf, Cf, hcountCost, hdone⟩ := RD_retainCost (fun budget start hr =>
              incrementDeltaCountTrace v (by omega) hI1 hp' hret hr) hinc
            exact ⟨_, _, _, by omega, hdone⟩
          · rw [if_neg hpv]
            have hpw : previous ≠ (⟨0⟩ : UInt256) := fun he => hpv
              ((currencyDeltaValue_signed evm target currency).trans ((signed_eq_zero_iff previous).mpr he))
            have hskip := poolManagerBlocks.poolManager_block_12707_fallthrough
              (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hpw) hstored
            have hdone := poolManagerBlocks.poolManager_block_12713
              (by change R.length + 1 ≤ 1024; omega) hret hskip
            exact ⟨_, _, _, by omega, hdone⟩
    · rw [if_neg hfitValue]
      have hfit : ¬int256Fits (currencyDeltaValue evm target currency + delta) := by
        rw [hnext]; exact hfitValue
      obtain ⟨aw', k', C', hprepCost, hadd⟩ := hprep
      exact checkedSignedAddReverts v (by simp only [List.length_cons]; omega)
        (by rw [hsum]; exact hfit) hadd

theorem accountDeltaWordTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw ret currencyWord : UInt256} {target currency : AccountAddress} {delta : Int}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 9 ≤ 1024) (hI : evm.executionEnv = I)
    (hcurrency : UInt256.land currencyWord solcAddrMask = accountWord currency)
    (hlo : -(2^127 : Int) ≤ delta) (hhi : delta < 2^127)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12528⟩
      (currencyWord :: EVM.wordOfInt delta :: accountWord target :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    accountDeltaTraceResult v I g s0 evm target currency delta ret R mem rdata := by
  have hr := accountDeltaWordCostTrace v hstack hI hcurrency hlo hhi hret h
  unfold accountDeltaTraceResult
  unfold accountDeltaCostTraceResult at hr
  by_cases hz : delta = 0
  · rw [if_pos hz] at hr ⊢
    obtain ⟨aw1, k1, C1, _, rd⟩ := hr
    exact ⟨aw1, k1, C1, rd⟩
  rw [if_neg hz] at hr ⊢
  generalize hnext : currencyDeltaValue evm target currency + delta = next at hr ⊢
  by_cases hfit : int256Fits next
  · rw [if_pos hfit] at hr ⊢
    by_cases hp : I.perm = false
    · rw [if_pos hp] at hr ⊢
      exact hr
    · rw [if_neg hp] at hr ⊢
      obtain ⟨aw1, k1, C1, _, rd⟩ := hr
      exact ⟨aw1, k1, C1, rd⟩
  · rw [if_neg hfit] at hr ⊢
    exact hr


-- Canonical address specialization used by the public mint, burn, and clear entries.
theorem accountDeltaTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw ret : UInt256} {target currency : AccountAddress} {delta : Int}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 9 ≤ 1024) (hI : evm.executionEnv = I)
    (hlo : -(2^127 : Int) ≤ delta) (hhi : delta < 2^127)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12528⟩
      (accountWord currency :: EVM.wordOfInt delta :: accountWord target :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    accountDeltaTraceResult v I g s0 evm target currency delta ret R mem rdata :=
  accountDeltaWordTrace v hstack hI (solcAddrMask_clean (accountWord_canonical currency)) hlo hhi hret h

end Benchmarks.UniswapV4PoolManager
