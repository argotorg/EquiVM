import Benchmarks.UniswapV4PoolManager.BurnAuthorization
import Benchmarks.UniswapV4PoolManager.BalanceBurnTrace
import Benchmarks.UniswapV4PoolManager.TransferFromTrace

/-! Caller, operator, and allowance bytecode in the ERC6909 burn path. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def burnFromStack (sender id amount : UInt256) (R : List UInt256) : List UInt256 :=
  sender :: solcAddrMask :: ⟨1005⟩ :: transferEventTopic :: amount :: ⟨0⟩ :: id :: R

theorem burnOperatorTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {sender id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 10 ≤ 1024) (hmem : mem.size = 96)
    (hc : sender.toNat < EVM.addressModulus) (hne : accountWord I.source ≠ sender)
    (h : RD (deployedRuntime v) I g s0 ⟨955⟩ (burnFromStack sender id amount R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨967⟩
      (UInt256.isZero (UInt256.land (solcSlotWordAt (operatorSlot sender (accountWord I.source)) σ I) ⟨255⟩) ::
        balanceBurnStack sender id amount R) (transferFromOperatorMemory I sender mem) aw' rdata σ k' C' := by
  have heq : UInt256.eq sender (accountWord I.source) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hne (uInt256_eq_one_eq he).symm)
  have hcond : UInt256.isZero (UInt256.eq (UInt256.land sender solcAddrMask) (accountWord I.source)) ≠ ⟨0⟩ := by
    rw [solcAddrMask_clean hc, heq]; decide
  have hjOperator : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 1184) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have hoperator := poolManagerBlocks.poolManager_block_955_taken
    (by change R.length + 2 + 7 ≤ 1024; omega) hcond hjOperator h
  change RD (deployedRuntime v) I g s0 ⟨1184⟩
    (UInt256.isZero (UInt256.eq (UInt256.land sender solcAddrMask) (accountWord I.source)) ::
      balanceBurnStack (UInt256.land sender solcAddrMask) id amount R) mem aw rdata σ _ _ at hoperator
  rw [solcAddrMask_clean hc] at hoperator
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 967) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  obtain ⟨k', C', hnext⟩ := poolManagerBlocks.poolManager_block_1184
    (by change R.length + 1 + 8 ≤ 1024; omega) hj hoperator
  let masked := UInt256.land (accountWord I.source) solcAddrMask
  let nextMem := nestedMappingMemory sender masked ⟨3⟩ mem
  change RD (deployedRuntime v) I g s0 ⟨967⟩
    (UInt256.isZero (UInt256.land (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ nextMem) σ I) ⟨255⟩) ::
      balanceBurnStack sender id amount R) nextMem _ rdata σ k' C' at hnext
  have hm : masked = accountWord I.source := solcAddrMask_clean (accountWord_canonical _)
  dsimp only [nextMem] at hnext
  rw [hm, nestedMappingMemory_slot _ _ _ hmem] at hnext
  exact ⟨_, _, _, hnext⟩

theorem burnSkipAllowanceTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {sender id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 10 ≤ 1024) (hmem : mem.size = 96)
    (hc : sender.toNat < EVM.addressModulus)
    (hskip : ¬(accountWord I.source ≠ sender ∧
      UInt256.land (solcSlotWordAt (operatorSlot sender (accountWord I.source)) σ I) ⟨255⟩ = ⟨0⟩))
    (h : RD (deployedRuntime v) I g s0 ⟨955⟩ (burnFromStack sender id amount R) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', mem'.size = 96 ∧ RD (deployedRuntime v) I g s0 ⟨972⟩
      (balanceBurnStack sender id amount R) mem' aw' rdata σ k' C' := by
  by_cases heq : accountWord I.source = sender
  · have hcond : UInt256.isZero (UInt256.eq (UInt256.land sender solcAddrMask) (accountWord I.source)) = ⟨0⟩ := by
      rw [solcAddrMask_clean hc, heq, uInt256_eq_self]; decide
    have h967 := poolManagerBlocks.poolManager_block_955_fallthrough
      (by change R.length + 2 + 7 ≤ 1024; omega) hcond h
    change RD (deployedRuntime v) I g s0 ⟨967⟩
      (UInt256.isZero (UInt256.eq (UInt256.land sender solcAddrMask) (accountWord I.source)) ::
        balanceBurnStack (UInt256.land sender solcAddrMask) id amount R) mem aw rdata σ _ _ at h967
    rw [hcond, solcAddrMask_clean hc] at h967
    have h972 := poolManagerBlocks.poolManager_block_967_fallthrough
      (by change R.length + 6 + 2 ≤ 1024; omega) rfl h967
    exact ⟨mem, _, _, _, hmem, h972⟩
  · have hop : UInt256.land (solcSlotWordAt (operatorSlot sender (accountWord I.source)) σ I) ⟨255⟩ ≠ ⟨0⟩ :=
      fun hz => hskip ⟨heq, hz⟩
    obtain ⟨aw', k', C', h967⟩ := burnOperatorTrace v hstack hmem hc heq h
    have h972 := poolManagerBlocks.poolManager_block_967_fallthrough
      (by change R.length + 6 + 2 ≤ 1024; omega) (isZero_eq_zero_of_ne hop) h967
    exact ⟨_, _, _, _, nestedMappingMemory_size _ _ _ hmem, h972⟩

theorem burnNeedAllowanceTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {sender id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 10 ≤ 1024) (hmem : mem.size = 96)
    (hc : sender.toNat < EVM.addressModulus)
    (hneed : accountWord I.source ≠ sender ∧
      UInt256.land (solcSlotWordAt (operatorSlot sender (accountWord I.source)) σ I) ⟨255⟩ = ⟨0⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨955⟩ (burnFromStack sender id amount R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨1010⟩ (balanceBurnStack sender id amount R)
      (transferFromOperatorMemory I sender mem) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', h967⟩ := burnOperatorTrace v hstack hmem hc hneed.1 h
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 1010) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have h1010 := poolManagerBlocks.poolManager_block_967_taken
    (by change R.length + 6 + 2 ≤ 1024; omega) (by rw [hneed.2]; decide) hj h967
  exact ⟨_, _, _, h1010⟩

theorem burnAllowanceReadTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {sender id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 10 ≤ 1024) (hmem : mem.size = 96)
    (h : RD (deployedRuntime v) I g s0 ⟨1010⟩ (balanceBurnStack sender id amount R) mem aw rdata σ k C) :
    let allowed := solcSlotWordAt (allowanceSlot sender (accountWord I.source) id) σ I
    ∃ aw' k' C', RD (deployedRuntime v) I g s0
      (if allowed = maxAllowanceWord then ⟨1106⟩ else ⟨1113⟩)
      (amount :: allowed :: balanceBurnStack sender id amount R)
      (transferFromAllowanceMemory I sender id mem) aw' rdata σ k' C' := by
  let allowed := solcSlotWordAt (allowanceSlot sender (accountWord I.source) id) σ I
  let rawMem := tripleMappingMemory sender (UInt256.land (accountWord I.source) solcAddrMask) id ⟨5⟩ mem
  have hm : rawMem = transferFromAllowanceMemory I sender id mem := by
    dsimp only [rawMem, transferFromAllowanceMemory]
    rw [solcAddrMask_clean (accountWord_canonical _)]
  have hs : keccakWord ⟨0⟩ ⟨64⟩ rawMem = allowanceSlot sender (accountWord I.source) id := by
    rw [hm, transferFromAllowanceMemory, tripleMappingMemory_slot _ _ _ _ hmem]; rfl
  have hv : solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ rawMem) σ I = allowed := congrArg (fun slot => solcSlotWordAt slot σ I) hs
  dsimp only
  by_cases hmax : allowed = maxAllowanceWord
  · rw [if_pos hmax]
    have hcond : UInt256.sub (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ rawMem) σ I) maxAllowanceWord = ⟨0⟩ := by
      rw [hv, hmax]; exact u256_sub_eq_zero_iff_eq.mpr rfl
    obtain ⟨k', C', hnext⟩ := poolManagerBlocks.poolManager_block_1010_fallthrough (R := R) hstack hcond h
    change RD (deployedRuntime v) I g s0 ⟨1106⟩
      (amount :: solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ rawMem) σ I :: balanceBurnStack sender id amount R)
      rawMem _ rdata σ k' C' at hnext
    rw [hv, hm] at hnext
    exact ⟨_, k', C', hnext⟩
  · rw [if_neg hmax]
    have hcond : UInt256.sub (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ rawMem) σ I) maxAllowanceWord ≠ ⟨0⟩ := by
      rw [hv]; exact fun hz => hmax (u256_sub_eq_zero_iff_eq.mp hz)
    have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 1113) = true := by
      rw [deployedRuntime_jumps]; jump_dest
    obtain ⟨k', C', hnext⟩ := poolManagerBlocks.poolManager_block_1010_taken (R := R) hstack hcond hj h
    change RD (deployedRuntime v) I g s0 ⟨1113⟩
      (amount :: solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ rawMem) σ I :: balanceBurnStack sender id amount R)
      rawMem _ rdata σ k' C' at hnext
    rw [hv, hm] at hnext
    exact ⟨_, k', C', hnext⟩

theorem burnAllowanceStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {sender id amount value extra : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 11 ≤ 1024) (hmem : mem.size = 96) (hp : I.perm = true)
    (h : RD (deployedRuntime v) I g s0 ⟨1122⟩ (value :: balanceBurnStack sender id amount (extra :: R))
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨972⟩ (balanceBurnStack sender id amount (extra :: R))
      (transferFromAllowanceMemory I sender id mem) aw' rdata
      (sstoreAccountMap I.codeOwner σ (allowanceSlot sender (accountWord I.source) id) value) k' C' := by
  have hj1106 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 1106) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have hj972 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 972) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  obtain ⟨k', C', h1106⟩ := poolManagerBlocks.poolManager_block_1122 (R := R) hstack hp hj1106 h
  let rawMem := tripleMappingMemory sender (UInt256.land (accountWord I.source) solcAddrMask) id ⟨5⟩ mem
  change RD (deployedRuntime v) I g s0 ⟨1106⟩
    (amount :: extra :: balanceBurnStack sender id amount (extra :: R)) rawMem _ rdata
    (sstoreAccountMap I.codeOwner σ (keccakWord ⟨0⟩ ⟨64⟩ rawMem) value) k' C' at h1106
  have h972 := poolManagerBlocks.poolManager_block_1106
    (by change R.length + 1 + 6 + 2 ≤ 1024; omega) hj972 h1106
  have hm : rawMem = transferFromAllowanceMemory I sender id mem := by
    dsimp only [rawMem, transferFromAllowanceMemory]
    rw [solcAddrMask_clean (accountWord_canonical _)]
  have hs : keccakWord ⟨0⟩ ⟨64⟩ rawMem = allowanceSlot sender (accountWord I.source) id := by
    rw [hm, transferFromAllowanceMemory, tripleMappingMemory_slot _ _ _ _ hmem]; rfl
  rw [hs, hm] at h972
  exact ⟨_, _, _, h972⟩

end Benchmarks.UniswapV4PoolManager
