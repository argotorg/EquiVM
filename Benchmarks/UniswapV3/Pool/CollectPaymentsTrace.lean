import Benchmarks.UniswapV3.Pool.CollectAmountsTrace
import Benchmarks.UniswapV3.Pool.SafeTransfer
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_027

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def collectPaymentMap (σ : AccountMap) (ee : ExecutionEnv) (key : UInt256)
    (second : Bool) (amount : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3)
    (protocolFeeUpdateWord second (solcSlotWordAt (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3) σ ee)
      (UInt256.sub (positionOwedWord key second σ ee) amount))

theorem SourceState.collectPaymentState {s0 ee σ evm} (hs : SourceState s0 ee σ evm)
    (key : UInt256) (second : Bool) (amount : UInt256) :
    SourceState s0 ee (collectPaymentMap σ ee key second amount)
      (collectPaymentState evm key second amount) := by
  have h := hs.readModifyWrite (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3)
    (fun old => protocolFeeUpdateWord second old (UInt256.sub (positionOwedWord key second σ ee) amount))
  simpa only [collectPaymentMap, Benchmarks.UniswapV3.Pool.collectPaymentState,
    storePositionOwed, hs.accounts, hs.env, solcSlotWordAt] using h

theorem collectStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw key amount0 amount1 x3 x4 x5 x6 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (second : Bool) (recipient : AccountAddress)
    (rd : RD (deployedRuntime v) ee g s0 (if second then ⟨7879⟩ else ⟨7780⟩)
      (solcMappingSlot ⟨7⟩ key :: amount1 :: amount0 :: x3 :: x4 :: x5 :: x6 :: EVM.word recipient.val :: R)
      mem aw rdata σ k C)
    (hfit : (if second then amount1 else amount0).toNat < 2 ^ 128)
    (hperm : ee.perm = true) (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨15238⟩
      ((if second then amount1 else amount0) :: EVM.word recipient.val ::
        EVM.word (poolToken v second).val :: (if second then ⟨7965⟩ else ⟨7863⟩) ::
        solcMappingSlot ⟨7⟩ key :: amount1 :: amount0 :: x3 :: x4 :: x5 :: x6 :: EVM.word recipient.val :: R)
      mem aw rdata (collectPaymentMap σ ee key second (if second then amount1 else amount0)) k' C' := by
  cases second
  · obtain ⟨_, _, rdCall⟩ := uniswapV3Pool_block_7780 (immWords := wordsOf (immStore v)) hov hperm
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have hc : UInt256.land amount0 (UInt256.ofNat (2 ^ 128 - 1)) = amount0 := by
      rw [u256_land_comm]; exact uint128Word_clean hfit
    have hf := positionOwedWord_evm0 key σ ee
    unfold solcSlotWordAt at hf
    simp only [uniswapV3Pool_block_7780_stack, solcMask128, hc, wordsOf_immStore_token0, hf] at rdCall
    have hmap : sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3)
        (UInt256.lor (UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
          (UInt256.sub (positionOwedWord key false σ ee) amount0))
          (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
            (fun ac => ac.storage.getD (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3) (⟨0⟩ : UInt256)))
            (UInt256.lnot (UInt256.ofNat (2 ^ 128 - 1))))) =
        collectPaymentMap σ ee key false amount0 := rfl
    rw [hmap] at rdCall
    exact ⟨_, _, rdCall⟩
  · obtain ⟨_, _, rdCall⟩ := uniswapV3Pool_block_7879 (immWords := wordsOf (immStore v)) hov hperm
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have hc : UInt256.land amount1 (UInt256.ofNat (2 ^ 128 - 1)) = amount1 := by
      rw [u256_land_comm]; exact uint128Word_clean hfit
    have hf := positionOwedWord_evm1 key σ ee
    unfold solcSlotWordAt at hf
    simp only [uniswapV3Pool_block_7879_stack, solcMask128, hc, wordsOf_immStore_token1, hf] at rdCall
    simp only [solcShift128] at rdCall
    have hmap : sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3)
        (UInt256.lor (UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
          (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
            (fun ac => ac.storage.getD (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3) (⟨0⟩ : UInt256))))
          (UInt256.mul (UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
            (UInt256.sub (positionOwedWord key true σ ee) amount1)) (UInt256.ofNat (2 ^ 128)))) =
        collectPaymentMap σ ee key true amount1 := rfl
    rw [hmap] at rdCall
    exact ⟨_, _, rdCall⟩

theorem collectTransferX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p key amount0 amount1 x3 x4 x5 x6 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (second : Bool) (recipient : AccountAddress)
    (rd : RD (deployedRuntime v) ee g s0 (if second then ⟨7879⟩ else ⟨7780⟩)
      (solcMappingSlot ⟨7⟩ key :: amount1 :: amount0 :: x3 :: x4 :: x5 :: x6 :: EVM.word recipient.val :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hfit : (if second then amount1 else amount0).toNat < 2 ^ 128)
    (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 195 ≤ 2 ^ 200) (hov : R.length + 28 ≤ 1024) :
    let amount := if second then amount1 else amount0
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config (safeTransferFrame (immStore v) (poolToken v second) recipient amount)
        (collectPaymentState evm key second amount) safeTransferFunction.body .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecFuncBody config (safeTransferFrame (immStore v) (poolToken v second) recipient amount)
        (collectPaymentState evm key second amount) safeTransferFunction.body
        (.returned (safeTransferCallFrame (immStore v) (poolToken v second) recipient amount true out) evm' none) ∧
      RD (deployedRuntime v) ee g s0 (if second then ⟨7965⟩ else ⟨7863⟩)
        (solcMappingSlot ⟨7⟩ key :: amount1 :: amount0 :: x3 :: x4 :: x5 :: x6 :: EVM.word recipient.val :: R)
        mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ 128 ≤ mem'.size ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      next.toNat ≤ p.toNat + 2 ^ 138 + 163 := by
  dsimp only
  obtain ⟨_, _, rdCall⟩ := collectStoreX (v := v) second recipient rd hfit hperm (by omega)
  have hsCall := SourceState.collectPaymentState hs key second (if second then amount1 else amount0)
  rcases safeTransferX (v := v) (immStore v) (poolToken v second) recipient rdCall hsCall hperm
    hm hmem hzero hb (by cases second <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rw [uniswapV3PoolPatchedValidJumps v] <;> jump_dest)
    (by evm_ov) with hbad | ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rdDone, hm', hpref, hnext⟩
  · exact Or.inl hbad
  · refine Or.inr ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rdDone, hm',
      le_trans hmem hpref.size, ?_, hnext⟩
    rw [MemoryPrefix.memLoad hpref (UInt256.ofNat 96) (by decide)
      (by change 128 ≤ p.toNat; exact hm.lower) (by exact hmem), hzero]

def collectGuardStack (second : Bool) (key amount0 amount1 junk : UInt256) (R : List UInt256) :=
  if second then solcMappingSlot ⟨7⟩ key :: amount1 :: amount0 :: R
  else amount1 :: solcMappingSlot ⟨7⟩ key :: junk :: amount0 :: R

theorem collectPaymentX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p key lower upper amount0 amount1 junk x3 x4 x5 x6 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (second : Bool) (recipient : AccountAddress) (locals : Store)
    (rd : RD (deployedRuntime v) ee g s0 (if second then ⟨7863⟩ else ⟨7762⟩)
      (collectGuardStack second key amount0 amount1 junk (x3 :: x4 :: x5 :: x6 :: EVM.word recipient.val :: R))
      mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hvalues : CollectValues locals recipient lower upper key amount0 amount1)
    (hfit0 : amount0.toNat < 2 ^ 128) (hfit1 : amount1.toNat < 2 ^ 128)
    (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 195 ≤ 2 ^ 200) (hov : R.length + 28 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
        (collectTokenStmt second) .reverted) ∨
    ∃ evm' σ' locals' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
        (collectTokenStmt second) (.ok {contract := contract, locals := locals', immutables := immStore v} evm') ∧
      CollectValues locals' recipient lower upper key amount0 amount1 ∧
      RD (deployedRuntime v) ee g s0 (if second then ⟨7965⟩ else ⟨7863⟩)
        (solcMappingSlot ⟨7⟩ key :: amount1 :: amount0 :: x3 :: x4 :: x5 :: x6 :: EVM.word recipient.val :: R)
        mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ 128 ≤ mem'.size ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      next.toNat ≤ p.toNat + 2 ^ 138 + 163 := by
  have hfit : (if second then amount1 else amount0).toNat < 2 ^ 128 := by
    cases second
    · exact hfit0
    · exact hfit1
  have hc : UInt256.land (if second then amount1 else amount0) (UInt256.ofNat (2 ^ 128 - 1)) =
      (if second then amount1 else amount0) := by
    rw [u256_land_comm]; exact uint128Word_clean hfit
  have hget := CollectValues.amount hvalues second
  by_cases hz : (if second then amount1 else amount0) = ⟨0⟩
  · have hskip : ∃ k' C', RD (deployedRuntime v) ee g s0 (if second then ⟨7965⟩ else ⟨7863⟩)
        (solcMappingSlot ⟨7⟩ key :: amount1 :: amount0 :: x3 :: x4 :: x5 :: x6 :: EVM.word recipient.val :: R)
        mem aw rdata σ k' C' := by
      cases second <;> simp only [Bool.false_eq_true, ↓reduceIte] at hc hz
      · have hr := uniswapV3Pool_block_7762_taken (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [solcMask128, hc, hz]; decide)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
        exact ⟨_, _, hr⟩
      · have hr := uniswapV3Pool_block_7863_taken (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [solcMask128, hc, hz]; decide)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
        exact ⟨_, _, hr⟩
    obtain ⟨k', C', rdSkip⟩ := hskip
    have hget0 : locals.get? (poolAmountName second) = some (.int 0) := by
      simpa only [hz, show Int.ofNat (⟨0⟩ : UInt256).toNat = (0 : Int) from by decide] using hget
    exact Or.inr ⟨evm, σ, locals, rdata, mem, aw, p, k', C', hs,
      collectTokenZero locals (immStore v) evm second hget0, hvalues, rdSkip, hm, hmem, hzero,
      le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)⟩
  · have hpos : 0 < (if second then amount1 else amount0).toNat := by
      by_contra hn
      exact hz (uint256_toNat_eq_zero (by omega))
    have hready : ∃ k' C', RD (deployedRuntime v) ee g s0 (if second then ⟨7879⟩ else ⟨7780⟩)
        (solcMappingSlot ⟨7⟩ key :: amount1 :: amount0 :: x3 :: x4 :: x5 :: x6 :: EVM.word recipient.val :: R)
        mem aw rdata σ k' C' := by
      cases second <;> simp only [Bool.false_eq_true, ↓reduceIte] at hc hz
      · have hr := uniswapV3Pool_block_7762_fallthrough (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [solcMask128, hc]; exact isZero_eq_zero_of_ne hz) rd
        exact ⟨_, _, hr⟩
      · have hr := uniswapV3Pool_block_7863_fallthrough (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [solcMask128, hc]; exact isZero_eq_zero_of_ne hz) rd
        exact ⟨_, _, hr⟩
    obtain ⟨_, _, rdReady⟩ := hready
    rcases collectTransferX (v := v) second recipient rdReady hs hperm hfit hm hmem hzero hb hov with
      ⟨rdRev, hcall⟩ | ⟨evm', σ', out, mem', aw', next, k', C', hs', hcall, rdDone, hm', hmem', hz', hn⟩
    · exact Or.inl ⟨rdRev, collectTokenReverts v locals evm key second recipient _ hvalues.recipient
        hget hvalues.position hpos hcall⟩
    · exact Or.inr ⟨evm', σ', locals.insert (poolTransferCallName second) .unit,
        out, mem', aw', next, k', C', hs',
        collectTokenReturns v locals evm evm' key second recipient _ _ hvalues.recipient
          hget hvalues.position hpos hcall,
        collectPaid_values hvalues second, rdDone, hm', hmem', hz', hn⟩

end Benchmarks.UniswapV3.Pool
