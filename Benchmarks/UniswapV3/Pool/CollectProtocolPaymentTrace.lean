import Benchmarks.UniswapV3.Pool.CollectProtocolPaymentsSource
import Benchmarks.UniswapV3.Pool.SafeTransfer

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000


theorem collectProtocolAdjust0X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw amount0 amount1 : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨9080⟩ (amount1 :: amount0 :: R) mem aw rdata σ k C)
    (hpos : 0 < amount0.toNat) (hfit : amount0.toNat < 2 ^ 128) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨9109⟩
      (amount1 :: collectProtocolAdjustedAmount amount0 (protocolFeesWord false σ ee) :: R)
      mem aw rdata σ k' C' := by
  have hc : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) amount0 = amount0 := uint128Word_clean hfit
  have hf : UInt256.land
      (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
        (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))
      (UInt256.ofNat (2 ^ 128 - 1)) = protocolFeesWord false σ ee := rfl
  by_cases heq : amount0 = protocolFeesWord false σ ee
  · obtain ⟨_, _, rdEq⟩ := uniswapV3Pool_block_9080_fallthrough
      (immWords := wordsOf (immStore v)) hov
      (by rw [solcMask128, hf, hc, ← heq, uInt256_eq_self]; decide) rd
    have rdDec := uniswapV3Pool_block_9102 (immWords := wordsOf (immStore v)) (by evm_ov) rdEq
    have hdec : amount0 + UInt256.lnot (UInt256.ofNat 0) = UInt256.sub amount0 ⟨1⟩ :=
      u256_add_lnot_zero_eq_sub_one amount0
    simp only [uniswapV3Pool_block_9102_stack, hdec] at rdDec
    rw [collectProtocolAdjustedAmount_eq_sub amount0 _ heq hpos hfit]
    exact ⟨_, _, rdDec⟩
  · rw [collectProtocolAdjustedAmount, if_neg heq]
    exact uniswapV3Pool_block_9080_taken (immWords := wordsOf (immStore v)) hov
      (by rw [solcMask128, hf, hc, u256_eq_of_ne (Ne.symm heq)]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd

theorem collectProtocolAdjust1X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw amount : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨9207⟩ (amount :: R) mem aw rdata σ k C)
    (hpos : 0 < amount.toNat) (hfit : amount.toNat < 2 ^ 128) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨9240⟩
      (collectProtocolAdjustedAmount amount (protocolFeesWord true σ ee) :: R)
      mem aw rdata σ k' C' := by
  have hc : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) amount = amount := uint128Word_clean hfit
  have hf : UInt256.land (UInt256.div
      (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
        (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)))
      (UInt256.ofNat (2 ^ 128 - 1)) = protocolFeesWord true σ ee := by
    rw [solcShift128]; rfl
  by_cases heq : amount = protocolFeesWord true σ ee
  · obtain ⟨_, _, rdEq⟩ := uniswapV3Pool_block_9207_fallthrough
      (immWords := wordsOf (immStore v)) hov
      (by rw [solcMask128, hf, hc, ← heq, uInt256_eq_self]; decide) rd
    have rdDec := uniswapV3Pool_block_9236 (immWords := wordsOf (immStore v)) (by evm_ov) rdEq
    have hdec : UInt256.lnot (UInt256.ofNat 0) + amount = UInt256.sub amount ⟨1⟩ :=
      lnot_zero_add amount
    simp only [uniswapV3Pool_block_9236_stack, hdec] at rdDec
    rw [collectProtocolAdjustedAmount_eq_sub amount _ heq hpos hfit]
    exact ⟨_, _, rdDec⟩
  · rw [collectProtocolAdjustedAmount, if_neg heq]
    exact uniswapV3Pool_block_9207_taken (immWords := wordsOf (immStore v)) hov
      (by rw [solcMask128, hf, hc, u256_eq_of_ne (Ne.symm heq)]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd

def collectProtocolFeeMap (σ : AccountMap) (ee : ExecutionEnv) (second : Bool) (amount : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ ⟨3⟩
    (protocolFeeUpdateWord second (solcSlotWordAt ⟨3⟩ σ ee)
      (UInt256.sub (protocolFeesWord second σ ee) amount))

theorem SourceState.collectProtocolFeeState {s0 ee σ evm} (hs : SourceState s0 ee σ evm)
    (second : Bool) (amount : UInt256) :
    SourceState s0 ee (collectProtocolFeeMap σ ee second amount)
      (collectProtocolFeeState evm second amount) := by
  have h := hs.readModifyWrite ⟨3⟩ (fun old => protocolFeeUpdateWord second old
    (UInt256.sub (protocolFeesWord second σ ee) amount))
  simpa only [collectProtocolFeeMap, Benchmarks.UniswapV3.Pool.collectProtocolFeeState,
    storeProtocolFee, hs.accounts, hs.env, solcSlotWordAt] using h

theorem collectProtocolStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw amount0 amount1 x2 x3 : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool) (recipient : AccountAddress)
    (rd : RD (deployedRuntime v) ee g s0 (if second then ⟨9240⟩ else ⟨9109⟩)
      (amount1 :: amount0 :: x2 :: x3 :: EVM.word recipient.val :: R) mem aw rdata σ k C)
    (hfit : (if second then amount1 else amount0).toNat < 2 ^ 128)
    (hperm : ee.perm = true) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨15238⟩
      ((if second then amount1 else amount0) :: EVM.word recipient.val ::
        EVM.word (poolToken v second).val :: (if second then ⟨9325⟩ else ⟨9191⟩) ::
        amount1 :: amount0 :: x2 :: x3 :: EVM.word recipient.val :: R) mem aw rdata
      (collectProtocolFeeMap σ ee second (if second then amount1 else amount0)) k' C' := by
  cases second
  · obtain ⟨_, _, rdCall⟩ := uniswapV3Pool_block_9109 (immWords := wordsOf (immStore v)) hov hperm
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have hc : UInt256.land amount0 (UInt256.ofNat (2 ^ 128 - 1)) = amount0 := by
      rw [u256_land_comm]; exact uint128Word_clean hfit
    simp only [uniswapV3Pool_block_9109_stack, solcMask128, hc, wordsOf_immStore_token0] at rdCall
    have hf : UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
        (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) = protocolFeesWord false σ ee := u256_land_comm _ _
    have hm : sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 3)
        (UInt256.lor (UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
          (UInt256.sub (protocolFeesWord false σ ee) amount0))
          (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.lnot (UInt256.ofNat (2 ^ 128 - 1))))) =
        collectProtocolFeeMap σ ee false amount0 := rfl
    simp only [hf, hm] at rdCall
    exact ⟨_, _, rdCall⟩
  · obtain ⟨_, _, rdCall⟩ := uniswapV3Pool_block_9240 (immWords := wordsOf (immStore v)) hov hperm
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have hc : UInt256.land amount1 (UInt256.ofNat (2 ^ 128 - 1)) = amount1 := by
      rw [u256_land_comm]; exact uint128Word_clean hfit
    simp only [uniswapV3Pool_block_9240_stack, solcMask128, hc, wordsOf_immStore_token1] at rdCall
    simp only [solcShift128] at rdCall
    have hf : UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
        (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) (UInt256.ofNat (2 ^ 128))) =
        protocolFeesWord true σ ee := u256_land_comm _ _
    have hm : sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 3)
        (UInt256.lor (UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))))
          (UInt256.mul (UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
            (UInt256.sub (protocolFeesWord true σ ee) amount1)) (UInt256.ofNat (2 ^ 128)))) =
        collectProtocolFeeMap σ ee true amount1 := rfl
    simp only [hf, hm] at rdCall
    exact ⟨_, _, rdCall⟩

theorem collectProtocolTransferX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p amount0 amount1 x2 x3 : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool) (recipient : AccountAddress)
    (rd : RD (deployedRuntime v) ee g s0 (if second then ⟨9240⟩ else ⟨9109⟩)
      (amount1 :: amount0 :: x2 :: x3 :: EVM.word recipient.val :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hfit : (if second then amount1 else amount0).toNat < 2 ^ 128)
    (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 195 ≤ 2 ^ 200) (hov : R.length + 25 ≤ 1024) :
    let amount := if second then amount1 else amount0
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config (safeTransferFrame (immStore v) (poolToken v second) recipient amount)
        (collectProtocolFeeState evm second amount) safeTransferFunction.body .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecFuncBody config (safeTransferFrame (immStore v) (poolToken v second) recipient amount)
        (collectProtocolFeeState evm second amount) safeTransferFunction.body
        (.returned (safeTransferCallFrame (immStore v) (poolToken v second) recipient amount true out)
          evm' none) ∧
      RD (deployedRuntime v) ee g s0 (if second then ⟨9325⟩ else ⟨9191⟩)
        (amount1 :: amount0 :: x2 :: x3 :: EVM.word recipient.val :: R) mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ 128 ≤ mem'.size ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      next.toNat ≤ p.toNat + 2 ^ 138 + 163 := by
  dsimp only
  obtain ⟨_, _, rdCall⟩ := collectProtocolStoreX (v := v) second recipient rd hfit hperm (by omega)
  have hsCall := SourceState.collectProtocolFeeState hs second (if second then amount1 else amount0)
  rcases safeTransferX (v := v) (immStore v) (poolToken v second) recipient rdCall hsCall hperm
    hm hmem hzero hb (by cases second <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rw [uniswapV3PoolPatchedValidJumps v] <;> jump_dest)
    (by evm_ov) with hbad | ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rdDone, hm', hpref, hnext⟩
  · exact Or.inl hbad
  · refine Or.inr ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rdDone, hm',
      le_trans hmem hpref.size, ?_, hnext⟩
    rw [MemoryPrefix.memLoad hpref (UInt256.ofNat 96) (by decide)
      (by change 128 ≤ p.toNat; exact hm.lower) (by exact hmem), hzero]

theorem CollectProtocolValues.amount {locals : Store} {recipient : AccountAddress}
    {amount0 amount1 : UInt256} (h : CollectProtocolValues locals recipient amount0 amount1) (second : Bool) :
    locals.get? (poolAmountName second) =
      some (.int (Int.ofNat (if second then amount1 else amount0).toNat)) := by
  cases second
  · exact h.amount0
  · exact h.amount1

theorem collectProtocolPositiveX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p amount0 amount1 x2 x3 : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool) (recipient : AccountAddress)
    (locals : Store)
    (rd : RD (deployedRuntime v) ee g s0 (if second then ⟨9207⟩ else ⟨9080⟩)
      (amount1 :: amount0 :: x2 :: x3 :: EVM.word recipient.val :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hvalues : CollectProtocolValues locals recipient amount0 amount1)
    (hpos : 0 < (if second then amount1 else amount0).toNat)
    (hfit : (if second then amount1 else amount0).toNat < 2 ^ 128)
    (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 195 ≤ 2 ^ 200) (hov : R.length + 25 ≤ 1024) :
    let amount := if second then amount1 else amount0
    let fee := protocolFeesWord second evm.accountMap evm.executionEnv
    let adjusted := collectProtocolAdjustedAmount amount fee
    let amount0' := if second then amount0 else adjusted
    let amount1' := if second then adjusted else amount1
    let locals' := collectProtocolPaidLocals locals second amount fee
    (RDrev (deployedRuntime v) g s0 ∧
      ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
        (collectProtocolTokenStmt second) .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
        (collectProtocolTokenStmt second)
        (.ok {contract := contract, locals := locals', immutables := immStore v} evm') ∧
      RD (deployedRuntime v) ee g s0 (if second then ⟨9325⟩ else ⟨9191⟩)
        (amount1' :: amount0' :: x2 :: x3 :: EVM.word recipient.val :: R) mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ 128 ≤ mem'.size ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      next.toNat ≤ p.toNat + 2 ^ 138 + 163 := by
  dsimp only
  let amount := if second then amount1 else amount0
  let fee := protocolFeesWord second evm.accountMap evm.executionEnv
  let adjusted := collectProtocolAdjustedAmount amount fee
  let a0 := if second then amount0 else adjusted
  let a1 := if second then adjusted else amount1
  have hsel : (if second then a1 else a0) = adjusted := by cases second <;> rfl
  have hfee : protocolFeesWord second σ ee = fee := by simp only [fee, hs.accounts, hs.env]
  have hget := CollectProtocolValues.amount hvalues second
  have hadjust : adjusted.toNat < 2 ^ 128 := collectProtocolAdjustedAmount_lt amount fee hfit
  have hrd : ∃ k' C', RD (deployedRuntime v) ee g s0 (if second then ⟨9240⟩ else ⟨9109⟩)
      (a1 :: a0 :: x2 :: x3 :: EVM.word recipient.val :: R) mem aw rdata σ k' C' := by
    cases second
    · obtain ⟨k', C', hr⟩ := collectProtocolAdjust0X (v := v) rd hpos hfit (by evm_ov)
      rw [hfee] at hr
      exact ⟨k', C', hr⟩
    · obtain ⟨k', C', hr⟩ := collectProtocolAdjust1X (v := v) rd hpos hfit (by evm_ov)
      rw [hfee] at hr
      exact ⟨k', C', hr⟩
  obtain ⟨_, _, rdReady⟩ := hrd
  rcases collectProtocolTransferX (v := v) second recipient rdReady hs hperm
      (by rw [hsel]; exact hadjust) hm hmem hzero hb hov with
    ⟨rdRev, hcall⟩ | ⟨evm', σ', out, mem', aw', next, k', C', hs', hcall, rdDone, hm', hmem', hz', hn⟩
  · rw [hsel] at hcall
    exact Or.inl ⟨rdRev, collectProtocolTokenReverts v locals evm second recipient amount
      hvalues.recipient hget hvalues.fees hpos hcall⟩
  · rw [hsel] at hcall
    exact Or.inr ⟨evm', σ', out, mem', aw', next, k', C', hs',
      collectProtocolTokenReturns v locals evm evm' second recipient amount _
        hvalues.recipient hget hvalues.fees hpos hcall, rdDone, hm', hmem', hz', hn⟩

def collectProtocolGuardStack (second : Bool) (amount0 amount1 junk : UInt256)
    (tail : List UInt256) : List UInt256 :=
  if second then amount1 :: amount0 :: tail else amount1 :: junk :: amount0 :: tail

theorem collectProtocolPaymentX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p amount0 amount1 junk x2 x3 : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool) (recipient : AccountAddress)
    (locals : Store)
    (rd : RD (deployedRuntime v) ee g s0 (if second then ⟨9191⟩ else ⟨9062⟩)
      (collectProtocolGuardStack second amount0 amount1 junk (x2 :: x3 :: EVM.word recipient.val :: R))
      mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hvalues : CollectProtocolValues locals recipient amount0 amount1)
    (hfit0 : amount0.toNat < 2 ^ 128) (hfit1 : amount1.toNat < 2 ^ 128)
    (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 195 ≤ 2 ^ 200) (hov : R.length + 25 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
        (collectProtocolTokenStmt second) .reverted) ∨
    ∃ evm' σ' locals' amount0' amount1' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
        (collectProtocolTokenStmt second)
        (.ok {contract := contract, locals := locals', immutables := immStore v} evm') ∧
      CollectProtocolValues locals' recipient amount0' amount1' ∧
      amount0'.toNat < 2 ^ 128 ∧ amount1'.toNat < 2 ^ 128 ∧
      RD (deployedRuntime v) ee g s0 (if second then ⟨9325⟩ else ⟨9191⟩)
        (amount1' :: amount0' :: x2 :: x3 :: EVM.word recipient.val :: R) mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ 128 ≤ mem'.size ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      next.toNat ≤ p.toNat + 2 ^ 138 + 163 := by
  have hfit : (if second then amount1 else amount0).toNat < 2 ^ 128 := by
    cases second
    · exact hfit0
    · exact hfit1
  have hc : UInt256.land (if second then amount1 else amount0) (UInt256.ofNat (2 ^ 128 - 1)) =
      (if second then amount1 else amount0) := by
    rw [u256_land_comm]; exact uint128Word_clean hfit
  have hget := CollectProtocolValues.amount hvalues second
  by_cases hz : (if second then amount1 else amount0) = ⟨0⟩
  · have hskip : ∃ k' C', RD (deployedRuntime v) ee g s0 (if second then ⟨9325⟩ else ⟨9191⟩)
        (amount1 :: amount0 :: x2 :: x3 :: EVM.word recipient.val :: R) mem aw rdata σ k' C' := by
      cases second <;> simp only [Bool.false_eq_true, ↓reduceIte] at hc hz
      · have hr := uniswapV3Pool_block_9062_taken (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [solcMask128, hc, hz]; decide)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
        exact ⟨_, _, hr⟩
      · have hr := uniswapV3Pool_block_9191_taken (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [solcMask128, hc, hz]; decide)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
        exact ⟨_, _, hr⟩
    obtain ⟨k', C', rdSkip⟩ := hskip
    have hget0 : locals.get? (poolAmountName second) = some (.int 0) := by
      simpa only [hz, show Int.ofNat (⟨0⟩ : UInt256).toNat = (0 : Int) from by decide] using hget
    exact Or.inr ⟨evm, σ, locals, amount0, amount1, rdata, mem, aw, p, k', C', hs,
      collectProtocolTokenZero locals (immStore v) evm second hget0, hvalues, hfit0, hfit1, rdSkip,
      hm, hmem, hzero, le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)⟩
  · have hpos : 0 < (if second then amount1 else amount0).toNat := by
      by_contra hn
      exact hz (uint256_toNat_eq_zero (by omega))
    have hready : ∃ k' C', RD (deployedRuntime v) ee g s0 (if second then ⟨9207⟩ else ⟨9080⟩)
        (amount1 :: amount0 :: x2 :: x3 :: EVM.word recipient.val :: R) mem aw rdata σ k' C' := by
      cases second <;> simp only [Bool.false_eq_true, ↓reduceIte] at hc hz
      · have hr := uniswapV3Pool_block_9062_fallthrough (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [solcMask128, hc]; exact isZero_eq_zero_of_ne hz) rd
        exact ⟨_, _, hr⟩
      · have hr := uniswapV3Pool_block_9191_fallthrough (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [solcMask128, hc]; exact isZero_eq_zero_of_ne hz) rd
        exact ⟨_, _, hr⟩
    obtain ⟨_, _, rdReady⟩ := hready
    rcases collectProtocolPositiveX (v := v) second recipient locals rdReady hs hperm hvalues
        hpos hfit hm hmem hzero hb hov with
      hbad | ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rdDone, hm', hmem', hz', hn⟩
    · exact Or.inl hbad
    · let fee := protocolFeesWord second evm.accountMap evm.executionEnv
      let amount := if second then amount1 else amount0
      let adjusted := collectProtocolAdjustedAmount amount fee
      let a0 := if second then amount0 else adjusted
      let a1 := if second then adjusted else amount1
      let locals' := collectProtocolPaidLocals locals second amount fee
      have hvals : CollectProtocolValues locals' recipient a0 a1 := by
        cases second <;> exact collectProtocolPaid_values hvalues _ fee
      have hadj : adjusted.toNat < 2 ^ 128 := collectProtocolAdjustedAmount_lt amount fee hfit
      have hb0 : a0.toNat < 2 ^ 128 := by cases second; exact hadj; exact hfit0
      have hb1 : a1.toNat < 2 ^ 128 := by cases second; exact hfit1; exact hadj
      exact Or.inr ⟨evm', σ', locals', a0, a1, out, mem', aw', next, k', C', hs', hbody,
        hvals, hb0, hb1, rdDone, hm', hmem', hz', hn⟩

end Benchmarks.UniswapV3.Pool
