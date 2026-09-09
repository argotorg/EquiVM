import Benchmarks.WETH9.Bytecode
import Benchmarks.WETH9.ConstructorTrusted
import Reasoning.Reach

/-!
# WETH9 constructor — the symbolic keccak-data clear loop (creation.hex pc 254–276)

The compact-string store subroutine ends by zeroing the `oldWords = ⌈oldLen/32⌉` keccak-data
words `keccak(slot)+0 .. keccak(slot)+oldWords-1`, then runs a small return dance back to the
caller's return address leaving `[slot]` on the stack.  This file discharges that loop with
`RD.whileLoopCarryFull` (variant = words remaining) and the `⟨244⟩→⟨274⟩→⟨244⟩→retAddr` dance.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.WETH9

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-! ## Cursor arithmetic (`keccak(slot) + i`) -/

theorem u256_add_zero (K : UInt256) : K + ⟨0⟩ = K := by
  apply u256_inj
  rw [uadd_toNat, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.add_zero]
  exact Nat.mod_eq_of_lt K.val.isLt

theorem weth9ClearCursor_toNat (K : UInt256) (oldWords i : Nat)
    (hK : K.toNat + oldWords < UInt256.size) (hi : i ≤ oldWords) :
    (K + UInt256.ofNat i).toNat = K.toNat + i := by
  rw [uadd_toNat, ulit_toNat' i (by omega), Nat.mod_eq_of_lt (by omega)]

theorem weth9ClearCursor_succ (K : UInt256) (a : Nat) :
    (⟨1⟩ : UInt256) + (K + UInt256.ofNat a) = K + UInt256.ofNat (a + 1) := by
  rw [← u256_one_add_ofNat, ← uadd_assoc, ← uadd_assoc, uadd_comm (⟨1⟩ : UInt256) K]

/-! ## The clear loop + return dance -/

/-- From the loop head `⟨254⟩` (carrying cursor `keccak(slot)+0`, bound `keccak(slot)+oldWords`,
    the two return-dance addresses, `slot`, `retAddr`, and post-short-store storage `σ'`), run the
    `SSTORE 0` loop to completion and the return dance, reaching `retAddr` with `[slot]` and the
    storage `clearDataWordsForwardFrom … keccak(slot) 0 oldWords`. -/
theorem weth9ClearLoopAndReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {k C : ℕ}
    (K : UInt256) (oldWords : Nat) (slot retAddr : UInt256)
    (hK : K.toNat + oldWords < UInt256.size)
    (hperm : ee.perm = true)
    (hRA : (D_J weth9CreationBytecode 0).contains retAddr = true)
    (h : RD weth9CreationBytecode ee g s0 ⟨254⟩
          [K, K + UInt256.ofNat oldWords, ⟨274⟩, ⟨244⟩, slot, retAddr]
          mem aw rdata (cA, σ') k C) :
    ∃ k' C', RD weth9CreationBytecode ee g s0 retAddr [slot] mem aw rdata
          (cA, clearDataWordsForwardFrom ee.codeOwner σ' K ⟨0⟩ oldWords) k' C' := by
  -- Package the loop into `RD.whileLoopCarryFull`.
  have hexit : ∀ a : ℕ, a + 0 = oldWords → ∀ k C,
      RD weth9CreationBytecode ee g s0 ⟨254⟩
        [K + UInt256.ofNat a, K + UInt256.ofNat oldWords, ⟨274⟩, ⟨244⟩, slot, retAddr]
        mem aw rdata (cA, clearDataWordsForwardFrom ee.codeOwner σ' K ⟨0⟩ a) k C →
      ∃ k' C', RD weth9CreationBytecode ee g s0 ⟨244⟩
        [K + UInt256.ofNat a, K + UInt256.ofNat oldWords, ⟨274⟩, ⟨244⟩, slot, retAddr]
        mem aw rdata (cA, clearDataWordsForwardFrom ee.codeOwner σ' K ⟨0⟩ a) k' C' := by
    intro a hInv k C hrd
    have ha : a = oldWords := by omega
    subst ha
    have hcond :
        UInt256.isZero (UInt256.gt (K + UInt256.ofNat a) (K + UInt256.ofNat a)) ≠ ⟨0⟩ := by
      rw [ugt_zero (le_refl _)]; decide
    exact ⟨_, _, evm_run hrd with [
      jumpdest, dup1, dup3, gt, iszero, push2 ⟨244⟩, jumpiT hcond (by decide +native)]⟩
  have hbody : ∀ (v : ℕ) (a : ℕ), a + (v + 1) = oldWords → ∀ k C,
      RD weth9CreationBytecode ee g s0 ⟨254⟩
        [K + UInt256.ofNat a, K + UInt256.ofNat oldWords, ⟨274⟩, ⟨244⟩, slot, retAddr]
        mem aw rdata (cA, clearDataWordsForwardFrom ee.codeOwner σ' K ⟨0⟩ a) k C →
      ∃ a' k' C', a' + v = oldWords ∧
        RD weth9CreationBytecode ee g s0 ⟨254⟩
          [K + UInt256.ofNat a', K + UInt256.ofNat oldWords, ⟨274⟩, ⟨244⟩, slot, retAddr]
          mem aw rdata (cA, clearDataWordsForwardFrom ee.codeOwner σ' K ⟨0⟩ a') k' C' := by
    intro v a hInv k C hrd
    have halt : a < oldWords := by omega
    have hcond :
        UInt256.isZero (UInt256.gt (K + UInt256.ofNat oldWords) (K + UInt256.ofNat a)) = ⟨0⟩ := by
      rw [ugt_one (by
        rw [weth9ClearCursor_toNat K oldWords a hK (by omega),
          weth9ClearCursor_toNat K oldWords oldWords hK (le_refl _)]
        omega)]
      decide
    have hbefore := evm_run hrd with [
      jumpdest, dup1, dup3, gt, iszero, push2 ⟨244⟩, jumpiNT hcond,
      push1 ⟨0⟩, dup2]
    obtain ⟨k', C', hafter⟩ := hbefore.sstore hperm (by decide +native) (by evm_ov)
    have hnext := evm_run hafter with [push1 ⟨1⟩, add, push2 ⟨254⟩, jump (by decide +native)]
    rw [weth9ClearCursor_succ K a, ← clearDataWordsForwardFrom_append ee.codeOwner σ' K a] at hnext
    exact ⟨a + 1, _, _, by omega, hnext⟩
  -- Feed the initial cursor state and run the loop to exhaustion.
  have h0 : RD weth9CreationBytecode ee g s0 ⟨254⟩
      [K + UInt256.ofNat 0, K + UInt256.ofNat oldWords, ⟨274⟩, ⟨244⟩, slot, retAddr]
      mem aw rdata (cA, clearDataWordsForwardFrom ee.codeOwner σ' K ⟨0⟩ 0) k C := by
    rw [show K + UInt256.ofNat 0 = K from by
      rw [show (UInt256.ofNat 0 : UInt256) = ⟨0⟩ from rfl]; exact u256_add_zero K]
    exact h
  obtain ⟨a', k', C', hInv0, hexitRD⟩ :=
    RD.whileLoopCarryFull ⟨254⟩ ⟨244⟩ (fun v i => i + v = oldWords)
      (fun i => [K + UInt256.ofNat i, K + UInt256.ofNat oldWords, ⟨274⟩, ⟨244⟩, slot, retAddr])
      (fun _ => mem) (fun _ => aw)
      (fun i => (cA, clearDataWordsForwardFrom ee.codeOwner σ' K ⟨0⟩ i))
      (fun i => [K + UInt256.ofNat i, K + UInt256.ofNat oldWords, ⟨274⟩, ⟨244⟩, slot, retAddr])
      hexit hbody oldWords 0 (by omega) k C h0
  have ha' : a' = oldWords := by omega
  subst ha'
  -- Return dance ⟨244⟩ → ⟨274⟩ → ⟨244⟩ → retAddr, leaving `[slot]`.
  exact ⟨_, _, evm_run hexitRD with [
    jumpdest, pop, swap1, jump (by decide +native),
    jumpdest, swap1, jump (by decide +native),
    jumpdest, pop, swap1, jump hRA]⟩

/-! ## Reconciling the EVM store-then-clear order with the Solm clear-then-store order -/

/-- The EVM stores the short word at `slot` **then** clears the keccak-data words; the Solm write
    clears **then** stores.  Since `slot` is disjoint from every cleared cursor `keccak(slot)+i`, the
    two agree up to `accountMapEquiv`. -/
theorem clear_sstore_comm_equiv (cO : AccountAddress) (K slot sw : UInt256) :
    ∀ (n : Nat) (σ : AccountMap), (∀ i, i < n → slot ≠ K + UInt256.ofNat i) →
      accountMapEquiv
        (clearDataWordsForwardFrom cO (sstoreAccountMap cO σ slot sw) K ⟨0⟩ n)
        (sstoreAccountMap cO (clearDataWordsForwardFrom cO σ K ⟨0⟩ n) slot sw)
  | 0, σ, _ => accountMapEquiv_refl _
  | n + 1, σ, hdisj => by
      rw [clearDataWordsForwardFrom_append cO (sstoreAccountMap cO σ slot sw) K n,
        clearDataWordsForwardFrom_append cO σ K n]
      refine accountMapEquiv.trans
        (accountMapEquiv_sstoreAccountMap cO (K + UInt256.ofNat n) ⟨0⟩
          (clear_sstore_comm_equiv cO K slot sw n σ (fun i hi => hdisj i (by omega)))) ?_
      exact (accountMapEquiv_sstoreAccountMap_erase_comm
        (clearDataWordsForwardFrom cO σ K ⟨0⟩ n) cO slot sw (K + UInt256.ofNat n)
        (hdisj n (by omega))).symm

/-- For `name`/`symbol` slots, every cleared cursor `keccak(slot)+i` (`i < oldWords`) differs from
    the small `slot` itself. -/
theorem weth9ClearSlotDisjoint (slot : UInt256) (hslot : slot = ⟨0⟩ ∨ slot = ⟨1⟩) (ow i : Nat)
    (hK : (Solm.solidityBytesDataBaseSlot slot).toNat + ow < UInt256.size) (hi : i < ow) :
    slot ≠ Solm.solidityBytesDataBaseSlot slot + UInt256.ofNat i := by
  intro heq
  have hval := weth9ClearCursor_toNat (Solm.solidityBytesDataBaseSlot slot) ow i hK (by omega)
  have hslotval := congrArg UInt256.toNat heq
  rw [hval] at hslotval
  rcases hslot with h | h <;> subst h
  · rw [weth9DataBaseSlot0] at hslotval
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (⟨0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563⟩ : UInt256).toNat
        = 0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563 from rfl] at hslotval
    omega
  · rw [weth9DataBaseSlot1] at hslotval
    simp only [show (⟨1⟩ : UInt256).toNat = 1 from rfl,
      show (⟨0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6⟩ : UInt256).toNat
        = 0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6 from rfl] at hslotval
    omega

/-- Combined reconciliation for `name`/`symbol`: the EVM's `clear(store(σ,slot,sw), K, ow)` is
    `accountMapEquiv` to the Solm's `store(clear(σ,K,ow), slot, sw)`. -/
theorem weth9ClearStoreCommEquiv (cO : AccountAddress) (σ : AccountMap) (slot sw : UInt256)
    (hslot : slot = ⟨0⟩ ∨ slot = ⟨1⟩) (ow : Nat)
    (hK : (Solm.solidityBytesDataBaseSlot slot).toNat + ow < UInt256.size) :
    accountMapEquiv
      (clearDataWordsForwardFrom cO (sstoreAccountMap cO σ slot sw)
        (Solm.solidityBytesDataBaseSlot slot) ⟨0⟩ ow)
      (sstoreAccountMap cO
        (clearDataWordsForwardFrom cO σ (Solm.solidityBytesDataBaseSlot slot) ⟨0⟩ ow) slot sw) :=
  clear_sstore_comm_equiv cO (Solm.solidityBytesDataBaseSlot slot) slot sw ow σ
    (fun i hi => weth9ClearSlotDisjoint slot hslot ow i hK hi)

end Benchmarks.WETH9
