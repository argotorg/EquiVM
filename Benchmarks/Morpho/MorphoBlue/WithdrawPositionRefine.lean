import Benchmarks.Morpho.MorphoBlue.WithdrawMathRefine
import Benchmarks.Morpho.MorphoBlue.SupplyPositionRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoWithdrawPositionReachSub {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw id assets shares account receiver : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 32 ≤ 1024)
    (hc : account.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7737)
      (withdrawUpdateTail id assets shares account receiver R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12833)
      ([solcSlotWordAt (positionSlot id account) σ ee, shares, UInt256.ofNat 7774, positionSlot id account] ++
        withdrawUpdateTail id assets shares account receiver R)
      (supplyPositionMem id account mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_7737_packed (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 17 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_7737_stack, morphoBlocks.morpho_block_7737_memory] at rd1
  rw [solcAddrMask_clean hc] at rd1
  let m1 := twoWordHashMem id (UInt256.ofNat 2) mem
  have hh1 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1 = solcMappingSlot ⟨2⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  let m2 := twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1) m1
  have hm2 : m2 = supplyPositionMem id account mem := by dsimp only [m2]; rw [hh1]; rfl
  have hh2 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (supplyPositionMem id account mem) =
      positionSlot id account := twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    ([solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2) σ ee, shares,
      UInt256.ofNat 7774, keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2] ++
      withdrawUpdateTail id assets shares account receiver R) m2 _ _ _ _ _ at rd1
  rw [hm2, hh2] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoWithdrawPositionStatic {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw slot value : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 3 ≤ 1024)
    (hp : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7774) (value :: slot :: R) mem aw out σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  have r1 := h.jumpdest (by
    immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
      (⟨7774⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
      morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by
    immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
      (⟨7775⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  exact r2.sstoreStatic hp (by
    immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
      (⟨7776⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)

theorem MarketTransferLocals.evalPositionShares {p assets shares account receiver locals}
    (hl : MarketTransferLocals p assets shares account receiver locals) (imms : Store) (evm : EVM.State)
    (hc : account.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"position", [.mindex (.var "id"), .mindex (.var "onBehalf"), .field "supplyShares"]⟩) =
      .ok (.int (Int.ofNat (solcSlotWordAt (positionSlot p.id account) evm.accountMap evm.executionEnv).toNat)) :=
  evalMorphoPositionField evm locals imms _ _ p.id account 0 hl.position
    (hl.evalId imms evm) (hl.evalAccount imms evm) hc

inductive WithdrawPositionRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (withdrawTransition.body.drop 14) .reverted → RDrev (deployedRuntime v) g s0 →
      WithdrawPositionRefines v ee g s0 p assets shares account receiver locals imms evm mem R
  | static : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (withdrawTransition.body.drop 14) .staticViolation → RDstatic (deployedRuntime v) g s0 →
      WithdrawPositionRefines v ee g s0 p assets shares account receiver locals imms evm mem R
  | ok {evm' σ' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (withdrawTransition.body.drop 14) { contract := contract, locals := locals, immutables := imms }
        evm' (withdrawTransition.body.drop 15) → SourceState s0 ee σ' evm' → ee.perm = true →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
        ([shares, UInt256.ofNat 7788, UInt256.ofNat 7813] ++ withdrawUpdateTail p.id assets shares account receiver R)
        (supplyPositionMem p.id account mem) aw' out' σ' k' C' →
      WithdrawPositionRefines v ee g s0 p assets shares account receiver locals imms evm mem R

theorem morphoWithdrawPositionRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw assets shares account receiver : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords)
    (locals imms : Store) (hstack : R.length + 32 ≤ 1024) (hc : account.toNat < EVM.addressModulus)
    (hl : MarketTransferLocals p assets shares account receiver locals) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7737)
      (withdrawUpdateTail p.id assets shares account receiver R) mem aw out σ k C) :
    WithdrawPositionRefines v ee g s0 p assets shares account receiver locals imms evm mem R := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoWithdrawPositionReachSub (v := v) hstack hc h
  have hp := hl.evalPositionShares imms evm hc
  have hsh := hl.evalShares imms evm
  by_cases hf : shares.toNat ≤ (solcSlotWordAt (positionSlot p.id account) σ ee).toNat
  swap
  · have hf' : (solcSlotWordAt (positionSlot p.id account) evm.accountMap evm.executionEnv).toNat < shares.toNat := by
      simpa only [hs.env, ← hs.accounts] using Nat.lt_of_not_ge hf
    exact .reverted (ExecBlock.consRevert (ExecStmt.assignExprRevert (evalCheckedSubUnderflow hp hsh hf')))
      (morphoCheckedSubReverts (v := v) (by change R.length + 15 + 6 ≤ 1024; omega) (Nat.lt_of_not_ge hf) rd1)
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedSubOk (v := v) (by change R.length + 15 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hf rd1
  have hf' : shares.toNat ≤ (solcSlotWordAt (positionSlot p.id account) evm.accountMap evm.executionEnv).toNat := by
    simpa only [hs.env, ← hs.accounts] using hf
  have hass : ExecStmt config { contract := contract, locals := locals, immutables := imms }
      evm withdrawTransition.body[14]!
      (.ok { contract := contract, locals := locals, immutables := imms }
        (storePositionSupplyShares evm p.id account
          (UInt256.sub (solcSlotWordAt (positionSlot p.id account) evm.accountMap evm.executionEnv) shares))) :=
    ExecStmt.assign (evalExpr_uint256_sub hp hsh hf')
      (assignPositionSupplyShares evm locals imms _ _ p.id account _ hc hl.position (hl.evalId imms evm) (hl.evalAccount imms evm))
  by_cases hperm : ee.perm = true
  · obtain ⟨k3, C3, rd3⟩ := morphoBlocks.morpho_block_7774 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 16 ≤ 1024; omega) hperm
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    have hs' := storePositionSupplyShares_bridge hs p.id account
      (UInt256.sub (solcSlotWordAt (positionSlot p.id account) evm.accountMap evm.executionEnv) shares)
    exact .ok (StateBlock.start.step hass) (by simpa only [hs.env, ← hs.accounts] using hs') hperm rd3
  · exact .static (ExecBlock.consStatic (execStmt_assign_static hass (by rw [hs.env]; exact Bool.eq_false_iff.mpr hperm)))
      (morphoWithdrawPositionStatic (v := v) (by change R.length + 14 + 3 ≤ 1024; omega) (Bool.eq_false_iff.mpr hperm) rd2)

end Benchmarks.Morpho.MorphoBlue
