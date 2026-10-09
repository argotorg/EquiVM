import Benchmarks.Morpho.MorphoBlue.SupplyMathRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def supplyPositionMem (id account : UInt256) (mem : ByteArray) : ByteArray :=
  twoWordHashMem account (solcMappingSlot ⟨2⟩ id) (twoWordHashMem id (UInt256.ofNat 2) mem)

theorem morphoSupplyPositionReachAdd {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw id assets shares account srcOff len : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3984)
      (supplyUpdateTail id assets shares account srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12651)
      ([solcSlotWordAt (positionSlot id account) σ ee, shares, UInt256.ofNat 4017, positionSlot id account] ++
        supplyUpdateTail id assets shares account srcOff len R)
      (supplyPositionMem id account mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_3984_packed (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 14 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  let m1 := twoWordHashMem id (UInt256.ofNat 2) mem
  have hh1 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1 = solcMappingSlot ⟨2⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  let m2 := twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1) m1
  have hm2 : m2 = supplyPositionMem id account mem := by dsimp only [m2]; rw [hh1]; rfl
  have hh2 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (supplyPositionMem id account mem) =
      positionSlot id account := twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    ([solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2) σ ee, shares,
      UInt256.ofNat 4017, keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2] ++
      supplyUpdateTail id assets shares account srcOff len R) m2 _ _ _ _ _ at rd1
  rw [hm2, hh2] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoSupplyPositionStatic {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw slot value : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 3 ≤ 1024)
    (hp : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4017) (value :: slot :: R) mem aw out σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  have r1 := h.jumpdest (by
    immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
      (⟨4017⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
      morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by
    immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
      (⟨4018⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  exact r2.sstoreStatic hp (by
    immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
      (⟨4019⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)

theorem SupplyLocals.evalPositionShares {p assets shares account data locals}
    (hl : SupplyLocals p assets shares account data locals) (imms : Store) (evm : EVM.State)
    (hc : account.toNat < EVM.addressModulus) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"position", [.mindex (.var "id"), .mindex (.var "onBehalf"), .field "supplyShares"]⟩) =
      .ok (.int (Int.ofNat (solcSlotWordAt (positionSlot p.id account) evm.accountMap evm.executionEnv).toNat)) :=
  evalMorphoPositionField evm locals imms _ _ p.id account 0 hl.position
    (hl.evalId imms evm) (hl.evalAccount imms evm) hc

inductive SupplyPositionRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets shares account srcOff len : UInt256)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (supplyTransition.body.drop 12) .reverted → RDrev (deployedRuntime v) g s0 →
      SupplyPositionRefines v ee g s0 p assets shares account srcOff len locals imms evm mem R
  | static : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (supplyTransition.body.drop 12) .staticViolation → RDstatic (deployedRuntime v) g s0 →
      SupplyPositionRefines v ee g s0 p assets shares account srcOff len locals imms evm mem R
  | ok {evm' σ' aw' out' k' C'} :
      StateBlock config { contract := contract, locals := locals, immutables := imms }
        evm (supplyTransition.body.drop 12) { contract := contract, locals := locals, immutables := imms }
        evm' (supplyTransition.body.drop 13) → SourceState s0 ee σ' evm' → ee.perm = true →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
        ([shares, UInt256.ofNat 4031, UInt256.ofNat 4056] ++ supplyUpdateTail p.id assets shares account srcOff len R)
        (supplyPositionMem p.id account mem) aw' out' σ' k' C' →
      SupplyPositionRefines v ee g s0 p assets shares account srcOff len locals imms evm mem R

theorem morphoSupplyPositionRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw assets shares account srcOff len : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (data : ByteArray)
    (locals imms : Store) (hstack : R.length + 24 ≤ 1024) (hc : account.toNat < EVM.addressModulus)
    (hl : SupplyLocals p assets shares account data locals) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3984)
      (supplyUpdateTail p.id assets shares account srcOff len R) mem aw out σ k C) :
    SupplyPositionRefines v ee g s0 p assets shares account srcOff len locals imms evm mem R := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoSupplyPositionReachAdd (v := v) hstack h
  have hp := hl.evalPositionShares imms evm hc
  have hsh := hl.evalShares imms evm
  by_cases hf : (solcSlotWordAt (positionSlot p.id account) σ ee).toNat + shares.toNat < UInt256.size
  swap
  · have hf' : UInt256.size ≤ (solcSlotWordAt (positionSlot p.id account) evm.accountMap evm.executionEnv).toNat + shares.toNat := by
      simpa only [hs.env, ← hs.accounts] using Nat.le_of_not_gt hf
    exact .reverted (ExecBlock.consRevert (ExecStmt.assignExprRevert (checkedAddSourceOverflow hp hsh hf')))
      (morphoCheckedAddReverts (v := v) (by change R.length + 12 + 6 ≤ 1024; omega) (Nat.le_of_not_gt hf) rd1)
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedAddOk (v := v) (by change R.length + 12 + 6 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hf rd1
  have hf' : (solcSlotWordAt (positionSlot p.id account) evm.accountMap evm.executionEnv).toNat + shares.toNat < UInt256.size := by
    simpa only [hs.env, ← hs.accounts] using hf
  have hass : ExecStmt config { contract := contract, locals := locals, immutables := imms }
      evm supplyTransition.body[12]!
      (.ok { contract := contract, locals := locals, immutables := imms }
        (storePositionSupplyShares evm p.id account
          (solcSlotWordAt (positionSlot p.id account) evm.accountMap evm.executionEnv + shares))) :=
    ExecStmt.assign (checkedAddSourceOk hp hsh hf')
      (assignPositionSupplyShares evm locals imms _ _ p.id account _ hc hl.position (hl.evalId imms evm) (hl.evalAccount imms evm))
  by_cases hperm : ee.perm = true
  · obtain ⟨k3, C3, rd3⟩ := morphoBlocks.morpho_block_4017 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 13 ≤ 1024; omega) hperm
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    have hs' := storePositionSupplyShares_bridge hs p.id account
      (solcSlotWordAt (positionSlot p.id account) evm.accountMap evm.executionEnv + shares)
    exact .ok (StateBlock.start.step hass) (by simpa only [hs.env, ← hs.accounts] using hs') hperm rd3
  · exact .static (ExecBlock.consStatic (execStmt_assign_static hass (by rw [hs.env]; exact Bool.eq_false_iff.mpr hperm)))
      (morphoSupplyPositionStatic (v := v) (by change R.length + 11 + 3 ≤ 1024; omega) (Bool.eq_false_iff.mpr hperm) rd2)

end Benchmarks.Morpho.MorphoBlue
