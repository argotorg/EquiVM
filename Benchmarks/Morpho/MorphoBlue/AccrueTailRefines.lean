import Benchmarks.Morpho.MorphoBlue.AccrueFinishRefine

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue

-- An IRM-body suffix ends before the common source timestamp assignment.
-- Its bytecode continuation has already performed that final assignment.
inductive AccrueTailRefines (fork : Ethereum.Fork) (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (imms locals : Store) (evm : EVM.State) (stmts : List Stmt)
    (ret : UInt256) (R : List UInt256) (spare : Nat) : Prop where
  | reverted : ExecBlock fork config { contract := contract, locals := locals, immutables := imms } evm stmts .reverted →
      RDrev fork (deployedRuntime v) g s0 → AccrueTailRefines fork v ee g s0 p imms locals evm stmts ret R spare
  | static : ExecBlock fork config { contract := contract, locals := locals, immutables := imms } evm stmts .staticViolation →
      RDstatic fork (deployedRuntime v) g s0 → AccrueTailRefines fork v ee g s0 p imms locals evm stmts ret R spare
  | ok {locals' evm' σ' mem' fp' aw' rdata' k' C'} :
      ExecBlock fork config { contract := contract, locals := locals, immutables := imms } evm stmts
        (.ok { contract := contract, locals := locals', immutables := imms } evm') →
      MarketLocals p locals' → SourceState s0 ee σ'
        (storeMarketLastUpdate evm' p.id (halfWord false (UInt256.ofNat evm'.executionEnv.header.timestamp))) →
      MorphoHeap mem' fp' spare →
      RD fork (deployedRuntime v) ee g s0 ret R mem' aw' rdata' σ' k' C' →
      AccrueTailRefines fork v ee g s0 p imms locals evm stmts ret R spare

theorem AccrueTailRefines.prepend {v ee g s0 p imms locals evm stmts ret R spare locals₀ evm₀ stmts₀}
    (h : AccrueTailRefines fork v ee g s0 p imms locals evm stmts ret R spare)
    (hab : StateBlock fork config { contract := contract, locals := locals₀, immutables := imms } evm₀ stmts₀
      { contract := contract, locals := locals, immutables := imms } evm stmts) :
    AccrueTailRefines fork v ee g s0 p imms locals₀ evm₀ stmts₀ ret R spare := by
  cases h with
  | reverted he hr => exact .reverted (hab.run he) hr
  | static he hr => exact .static (hab.run he) hr
  | ok he hl hs hm hr => exact .ok (hab.run he) hl hs hm hr

-- The stronger result also records exactly what the routine allocates and preserves.
inductive AccrueTailRefinesWithMemory (fork : Ethereum.Fork) (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (imms locals : Store) (evm : EVM.State) (stmts : List Stmt)
    (ret : UInt256) (R : List UInt256) (spare : Nat) (mem : ByteArray) (fp : UInt256) (extra : Nat) : Prop where
  | reverted : ExecBlock fork config { contract := contract, locals := locals, immutables := imms } evm stmts .reverted →
      RDrev fork (deployedRuntime v) g s0 → AccrueTailRefinesWithMemory fork v ee g s0 p imms locals evm stmts ret R spare mem fp extra
  | static : ExecBlock fork config { contract := contract, locals := locals, immutables := imms } evm stmts .staticViolation →
      RDstatic fork (deployedRuntime v) g s0 → AccrueTailRefinesWithMemory fork v ee g s0 p imms locals evm stmts ret R spare mem fp extra
  | ok {locals' evm' σ' mem' fp' aw' rdata' k' C'} :
      ee.perm = true →
      ExecBlock fork config { contract := contract, locals := locals, immutables := imms } evm stmts
        (.ok { contract := contract, locals := locals', immutables := imms } evm') →
      MarketLocals p locals' → SourceState s0 ee σ'
        (storeMarketLastUpdate evm' p.id (halfWord false (UInt256.ofNat evm'.executionEnv.header.timestamp))) →
      MorphoHeap mem' fp' spare →
      HeapAdvance mem fp mem' fp' (extra + if marketFieldWord σ' ee p.id 5 = ⟨0⟩ then 0 else 64) →
      RD fork (deployedRuntime v) ee g s0 ret R mem' aw' rdata' σ' k' C' →
      AccrueTailRefinesWithMemory fork v ee g s0 p imms locals evm stmts ret R spare mem fp extra

theorem AccrueTailRefinesWithMemory.forget {v ee g s0 p imms locals evm stmts ret R spare mem fp extra}
    (h : AccrueTailRefinesWithMemory fork v ee g s0 p imms locals evm stmts ret R spare mem fp extra) :
    AccrueTailRefines fork v ee g s0 p imms locals evm stmts ret R spare := by
  cases h with
  | reverted he hr => exact .reverted he hr
  | static he hr => exact .static he hr
  | ok _ he hl hs hm ha hr => exact .ok he hl hs hm hr

theorem AccrueTailRefinesWithMemory.prepend {v ee g s0 p imms locals evm stmts ret R spare mem fp extra locals₀ evm₀ stmts₀}
    (h : AccrueTailRefinesWithMemory fork v ee g s0 p imms locals evm stmts ret R spare mem fp extra)
    (hab : StateBlock fork config { contract := contract, locals := locals₀, immutables := imms } evm₀ stmts₀
      { contract := contract, locals := locals, immutables := imms } evm stmts) :
    AccrueTailRefinesWithMemory fork v ee g s0 p imms locals₀ evm₀ stmts₀ ret R spare mem fp extra := by
  cases h with
  | reverted he hr => exact .reverted (hab.run he) hr
  | static he hr => exact .static (hab.run he) hr
  | ok hp he hl hs hm ha hr => exact .ok hp (hab.run he) hl hs hm ha hr

theorem AccrueTailRefinesWithMemory.memoryPrepend {v ee g s0 p imms locals evm stmts ret R spare mem fp extra mem₀ fp₀ count}
    (h : AccrueTailRefinesWithMemory fork v ee g s0 p imms locals evm stmts ret R spare mem fp extra)
    (ha : HeapAdvance mem₀ fp₀ mem fp count) :
    AccrueTailRefinesWithMemory fork v ee g s0 p imms locals evm stmts ret R spare mem₀ fp₀ (count + extra) := by
  cases h with
  | reverted he hr => exact .reverted he hr
  | static he hr => exact .static he hr
  | ok hp he hl hs hm hb hr =>
    exact .ok hp he hl hs hm (by simpa only [Nat.add_assoc] using ha.trans hb) hr

theorem morphoAccrueFinishTailWithMemory {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {rate interest ret fp : UInt256} {R : List UInt256} {spare : Nat}
    (p : MarketParamsWords) (locals imms : Store) (hstack : R.length + 40 ≤ 1024) (hp : ee.perm = true)
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem fp spare) (hb : 64 ≤ spare)
    (hl : AccrueLocals p locals rate interest ⟨0⟩) (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD fork (deployedRuntime v) ee g s0
      (if marketFieldWord σ ee p.id 5 = ⟨0⟩ then UInt256.ofNat 13706 else UInt256.ofNat 13738)
      ([wad, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, p.id,
        UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 0, marketFieldWord σ ee p.id 5] ++
        accrueMathTail p.id rate ret R) mem aw rdata σ k C) :
    AccrueTailRefinesWithMemory fork v ee g s0 p imms locals evm (accrueIrmBody.drop 10) ret R (spare - 64) mem fp 0 := by
  rcases morphoAccrueFinishRefineWithMemory p locals imms hstack hp hs hm hb hl hvalid h with hr | hok
  · exact .reverted hr.1 hr.2
  · obtain ⟨locals', evm', σ', mem', fp', aw', k', C', he, hl, hs, hm, ha, hr⟩ := hok
    exact .ok hp he hl hs hm (by simpa only [Nat.zero_add] using ha) hr

theorem morphoAccrueFinishTail {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {rate interest ret fp : UInt256} {R : List UInt256} {spare : Nat}
    (p : MarketParamsWords) (locals imms : Store) (hstack : R.length + 40 ≤ 1024) (hp : ee.perm = true)
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem fp spare) (hb : 64 ≤ spare)
    (hl : AccrueLocals p locals rate interest ⟨0⟩) (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD fork (deployedRuntime v) ee g s0
      (if marketFieldWord σ ee p.id 5 = ⟨0⟩ then UInt256.ofNat 13706 else UInt256.ofNat 13738)
      ([wad, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, p.id,
        UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 0, marketFieldWord σ ee p.id 5] ++
        accrueMathTail p.id rate ret R) mem aw rdata σ k C) :
    AccrueTailRefines fork v ee g s0 p imms locals evm (accrueIrmBody.drop 10) ret R (spare - 64) := by
  exact (morphoAccrueFinishTailWithMemory p locals imms hstack hp hs hm hb hl hvalid h).forget

end Benchmarks.Morpho.MorphoBlue
