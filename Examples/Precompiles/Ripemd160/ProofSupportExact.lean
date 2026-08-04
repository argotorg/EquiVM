import Examples.Precompiles.Ripemd160.ProofSupport
import Reasoning.ReachExact

/-!
# Threshold-exact RIPEMD-160 proof support

Exact-gas counterparts of the contract-local symbolic-execution rules in
`Examples.Precompiles.Ripemd160.ProofSupport`.  The generic threshold machinery remains in
`Reasoning.ReachExact`; this file only connects it to opcodes whose one-step lemmas are local to
the RIPEMD-160 development.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Reach

open Reasoning.Theory

theorem RDx.dup12 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (h : RDx code ee g s0
      pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP12, .none)) (hov : t.length + 13 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩)
      (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup12_xstep hc hp hdec hs hov)

theorem RDx.dup16 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: pp :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP16, .none)) (hov : t.length + 17 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩)
      (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: pp :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup16_xstep hc hp hdec hs hov)

theorem RDx.push8 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH8, some (argv, 8)))
    (hov : stk.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + UInt256.ofNat 9) (argv :: stk)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.pushConst argv (by decide) hdec hov

theorem RDx.push3 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (h : RDx code ee g s0 pc stk mem aw rdata acc k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH3, some (argv, 3)))
    (hov : stk.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + UInt256.ofNat 4) (argv :: stk)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.pushConst argv (by decide) hdec hov

theorem RDx.byte {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.BYTE, .none)) (hov : t.length + 1 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) (UInt256.byteAt a b :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => byte_xstep hc hp hdec hs hov)

/-- `MSTORE8` with its exact dynamic memory-expansion cost. -/
theorem RDx.mstore8 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256} (mcost : ℕ) (memout : ByteArray) (awout : UInt256)
    (h : RDx code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MSTORE8, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: t →
        memoryExpansionCost s .MSTORE8 = mcost)
    (hmemout : (⟨#[UInt8.ofNat b.toNat]⟩ : ByteArray).write 0 mem a.toNat 1 = memout)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat 1) = awout)
    (hov : t.length ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) t memout awout rdata acc
      (k + 1) (C + (mcost + 3)) := by
  apply RDx.step (cost := mcost + 3) (fun s => stMStore8 s a b t) h (by omega)
  · intro s hm
    have hs := mstore8_xstep hm.1 hm.2.1 hdec hm.2.2.1 hov
    rw [hmc s hm.2.2.2.2.1 hm.2.2.1] at hs
    exact hs
  · intro s hm
    rcases hm with ⟨hcode, hpc, _hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stMStore8] using hcode
    · simp only [stMStore8, hpc]
    · simp only [stMStore8]; rw [hmem, hmemout]
    · simp only [stMStore8]; rw [haw, hawout]
    · simpa only [stMStore8] using hrdata
    · simpa only [stMStore8] using hacc
    · simpa only [stMStore8] using hee
    · simpa only [stMStore8] using hworld
  · intro s hm
    simp only [stMStore8]
    rw [hmc s hm.2.2.2.2.1 hm.2.2.1, Sat256.subNat_subNat]

/-- `MCOPY` with exact memory expansion and copy-word cost. -/
theorem RDx.mcopy {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256} (mcost : ℕ)
    (memout : ByteArray) (awout : UInt256)
    (h : RDx code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MCOPY, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: t → memoryExpansionCost s .MCOPY = mcost)
    (hmemout : mem.write b.toNat mem a.toNat c.toNat = memout)
    (hawout : UInt256.ofNat
      (MachineState.M aw.toNat (max a.toNat b.toNat) c.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩) t memout awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Gverylow +
        GasConstants.Gcopy * ((c.toNat + 31) / 32)))) := by
  let cost := mcost + (GasConstants.Gverylow +
    GasConstants.Gcopy * ((c.toNat + 31) / 32))
  apply RDx.step (cost := cost) (fun s => stMcopy s a b c t) h (by
    simp only [cost, GasConstants.Gverylow]
    omega)
  · intro s hm
    have hs := mcopy_xstep hm.1 hm.2.1 hdec hm.2.2.1 hov
    rw [hmc s hm.2.2.2.2.1 hm.2.2.1, collapse_two_stage] at hs
    simpa only [cost] using hs
  · intro s hm
    rcases hm with ⟨hcode, hpc, _hstk, hmem, haw, hrdata, hacc, hee, hworld⟩
    refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [stMcopy] using hcode
    · simp only [stMcopy, hpc]
    · simp only [stMcopy]; rw [hmem, hmemout]
    · simp only [stMcopy]; rw [haw, hawout]
    · simpa only [stMcopy] using hrdata
    · simpa only [stMcopy] using hacc
    · simpa only [stMcopy] using hee
    · simpa only [stMcopy] using hworld
  · intro s hm
    simp only [stMcopy, cost]
    rw [hmc s hm.2.2.2.2.1 hm.2.2.1, Sat256.subNat_subNat]

theorem RDx.swap13 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn : UInt256} {t : List UInt256}
    (rd : RDx code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP13, .none)) (hov : t.length + 14 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩)
      (nn :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap13_xstep hc hp hdec hs hov)

theorem RDx.swap14 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn oo : UInt256} {t : List UInt256}
    (rd : RDx code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP14, .none)) (hov : t.length + 15 ≤ 1024) :
    RDx code ee g s0 (pc + ⟨1⟩)
      (oo :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap14_xstep hc hp hdec hs hov)

end Reasoning.Reach
