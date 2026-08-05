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
