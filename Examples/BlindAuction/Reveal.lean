import Examples.BlindAuction.Storage
import Examples.BlindAuction.BiddingEnd
import Examples.BlindAuction.RevealEnd
import Reasoning.ExternalCall
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 800000

namespace Reasoning.Theory

-- PROMOTE -> Reasoning.Stepping: generic `DUP10` xstep, matching the existing `DUP2`-`DUP8`.
theorem blindAuctionDup10_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h i j : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP10, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: t)
    (hov : t.length + 11 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (j :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: t),
           .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP10, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup10 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: t).length - 10 + 11 >
          1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Reasoning.Stepping: generic `DUP11` xstep.
theorem blindAuctionDup11_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h i j k : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP11, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: t)
    (hov : t.length + 12 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s (k :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP11, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup11 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: t).length - 11 + 12 >
          1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Reasoning.Stepping: generic `SWAP5` xstep.
theorem blindAuctionSwap5_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP5, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: t)
    (hov : t.length + 6 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (f :: b :: c :: d :: e :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP5, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap5 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: t).length - 6 + 6 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Reasoning.Stepping: generic `SWAP6` xstep.
theorem blindAuctionSwap6_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f h : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP6, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: h :: t)
    (hov : t.length + 7 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (h :: b :: c :: d :: e :: f :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP6, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap6 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: h :: t).length - 7 + 7 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Reasoning.Stepping: generic `SWAP7` xstep.
theorem blindAuctionSwap7_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP7, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: t)
    (hov : t.length + 8 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (h :: b :: c :: d :: e :: f :: gg :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP7, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap7 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: t).length - 8 + 8 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Reasoning.Stepping: generic `SWAP8` xstep.
theorem blindAuctionSwap8_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h i : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP8, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: i :: t)
    (hov : t.length + 9 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (i :: b :: c :: d :: e :: f :: gg :: h :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP8, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap8 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: i :: t).length - 9 + 9 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Reasoning.Stepping: generic `SWAP10` xstep.
theorem blindAuctionSwap10_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h i j k : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP10, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: t)
    (hov : t.length + 11 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (k :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: a :: t),
           .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP10, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap10 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: t).length - 11 + 11 >
          1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Reasoning.Stepping: generic `SWAP11` xstep.
theorem blindAuctionSwap11_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg h i j k l : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP11, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: l :: t)
    (hov : t.length + 12 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s (l :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP11, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap11 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: k :: l :: t).length - 12 + 12 >
          1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

end Reasoning.Theory

namespace Reasoning.Reach

-- PROMOTE -> Reasoning.Reach: generic `RD.dup10`, matching the existing `RD.dup2`-`RD.dup8`.
theorem RD.dup10 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h i j : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: t) mem aw
      rdata acc k C)
    (hdec : decode code pc = some (.DUP10, .none)) (hov : t.length + 11 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (j :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => blindAuctionDup10_xstep hc hp hdec hs hov)

theorem RD.dup11 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h i j l : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP11, .none)) (hov : t.length + 12 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (l :: a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => blindAuctionDup11_xstep hc hp hdec hs hov)

theorem RD.swap5 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP5, .none)) (hov : t.length + 6 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (f :: b :: c :: d :: e :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => blindAuctionSwap5_xstep hc hp hdec hs hov)

theorem RD.swap6 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f h : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: h :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP6, .none)) (hov : t.length + 7 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (h :: b :: c :: d :: e :: f :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => blindAuctionSwap6_xstep hc hp hdec hs hov)

theorem RD.swap7 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: h :: t) mem aw rdata acc
      k C)
    (hdec : decode code pc = some (.SWAP7, .none)) (hov : t.length + 8 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (h :: b :: c :: d :: e :: f :: gg :: a :: t) mem aw
      rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => blindAuctionSwap7_xstep hc hp hdec hs hov)

theorem RD.swap8 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h i : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: h :: i :: t) mem aw
      rdata acc k C)
    (hdec : decode code pc = some (.SWAP8, .none)) (hov : t.length + 9 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (i :: b :: c :: d :: e :: f :: gg :: h :: a :: t) mem
      aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => blindAuctionSwap8_xstep hc hp hdec hs hov)

theorem RD.swap10 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h i j l : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP10, .none)) (hov : t.length + 11 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (l :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => blindAuctionSwap10_xstep hc hp hdec hs hov)

theorem RD.swap11 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg h i j l m : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: m :: t) mem aw rdata acc
      k C)
    (hdec : decode code pc = some (.SWAP11, .none)) (hov : t.length + 12 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (m :: b :: c :: d :: e :: f :: gg :: h :: i :: j :: l :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => blindAuctionSwap11_xstep hc hp hdec hs hov)

open BlindAuction

theorem RD.blindAuctionRevealDecodeEmptyArray1713 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {start ennd ret headOff : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1713⟩
        (start :: ennd :: ret :: headOff :: R) mem aw rdata acc k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨1⟩)
    (hlen : uInt256OfByteArray (ee.calldata.readBytes start.toNat 32) = ⟨0⟩)
    (hend : UInt256.gt (start + ⟨0⟩ + ⟨32⟩) ennd = ⟨0⟩)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ret
      (⟨0⟩ :: (start + ⟨32⟩) :: headOff :: R) mem aw rdata acc k' C' := by
  have rd1729 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt,
    push2 ⟨1729⟩, jumpiT (by rw [hstart]; decide) (by jump_dest)]
  have rd1733 := evm_run rd1729 with [jumpdest, pop, dup2, calldataload]
  have rd1742 := RD.pushConst rd1733 ⟨18446744073709551615⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1752 := evm_run rd1742 with [
    dup2, gt, iszero, push2 ⟨1752⟩, jumpiT (by rw [hlen]; decide) (by jump_dest)]
  obtain ⟨_, _, rd1752z⟩ : ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨1752⟩
      (⟨0⟩ :: ⟨0⟩ :: start :: ennd :: ret :: headOff :: R) mem aw rdata acc k' C' :=
    ⟨_, _, by simpa [hlen] using rd1752⟩
  have rd1778 := evm_run rd1752z with [
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop, dup4, push1 ⟨32⟩,
    dup3, push1 ⟨5⟩, shl, dup6, add, add, gt, iszero, push2 ⟨1778⟩,
    jumpiT
      (by
        rw [show UInt256.shiftLeft (⟨0⟩ : UInt256) ⟨5⟩ = ⟨0⟩ by decide]
        rw [hend]
        decide)
      (by jump_dest)]
  exact ⟨_, _, evm_run rd1778 with [
    jumpdest, swap3, pop, swap3, swap1, pop, jump hret]⟩

theorem RD.blindAuctionRevealDecodeArray1713 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {start ennd ret headOff len : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1713⟩
        (start :: ennd :: ret :: headOff :: R) mem aw rdata acc k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨1⟩)
    (hlen : uInt256OfByteArray (ee.calldata.readBytes start.toNat 32) = len)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hend : UInt256.gt ((start + UInt256.shiftLeft len ⟨5⟩) + ⟨32⟩) ennd = ⟨0⟩)
    (hret : (D_J blindAuctionBytecode 0).contains ret = true) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ret
      (len :: (start + ⟨32⟩) :: headOff :: R) mem aw rdata acc k' C' := by
  have rd1729 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt,
    push2 ⟨1729⟩, jumpiT (by rw [hstart]; decide) (by jump_dest)]
  have rd1733 := evm_run rd1729 with [jumpdest, pop, dup2, calldataload]
  have rd1742 := RD.pushConst rd1733 ⟨18446744073709551615⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1752 := evm_run rd1742 with [
    dup2, gt, iszero, push2 ⟨1752⟩, jumpiT
      (by
        rw [hlen, hlenMax]
        decide)
      (by jump_dest)]
  obtain ⟨_, _, rd1752z⟩ : ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨1752⟩
      (len :: ⟨0⟩ :: start :: ennd :: ret :: headOff :: R) mem aw rdata acc k' C' :=
    ⟨_, _, by simpa [hlen] using rd1752⟩
  have rd1778 := evm_run rd1752z with [
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop, dup4, push1 ⟨32⟩,
    dup3, push1 ⟨5⟩, shl, dup6, add, add, gt, iszero, push2 ⟨1778⟩,
    jumpiT
      (by
        rw [hend]
        decide)
      (by jump_dest)]
  exact ⟨_, _, evm_run rd1778 with [
    jumpdest, swap3, pop, swap3, swap1, pop, jump hret]⟩

theorem RD.blindAuctionRevealDecodeArray1713_startRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat}
    {start ennd ret headOff : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1713⟩
      (start :: ennd :: ret :: headOff :: R) mem aw rdata acc k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev blindAuctionBytecode g s0 := by
  have rd1728 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt,
    push2 ⟨1729⟩, jumpiNT
      (by exact hstart),
    push0, push0]
  exact RD.rev _ rd1728 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem RD.blindAuctionRevealDecodeArray1713_lengthRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat}
    {start ennd ret headOff len : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1713⟩
      (start :: ennd :: ret :: headOff :: R) mem aw rdata acc k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨1⟩)
    (hlen : uInt256OfByteArray (ee.calldata.readBytes start.toNat 32) = len)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨1⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev blindAuctionBytecode g s0 := by
  have rd1729 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt,
    push2 ⟨1729⟩, jumpiT
      (by
        rw [hstart]
        decide)
      (by jump_dest)]
  have rd1733 := evm_run rd1729 with [jumpdest, pop, dup2, calldataload]
  have rd1742 := RD.pushConst rd1733 ⟨18446744073709551615⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1751 := evm_run rd1742 with [
    dup2, gt, iszero, push2 ⟨1752⟩, jumpiNT
      (by
        rw [hlen, hlenMax]
        decide),
    push0, push0]
  exact RD.rev _ rd1751 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem RD.blindAuctionRevealDecodeArray1713_endRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat}
    {start ennd ret headOff len : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1713⟩
      (start :: ennd :: ret :: headOff :: R) mem aw rdata acc k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨1⟩)
    (hlen : uInt256OfByteArray (ee.calldata.readBytes start.toNat 32) = len)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hend : UInt256.gt ((start + UInt256.shiftLeft len ⟨5⟩) + ⟨32⟩) ennd = ⟨1⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev blindAuctionBytecode g s0 := by
  have rd1729 := evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt,
    push2 ⟨1729⟩, jumpiT
      (by
        rw [hstart]
        decide)
      (by jump_dest)]
  have rd1733 := evm_run rd1729 with [jumpdest, pop, dup2, calldataload]
  have rd1742 := RD.pushConst rd1733 ⟨18446744073709551615⟩ (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1752 := evm_run rd1742 with [
    dup2, gt, iszero, push2 ⟨1752⟩, jumpiT
      (by
        rw [hlen, hlenMax]
        decide)
      (by jump_dest)]
  obtain ⟨_, _, rd1752z⟩ : ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨1752⟩
      (len :: ⟨0⟩ :: start :: ennd :: ret :: headOff :: R) mem aw rdata acc k' C' :=
    ⟨_, _, by simpa [hlen] using rd1752⟩
  have rd1777 := evm_run rd1752z with [
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop, dup4, push1 ⟨32⟩,
    dup3, push1 ⟨5⟩, shl, dup6, add, add, gt, iszero, push2 ⟨1778⟩,
    jumpiNT
      (by
        rw [hend]
        decide),
    push0, push0]
  exact RD.rev _ rd1777 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

end Reasoning.Reach

namespace BlindAuction

/-! ## `reveal(uint256[],bool[],bytes32[])` outer body facts -/

abbrev revealMaxU64 : UInt256 := ⟨18446744073709551615⟩

abbrev revealValuesOffsetWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev revealFakesOffsetWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev revealSecretsOffsetWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

theorem blindAuctionRevealSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x90, 0x0f, 0x08, 0x0a]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x90, 0x0f, 0x08, 0x0a]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem blindAuctionDispatch_reveal {cd : ByteArray}
    (hsel : ((⟨#[0x90, 0x0f, 0x08, 0x0a]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg blindAuctionContract cd = some revealTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x90, 0x0f, 0x08, 0x0a]⟩ : ByteArray) :=
    (blindAuctionByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition])
    (post := [withdrawTransition, auctionEndTransition, beneficiaryGetter, biddingEndGetter,
      revealEndGetter, endedGetter, highestBidderGetter, highestBidGetter, bidsGetter])
    rfl ?_ (by rw [selectorOf, blindAuctionRevealSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  rw [selectorOf, blindAuctionBidSelectorBytes, hcd]
  decide

theorem blindAuctionX_reveal_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨387⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd387⟩ := hreach
  have rd395 := evm_run rd387 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨398⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd395.revertStub (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionX_reveal_decodeEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨387⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1785⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd387⟩ := hreach
  have rd1785 := evm_run rd387 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨398⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨276⟩, push2 ⟨413⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1785⟩, jump (by jump_dest)]
  exact ⟨_, _, rd1785⟩

theorem blindAuctionRevealX_decode_head_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩)
    (hentry : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1785⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1785⟩ := hentry
  exact evm_run rd1785 with [
    jumpdest, push0, push0, push0, push0, push0, push0, push1 ⟨96⟩,
    dup8, dup10, sub, slt, iszero, push2 ⟨1806⟩,
    jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem blindAuctionRevealX_decode_head_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩)
    (hentry : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1785⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1785⟩ := hentry
  have rd1806 := evm_run rd1785 with [
    jumpdest, push0, push0, push0, push0, push0, push0, push1 ⟨96⟩,
    dup8, dup10, sub, slt, iszero, push2 ⟨1806⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest) ]
  exact ⟨_, _, rd1806⟩

theorem blindAuctionRevealX_decode_valuesOffset_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hgt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨1⟩)
    (hhead : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1806⟩ := hhead
  have rd1809 := evm_run rd1806 with [jumpdest, dup7, calldataload]
  have rd1818 := RD.pushConst rd1809 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  exact evm_run rd1818 with [
    dup2, gt, iszero, push2 ⟨1828⟩, jumpiNT (by
      have hgt' :
          UInt256.gt
              (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
              revealMaxU64 = ⟨1⟩ := by
        simpa [revealValuesOffsetWord, calldataWord] using hgt
      rw [hgt']; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem blindAuctionRevealX_decode_valuesOffset_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hgt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hhead : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1828⟩
      [revealValuesOffsetWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1806⟩ := hhead
  have rd1809 := evm_run rd1806 with [jumpdest, dup7, calldataload]
  have rd1818 := RD.pushConst rd1809 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1828 := evm_run rd1818 with [
    dup2, gt, iszero, push2 ⟨1828⟩, jumpiT (by
      have hgt' :
          UInt256.gt
              (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
              revealMaxU64 = ⟨0⟩ := by
        simpa [revealValuesOffsetWord, calldataWord] using hgt
      rw [hgt']; decide) (by jump_dest) ]
  exact ⟨_, _, by simpa [revealValuesOffsetWord, calldataWord] using rd1828⟩

theorem blindAuctionRevealDecodeValuesCall1806_to_1713
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {sel : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord ee) revealMaxU64 = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨1713⟩
      [⟨4⟩ + revealValuesOffsetWord ee, UInt256.ofNat ee.calldata.size, ⟨1840⟩,
        revealValuesOffsetWord ee, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  have rd1809 := evm_run rd with [jumpdest, dup7, calldataload]
  have rd1818 := RD.pushConst rd1809 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1828 := evm_run rd1818 with [
    dup2, gt, iszero, push2 ⟨1828⟩, jumpiT
      (by
        have hgt' :
            UInt256.gt
                (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
                revealMaxU64 = ⟨0⟩ := by
          simpa [revealValuesOffsetWord, calldataWord] using hvaluesGt
        rw [hgt']
        decide)
      (by jump_dest)]
  have rd1829 := evm_run rd1828 with [jumpdest, push2 ⟨1840⟩]
  have rd1833 := RD.dup10 rd1829 (by decide) (by simp)
  have rd1834 := evm_run rd1833 with [dup3]
  have rd1835 := RD.dup11 rd1834 (by decide) (by simp)
  have rd1839 := evm_run rd1835 with [add, push2 ⟨1713⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [revealValuesOffsetWord, calldataWord] using rd1839⟩

theorem blindAuctionRevealDecodeEmptyArrays1806_to_413
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {sel : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord ee).toNat 32)
        = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord ee) + ⟨0⟩) + ⟨32⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord ee).toNat 32)
        = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord ee) + ⟨0⟩) + ⟨32⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord ee).toNat 32)
        = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨0⟩) + ⟨32⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨413⟩
      [⟨0⟩, (⟨4⟩ + revealSecretsOffsetWord ee) + ⟨32⟩,
        ⟨0⟩, (⟨4⟩ + revealFakesOffsetWord ee) + ⟨32⟩,
        ⟨0⟩, (⟨4⟩ + revealValuesOffsetWord ee) + ⟨32⟩, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd1713v⟩ := blindAuctionRevealDecodeValuesCall1806_to_1713 rd hvaluesGt
  obtain ⟨_, _, rd1840⟩ :=
    RD.blindAuctionRevealDecodeEmptyArray1713 rd1713v hvaluesStart hvaluesLen
      hvaluesEnd (by jump_dest) (by simp)
  have rd1841 := evm_run rd1840 with [jumpdest, swap1]
  have rd1843 := RD.swap8 rd1841 (by decide) (by simp)
  have rd1844 := evm_run rd1843 with [pop]
  have rd1845 := RD.swap6 rd1844 (by decide) (by simp)
  have rd1847 := evm_run rd1845 with [pop, pop]
  have rd1852 := evm_run rd1847 with [push1 ⟨32⟩, dup8, add, calldataload]
  have rd1861 := RD.pushConst rd1852 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1871 := evm_run rd1861 with [
    dup2, gt, iszero, push2 ⟨1871⟩, jumpiT
      (by
        have hgt' :
            UInt256.gt
                (uInt256OfByteArray
                  (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
                revealMaxU64 = ⟨0⟩ := by
          simpa [revealFakesOffsetWord, calldataWord] using hfakesGt
        rw [hgt']
        decide)
      (by jump_dest)]
  have rd1875 := evm_run rd1871 with [jumpdest, push2 ⟨1883⟩]
  have rd1876 := RD.dup10 rd1875 (by decide) (by simp)
  have rd1877 := evm_run rd1876 with [dup3]
  have rd1878 := RD.dup11 rd1877 (by decide) (by simp)
  have rd1882 := evm_run rd1878 with [add, push2 ⟨1713⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1883⟩ :=
    RD.blindAuctionRevealDecodeEmptyArray1713 rd1882 hfakesStart hfakesLen
      hfakesEnd (by jump_dest) (by simp)
  have rd1884 := evm_run rd1883 with [jumpdest, swap1]
  have rd1885 := RD.swap6 rd1884 (by decide) (by simp)
  have rd1886 := evm_run rd1885 with [pop, swap4, pop, pop]
  have rd1895 := evm_run rd1886 with [push1 ⟨64⟩, dup8, add, calldataload]
  have rd1904 := RD.pushConst rd1895 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1914 := evm_run rd1904 with [
    dup2, gt, iszero, push2 ⟨1914⟩, jumpiT
      (by
        have hgt' :
            UInt256.gt
                (uInt256OfByteArray
                  (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32))
                revealMaxU64 = ⟨0⟩ := by
          simpa [revealSecretsOffsetWord, calldataWord] using hsecretsGt
        rw [hgt']
        decide)
      (by jump_dest)]
  have rd1918 := evm_run rd1914 with [jumpdest, push2 ⟨1926⟩]
  have rd1919 := RD.dup10 rd1918 (by decide) (by simp)
  have rd1920 := evm_run rd1919 with [dup3]
  have rd1921 := RD.dup11 rd1920 (by decide) (by simp)
  have rd1925 := evm_run rd1921 with [add, push2 ⟨1713⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1926⟩ :=
    RD.blindAuctionRevealDecodeEmptyArray1713 rd1925 hsecretsStart hsecretsLen
      hsecretsEnd (by jump_dest) (by simp)
  have rd1927 := evm_run rd1926 with [jumpdest]
  have rd1928 := RD.swap8 rd1927 (by decide) (by simp)
  have rd1929 := RD.swap11 rd1928 (by decide) (by simp)
  have rd1930 := RD.swap7 rd1929 (by decide) (by simp)
  have rd1931 := RD.swap10 rd1930 (by decide) (by simp)
  have rd1932 := evm_run rd1931 with [pop]
  have rd1933 := RD.swap5 rd1932 (by decide) (by simp)
  have rd1934 := RD.swap8 rd1933 (by decide) (by simp)
  have rd1935 := evm_run rd1934 with [pop, swap3]
  have rd1937 := RD.swap6 rd1935 (by decide) (by simp)
  have rd1939 := evm_run rd1937 with [swap4]
  have rd1940 := RD.swap5 rd1939 (by decide) (by simp)
  have rd1943 := evm_run rd1940 with [swap3, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa using rd1943⟩

theorem blindAuctionRevealDecodeEmptyArrays1806_to_887
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {sel : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord ee).toNat 32)
        = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord ee) + ⟨0⟩) + ⟨32⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord ee).toNat 32)
        = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord ee) + ⟨0⟩) + ⟨32⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord ee).toNat 32)
        = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨0⟩) + ⟨32⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨887⟩
      [⟨0⟩, (⟨4⟩ + revealSecretsOffsetWord ee) + ⟨32⟩,
        ⟨0⟩, (⟨4⟩ + revealFakesOffsetWord ee) + ⟨32⟩,
        ⟨0⟩, (⟨4⟩ + revealValuesOffsetWord ee) + ⟨32⟩, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd413⟩ :=
    blindAuctionRevealDecodeEmptyArrays1806_to_413 rd hvaluesGt hvaluesStart hvaluesLen
      hvaluesEnd hfakesGt hfakesStart hfakesLen hfakesEnd hsecretsGt hsecretsStart
      hsecretsLen hsecretsEnd
  have rd887 := evm_run rd413 with [jumpdest, push2 ⟨887⟩, jump (by jump_dest)]
  exact ⟨_, _, rd887⟩

abbrev revealScratchTimestampWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

def revealScratchBiddingEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)

def revealScratchRevealEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)

def revealScratchBidsLengthSlot (I : ExecutionEnv) : UInt256 :=
  bidsBase (.address I.source)

def revealScratchBidsLengthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩)

theorem revealScratchBiddingEndWord_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (I : ExecutionEnv) :
    revealScratchBiddingEndWord σ I = revealScratchBiddingEndWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner ⟨1⟩ ⟨0⟩

theorem revealScratchRevealEndWord_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (I : ExecutionEnv) :
    revealScratchRevealEndWord σ I = revealScratchRevealEndWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner ⟨2⟩ ⟨0⟩

theorem revealScratchBidsLengthWord_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (I : ExecutionEnv) :
    revealScratchBidsLengthWord σ I = revealScratchBidsLengthWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (revealScratchBidsLengthSlot I) ⟨0⟩

abbrev revealScratchSenderWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev revealScratchEmptyDecodedStack
    (I : ExecutionEnv) (valuesEnd fakesEnd secretsEnd : UInt256) : List UInt256 :=
  [⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]

abbrev revealDecodedStack (I : ExecutionEnv)
    (valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256) : List UInt256 :=
  [secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩,
    blindAuctionSelWord I]

theorem blindAuctionRevealDecodeArrays1806_to_413
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {sel valuesLen fakesLen secretsLen : UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, sel]
      mem aw rdata acc k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord ee).toNat 32)
        = valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord ee) + UInt256.shiftLeft valuesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord ee).toNat 32)
        = fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord ee) + UInt256.shiftLeft fakesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord ee).toNat 32)
        = secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord ee) + UInt256.shiftLeft secretsLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨413⟩
      [secretsLen, (⟨4⟩ + revealSecretsOffsetWord ee) + ⟨32⟩,
        fakesLen, (⟨4⟩ + revealFakesOffsetWord ee) + ⟨32⟩,
        valuesLen, (⟨4⟩ + revealValuesOffsetWord ee) + ⟨32⟩, ⟨276⟩, sel]
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd1713v⟩ := blindAuctionRevealDecodeValuesCall1806_to_1713 rd hvaluesGt
  obtain ⟨_, _, rd1840⟩ :=
    RD.blindAuctionRevealDecodeArray1713 rd1713v hvaluesStart hvaluesLen
      (by simpa [revealMaxU64] using hvaluesLenMax) hvaluesEnd (by jump_dest) (by simp)
  have rd1841 := evm_run rd1840 with [jumpdest, swap1]
  have rd1843 := RD.swap8 rd1841 (by decide) (by simp)
  have rd1844 := evm_run rd1843 with [pop]
  have rd1845 := RD.swap6 rd1844 (by decide) (by simp)
  have rd1847 := evm_run rd1845 with [pop, pop]
  have rd1852 := evm_run rd1847 with [push1 ⟨32⟩, dup8, add, calldataload]
  have rd1861 := RD.pushConst rd1852 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1871 := evm_run rd1861 with [
    dup2, gt, iszero, push2 ⟨1871⟩, jumpiT
      (by
        have hgt' :
            UInt256.gt
                (uInt256OfByteArray
                  (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
                revealMaxU64 = ⟨0⟩ := by
          simpa [revealFakesOffsetWord, calldataWord] using hfakesGt
        rw [hgt']
        decide)
      (by jump_dest)]
  have rd1875 := evm_run rd1871 with [jumpdest, push2 ⟨1883⟩]
  have rd1876 := RD.dup10 rd1875 (by decide) (by simp)
  have rd1877 := evm_run rd1876 with [dup3]
  have rd1878 := RD.dup11 rd1877 (by decide) (by simp)
  have rd1882 := evm_run rd1878 with [add, push2 ⟨1713⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1883⟩ :=
    RD.blindAuctionRevealDecodeArray1713 rd1882 hfakesStart hfakesLen
      (by simpa [revealMaxU64] using hfakesLenMax) hfakesEnd (by jump_dest) (by simp)
  have rd1884 := evm_run rd1883 with [jumpdest, swap1]
  have rd1885 := RD.swap6 rd1884 (by decide) (by simp)
  have rd1886 := evm_run rd1885 with [pop, swap4, pop, pop]
  have rd1895 := evm_run rd1886 with [push1 ⟨64⟩, dup8, add, calldataload]
  have rd1904 := RD.pushConst rd1895 revealMaxU64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have rd1914 := evm_run rd1904 with [
    dup2, gt, iszero, push2 ⟨1914⟩, jumpiT
      (by
        have hgt' :
            UInt256.gt
                (uInt256OfByteArray
                  (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨64⟩).toNat 32))
                revealMaxU64 = ⟨0⟩ := by
          simpa [revealSecretsOffsetWord, calldataWord] using hsecretsGt
        rw [hgt']
        decide)
      (by jump_dest)]
  have rd1918 := evm_run rd1914 with [jumpdest, push2 ⟨1926⟩]
  have rd1919 := RD.dup10 rd1918 (by decide) (by simp)
  have rd1920 := evm_run rd1919 with [dup3]
  have rd1921 := RD.dup11 rd1920 (by decide) (by simp)
  have rd1925 := evm_run rd1921 with [add, push2 ⟨1713⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd1926⟩ :=
    RD.blindAuctionRevealDecodeArray1713 rd1925 hsecretsStart hsecretsLen
      (by simpa [revealMaxU64] using hsecretsLenMax) hsecretsEnd (by jump_dest) (by simp)
  have rd1927 := evm_run rd1926 with [jumpdest]
  have rd1928 := RD.swap8 rd1927 (by decide) (by simp)
  have rd1929 := RD.swap11 rd1928 (by decide) (by simp)
  have rd1930 := RD.swap7 rd1929 (by decide) (by simp)
  have rd1931 := RD.swap10 rd1930 (by decide) (by simp)
  have rd1932 := evm_run rd1931 with [pop]
  have rd1933 := RD.swap5 rd1932 (by decide) (by simp)
  have rd1934 := RD.swap8 rd1933 (by decide) (by simp)
  have rd1935 := evm_run rd1934 with [pop, swap3]
  have rd1937 := RD.swap6 rd1935 (by decide) (by simp)
  have rd1939 := evm_run rd1937 with [swap4]
  have rd1940 := RD.swap5 rd1939 (by decide) (by simp)
  have rd1943 := evm_run rd1940 with [swap3, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa [revealDecodedStack] using rd1943⟩

theorem blindAuctionRevealDecodeArrays1806_to_887
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {valuesLen fakesLen secretsLen : UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD blindAuctionBytecode ee g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat ee.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord ee]
      mem aw rdata acc k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord ee).toNat 32)
        = valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord ee) + UInt256.shiftLeft valuesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord ee).toNat 32)
        = fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord ee) + UInt256.shiftLeft fakesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord ee) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨31⟩)
        (UInt256.ofNat ee.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord ee).toNat 32)
        = secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord ee) + UInt256.shiftLeft secretsLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat ee.calldata.size) = ⟨0⟩) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨887⟩
      (revealDecodedStack ee valuesLen ((⟨4⟩ + revealValuesOffsetWord ee) + ⟨32⟩)
        fakesLen ((⟨4⟩ + revealFakesOffsetWord ee) + ⟨32⟩)
        secretsLen ((⟨4⟩ + revealSecretsOffsetWord ee) + ⟨32⟩))
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd413⟩ :=
    blindAuctionRevealDecodeArrays1806_to_413 rd hvaluesGt hvaluesStart hvaluesLen
      hvaluesLenMax hvaluesEnd hfakesGt hfakesStart hfakesLen hfakesLenMax hfakesEnd
      hsecretsGt hsecretsStart hsecretsLen hsecretsLenMax hsecretsEnd
  have rd887 := evm_run rd413 with [jumpdest, push2 ⟨887⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [revealDecodedStack] using rd887⟩

noncomputable def revealScratchBidsSourceMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.ofNat I.source.val)).write 0 solcFreePtrMem 0 32

noncomputable def revealScratchBidsHashMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 (revealScratchBidsSourceMem I) 32 32

theorem revealScratch_readWithPadding_zero (mem : ByteArray) (addr : ℕ) :
    mem.readWithPadding addr 0 = ByteArray.empty := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  by_cases h : addr ≥ mem.size
  · simp [h]
    exact zeroes_zero (n := (OfNat.ofNat 0 : USize)) (by rfl)
  · simp [h]
    exact zeroes_zero (n := (OfNat.ofNat 0 : USize)) (by rfl)

theorem revealScratch_write_len_zero (src base : ByteArray) (sa da : ℕ) :
    src.write sa base da 0 = base := by
  unfold ByteArray.write
  simp

theorem revealScratchBidsSourceMem_size (I : ExecutionEnv) :
    (revealScratchBidsSourceMem I).size = 96 := by
  unfold revealScratchBidsSourceMem
  rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  norm_num

theorem revealScratchBidsHashMem_size (I : ExecutionEnv) :
    (revealScratchBidsHashMem I).size = 96 := by
  unfold revealScratchBidsHashMem
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])
      (by rw [revealScratchBidsSourceMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, revealScratchBidsSourceMem_size,
    toByteArray_size]
  norm_num

theorem revealScratchBidsHashMem_read64 (I : ExecutionEnv) :
    (revealScratchBidsHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold revealScratchBidsHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [revealScratchBidsSourceMem_size]; norm_num) (by omega)
      (by rw [revealScratchBidsSourceMem_size])]
  unfold revealScratchBidsSourceMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; norm_num) (by omega)
      (by rw [solcFreePtrMem_size])]
  exact solcFreePtrMem_read64

theorem revealScratchBidsHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (revealScratchBidsHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((revealScratchBidsHashMem I).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [revealScratchBidsHashMem_size]; decide) (by decide)
    (revealScratchBidsHashMem_read64 I)

def revealScratchStTimestamp (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := UInt256.ofNat s.executionEnv.header.timestamp :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat 2 } }

theorem revealScratchTimestamp_xstep {s : State} {code : ByteArray} {pcv : UInt256}
    {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.TIMESTAMP, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
       else .ok (revealScratchStTimestamp s, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.TIMESTAMP, .none) := by
    rw [hcode, hpc]
    exact hdec
  have hov' : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by
    rw [hstk]
    omega
  rw [← hcode, step_timestamp s hd, if_neg hov']
  simp only [GasConstants.Gbase, revealScratchStTimestamp]

theorem RD.revealScratchTimestamp {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.TIMESTAMP, .none)) (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.ofNat ee.header.timestamp :: stk) mem aw rdata acc
      (k + 1) (C + 2) := by
  unfold RD at rd ⊢
  rcases rd with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee,
      hworld⟩
  · exact Or.inl hoog
  · have st := revealScratchTimestamp_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨revealScratchStTimestamp s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [revealScratchStTimestamp]
        exact hcode
      · simp only [revealScratchStTimestamp]
        rw [hpc]
      · simp only [revealScratchStTimestamp]
        rw [hstk, hee]
      · simp only [revealScratchStTimestamp]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [revealScratchStTimestamp]
        exact hmem
      · simp only [revealScratchStTimestamp]
        exact haw
      · simp only [revealScratchStTimestamp]
        exact hrdata
      · simp only [revealScratchStTimestamp]
        exact hacc
      · simp only [revealScratchStTimestamp]
        exact hee
      · simp only [revealScratchStTimestamp]
        exact hworld

theorem blindAuctionRevealX_from887_afterTimeGuards_empty {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesEnd fakesEnd secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealScratchEmptyDecodedStack I valuesEnd fakesEnd secretsEnd) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd890 := evm_run rd with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd891₀⟩ := rd890.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd891⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨891⟩
      [revealScratchBiddingEndWord σ I, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBiddingEndWord,
      revealScratchEmptyDecodedStack] using rd891₀⟩
  have hgt : UInt256.gt (revealScratchTimestampWord I) (revealScratchBiddingEndWord σ I) = ⟨1⟩ :=
    ugt_one hafter
  have rd893₀ := RD.revealScratchTimestamp (evm_run rd891 with [dup1]) (by decide) (by evm_ov)
  have rd894₀ := evm_run rd893₀ with [gt]
  have rd894 := rd894₀
  rw [show UInt256.gt (UInt256.ofNat I.header.timestamp) (revealScratchBiddingEndWord σ I) =
      ⟨1⟩ from by simpa [revealScratchTimestampWord] using hgt] at rd894
  have rd925 := evm_run rd894 with [push2 ⟨925⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd928 := evm_run rd925 with [jumpdest, push1 ⟨2⟩]
  obtain ⟨_, _, rd929₀⟩ := rd928.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd929⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨929⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchRevealEndWord] using rd929₀⟩
  have hlt : UInt256.lt (revealScratchTimestampWord I) (revealScratchRevealEndWord σ I) = ⟨1⟩ :=
    ult_one hbefore
  have rd931₀ := RD.revealScratchTimestamp (evm_run rd929 with [dup1]) (by decide) (by evm_ov)
  have rd932₀ := evm_run rd931₀ with [lt]
  have rd932 := rd932₀
  rw [show UInt256.lt (UInt256.ofNat I.header.timestamp) (revealScratchRevealEndWord σ I) =
      ⟨1⟩ from by simpa [revealScratchTimestampWord] using hlt] at rd932
  exact ⟨_, _, evm_run rd932 with [push2 ⟨963⟩, jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem blindAuctionRevealX_from887_lengthMismatch_empty {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesEnd fakesEnd secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealScratchEmptyDecodedStack I valuesEnd fakesEnd secretsEnd) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hbidsNonzero : revealScratchBidsLengthWord σ I ≠ ⟨0⟩)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd963⟩ :=
    blindAuctionRevealX_from887_afterTimeGuards_empty (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hafter hbefore
  have rd968 := evm_run rd963 with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [revealScratchBidsLengthWord σ I, revealScratchRevealEndWord σ I,
        revealScratchBiddingEndWord σ I, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩,
        valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBidsLengthWord,
      revealScratchBidsLengthSlot] using rd979₀⟩
  have heq0 : UInt256.eq (revealScratchBidsLengthWord σ I) (⟨0⟩ : UInt256) = ⟨0⟩ :=
    u256_eq_of_ne hbidsNonzero
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [heq0] at rd982
  have rd988 := evm_run rd982 with [push2 ⟨989⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd988 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionRevealX_from887_afterTimeGuards {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd890 := evm_run rd with [jumpdest, push1 ⟨1⟩]
  obtain ⟨_, _, rd891₀⟩ := rd890.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd891⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨891⟩
      [revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBiddingEndWord, revealDecodedStack] using rd891₀⟩
  have hgt : UInt256.gt (revealScratchTimestampWord I) (revealScratchBiddingEndWord σ I) = ⟨1⟩ :=
    ugt_one hafter
  have rd893₀ := RD.revealScratchTimestamp (evm_run rd891 with [dup1]) (by decide) (by evm_ov)
  have rd894₀ := evm_run rd893₀ with [gt]
  have rd894 := rd894₀
  rw [show UInt256.gt (UInt256.ofNat I.header.timestamp) (revealScratchBiddingEndWord σ I) =
      ⟨1⟩ from by simpa [revealScratchTimestampWord] using hgt] at rd894
  have rd925 := evm_run rd894 with [push2 ⟨925⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd928 := evm_run rd925 with [jumpdest, push1 ⟨2⟩]
  obtain ⟨_, _, rd929₀⟩ := rd928.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd929⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨929⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchRevealEndWord] using rd929₀⟩
  have hlt : UInt256.lt (revealScratchTimestampWord I) (revealScratchRevealEndWord σ I) = ⟨1⟩ :=
    ult_one hbefore
  have rd931₀ := RD.revealScratchTimestamp (evm_run rd929 with [dup1]) (by decide) (by evm_ov)
  have rd932₀ := evm_run rd931₀ with [lt]
  have rd932 := rd932₀
  rw [show UInt256.lt (UInt256.ofNat I.header.timestamp) (revealScratchRevealEndWord σ I) =
      ⟨1⟩ from by simpa [revealScratchTimestampWord] using hlt] at rd932
  exact ⟨_, _, evm_run rd932 with [push2 ⟨963⟩, jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem blindAuctionRevealX_from887_valuesLengthMismatch {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesNe : revealScratchBidsLengthWord σ I ≠ valuesLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd963⟩ :=
    blindAuctionRevealX_from887_afterTimeGuards (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hafter hbefore
  have rd968 := evm_run rd963 with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [revealScratchBidsLengthWord σ I, revealScratchRevealEndWord σ I,
        revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBidsLengthWord,
      revealScratchBidsLengthSlot] using rd979₀⟩
  have heq0 : UInt256.eq (revealScratchBidsLengthWord σ I) valuesLen = ⟨0⟩ :=
    u256_eq_of_ne hvaluesNe
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [heq0] at rd982
  have rd988 := evm_run rd982 with [push2 ⟨989⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd988 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionRevealX_from887_fakesLengthMismatch {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesNe : revealScratchBidsLengthWord σ I ≠ fakesLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd963⟩ :=
    blindAuctionRevealX_from887_afterTimeGuards (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hafter hbefore
  have rd968 := evm_run rd963 with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [revealScratchBidsLengthWord σ I, revealScratchRevealEndWord σ I,
        revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBidsLengthWord,
      revealScratchBidsLengthSlot] using rd979₀⟩
  have heqValues :
      UInt256.eq (revealScratchBidsLengthWord σ I) valuesLen = ⟨1⟩ := by
    rw [← hvaluesEq]
    exact u256_eq_refl _
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [heqValues] at rd982
  have rd989 := evm_run rd982 with [push2 ⟨989⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have heqFakes : UInt256.eq (revealScratchBidsLengthWord σ I) fakesLen = ⟨0⟩ :=
    u256_eq_of_ne hfakesNe
  have rd993₀ := evm_run rd989 with [jumpdest, dup6, dup2, eq]
  have rd993 := rd993₀
  rw [heqFakes] at rd993
  have rd999 := evm_run rd993 with [push2 ⟨1000⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd999 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionRevealX_from887_secretsLengthMismatch {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨887⟩
      (revealDecodedStack I valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesEq : revealScratchBidsLengthWord σ I = fakesLen)
    (hsecretsNe : revealScratchBidsLengthWord σ I ≠ secretsLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd963⟩ :=
    blindAuctionRevealX_from887_afterTimeGuards (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hafter hbefore
  have rd968 := evm_run rd963 with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [revealScratchBidsLengthWord σ I, revealScratchRevealEndWord σ I,
        revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBidsLengthWord,
      revealScratchBidsLengthSlot] using rd979₀⟩
  have heqValues :
      UInt256.eq (revealScratchBidsLengthWord σ I) valuesLen = ⟨1⟩ := by
    rw [← hvaluesEq]
    exact u256_eq_refl _
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [heqValues] at rd982
  have rd989 := evm_run rd982 with [push2 ⟨989⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have heqFakes :
      UInt256.eq (revealScratchBidsLengthWord σ I) fakesLen = ⟨1⟩ := by
    rw [← hfakesEq]
    exact u256_eq_refl _
  have rd993₀ := evm_run rd989 with [jumpdest, dup6, dup2, eq]
  have rd993 := rd993₀
  rw [heqFakes] at rd993
  have rd1000 := evm_run rd993 with [push2 ⟨1000⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have heqSecrets : UInt256.eq (revealScratchBidsLengthWord σ I) secretsLen = ⟨0⟩ :=
    u256_eq_of_ne hsecretsNe
  have rd1004₀ := evm_run rd1000 with [jumpdest, dup4, dup2, eq]
  have rd1004 := rd1004₀
  rw [heqSecrets] at rd1004
  have rd1010 := evm_run rd1004 with [push2 ⟨1011⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd1010 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionRevealDecodeArrays1806_valuesLengthMismatch_reverts
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State} {k C : Nat}
    {valuesLen fakesLen secretsLen : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord I).toNat 32)
        = valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord I) + UInt256.shiftLeft valuesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord I).toNat 32)
        = fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord I) + UInt256.shiftLeft fakesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord I).toNat 32)
        = secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord I) + UInt256.shiftLeft secretsLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesNe : revealScratchBidsLengthWord σ I ≠ valuesLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd887⟩ :=
    blindAuctionRevealDecodeArrays1806_to_887 (ee := I) rd hvaluesGt hvaluesStart
      hvaluesLen hvaluesLenMax hvaluesEnd hfakesGt hfakesStart hfakesLen hfakesLenMax
      hfakesEnd hsecretsGt hsecretsStart hsecretsLen hsecretsLenMax hsecretsEnd
  exact blindAuctionRevealX_from887_valuesLengthMismatch (cA := cA) (σ := σ) (I := I)
    (g := g) (s0 := s0) rd887 hafter hbefore hvaluesNe hbidsHash

theorem blindAuctionRevealDecodeArrays1806_fakesLengthMismatch_reverts
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State} {k C : Nat}
    {valuesLen fakesLen secretsLen : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord I).toNat 32)
        = valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord I) + UInt256.shiftLeft valuesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord I).toNat 32)
        = fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord I) + UInt256.shiftLeft fakesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord I).toNat 32)
        = secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord I) + UInt256.shiftLeft secretsLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesNe : revealScratchBidsLengthWord σ I ≠ fakesLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd887⟩ :=
    blindAuctionRevealDecodeArrays1806_to_887 (ee := I) rd hvaluesGt hvaluesStart
      hvaluesLen hvaluesLenMax hvaluesEnd hfakesGt hfakesStart hfakesLen hfakesLenMax
      hfakesEnd hsecretsGt hsecretsStart hsecretsLen hsecretsLenMax hsecretsEnd
  exact blindAuctionRevealX_from887_fakesLengthMismatch (cA := cA) (σ := σ) (I := I)
    (g := g) (s0 := s0) rd887 hafter hbefore hvaluesEq hfakesNe hbidsHash

theorem blindAuctionRevealDecodeArrays1806_secretsLengthMismatch_reverts
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {I : ExecutionEnv}
    {g : Sat256}
    {s0 : State} {k C : Nat}
    {valuesLen fakesLen secretsLen : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1806⟩
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨413⟩, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hvaluesGt : UInt256.gt (revealValuesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hvaluesStart :
      UInt256.slt ((⟨4⟩ + revealValuesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hvaluesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealValuesOffsetWord I).toNat 32)
        = valuesLen)
    (hvaluesLenMax : UInt256.gt valuesLen revealMaxU64 = ⟨0⟩)
    (hvaluesEnd :
      UInt256.gt (((⟨4⟩ + revealValuesOffsetWord I) + UInt256.shiftLeft valuesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hfakesGt : UInt256.gt (revealFakesOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hfakesStart :
      UInt256.slt ((⟨4⟩ + revealFakesOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hfakesLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealFakesOffsetWord I).toNat 32)
        = fakesLen)
    (hfakesLenMax : UInt256.gt fakesLen revealMaxU64 = ⟨0⟩)
    (hfakesEnd :
      UInt256.gt (((⟨4⟩ + revealFakesOffsetWord I) + UInt256.shiftLeft fakesLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hsecretsGt : UInt256.gt (revealSecretsOffsetWord I) revealMaxU64 = ⟨0⟩)
    (hsecretsStart :
      UInt256.slt ((⟨4⟩ + revealSecretsOffsetWord I) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hsecretsLen :
      uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + revealSecretsOffsetWord I).toNat 32)
        = secretsLen)
    (hsecretsLenMax : UInt256.gt secretsLen revealMaxU64 = ⟨0⟩)
    (hsecretsEnd :
      UInt256.gt (((⟨4⟩ + revealSecretsOffsetWord I) + UInt256.shiftLeft secretsLen ⟨5⟩)
        + ⟨32⟩) (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hafter :
      (revealScratchBiddingEndWord σ I).toNat < (revealScratchTimestampWord I).toNat)
    (hbefore :
      (revealScratchTimestampWord I).toNat < (revealScratchRevealEndWord σ I).toNat)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesEq : revealScratchBidsLengthWord σ I = fakesLen)
    (hsecretsNe : revealScratchBidsLengthWord σ I ≠ secretsLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd887⟩ :=
    blindAuctionRevealDecodeArrays1806_to_887 (ee := I) rd hvaluesGt hvaluesStart
      hvaluesLen hvaluesLenMax hvaluesEnd hfakesGt hfakesStart hfakesLen hfakesLenMax
      hfakesEnd hsecretsGt hsecretsStart hsecretsLen hsecretsLenMax hsecretsEnd
  exact blindAuctionRevealX_from887_secretsLengthMismatch (cA := cA) (σ := σ) (I := I)
    (g := g) (s0 := s0) rd887 hafter hbefore hvaluesEq hfakesEq hsecretsNe hbidsHash

theorem blindAuctionRevealX_from963_lengthsOk_toLoopInit {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesEq : revealScratchBidsLengthWord σ I = fakesLen)
    (hsecretsEq : revealScratchBidsLengthWord σ I = secretsLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
      [⟨0⟩, ⟨0⟩, revealScratchBidsLengthWord σ I,
        revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd968 := evm_run rd with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [revealScratchBidsLengthWord σ I, revealScratchRevealEndWord σ I,
        revealScratchBiddingEndWord σ I, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [revealScratchBidsLengthWord,
      revealScratchBidsLengthSlot] using rd979₀⟩
  have heqValues :
      UInt256.eq (revealScratchBidsLengthWord σ I) valuesLen = ⟨1⟩ := by
    rw [← hvaluesEq]
    exact u256_eq_refl _
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [heqValues] at rd982
  have rd989 := evm_run rd982 with [push2 ⟨989⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have heqFakes :
      UInt256.eq (revealScratchBidsLengthWord σ I) fakesLen = ⟨1⟩ := by
    rw [← hfakesEq]
    exact u256_eq_refl _
  have rd993₀ := evm_run rd989 with [jumpdest, dup6, dup2, eq]
  have rd993 := rd993₀
  rw [heqFakes] at rd993
  have rd1000 := evm_run rd993 with [push2 ⟨1000⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have heqSecrets :
      UInt256.eq (revealScratchBidsLengthWord σ I) secretsLen = ⟨1⟩ := by
    rw [← hsecretsEq]
    exact u256_eq_refl _
  have rd1004₀ := evm_run rd1000 with [jumpdest, dup4, dup2, eq]
  have rd1004 := rd1004₀
  rw [heqSecrets] at rd1004
  have rd1011 := evm_run rd1004 with [push2 ⟨1011⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1014 := evm_run rd1011 with [jumpdest, push0, dup1]
  exact ⟨_, _, rd1014⟩

theorem blindAuctionRevealX_from963_lengthsOk_zero_toCall {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesLen valuesEnd fakesLen fakesEnd secretsLen secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbidsZero : revealScratchBidsLengthWord σ I = ⟨0⟩)
    (hvaluesEq : revealScratchBidsLengthWord σ I = valuesLen)
    (hfakesEq : revealScratchBidsLengthWord σ I = fakesLen)
    (hsecretsEq : revealScratchBidsLengthWord σ I = secretsLen)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ gasArg k' C', RD blindAuctionBytecode I g s0 ⟨1349⟩
      [gasArg, revealScratchSenderWord I, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, revealScratchSenderWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd1014⟩ :=
    blindAuctionRevealX_from963_lengthsOk_toLoopInit (cA := cA) (σ := σ) (I := I)
      (g := g) (s0 := s0) rd hvaluesEq hfakesEq hsecretsEq hbidsHash
  have hlt : UInt256.lt (⟨0⟩ : UInt256) (revealScratchBidsLengthWord σ I) = ⟨0⟩ := by
    rw [hbidsZero]
    decide
  have rd1019₀ := evm_run rd1014 with [jumpdest, dup3, dup2, lt, iszero]
  have rd1019 := rd1019₀
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1019
  have rd1331 := evm_run rd1019 with [push2 ⟨1331⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1348₀ := evm_run rd1331 with [
    jumpdest, pop, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (revealScratchBidsHashMem_mload64 I)
      (by decide) (by evm_ov),
    push0, swap1, caller, swap1, dup4, swap1, dup4, dup2, dup2, dup2, dup6, dup8]
  obtain ⟨gasArg, rd1349⟩ := rd1348₀.gas (by decide) (by evm_ov)
  exact ⟨gasArg, _, _, by
    simpa [revealScratchSenderWord, hbidsZero, hvaluesEq, hfakesEq, hsecretsEq] using rd1349⟩

set_option maxHeartbeats 1000000 in
theorem blindAuctionRevealX_from963_empty_toCall {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {valuesEnd fakesEnd secretsEnd : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩,
        blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbidsZero : revealScratchBidsLengthWord σ I = ⟨0⟩)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ gasArg k' C', RD blindAuctionBytecode I g s0 ⟨1349⟩
      [gasArg, revealScratchSenderWord I, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, revealScratchSenderWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I, ⟨0⟩,
        secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd968 := evm_run rd with [jumpdest, caller, push0, swap1, dup2]
  have rd969 := evm_run rd968 with [
    raw mstore 0 (revealScratchBidsSourceMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd978 := evm_run rd969 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (revealScratchBidsHashMem I) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (revealScratchBidsLengthSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hbidsHash (by decide) (by evm_ov)]
  obtain ⟨_, _, rd979₀⟩ := rd978.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd979⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨979⟩
      [⟨0⟩, revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I, ⟨0⟩,
        secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    have hpc979 :
        (⟨963⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
                    UInt256.ofNat 2 +
                  UInt256.ofNat 2 +
                ⟨1⟩ +
              UInt256.ofNat 2 +
            ⟨1⟩ +
          ⟨1⟩ +
        ⟨1⟩ : UInt256) = ⟨979⟩ := by
      native_decide
    have hload0 :
        Option.option (⟨0⟩ : UInt256)
          (fun ac => Batteries.RBMap.findD ac.storage (revealScratchBidsLengthSlot I) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner) = ⟨0⟩ := by
      simpa [revealScratchBidsLengthWord, revealScratchBidsLengthSlot] using hbidsZero
    exact ⟨_, _, by simpa [hpc979, hload0] using rd979₀⟩
  have rd982₀ := evm_run rd979 with [dup8, dup2, eq]
  have rd982 := rd982₀
  rw [show UInt256.eq (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd982
  have rd989 := evm_run rd982 with [push2 ⟨989⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd993₀ := evm_run rd989 with [jumpdest, dup6, dup2, eq]
  have rd993 := rd993₀
  rw [show UInt256.eq (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd993
  have rd1000 := evm_run rd993 with [push2 ⟨1000⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1004₀ := evm_run rd1000 with [jumpdest, dup4, dup2, eq]
  have rd1004 := rd1004₀
  rw [show UInt256.eq (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1004
  have rd1011 := evm_run rd1004 with [push2 ⟨1011⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1019₀ := evm_run rd1011 with [
    jumpdest, push0, dup1, jumpdest, dup3, dup2, lt, iszero]
  have rd1019 := rd1019₀
  rw [show UInt256.lt (⟨0⟩ : UInt256) (⟨0⟩ : UInt256) = ⟨0⟩ by decide,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd1019
  have rd1331 := evm_run rd1019 with [push2 ⟨1331⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd1348₀ := evm_run rd1331 with [
    jumpdest, pop, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (revealScratchBidsHashMem_mload64 I)
      (by decide) (by evm_ov),
    push0, swap1, caller, swap1, dup4, swap1, dup4, dup2, dup2, dup2, dup6, dup8]
  obtain ⟨gasArg, rd1349⟩ := rd1348₀.gas (by decide) (by evm_ov)
  exact ⟨gasArg, _, _, by simpa [revealScratchSenderWord] using rd1349⟩

theorem blindAuctionRevealX_from963_empty_callMade {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {valuesEnd fakesEnd secretsEnd : UInt256}
    (hdepth : I.depth.val < 1024)
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩,
        blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbidsZero : revealScratchBidsLengthWord σ I = ⟨0⟩)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
          (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
          (initState cA gh bl σ σ₀ g A I).blocks
          σ (initState cA gh bl σ σ₀ g A I).σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (revealScratchSenderWord I))
          (toExecute σ (AccountAddress.ofUInt256 (revealScratchSenderWord I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ByteArray.empty (I.depth + 1) I.header I.perm)
      ∧ o.size < UInt256.size
      ∧ RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
          [(if z then ⟨1⟩ else ⟨0⟩), ⟨128⟩, ⟨0⟩, revealScratchSenderWord I,
            ⟨0⟩, ⟨0⟩, ⟨0⟩, revealScratchRevealEndWord σ I,
            revealScratchBiddingEndWord σ I, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩,
            valuesEnd, ⟨276⟩, blindAuctionSelWord I]
          (revealScratchBidsHashMem I) (UInt256.ofNat 3) o (cA', σ') k' C' := by
  obtain ⟨gasArg, _, _, rd1349⟩ :=
    blindAuctionRevealX_from963_empty_toCall (cA := cA) (σ := σ) (I := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) rd hbidsZero hbidsHash
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd1350₀, hosz⟩ :=
    rd1349.call (by decide) hdepth (by evm_ov)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  have hcd : (revealScratchBidsHashMem I).readWithPadding
      (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat = ByteArray.empty := by
    exact revealScratch_readWithPadding_zero _ _
  have hΘ' : ∃ (g'' : UInt256) (A' : Substate),
      (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
        (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
        (initState cA gh bl σ σ₀ g A I).blocks
        σ (initState cA gh bl σ σ₀ g A I).σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
        (AccountAddress.ofUInt256 (revealScratchSenderWord I))
        (toExecute σ (AccountAddress.ofUInt256 (revealScratchSenderWord I)))
        callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
        ByteArray.empty (I.depth + 1) I.header I.perm := by
    rcases hΘ with ⟨g'', A', hΘeq⟩
    refine ⟨g'', A', ?_⟩
    rw [hcd] at hΘeq
    exact hΘeq
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      (UInt256.ofNat 3) := by
    decide
  rw [hmin, revealScratch_write_len_zero, haw] at rd1350₀
  exact ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ', hosz,
    by simpa [revealScratchSenderWord] using rd1350₀⟩

set_option maxHeartbeats 1000000 in
theorem blindAuctionRevealX_from963_empty_callDepth {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : ℕ} {valuesEnd fakesEnd secretsEnd : UInt256}
    (hdepth : I.depth = 1024)
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨963⟩
      [revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩,
        blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbidsZero : revealScratchBidsLengthWord σ I = ⟨0⟩)
    (hbidsHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((revealScratchBidsHashMem I).readWithPadding 0 64))) =
          revealScratchBidsLengthSlot I) :
    ∃ k' C', RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, revealScratchSenderWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        revealScratchRevealEndWord σ I, revealScratchBiddingEndWord σ I, ⟨0⟩,
        secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, blindAuctionSelWord I]
      (revealScratchBidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨gasArg, _, _, rd1349⟩ :=
    blindAuctionRevealX_from963_empty_toCall (cA := cA) (σ := σ) (I := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) rd hbidsZero hbidsHash
  obtain ⟨k', C', rd1350₀⟩ := rd1349.callDepthLimit (by decide) hdepth (by evm_ov)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 3).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      (UInt256.ofNat 3) := by
    decide
  rw [hmin, revealScratch_write_len_zero, haw] at rd1350₀
  exact ⟨k', C', by simpa [revealScratchSenderWord] using rd1350₀⟩

theorem blindAuctionRevealX_postCallEmpty_toRequire {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    {z senderWord revealEnd biddingEnd valuesEnd fakesEnd secretsEnd : UInt256}
    {sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
      [z, ⟨128⟩, ⟨0⟩, senderWord, ⟨0⟩, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1405⟩
      [z, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd, ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd,
        ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq, push2 ⟨1395⟩,
    jumpiT (by decide) (by jump_dest), jumpdest, push1 ⟨96⟩, swap2, pop,
    jumpdest, pop, pop, swap1, pop]⟩

theorem blindAuctionRevealX_postCallEmpty_success_stop {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    {senderWord revealEnd biddingEnd valuesEnd fakesEnd secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
      [⟨1⟩, ⟨128⟩, ⟨0⟩, senderWord, ⟨0⟩, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k C) :
    RDret blindAuctionBytecode g s0 acc ByteArray.empty := by
  obtain ⟨_, _, rd1405⟩ := blindAuctionRevealX_postCallEmpty_toRequire rd
  have rd1413 := evm_run rd1405 with [
    dup1, push2 ⟨1413⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  have rd276 := evm_run rd1413 with [
    jumpdest, pop, pop, pop, pop, pop, pop, pop, pop, pop, pop, pop,
    jump (by jump_dest), jumpdest]
  exact rd276.stop (by decide) (by evm_ov)

theorem blindAuctionRevealX_postCallEmpty_failure_revert {I} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    {senderWord revealEnd biddingEnd valuesEnd fakesEnd secretsEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, senderWord, ⟨0⟩, ⟨0⟩, ⟨0⟩, revealEnd, biddingEnd,
        ⟨0⟩, secretsEnd, ⟨0⟩, fakesEnd, ⟨0⟩, valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty acc k C) :
    RDrev blindAuctionBytecode g s0 := by
  obtain ⟨_, _, rd1405⟩ := blindAuctionRevealX_postCallEmpty_toRequire rd
  have rd1410 := evm_run rd1405 with [
    dup1, push2 ⟨1413⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd1410 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionRevealBodyReverts_nonpayable {evm : EVM.State} {locals : Store}
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals
      revealTransition.body .reverted := by
  dsimp [revealTransition]
  exact bodyReverts_nonPayable h

theorem blindAuctionRevealParamNames :
    revealTransition.params.map Param.name = ["values", "fakes", "secrets"] := rfl

theorem blindAuctionRevealParamTypes :
    (transitionSignature revealTransition).paramTypes =
      [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] := rfl

theorem decodeABIValues_reveal_heads_none_short (bytes : List UInt8) (hshort : bytes.length < 96) :
    decodeABIValues? [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32]
      bytes 0 0 96 96 = none := by
  rw [decodeABIValues?]
  simp only [isDynamicABIType, reduceIte, zero_add]
  cases hread : readNat? bytes 0 with
  | none => rfl
  | some off =>
      by_cases hofflt : off < 96
      · simp [hofflt]
      · have hreadOff : readNat? bytes off = none := by
          have hno : ¬ 32 ≤ bytes.length - off := by omega
          simp [readNat?, readWord?, readBytes?, hno]
        simp [hofflt, decodeABIValue?, hreadOff]

theorem blindAuctionDecode_reveal_none_short {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["values", "fakes", "secrets"]
    [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  simp only [List.isEmpty_cons]
  rw [if_neg]
  · simp only [decodeCalldata.decodeArgs]
    have hargsShort : (List.drop 4 I.calldata.toList).length < 96 := by
      rw [List.length_drop, htlen]
      omega
    simp only [abiTupleHeadSize?, isDynamicABIType, reduceIte, Option.bind, bind]
    rw [decodeABIValues_reveal_heads_none_short (List.drop 4 I.calldata.toList) hargsShort]
  · rintro ⟨_, hhuge⟩
    rw [List.length_drop, htlen] at hhuge
    omega

theorem blindAuctionDecode_reveal_none_huge {I : ExecutionEnv}
    (hhuge : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["values", "fakes", "secrets"]
    [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] I.calldata = none
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  simp only [List.isEmpty_cons]
  rw [if_pos]
  exact ⟨trivial, by rw [List.length_drop, htlen]; omega⟩

theorem decodeABIValue_dynamicArray_is_array {elemTy : ABIType} {bytes : List UInt8}
    {start : Nat} {v : Value} {endOffset : Nat}
    (h : decodeABIValue? (.dynamicArray elemTy) bytes start = some (v, endOffset)) :
    ∃ xs, v = .array xs := by
  unfold decodeABIValue? at h
  cases hsize : readNat? bytes start with
  | none => simp [hsize] at h
  | some size =>
      by_cases hmax : solcMaxU64 < size
      · simp [hsize, hmax] at h
      · by_cases hdyn : isDynamicABIType elemTy
        · simp [hsize, hmax, hdyn] at h
          cases helems : decodeABIArrayDynamicElems? elemTy size bytes (start + 32) with
          | none => simp [helems] at h
          | some p =>
              rcases p with ⟨xs, _⟩
              simp [helems] at h
              exact ⟨xs, h.1.symm⟩
        · simp [hsize, hmax, hdyn] at h
          cases hstatic : staticABIEncodedSize? elemTy with
          | none => simp [hstatic] at h
          | some elemSize =>
              simp [hstatic] at h
              cases helems : decodeABIArrayStaticElems? elemTy size elemSize bytes (start + 32) with
              | none => simp [helems] at h
              | some p =>
                  rcases p with ⟨xs, _⟩
                  simp [helems] at h
                  exact ⟨xs, h.1.symm⟩

theorem readBytes32_some_length {bytes : List UInt8} {off : Nat} {out : List UInt8}
    (h : readBytes? bytes off 32 = some out) : off + 32 ≤ bytes.length := by
  unfold readBytes? at h
  by_cases hle : 32 ≤ bytes.length - off
  · omega
  · simp [hle] at h

theorem readWord?_some_length {bytes : List UInt8} {off : Nat} {word : EVM.Word}
    (h : readWord? bytes off = some word) : off + 32 ≤ bytes.length := by
  unfold readWord? at h
  cases hbytes : readBytes? bytes off 32 with
  | none => simp [hbytes] at h
  | some _ => exact readBytes32_some_length hbytes

theorem readNat?_some_length {bytes : List UInt8} {off n : Nat}
    (h : readNat? bytes off = some n) : off + 32 ≤ bytes.length := by
  unfold readNat? readWord? at h
  cases hbytes : readBytes? bytes off 32 with
  | none => simp [hbytes] at h
  | some _ => exact readBytes32_some_length hbytes

theorem readNat?_some_bytesToWord {bytes : List UInt8} {off n : Nat}
    (h : readNat? bytes off = some n) :
    ABI.bytesToWord ((bytes.drop off).take 32) = UInt256.ofNat n := by
  unfold readNat? readWord? readBytes? at h
  by_cases hle : 32 ≤ bytes.length - off
  · simp [hle] at h
    cases h
    exact (u256_ofNat_toNat _).symm
  · simp [hle] at h

theorem decode_word_at_eq_any (cd : ByteArray) (off : ℕ) (hsz : off + 32 ≤ cd.size) :
    ABI.bytesToWord ((cd.toList.drop off).take 32) =
      uInt256OfByteArray (cd.readBytes off 32) := by
  by_cases hoff : off < 2 ^ 64
  · exact decode_word_at_eq cd off hsz hoff
  · rw [uInt256OfByteArray_eq]
    unfold ABI.bytesToWord fromByteArrayBigEndian
    congr 2
    rw [byteArray_toList_eq (cd.readBytes off 32)]
    unfold ByteArray.readBytes
    rw [if_neg]
    · simp only [ByteArray.toList_data_append, byteArray_zeroes_toList]
      have hreadSize : (ByteArray.mk (((cd.toList.drop off).take 32).toArray)).size = 32 := by
        show (((cd.toList.drop off).take 32).toArray).size = 32
        have hlen : ((cd.toList.drop off).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          rw [byteArray_toList_eq, Array.length_toList]
          have hds : cd.data.size = cd.size := rfl
          rw [hds]
          omega
        simp [hlen]
      rw [hreadSize]
      simp [byteArray_toList_eq]
    · simp
      exact Nat.le_of_not_gt hoff

theorem readNat?_calldataWord_eq {I : ExecutionEnv} {headOff off : Nat}
    (hread : readNat? (List.drop 4 I.calldata.toList) headOff = some off) :
    calldataWord I.calldata (4 + headOff) = UInt256.ofNat off := by
  have hreadLen := readNat?_some_length hread
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hsz : 4 + headOff + 32 ≤ I.calldata.size := by
    rw [List.length_drop, htlen] at hreadLen
    omega
  rw [calldataWord]
  rw [← decode_word_at_eq_any I.calldata (4 + headOff) hsz]
  have hword := readNat?_some_bytesToWord hread
  simpa [List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hword

theorem decodeABIValue_elem_end_le {elem : ElemType} {bytes : List UInt8}
    {start : Nat} {v : Value} {endOffset : Nat}
    (h : decodeABIValue? (.elem elem) bytes start = some (v, endOffset)) :
    endOffset = start + 32 ∧ start + 32 ≤ bytes.length := by
  cases elem <;> unfold decodeABIValue? at h
  case bool =>
    cases hread : readWord? bytes start with
    | none => simp [hread] at h
    | some word =>
        cases hdec : decodeABIWord? (.elem .bool) word with
        | none => simp [hread, hdec] at h
        | some value =>
            simp [hread, hdec] at h
            exact ⟨h.2.symm, readWord?_some_length hread⟩
  case address =>
    cases hread : readWord? bytes start with
    | none => simp [hread] at h
    | some word =>
        cases hdec : decodeABIWord? (.elem .address) word with
        | none => simp [hread, hdec] at h
        | some value =>
            simp [hread, hdec] at h
            exact ⟨h.2.symm, readWord?_some_length hread⟩
  case int it =>
    cases hread : readWord? bytes start with
    | none => simp [hread] at h
    | some word =>
        cases hdec : decodeABIWord? (.elem (.int it)) word with
        | none => simp [hread, hdec] at h
        | some value =>
            simp [hread, hdec] at h
            exact ⟨h.2.symm, readWord?_some_length hread⟩
  case fixed ft =>
    cases hread : readWord? bytes start with
    | none => simp [hread] at h
    | some word => simp [decodeABIWord?] at h
  case bytes n =>
    cases hread : readBytes? bytes start 32 with
    | none => simp [hread] at h
    | some wordBytes =>
        simp [hread] at h
        cases hzero : zeroPadding? wordBytes (n.val + 1) (31 - n.val) with
        | none => simp [hzero] at h
        | some u =>
            simp [hzero] at h
            exact ⟨h.2.symm, readBytes32_some_length hread⟩
  case function =>
    cases hread : readBytes? bytes start 32 with
    | none => simp [hread] at h
    | some wordBytes =>
        cases hzero : zeroPadding? wordBytes 24 8 with
        | none => simp [hread, hzero] at h
        | some u =>
            simp [hread, hzero] at h
            exact ⟨h.2.symm, readBytes32_some_length hread⟩

theorem decodeABIArrayStaticElems_elem32_facts {elem : ElemType} {n : Nat}
    {bytes : List UInt8} {start : Nat} {values : List Value} {endOffset : Nat}
    (hstart : start ≤ bytes.length)
    (h : decodeABIArrayStaticElems? (.elem elem) n 32 bytes start = some (values, endOffset)) :
    endOffset = start + 32 * n ∧ endOffset ≤ bytes.length ∧ values.length = n := by
  induction n generalizing start values endOffset with
  | zero =>
      simp [decodeABIArrayStaticElems?] at h
      rcases h with ⟨hvalues, hend⟩
      cases hvalues
      cases hend
      exact ⟨by omega, hstart, rfl⟩
  | succ n ih =>
      rw [decodeABIArrayStaticElems?] at h
      cases hval : decodeABIValue? (.elem elem) bytes start with
      | none => simp [hval] at h
      | some p =>
          rcases p with ⟨value, end0⟩
          obtain ⟨hend0, hend0le⟩ := decodeABIValue_elem_end_le hval
          simp [hval] at h
          cases hrest : decodeABIArrayStaticElems? (.elem elem) n 32 bytes end0 with
          | none => simp [hrest] at h
          | some q =>
              rcases q with ⟨valuesRest, restEnd⟩
              simp [hrest] at h
              rcases h with ⟨hend0', htail⟩
              rcases htail with ⟨hvalues, hend⟩
              cases hvalues
              cases hend
              obtain ⟨ihEq, ihLe, ihLen⟩ := ih (by omega) hrest
              exact ⟨by omega, ihLe, by simp [ihLen]⟩

theorem decodeABIValue_dynamicArray_elem32_facts {elem : ElemType}
    {bytes : List UInt8} {start : Nat} {values : List Value} {endOffset : Nat}
    (h : decodeABIValue? (.dynamicArray (.elem elem)) bytes start =
      some (.array values, endOffset)) :
    ∃ len, readNat? bytes start = some len ∧ ¬ solcMaxU64 < len ∧
      endOffset = start + 32 + 32 * len ∧ endOffset ≤ bytes.length ∧ values.length = len := by
  unfold decodeABIValue? at h
  cases hread : readNat? bytes start with
  | none => simp [hread] at h
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at h
      · simp [hread, hmax, staticABIEncodedSize?, isDynamicABIType] at h
        cases hstatic : decodeABIArrayStaticElems? (.elem elem) len 32 bytes (start + 32) with
        | none => simp [hstatic] at h
        | some p =>
            rcases p with ⟨values', end'⟩
            simp [hstatic] at h
            rcases h with ⟨hvalues, hendOffset⟩
            obtain ⟨hend, hle, hlen⟩ :=
              decodeABIArrayStaticElems_elem32_facts (readNat?_some_length hread) hstatic
            refine ⟨len, rfl, hmax, ?_, ?_, ?_⟩
            · rw [← hendOffset]
              exact hend
            · rwa [hendOffset] at hle
            · rwa [hvalues] at hlen

theorem uadd3_ofNat_toNat {a b c : Nat}
    (ha : a < UInt256.size) (hb : b < UInt256.size) (hc : c < UInt256.size)
    (hab : a + b < UInt256.size) (habc : a + b + c < UInt256.size) :
    ((UInt256.ofNat a + UInt256.ofNat b) + UInt256.ofNat c).toNat = a + b + c := by
  rw [uadd_toNat]
  have habWord : (UInt256.ofNat a + UInt256.ofNat b).toNat = a + b :=
    uadd_ofNat_toNat ha hb hab
  rw [habWord, ulit_toNat' c hc]
  exact Nat.mod_eq_of_lt habc

theorem shiftLeft5_ofNat_eq {n : Nat} (h : 32 * n < UInt256.size) :
    UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩ = UInt256.ofNat (32 * n) := by
  apply u256_inj
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨5⟩ : UInt256).val ≥ 256))]
  change (((UInt256.ofNat n).val.val <<< (⟨5⟩ : UInt256).val.val) % UInt256.size) =
    (UInt256.ofNat (32 * n)).val.val
  rw [show (⟨5⟩ : UInt256).val.val = 5 by decide]
  rw [show (UInt256.ofNat n).val.val = n by
    exact ulit_toNat' n (by
      have : n ≤ 32 * n := by omega
      exact lt_of_le_of_lt this h)]
  rw [show (UInt256.ofNat (32 * n)).val.val = 32 * n by exact ulit_toNat' (32 * n) h]
  rw [Nat.shiftLeft_eq, Nat.mul_comm]
  exact Nat.mod_eq_of_lt h

theorem revealArrayGuards_of_decode_elem32 {I : ExecutionEnv} {headOff off : Nat}
    {elem : ElemType} {values : List Value} {endOffset : Nat}
    (hcalldataSign : I.calldata.size < 2 ^ 255)
    (hreadHead : readNat? (List.drop 4 I.calldata.toList) headOff = some off)
    (hoffMax : ¬ solcMaxU64 < off)
    (hdecode : decodeABIValue? (.dynamicArray (.elem elem)) (List.drop 4 I.calldata.toList)
      off = some (.array values, endOffset)) :
    ∃ lenWord : UInt256,
      values.length = lenWord.toNat ∧
      UInt256.gt (calldataWord I.calldata (4 + headOff)) revealMaxU64 = ⟨0⟩ ∧
      UInt256.slt (((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩ ∧
      uInt256OfByteArray
          (I.calldata.readBytes
            (((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)).toNat) 32) =
        lenWord ∧
      UInt256.gt lenWord revealMaxU64 = ⟨0⟩ ∧
      UInt256.gt ((((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)) +
            UInt256.shiftLeft lenWord ⟨5⟩) + ⟨32⟩)
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
  obtain ⟨len, hreadLen, hlenMax, hendEq, hendLe, hvaluesLen⟩ :=
    decodeABIValue_dynamicArray_elem32_facts hdecode
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hargsLen : (List.drop 4 I.calldata.toList).length = I.calldata.size - 4 := by
    rw [List.length_drop, htlen]
  have hoffEnd : 4 + off + 32 + 32 * len ≤ I.calldata.size := by
    rw [hargsLen] at hendLe
    omega
  have hoffSmall : off < 2 ^ 64 := by
    unfold solcMaxU64 at hoffMax
    omega
  have hlenSmall : len < 2 ^ 64 := by
    unfold solcMaxU64 at hlenMax
    omega
  have h32lenSmall : 32 * len < UInt256.size := by
    have : 32 * len < 2 ^ 69 := by omega
    norm_num [UInt256.size]
    omega
  have hword : calldataWord I.calldata (4 + headOff) = UInt256.ofNat off :=
    readNat?_calldataWord_eq hreadHead
  have hstartToNat :
      (((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)).toNat) = 4 + off := by
    rw [hword]
    simpa using (uadd_ofNat_toNat (a := 4) (b := off) (by norm_num [UInt256.size])
      (lt_size_of_lt_sign (by omega : off < 2 ^ 255))
      (lt_size_of_lt_sign (by omega : 4 + off < 2 ^ 255)))
  have hlenWordEq :
      uInt256OfByteArray
          (I.calldata.readBytes
            (((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)).toNat) 32) =
        UInt256.ofNat len := by
    have hlenWord := readNat?_calldataWord_eq (I := I) (headOff := off) hreadLen
    rw [hstartToNat]
    simpa [calldataWord] using hlenWord
  refine ⟨UInt256.ofNat len, ?_, ?_, ?_, hlenWordEq, ?_, ?_⟩
  · rw [hvaluesLen]
    exact (ulit_toNat' len (lt_size_of_lt_sign (by omega : len < 2 ^ 255))).symm
  · rw [hword]
    apply ugt_zero
    rw [ulit_toNat' off (lt_size_of_lt_sign (by omega : off < 2 ^ 255))]
    rw [show revealMaxU64.toNat = solcMaxU64 by native_decide]
    unfold solcMaxU64 at hoffMax ⊢
    omega
  · have hstart31ToNat :
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)) + ⟨31⟩).toNat) =
          4 + off + 31 := by
      rw [hword]
      simpa using (uadd3_ofNat_toNat (a := 4) (b := off) (c := 31)
        (by norm_num [UInt256.size])
        (lt_size_of_lt_sign (by omega : off < 2 ^ 255))
        (by norm_num [UInt256.size])
        (lt_size_of_lt_sign (by omega : 4 + off < 2 ^ 255))
        (lt_size_of_lt_sign (by omega : 4 + off + 31 < 2 ^ 255)))
    apply slt_lit_one_low (m := I.calldata.size)
    · exact hcalldataSign
    · rw [hstart31ToNat]
      omega
  · apply ugt_zero
    rw [ulit_toNat' len (lt_size_of_lt_sign (by omega : len < 2 ^ 255))]
    rw [show revealMaxU64.toNat = solcMaxU64 by native_decide]
    unfold solcMaxU64 at hlenMax ⊢
    omega
  · have hendToNat :
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata (4 + headOff)) +
              UInt256.shiftLeft (UInt256.ofNat len) ⟨5⟩) + ⟨32⟩).toNat) =
          4 + off + 32 * len + 32 := by
      rw [hword, shiftLeft5_ofNat_eq h32lenSmall]
      have h4off :
          ((UInt256.ofNat 4 + UInt256.ofNat off) + UInt256.ofNat (32 * len) +
              UInt256.ofNat 32).toNat = 4 + off + 32 * len + 32 := by
        rw [uadd_toNat]
        have hleft :
            ((UInt256.ofNat 4 + UInt256.ofNat off) + UInt256.ofNat (32 * len)).toNat =
              4 + off + 32 * len := by
          exact uadd3_ofNat_toNat
            (by norm_num [UInt256.size])
            (lt_size_of_lt_sign (by omega : off < 2 ^ 255))
            h32lenSmall
            (lt_size_of_lt_sign (by omega : 4 + off < 2 ^ 255))
            (lt_size_of_lt_sign (by omega : 4 + off + 32 * len < 2 ^ 255))
        rw [hleft, ulit_toNat' 32 (by norm_num [UInt256.size])]
        exact Nat.mod_eq_of_lt
          (lt_size_of_lt_sign (by omega : 4 + off + 32 * len + 32 < 2 ^ 255))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h4off
    apply ugt_zero
    rw [hendToNat]
    rw [ulit_toNat' I.calldata.size (lt_size_of_lt_sign hcalldataSign)]
    omega

theorem blindAuctionDecode_reveal_callargs_shape {I : ExecutionEnv} {callargs : Store}
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs) :
    ∃ values fakes secrets : List Value,
      callargs.get? "values" = some (.array values) ∧
      callargs.get? "fakes" = some (.array fakes) ∧
      callargs.get? "secrets" = some (.array secrets) := by
  change decodeCalldata ["values", "fakes", "secrets"]
    [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] I.calldata =
      some callargs at hdec
  unfold decodeCalldata at hdec
  simp only [List.isEmpty_cons] at hdec
  split at hdec
  · contradiction
  next _ =>
    split at hdec
    · contradiction
    next _ =>
      simp [decodeCalldata.decodeArgs, decodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
        Option.bind, bind] at hdec
      cases h0 : readNat? (List.drop 4 I.calldata.toList) 0 with
      | none => simp [h0] at hdec
      | some off0 =>
          by_cases hmax0 : solcMaxU64 < off0
          · simp [h0, hmax0] at hdec
          · by_cases hoff0 : off0 < 96
            · simp [h0, hmax0, hoff0] at hdec
            ·
              simp [h0, hmax0, hoff0] at hdec
              cases hval0 : decodeABIValue? (.dynamicArray uint256)
                  (List.drop 4 I.calldata.toList) off0 with
              | none => simp [hval0] at hdec
              | some p0 =>
                  rcases p0 with ⟨v0, _⟩
                  rcases decodeABIValue_dynamicArray_is_array hval0 with ⟨values, rfl⟩
                  simp [hval0] at hdec
                  cases h1 : readNat? (List.drop 4 I.calldata.toList) 32 with
                  | none => simp [h1] at hdec
                  | some off1 =>
                      by_cases hmax1 : solcMaxU64 < off1
                      · simp [h1, hmax1] at hdec
                      · by_cases hoff1 : off1 < 96
                        · simp [h1, hmax1, hoff1] at hdec
                        ·
                          simp [h1, hmax1, hoff1] at hdec
                          cases hval1 : decodeABIValue? (.dynamicArray boolTy)
                              (List.drop 4 I.calldata.toList) off1 with
                          | none => simp [hval1] at hdec
                          | some p1 =>
                              rcases p1 with ⟨v1, _⟩
                              rcases decodeABIValue_dynamicArray_is_array hval1 with ⟨fakes, rfl⟩
                              simp [hval1] at hdec
                              cases h2 : readNat? (List.drop 4 I.calldata.toList) 64 with
                              | none => simp [h2] at hdec
                              | some off2 =>
                                  by_cases hmax2 : solcMaxU64 < off2
                                  · simp [h2, hmax2] at hdec
                                  · by_cases hoff2 : off2 < 96
                                    · simp [h2, hmax2, hoff2] at hdec
                                    ·
                                      simp [h2, hmax2, hoff2] at hdec
                                      cases hval2 : decodeABIValue? (.dynamicArray bytes32)
                                          (List.drop 4 I.calldata.toList) off2 with
                                      | none => simp [hval2] at hdec
                                      | some p2 =>
                                          rcases p2 with ⟨v2, _⟩
                                          rcases decodeABIValue_dynamicArray_is_array hval2 with
                                            ⟨secrets, rfl⟩
                                          simp [hval2] at hdec
                                          simp [decodeCalldata.insertValues] at hdec
                                          cases hdec
                                          refine ⟨values, fakes, secrets, ?_, ?_, ?_⟩
                                          · rw [store_get_ne, store_get_ne, store_get_self]
                                            · decide
                                            · decide
                                          · rw [store_get_ne, store_get_self]
                                            decide
                                          · rw [store_get_self]

theorem blindAuctionDecode_reveal_callargs_store_shape {I : ExecutionEnv} {callargs : Store}
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs) :
    ∃ values fakes secrets : List Value,
      callargs =
        (((∅ : Store).insert "values" (.array values)).insert "fakes" (.array fakes)).insert
          "secrets" (.array secrets) := by
  change decodeCalldata ["values", "fakes", "secrets"]
    [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] I.calldata =
      some callargs at hdec
  unfold decodeCalldata at hdec
  simp only [List.isEmpty_cons] at hdec
  split at hdec
  · contradiction
  next _ =>
    split at hdec
    · contradiction
    next _ =>
      simp [decodeCalldata.decodeArgs, decodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
        Option.bind, bind] at hdec
      cases h0 : readNat? (List.drop 4 I.calldata.toList) 0 with
      | none => simp [h0] at hdec
      | some off0 =>
          by_cases hmax0 : solcMaxU64 < off0
          · simp [h0, hmax0] at hdec
          · by_cases hoff0 : off0 < 96
            · simp [h0, hmax0, hoff0] at hdec
            ·
              simp [h0, hmax0, hoff0] at hdec
              cases hval0 : decodeABIValue? (.dynamicArray uint256)
                  (List.drop 4 I.calldata.toList) off0 with
              | none => simp [hval0] at hdec
              | some p0 =>
                  rcases p0 with ⟨v0, _⟩
                  rcases decodeABIValue_dynamicArray_is_array hval0 with ⟨values, rfl⟩
                  simp [hval0] at hdec
                  cases h1 : readNat? (List.drop 4 I.calldata.toList) 32 with
                  | none => simp [h1] at hdec
                  | some off1 =>
                      by_cases hmax1 : solcMaxU64 < off1
                      · simp [h1, hmax1] at hdec
                      · by_cases hoff1 : off1 < 96
                        · simp [h1, hmax1, hoff1] at hdec
                        ·
                          simp [h1, hmax1, hoff1] at hdec
                          cases hval1 : decodeABIValue? (.dynamicArray boolTy)
                              (List.drop 4 I.calldata.toList) off1 with
                          | none => simp [hval1] at hdec
                          | some p1 =>
                              rcases p1 with ⟨v1, _⟩
                              rcases decodeABIValue_dynamicArray_is_array hval1 with ⟨fakes, rfl⟩
                              simp [hval1] at hdec
                              cases h2 : readNat? (List.drop 4 I.calldata.toList) 64 with
                              | none => simp [h2] at hdec
                              | some off2 =>
                                  by_cases hmax2 : solcMaxU64 < off2
                                  · simp [h2, hmax2] at hdec
                                  · by_cases hoff2 : off2 < 96
                                    · simp [h2, hmax2, hoff2] at hdec
                                    ·
                                      simp [h2, hmax2, hoff2] at hdec
                                      cases hval2 : decodeABIValue? (.dynamicArray bytes32)
                                          (List.drop 4 I.calldata.toList) off2 with
                                      | none => simp [hval2] at hdec
                                      | some p2 =>
                                          rcases p2 with ⟨v2, _⟩
                                          rcases decodeABIValue_dynamicArray_is_array hval2 with
                                            ⟨secrets, rfl⟩
                                          simp [hval2] at hdec
                                          simp [decodeCalldata.insertValues] at hdec
                                          cases hdec
                                          exact ⟨values, fakes, secrets, rfl⟩

theorem blindAuctionDecode_reveal_callargs_absent {I : ExecutionEnv} {callargs : Store}
    {name : Ident}
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hvalues : ("values" == name) = false)
    (hfakes : ("fakes" == name) = false)
    (hsecrets : ("secrets" == name) = false) :
    callargs.get? name = none := by
  change decodeCalldata ["values", "fakes", "secrets"]
    [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32] I.calldata =
      some callargs at hdec
  unfold decodeCalldata at hdec
  simp only [List.isEmpty_cons] at hdec
  split at hdec
  · contradiction
  next _ =>
    split at hdec
    · contradiction
    next _ =>
      simp [decodeCalldata.decodeArgs, abiTupleHeadSize?, isDynamicABIType, Option.bind, bind]
        at hdec
      cases hvals : decodeABIValues?
          [.dynamicArray uint256, .dynamicArray boolTy, .dynamicArray bytes32]
          (List.drop 4 I.calldata.toList) 0 0 96 96 with
      | none => simp [hvals] at hdec
      | some p =>
          rcases p with ⟨vals, _⟩
          cases vals with
          | nil => simp [hvals, decodeCalldata.insertValues] at hdec
          | cons v0 vals =>
              cases vals with
              | nil => simp [hvals, decodeCalldata.insertValues] at hdec
              | cons v1 vals =>
                  cases vals with
                  | nil => simp [hvals, decodeCalldata.insertValues] at hdec
                  | cons v2 vals =>
                      cases vals with
                      | nil =>
                          simp [hvals, decodeCalldata.insertValues] at hdec
                          cases hdec
                          rw [store_get_ne, store_get_ne, store_get_ne]
                          · simp
                          · exact hvalues
                          · exact hfakes
                          · exact hsecrets
                      | cons v3 vals =>
                          simp [hvals, decodeCalldata.insertValues] at hdec

theorem blindAuctionRevealCallvalueRequire_ok {evm : EVM.State} {locals : Store}
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecStmt blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.require (.binary .eq (.env .callvalue) (.intLit 0)))
      (.ok { contract := blindAuctionContract, locals := locals } evm) := by
  exact ExecStmt.requireTrue (evalCallvalueEq_true h)

theorem blindAuctionRevealBody_of_zero_tail {evm : EVM.State} {locals : Store} {result}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (htail : ExecFuncBody blindAuctionConfig
      { contract := blindAuctionContract, locals := locals } evm
      (List.drop 1 revealTransition.body) result) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals
      revealTransition.body result := by
  dsimp [ExecTransitionBody, revealTransition] at htail ⊢
  have hreq := blindAuctionRevealCallvalueRequire_ok (locals := locals) h
  cases htail with
  | execBlockOK hblk => exact ExecFuncBody.execBlockOK (ExecBlock.consNormal hreq hblk)
  | execBlockRet hblk => exact ExecFuncBody.execBlockRet (ExecBlock.consNormal hreq hblk)
  | execBlockRevert hblk => exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal hreq hblk)
  | execBlockBreak hblk => exact ExecFuncBody.execBlockBreak (ExecBlock.consNormal hreq hblk)
  | execBlockContinue hblk => exact ExecFuncBody.execBlockContinue (ExecBlock.consNormal hreq hblk)

theorem evalExpr_reveal_biddingEnd (evm : EVM.State) (locals : Store)
    (hbase : locals.get? biddingEndRef.base = none) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.storage biddingEndRef) =
        .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)) := by
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := locals } evm biddingEndRef =
      .ok { base := "biddingEnd", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, biddingEndRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? blindAuctionContract.storage
      ({ base := "biddingEnd", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase) (her := her)
    (hty := hty) (hloc := blindAuctionConfig_storage_biddingEnd)]
  rw [blindAuctionBiddingEndStorageLocLoad_uint256]

theorem evalExpr_reveal_revealEnd (evm : EVM.State) (locals : Store)
    (hbase : locals.get? revealEndRef.base = none) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.storage revealEndRef) =
        .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)) := by
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := locals } evm revealEndRef =
      .ok { base := "revealEnd", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, revealEndRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? blindAuctionContract.storage
      ({ base := "revealEnd", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase) (her := her)
    (hty := hty) (hloc := blindAuctionConfig_storage_revealEnd)]
  rw [blindAuctionRevealEndStorageLocLoad_uint256]

theorem evalExpr_reveal_afterBiddingEnd_true (evm : EVM.State) (locals : Store)
    (hbase : locals.get? biddingEndRef.base = none)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .gt now (.storage biddingEndRef)) = .ok (.bool true) := by
  simp only [evalExpr?, now, envValue, evalExpr_reveal_biddingEnd evm locals hbase, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_reveal_afterBiddingEnd_false (evm : EVM.State) (locals : Store)
    (hbase : locals.get? biddingEndRef.base = none)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .gt now (.storage biddingEndRef)) = .ok (.bool false) := by
  simp only [evalExpr?, now, envValue, evalExpr_reveal_biddingEnd evm locals hbase, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_reveal_beforeRevealEnd_true (evm : EVM.State) (locals : Store)
    (hbase : locals.get? revealEndRef.base = none)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .lt now (.storage revealEndRef)) = .ok (.bool true) := by
  simp only [evalExpr?, now, envValue, evalExpr_reveal_revealEnd evm locals hbase, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_reveal_beforeRevealEnd_false (evm : EVM.State) (locals : Store)
    (hbase : locals.get? revealEndRef.base = none)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .lt now (.storage revealEndRef)) = .ok (.bool false) := by
  simp only [evalExpr?, now, envValue, evalExpr_reveal_revealEnd evm locals hbase, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem blindAuctionRevealBodyReverts_tooEarly {evm : EVM.State} {locals : Store}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbidding : locals.get? biddingEndRef.base = none)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [revealTransition]
  exact (ABlock.start
    |>.requireStep (evalCallvalueEq_true hwv)
    |>.requireRevert (evalExpr_reveal_afterBiddingEnd_false evm locals hbidding htime))

theorem blindAuctionRevealBodyReverts_tooLate {evm : EVM.State} {locals : Store}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbidding : locals.get? biddingEndRef.base = none)
    (hreveal : locals.get? revealEndRef.base = none)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  dsimp [revealTransition]
  exact (ABlock.start
    |>.requireStep (evalCallvalueEq_true hwv)
    |>.requireStep (evalExpr_reveal_afterBiddingEnd_true evm locals hbidding hafter)
    |>.requireRevert (evalExpr_reveal_beforeRevealEnd_false evm locals hreveal htime))

/-! ### Source-side base facts for an empty decoded reveal loop -/

def revealEmptyStore : Store :=
  (((∅ : Store).insert "values" (.array [])).insert "fakes" (.array [])).insert "secrets" (.array [])

theorem blindAuctionDecode_reveal_callargs_empty_eq {I : ExecutionEnv} {callargs : Store}
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hvalues : callargs.get? "values" = some (.array []))
    (hfakes : callargs.get? "fakes" = some (.array []))
    (hsecrets : callargs.get? "secrets" = some (.array [])) :
    callargs = revealEmptyStore := by
  obtain ⟨values, fakes, secrets, rfl⟩ :=
    blindAuctionDecode_reveal_callargs_store_shape hdec
  have hvaluesNil : values = [] := by
    rw [store_get_ne, store_get_ne, store_get_self] at hvalues
    · cases hvalues
      rfl
    · decide
    · decide
  have hfakesNil : fakes = [] := by
    rw [store_get_ne, store_get_self] at hfakes
    · cases hfakes
      rfl
    · decide
  have hsecretsNil : secrets = [] := by
    rw [store_get_self] at hsecrets
    cases hsecrets
    rfl
  simp [revealEmptyStore, hvaluesNil, hfakesNil, hsecretsNil]

def revealLengthStore : Store :=
  revealEmptyStore.insert "length" (.int 0)

def revealRefundStore (refund : UInt256) : Store :=
  revealLengthStore.insert "refund" (.int (Int.ofNat refund.toNat))

def revealLoopStore (refund i : UInt256) : Store :=
  (revealRefundStore refund).insert "i" (.int (Int.ofNat i.toNat))

def revealCallStore (refund i : UInt256) (success : Bool) (out : ByteArray) : Store :=
  (revealLoopStore refund i).insert "success" (.bool success) |>.insert "_data" (.bytes out)

theorem revealEmptyStore_values :
    revealEmptyStore.get? "values" = some (.array []) := by
  native_decide

theorem revealEmptyStore_fakes :
    revealEmptyStore.get? "fakes" = some (.array []) := by
  native_decide

theorem revealEmptyStore_secrets :
    revealEmptyStore.get? "secrets" = some (.array []) := by
  native_decide

theorem revealEmptyStore_bids_none :
    revealEmptyStore.get? "bids" = none := by
  native_decide

theorem evalExpr_reveal_empty_values_length (evm : EVM.State) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := revealEmptyStore } evm
      (.arrayLength .localVar { base := "values" }) = .ok (.int 0) := by
  rw [evalExpr?]
  rw [revealEmptyStore_values]
  simp [readLocalPath?, EvalResult.bind, bind, pure]

theorem evalExpr_reveal_empty_fakes_length (evm : EVM.State) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := revealEmptyStore } evm
      (.arrayLength .localVar { base := "fakes" }) = .ok (.int 0) := by
  rw [evalExpr?]
  rw [revealEmptyStore_fakes]
  simp [readLocalPath?, EvalResult.bind, bind, pure]

theorem evalExpr_reveal_empty_secrets_length (evm : EVM.State) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := revealEmptyStore } evm
      (.arrayLength .localVar { base := "secrets" }) = .ok (.int 0) := by
  rw [evalExpr?]
  rw [revealEmptyStore_secrets]
  simp [readLocalPath?, EvalResult.bind, bind, pure]

theorem evalExpr_reveal_local_empty_array_length (evm : EVM.State) (locals : Store)
    (name : Ident) (h : locals.get? name = some (.array [])) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.arrayLength .localVar { base := name }) = .ok (.int 0) := by
  rw [evalExpr?]
  rw [h]
  simp [readLocalPath?, EvalResult.bind, bind, pure]

theorem evalExpr_reveal_local_array_length (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (h : locals.get? name = some (.array xs)) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.arrayLength .localVar { base := name }) = .ok (.int xs.length) := by
  rw [evalExpr?]
  rw [h]
  simp [readLocalPath?, EvalResult.bind, bind, pure]

theorem evalExpr_reveal_var_value (evm : EVM.State) (locals : Store) (name : Ident) (v : Value)
    (h : locals.get? name = some v) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.var name) = .ok v := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable (locals.get? name) = .ok v
  rw [h]
  rfl

theorem evalExpr_reveal_var_int (evm : EVM.State) (locals : Store) (name : Ident) (n : Int)
    (h : locals.get? name = some (.int n)) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.var name) = .ok (.int n) := by
  exact evalExpr_reveal_var_value evm locals name (.int n) h

theorem evalExpr_reveal_local_empty_length_eq_zero_var (evm : EVM.State) (locals : Store)
    (name : Ident) (harr : locals.get? name = some (.array []))
    (hlen : locals.get? "length" = some (.int 0)) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .eq (.arrayLength .localVar { base := name }) (.var "length")) =
        .ok (.bool true) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_local_empty_array_length evm locals name harr,
    evalExpr_reveal_var_int evm locals "length" 0 hlen, EvalResult.bind, bind]
  rfl

theorem evalExpr_reveal_local_array_length_eq_var_false (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (len : UInt256)
    (harr : locals.get? name = some (.array xs))
    (hlen : locals.get? "length" = some (.int (Int.ofNat len.toNat)))
    (hne : xs.length ≠ len.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .eq (.arrayLength .localVar { base := name }) (.var "length")) =
        .ok (.bool false) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_local_array_length evm locals name xs harr,
    evalExpr_reveal_var_int evm locals "length" (Int.ofNat len.toNat) hlen,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  have hint : (Int.ofNat xs.length == Int.ofNat len.toNat) = false := by
    simp [beq_eq_false_iff_ne, hne]
  simpa [hint] using hne

theorem evalExpr_reveal_local_array_length_eq_var_true (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (len : UInt256)
    (harr : locals.get? name = some (.array xs))
    (hlen : locals.get? "length" = some (.int (Int.ofNat len.toNat)))
    (heq : xs.length = len.toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .eq (.arrayLength .localVar { base := name }) (.var "length")) =
        .ok (.bool true) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_local_array_length evm locals name xs harr,
    evalExpr_reveal_var_int evm locals "length" (Int.ofNat len.toNat) hlen,
    EvalResult.bind, bind]
  simp [evalBinaryOp?, heq]

theorem evalExpr_reveal_loop_cond_false (evm : EVM.State) (locals : Store)
    (hi : locals.get? "i" = some (.int 0))
    (hlen : locals.get? "length" = some (.int 0)) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.binary .lt (.var "i") (.var "length")) = .ok (.bool false) := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_int evm locals "i" 0 hi,
    evalExpr_reveal_var_int evm locals "length" 0 hlen, EvalResult.bind, bind]
  rfl

theorem evalExpr_reveal_local_array_index_any (evm : EVM.State) (locals : Store)
    (name : Ident) (xs : List Value) (idx : UInt256) (v : Value)
    (harr : locals.get? name = some (.array xs))
    (hi : locals.get? "i" = some (.int (Int.ofNat idx.toNat)))
    (hbound : idx.toNat < xs.length)
    (hlookup : lookupNth? xs idx.toNat = some v) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.index (.var name) (.var "i")) = .ok v := by
  rw [evalExpr?]
  simp only [evalExpr_reveal_var_value evm locals name (.array xs) harr,
    evalExpr_reveal_var_value evm locals "i" (.int (Int.ofNat idx.toNat)) hi,
    EvalResult.bind, bind]
  unfold evalIndex?
  simp only
  rw [if_pos]
  · simp [EvalResult.ofOption, hlookup]
  · constructor
    · exact Int.natCast_nonneg idx.toNat
    · simpa using hbound

theorem evalExpr_reveal_sender (evm : EVM.State) (locals : Store) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      sender = .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_reveal_refund (evm : EVM.State) (locals : Store) (refund : UInt256)
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat))) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.var "refund") = .ok (.int (Int.ofNat refund.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable (locals.get? "refund") =
    .ok (.int (Int.ofNat refund.toNat))
  rw [hrefund]
  rfl

theorem evalExpr_reveal_emptyBytes (evm : EVM.State) (locals : Store) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.newBytes (.intLit 0)) = .ok (.bytes ByteArray.empty) := by
  simp [evalExpr?, pure, bind, EvalResult.bind]
  rfl

theorem revealCallStore_success_get (refund i : UInt256) (success : Bool) (out : ByteArray) :
    (revealCallStore refund i success out).get? "success" = some (.bool success) := by
  unfold revealCallStore
  rw [store_get_ne]
  · exact store_get_self _ _ _
  · decide

theorem evalExpr_reveal_success (evm : EVM.State) (refund i : UInt256) (success : Bool)
    (out : ByteArray) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := revealCallStore refund i success out } evm
      (.var "success") = .ok (.bool success) := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable
    ((revealCallStore refund i success out).get? "success") = .ok (.bool success)
  rw [revealCallStore_success_get]
  rfl

theorem evalExpr_reveal_bids_length_zero (evm : EVM.State) (locals : Store)
    (hbids : locals.get? "bids" = none)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = ⟨0⟩) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.arrayLength .storage (bidsRef sender)) = .ok (.int 0) := by
  let er : EvaledStorageRef :=
    { base := "bids", steps := [.mindex (.address evm.executionEnv.source)] }
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := locals } evm (bidsRef sender) = .ok er := by
    simp [er, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsRef, sender,
      evalExpr?, envValue, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  have hty : storageTypeAt? blindAuctionContract.storage er = some (.dynamicArray bidStructTy) := by
    simp [er, storageTypeAt?, blindAuctionContract, storageDecls, storageTypeStep?, bidStructTy]
  have hres :
      resolveStorageRef? blindAuctionConfig
        { contract := blindAuctionContract, locals := locals } evm (bidsRef sender) =
        .ok (er, .dynamicArray bidStructTy) :=
    resolveStorageRef?_ok hbids her hty
  rw [evalExpr?]
  simp only [hres, bind, EvalResult.bind]
  change readStorageArrayLength? blindAuctionConfig evm er (.dynamicArray bidStructTy) =
    .ok (.int 0)
  simp only [readStorageArrayLength?, er, List.cons_append, List.nil_append]
  change (match some (blindAuctionUint256Loc (bidsBase (.address evm.executionEnv.source))) with
    | some lenLoc =>
        match storageLocLoad evm lenLoc with
        | Value.int n => pure (Value.int n)
        | _ => EvalResult.error .storageError
    | none => EvalResult.error .storageError) = EvalResult.ok (Value.int 0)
  change (match storageLocLoad evm (blindAuctionUint256Loc (bidsBase (.address evm.executionEnv.source))) with
    | Value.int n => pure (Value.int n)
    | _ => EvalResult.error .storageError) = EvalResult.ok (Value.int 0)
  rw [blindAuctionBiddingEndStorageLocLoad_uint256, hlen]
  rfl

theorem evalExpr_reveal_bids_length_any (evm : EVM.State) (locals : Store) (len : UInt256)
    (hbids : locals.get? "bids" = none)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
  let er : EvaledStorageRef :=
    { base := "bids", steps := [.mindex (.address evm.executionEnv.source)] }
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := locals } evm (bidsRef sender) = .ok er := by
    simp [er, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, bidsRef, sender,
      evalExpr?, envValue, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  have hty : storageTypeAt? blindAuctionContract.storage er = some (.dynamicArray bidStructTy) := by
    simp [er, storageTypeAt?, blindAuctionContract, storageDecls, storageTypeStep?, bidStructTy]
  have hres :
      resolveStorageRef? blindAuctionConfig
        { contract := blindAuctionContract, locals := locals } evm (bidsRef sender) =
        .ok (er, .dynamicArray bidStructTy) :=
    resolveStorageRef?_ok hbids her hty
  rw [evalExpr?]
  simp only [hres, bind, EvalResult.bind]
  change readStorageArrayLength? blindAuctionConfig evm er (.dynamicArray bidStructTy) =
    .ok (.int (Int.ofNat len.toNat))
  simp only [readStorageArrayLength?, er, List.cons_append, List.nil_append]
  change (match some (blindAuctionUint256Loc (bidsBase (.address evm.executionEnv.source))) with
    | some lenLoc =>
        match storageLocLoad evm lenLoc with
        | Value.int n => pure (Value.int n)
        | _ => EvalResult.error .storageError
    | none => EvalResult.error .storageError) = EvalResult.ok (Value.int (Int.ofNat len.toNat))
  change (match storageLocLoad evm (blindAuctionUint256Loc (bidsBase (.address evm.executionEnv.source))) with
    | Value.int n => pure (Value.int n)
    | _ => EvalResult.error .storageError) = EvalResult.ok (Value.int (Int.ofNat len.toNat))
  rw [blindAuctionBiddingEndStorageLocLoad_uint256, hlen]
  rfl

theorem blindAuctionRevealBodyReturns_empty_callSuccess
    (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = ⟨0⟩)
    (hcall :
      callViaEVM evm (EVM.address evm.executionEnv.source) 0 ByteArray.empty
        (true, evm', out)) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm revealEmptyStore
      revealTransition.body
      (.returned { contract := blindAuctionContract, locals := revealCallStore ⟨0⟩ ⟨0⟩ true out }
        evm' none) := by
  refine ExecFuncBody.execBlockOK ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_afterBiddingEnd_true evm revealEmptyStore (by native_decide) hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_beforeRevealEnd_true evm revealEmptyStore (by native_decide) hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := revealEmptyStore }
        evm (.arrayLength .storage (bidsRef sender)) = .ok (.int 0) := by
    exact evalExpr_reveal_bids_length_zero evm revealEmptyStore revealEmptyStore_bids_none hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := revealLengthStore } evm
    [ .require (.binary .eq (.arrayLength .localVar { base := "values" }) (.var "length")),
      .require (.binary .eq (.arrayLength .localVar { base := "fakes" }) (.var "length")),
      .require (.binary .eq (.arrayLength .localVar { base := "secrets" }) (.var "length")),
      .letDecl "refund" (some uint256) (.intLit 0),
      .for [ .letDecl "i" (some uint256) (.intLit 0) ]
        (.binary .lt (.var "i") (.var "length"))
        [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
        [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
          .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
          .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
          .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
          .ite
            (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
              (.keccak256 (.abiEncodePacked
                [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
            [.continue] [],
          .assign .localVar { base := "refund" }
            (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
          .ite
            (.binary .and (.unary .not (.var "fake"))
              (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
            [ .internalCall "placeBid" [sender, .var "value"] "ok",
              .ite (.var "ok")
                [ .assign .localVar { base := "refund" }
                    (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
          .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ],
      .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
      .require (.var "success") ]
    (.ok { contract := blindAuctionContract, locals := revealCallStore ⟨0⟩ ⟨0⟩ true out }
      evm')
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "values"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "fakes"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "secrets"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
    [ .for [ .letDecl "i" (some uint256) (.intLit 0) ]
        (.binary .lt (.var "i") (.var "length"))
        [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
        [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
          .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
          .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
          .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
          .ite
            (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
              (.keccak256 (.abiEncodePacked
                [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
            [.continue] [],
          .assign .localVar { base := "refund" }
            (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
          .ite
            (.binary .and (.unary .not (.var "fake"))
              (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
            [ .internalCall "placeBid" [sender, .var "value"] "ok",
              .ite (.var "ok")
                [ .assign .localVar { base := "refund" }
                    (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
          .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ],
      .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
      .require (.var "success") ]
    (.ok { contract := blindAuctionContract, locals := revealCallStore ⟨0⟩ ⟨0⟩ true out }
      evm')
  have hfor :
      ExecStmt blindAuctionConfig
        { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
        (.for [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.var "length"))
          [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
          [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
            .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
            .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
            .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
            .ite
              (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
                (.keccak256 (.abiEncodePacked
                  [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
              [.continue] [],
            .assign .localVar { base := "refund" }
              (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
            .ite
              (.binary .and (.unary .not (.var "fake"))
                (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
              [ .internalCall "placeBid" [sender, .var "value"] "ok",
                .ite (.var "ok")
                  [ .assign .localVar { base := "refund" }
                      (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
            .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ])
        (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
    have hinit :
        ExecBlock blindAuctionConfig
          { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
      refine ExecBlock.consNormal
        (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
      exact ExecBlock.nil
    have hloop :
        ExecForLoop blindAuctionConfig
          { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm
          (.binary .lt (.var "i") (.var "length"))
          [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
          [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
            .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
            .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
            .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
            .ite
              (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
                (.keccak256 (.abiEncodePacked
                  [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
              [.continue] [],
            .assign .localVar { base := "refund" }
              (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
            .ite
              (.binary .and (.unary .not (.var "fake"))
                (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
              [ .internalCall "placeBid" [sender, .var "value"] "ok",
                .ite (.var "ok")
                  [ .assign .localVar { base := "refund" }
                      (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
            .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
          (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
      exact ExecForLoop.falseDone
        (evalExpr_reveal_loop_cond_false evm (revealLoopStore ⟨0⟩ ⟨0⟩)
          (by native_decide) (by native_decide))
    exact ExecStmt.for hinit hloop
  refine ExecBlock.consNormal hfor ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallSuccess
      (evalExpr_reveal_sender evm (revealLoopStore ⟨0⟩ ⟨0⟩))
      (evalExpr_reveal_refund evm (revealLoopStore ⟨0⟩ ⟨0⟩) ⟨0⟩ (by native_decide))
      (evalExpr_reveal_emptyBytes evm (revealLoopStore ⟨0⟩ ⟨0⟩))
      hcall) ?_
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_reveal_success evm' ⟨0⟩ ⟨0⟩ true out))
    ExecBlock.nil

theorem blindAuctionRevealBodyReverts_empty_callFailure
    (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = ⟨0⟩)
    (hcall :
      callViaEVM evm (EVM.address evm.executionEnv.source) 0 ByteArray.empty
        (false, evm', out)) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm revealEmptyStore
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_afterBiddingEnd_true evm revealEmptyStore (by native_decide) hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_beforeRevealEnd_true evm revealEmptyStore (by native_decide) hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := revealEmptyStore }
        evm (.arrayLength .storage (bidsRef sender)) = .ok (.int 0) := by
    exact evalExpr_reveal_bids_length_zero evm revealEmptyStore revealEmptyStore_bids_none hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := revealLengthStore } evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "values"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "fakes"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_empty_length_eq_zero_var evm revealLengthStore "secrets"
        (by native_decide) (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
    (List.drop 8 revealTransition.body) .reverted
  have hfor :
      ExecStmt blindAuctionConfig
        { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
        (.for [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.binary .lt (.var "i") (.var "length"))
          [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
          [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
            .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
            .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
            .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
            .ite
              (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
                (.keccak256 (.abiEncodePacked
                  [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
              [.continue] [],
            .assign .localVar { base := "refund" }
              (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
            .ite
              (.binary .and (.unary .not (.var "fake"))
                (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
              [ .internalCall "placeBid" [sender, .var "value"] "ok",
                .ite (.var "ok")
                  [ .assign .localVar { base := "refund" }
                      (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
            .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ])
        (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
    have hinit :
        ExecBlock blindAuctionConfig
          { contract := blindAuctionContract, locals := revealRefundStore ⟨0⟩ } evm
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
      refine ExecBlock.consNormal
        (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
      exact ExecBlock.nil
    have hloop :
        ExecForLoop blindAuctionConfig
          { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm
          (.binary .lt (.var "i") (.var "length"))
          [ .assign .localVar { base := "i" } (.binary .add (.var "i") (.intLit 1)) ]
          [ .letStorage "bidToCheck" (bidElemRef sender (.var "i")),
            .letDecl "value" (some uint256) (.index (.var "values") (.var "i")),
            .letDecl "fake" (some boolTy) (.index (.var "fakes") (.var "i")),
            .letDecl "secret" (some bytes32) (.index (.var "secrets") (.var "i")),
            .ite
              (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
                (.keccak256 (.abiEncodePacked
                  [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
              [.continue] [],
            .assign .localVar { base := "refund" }
              (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
            .ite
              (.binary .and (.unary .not (.var "fake"))
                (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
              [ .internalCall "placeBid" [sender, .var "value"] "ok",
                .ite (.var "ok")
                  [ .assign .localVar { base := "refund" }
                      (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
            .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
          (.ok { contract := blindAuctionContract, locals := revealLoopStore ⟨0⟩ ⟨0⟩ } evm) := by
      exact ExecForLoop.falseDone
        (evalExpr_reveal_loop_cond_false evm (revealLoopStore ⟨0⟩ ⟨0⟩)
          (by native_decide) (by native_decide))
    exact ExecStmt.for hinit hloop
  refine ExecBlock.consNormal hfor ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalExpr_reveal_sender evm (revealLoopStore ⟨0⟩ ⟨0⟩))
      (evalExpr_reveal_refund evm (revealLoopStore ⟨0⟩ ⟨0⟩) ⟨0⟩ (by native_decide))
      (evalExpr_reveal_emptyBytes evm (revealLoopStore ⟨0⟩ ⟨0⟩))
      hcall) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_reveal_success evm' ⟨0⟩ ⟨0⟩ false out))

theorem blindAuctionRevealBodyReverts_valuesLengthMismatch (evm : EVM.State)
    (callargs : Store) (values : List Value) (len : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hne : values.length ≠ len.toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs }
        evm (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
    exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract,
      locals := callargs.insert "length" (.int (Int.ofNat len.toNat)) } evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consRevert ?_
  refine ExecStmt.requireFalse ?_
  apply evalExpr_reveal_local_array_length_eq_var_false
  · rw [store_get_ne]
    · exact hvalues
    · decide
  · rw [store_get_self]
  · exact hne

theorem blindAuctionRevealBodyReverts_fakesLengthMismatch (evm : EVM.State)
    (callargs : Store) (values fakes : List Value) (len : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesNe : fakes.length ≠ len.toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs } evm
        (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
    exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract,
      locals := callargs.insert "length" (.int (Int.ofNat len.toNat)) } evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (callargs.insert "length" (.int (Int.ofNat len.toNat))) "values" values len
        (by
          rw [store_get_ne]
          · exact hvalues
          · decide)
        (by rw [store_get_self]) hvaluesLen)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.requireFalse ?_
  apply evalExpr_reveal_local_array_length_eq_var_false
  · rw [store_get_ne]
    · exact hfakes
    · decide
  · rw [store_get_self]
  · exact hfakesNe

theorem blindAuctionRevealBodyReverts_secretsLengthMismatch (evm : EVM.State)
    (callargs : Store) (values fakes secrets : List Value) (len : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesLen : fakes.length = len.toNat)
    (hsecretsNe : secrets.length ≠ len.toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs
      revealTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs } evm
        (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
    exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig
    { contract := blindAuctionContract,
      locals := callargs.insert "length" (.int (Int.ofNat len.toNat)) } evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (callargs.insert "length" (.int (Int.ofNat len.toNat))) "values" values len
        (by
          rw [store_get_ne]
          · exact hvalues
          · decide)
        (by rw [store_get_self]) hvaluesLen)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (callargs.insert "length" (.int (Int.ofNat len.toNat))) "fakes" fakes len
        (by
          rw [store_get_ne]
          · exact hfakes
          · decide)
        (by rw [store_get_self]) hfakesLen)) ?_
  refine ExecBlock.consRevert ?_
  refine ExecStmt.requireFalse ?_
  apply evalExpr_reveal_local_array_length_eq_var_false
  · rw [store_get_ne]
    · exact hsecrets
    · decide
  · rw [store_get_self]
  · exact hsecretsNe

theorem blindAuctionRevealBodyReverts_decoded_lengthMismatch
    (evm : EVM.State) {I : ExecutionEnv} {callargs : Store} {len : UInt256}
    {values fakes secrets : List Value}
    (hdec : decodeCalldata (revealTransition.params.map Param.name)
      (transitionSignature revealTransition).paramTypes I.calldata = some callargs)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hmismatch :
      values.length ≠ len.toNat ∨ fakes.length ≠ len.toNat ∨
        secrets.length ≠ len.toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs
      revealTransition.body .reverted := by
  have hbids : callargs.get? "bids" = none :=
    blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
  have hbidding : callargs.get? biddingEndRef.base = none :=
    blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
  have hreveal : callargs.get? revealEndRef.base = none :=
    blindAuctionDecode_reveal_callargs_absent hdec (by decide) (by decide) (by decide)
  by_cases hvaluesEq : values.length = len.toNat
  · by_cases hfakesEq : fakes.length = len.toNat
    · have hsecretsNe : secrets.length ≠ len.toNat := by
        rcases hmismatch with hvaluesNe | htail
        · exact False.elim (hvaluesNe hvaluesEq)
        · rcases htail with hfakesNe | hsecretsNe
          · exact False.elim (hfakesNe hfakesEq)
          · exact hsecretsNe
      exact blindAuctionRevealBodyReverts_secretsLengthMismatch evm callargs values fakes
        secrets len hwv hbidding hreveal hbids hvalues hfakes hsecrets hafter hbefore hlen
        hvaluesEq hfakesEq hsecretsNe
    · exact blindAuctionRevealBodyReverts_fakesLengthMismatch evm callargs values fakes len
        hwv hbidding hreveal hbids hvalues hfakes hafter hbefore hlen hvaluesEq hfakesEq
  · exact blindAuctionRevealBodyReverts_valuesLengthMismatch evm callargs values len hwv
      hbidding hreveal hbids hvalues hafter hbefore hlen hvaluesEq

/-- `reveal(uint256[],bool[],bytes32[])` body (pc 387) refines its transition. -/
theorem blindAuctionRevealBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x90, 0x0f, 0x08, 0x0a]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨387⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
 :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm

  have hsz := blindAuctionRevealSelector_size hsel
  have hd := blindAuctionDispatch_reveal (cd := I.calldata) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have _hdecodeEntry :=
      blindAuctionX_reveal_decodeEntry (g := Sat256.ofUInt256 g) hwv hreach
    by_cases hshortHead : I.calldata.size < 100
    · have hdecNone := blindAuctionDecode_reveal_none_short (I := I) hsz hshortHead
      have hslt :
          UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ =
            ⟨1⟩ := by
        have h :=
          solcCalldataStaticLenCheckShort (sz := I.calldata.size) (words := 3)
            hsz hshortHead hsize (by omega)
        simpa using h
      have hrev := blindAuctionRevealX_decode_head_revert
        (g := Sat256.ofUInt256 g) hslt _hdecodeEntry
      exact hrev.reEquivDecodingFailed hcode hd hdecNone
    · by_cases hhuge : 2 ^ 255 + 4 ≤ I.calldata.size
      · have hdecNone := blindAuctionDecode_reveal_none_huge (I := I) hhuge
        have hslt :
            UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ =
              ⟨1⟩ := by
          have h :=
            solcCalldataStaticLenCheckHuge (sz := I.calldata.size) (words := 3)
              hhuge hsize (by omega)
          simpa using h
        have hrev := blindAuctionRevealX_decode_head_revert
          (g := Sat256.ofUInt256 g) hslt _hdecodeEntry
        exact hrev.reEquivDecodingFailed hcode hd hdecNone
      · sorry
  · have hrev := blindAuctionX_reveal_nonpayable (g := Sat256.ofUInt256 g) hwv hreach
    by_cases hdecNone :
        decodeCalldata (revealTransition.params.map Param.name)
          (transitionSignature revealTransition).paramTypes I.calldata = none
    · exact hrev.reEquivDecodingFailed hcode hd hdecNone
    · obtain ⟨callargs, hdec⟩ := Option.ne_none_iff_exists'.mp hdecNone
      have hbody :
          ExecTransitionBody blindAuctionConfig blindAuctionContract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) callargs
            revealTransition.body .reverted := by
        exact blindAuctionRevealBodyReverts_nonpayable
          (by simp only [initState]; exact hwv)
      exact hrev.reEquivExecutionRevert hcode hd hdec hbody

end BlindAuction
