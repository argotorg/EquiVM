import Benchmarks.UniswapV3Pool.InitializeGetTickLog

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

def getTickLogRSquared50Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.mul (getTickLogRAfter51Word ee) (getTickLogRAfter51Word ee)

def getTickLogRShifted50Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared50Word ee) ⟨127⟩

def getTickLog2BaseWord (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftLeft (getTickMsbWord ee + UInt256.lnot ⟨127⟩) ⟨64⟩

def getTickLog2Bit63Mask : UInt256 := ⟨9223372036854775808⟩

def getTickLog2Bit62Mask : UInt256 := ⟨4611686018427387904⟩

def getTickLog2Bit61Mask : UInt256 := ⟨2305843009213693952⟩

def getTickLog2Bit60Mask : UInt256 := ⟨1152921504606846976⟩

def getTickLog2Bit59Mask : UInt256 := ⟨576460752303423488⟩

def getTickLog2Bit58Mask : UInt256 := ⟨288230376151711744⟩

def getTickLog2Bit57Mask : UInt256 := ⟨144115188075855872⟩

def getTickLog2Bit56Mask : UInt256 := ⟨72057594037927936⟩

def getTickLog2Bit55Mask : UInt256 := ⟨36028797018963968⟩

def getTickLog2Bit54Mask : UInt256 := ⟨18014398509481984⟩

def getTickLog2Bit53Mask : UInt256 := ⟨9007199254740992⟩

def getTickLog2Bit52Mask : UInt256 := ⟨4503599627370496⟩

def getTickLog2Bit51Mask : UInt256 := ⟨2251799813685248⟩

def getTickLog2Bit50Mask : UInt256 := ⟨1125899906842624⟩

def getTickLog2Bit63Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.land getTickLog2Bit63Mask
    (UInt256.shiftRight (getTickLogRSquared63Word ee) ⟨192⟩)

def getTickLog2After63Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickLog2Bit63Word ee) (getTickLog2BaseWord ee)

def getTickLog2Bit62Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.land getTickLog2Bit62Mask
    (UInt256.shiftRight (getTickLogRSquared62Word ee) ⟨193⟩)

def getTickLog2After62Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickLog2Bit62Word ee) (getTickLog2After63Word ee)

def getTickLog2Bit61Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.land getTickLog2Bit61Mask
    (UInt256.shiftRight (getTickLogRSquared61Word ee) ⟨194⟩)

def getTickLog2After61Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickLog2Bit61Word ee) (getTickLog2After62Word ee)

def getTickLog2Bit60Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.land getTickLog2Bit60Mask
    (UInt256.shiftRight (getTickLogRSquared60Word ee) ⟨195⟩)

def getTickLog2After60Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickLog2Bit60Word ee) (getTickLog2After61Word ee)

def getTickLog2Bit59Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.land getTickLog2Bit59Mask
    (UInt256.shiftRight (getTickLogRSquared59Word ee) ⟨196⟩)

def getTickLog2After59Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickLog2Bit59Word ee) (getTickLog2After60Word ee)

def getTickLog2Bit58Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.land getTickLog2Bit58Mask
    (UInt256.shiftRight (getTickLogRSquared58Word ee) ⟨197⟩)

def getTickLog2After58Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickLog2Bit58Word ee) (getTickLog2After59Word ee)

def getTickLog2Bit57Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.land getTickLog2Bit57Mask
    (UInt256.shiftRight (getTickLogRSquared57Word ee) ⟨198⟩)

def getTickLog2After57Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickLog2Bit57Word ee) (getTickLog2After58Word ee)

def getTickLog2Bit56Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.land getTickLog2Bit56Mask
    (UInt256.shiftRight (getTickLogRSquared56Word ee) ⟨199⟩)

def getTickLog2After56Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickLog2Bit56Word ee) (getTickLog2After57Word ee)

def getTickLog2Bit55Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.land getTickLog2Bit55Mask
    (UInt256.shiftRight (getTickLogRSquared55Word ee) ⟨200⟩)

def getTickLog2After55Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickLog2Bit55Word ee) (getTickLog2After56Word ee)

def getTickLog2Bit54Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.land getTickLog2Bit54Mask
    (UInt256.shiftRight (getTickLogRSquared54Word ee) ⟨201⟩)

def getTickLog2After54Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickLog2Bit54Word ee) (getTickLog2After55Word ee)

def getTickLog2Bit53Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.land getTickLog2Bit53Mask
    (UInt256.shiftRight (getTickLogRSquared53Word ee) ⟨202⟩)

def getTickLog2After53Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickLog2Bit53Word ee) (getTickLog2After54Word ee)

def getTickLog2Bit52Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.land getTickLog2Bit52Mask
    (UInt256.shiftRight (getTickLogRSquared52Word ee) ⟨203⟩)

def getTickLog2After52Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickLog2Bit52Word ee) (getTickLog2After53Word ee)

def getTickLog2Bit51Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.land getTickLog2Bit51Mask
    (UInt256.shiftRight (getTickLogRSquared51Word ee) ⟨204⟩)

def getTickLog2After51Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickLog2Bit51Word ee) (getTickLog2After52Word ee)

def getTickLog2Bit50Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.land getTickLog2Bit50Mask
    (UInt256.shiftRight (getTickLogRSquared50Word ee) ⟨205⟩)

def getTickLog2After50Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.lor (getTickLog2Bit50Word ee) (getTickLog2After51Word ee)

def getTickLogSqrt10001Multiplier : UInt256 := ⟨255738958999603826347141⟩

def getTickLowOffsetWord : UInt256 := ⟨3402992956809132418596140100660247209⟩

def getTickHiOffsetWord : UInt256 := ⟨291339464771989622907027621153398088495⟩

def getTickLogSqrt10001Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.mul (getTickLog2After50Word ee) getTickLogSqrt10001Multiplier

def getTickLowBiasedWord (ee : ExecutionEnv) : UInt256 :=
  getTickLogSqrt10001Word ee + UInt256.lnot getTickLowOffsetWord

def getTickLowWord (ee : ExecutionEnv) : UInt256 :=
  UInt256.sar ⟨128⟩ (getTickLowBiasedWord ee)

def getTickHiBiasedWord (ee : ExecutionEnv) : UInt256 :=
  getTickLogSqrt10001Word ee + getTickHiOffsetWord

def getTickHiWord (ee : ExecutionEnv) : UInt256 :=
  UInt256.sar ⟨128⟩ (getTickHiBiasedWord ee)

def getTickHiInt24Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨2⟩ (getTickHiWord ee)

def getTickLowInt24Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨2⟩ (getTickLowWord ee)

def getTickLowEqHiWord (ee : ExecutionEnv) : UInt256 :=
  UInt256.eq (getTickLowInt24Word ee) (getTickHiInt24Word ee)

-- LIBRARY CANDIDATE: fills the missing `Reasoning.Theory` wrapper for EVM `DUP16`.
theorem dup16_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP16, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        oo :: pp :: t)
    (hov : t.length + 17 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll ::
              mm :: nn :: oo :: pp :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP16, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup16 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
          nn :: oo :: pp :: t).length - 16 + 17 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- LIBRARY CANDIDATE: companion `RD` combinator for the missing `DUP16` wrapper.
theorem RD.dup16 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        oo :: pp :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP16, .none)) (hov : t.length + 17 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
        nn :: oo :: pp :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup16_xstep hc hp hdec hs hov)

-- LIBRARY CANDIDATE: fills the missing `Reasoning.Theory` wrapper for EVM `SWAP15`.
theorem swap15_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP15, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        oo :: pp :: t)
    (hov : t.length + 16 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (pp :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
              nn :: oo :: a :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP15, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap15 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
          nn :: oo :: pp :: t).length - 16 + 16 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- LIBRARY CANDIDATE: companion `RD` combinator for the missing `SWAP15` wrapper.
theorem RD.swap15 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        oo :: pp :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP15, .none)) (hov : t.length + 16 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (pp :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        oo :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap15_xstep hc hp hdec hs hov)

-- LIBRARY CANDIDATE: fills the missing `Reasoning.Theory` wrapper for EVM `SWAP14`.
theorem swap14_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn oo : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP14, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        oo :: t)
    (hov : t.length + 15 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (oo :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
              nn :: a :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP14, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap14 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
          nn :: oo :: t).length - 15 + 15 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- LIBRARY CANDIDATE: companion `RD` combinator for the missing `SWAP14` wrapper.
theorem RD.swap14 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn oo : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        oo :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP14, .none)) (hov : t.length + 15 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (oo :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap14_xstep hc hp hdec hs hov)

-- LIBRARY CANDIDATE: fills the missing `Reasoning.Theory` wrapper for EVM `SWAP12`.
theorem swap12_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP12, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: t)
    (hov : t.length + 13 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (mm :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll ::
              a :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP12, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap12 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll ::
          mm :: t).length - 13 + 13 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- LIBRARY CANDIDATE: companion `RD` combinator for the missing `SWAP12` wrapper.
theorem RD.swap12 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP12, .none)) (hov : t.length + 13 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (mm :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap12_xstep hc hp hdec hs hov)

-- LIBRARY CANDIDATE: fills the missing `Reasoning.Theory` wrapper for EVM `SWAP9`.
theorem swap9_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP9, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
    (hov : t.length + 10 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (jj :: b :: c :: d :: e :: f :: gg :: hh :: ii :: a :: t),
          .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP9, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap9 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t).length - 10 + 10 >
          1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- LIBRARY CANDIDATE: companion `RD` combinator for the missing `SWAP9` wrapper.
theorem RD.swap9 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP9, .none)) (hov : t.length + 10 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (jj :: b :: c :: d :: e :: f :: gg :: hh :: ii :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => swap9_xstep hc hp hdec hs hov)

-- LIBRARY CANDIDATE: fills the missing `Reasoning.Theory` wrapper for EVM `SAR`.
theorem sar_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SAR, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.sar a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SAR, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_sar s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

-- LIBRARY CANDIDATE: companion `RD` combinator for the missing `SAR` wrapper.
theorem RD.sar {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SAR, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.sar a b :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => sar_xstep hc hp hdec hs hov)

-- LIBRARY CANDIDATE: state update helper for the missing EVM `SIGNEXTEND` wrapper.
def stSignextend (s : State) (res : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := res :: t,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat 5 } }

-- LIBRARY CANDIDATE: fills the missing `Reasoning.Theory` wrapper for EVM `SIGNEXTEND`.
theorem signextend_xstep {s : State} {code : ByteArray}
    {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SIGNEXTEND, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
         else .ok (stSignextend s (UInt256.signextend a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SIGNEXTEND, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_signextend s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Glow, stSignextend]

-- LIBRARY CANDIDATE: companion `RD` combinator for the missing `SIGNEXTEND` wrapper.
theorem RD.signextend {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SIGNEXTEND, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.signextend a b :: t) mem aw rdata acc
      (k + 1) (C + 5) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc,
      hee, hworld⟩
  · exact Or.inl hoog
  · have st := signextend_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 5
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stSignextend s (UInt256.signextend a b) t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stSignextend]; exact hcode
      · simp only [stSignextend]; rw [hpc]
      · rfl
      · simp only [stSignextend]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stSignextend]; exact hmem
      · simp only [stSignextend]; exact haw
      · simp only [stSignextend]; exact hrdata
      · simp only [stSignextend]; exact hacc
      · exact hee
      · exact hworld

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioLog2Bits63To57 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14403⟩
      (getTickLogRAfter51Word ee :: getTickLogRSquared52Word ee ::
        getTickLogRSquared53Word ee :: getTickLogRSquared54Word ee ::
          getTickLogRSquared55Word ee :: getTickLogRSquared56Word ee ::
            getTickLogRSquared57Word ee :: getTickLogRSquared58Word ee ::
              getTickLogRSquared59Word ee :: getTickLogRSquared60Word ee ::
                getTickLogRSquared61Word ee :: getTickLogRSquared62Word ee ::
                  getTickLogRSquared51Word ee :: ⟨127⟩ :: getTickLogRSquared63Word ee ::
                    getTickMsbWord ee :: getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee ::
                      ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 28 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14553⟩
      (getTickLog2After57Word ee :: getTickLogRSquared56Word ee ::
        getTickLogRSquared55Word ee :: getTickLogRSquared54Word ee ::
          getTickLogRSquared53Word ee :: getTickLogRSquared52Word ee ::
            getTickLogRSquared51Word ee :: getTickLogRSquared50Word ee ::
              getTickMsbWord ee :: getTickLogRShifted50Word ee :: getTickRatioWord ee ::
                ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee ::
                  ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14403 : decode code ⟨14403⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14404 : decode code ⟨14404⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14405 : decode code ⟨14405⟩ = some (.SWAP13, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14406 : decode code ⟨14406⟩ = some (.DUP14, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14407 : decode code ⟨14407⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14408 : decode code ⟨14408⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14409 : decode code ⟨14409⟩ = some (.SWAP15, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14410 : decode code ⟨14410⟩ = some (.SWAP14, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14411 : decode code ⟨14411⟩ = some (.Push .PUSH1, some (⟨127⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14413 : decode code ⟨14413⟩ = some (.NOT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14414 : decode code ⟨14414⟩ = some (.DUP16, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14415 : decode code ⟨14415⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14416 : decode code ⟨14416⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14418 : decode code ⟨14418⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14419 : decode code ⟨14419⟩ = some (.Push .PUSH1, some (⟨192⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14421 : decode code ⟨14421⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14422 : decode code ⟨14422⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14423 : decode code ⟨14423⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14424 : decode code ⟨14424⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14425 :
      decode code ⟨14425⟩ = some (.Push .PUSH8, some (getTickLog2Bit63Mask, 8)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14434 : decode code ⟨14434⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14435 : decode code ⟨14435⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14436 : decode code ⟨14436⟩ = some (.Push .PUSH1, some (⟨193⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14438 : decode code ⟨14438⟩ = some (.SWAP12, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14439 : decode code ⟨14439⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14440 : decode code ⟨14440⟩ = some (.SWAP12, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14441 : decode code ⟨14441⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14442 :
      decode code ⟨14442⟩ = some (.Push .PUSH8, some (getTickLog2Bit62Mask, 8)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14451 : decode code ⟨14451⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14452 : decode code ⟨14452⟩ = some (.SWAP11, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14453 : decode code ⟨14453⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14454 : decode code ⟨14454⟩ = some (.SWAP11, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14455 : decode code ⟨14455⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14456 : decode code ⟨14456⟩ = some (.Push .PUSH1, some (⟨194⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14458 : decode code ⟨14458⟩ = some (.SWAP10, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14459 : decode code ⟨14459⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14460 : decode code ⟨14460⟩ = some (.SWAP10, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14461 : decode code ⟨14461⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14462 :
      decode code ⟨14462⟩ = some (.Push .PUSH8, some (getTickLog2Bit61Mask, 8)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14471 : decode code ⟨14471⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14472 : decode code ⟨14472⟩ = some (.SWAP9, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14473 : decode code ⟨14473⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14474 : decode code ⟨14474⟩ = some (.SWAP9, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14475 : decode code ⟨14475⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14476 : decode code ⟨14476⟩ = some (.Push .PUSH1, some (⟨195⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14478 : decode code ⟨14478⟩ = some (.SWAP8, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14479 : decode code ⟨14479⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14480 : decode code ⟨14480⟩ = some (.SWAP8, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14481 : decode code ⟨14481⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14482 :
      decode code ⟨14482⟩ = some (.Push .PUSH8, some (getTickLog2Bit60Mask, 8)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14491 : decode code ⟨14491⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14492 : decode code ⟨14492⟩ = some (.SWAP7, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14493 : decode code ⟨14493⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14494 : decode code ⟨14494⟩ = some (.SWAP7, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14495 : decode code ⟨14495⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14496 : decode code ⟨14496⟩ = some (.Push .PUSH1, some (⟨196⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14498 : decode code ⟨14498⟩ = some (.SWAP6, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14499 : decode code ⟨14499⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14500 : decode code ⟨14500⟩ = some (.SWAP6, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14501 : decode code ⟨14501⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14502 :
      decode code ⟨14502⟩ = some (.Push .PUSH8, some (getTickLog2Bit59Mask, 8)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14511 : decode code ⟨14511⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14512 : decode code ⟨14512⟩ = some (.SWAP5, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14513 : decode code ⟨14513⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14514 : decode code ⟨14514⟩ = some (.SWAP5, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14515 : decode code ⟨14515⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14516 : decode code ⟨14516⟩ = some (.Push .PUSH1, some (⟨197⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14518 : decode code ⟨14518⟩ = some (.SWAP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14519 : decode code ⟨14519⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14520 : decode code ⟨14520⟩ = some (.SWAP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14521 : decode code ⟨14521⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14522 :
      decode code ⟨14522⟩ = some (.Push .PUSH8, some (getTickLog2Bit58Mask, 8)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14531 : decode code ⟨14531⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14532 : decode code ⟨14532⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14533 : decode code ⟨14533⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14534 : decode code ⟨14534⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14535 : decode code ⟨14535⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14536 : decode code ⟨14536⟩ = some (.Push .PUSH1, some (⟨198⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14538 : decode code ⟨14538⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14539 : decode code ⟨14539⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14540 : decode code ⟨14540⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14541 : decode code ⟨14541⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14542 :
      decode code ⟨14542⟩ = some (.Push .PUSH8, some (getTickLog2Bit57Mask, 8)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14551 : decode code ⟨14551⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14552 : decode code ⟨14552⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14404 := by
    simpa using h.dup1 hd14403 (by
      simp only [List.length_cons]
      omega)
  have rd14405 := by
    simpa [getTickLogRSquared50Word] using rd14404.mul hd14404 (by
      simp only [List.length_cons]
      omega)
  have rd14406 := by
    simpa using RD.swap13 rd14405 hd14405 (by
      simp only [List.length_cons]
      omega)
  have rd14407 := by
    simpa using rd14406.dup14 hd14406 (by
      simp only [List.length_cons]
      omega)
  have rd14408 := by
    simpa using rd14407.swap1 hd14407 (by
      simp only [List.length_cons]
      omega)
  have rd14409 := by
    simpa [getTickLogRShifted50Word] using rd14408.shr hd14408 (by
      simp only [List.length_cons]
      omega)
  have rd14410 := by
    simpa using RD.swap15 rd14409 hd14409 (by
      simp only [List.length_cons]
      omega)
  have rd14411 := by
    simpa using RD.swap14 rd14410 hd14410 (by
      simp only [List.length_cons]
      omega)
  have rd14413 := by
    simpa using rd14411.push1 ⟨127⟩ hd14411 (by
      simp only [List.length_cons]
      omega)
  have rd14414 := by
    simpa using rd14413.not hd14413 (by
      simp only [List.length_cons]
      omega)
  have rd14415 := by
    simpa using RD.dup16 rd14414 hd14414 (by
      simp only [List.length_cons]
      omega)
  have rd14416 := by
    simpa using rd14415.add hd14415 (by
      simp only [List.length_cons]
      omega)
  have rd14418 := by
    simpa using rd14416.push1 ⟨64⟩ hd14416 (by
      simp only [List.length_cons]
      omega)
  have rd14419 := by
    simpa [getTickLog2BaseWord] using rd14418.shl hd14418 (by
      simp only [List.length_cons]
      omega)
  have rd14421 := by
    simpa using rd14419.push1 ⟨192⟩ hd14419 (by
      simp only [List.length_cons]
      omega)
  have rd14422 := by
    simpa using rd14421.swap2 hd14421 (by
      simp only [List.length_cons]
      omega)
  have rd14423 := by
    simpa using rd14422.swap1 hd14422 (by
      simp only [List.length_cons]
      omega)
  have rd14424 := by
    simpa using rd14423.swap2 hd14423 (by
      simp only [List.length_cons]
      omega)
  have rd14425 := by
    simpa using rd14424.shr hd14424 (by
      simp only [List.length_cons]
      omega)
  have rd14434 := by
    simpa using rd14425.pushConst getTickLog2Bit63Mask
      (by native_decide : Operation.POp.PUSH8 ≠ .PUSH0) hd14425 (by
        simp only [List.length_cons]
        omega)
  have rd14435 := by
    simpa [getTickLog2Bit63Word] using rd14434.and hd14434 (by
      simp only [List.length_cons]
      omega)
  have rd14436 := by
    simpa [getTickLog2After63Word] using rd14435.lor hd14435 (by
      simp only [List.length_cons]
      omega)
  have rd14438 := by
    simpa using rd14436.push1 ⟨193⟩ hd14436 (by
      simp only [List.length_cons]
      omega)
  have rd14439 := by
    simpa using RD.swap12 rd14438 hd14438 (by
      simp only [List.length_cons]
      omega)
  have rd14440 := by
    simpa using rd14439.swap1 hd14439 (by
      simp only [List.length_cons]
      omega)
  have rd14441 := by
    simpa using RD.swap12 rd14440 hd14440 (by
      simp only [List.length_cons]
      omega)
  have rd14442 := by
    simpa using rd14441.shr hd14441 (by
      simp only [List.length_cons]
      omega)
  have rd14451 := by
    simpa using rd14442.pushConst getTickLog2Bit62Mask
      (by native_decide : Operation.POp.PUSH8 ≠ .PUSH0) hd14442 (by
        simp only [List.length_cons]
        omega)
  have rd14452 := by
    simpa [getTickLog2Bit62Word] using rd14451.and hd14451 (by
      simp only [List.length_cons]
      omega)
  have rd14453 := by
    simpa using rd14452.swap11 hd14452 (by
      simp only [List.length_cons]
      omega)
  have rd14454 := by
    simpa using rd14453.swap1 hd14453 (by
      simp only [List.length_cons]
      omega)
  have rd14455 := by
    simpa using rd14454.swap11 hd14454 (by
      simp only [List.length_cons]
      omega)
  have rd14456 := by
    simpa [getTickLog2After62Word] using rd14455.lor hd14455 (by
      simp only [List.length_cons]
      omega)
  have rd14458 := by
    simpa using rd14456.push1 ⟨194⟩ hd14456 (by
      simp only [List.length_cons]
      omega)
  have rd14459 := by
    simpa using rd14458.swap10 hd14458 (by
      simp only [List.length_cons]
      omega)
  have rd14460 := by
    simpa using rd14459.swap1 hd14459 (by
      simp only [List.length_cons]
      omega)
  have rd14461 := by
    simpa using rd14460.swap10 hd14460 (by
      simp only [List.length_cons]
      omega)
  have rd14462 := by
    simpa using rd14461.shr hd14461 (by
      simp only [List.length_cons]
      omega)
  have rd14471 := by
    simpa using rd14462.pushConst getTickLog2Bit61Mask
      (by native_decide : Operation.POp.PUSH8 ≠ .PUSH0) hd14462 (by
        simp only [List.length_cons]
        omega)
  have rd14472 := by
    simpa [getTickLog2Bit61Word] using rd14471.and hd14471 (by
      simp only [List.length_cons]
      omega)
  have rd14473 := by
    simpa using RD.swap9 rd14472 hd14472 (by
      simp only [List.length_cons]
      omega)
  have rd14474 := by
    simpa using rd14473.swap1 hd14473 (by
      simp only [List.length_cons]
      omega)
  have rd14475 := by
    simpa using RD.swap9 rd14474 hd14474 (by
      simp only [List.length_cons]
      omega)
  have rd14476 := by
    simpa [getTickLog2After61Word] using rd14475.lor hd14475 (by
      simp only [List.length_cons]
      omega)
  have rd14478 := by
    simpa using rd14476.push1 ⟨195⟩ hd14476 (by
      simp only [List.length_cons]
      omega)
  have rd14479 := by
    simpa using rd14478.swap8 hd14478 (by
      simp only [List.length_cons]
      omega)
  have rd14480 := by
    simpa using rd14479.swap1 hd14479 (by
      simp only [List.length_cons]
      omega)
  have rd14481 := by
    simpa using rd14480.swap8 hd14480 (by
      simp only [List.length_cons]
      omega)
  have rd14482 := by
    simpa using rd14481.shr hd14481 (by
      simp only [List.length_cons]
      omega)
  have rd14491 := by
    simpa using rd14482.pushConst getTickLog2Bit60Mask
      (by native_decide : Operation.POp.PUSH8 ≠ .PUSH0) hd14482 (by
        simp only [List.length_cons]
        omega)
  have rd14492 := by
    simpa [getTickLog2Bit60Word] using rd14491.and hd14491 (by
      simp only [List.length_cons]
      omega)
  have rd14493 := by
    simpa using rd14492.swap7 hd14492 (by
      simp only [List.length_cons]
      omega)
  have rd14494 := by
    simpa using rd14493.swap1 hd14493 (by
      simp only [List.length_cons]
      omega)
  have rd14495 := by
    simpa using rd14494.swap7 hd14494 (by
      simp only [List.length_cons]
      omega)
  have rd14496 := by
    simpa [getTickLog2After60Word] using rd14495.lor hd14495 (by
      simp only [List.length_cons]
      omega)
  have rd14498 := by
    simpa using rd14496.push1 ⟨196⟩ hd14496 (by
      simp only [List.length_cons]
      omega)
  have rd14499 := by
    simpa using rd14498.swap6 hd14498 (by
      simp only [List.length_cons]
      omega)
  have rd14500 := by
    simpa using rd14499.swap1 hd14499 (by
      simp only [List.length_cons]
      omega)
  have rd14501 := by
    simpa using rd14500.swap6 hd14500 (by
      simp only [List.length_cons]
      omega)
  have rd14502 := by
    simpa using rd14501.shr hd14501 (by
      simp only [List.length_cons]
      omega)
  have rd14511 := by
    simpa using rd14502.pushConst getTickLog2Bit59Mask
      (by native_decide : Operation.POp.PUSH8 ≠ .PUSH0) hd14502 (by
        simp only [List.length_cons]
        omega)
  have rd14512 := by
    simpa [getTickLog2Bit59Word] using rd14511.and hd14511 (by
      simp only [List.length_cons]
      omega)
  have rd14513 := by
    simpa using rd14512.swap5 hd14512 (by
      simp only [List.length_cons]
      omega)
  have rd14514 := by
    simpa using rd14513.swap1 hd14513 (by
      simp only [List.length_cons]
      omega)
  have rd14515 := by
    simpa using rd14514.swap5 hd14514 (by
      simp only [List.length_cons]
      omega)
  have rd14516 := by
    simpa [getTickLog2After59Word] using rd14515.lor hd14515 (by
      simp only [List.length_cons]
      omega)
  have rd14518 := by
    simpa using rd14516.push1 ⟨197⟩ hd14516 (by
      simp only [List.length_cons]
      omega)
  have rd14519 := by
    simpa using rd14518.swap4 hd14518 (by
      simp only [List.length_cons]
      omega)
  have rd14520 := by
    simpa using rd14519.swap1 hd14519 (by
      simp only [List.length_cons]
      omega)
  have rd14521 := by
    simpa using rd14520.swap4 hd14520 (by
      simp only [List.length_cons]
      omega)
  have rd14522 := by
    simpa using rd14521.shr hd14521 (by
      simp only [List.length_cons]
      omega)
  have rd14531 := by
    simpa using rd14522.pushConst getTickLog2Bit58Mask
      (by native_decide : Operation.POp.PUSH8 ≠ .PUSH0) hd14522 (by
        simp only [List.length_cons]
        omega)
  have rd14532 := by
    simpa [getTickLog2Bit58Word] using rd14531.and hd14531 (by
      simp only [List.length_cons]
      omega)
  have rd14533 := by
    simpa using rd14532.swap3 hd14532 (by
      simp only [List.length_cons]
      omega)
  have rd14534 := by
    simpa using rd14533.swap1 hd14533 (by
      simp only [List.length_cons]
      omega)
  have rd14535 := by
    simpa using rd14534.swap3 hd14534 (by
      simp only [List.length_cons]
      omega)
  have rd14536 := by
    simpa [getTickLog2After58Word] using rd14535.lor hd14535 (by
      simp only [List.length_cons]
      omega)
  have rd14538 := by
    simpa using rd14536.push1 ⟨198⟩ hd14536 (by
      simp only [List.length_cons]
      omega)
  have rd14539 := by
    simpa using rd14538.swap2 hd14538 (by
      simp only [List.length_cons]
      omega)
  have rd14540 := by
    simpa using rd14539.swap1 hd14539 (by
      simp only [List.length_cons]
      omega)
  have rd14541 := by
    simpa using rd14540.swap2 hd14540 (by
      simp only [List.length_cons]
      omega)
  have rd14542 := by
    simpa using rd14541.shr hd14541 (by
      simp only [List.length_cons]
      omega)
  have rd14551 := by
    simpa using rd14542.pushConst getTickLog2Bit57Mask
      (by native_decide : Operation.POp.PUSH8 ≠ .PUSH0) hd14542 (by
        simp only [List.length_cons]
        omega)
  have rd14552 := by
    simpa [getTickLog2Bit57Word] using rd14551.and hd14551 (by
      simp only [List.length_cons]
      omega)
  have rd14553 := by
    simpa [getTickLog2After57Word] using rd14552.lor hd14552 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14553⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioLog2Bits56To50 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14553⟩
      (getTickLog2After57Word ee :: getTickLogRSquared56Word ee ::
        getTickLogRSquared55Word ee :: getTickLogRSquared54Word ee ::
          getTickLogRSquared53Word ee :: getTickLogRSquared52Word ee ::
            getTickLogRSquared51Word ee :: getTickLogRSquared50Word ee ::
              getTickMsbWord ee :: getTickLogRShifted50Word ee :: getTickRatioWord ee ::
                ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee ::
                  ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 23 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14666⟩
      (getTickLog2After50Word ee :: getTickMsbWord ee :: getTickLogRShifted50Word ee ::
        getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
          initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14553 : decode code ⟨14553⟩ = some (.Push .PUSH1, some (⟨199⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14555 : decode code ⟨14555⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14556 : decode code ⟨14556⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14557 : decode code ⟨14557⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14558 : decode code ⟨14558⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14559 :
      decode code ⟨14559⟩ = some (.Push .PUSH8, some (getTickLog2Bit56Mask, 8)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14568 : decode code ⟨14568⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14569 : decode code ⟨14569⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14570 : decode code ⟨14570⟩ = some (.Push .PUSH1, some (⟨200⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14572 : decode code ⟨14572⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14573 : decode code ⟨14573⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14574 : decode code ⟨14574⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14575 : decode code ⟨14575⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14576 :
      decode code ⟨14576⟩ = some (.Push .PUSH7, some (getTickLog2Bit55Mask, 7)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14584 : decode code ⟨14584⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14585 : decode code ⟨14585⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14586 : decode code ⟨14586⟩ = some (.Push .PUSH1, some (⟨201⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14588 : decode code ⟨14588⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14589 : decode code ⟨14589⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14590 : decode code ⟨14590⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14591 : decode code ⟨14591⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14592 :
      decode code ⟨14592⟩ = some (.Push .PUSH7, some (getTickLog2Bit54Mask, 7)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14600 : decode code ⟨14600⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14601 : decode code ⟨14601⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14602 : decode code ⟨14602⟩ = some (.Push .PUSH1, some (⟨202⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14604 : decode code ⟨14604⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14605 : decode code ⟨14605⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14606 : decode code ⟨14606⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14607 : decode code ⟨14607⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14608 :
      decode code ⟨14608⟩ = some (.Push .PUSH7, some (getTickLog2Bit53Mask, 7)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14616 : decode code ⟨14616⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14617 : decode code ⟨14617⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14618 : decode code ⟨14618⟩ = some (.Push .PUSH1, some (⟨203⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14620 : decode code ⟨14620⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14621 : decode code ⟨14621⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14622 : decode code ⟨14622⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14623 : decode code ⟨14623⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14624 :
      decode code ⟨14624⟩ = some (.Push .PUSH7, some (getTickLog2Bit52Mask, 7)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14632 : decode code ⟨14632⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14633 : decode code ⟨14633⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14634 : decode code ⟨14634⟩ = some (.Push .PUSH1, some (⟨204⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14636 : decode code ⟨14636⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14637 : decode code ⟨14637⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14638 : decode code ⟨14638⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14639 : decode code ⟨14639⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14640 :
      decode code ⟨14640⟩ = some (.Push .PUSH7, some (getTickLog2Bit51Mask, 7)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14648 : decode code ⟨14648⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14649 : decode code ⟨14649⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14650 : decode code ⟨14650⟩ = some (.Push .PUSH1, some (⟨205⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14652 : decode code ⟨14652⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14653 : decode code ⟨14653⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14654 : decode code ⟨14654⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14655 : decode code ⟨14655⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14656 :
      decode code ⟨14656⟩ = some (.Push .PUSH7, some (getTickLog2Bit50Mask, 7)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14664 : decode code ⟨14664⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14665 : decode code ⟨14665⟩ = some (.OR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14555 := by
    simpa using h.push1 ⟨199⟩ hd14553 (by
      simp only [List.length_cons]
      omega)
  have rd14556 := by
    simpa using rd14555.swap2 hd14555 (by
      simp only [List.length_cons]
      omega)
  have rd14557 := by
    simpa using rd14556.swap1 hd14556 (by
      simp only [List.length_cons]
      omega)
  have rd14558 := by
    simpa using rd14557.swap2 hd14557 (by
      simp only [List.length_cons]
      omega)
  have rd14559 := by
    simpa using rd14558.shr hd14558 (by
      simp only [List.length_cons]
      omega)
  have rd14568 := by
    simpa using rd14559.pushConst getTickLog2Bit56Mask
      (by native_decide : Operation.POp.PUSH8 ≠ .PUSH0) hd14559 (by
        simp only [List.length_cons]
        omega)
  have rd14569 := by
    simpa [getTickLog2Bit56Word] using rd14568.and hd14568 (by
      simp only [List.length_cons]
      omega)
  have rd14570 := by
    simpa [getTickLog2After56Word] using rd14569.lor hd14569 (by
      simp only [List.length_cons]
      omega)
  have rd14572 := by
    simpa using rd14570.push1 ⟨200⟩ hd14570 (by
      simp only [List.length_cons]
      omega)
  have rd14573 := by
    simpa using rd14572.swap2 hd14572 (by
      simp only [List.length_cons]
      omega)
  have rd14574 := by
    simpa using rd14573.swap1 hd14573 (by
      simp only [List.length_cons]
      omega)
  have rd14575 := by
    simpa using rd14574.swap2 hd14574 (by
      simp only [List.length_cons]
      omega)
  have rd14576 := by
    simpa using rd14575.shr hd14575 (by
      simp only [List.length_cons]
      omega)
  have rd14584 := by
    simpa using rd14576.pushConst getTickLog2Bit55Mask
      (by native_decide : Operation.POp.PUSH7 ≠ .PUSH0) hd14576 (by
        simp only [List.length_cons]
        omega)
  have rd14585 := by
    simpa [getTickLog2Bit55Word] using rd14584.and hd14584 (by
      simp only [List.length_cons]
      omega)
  have rd14586 := by
    simpa [getTickLog2After55Word] using rd14585.lor hd14585 (by
      simp only [List.length_cons]
      omega)
  have rd14588 := by
    simpa using rd14586.push1 ⟨201⟩ hd14586 (by
      simp only [List.length_cons]
      omega)
  have rd14589 := by
    simpa using rd14588.swap2 hd14588 (by
      simp only [List.length_cons]
      omega)
  have rd14590 := by
    simpa using rd14589.swap1 hd14589 (by
      simp only [List.length_cons]
      omega)
  have rd14591 := by
    simpa using rd14590.swap2 hd14590 (by
      simp only [List.length_cons]
      omega)
  have rd14592 := by
    simpa using rd14591.shr hd14591 (by
      simp only [List.length_cons]
      omega)
  have rd14600 := by
    simpa using rd14592.pushConst getTickLog2Bit54Mask
      (by native_decide : Operation.POp.PUSH7 ≠ .PUSH0) hd14592 (by
        simp only [List.length_cons]
        omega)
  have rd14601 := by
    simpa [getTickLog2Bit54Word] using rd14600.and hd14600 (by
      simp only [List.length_cons]
      omega)
  have rd14602 := by
    simpa [getTickLog2After54Word] using rd14601.lor hd14601 (by
      simp only [List.length_cons]
      omega)
  have rd14604 := by
    simpa using rd14602.push1 ⟨202⟩ hd14602 (by
      simp only [List.length_cons]
      omega)
  have rd14605 := by
    simpa using rd14604.swap2 hd14604 (by
      simp only [List.length_cons]
      omega)
  have rd14606 := by
    simpa using rd14605.swap1 hd14605 (by
      simp only [List.length_cons]
      omega)
  have rd14607 := by
    simpa using rd14606.swap2 hd14606 (by
      simp only [List.length_cons]
      omega)
  have rd14608 := by
    simpa using rd14607.shr hd14607 (by
      simp only [List.length_cons]
      omega)
  have rd14616 := by
    simpa using rd14608.pushConst getTickLog2Bit53Mask
      (by native_decide : Operation.POp.PUSH7 ≠ .PUSH0) hd14608 (by
        simp only [List.length_cons]
        omega)
  have rd14617 := by
    simpa [getTickLog2Bit53Word] using rd14616.and hd14616 (by
      simp only [List.length_cons]
      omega)
  have rd14618 := by
    simpa [getTickLog2After53Word] using rd14617.lor hd14617 (by
      simp only [List.length_cons]
      omega)
  have rd14620 := by
    simpa using rd14618.push1 ⟨203⟩ hd14618 (by
      simp only [List.length_cons]
      omega)
  have rd14621 := by
    simpa using rd14620.swap2 hd14620 (by
      simp only [List.length_cons]
      omega)
  have rd14622 := by
    simpa using rd14621.swap1 hd14621 (by
      simp only [List.length_cons]
      omega)
  have rd14623 := by
    simpa using rd14622.swap2 hd14622 (by
      simp only [List.length_cons]
      omega)
  have rd14624 := by
    simpa using rd14623.shr hd14623 (by
      simp only [List.length_cons]
      omega)
  have rd14632 := by
    simpa using rd14624.pushConst getTickLog2Bit52Mask
      (by native_decide : Operation.POp.PUSH7 ≠ .PUSH0) hd14624 (by
        simp only [List.length_cons]
        omega)
  have rd14633 := by
    simpa [getTickLog2Bit52Word] using rd14632.and hd14632 (by
      simp only [List.length_cons]
      omega)
  have rd14634 := by
    simpa [getTickLog2After52Word] using rd14633.lor hd14633 (by
      simp only [List.length_cons]
      omega)
  have rd14636 := by
    simpa using rd14634.push1 ⟨204⟩ hd14634 (by
      simp only [List.length_cons]
      omega)
  have rd14637 := by
    simpa using rd14636.swap2 hd14636 (by
      simp only [List.length_cons]
      omega)
  have rd14638 := by
    simpa using rd14637.swap1 hd14637 (by
      simp only [List.length_cons]
      omega)
  have rd14639 := by
    simpa using rd14638.swap2 hd14638 (by
      simp only [List.length_cons]
      omega)
  have rd14640 := by
    simpa using rd14639.shr hd14639 (by
      simp only [List.length_cons]
      omega)
  have rd14648 := by
    simpa using rd14640.pushConst getTickLog2Bit51Mask
      (by native_decide : Operation.POp.PUSH7 ≠ .PUSH0) hd14640 (by
        simp only [List.length_cons]
        omega)
  have rd14649 := by
    simpa [getTickLog2Bit51Word] using rd14648.and hd14648 (by
      simp only [List.length_cons]
      omega)
  have rd14650 := by
    simpa [getTickLog2After51Word] using rd14649.lor hd14649 (by
      simp only [List.length_cons]
      omega)
  have rd14652 := by
    simpa using rd14650.push1 ⟨205⟩ hd14650 (by
      simp only [List.length_cons]
      omega)
  have rd14653 := by
    simpa using rd14652.swap2 hd14652 (by
      simp only [List.length_cons]
      omega)
  have rd14654 := by
    simpa using rd14653.swap1 hd14653 (by
      simp only [List.length_cons]
      omega)
  have rd14655 := by
    simpa using rd14654.swap2 hd14654 (by
      simp only [List.length_cons]
      omega)
  have rd14656 := by
    simpa using rd14655.shr hd14655 (by
      simp only [List.length_cons]
      omega)
  have rd14664 := by
    simpa using rd14656.pushConst getTickLog2Bit50Mask
      (by native_decide : Operation.POp.PUSH7 ≠ .PUSH0) hd14656 (by
        simp only [List.length_cons]
        omega)
  have rd14665 := by
    simpa [getTickLog2Bit50Word] using rd14664.and hd14664 (by
      simp only [List.length_cons]
      omega)
  have rd14666 := by
    simpa [getTickLog2After50Word] using rd14665.lor hd14665 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14666⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioTickEstimateSetup {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14666⟩
      (getTickLog2After50Word ee :: getTickMsbWord ee :: getTickLogRShifted50Word ee ::
        getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
          initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14739⟩
      (⟨14786⟩ :: getTickLowEqHiWord ee :: getTickHiWord ee :: getTickLowWord ee ::
        getTickLogSqrt10001Word ee :: getTickLog2After50Word ee :: getTickMsbWord ee ::
          getTickLogRShifted50Word ee :: getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee ::
            ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14666 :
      decode code ⟨14666⟩ =
        some (.Push .PUSH10, some (getTickLogSqrt10001Multiplier, 10)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14677 : decode code ⟨14677⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14678 : decode code ⟨14678⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14679 :
      decode code ⟨14679⟩ = some (.Push .PUSH16, some (getTickLowOffsetWord, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14696 : decode code ⟨14696⟩ = some (.NOT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14697 : decode code ⟨14697⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14698 : decode code ⟨14698⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14699 : decode code ⟨14699⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14701 : decode code ⟨14701⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14702 : decode code ⟨14702⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14703 : decode code ⟨14703⟩ = some (.SAR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14704 : decode code ⟨14704⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14705 :
      decode code ⟨14705⟩ = some (.Push .PUSH16, some (getTickHiOffsetWord, 16)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14722 : decode code ⟨14722⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14723 : decode code ⟨14723⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14724 : decode code ⟨14724⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14725 : decode code ⟨14725⟩ = some (.SAR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14726 : decode code ⟨14726⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14728 : decode code ⟨14728⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14729 : decode code ⟨14729⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14730 : decode code ⟨14730⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14731 : decode code ⟨14731⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14732 : decode code ⟨14732⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14733 : decode code ⟨14733⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14734 : decode code ⟨14734⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14735 : decode code ⟨14735⟩ = some (.EQ, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14736 : decode code ⟨14736⟩ = some (.Push .PUSH2, some (⟨14786⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14677 := by
    simpa using h.pushConst getTickLogSqrt10001Multiplier
      (by native_decide : Operation.POp.PUSH10 ≠ .PUSH0) hd14666 (by
        simp only [List.length_cons]
        omega)
  have rd14678 := by
    simpa using rd14677.dup2 hd14677 (by
      simp only [List.length_cons]
      omega)
  have rd14679 := by
    simpa [getTickLogSqrt10001Word] using rd14678.mul hd14678 (by
      simp only [List.length_cons]
      omega)
  have rd14696 := by
    simpa using rd14679.pushConst getTickLowOffsetWord
      (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd14679 (by
        simp only [List.length_cons]
        omega)
  have rd14697 := by
    simpa using rd14696.not hd14696 (by
      simp only [List.length_cons]
      omega)
  have rd14698 := by
    simpa using rd14697.dup2 hd14697 (by
      simp only [List.length_cons]
      omega)
  have rd14699 := by
    simpa [getTickLowBiasedWord] using rd14698.add hd14698 (by
      simp only [List.length_cons]
      omega)
  have rd14701 := by
    simpa using rd14699.push1 ⟨128⟩ hd14699 (by
      simp only [List.length_cons]
      omega)
  have rd14702 := by
    simpa using rd14701.swap1 hd14701 (by
      simp only [List.length_cons]
      omega)
  have rd14703 := by
    simpa using rd14702.dup2 hd14702 (by
      simp only [List.length_cons]
      omega)
  have rd14704 := by
    simpa [getTickLowWord] using RD.sar rd14703 hd14703 (by
      simp only [List.length_cons]
      omega)
  have rd14705 := by
    simpa using rd14704.swap1 hd14704 (by
      simp only [List.length_cons]
      omega)
  have rd14722 := by
    simpa using rd14705.pushConst getTickHiOffsetWord
      (by native_decide : Operation.POp.PUSH16 ≠ .PUSH0) hd14705 (by
        simp only [List.length_cons]
        omega)
  have rd14723 := by
    simpa using rd14722.dup4 hd14722 (by
      simp only [List.length_cons]
      omega)
  have rd14724 := by
    simpa [getTickHiBiasedWord] using rd14723.add hd14723 (by
      simp only [List.length_cons]
      omega)
  have rd14725 := by
    simpa using rd14724.swap1 hd14724 (by
      simp only [List.length_cons]
      omega)
  have rd14726 := by
    simpa [getTickHiWord] using RD.sar rd14725 hd14725 (by
      simp only [List.length_cons]
      omega)
  have rd14728 := by
    simpa using rd14726.push1 ⟨2⟩ hd14726 (by
      simp only [List.length_cons]
      omega)
  have rd14729 := by
    simpa using rd14728.dup2 hd14728 (by
      simp only [List.length_cons]
      omega)
  have rd14730 := by
    simpa using rd14729.dup2 hd14729 (by
      simp only [List.length_cons]
      omega)
  have rd14731 := by
    simpa [getTickHiInt24Word] using RD.signextend rd14730 hd14730 (by
      simp only [List.length_cons]
      omega)
  have rd14732 := by
    simpa using rd14731.swap1 hd14731 (by
      simp only [List.length_cons]
      omega)
  have rd14733 := by
    simpa using rd14732.dup4 hd14732 (by
      simp only [List.length_cons]
      omega)
  have rd14734 := by
    simpa using rd14733.swap1 hd14733 (by
      simp only [List.length_cons]
      omega)
  have rd14735 := by
    simpa [getTickLowInt24Word] using RD.signextend rd14734 hd14734 (by
      simp only [List.length_cons]
      omega)
  have rd14736 := by
    simpa [getTickLowEqHiWord] using rd14735.eq hd14735 (by
      simp only [List.length_cons]
      omega)
  have rd14739 := by
    simpa using rd14736.push2 ⟨14786⟩ hd14736 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14739⟩

end Benchmarks.UniswapV3Pool
