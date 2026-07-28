import Benchmarks.UniswapV3Pool.InitializeGetTick

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

abbrev getTickLogRSquared61Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.mul (getTickLogRAfter62Word ee) (getTickLogRAfter62Word ee)

abbrev getTickLogRShifted61Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared61Word ee) ⟨127⟩

abbrev getTickLogF61Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared61Word ee) ⟨255⟩

abbrev getTickLogRAfter61Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRShifted61Word ee) (getTickLogF61Word ee)

abbrev getTickLogRSquared60Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.mul (getTickLogRAfter61Word ee) (getTickLogRAfter61Word ee)

abbrev getTickLogRShifted60Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared60Word ee) ⟨127⟩

abbrev getTickLogF60Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared60Word ee) ⟨255⟩

abbrev getTickLogRAfter60Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRShifted60Word ee) (getTickLogF60Word ee)

def getTickLogRSquared59Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.mul (getTickLogRAfter60Word ee) (getTickLogRAfter60Word ee)

def getTickLogRShifted59Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared59Word ee) ⟨127⟩

def getTickLogF59Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared59Word ee) ⟨255⟩

def getTickLogRAfter59Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRShifted59Word ee) (getTickLogF59Word ee)

def getTickLogRSquared58Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.mul (getTickLogRAfter59Word ee) (getTickLogRAfter59Word ee)

def getTickLogRShifted58Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared58Word ee) ⟨127⟩

def getTickLogF58Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared58Word ee) ⟨255⟩

def getTickLogRAfter58Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRShifted58Word ee) (getTickLogF58Word ee)

def getTickLogRSquared57Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.mul (getTickLogRAfter58Word ee) (getTickLogRAfter58Word ee)

def getTickLogRShifted57Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared57Word ee) ⟨127⟩

def getTickLogF57Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared57Word ee) ⟨255⟩

def getTickLogRAfter57Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRShifted57Word ee) (getTickLogF57Word ee)

def getTickLogRSquared56Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.mul (getTickLogRAfter57Word ee) (getTickLogRAfter57Word ee)

def getTickLogRShifted56Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared56Word ee) ⟨127⟩

def getTickLogF56Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared56Word ee) ⟨255⟩

def getTickLogRAfter56Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRShifted56Word ee) (getTickLogF56Word ee)

def getTickLogRSquared55Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.mul (getTickLogRAfter56Word ee) (getTickLogRAfter56Word ee)

def getTickLogRShifted55Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared55Word ee) ⟨127⟩

def getTickLogF55Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared55Word ee) ⟨255⟩

def getTickLogRAfter55Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRShifted55Word ee) (getTickLogF55Word ee)

def getTickLogRSquared54Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.mul (getTickLogRAfter55Word ee) (getTickLogRAfter55Word ee)

def getTickLogRShifted54Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared54Word ee) ⟨127⟩

def getTickLogF54Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared54Word ee) ⟨255⟩

def getTickLogRAfter54Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRShifted54Word ee) (getTickLogF54Word ee)

def getTickLogRSquared53Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.mul (getTickLogRAfter54Word ee) (getTickLogRAfter54Word ee)

def getTickLogRShifted53Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared53Word ee) ⟨127⟩

def getTickLogF53Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared53Word ee) ⟨255⟩

def getTickLogRAfter53Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRShifted53Word ee) (getTickLogF53Word ee)

def getTickLogRSquared52Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.mul (getTickLogRAfter53Word ee) (getTickLogRAfter53Word ee)

def getTickLogRShifted52Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared52Word ee) ⟨127⟩

def getTickLogF52Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared52Word ee) ⟨255⟩

def getTickLogRAfter52Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRShifted52Word ee) (getTickLogF52Word ee)

def getTickLogRSquared51Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.mul (getTickLogRAfter52Word ee) (getTickLogRAfter52Word ee)

def getTickLogRShifted51Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared51Word ee) ⟨127⟩

def getTickLogF51Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRSquared51Word ee) ⟨255⟩

def getTickLogRAfter51Word (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (getTickLogRShifted51Word ee) (getTickLogF51Word ee)

-- LIBRARY CANDIDATE: fills the missing `Reasoning.Theory` wrapper for EVM `DUP12`.
theorem dup12_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP12, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
    (hov : t.length + 13 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP12, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup12 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll ::
          t).length - 12 + 13 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- LIBRARY CANDIDATE: companion `RD` combinator for the missing `DUP12` wrapper.
theorem RD.dup12 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP12, .none)) (hov : t.length + 13 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup12_xstep hc hp hdec hs hov)

-- LIBRARY CANDIDATE: fills the missing `Reasoning.Theory` wrapper for EVM `SWAP13`.
theorem swap13_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP13, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: t)
    (hov : t.length + 14 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (nn :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
              a :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP13, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap13 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
          nn :: t).length - 14 + 14 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- LIBRARY CANDIDATE: companion `RD` combinator for the missing `SWAP13` wrapper.
theorem RD.swap13 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP13, .none)) (hov : t.length + 14 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (nn :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap13_xstep hc hp hdec hs hov)

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioLogStep61 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14300⟩
      (getTickLogRAfter62Word ee :: getTickLogRSquared62Word ee :: ⟨255⟩ ::
        ⟨127⟩ :: getTickLogRSquared63Word ee :: getTickMsbWord ee ::
          getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
            initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14309⟩
      (getTickLogRAfter61Word ee :: getTickLogRSquared61Word ee ::
        getTickLogRSquared62Word ee :: ⟨255⟩ :: ⟨127⟩ ::
          getTickLogRSquared63Word ee :: getTickMsbWord ee :: getTickRatioWord ee ::
          ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
            initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14300 : decode code ⟨14300⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14301 : decode code ⟨14301⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14302 : decode code ⟨14302⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14303 : decode code ⟨14303⟩ = some (.DUP5, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14304 : decode code ⟨14304⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14305 : decode code ⟨14305⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14306 : decode code ⟨14306⟩ = some (.DUP5, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14307 : decode code ⟨14307⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14308 : decode code ⟨14308⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14301 := by
    simpa using h.dup1 hd14300 (by
      simp only [List.length_cons]
      omega)
  have rd14302 := by
    simpa [getTickLogRSquared61Word] using rd14301.mul hd14301 (by
      simp only [List.length_cons]
      omega)
  have rd14303 := by
    simpa using rd14302.dup1 hd14302 (by
      simp only [List.length_cons]
      omega)
  have rd14304 := by
    simpa using rd14303.dup5 hd14303 (by
      simp only [List.length_cons]
      omega)
  have rd14305 := by
    simpa [getTickLogRShifted61Word] using rd14304.shr hd14304 (by
      simp only [List.length_cons]
      omega)
  have rd14306 := by
    simpa using rd14305.dup2 hd14305 (by
      simp only [List.length_cons]
      omega)
  have rd14307 := by
    simpa using rd14306.dup5 hd14306 (by
      simp only [List.length_cons]
      omega)
  have rd14308 := by
    simpa [getTickLogF61Word] using rd14307.shr hd14307 (by
      simp only [List.length_cons]
      omega)
  have rd14309 := by
    simpa [getTickLogRAfter61Word] using rd14308.shr hd14308 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14309⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioLogStep60 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14309⟩
      (getTickLogRAfter61Word ee :: getTickLogRSquared61Word ee ::
        getTickLogRSquared62Word ee :: ⟨255⟩ :: ⟨127⟩ ::
          getTickLogRSquared63Word ee :: getTickMsbWord ee :: getTickRatioWord ee ::
          ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
            initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 19 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14318⟩
      (getTickLogRAfter60Word ee :: getTickLogRSquared60Word ee ::
        getTickLogRSquared61Word ee :: getTickLogRSquared62Word ee ::
          ⟨255⟩ :: ⟨127⟩ :: getTickLogRSquared63Word ee :: getTickMsbWord ee ::
            getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
              initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14309 : decode code ⟨14309⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14310 : decode code ⟨14310⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14311 : decode code ⟨14311⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14312 : decode code ⟨14312⟩ = some (.DUP6, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14313 : decode code ⟨14313⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14314 : decode code ⟨14314⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14315 : decode code ⟨14315⟩ = some (.DUP6, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14316 : decode code ⟨14316⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14317 : decode code ⟨14317⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14310 := by
    simpa using h.dup1 hd14309 (by
      simp only [List.length_cons]
      omega)
  have rd14311 := by
    simpa [getTickLogRSquared60Word] using rd14310.mul hd14310 (by
      simp only [List.length_cons]
      omega)
  have rd14312 := by
    simpa using rd14311.dup1 hd14311 (by
      simp only [List.length_cons]
      omega)
  have rd14313 := by
    simpa using rd14312.dup6 hd14312 (by
      simp only [List.length_cons]
      omega)
  have rd14314 := by
    simpa [getTickLogRShifted60Word] using rd14313.shr hd14313 (by
      simp only [List.length_cons]
      omega)
  have rd14315 := by
    simpa using rd14314.dup2 hd14314 (by
      simp only [List.length_cons]
      omega)
  have rd14316 := by
    simpa using rd14315.dup6 hd14315 (by
      simp only [List.length_cons]
      omega)
  have rd14317 := by
    simpa [getTickLogF60Word] using rd14316.shr hd14316 (by
      simp only [List.length_cons]
      omega)
  have rd14318 := by
    simpa [getTickLogRAfter60Word] using rd14317.shr hd14317 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14318⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioLogStep59 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14318⟩
      (getTickLogRAfter60Word ee :: getTickLogRSquared60Word ee ::
        getTickLogRSquared61Word ee :: getTickLogRSquared62Word ee ::
          ⟨255⟩ :: ⟨127⟩ :: getTickLogRSquared63Word ee :: getTickMsbWord ee ::
            getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
              initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14327⟩
      (getTickLogRAfter59Word ee :: getTickLogRSquared59Word ee ::
        getTickLogRSquared60Word ee :: getTickLogRSquared61Word ee ::
          getTickLogRSquared62Word ee :: ⟨255⟩ :: ⟨127⟩ ::
            getTickLogRSquared63Word ee :: getTickMsbWord ee :: getTickRatioWord ee ::
              ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
                initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14318 : decode code ⟨14318⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14319 : decode code ⟨14319⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14320 : decode code ⟨14320⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14321 : decode code ⟨14321⟩ = some (.DUP7, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14322 : decode code ⟨14322⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14323 : decode code ⟨14323⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14324 : decode code ⟨14324⟩ = some (.DUP7, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14325 : decode code ⟨14325⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14326 : decode code ⟨14326⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14319 := by
    simpa using h.dup1 hd14318 (by
      simp only [List.length_cons]
      omega)
  have rd14320 := by
    simpa [getTickLogRSquared59Word] using rd14319.mul hd14319 (by
      simp only [List.length_cons]
      omega)
  have rd14321 := by
    simpa using rd14320.dup1 hd14320 (by
      simp only [List.length_cons]
      omega)
  have rd14322 := by
    simpa using rd14321.dup7 hd14321 (by
      simp only [List.length_cons]
      omega)
  have rd14323 := by
    simpa [getTickLogRShifted59Word] using rd14322.shr hd14322 (by
      simp only [List.length_cons]
      omega)
  have rd14324 := by
    simpa using rd14323.dup2 hd14323 (by
      simp only [List.length_cons]
      omega)
  have rd14325 := by
    simpa using rd14324.dup7 hd14324 (by
      simp only [List.length_cons]
      omega)
  have rd14326 := by
    simpa [getTickLogF59Word] using rd14325.shr hd14325 (by
      simp only [List.length_cons]
      omega)
  have rd14327 := by
    simpa [getTickLogRAfter59Word] using rd14326.shr hd14326 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14327⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioLogStep58 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14327⟩
      (getTickLogRAfter59Word ee :: getTickLogRSquared59Word ee ::
        getTickLogRSquared60Word ee :: getTickLogRSquared61Word ee ::
          getTickLogRSquared62Word ee :: ⟨255⟩ :: ⟨127⟩ ::
            getTickLogRSquared63Word ee :: getTickMsbWord ee :: getTickRatioWord ee ::
              ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
                initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14336⟩
      (getTickLogRAfter58Word ee :: getTickLogRSquared58Word ee ::
        getTickLogRSquared59Word ee :: getTickLogRSquared60Word ee ::
          getTickLogRSquared61Word ee :: getTickLogRSquared62Word ee ::
            ⟨255⟩ :: ⟨127⟩ :: getTickLogRSquared63Word ee :: getTickMsbWord ee ::
              getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ ::
                ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14327 : decode code ⟨14327⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14328 : decode code ⟨14328⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14329 : decode code ⟨14329⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14330 : decode code ⟨14330⟩ = some (.DUP8, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14331 : decode code ⟨14331⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14332 : decode code ⟨14332⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14333 : decode code ⟨14333⟩ = some (.DUP8, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14334 : decode code ⟨14334⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14335 : decode code ⟨14335⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14328 := by
    simpa using h.dup1 hd14327 (by
      simp only [List.length_cons]
      omega)
  have rd14329 := by
    simpa [getTickLogRSquared58Word] using rd14328.mul hd14328 (by
      simp only [List.length_cons]
      omega)
  have rd14330 := by
    simpa using rd14329.dup1 hd14329 (by
      simp only [List.length_cons]
      omega)
  have rd14331 := by
    simpa using rd14330.dup8 hd14330 (by
      simp only [List.length_cons]
      omega)
  have rd14332 := by
    simpa [getTickLogRShifted58Word] using rd14331.shr hd14331 (by
      simp only [List.length_cons]
      omega)
  have rd14333 := by
    simpa using rd14332.dup2 hd14332 (by
      simp only [List.length_cons]
      omega)
  have rd14334 := by
    simpa using rd14333.dup8 hd14333 (by
      simp only [List.length_cons]
      omega)
  have rd14335 := by
    simpa [getTickLogF58Word] using rd14334.shr hd14334 (by
      simp only [List.length_cons]
      omega)
  have rd14336 := by
    simpa [getTickLogRAfter58Word] using rd14335.shr hd14335 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14336⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioLogStep57 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14336⟩
      (getTickLogRAfter58Word ee :: getTickLogRSquared58Word ee ::
        getTickLogRSquared59Word ee :: getTickLogRSquared60Word ee ::
          getTickLogRSquared61Word ee :: getTickLogRSquared62Word ee ::
            ⟨255⟩ :: ⟨127⟩ :: getTickLogRSquared63Word ee :: getTickMsbWord ee ::
              getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ ::
                ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14345⟩
      (getTickLogRAfter57Word ee :: getTickLogRSquared57Word ee ::
        getTickLogRSquared58Word ee :: getTickLogRSquared59Word ee ::
          getTickLogRSquared60Word ee :: getTickLogRSquared61Word ee ::
            getTickLogRSquared62Word ee :: ⟨255⟩ :: ⟨127⟩ ::
              getTickLogRSquared63Word ee :: getTickMsbWord ee :: getTickRatioWord ee ::
                ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
                  initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14336 : decode code ⟨14336⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14337 : decode code ⟨14337⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14338 : decode code ⟨14338⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14339 : decode code ⟨14339⟩ = some (.DUP9, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14340 : decode code ⟨14340⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14341 : decode code ⟨14341⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14342 : decode code ⟨14342⟩ = some (.DUP9, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14343 : decode code ⟨14343⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14344 : decode code ⟨14344⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14337 := by
    simpa using h.dup1 hd14336 (by
      simp only [List.length_cons]
      omega)
  have rd14338 := by
    simpa [getTickLogRSquared57Word] using rd14337.mul hd14337 (by
      simp only [List.length_cons]
      omega)
  have rd14339 := by
    simpa using rd14338.dup1 hd14338 (by
      simp only [List.length_cons]
      omega)
  have rd14340 := by
    simpa using rd14339.dup9 hd14339 (by
      simp only [List.length_cons]
      omega)
  have rd14341 := by
    simpa [getTickLogRShifted57Word] using rd14340.shr hd14340 (by
      simp only [List.length_cons]
      omega)
  have rd14342 := by
    simpa using rd14341.dup2 hd14341 (by
      simp only [List.length_cons]
      omega)
  have rd14343 := by
    simpa using rd14342.dup9 hd14342 (by
      simp only [List.length_cons]
      omega)
  have rd14344 := by
    simpa [getTickLogF57Word] using rd14343.shr hd14343 (by
      simp only [List.length_cons]
      omega)
  have rd14345 := by
    simpa [getTickLogRAfter57Word] using rd14344.shr hd14344 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14345⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioLogStep56 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14345⟩
      (getTickLogRAfter57Word ee :: getTickLogRSquared57Word ee ::
        getTickLogRSquared58Word ee :: getTickLogRSquared59Word ee ::
          getTickLogRSquared60Word ee :: getTickLogRSquared61Word ee ::
            getTickLogRSquared62Word ee :: ⟨255⟩ :: ⟨127⟩ ::
              getTickLogRSquared63Word ee :: getTickMsbWord ee :: getTickRatioWord ee ::
                ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
                  initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 23 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14354⟩
      (getTickLogRAfter56Word ee :: getTickLogRSquared56Word ee ::
        getTickLogRSquared57Word ee :: getTickLogRSquared58Word ee ::
          getTickLogRSquared59Word ee :: getTickLogRSquared60Word ee ::
            getTickLogRSquared61Word ee :: getTickLogRSquared62Word ee ::
              ⟨255⟩ :: ⟨127⟩ :: getTickLogRSquared63Word ee :: getTickMsbWord ee ::
                getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ ::
                  ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14345 : decode code ⟨14345⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14346 : decode code ⟨14346⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14347 : decode code ⟨14347⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14348 : decode code ⟨14348⟩ = some (.DUP10, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14349 : decode code ⟨14349⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14350 : decode code ⟨14350⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14351 : decode code ⟨14351⟩ = some (.DUP10, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14352 : decode code ⟨14352⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14353 : decode code ⟨14353⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14346 := by
    simpa using h.dup1 hd14345 (by
      simp only [List.length_cons]
      omega)
  have rd14347 := by
    simpa [getTickLogRSquared56Word] using rd14346.mul hd14346 (by
      simp only [List.length_cons]
      omega)
  have rd14348 := by
    simpa using rd14347.dup1 hd14347 (by
      simp only [List.length_cons]
      omega)
  have rd14349 := by
    simpa using rd14348.dup10 hd14348 (by
      simp only [List.length_cons]
      omega)
  have rd14350 := by
    simpa [getTickLogRShifted56Word] using rd14349.shr hd14349 (by
      simp only [List.length_cons]
      omega)
  have rd14351 := by
    simpa using rd14350.dup2 hd14350 (by
      simp only [List.length_cons]
      omega)
  have rd14352 := by
    simpa using rd14351.dup10 hd14351 (by
      simp only [List.length_cons]
      omega)
  have rd14353 := by
    simpa [getTickLogF56Word] using rd14352.shr hd14352 (by
      simp only [List.length_cons]
      omega)
  have rd14354 := by
    simpa [getTickLogRAfter56Word] using rd14353.shr hd14353 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14354⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioLogStep55 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14354⟩
      (getTickLogRAfter56Word ee :: getTickLogRSquared56Word ee ::
        getTickLogRSquared57Word ee :: getTickLogRSquared58Word ee ::
          getTickLogRSquared59Word ee :: getTickLogRSquared60Word ee ::
            getTickLogRSquared61Word ee :: getTickLogRSquared62Word ee ::
              ⟨255⟩ :: ⟨127⟩ :: getTickLogRSquared63Word ee :: getTickMsbWord ee ::
                getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ ::
                  ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14363⟩
      (getTickLogRAfter55Word ee :: getTickLogRSquared55Word ee ::
        getTickLogRSquared56Word ee :: getTickLogRSquared57Word ee ::
          getTickLogRSquared58Word ee :: getTickLogRSquared59Word ee ::
            getTickLogRSquared60Word ee :: getTickLogRSquared61Word ee ::
              getTickLogRSquared62Word ee :: ⟨255⟩ :: ⟨127⟩ ::
                getTickLogRSquared63Word ee :: getTickMsbWord ee :: getTickRatioWord ee ::
                  ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
                    initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14354 : decode code ⟨14354⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14355 : decode code ⟨14355⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14356 : decode code ⟨14356⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14357 : decode code ⟨14357⟩ = some (.DUP11, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14358 : decode code ⟨14358⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14359 : decode code ⟨14359⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14360 : decode code ⟨14360⟩ = some (.DUP11, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14361 : decode code ⟨14361⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14362 : decode code ⟨14362⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14355 := by
    simpa using h.dup1 hd14354 (by
      simp only [List.length_cons]
      omega)
  have rd14356 := by
    simpa [getTickLogRSquared55Word] using rd14355.mul hd14355 (by
      simp only [List.length_cons]
      omega)
  have rd14357 := by
    simpa using rd14356.dup1 hd14356 (by
      simp only [List.length_cons]
      omega)
  have rd14358 := by
    simpa using rd14357.dup11 hd14357 (by
      simp only [List.length_cons]
      omega)
  have rd14359 := by
    simpa [getTickLogRShifted55Word] using rd14358.shr hd14358 (by
      simp only [List.length_cons]
      omega)
  have rd14360 := by
    simpa using rd14359.dup2 hd14359 (by
      simp only [List.length_cons]
      omega)
  have rd14361 := by
    simpa using rd14360.dup11 hd14360 (by
      simp only [List.length_cons]
      omega)
  have rd14362 := by
    simpa [getTickLogF55Word] using rd14361.shr hd14361 (by
      simp only [List.length_cons]
      omega)
  have rd14363 := by
    simpa [getTickLogRAfter55Word] using rd14362.shr hd14362 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14363⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioLogStep54 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14363⟩
      (getTickLogRAfter55Word ee :: getTickLogRSquared55Word ee ::
        getTickLogRSquared56Word ee :: getTickLogRSquared57Word ee ::
          getTickLogRSquared58Word ee :: getTickLogRSquared59Word ee ::
            getTickLogRSquared60Word ee :: getTickLogRSquared61Word ee ::
              getTickLogRSquared62Word ee :: ⟨255⟩ :: ⟨127⟩ ::
                getTickLogRSquared63Word ee :: getTickMsbWord ee :: getTickRatioWord ee ::
                  ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
                    initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 25 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14372⟩
      (getTickLogRAfter54Word ee :: getTickLogRSquared54Word ee ::
        getTickLogRSquared55Word ee :: getTickLogRSquared56Word ee ::
          getTickLogRSquared57Word ee :: getTickLogRSquared58Word ee ::
            getTickLogRSquared59Word ee :: getTickLogRSquared60Word ee ::
              getTickLogRSquared61Word ee :: getTickLogRSquared62Word ee ::
                ⟨255⟩ :: ⟨127⟩ :: getTickLogRSquared63Word ee :: getTickMsbWord ee ::
                  getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ ::
                    ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14363 : decode code ⟨14363⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14364 : decode code ⟨14364⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14365 : decode code ⟨14365⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14366 : decode code ⟨14366⟩ = some (.DUP12, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14367 : decode code ⟨14367⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14368 : decode code ⟨14368⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14369 : decode code ⟨14369⟩ = some (.DUP12, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14370 : decode code ⟨14370⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14371 : decode code ⟨14371⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14364 := by
    simpa using h.dup1 hd14363 (by
      simp only [List.length_cons]
      omega)
  have rd14365 := by
    simpa [getTickLogRSquared54Word] using rd14364.mul hd14364 (by
      simp only [List.length_cons]
      omega)
  have rd14366 := by
    simpa using rd14365.dup1 hd14365 (by
      simp only [List.length_cons]
      omega)
  have rd14367 := by
    simpa using RD.dup12 rd14366 hd14366 (by
      simp only [List.length_cons]
      omega)
  have rd14368 := by
    simpa [getTickLogRShifted54Word] using rd14367.shr hd14367 (by
      simp only [List.length_cons]
      omega)
  have rd14369 := by
    simpa using rd14368.dup2 hd14368 (by
      simp only [List.length_cons]
      omega)
  have rd14370 := by
    simpa using RD.dup12 rd14369 hd14369 (by
      simp only [List.length_cons]
      omega)
  have rd14371 := by
    simpa [getTickLogF54Word] using rd14370.shr hd14370 (by
      simp only [List.length_cons]
      omega)
  have rd14372 := by
    simpa [getTickLogRAfter54Word] using rd14371.shr hd14371 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14372⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioLogStep53 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14372⟩
      (getTickLogRAfter54Word ee :: getTickLogRSquared54Word ee ::
        getTickLogRSquared55Word ee :: getTickLogRSquared56Word ee ::
          getTickLogRSquared57Word ee :: getTickLogRSquared58Word ee ::
            getTickLogRSquared59Word ee :: getTickLogRSquared60Word ee ::
              getTickLogRSquared61Word ee :: getTickLogRSquared62Word ee ::
                ⟨255⟩ :: ⟨127⟩ :: getTickLogRSquared63Word ee :: getTickMsbWord ee ::
                  getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ ::
                    ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14381⟩
      (getTickLogRAfter53Word ee :: getTickLogRSquared53Word ee ::
        getTickLogRSquared54Word ee :: getTickLogRSquared55Word ee ::
          getTickLogRSquared56Word ee :: getTickLogRSquared57Word ee ::
            getTickLogRSquared58Word ee :: getTickLogRSquared59Word ee ::
              getTickLogRSquared60Word ee :: getTickLogRSquared61Word ee ::
                getTickLogRSquared62Word ee :: ⟨255⟩ :: ⟨127⟩ ::
                  getTickLogRSquared63Word ee :: getTickMsbWord ee :: getTickRatioWord ee ::
                    ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
                      initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14372 : decode code ⟨14372⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14373 : decode code ⟨14373⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14374 : decode code ⟨14374⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14375 : decode code ⟨14375⟩ = some (.DUP13, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14376 : decode code ⟨14376⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14377 : decode code ⟨14377⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14378 : decode code ⟨14378⟩ = some (.DUP13, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14379 : decode code ⟨14379⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14380 : decode code ⟨14380⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14373 := by
    simpa using h.dup1 hd14372 (by
      simp only [List.length_cons]
      omega)
  have rd14374 := by
    simpa [getTickLogRSquared53Word] using rd14373.mul hd14373 (by
      simp only [List.length_cons]
      omega)
  have rd14375 := by
    simpa using rd14374.dup1 hd14374 (by
      simp only [List.length_cons]
      omega)
  have rd14376 := by
    simpa using rd14375.dup13 hd14375 (by
      simp only [List.length_cons]
      omega)
  have rd14377 := by
    simpa [getTickLogRShifted53Word] using rd14376.shr hd14376 (by
      simp only [List.length_cons]
      omega)
  have rd14378 := by
    simpa using rd14377.dup2 hd14377 (by
      simp only [List.length_cons]
      omega)
  have rd14379 := by
    simpa using rd14378.dup13 hd14378 (by
      simp only [List.length_cons]
      omega)
  have rd14380 := by
    simpa [getTickLogF53Word] using rd14379.shr hd14379 (by
      simp only [List.length_cons]
      omega)
  have rd14381 := by
    simpa [getTickLogRAfter53Word] using rd14380.shr hd14380 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14381⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioLogStep52 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14381⟩
      (getTickLogRAfter53Word ee :: getTickLogRSquared53Word ee ::
        getTickLogRSquared54Word ee :: getTickLogRSquared55Word ee ::
          getTickLogRSquared56Word ee :: getTickLogRSquared57Word ee ::
            getTickLogRSquared58Word ee :: getTickLogRSquared59Word ee ::
              getTickLogRSquared60Word ee :: getTickLogRSquared61Word ee ::
                getTickLogRSquared62Word ee :: ⟨255⟩ :: ⟨127⟩ ::
                  getTickLogRSquared63Word ee :: getTickMsbWord ee :: getTickRatioWord ee ::
                    ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ ::
                      initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 27 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14390⟩
      (getTickLogRAfter52Word ee :: getTickLogRSquared52Word ee ::
        getTickLogRSquared53Word ee :: getTickLogRSquared54Word ee ::
          getTickLogRSquared55Word ee :: getTickLogRSquared56Word ee ::
            getTickLogRSquared57Word ee :: getTickLogRSquared58Word ee ::
              getTickLogRSquared59Word ee :: getTickLogRSquared60Word ee ::
                getTickLogRSquared61Word ee :: getTickLogRSquared62Word ee ::
                  ⟨255⟩ :: ⟨127⟩ :: getTickLogRSquared63Word ee :: getTickMsbWord ee ::
                    getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ ::
                      ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14381 : decode code ⟨14381⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14382 : decode code ⟨14382⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14383 : decode code ⟨14383⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14384 : decode code ⟨14384⟩ = some (.DUP14, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14385 : decode code ⟨14385⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14386 : decode code ⟨14386⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14387 : decode code ⟨14387⟩ = some (.DUP14, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14388 : decode code ⟨14388⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14389 : decode code ⟨14389⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14382 := by
    simpa using h.dup1 hd14381 (by
      simp only [List.length_cons]
      omega)
  have rd14383 := by
    simpa [getTickLogRSquared52Word] using rd14382.mul hd14382 (by
      simp only [List.length_cons]
      omega)
  have rd14384 := by
    simpa using rd14383.dup1 hd14383 (by
      simp only [List.length_cons]
      omega)
  have rd14385 := by
    simpa using rd14384.dup14 hd14384 (by
      simp only [List.length_cons]
      omega)
  have rd14386 := by
    simpa [getTickLogRShifted52Word] using rd14385.shr hd14385 (by
      simp only [List.length_cons]
      omega)
  have rd14387 := by
    simpa using rd14386.dup2 hd14386 (by
      simp only [List.length_cons]
      omega)
  have rd14388 := by
    simpa using rd14387.dup14 hd14387 (by
      simp only [List.length_cons]
      omega)
  have rd14389 := by
    simpa [getTickLogF52Word] using rd14388.shr hd14388 (by
      simp only [List.length_cons]
      omega)
  have rd14390 := by
    simpa [getTickLogRAfter52Word] using rd14389.shr hd14389 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14390⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioLogStep51 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14390⟩
      (getTickLogRAfter52Word ee :: getTickLogRSquared52Word ee ::
        getTickLogRSquared53Word ee :: getTickLogRSquared54Word ee ::
          getTickLogRSquared55Word ee :: getTickLogRSquared56Word ee ::
            getTickLogRSquared57Word ee :: getTickLogRSquared58Word ee ::
              getTickLogRSquared59Word ee :: getTickLogRSquared60Word ee ::
                getTickLogRSquared61Word ee :: getTickLogRSquared62Word ee ::
                  ⟨255⟩ :: ⟨127⟩ :: getTickLogRSquared63Word ee :: getTickMsbWord ee ::
                    getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee :: ⟨10793⟩ ::
                      ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 28 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨14403⟩
      (getTickLogRAfter51Word ee :: getTickLogRSquared52Word ee ::
        getTickLogRSquared53Word ee :: getTickLogRSquared54Word ee ::
          getTickLogRSquared55Word ee :: getTickLogRSquared56Word ee ::
            getTickLogRSquared57Word ee :: getTickLogRSquared58Word ee ::
              getTickLogRSquared59Word ee :: getTickLogRSquared60Word ee ::
                getTickLogRSquared61Word ee :: getTickLogRSquared62Word ee ::
                  getTickLogRSquared51Word ee :: ⟨127⟩ :: getTickLogRSquared63Word ee ::
                    getTickMsbWord ee :: getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee ::
                      ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14390 : decode code ⟨14390⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14391 : decode code ⟨14391⟩ = some (.MUL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14392 : decode code ⟨14392⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14393 : decode code ⟨14393⟩ = some (.DUP15, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14394 : decode code ⟨14394⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14395 : decode code ⟨14395⟩ = some (.SWAP13, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14396 : decode code ⟨14396⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14397 : decode code ⟨14397⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14398 : decode code ⟨14398⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14399 : decode code ⟨14399⟩ = some (.SWAP13, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14400 : decode code ⟨14400⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14401 : decode code ⟨14401⟩ = some (.SWAP13, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14402 : decode code ⟨14402⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14391 := by
    simpa using h.dup1 hd14390 (by
      simp only [List.length_cons]
      omega)
  have rd14392 := by
    simpa [getTickLogRSquared51Word] using rd14391.mul hd14391 (by
      simp only [List.length_cons]
      omega)
  have rd14393 := by
    simpa using rd14392.dup1 hd14392 (by
      simp only [List.length_cons]
      omega)
  have rd14394 := by
    simpa using rd14393.dup15 hd14393 (by
      simp only [List.length_cons]
      omega)
  have rd14395 := by
    simpa [getTickLogRShifted51Word] using rd14394.shr hd14394 (by
      simp only [List.length_cons]
      omega)
  have rd14396 := by
    simpa using RD.swap13 rd14395 hd14395 (by
      simp only [List.length_cons]
      omega)
  have rd14397 := by
    simpa using rd14396.dup2 hd14396 (by
      simp only [List.length_cons]
      omega)
  have rd14398 := by
    simpa using rd14397.swap1 hd14397 (by
      simp only [List.length_cons]
      omega)
  have rd14399 := by
    simpa [getTickLogF51Word] using rd14398.shr hd14398 (by
      simp only [List.length_cons]
      omega)
  have rd14400 := by
    simpa using RD.swap13 rd14399 hd14399 (by
      simp only [List.length_cons]
      omega)
  have rd14401 := by
    simpa using rd14400.swap1 hd14400 (by
      simp only [List.length_cons]
      omega)
  have rd14402 := by
    simpa using RD.swap13 rd14401 hd14401 (by
      simp only [List.length_cons]
      omega)
  have rd14403 := by
    simpa [getTickLogRAfter51Word] using rd14402.shr hd14402 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd14403⟩

end Benchmarks.UniswapV3Pool
