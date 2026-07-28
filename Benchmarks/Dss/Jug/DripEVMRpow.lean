import Benchmarks.Dss.Jug.DripEVMVat

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Jug

theorem RD.jugDripToRpowRoutine
    {cA cA' gh bl σ σ' σ₀ A I} {g sel fee : UInt256}
    {out : ByteArray} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size) (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (rd1485 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1485⟩
      (fee :: ⟨1524⟩ :: ⟨1530⟩ :: dripVatIlksPrevWord out :: ⟨0⟩ ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩ (dripVatIlksPostCallMem I out))
      (UInt256.ofNat 6) out (cA', σ') k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2153⟩
      (jugRay :: UInt256.sub (UInt256.ofNat I.header.timestamp)
          (jugSlotWord (fileDutyRhoSlotFor I) σ' I) ::
        fee :: ⟨1524⟩ :: ⟨1530⟩ :: dripVatIlksPrevWord out :: ⟨0⟩ ::
        fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
        (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩ (dripVatIlksPostCallMem I out)))
      (UInt256.ofNat 6) out (cA', σ') k' C' := by
  let mem0 := twoWordHashMem (fileDutyIlkWord I) ⟨1⟩ (dripVatIlksPostCallMem I out)
  let mem1 := twoWordHashMem (fileDutyIlkWord I) ⟨1⟩ mem0
  have hpostSize : 64 ≤ (dripVatIlksPostCallMem I out).size := by
    rw [dripVatIlksPostCallMem_size_long I out hlo hout]
    omega
  have hmem0 : 64 ≤ mem0.size := by
    change 64 ≤ (twoWordHashMem (fileDutyIlkWord I) ⟨1⟩
      (dripVatIlksPostCallMem I out)).size
    rw [drip_twoWordHashMem_size_of_ge64 (fileDutyIlkWord I) (⟨1⟩ : UInt256) hpostSize]
    exact hpostSize
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (mem1.readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (fileDutyIlkWord I) := by
    change UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem (fileDutyIlkWord I) ⟨1⟩ mem0).readWithPadding 0 64))) =
      solcMappingSlot ⟨1⟩ (fileDutyIlkWord I)
    exact drip_twoWordHashMem_solcMappingSlot_of_ge64 (⟨1⟩ : UInt256)
      (fileDutyIlkWord I) hmem0
  have rd1489 := evm_run rd1485 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1491 := rd1489.mstore 0 (wordAt0Mem (fileDutyIlkWord I) mem0)
    (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1497 := evm_run rd1491 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1498 := rd1497.mstore 0 mem1
    (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1502 := evm_run rd1498 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd1503 := rd1502.keccak256 0 (solcMappingSlot ⟨1⟩ (fileDutyIlkWord I))
    (UInt256.ofNat 6) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rd1504 := rd1503.add (by native_decide) (by evm_ov)
  obtain ⟨k1505, C1505, rd1505raw⟩ := rd1504.sload (by native_decide) (by evm_ov)
  have rd1505 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1505⟩
      (jugSlotWord (fileDutyRhoSlotFor I) σ' I :: fee :: ⟨1524⟩ :: ⟨1530⟩ ::
        dripVatIlksPrevWord out :: ⟨0⟩ :: fileDutyIlkWord I :: ⟨357⟩ :: sel :: [])
      mem1 (UInt256.ofNat 6) out (cA', σ') k1505 C1505 := by
    simpa [jugSlotWord, solcSlotWord, fileDutyRhoSlotFor_eq hsz36,
      u256_add_comm] using rd1505raw
  have rd1506 := RD.timestamp rd1505 (by native_decide) (by evm_ov)
  have rd1507 := rd1506.sub (by native_decide) (by evm_ov)
  have rd1520 := rd1507.pushConst jugRay
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd1523 := rd1520.push2 ⟨2153⟩ (by native_decide) (by evm_ov)
  have rd2153 := rd1523.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa using rd2153⟩

theorem RD.jugDripRpowNZeroReturns
    {cA gh bl σ σ₀ A I} {g b x : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (rd2153 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2153⟩
      (b :: ⟨0⟩ :: x :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1524⟩
      (b :: R) mem (UInt256.ofNat 6) out acc k' C' := by
  have rd2162 := evm_run rd2153 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2313⟩ (by native_decide) (by evm_ov)]
  by_cases hx : x = ⟨0⟩
  · have hxZero : UInt256.isZero x ≠ ⟨0⟩ := by
      rw [hx]
      decide
    have rd2313 := rd2162.jumpiT (by native_decide) hxZero (by jump_dest) (by evm_ov)
    have rd2313' := by
      simpa [hx] using rd2313
    have rd2320 := evm_run rd2313' with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw dup4 (by native_decide) (by evm_ov),
      raw dup1 (by native_decide) (by evm_ov),
      raw iszero (by native_decide) (by evm_ov),
      raw push2 ⟨2329⟩ (by native_decide) (by evm_ov)]
    have hnZero : UInt256.isZero (⟨0⟩ : UInt256) ≠ ⟨0⟩ := by decide
    have rd2329 := rd2320.jumpiT (by native_decide) hnZero (by jump_dest) (by evm_ov)
    have rd2342 := evm_run rd2329 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw dup4 (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw swap4 (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rd1524 := rd2342.jump (by native_decide) (by jump_dest) (by evm_ov)
    exact ⟨_, _, by simpa using rd1524⟩
  · have hxNonzero : UInt256.isZero x = ⟨0⟩ := isZero_eq_zero_of_ne hx
    have rd2163 := rd2162.jumpiNT (by native_decide) hxNonzero (by evm_ov)
    have rd2172 := evm_run rd2163 with [
      raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
      raw dup5 (by native_decide) (by evm_ov),
      raw and (by native_decide) (by evm_ov),
      raw dup1 (by native_decide) (by evm_ov),
      raw iszero (by native_decide) (by evm_ov),
      raw push2 ⟨2180⟩ (by native_decide) (by evm_ov)]
    have hland : UInt256.land (⟨0⟩ : UInt256) ⟨1⟩ = ⟨0⟩ := by decide
    have hoddZero : UInt256.isZero (UInt256.land (⟨0⟩ : UInt256) ⟨1⟩) ≠ ⟨0⟩ := by
      rw [hland]
      decide
    have rd2180 := rd2172.jumpiT (by native_decide) hoddZero (by jump_dest) (by evm_ov)
    have rd2196 := evm_run rd2180 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw dup4 (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
      raw dup4 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
      raw dup6 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw swap5 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov)]
    have rd2202 := evm_run rd2196 with [
      raw dup5 (by native_decide) (by evm_ov),
      raw iszero (by native_decide) (by evm_ov),
      raw push2 ⟨2307⟩ (by native_decide) (by evm_ov)]
    have hdivZero : UInt256.div (⟨0⟩ : UInt256) ⟨2⟩ = ⟨0⟩ := by decide
    have hnDone :
        UInt256.isZero (UInt256.div (⟨0⟩ : UInt256) ⟨2⟩) ≠ ⟨0⟩ := by
      rw [hdivZero]
      decide
    have rd2307 := rd2202.jumpiT (by native_decide) hnDone (by jump_dest) (by evm_ov)
    have rd2335pre := evm_run rd2307 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw push2 ⟨2335⟩ (by native_decide) (by evm_ov)]
    have rd2335 := rd2335pre.jump (by native_decide) (by jump_dest) (by evm_ov)
    have rd2342 := evm_run rd2335 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw swap4 (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rd1524 := rd2342.jump (by native_decide) (by jump_dest) (by evm_ov)
    exact ⟨_, _, by simpa [hland, hdivZero] using rd1524⟩

theorem RD.jugDripRpowNOneReturns
    {cA gh bl σ σ₀ A I} {g b x : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (rd2153 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2153⟩
      (b :: ⟨1⟩ :: x :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1524⟩
      (x :: R) mem (UInt256.ofNat 6) out acc k' C' := by
  have rd2162 := evm_run rd2153 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2313⟩ (by native_decide) (by evm_ov)]
  by_cases hx : x = ⟨0⟩
  · have hxZero : UInt256.isZero x ≠ ⟨0⟩ := by
      rw [hx]
      decide
    have rd2313 := rd2162.jumpiT (by native_decide) hxZero (by jump_dest) (by evm_ov)
    have rd2313' := by
      simpa [hx] using rd2313
    have rd2320 := evm_run rd2313' with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw dup4 (by native_decide) (by evm_ov),
      raw dup1 (by native_decide) (by evm_ov),
      raw iszero (by native_decide) (by evm_ov),
      raw push2 ⟨2329⟩ (by native_decide) (by evm_ov)]
    have hnNonzero : UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ := by decide
    have rd2321 := rd2320.jumpiNT (by native_decide) hnNonzero (by evm_ov)
    have rd2333pre := evm_run rd2321 with [
      raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw push2 ⟨2333⟩ (by native_decide) (by evm_ov)]
    have rd2333 := rd2333pre.jump (by native_decide) (by jump_dest) (by evm_ov)
    have rd2342 := evm_run rd2333 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw swap4 (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rd1524 := rd2342.jump (by native_decide) (by jump_dest) (by evm_ov)
    exact ⟨_, _, by simpa [hx] using rd1524⟩
  · have hxNonzero : UInt256.isZero x = ⟨0⟩ := isZero_eq_zero_of_ne hx
    have rd2163 := rd2162.jumpiNT (by native_decide) hxNonzero (by evm_ov)
    have rd2172 := evm_run rd2163 with [
      raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
      raw dup5 (by native_decide) (by evm_ov),
      raw and (by native_decide) (by evm_ov),
      raw dup1 (by native_decide) (by evm_ov),
      raw iszero (by native_decide) (by evm_ov),
      raw push2 ⟨2180⟩ (by native_decide) (by evm_ov)]
    have hland : UInt256.land (⟨1⟩ : UInt256) ⟨1⟩ = ⟨1⟩ := by decide
    have hoddNonzero : UInt256.isZero (UInt256.land (⟨1⟩ : UInt256) ⟨1⟩) = ⟨0⟩ := by
      rw [hland]
      decide
    have rd2173 := rd2172.jumpiNT (by native_decide) hoddNonzero (by evm_ov)
    have rd2184pre := evm_run rd2173 with [
      raw dup6 (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw push2 ⟨2184⟩ (by native_decide) (by evm_ov)]
    have rd2184 := rd2184pre.jump (by native_decide) (by jump_dest) (by evm_ov)
    have rd2196 := evm_run rd2184 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
      raw dup4 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
      raw dup6 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw swap5 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov)]
    have rd2202 := evm_run rd2196 with [
      raw dup5 (by native_decide) (by evm_ov),
      raw iszero (by native_decide) (by evm_ov),
      raw push2 ⟨2307⟩ (by native_decide) (by evm_ov)]
    have hdivOne : UInt256.div (⟨1⟩ : UInt256) ⟨2⟩ = ⟨0⟩ := by decide
    have hnDone :
        UInt256.isZero (UInt256.div (⟨1⟩ : UInt256) ⟨2⟩) ≠ ⟨0⟩ := by
      rw [hdivOne]
      decide
    have rd2307 := rd2202.jumpiT (by native_decide) hnDone (by jump_dest) (by evm_ov)
    have rd2335pre := evm_run rd2307 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw push2 ⟨2335⟩ (by native_decide) (by evm_ov)]
    have rd2335 := rd2335pre.jump (by native_decide) (by jump_dest) (by evm_ov)
    have rd2342 := evm_run rd2335 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw swap4 (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rd1524 := rd2342.jump (by native_decide) (by jump_dest) (by evm_ov)
    exact ⟨_, _, by simpa [hland, hdivOne] using rd1524⟩

theorem RD.jugDripRpowXZeroNNonzeroReturns
    {cA gh bl σ σ₀ A I} {g b n : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hnz : n ≠ ⟨0⟩)
    (rd2153 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2153⟩
      (b :: n :: ⟨0⟩ :: ⟨1524⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1524⟩
      (⟨0⟩ :: R) mem (UInt256.ofNat 6) out acc k' C' := by
  have rd2162 := evm_run rd2153 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2313⟩ (by native_decide) (by evm_ov)]
  have hxZero : UInt256.isZero (⟨0⟩ : UInt256) ≠ ⟨0⟩ := by decide
  have rd2313 := rd2162.jumpiT (by native_decide) hxZero (by jump_dest) (by evm_ov)
  have rd2320 := evm_run rd2313 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2329⟩ (by native_decide) (by evm_ov)]
  have hnNonzero : UInt256.isZero n = ⟨0⟩ := isZero_eq_zero_of_ne hnz
  have rd2321 := rd2320.jumpiNT (by native_decide) hnNonzero (by evm_ov)
  have rd2333pre := evm_run rd2321 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push2 ⟨2333⟩ (by native_decide) (by evm_ov)]
  have rd2333 := rd2333pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd2342 := evm_run rd2333 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd1524 := rd2342.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa using rd1524⟩

theorem RD.jugDripRmulReturns
    {cA gh bl σ σ₀ A I} {g pow prev : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hfit : pow.toNat * prev.toNat < UInt256.size)
    (rd1524 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1524⟩
      (pow :: ⟨1530⟩ :: prev :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1530⟩
      (UInt256.div (prev * pow) jugRay :: prev :: R) mem (UInt256.ofNat 6) out acc k' C' := by
  have rd1529 := evm_run rd1524 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨2343⟩ (by native_decide) (by evm_ov)]
  have rd2343 := rd1529.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd2353 := evm_run rd2343 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨2367⟩ (by native_decide) (by evm_ov)]
  by_cases hprev0 : prev = ⟨0⟩
  · have hcond : UInt256.isZero prev ≠ ⟨0⟩ := by
      rw [hprev0]
      decide
    have rd2367 := rd2353.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
    have rd2371 := evm_run rd2367 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨2376⟩ (by native_decide) (by evm_ov)]
    have hcond2 : UInt256.isZero prev ≠ ⟨0⟩ := by
      rw [hprev0]
      decide
    have rd2376 := rd2371.jumpiT (by native_decide) hcond2 (by jump_dest) (by evm_ov)
    have rd2377 := RD.jumpdest rd2376 (by native_decide) (by evm_ov)
    have rd2390 := rd2377.pushConst jugRay
      (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
    have rd2396 := evm_run rd2390 with [
      raw swap1 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rd1530 := rd2396.jump (by native_decide) (by jump_dest) (by evm_ov)
    exact ⟨_, _, by simpa [hprev0] using rd1530⟩
  · have hcond : UInt256.isZero prev = ⟨0⟩ := isZero_eq_zero_of_ne hprev0
    have rd2354 := rd2353.jumpiNT (by native_decide) hcond (by evm_ov)
    have rd2362 := evm_run rd2354 with [
      raw pop (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup2 (by native_decide) (by evm_ov),
      raw push2 ⟨2364⟩ (by native_decide) (by evm_ov)]
    have rd2364 := rd2362.jumpiT (by native_decide) hprev0 (by jump_dest) (by evm_ov)
    have hprevNatNe : prev.toNat ≠ 0 := by
      intro hzero
      exact hprev0 (uint256_toNat_eq_zero hzero)
    have hfit' : prev.toNat * pow.toNat < UInt256.size := by
      simpa [Nat.mul_comm] using hfit
    have hdivY : UInt256.div (prev * pow) prev = pow := by
      apply u256_inj
      rw [udiv_toNat]
      have hprod : (prev * pow).toNat = prev.toNat * pow.toNat := by
        rw [umul_toNat prev pow hfit']
      have hprevPos : 0 < prev.toNat := Nat.pos_of_ne_zero hprevNatNe
      rw [hprod]
      exact Nat.mul_div_right pow.toNat hprevPos
    have rd2368 := evm_run rd2364 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw eq (by native_decide) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨2376⟩ (by native_decide) (by evm_ov)]
    have heqCond :
        UInt256.eq (UInt256.div (prev * pow) prev) pow ≠ ⟨0⟩ := by
      rw [hdivY, u256_eq_refl]
      exact one_ne_zero_uint
    have rd2376 := rd2368.jumpiT (by native_decide) heqCond (by jump_dest) (by evm_ov)
    have rd2377 := RD.jumpdest rd2376 (by native_decide) (by evm_ov)
    have rd2390 := rd2377.pushConst jugRay
      (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
    have rd2396 := evm_run rd2390 with [
      raw swap1 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rd1530 := rd2396.jump (by native_decide) (by jump_dest) (by evm_ov)
    exact ⟨_, _, by simpa using rd1530⟩

theorem RD.jugDripRmulRayReturns
    {cA gh bl σ σ₀ A I} {g prev : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hfit : jugRay.toNat * prev.toNat < UInt256.size)
    (rd1524 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1524⟩
      (jugRay :: ⟨1530⟩ :: prev :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1530⟩
      (prev :: prev :: R) mem (UInt256.ofNat 6) out acc k' C' := by
  have hquot : UInt256.div (prev * jugRay) jugRay = prev :=
    jugRay_mul_div_cancel prev hfit
  have rd1529 := evm_run rd1524 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨2343⟩ (by native_decide) (by evm_ov)]
  have rd2343 := rd1529.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd2353 := evm_run rd2343 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨2367⟩ (by native_decide) (by evm_ov)]
  by_cases hprev0 : prev = ⟨0⟩
  · have hcond : UInt256.isZero prev ≠ ⟨0⟩ := by
      rw [hprev0]
      decide
    have rd2367 := rd2353.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
    have rd2371 := evm_run rd2367 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨2376⟩ (by native_decide) (by evm_ov)]
    have hcond2 : UInt256.isZero prev ≠ ⟨0⟩ := by
      rw [hprev0]
      decide
    have rd2376 := rd2371.jumpiT (by native_decide) hcond2 (by jump_dest) (by evm_ov)
    have rd2377 := RD.jumpdest rd2376 (by native_decide) (by evm_ov)
    have rd2390 := rd2377.pushConst jugRay
      (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
    have rd2396 := evm_run rd2390 with [
      raw swap1 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rd1530 := rd2396.jump (by native_decide) (by jump_dest) (by evm_ov)
    exact ⟨_, _, by simpa [hprev0, hquot] using rd1530⟩
  · have hcond : UInt256.isZero prev = ⟨0⟩ := isZero_eq_zero_of_ne hprev0
    have rd2354 := rd2353.jumpiNT (by native_decide) hcond (by evm_ov)
    have rd2362 := evm_run rd2354 with [
      raw pop (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup2 (by native_decide) (by evm_ov),
      raw push2 ⟨2364⟩ (by native_decide) (by evm_ov)]
    have rd2364 := rd2362.jumpiT (by native_decide) hprev0 (by jump_dest) (by evm_ov)
    have hprevNatNe : prev.toNat ≠ 0 := by
      intro hzero
      exact hprev0 (uint256_toNat_eq_zero hzero)
    have hfit' : prev.toNat * jugRay.toNat < UInt256.size := by
      simpa [Nat.mul_comm] using hfit
    have hdivY : UInt256.div (prev * jugRay) prev = jugRay := by
      apply u256_inj
      rw [udiv_toNat]
      have hprod : (prev * jugRay).toNat = prev.toNat * jugRay.toNat := by
        rw [umul_toNat prev jugRay hfit']
      have hprevPos : 0 < prev.toNat := Nat.pos_of_ne_zero hprevNatNe
      rw [hprod]
      exact Nat.mul_div_right jugRay.toNat hprevPos
    have rd2368 := evm_run rd2364 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw eq (by native_decide) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨2376⟩ (by native_decide) (by evm_ov)]
    have heqCond :
        UInt256.eq (UInt256.div (prev * jugRay) prev) jugRay ≠ ⟨0⟩ := by
      rw [hdivY, u256_eq_refl]
      exact one_ne_zero_uint
    have rd2376 := rd2368.jumpiT (by native_decide) heqCond (by jump_dest) (by evm_ov)
    have rd2377 := RD.jumpdest rd2376 (by native_decide) (by evm_ov)
    have rd2390 := rd2377.pushConst jugRay
      (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
    have rd2396 := evm_run rd2390 with [
      raw swap1 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rd1530 := rd2396.jump (by native_decide) (by jump_dest) (by evm_ov)
    exact ⟨_, _, by
      change RD jugBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1530⟩
        (UInt256.div (prev * jugRay) jugRay :: prev :: R)
        mem (UInt256.ofNat 6) out acc _ _ at rd1530
      rw [hquot] at rd1530
      exact rd1530⟩

theorem RD.jugDripRmulOverflowReverts
    {cA gh bl σ σ₀ A I} {g pow prev : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hover : UInt256.size ≤ pow.toNat * prev.toNat)
    (rd1524 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1524⟩
      (pow :: ⟨1530⟩ :: prev :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    RDrev jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hprevNe : prev ≠ ⟨0⟩ := by
    intro hzero
    have hprod0 : pow.toNat * prev.toNat = 0 := by simp [hzero]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hdivNe : UInt256.div (prev * pow) prev ≠ pow :=
    u256_mul_div_overflow_ne pow prev hover
  have rd1529 := evm_run rd1524 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨2343⟩ (by native_decide) (by evm_ov)]
  have rd2343 := rd1529.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd2353 := evm_run rd2343 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨2367⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.isZero prev = ⟨0⟩ := isZero_eq_zero_of_ne hprevNe
  have rd2354 := rd2353.jumpiNT (by native_decide) hcond (by evm_ov)
  have rd2362 := evm_run rd2354 with [
    raw pop (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨2364⟩ (by native_decide) (by evm_ov)]
  have rd2364 := rd2362.jumpiT (by native_decide) hprevNe (by jump_dest) (by evm_ov)
  have rd2368 := evm_run rd2364 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2376⟩ (by native_decide) (by evm_ov)]
  have heqCond :
      UInt256.eq (UInt256.div (prev * pow) prev) pow = ⟨0⟩ := by
    exact u256_eq_of_ne hdivNe
  have rdFallthrough := rd2368.jumpiNT (by native_decide) heqCond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.jugDripRmulRayOverflowReverts
    {cA gh bl σ σ₀ A I} {g prev : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hover : UInt256.size ≤ jugRay.toNat * prev.toNat)
    (rd1524 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1524⟩
      (jugRay :: ⟨1530⟩ :: prev :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    RDrev jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hprevNe : prev ≠ ⟨0⟩ := by
    intro hzero
    have hprod0 : jugRay.toNat * prev.toNat = 0 := by simp [hzero]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hdivNe : UInt256.div (prev * jugRay) prev ≠ jugRay :=
    jugRay_mul_div_overflow_ne prev hover
  have rd1529 := evm_run rd1524 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨2343⟩ (by native_decide) (by evm_ov)]
  have rd2343 := rd1529.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd2353 := evm_run rd2343 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨2367⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.isZero prev = ⟨0⟩ := isZero_eq_zero_of_ne hprevNe
  have rd2354 := rd2353.jumpiNT (by native_decide) hcond (by evm_ov)
  have rd2362 := evm_run rd2354 with [
    raw pop (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨2364⟩ (by native_decide) (by evm_ov)]
  have rd2364 := rd2362.jumpiT (by native_decide) hprevNe (by jump_dest) (by evm_ov)
  have rd2368 := evm_run rd2364 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2376⟩ (by native_decide) (by evm_ov)]
  have heqCond :
      UInt256.eq (UInt256.div (prev * jugRay) prev) jugRay = ⟨0⟩ := by
    exact u256_eq_of_ne hdivNe
  have rdFallthrough := rd2368.jumpiNT (by native_decide) heqCond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.jugDiffSameReturnsZero
    {cA gh bl σ σ₀ A I} {g v : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hvMax : (v.toNat : Int) ≤ maxInt256)
    (rd2397 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2397⟩
      (v :: v :: ⟨1570⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1570⟩
      (⟨0⟩ :: R) mem (UInt256.ofNat 6) out acc k' C' := by
  have hvHi : v.toNat < 2 ^ 255 := by
    have hvInt : (v.toNat : Int) < (2 : Int) ^ 255 := by
      have hle : (v.toNat : Int) ≤ (2 : Int) ^ 255 - 1 := by
        simpa [maxInt256] using hvMax
      omega
    exact_mod_cast hvInt
  have hslt : UInt256.slt v (⟨0⟩ : UInt256) = ⟨0⟩ := by
    simpa using slt_lit_zero (a := v) (m := 0) (by norm_num) (by omega) hvHi
  have hsub : UInt256.sub v v = ⟨0⟩ := u256_sub_self v
  have rd2411 := evm_run rd2397 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw slt (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨2418⟩ (by native_decide) (by evm_ov)]
  have rd2412 := rd2411.jumpiNT (by native_decide)
    (by simpa using hslt)
    (by evm_ov)
  have rd2422 := evm_run rd2412 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw slt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2147⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.isZero (UInt256.slt v (⟨0⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hslt]
    decide
  have rd2147 := rd2422.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
  have rd2152 := evm_run rd2147 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd1570 := rd2152.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [hsub] using rd1570⟩

theorem RD.jugDiffReturns
    {cA gh bl σ σ₀ A I} {g rate prev : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hrateMax : (rate.toNat : Int) ≤ maxInt256)
    (hprevMax : (prev.toNat : Int) ≤ maxInt256)
    (rd2397 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2397⟩
      (prev :: rate :: ⟨1570⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    ∃ k' C', RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1570⟩
      (UInt256.sub rate prev :: R) mem (UInt256.ofNat 6) out acc k' C' := by
  have hrateHi : rate.toNat < 2 ^ 255 := by
    have hrateInt : (rate.toNat : Int) < (2 : Int) ^ 255 := by
      have hle : (rate.toNat : Int) ≤ (2 : Int) ^ 255 - 1 := by
        simpa [maxInt256] using hrateMax
      omega
    exact_mod_cast hrateInt
  have hprevHi : prev.toNat < 2 ^ 255 := by
    have hprevInt : (prev.toNat : Int) < (2 : Int) ^ 255 := by
      have hle : (prev.toNat : Int) ≤ (2 : Int) ^ 255 - 1 := by
        simpa [maxInt256] using hprevMax
      omega
    exact_mod_cast hprevInt
  have hrateSlt : UInt256.slt rate (⟨0⟩ : UInt256) = ⟨0⟩ := by
    simpa using slt_lit_zero (a := rate) (m := 0) (by norm_num) (by omega) hrateHi
  have hprevSlt : UInt256.slt prev (⟨0⟩ : UInt256) = ⟨0⟩ := by
    simpa using slt_lit_zero (a := prev) (m := 0) (by norm_num) (by omega) hprevHi
  have rd2411 := evm_run rd2397 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw slt (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨2418⟩ (by native_decide) (by evm_ov)]
  have rd2412 := rd2411.jumpiNT (by native_decide)
    (by simpa using hrateSlt)
    (by evm_ov)
  have rd2422 := evm_run rd2412 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw slt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2147⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.isZero (UInt256.slt prev (⟨0⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hprevSlt]
    decide
  have rd2147 := rd2422.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
  have rd2152 := evm_run rd2147 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd1570 := rd2152.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa using rd1570⟩

theorem RD.jugDiffSameRevertXBound
    {cA gh bl σ σ₀ A I} {g v : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hvMaxNot : ¬ (v.toNat : Int) ≤ maxInt256)
    (rd2397 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2397⟩
      (v :: v :: ⟨1570⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    RDrev jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hvHi : 2 ^ 255 ≤ v.toNat := by
    have hvInt : ((2 ^ 255 : ℕ) : Int) ≤ (v.toNat : Int) := by
      have hvGt : maxInt256 < (v.toNat : Int) := by
        omega
      simpa [maxInt256] using hvGt
    exact_mod_cast hvInt
  have hslt : UInt256.slt v (⟨0⟩ : UInt256) = ⟨1⟩ := by
    simpa using slt_lit_one_high (a := v) (m := 0) (by norm_num) hvHi
  have rd2411 := evm_run rd2397 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw slt (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨2418⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.slt v (⟨0⟩ : UInt256) ≠ ⟨0⟩ := by
    rw [hslt]
    decide
  have rd2418 := rd2411.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
  have rd2422 := evm_run rd2418 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2147⟩ (by native_decide) (by evm_ov)]
  have hcond2 : UInt256.isZero (UInt256.slt v (⟨0⟩ : UInt256)) = ⟨0⟩ := by
    rw [hslt]
    decide
  have rd2423 := rd2422.jumpiNT (by native_decide) hcond2 (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd2423
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.jugDiffRevertXBound
    {cA gh bl σ σ₀ A I} {g rate prev : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hrateMaxNot : ¬ (rate.toNat : Int) ≤ maxInt256)
    (rd2397 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2397⟩
      (prev :: rate :: ⟨1570⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    RDrev jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hrateHi : 2 ^ 255 ≤ rate.toNat := by
    have hrateInt : ((2 ^ 255 : ℕ) : Int) ≤ (rate.toNat : Int) := by
      have hrateGt : maxInt256 < (rate.toNat : Int) := by
        omega
      simpa [maxInt256] using hrateGt
    exact_mod_cast hrateInt
  have hslt : UInt256.slt rate (⟨0⟩ : UInt256) = ⟨1⟩ := by
    simpa using slt_lit_one_high (a := rate) (m := 0) (by norm_num) hrateHi
  have rd2411 := evm_run rd2397 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw slt (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨2418⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.slt rate (⟨0⟩ : UInt256) ≠ ⟨0⟩ := by
    rw [hslt]
    decide
  have rd2418 := rd2411.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)
  have rd2422 := evm_run rd2418 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2147⟩ (by native_decide) (by evm_ov)]
  have hcond2 : UInt256.isZero (UInt256.slt rate (⟨0⟩ : UInt256)) = ⟨0⟩ := by
    rw [hslt]
    decide
  have rd2423 := rd2422.jumpiNT (by native_decide) hcond2 (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd2423
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.jugDiffRevertYBound
    {cA gh bl σ σ₀ A I} {g rate prev : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hrateMax : (rate.toNat : Int) ≤ maxInt256)
    (hprevMaxNot : ¬ (prev.toNat : Int) ≤ maxInt256)
    (rd2397 : RD jugBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2397⟩
      (prev :: rate :: ⟨1570⟩ :: R)
      mem (UInt256.ofNat 6) out acc k C) :
    RDrev jugBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hrateHi : rate.toNat < 2 ^ 255 := by
    have hrateInt : (rate.toNat : Int) < (2 : Int) ^ 255 := by
      have hle : (rate.toNat : Int) ≤ (2 : Int) ^ 255 - 1 := by
        simpa [maxInt256] using hrateMax
      omega
    exact_mod_cast hrateInt
  have hprevHi : 2 ^ 255 ≤ prev.toNat := by
    have hprevInt : ((2 ^ 255 : ℕ) : Int) ≤ (prev.toNat : Int) := by
      have hprevGt : maxInt256 < (prev.toNat : Int) := by
        omega
      simpa [maxInt256] using hprevGt
    exact_mod_cast hprevInt
  have hrateSlt : UInt256.slt rate (⟨0⟩ : UInt256) = ⟨0⟩ := by
    simpa using slt_lit_zero (a := rate) (m := 0) (by norm_num) (by omega) hrateHi
  have hprevSlt : UInt256.slt prev (⟨0⟩ : UInt256) = ⟨1⟩ := by
    simpa using slt_lit_one_high (a := prev) (m := 0) (by norm_num) hprevHi
  have rd2411 := evm_run rd2397 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw slt (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨2418⟩ (by native_decide) (by evm_ov)]
  have rd2412 := rd2411.jumpiNT (by native_decide)
    (by simpa using hrateSlt)
    (by evm_ov)
  have rd2422 := evm_run rd2412 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw slt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2147⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.isZero (UInt256.slt prev (⟨0⟩ : UInt256)) = ⟨0⟩ := by
    rw [hprevSlt]
    decide
  have rd2423 := rd2422.jumpiNT (by native_decide) hcond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd2423
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)


end Benchmarks.Dss.Jug
