import Benchmarks.Dss.Cat.BiteRevertLeaves

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite(bytes32,address)` — per-external-call divergence bridges

Companion to `BiteRevertLeaves`: the EVM-boilerplate revert bridges at each of `bite`'s five
external calls (`ilks`, `urns` STATICCALLs; `grab`, `fess`, `kick` CALLs). Each call site has three
solc-emitted divergences — the `EXTCODESIZE`/`ISZERO` no-code guard, the call-failure guard, and
(for the view STATICCALLs) the return-`returndatasize` decode guard.

Each bridge matches the reach-cursor-as-hypothesis convention of `catBite{Grab,Fess,Kick}FailLeaf`:
it takes the EVM cursor *at the divergence* (discharged by the `catBiteBody` reach assembler) plus the
Solm body revert `hbody` (discharged by the matching `catBiteSource*Revert` — the shallow ilks/urns
ones are proved locally below), fires the per-call revert combinator to `RDrev`, and bridges to the
Solm `.reverted` via `RDrev.reEquivExecutionRevert`. -/

/-! ## `ilks` STATICCALL EVM combinators

The `vat.ilks(ilk)` STATICCALL (guard pc `1233` / call-guard pc `1249` / 5-word `0xa0` return) lacks
the Cat-specific `RD.catBiteIlks{NoCode,CallFailed,ReturnDecodeShortReverts}` wrappers that `urns`
carries, so we build them here directly from the generic `RD.uniswap*` combinators (exactly the way
`BiteCallUrns` builds the `urns` ones), and from the `catBiteTraceSeg2a` return-guard trace. -/

/-- **ilks no-code** — the `EXTCODESIZE(vat)` guard at pc `1233` reverts. Mirrors
`RD.catBiteUrnsNoCode` at the `ilks` guard pcs. -/
theorem RD.catBiteIlksNoCode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {target outPtr inSize outSize aw : UInt256} {mem o : ByteArray} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1233⟩
      (target :: target :: outPtr :: inSize :: outPtr :: outSize :: R)
      mem aw o (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ target = ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) :
    RDrev catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) :=
  RD.uniswapExtcodesizeGuardMissing (pc := ⟨1233⟩) (okPc := ⟨1245⟩) rd hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons]; omega)

/-- **ilks call failed** — the `STATICCALL` success guard at pc `1249` bubbles the revert. Mirrors
`RD.catBiteUrnsCallFailed` at the `ilks` call-guard pcs. -/
theorem RD.catBiteIlksCallFailed
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1249⟩
      (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) :=
  RD.uniswapCallSuccessGuardMissing (pc := ⟨1249⟩) (okPc := ⟨1265⟩) rd rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

/-- **ilks return decode short** — from the `STATICCALL` success guard (pc `1249`, `status ≠ 0`),
clear the guard, drop the three scratch frame words, read the free pointer, and fall through the
`returndatasize < 160` (`0xa0`, five words) length guard into the revert. Mirrors `catBiteTraceSeg2a`
but taking the short branch, and `RD.catBiteUrnsReturnDecodeShortReverts`'s revert tail. -/
theorem RD.catBiteIlksReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {status d0 d1 d2 : UInt256}
    {mem o : ByteArray} {aw : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1249⟩
      (status :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hstatus : status ≠ ⟨0⟩)
    (hshort : o.size < 160) (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hMload64Cost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨64⟩ : UInt256) :: R → memoryExpansionCost s .MLOAD = 0)
    (hMload64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hov : R.length + 6 ≤ 1024) :
    RDrev catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd1267⟩ :=
    RD.uniswapCallSuccessGuardOk (pc := ⟨1249⟩) (okPc := ⟨1265⟩) rd hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)
  have rd1268 := rd1267.pop (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1269 := rd1268.pop (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1270 := rd1269.pop (by native_decide) (by omega)
  have rd1272 := rd1270.push1 ⟨64⟩ (by native_decide) (by omega)
  have rd1273 := RD.mload 0 ⟨128⟩ aw rd1272 (by native_decide) hMload64Cost hMload64Value
    hMload64Aw (by omega)
  have rd1274 := rd1273.returndatasize (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1276 := rd1274.push1 ⟨160⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1277 := rd1276.dup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1278 := rd1277.lt (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1279 := rd1278.iszero (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1282 := rd1279.push2 ⟨1287⟩ (by native_decide) (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat o.size) ⟨160⟩ = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, ulit_toNat' o.size hhi]
    exact hshort
  have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) ⟨160⟩) = ⟨0⟩ := by
    rw [hlt]; decide
  have rdFallthrough := RD.jumpiNT rd1282 (by native_decide) hcond
    (by simp only [List.length_cons]; omega)
  exact RD.uniswapPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

/-! ## `urns` STATICCALL divergences (pc 1383 guard / 1399 call-guard / 1420 decode-guard) -/

/-- **urns no-code** — the `EXTCODESIZE(vat)` guard at pc `1383` reverts. -/
theorem catBiteUrnsNoCodeLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {target outPtr aw : UInt256} {mem o : ByteArray} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1383⟩
      (target :: target :: outPtr :: ⟨68⟩ :: outPtr :: ⟨64⟩ :: R) mem aw o (cA, σ_evm) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ_evm target = ⟨0⟩)
    (hov : R.length + 8 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.catBiteUrnsNoCode rd hcodeSize hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- **urns call failed** — the `STATICCALL` success guard at pc `1399` bubbles the revert. -/
theorem catBiteUrnsFailLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1399⟩
      (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 5 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.catBiteUrnsCallFailed rd hosz hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- **urns return decode short** — `returndatasize < 64` at the pc `1420` length guard reverts. -/
theorem catBiteUrnsDecodeShortLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1420⟩
      R mem aw o acc k C)
    (hshort : o.size < 64) (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hMload64Cost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨64⟩ : UInt256) :: R → memoryExpansionCost s .MLOAD = 0)
    (hMload64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hov : R.length + 4 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.catBiteUrnsReturnDecodeShortReverts rd hshort hhi hMload64Value hMload64Cost
    hMload64Aw hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-! ## `grab` / `fess` / `kick` CALL no-code divergences -/

/-- **grab no-code** — `EXTCODESIZE(vat)` guard at pc `2177` reverts. -/
theorem catBiteGrabNoCodeLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {target inOff inSize outOff : UInt256} {R : List UInt256}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2177⟩
      (target :: target :: ⟨0⟩ :: inOff :: inSize :: outOff :: ⟨0⟩ :: R) mem aw rdata (cA, σ_evm) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ_evm target = ⟨0⟩)
    (hov : R.length + 9 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.catBiteGrabNoCode rd hcodeSize hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- **fess no-code** — `EXTCODESIZE(vow)` guard at pc `2284` reverts. -/
theorem catBiteFessNoCodeLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {target inOff inSize outOff outSize : UInt256} {R : List UInt256}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2284⟩
      (target :: target :: ⟨0⟩ :: inOff :: inSize :: outOff :: outSize :: R) mem aw rdata (cA, σ_evm) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ_evm target = ⟨0⟩)
    (hov : R.length + 9 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.catBiteFessNoCode rd hcodeSize hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- **kick no-code** — `EXTCODESIZE(flip)` guard at pc `2516` reverts. The account map `(cAx, σx)`
is generic (the `grab`/`fess` CALLs before `kick` may have mutated state). -/
theorem catBiteKickNoCodeLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g target : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2516⟩
      (target :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨164⟩ :: ⟨128⟩ :: ⟨32⟩ :: R) mem aw rdata (cAx, σx) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σx target = ⟨0⟩)
    (hov : R.length + 9 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.catBiteKickGuardMissing rd hcodeSize hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-! ## `ilks` STATICCALL divergences (pc 1233 guard / 1249 call-guard / decode guard) -/

/-- **ilks no-code** — the `EXTCODESIZE(vat)` guard at pc `1233` reverts. -/
theorem catBiteIlksNoCodeLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {target outPtr inSize outSize aw : UInt256} {mem o : ByteArray} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1233⟩
      (target :: target :: outPtr :: inSize :: outPtr :: outSize :: R) mem aw o (cA, σ_evm) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ_evm target = ⟨0⟩)
    (hov : R.length + 8 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.catBiteIlksNoCode rd hcodeSize hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- **ilks call failed** — the `STATICCALL` success guard at pc `1249` bubbles the revert. -/
theorem catBiteIlksFailLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1249⟩
      (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 5 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.catBiteIlksCallFailed rd hosz hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- **ilks return decode short** — the ilks `STATICCALL` succeeds (`status ≠ 0`) but returns fewer
than the five expected words (`returndatasize < 160`); the length guard reverts. -/
theorem catBiteIlksDecodeShortLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {status d0 d1 d2 : UInt256}
    {mem o : ByteArray} {aw : UInt256} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1249⟩
      (status :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hstatus : status ≠ ⟨0⟩)
    (hshort : o.size < 160) (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hMload64Cost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨64⟩ : UInt256) :: R → memoryExpansionCost s .MLOAD = 0)
    (hMload64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hov : R.length + 6 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.catBiteIlksReturnDecodeShortReverts rd hstatus hshort hhi hMload64Value
    hMload64Cost hMload64Aw hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-! ## Solm-side revert lemmas (`catBiteSource*Revert`)

The shallow ilks/urns revert lemmas the bridges bridge to (`hbody`), genuinely absent from
`BiteSource` (which only has the deep grab/fess/kick tail reverts + the `live` revert). Each threads
the `checkedExternalCallStmts` prefix — `require(callvalue==0)`, the vat `EXTCODESIZE` guard, and (for
`urns`) the successful `ilks` call + tuple projections — then diverges at the given call. Modeled on
the public `catBiteSourceLiveRevert`. -/

/-- The `EXTCODESIZE(vat)` guard is *false* when the vat account has empty code. Dual of
`biteVatGuard_true`. -/
theorem biteVatGuard_false {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "vat" = none)
    (hcode0 :
      (UInt256.ofNat ((evm.lookupAccount (biteVatAddr evm)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, biteVatRead hbase, evalBinaryOp?, EVM.Word.ofNat,
    biteVatAddr, hcode0]

/-- **ilks no-code revert.** The vat `EXTCODESIZE` guard before the first STATICCALL is false. -/
theorem catBiteSourceIlksNoCodeRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode0 :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
      biteTransition.body .reverted := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  set L0 := biteLocals I with hL0
  have hblock :
      ExecBlock config { contract := contract, locals := L0 } evm0 biteTransition.body .reverted := by
    simp only [biteTransition, nonpayable, checkedExternalCallStmts, checkedMulUintInto,
      checkedSubUintInto, checkedAddUintInto, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue
      (evalCallvalueEq_true (by simp [evm0, initState]; exact hwv))) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse
      (biteVatGuard_false (biteLocals_get_vat I) (by simpa [evm0] using hvatCode0)))
  simpa [ExecTransitionBody, hL0] using ExecFuncBody.execBlockRevert hblock

/-- **ilks call-failed revert.** The vat guard passes but the first STATICCALL returns `success = 0`. -/
theorem catBiteSourceIlksFailRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmIlk : EVM.State} {ilksOut : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode0 :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
          (fun acc => acc.code.size))).toNat)
    (hIlksFailCall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
        "ilks" 0 [biteIlkVal I] (false, evmIlk, ilksOut) false) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
      biteTransition.body .reverted := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  set L0 := biteLocals I with hL0
  have hblock :
      ExecBlock config { contract := contract, locals := L0 } evm0 biteTransition.body .reverted := by
    simp only [biteTransition, nonpayable, checkedExternalCallStmts, checkedMulUintInto,
      checkedSubUintInto, checkedAddUintInto, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue
      (evalCallvalueEq_true (by simp [evm0, initState]; exact hwv))) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue
      (biteVatGuard_true (biteLocals_get_vat I) (by simpa [evm0] using hvatCode0))) ?_
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      (biteVatRead (biteLocals_get_vat I)) (by simp [evalExpr?, pure])
      (evalExprs_biteIlksArgs I (biteLocals_get_ilk I)) hIlksFailCall)
  simpa [ExecTransitionBody, hL0] using ExecFuncBody.execBlockRevert hblock

/-- **ilks return-decode revert.** The first STATICCALL succeeds but its return bytes do not ABI
decode to the `(uint256,uint256,uint256,uint256,uint256)` tuple. -/
theorem catBiteSourceIlksDecodeRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmIlk : EVM.State} {ilksOut : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode0 :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
          (fun acc => acc.code.size))).toNat)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
        "ilks" 0 [biteIlkVal I] (true, evmIlk, ilksOut) false)
    (hIlksDec : config.externalABI.decode? "ilks" ilksOut = none) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
      biteTransition.body .reverted := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  set L0 := biteLocals I with hL0
  have hblock :
      ExecBlock config { contract := contract, locals := L0 } evm0 biteTransition.body .reverted := by
    simp only [biteTransition, nonpayable, checkedExternalCallStmts, checkedMulUintInto,
      checkedSubUintInto, checkedAddUintInto, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue
      (evalCallvalueEq_true (by simp [evm0, initState]; exact hwv))) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue
      (biteVatGuard_true (biteLocals_get_vat I) (by simpa [evm0] using hvatCode0))) ?_
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      (biteVatRead (biteLocals_get_vat I)) (by simp [evalExpr?, pure])
      (evalExprs_biteIlksArgs I (biteLocals_get_ilk I)) hIlksCall hIlksDec)
  simpa [ExecTransitionBody, hL0] using ExecFuncBody.execBlockRevert hblock

section UrnsRevert
variable {cA gh bl σ σ₀ A I} {g : UInt256}
  {evmIlk evmUrn : EVM.State} {ilksOut urnsOut : ByteArray}
  {iArt iRate iSpot iLine iDust : UInt256}
  (hwv : I.weiValue = ⟨0⟩)
  (hvatCode0 :
    0 < (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
        (fun acc => acc.code.size))).toNat)
  (hIlksCall :
    typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (EVM.address (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)))
      "ilks" 0 [biteIlkVal I] (true, evmIlk, ilksOut) false)
  (hIlksDec :
    config.externalABI.decode? "ilks" ilksOut =
      some [bw iArt, bw iRate, bw iSpot, bw iLine, bw iDust])
  (hvatCodeIlk :
    0 < (UInt256.ofNat
      ((evmIlk.lookupAccount (biteVatAddr evmIlk)).option 0 (fun acc => acc.code.size))).toNat)

include hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk

/-- The public `catBiteSourceLiveRevert` prefix (nonpayable + vat guard + `ilks` STATICCALL + its
`rate`/`spot`/`dust` projections + the `urns` vat guard), leaving the `urns` external-call statement
as an `ExecBlock`-continuation goal. Shared by the two reachable `urns` divergences. -/
private theorem biteUrnsRevert_afterIlks
    (hUrnsStmtRevert :
      ExecStmt config { contract := contract, locals := bsDust I iArt iRate iSpot iLine iDust } evmIlk
        (.externalCall (.storage vatRef) "urns" (.intLit 0) [.var "ilk", .var "urn"] "vatUrn"
          (perm := false)) .reverted) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
      biteTransition.body .reverted := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  set L0 := biteLocals I with hL0
  set Lilk := L0.insert "vatIlk" (biteIlkTuple iArt iRate iSpot iLine iDust) with hLilk
  set Lrate := Lilk.insert "rate" (bw iRate) with hLrate
  set Lspot := Lrate.insert "spot" (bw iSpot) with hLspot
  set Ldust := Lspot.insert "dust" (bw iDust) with hLdust
  have hIlksStmt :
      ExecStmt config { contract := contract, locals := L0 } evm0
        (.externalCall (.storage vatRef) "ilks" (.intLit 0) [.var "ilk"] "vatIlk" (perm := false))
        (.ok { contract := contract, locals := Lilk } evmIlk) := by
    simpa [hLilk, biteIlkTuple, collapseReturns] using
      ExecStmt.externalCallSuccess
        (cfg := config) (solm := { contract := contract, locals := L0 }) (evm := evm0)
        (evm' := evmIlk)
        (receiver := .storage vatRef) (name := "ilks") (sendVal := 0)
        (target := biteVatAddr evm0) (args := [.var "ilk"]) (argVals := [biteIlkVal I])
        (out := ilksOut) (perm := false)
        (value := [bw iArt, bw iRate, bw iSpot, bw iLine, bw iDust])
        (biteVatRead (biteLocals_get_vat I))
        (by simp [evalExpr?, pure])
        (evalExprs_biteIlksArgs I (biteLocals_get_ilk I))
        hIlksCall hIlksDec
  have hRateStmt :
      ExecStmt config { contract := contract, locals := Lilk } evmIlk
        (.letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1))
        (.ok { contract := contract, locals := Lrate } evmIlk) :=
    biteTupleLet "vatIlk" "rate" (some uint256) 1
      (by rw [hLilk, store_get_self]) (by rfl)
  have hSpotStmt :
      ExecStmt config { contract := contract, locals := Lrate } evmIlk
        (.letDecl "spot" (some uint256) (.tupleGet (.var "vatIlk") 2))
        (.ok { contract := contract, locals := Lspot } evmIlk) :=
    biteTupleLet "vatIlk" "spot" (some uint256) 2
      (by rw [hLrate, store_get_ne _ _ (by decide), hLilk, store_get_self]) (by rfl)
  have hDustStmt :
      ExecStmt config { contract := contract, locals := Lspot } evmIlk
        (.letDecl "dust" (some uint256) (.tupleGet (.var "vatIlk") 4))
        (.ok { contract := contract, locals := Ldust } evmIlk) :=
    biteTupleLet "vatIlk" "dust" (some uint256) 4
      (by rw [hLspot, store_get_ne _ _ (by decide), hLrate, store_get_ne _ _ (by decide),
        hLilk, store_get_self]) (by rfl)
  have hDustVat : Ldust.get? "vat" = none := by
    rw [hLdust, store_get_ne _ _ (by decide), hLspot, store_get_ne _ _ (by decide),
      hLrate, store_get_ne _ _ (by decide), hLilk, store_get_ne _ _ (by decide)]
    exact biteLocals_get_vat I
  have hLdustEq : Ldust = bsDust I iArt iRate iSpot iLine iDust := by
    rw [hLdust, hLspot, hLrate, hLilk, hL0]
  have hblock :
      ExecBlock config { contract := contract, locals := L0 } evm0 biteTransition.body .reverted := by
    simp only [biteTransition, nonpayable, checkedExternalCallStmts, checkedMulUintInto,
      checkedSubUintInto, checkedAddUintInto, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue
      (evalCallvalueEq_true (by simp [evm0, initState]; exact hwv))) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue
      (biteVatGuard_true (biteLocals_get_vat I) (by simpa [evm0] using hvatCode0))) ?_
    refine ExecBlock.consNormal hIlksStmt ?_
    refine ExecBlock.consNormal hRateStmt ?_
    refine ExecBlock.consNormal hSpotStmt ?_
    refine ExecBlock.consNormal hDustStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue
      (biteVatGuard_true hDustVat hvatCodeIlk)) ?_
    rw [hLdustEq]
    exact ExecBlock.consRevert hUrnsStmtRevert
  simpa [ExecTransitionBody, hL0] using ExecFuncBody.execBlockRevert hblock

/-- **urns call-failed revert.** `ilks` succeeds; the second STATICCALL returns `success = 0`. -/
theorem catBiteSourceUrnsFailRevert
    (hUrnsFailCall :
      typedCallViaEVM config evmIlk (EVM.address (biteVatAddr evmIlk))
        "urns" 0 [biteIlkVal I, biteUrnVal I] (false, evmUrn, urnsOut) false) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
      biteTransition.body .reverted :=
  biteUrnsRevert_afterIlks hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk
    (ExecStmt.externalCallFailure (biteVatRead (bsDust_get_vat I _ _ _ _ _))
      (by simp [evalExpr?, pure])
      (evalExprs_biteUrnsArgs I (bsDust_get_ilk I _ _ _ _ _) (bsDust_get_urn I _ _ _ _ _))
      hUrnsFailCall)

/-- **urns return-decode revert.** `ilks` succeeds; the second STATICCALL succeeds but its return
bytes do not ABI decode to the `(uint256,uint256)` tuple. -/
theorem catBiteSourceUrnsDecodeRevert
    (hUrnsCall :
      typedCallViaEVM config evmIlk (EVM.address (biteVatAddr evmIlk))
        "urns" 0 [biteIlkVal I, biteUrnVal I] (true, evmUrn, urnsOut) false)
    (hUrnsDec : config.externalABI.decode? "urns" urnsOut = none) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
      biteTransition.body .reverted :=
  biteUrnsRevert_afterIlks hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk
    (ExecStmt.externalCallReturnDecodeRevert (biteVatRead (bsDust_get_vat I _ _ _ _ _))
      (by simp [evalExpr?, pure])
      (evalExprs_biteUrnsArgs I (bsDust_get_ilk I _ _ _ _ _) (bsDust_get_urn I _ _ _ _ _))
      hUrnsCall hUrnsDec)

end UrnsRevert

end Benchmarks.Dss.Cat
