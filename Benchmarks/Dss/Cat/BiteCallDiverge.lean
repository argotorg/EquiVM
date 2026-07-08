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

end Benchmarks.Dss.Cat
