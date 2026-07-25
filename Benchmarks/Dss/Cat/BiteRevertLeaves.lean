import Benchmarks.Dss.Cat.BiteConnect
import Benchmarks.Dss.Cat.BiteRevertPrim
import Benchmarks.Dss.Cat.BiteSource
import Benchmarks.Dss.Cat.BiteTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! # Cat `bite(bytes32,address)` — revert leaves

Each leaf concludes the SUCCESS-branch `runtimeEquivalenceFor …` shape but under a failing-condition
hypothesis, via the revert path: reach the divergence with the public `catBiteReach*`/`catBiteTraceSeg*`
segment lemmas, fire the matching revert primitive to get `RDrev`, and bridge to the Solm body's
`.reverted` result with `RDrev.reEquivExecutionRevert` + the matching `catBiteSource*Revert`.

Template: `catBiteShort` (BiteConnect.lean). Revert primitives: `RD.catBiteCheckedMulRevert`,
`RD.solcErrorStringRevertTailGrown`, `RD.solcCheckedSubStringRevertGrown`,
`RD.reachInvalidHalt`, and `RD.catBite{Grab,Fess,Kick}CallFailed`.

**Reach-cursor convention.** The entry→divergence reach assembler `catBiteBody` (Bite.lean) is not
yet completed (the inter-call return-data→memory threading is still open). Exactly as the success
leaf `catBiteSuccessLeaf` takes the whole-run `RDret` as a hypothesis, each revert leaf takes the EVM
reach cursor *at the divergence* as a hypothesis and completes the revert branch: fire the primitive
→ `RDrev`, run the Solm `catBiteSource*Revert`, bridge with `RDrev.reEquivExecutionRevert`. When the
reach assembler lands, its cursors discharge these hypotheses. -/

/-- **Generic `require(cond, "msg")`-false → `Error(string)` revert combinator.** From a reach-cursor
at the guard's `PUSH2 okPc` with the (already-computed) guard boolean `cond` on top, and `cond = ⟨0⟩`
(condition false), hand-trace `PUSH2 okPc; JUMPI`-not-taken into the `Error(string)` tail and fire
`RD.solcErrorStringRevertTailGrown` (grown post-call memory). Reused by every `bite` `require`
(live / spot / unsafe / litter / room / dart / dink / dartLimit / dinkLimit) — the leaf instantiates
`guardPc` + the tail Wf. The bytecode facts `hpush2`/`hjumpi`/`htail` are discharged by
`native_decide` at the concrete `guardPc`; the grown-memory facts by `omega` from the site state. -/
theorem RD.catBiteGuardStringRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {cond okPc : UInt256} {R : List UInt256} {k C : ℕ}
    {guardPc len rawWord shift word : UInt256} {op : Operation.POp} {width : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) guardPc
      (cond :: R) mem aw rdata acc k C)
    (hcond : cond = ⟨0⟩)
    (hpush2 : decode catBytecode guardPc = some (.Push .PUSH2, some (okPc, 2)))
    (hjumpi : decode catBytecode (guardPc + UInt256.ofNat 3) = some (.JUMPI, .none))
    (htail : solcErrorStringRevertTailWf catBytecode (guardPc + UInt256.ofNat 3 + ⟨1⟩)
      len rawWord shift op width)
    (hpush : op ≠ .PUSH0) (hword : UInt256.shiftLeft rawWord shift = word)
    (hmemsz : 228 ≤ mem.size) (haw : 8 ≤ aw.toNat) (hawsz : aw.toNat * 32 < UInt256.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 5 ≤ 1024) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd2 := rd.push2 okPc hpush2 (by simp only [List.length_cons]; omega)
  have rd3 := rd2.jumpiNT hjumpi hcond (by omega)
  exact RD.solcErrorStringRevertTailGrown rd3 htail hpush hword hmemsz haw hawsz hread64 hov

/-- **mul-overflow leaf (artRate = art·rate).** EVM cursor at the shared `checkedMul` routine `@3720`
with the `artRate` operands; overflow (`hover`) fires `RD.catBiteCheckedMulRevert`, the Solm body
reverts via `catBiteSourceArtRateOverflowRevert`, bridged by `RDrev.reEquivExecutionRevert`. -/
theorem catBiteArtRateOverflowLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {evmIlk evmUrn : EVM.State} {ilksOut urnsOut : ByteArray}
    {iArt iRate iSpot iLine iDust ink art ret : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3720⟩
      (iRate :: art :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 9 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode0 :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).option 0
          (fun acc => acc.code.size))).toNat)
    (hIlksCall :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
        "ilks" 0 [biteIlkVal I] (true, evmIlk, ilksOut) false)
    (hIlksDec :
      config.externalABI.decode? "ilks" ilksOut =
        some [bw iArt, bw iRate, bw iSpot, bw iLine, bw iDust])
    (hvatCodeIlk :
      0 < (UInt256.ofNat
        ((evmIlk.lookupAccount (biteVatAddr evmIlk)).option 0 (fun acc => acc.code.size))).toNat)
    (hUrnsCall :
      typedCallViaEVM config evmIlk (EVM.address (biteVatAddr evmIlk))
        "urns" 0 [biteIlkVal I, biteUrnVal I] (true, evmUrn, urnsOut) false)
    (hUrnsDec : config.externalABI.decode? "urns" urnsOut = some [bw ink, bw art])
    (hlive : catSlotWord ⟨2⟩ evmUrn.accountMap evmUrn.executionEnv = ⟨1⟩)
    (hfitInkSpot : ink.toNat * iSpot.toNat < UInt256.size) (hspotPos : 0 < iSpot.toNat)
    (hover : UInt256.size ≤ art.toNat * iRate.toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev : RDrev catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.catBiteCheckedMulRevert rd (by rw [Nat.mul_comm]; exact hover) hov
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted :=
    catBiteSourceArtRateOverflowRevert hwv hvatCode0 hIlksCall hIlksDec hvatCodeIlk
      hUrnsCall hUrnsDec hlive hfitInkSpot hspotPos hover
  have hfinal := hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  simpa using hfinal

/-- **call-fail leaf (kick).** EVM cursor at the `kick` success-guard `@2532` with a failed-call
status `⟨0⟩` on top; `RD.catBiteKickCallFailed` produces `RDrev`, bridged by
`RDrev.reEquivExecutionRevert`. The Solm body reverts via `catBiteSourceKickFailRevert` (green in
BiteSource; its `ExecTransitionBody … .reverted` is taken here as `hbody`, plugging in identically to
the mul-overflow leaf's `catBiteSourceArtRateOverflowRevert`). -/
theorem catBiteKickFailLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2532⟩
      (⟨0⟩ :: R) mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size) (hov : R.length + 5 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev : RDrev catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    RD.catBiteKickCallFailed rd hrdataSize hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- **Generic mul-overflow leaf** (`checkedMul` @3720): covers all six `checkedMul` overflow reverts
(inkSpot / artRate / dunkRoomWad / inkDart / dartRate / tabBase) — instantiate `a,b` with the site
operands and `hbody` with the matching `catBiteSource*OverflowRevert`. -/
theorem catBiteMulOverflowRevertLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b ret : UInt256} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3720⟩
      (a :: b :: ret :: R) mem aw rdata acc k C)
    (hover : UInt256.size ≤ a.toNat * b.toNat) (hov : R.length + 9 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.catBiteCheckedMulRevert rd hover hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- **call-fail leaf (grab).** EVM cursor at the `grab` success-guard `@2193` with failed status. -/
theorem catBiteGrabFailLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2193⟩
      (⟨0⟩ :: R) mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size) (hov : R.length + 5 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.catBiteGrabCallFailed rd hrdataSize hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- **call-fail leaf (fess).** EVM cursor at the `fess` success-guard `@2300` with failed status. -/
theorem catBiteFessFailLeaf {cA cA' gh bl σ_evm σ_solm σ' σ₀ A I} {g : UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2300⟩
      (⟨0⟩ :: R) mem aw rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) (hov : R.length + 5 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.catBiteFessCallFailed rd hrdataSize hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- **Generic require-false leaf**: covers all nine `bite` `require(cond, "msg")` reverts
(live / spot / unsafe / litter / room / dart / dink / dartLimit / dinkLimit) — instantiate `guardPc`
+ the guard/tail bytecode facts (by `native_decide`) and `hbody` with the matching
`catBiteSource*Revert`. Fires the generic `RD.catBiteGuardStringRevert`. -/
theorem catBiteRequireStringRevertLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {cond okPc : UInt256} {R : List UInt256} {k C : ℕ}
    {guardPc len rawWord shift word : UInt256} {op : Operation.POp} {width : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) guardPc
      (cond :: R) mem aw rdata acc k C)
    (hcond : cond = ⟨0⟩)
    (hpush2 : decode catBytecode guardPc = some (.Push .PUSH2, some (okPc, 2)))
    (hjumpi : decode catBytecode (guardPc + UInt256.ofNat 3) = some (.JUMPI, .none))
    (htail : solcErrorStringRevertTailWf catBytecode (guardPc + UInt256.ofNat 3 + ⟨1⟩)
      len rawWord shift op width)
    (hpush : op ≠ .PUSH0) (hword : UInt256.shiftLeft rawWord shift = word)
    (hmemsz : 228 ≤ mem.size) (haw : 8 ≤ aw.toNat) (hawsz : aw.toNat * 32 < UInt256.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 5 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.catBiteGuardStringRevert rd hcond hpush2 hjumpi htail hpush hword
    hmemsz haw hawsz hread64 hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- **checkedSub-underflow leaf (room = box − litter).** EVM cursor at the shared `checkedSub`
routine `@3762` with the `room` operands; underflow (`hlt`) fires `RD.solcCheckedSubStringRevertGrown`
(grown post-call memory), bridged to `catBiteSourceRoomUnderflowRevert`. -/
theorem catBiteRoomUnderflowRevertLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {a b ret okPc len rawWord shift word : UInt256} {op : Operation.POp} {width : ℕ}
    {R : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3762⟩
      (b :: a :: ret :: R) mem aw rdata acc k C)
    (hsub : solcCheckedSubSuccessWf catBytecode ⟨3762⟩ okPc)
    (htail : solcErrorStringRevertTailWf catBytecode (solcCheckedArithmeticRevertPc ⟨3762⟩)
      len rawWord shift op width)
    (hpush : op ≠ .PUSH0) (hlt : a.toNat < b.toNat)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmemsz : 228 ≤ mem.size) (haw : 8 ≤ aw.toNat) (hawsz : aw.toNat * 32 < UInt256.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.solcCheckedSubStringRevertGrown rd hsub htail hpush hlt hword
    hmemsz haw hawsz hread64 hov
  simpa using hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- **INVALID / div-by-zero leaf (milkChop == 0).** solc 0.6.12 compiles `tab / milkChop` with a
`milkChop != 0` guard whose false branch is the `INVALID` opcode `0xfe`. The whole run aborts with
`.error .InvalidInstruction` (or OOG on the way). Unlike the `REVERT` leaves this uses the distinct
`execResultsEquiv.invalidHalt` bridge: `RD.reachInvalidHaltXi`'s two-way halt disjunction maps its
`OutOfGass` disjunct to the `outOfGas` equivalence case and its `InvalidInstruction` disjunct to
`execResultsEquiv.invalidHalt`, feeding the Solm `.div`-revert body (`catBiteSourceMilkChopZeroRevert`,
supplied as `hbody`). -/
theorem catBiteMilkChopZeroRevertLeaf {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {invalidPc : UInt256} {stk : List UInt256} {k C : ℕ}
    (hcode : I.code = catBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some biteTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
        (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I))
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) invalidPc stk mem aw rdata acc k C)
    (hinvalid : decode catBytecode invalidPc = some (.INVALID, .none))
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (biteLocals I)
        biteTransition.body .reverted) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have rd' : RD I.code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) invalidPc stk mem aw rdata acc k C := by
    rw [hcode]; exact rd
  have hinv' : decode I.code invalidPc = some (.INVALID, .none) := by rw [hcode]; exact hinvalid
  have hg : (Sat256.ofUInt256 g).toUInt256 = g := rfl
  have hdis := RD.reachInvalidHaltXi rd' hinv'
  rw [hg] at hdis
  rcases hdis with hoog | hinv
  · exact reEquiv_outOfGas hoog
  · refine reEquiv_execution hdispatch hdecode hbody ?_
    rw [hinv]
    exact execResultsEquiv.invalidHalt rfl rfl

end Benchmarks.Dss.Cat
