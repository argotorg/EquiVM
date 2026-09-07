import Examples.UniswapV2Pair.PermitSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace UniswapV2Pair

theorem uniswapPermitHashPrefixAt {base cur : EVM.State} {I : ExecutionEnv}
    {structHash digest : Value}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
        .letDecl "digest" (some bytes32) permitDigestExpr ]
      (.ok { contract := contract, locals := permitAfterDigestStore base I structHash digest } cur) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl hstruct) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl hdigest) ExecBlock.nil

theorem uniswapPermitHashEcrecoverSuccessAt {base cur cur' : EVM.State} {I : ExecutionEnv}
    {structHash digest recovered : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered]) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
        .letDecl "digest" (some bytes32) permitDigestExpr,
        .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      (.ok (show Frame from
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered }) cur') := by
  have hhash := uniswapPermitHashPrefixAt (base := base) (cur := cur)
    (I := I) hstruct hdigest
  have hecrecover := uniswapPermitEcrecoverCallSuccessAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (recovered := recovered) (out := out) hcall hdec
  have hblock := execBlock_append hhash hecrecover
  simpa using hblock

theorem uniswapPermitHashEcrecoverFailureAt {base cur cur' : EVM.State} {I : ExecutionEnv}
    {structHash digest : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (false, cur', out) false) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
        .letDecl "digest" (some bytes32) permitDigestExpr,
        .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      .reverted := by
  have hhash := uniswapPermitHashPrefixAt (base := base) (cur := cur)
    (I := I) hstruct hdigest
  have hecrecover := uniswapPermitEcrecoverCallFailureAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (out := out) hcall
  have hblock := execBlock_append hhash hecrecover
  simpa using hblock

theorem uniswapPermitHashEcrecoverDecodeRevertAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = none) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
        .letDecl "digest" (some bytes32) permitDigestExpr,
        .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false) ]
      .reverted := by
  have hhash := uniswapPermitHashPrefixAt (base := base) (cur := cur)
    (I := I) hstruct hdigest
  have hecrecover := uniswapPermitEcrecoverCallDecodeRevertAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (out := out) hcall hdec
  have hblock := execBlock_append hhash hecrecover
  simpa using hblock

theorem uniswapPermitHashEcrecoverRequireSuccessAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest recovered : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered])
    (hnz : recovered ≠ .address (AccountAddress.ofNat 0))
    (heq : recovered = permitOwnerValue I) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
        .letDecl "digest" (some bytes32) permitDigestExpr,
        .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false),
        .require (.binary .and
          (.binary .ne (.var "recoveredAddress") zeroAddr)
          (.binary .eq (.var "recoveredAddress") (.var "owner"))) ]
      (.ok (show Frame from
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered }) cur') := by
  have hprefix := uniswapPermitHashEcrecoverSuccessAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (recovered := recovered) (out := out) hstruct hdigest hcall hdec
  have hrequire :
      ExecBlock config
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered } cur'
        [ .require (.binary .and
          (.binary .ne (.var "recoveredAddress") zeroAddr)
          (.binary .eq (.var "recoveredAddress") (.var "owner"))) ]
        (.ok
          { contract := contract,
            locals := permitAfterEcrecoverStore base I structHash digest recovered } cur') := by
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_permit_afterEcrecover_require_true base cur' I structHash digest recovered
          hnz heq))
      ExecBlock.nil
  have hblock := execBlock_append hprefix hrequire
  simpa using hblock

theorem uniswapPermitHashEcrecoverRequireZeroRevertAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest recovered : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered])
    (hzero : recovered = .address (AccountAddress.ofNat 0)) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
        .letDecl "digest" (some bytes32) permitDigestExpr,
        .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false),
        .require (.binary .and
          (.binary .ne (.var "recoveredAddress") zeroAddr)
          (.binary .eq (.var "recoveredAddress") (.var "owner"))) ]
      .reverted := by
  have hprefix := uniswapPermitHashEcrecoverSuccessAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (recovered := recovered) (out := out) hstruct hdigest hcall hdec
  have hrequire :
      ExecBlock config
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered } cur'
        [ .require (.binary .and
          (.binary .ne (.var "recoveredAddress") zeroAddr)
          (.binary .eq (.var "recoveredAddress") (.var "owner"))) ]
        .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_permit_afterEcrecover_require_false_zero base cur' I structHash digest
          recovered hzero))
  have hblock := execBlock_append hprefix hrequire
  simpa using hblock

theorem uniswapPermitHashEcrecoverRequireMismatchRevertAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest recovered : Value} {out : ByteArray}
    {recoveredAddr : AccountAddress}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered])
    (haddr : recovered = .address recoveredAddr)
    (hnz : recoveredAddr ≠ AccountAddress.ofNat 0)
    (hne : .address recoveredAddr ≠ permitOwnerValue I) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      [ .letDecl "structHash" (some bytes32) permitStructHashExpr,
        .letDecl "digest" (some bytes32) permitDigestExpr,
        .externalCall (.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
          [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false),
        .require (.binary .and
          (.binary .ne (.var "recoveredAddress") zeroAddr)
          (.binary .eq (.var "recoveredAddress") (.var "owner"))) ]
      .reverted := by
  have hprefix := uniswapPermitHashEcrecoverSuccessAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (recovered := recovered) (out := out) hstruct hdigest hcall hdec
  have hrequire :
      ExecBlock config
        { contract := contract,
          locals := permitAfterEcrecoverStore base I structHash digest recovered } cur'
        [ .require (.binary .and
          (.binary .ne (.var "recoveredAddress") zeroAddr)
          (.binary .eq (.var "recoveredAddress") (.var "owner"))) ]
        .reverted := by
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_permit_afterEcrecover_require_false_mismatch base cur' I structHash digest
          recovered recoveredAddr haddr hnz hne))
  have hblock := execBlock_append hprefix hrequire
  simpa using hblock

theorem uniswapPermitAfterNonceSuccessAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest recovered : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered])
    (hnz : recovered ≠ .address (AccountAddress.ofNat 0))
    (heq : recovered = permitOwnerValue I) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      permitAfterNonceBody
      (.ok (show Frame from
        { contract := contract,
          locals := permitAfterApproveStore base I structHash digest recovered })
        (permitApprovePostState cur' I)) := by
  have hprefix := uniswapPermitHashEcrecoverRequireSuccessAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (recovered := recovered) (out := out) hstruct hdigest hcall hdec hnz heq
  have happ := uniswapPermitApproveCallSuccessAt (base := base) (cur := cur')
    (I := I) (structHash := structHash) (digest := digest) (recovered := recovered)
  have hblock := execBlock_append hprefix happ
  simpa [permitAfterNonceBody] using hblock

theorem uniswapPermitAfterNonceEcrecoverFailureAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (false, cur', out) false) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      permitAfterNonceBody .reverted := by
  have hprefix := uniswapPermitHashEcrecoverFailureAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (out := out) hstruct hdigest hcall
  have hblock := execBlock_reverted_append
    (s2 := [
      .require (.binary .and
        (.binary .ne (.var "recoveredAddress") zeroAddr)
        (.binary .eq (.var "recoveredAddress") (.var "owner"))),
      .internalCall "_approve" [.var "owner", .var "spender", .var "value"]
        "_approveResult" ])
    hprefix
  simpa [permitAfterNonceBody] using hblock

theorem uniswapPermitAfterNonceEcrecoverDecodeRevertAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = none) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      permitAfterNonceBody .reverted := by
  have hprefix := uniswapPermitHashEcrecoverDecodeRevertAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (out := out) hstruct hdigest hcall hdec
  have hblock := execBlock_reverted_append
    (s2 := [
      .require (.binary .and
        (.binary .ne (.var "recoveredAddress") zeroAddr)
        (.binary .eq (.var "recoveredAddress") (.var "owner"))),
      .internalCall "_approve" [.var "owner", .var "spender", .var "value"]
        "_approveResult" ])
    hprefix
  simpa [permitAfterNonceBody] using hblock

theorem uniswapPermitAfterNonceRequireZeroRevertAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest recovered : Value} {out : ByteArray}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered])
    (hzero : recovered = .address (AccountAddress.ofNat 0)) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      permitAfterNonceBody .reverted := by
  have hprefix := uniswapPermitHashEcrecoverRequireZeroRevertAt (base := base) (cur := cur)
    (cur' := cur') (I := I) (structHash := structHash) (digest := digest)
    (recovered := recovered) (out := out) hstruct hdigest hcall hdec hzero
  have hblock := execBlock_reverted_append
    (s2 := [
      .internalCall "_approve" [.var "owner", .var "spender", .var "value"]
        "_approveResult" ])
    hprefix
  simpa [permitAfterNonceBody] using hblock

theorem uniswapPermitAfterNonceRequireMismatchRevertAt {base cur cur' : EVM.State}
    {I : ExecutionEnv} {structHash digest recovered : Value} {out : ByteArray}
    {recoveredAddr : AccountAddress}
    (hstruct :
      evalExpr? config { contract := contract, locals := permitAfterNonceLoadStore base I }
        cur permitStructHashExpr = .ok structHash)
    (hdigest :
      evalExpr? config { contract := contract, locals := permitAfterStructHashStore base I structHash }
        cur permitDigestExpr = .ok digest)
    (hcall : typedCallViaEVM config cur (AccountAddress.ofNat 1) "ecrecover" 0
      [digest, permitVValue I, permitRValue I, permitSValue I] (true, cur', out) false)
    (hdec : config.externalABI.decode? "ecrecover" out = some [recovered])
    (haddr : recovered = .address recoveredAddr)
    (hnz : recoveredAddr ≠ AccountAddress.ofNat 0)
    (hne : .address recoveredAddr ≠ permitOwnerValue I) :
    ExecBlock config { contract := contract, locals := permitAfterNonceLoadStore base I } cur
      permitAfterNonceBody .reverted := by
  have hprefix := uniswapPermitHashEcrecoverRequireMismatchRevertAt (base := base)
    (cur := cur) (cur' := cur') (I := I) (structHash := structHash)
    (digest := digest) (recovered := recovered) (out := out)
    (recoveredAddr := recoveredAddr) hstruct hdigest hcall hdec haddr hnz hne
  have hblock := execBlock_reverted_append
    (s2 := [
      .internalCall "_approve" [.var "owner", .var "spender", .var "value"]
        "_approveResult" ])
    hprefix
  simpa [permitAfterNonceBody] using hblock

theorem uniswapPermitNonceStorePrefix (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock config { contract := contract, locals := permitStore I } evm
      permitNonceStorePrefixBody
      (.ok { contract := contract, locals := permitAfterNonceLoadStore evm I }
        (permitAfterNonceState evm I)) := by
  change ExecBlock config { contract := contract, locals := permitStore I } evm
    [ .letDecl "domainSeparator" (some bytes32) (.storage domainSeparatorRef),
      .letDecl "nonce" (some uint256) (.storage (noncesRef (.var "owner"))),
      .assign .storage (noncesRef (.var "owner"))
        (wrapU256 (.binary .add (.var "nonce") (.intLit 1))) ]
    (.ok { contract := contract, locals := permitAfterNonceLoadStore evm I }
      (permitAfterNonceState evm I))
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_permit_domainSeparator_storage evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_permit_afterDomain_nonce_storage evm I)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_permit_nonce_next evm I) (permitAssignNonce evm I))
    ExecBlock.nil

theorem uniswapPermitBlockAfterNonce {evm : EVM.State} {I : ExecutionEnv} {result}
    (hrest : ExecBlock config
      { contract := contract, locals := permitAfterNonceLoadStore evm I }
      (permitAfterNonceState evm I) permitAfterNonceBody result) :
    ExecBlock config { contract := contract, locals := permitStore I } evm
      permitAfterDeadlineBody result := by
  have hblock := execBlock_append (uniswapPermitNonceStorePrefix evm I) hrest
  simpa [permitAfterDeadlineBody, permitNonceStorePrefixBody, permitAfterNonceBody] using hblock

theorem uniswapPermitDeadlinePrefix (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnotExpired : ¬ (permitDeadlineWord I).toNat <
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    ExecBlock config { contract := contract, locals := permitStore I } evm
      permitDeadlinePrefixBody
      (.ok { contract := contract, locals := permitStore I } evm) := by
  change ExecBlock config { contract := contract, locals := permitStore I } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .require (.binary .ge (.var "deadline") now) ]
    (.ok { contract := contract, locals := permitStore I } evm)
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_permit_deadline_ge_now_true evm I hnotExpired))
    ExecBlock.nil

theorem uniswapPermitBlockAfterDeadline {evm : EVM.State} {I : ExecutionEnv} {result}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnotExpired : ¬ (permitDeadlineWord I).toNat <
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hrest : ExecBlock config { contract := contract, locals := permitStore I } evm
      permitAfterDeadlineBody result) :
    ExecBlock config { contract := contract, locals := permitStore I } evm
      permitTransition.body result := by
  have hblock := execBlock_append
    (uniswapPermitDeadlinePrefix evm I hwv hnotExpired) hrest
  simpa [permitTransition, permitDeadlinePrefixBody, permitAfterDeadlineBody] using hblock

theorem uniswapPermitX_expired {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hexpired : (permitDeadlineWord I).toNat <
      (UInt256.ofNat I.header.timestamp).toNat)
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5473⟩
      [permitSWord I, permitRWord I, permitVWord I, permitDeadlineWord I,
        permitValueWord I, permitSpenderMaskedWord I, permitOwnerMaskedWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd5473⟩ := hdecoded
  have hlt :
      UInt256.lt (permitDeadlineWord I) (UInt256.ofNat I.header.timestamp) = ⟨1⟩ := by
    exact ult_one hexpired
  have rd5477₀ := evm_run rd5473 with [jumpdest, timestamp, dup5, lt]
  have rd5477 := rd5477₀
  rw [hlt] at rd5477
  have rd5482 := evm_run rd5477 with [iszero, push2 ⟨5547⟩, jumpiNT (by decide)]
  exact RD.solcErrorStringRevertTail
    (pc := ⟨5482⟩) (len := ⟨18⟩)
    (rawWord := (⟨1860528883258986746185044576161230704906577⟩ : UInt256))
    (shift := ⟨114⟩)
    (word := UInt256.shiftLeft
      (⟨1860528883258986746185044576161230704906577⟩ : UInt256) ⟨114⟩)
    (op := .PUSH18) (width := 18)
    rd5482
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) (by rfl) solcFreePtrMem_size solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem uniswapPermitX_deadlineOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hnotExpired : ¬ (permitDeadlineWord I).toNat <
      (UInt256.ofNat I.header.timestamp).toNat)
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5473⟩
      [permitSWord I, permitRWord I, permitVWord I, permitDeadlineWord I,
        permitValueWord I, permitSpenderMaskedWord I, permitOwnerMaskedWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5547⟩
      [permitSWord I, permitRWord I, permitVWord I, permitDeadlineWord I,
        permitValueWord I, permitSpenderMaskedWord I, permitOwnerMaskedWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd5473⟩ := hdecoded
  have hle : (UInt256.ofNat I.header.timestamp).toNat ≤ (permitDeadlineWord I).toNat := by
    omega
  have hlt : UInt256.lt (permitDeadlineWord I) (UInt256.ofNat I.header.timestamp) = ⟨0⟩ := by
    exact ult_zero hle
  have rd5477₀ := evm_run rd5473 with [jumpdest, timestamp, dup5, lt]
  have rd5477 := rd5477₀
  rw [hlt] at rd5477
  have rd5547 := evm_run rd5477 with [iszero, push2 ⟨5547⟩, jumpiT (by decide) (by jump_dest)]
  exact ⟨_, _, rd5547⟩

theorem uniswapPermitX_nonceStored {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hdeadlineOk : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5547⟩
      [permitSWord I, permitRWord I, permitVWord I, permitDeadlineWord I,
        permitValueWord I, permitSpenderMaskedWord I, permitOwnerMaskedWord I, ⟨570⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5589⟩
      [permitNonceWord σ I, ⟨1⟩, ⟨64⟩, ⟨32⟩, ⟨0⟩, permitOwnerMaskedWord I,
        solcAddrMask, permitDomainSeparatorWord σ I, permitSWord I, permitRWord I,
        permitVWord I, permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
        permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitNonceHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, permitAfterNonceAccountMap σ I) k C := by
  obtain ⟨_, _, rd5547⟩ := hdeadlineOk
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hownerMask :
      UInt256.land (permitOwnerMaskedWord I) solcAddrMask = permitOwnerMaskedWord I := by
    apply solcAddrMask_clean
    simpa [permitOwnerMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitOwnerWord I)
  have rd5550 := evm_run rd5547 with [jumpdest, push1 ⟨3⟩]
  obtain ⟨_, _, rd5551⟩ := rd5550.sload (by decide) (by evm_ov)
  have rd5561₀ := evm_run rd5551 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup10, and]
  have rd5561 := rd5561₀
  rw [hmask, hownerMask] at rd5561
  have rd5579 := evm_run rd5561 with [
    push1 ⟨0⟩, dup2, dup2,
    raw mstore 0 (wordAt0Mem (permitOwnerMaskedWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 (permitNonceHashMem I)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (mapSlot (permitOwnerMaskedWord I) ⟨4⟩)
      (UInt256.ofNat 3) (by decide) mem_cost
      (permitNonceKeccakSlot I) (by decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd5581⟩ := rd5579.sload (by decide) (by evm_ov)
  have rd5588 := evm_run rd5581 with [push1 ⟨1⟩, dup1, dup3, add, swap1, swap3]
  obtain ⟨_, _, rd5589⟩ := rd5588.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [permitDomainSeparatorWord, permitNonceWord, permitNonceNextWord,
      permitAfterNonceAccountMap, codeOwnerStorageWord] using rd5589⟩

theorem uniswapPermitX_structHashed {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hnonceEvm : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5589⟩
      [permitNonceWord σ I, ⟨1⟩, ⟨64⟩, ⟨32⟩, ⟨0⟩, permitOwnerMaskedWord I,
        solcAddrMask, permitDomainSeparatorWord σ I, permitSWord I, permitRWord I,
        permitVWord I, permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
        permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitNonceHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, permitAfterNonceAccountMap σ I) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5688⟩
      [permitStructHashWord σ I, ⟨64⟩, ⟨32⟩, ⟨0⟩, ⟨128⟩, ⟨1⟩,
        permitDomainSeparatorWord σ I, permitSWord I, permitRWord I, permitVWord I,
        permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
        permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitStructHashMem σ I) (UInt256.ofNat 11) ByteArray.empty
      (cA, permitAfterNonceAccountMap σ I) k C := by
  obtain ⟨_, _, rd5589⟩ := hnonceEvm
  have hspenderMask :
      UInt256.land (permitSpenderMaskedWord I) solcAddrMask = permitSpenderMaskedWord I := by
    apply solcAddrMask_clean
    simpa [permitSpenderMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitSpenderWord I)
  obtain ⟨_, _, rd5688⟩ := RD.uniswapPermitStructHash
    (nonce := permitNonceWord σ I) (owner := permitOwnerMaskedWord I)
    (spender := permitSpenderMaskedWord I) (value := permitValueWord I)
    (deadline := permitDeadlineWord I) (domain := permitDomainSeparatorWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (ret := ⟨570⟩) (R := [sel]) rd5589
    (permitNonceHashMem_size I) (permitNonceHashMem_read64 I) hspenderMask
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by
    simpa [permitStructHashWord, permitStructHashMem, permitStructHashLenMem,
      permitStructHashDataMem, permitStructHashDataWrites, permitTypehashWord] using rd5688⟩

theorem uniswapPermitX_digestHashed {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hstructEvm : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5688⟩
      [permitStructHashWord σ I, ⟨64⟩, ⟨32⟩, ⟨0⟩, ⟨128⟩, ⟨1⟩,
        permitDomainSeparatorWord σ I, permitSWord I, permitRWord I, permitVWord I,
        permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
        permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitStructHashMem σ I) (UInt256.ofNat 11) ByteArray.empty
      (cA, permitAfterNonceAccountMap σ I) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5746⟩
      [permitDigestWord σ I, ⟨64⟩, ⟨32⟩, ⟨0⟩, ⟨128⟩, ⟨1⟩, ⟨450⟩,
        permitSWord I, permitRWord I, permitVWord I, permitDeadlineWord I,
        permitValueWord I, permitSpenderMaskedWord I, permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitDigestMem σ I) (UInt256.ofNat 15) ByteArray.empty
      (cA, permitAfterNonceAccountMap σ I) k C := by
  obtain ⟨_, _, rd5688⟩ := hstructEvm
  have hbaseSize : (permitStructHashMem σ I).size = 352 := by
    simpa [permitStructHashMem] using
      permitRuntimeStructHashMem_size (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
        (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)
        (permitNonceHashMem_size I)
  have hbaseRead64 :
      (permitStructHashMem σ I).readWithPadding 64 32 =
        UInt256.toByteArray (⟨352⟩ : UInt256) := by
    simpa [permitStructHashMem] using
      permitRuntimeStructHashMem_read64 (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
        (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)
        (permitNonceHashMem_size I)
  obtain ⟨_, _, rd5746⟩ := RD.uniswapPermitDigestHash
    (structHash := permitStructHashWord σ I) (domain := permitDomainSeparatorWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (ret := ⟨570⟩) (R := [sel]) rd5688 hbaseSize hbaseRead64
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by
    simpa [permitDigestWord, permitDigestMem] using rd5746⟩

theorem uniswapPermitX_ecrecoverStaticcallMade
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hdigestEvm : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5746⟩
      [permitDigestWord σ I, ⟨64⟩, ⟨32⟩, ⟨0⟩, ⟨128⟩, ⟨1⟩, ⟨450⟩,
        permitSWord I, permitRWord I, permitVWord I, permitDeadlineWord I,
        permitValueWord I, permitSpenderMaskedWord I, permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitDigestMem σ I) (UInt256.ofNat 15) ByteArray.empty
      (cA, permitAfterNonceAccountMap σ I) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (permitAfterNonceAccountMap σ I) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute (permitAfterNonceAccountMap σ I)
            (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitEcrecoverInputMem σ I).readWithPadding 482 128)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨5814⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨610⟩, ⟨1⟩, ⟨0⟩,
            permitDigestWord σ I, permitSWord I, permitRWord I, permitVWord I,
            permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
            permitOwnerMaskedWord I, ⟨570⟩, sel]
          (permitEcrecoverStaticcallMem σ I o)
          (UInt256.ofNat 20) o (cA', σ') k C
      ∧ o.size < UInt256.size := by
  obtain ⟨_, _, rd5746⟩ := hdigestEvm
  have hstructMemSize : (permitStructHashMem σ I).size = 352 := by
    simpa [permitStructHashMem] using
      permitRuntimeStructHashMem_size (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
        (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)
        (permitNonceHashMem_size I)
  have hbaseSize : (permitDigestMem σ I).size = 450 := by
    simpa [permitDigestMem] using
      permitRuntimeDigestMem_size (permitDomainSeparatorWord σ I) (permitStructHashWord σ I)
        hstructMemSize
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5814, hoSize⟩ :=
    RD.uniswapPermitEcrecoverStaticcallMade
      (digest := permitDigestWord σ I) (s := permitSWord I) (r := permitRWord I)
      (v := permitVWord I) (deadline := permitDeadlineWord I)
      (value := permitValueWord I) (spender := permitSpenderMaskedWord I)
      (owner := permitOwnerMaskedWord I) (ret := ⟨570⟩) (R := [sel])
      rd5746 hbaseSize (permitVWord_mask_left I) hdepth
      (by simp only [List.length_singleton]; omega)
  refine ⟨cA', σ', z, o, A_in, callGas, k, C, ?_, ?_, hoSize⟩
  · simpa [initState, permitEcrecoverInputMem] using hΘ
  · simpa [permitEcrecoverInputMem, permitEcrecoverStaticcallMem] using rd5814

theorem uniswapPermitX_ecrecoverStaticcallDepthReverts
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hdigestEvm : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5746⟩
      [permitDigestWord σ I, ⟨64⟩, ⟨32⟩, ⟨0⟩, ⟨128⟩, ⟨1⟩, ⟨450⟩,
        permitSWord I, permitRWord I, permitVWord I, permitDeadlineWord I,
        permitValueWord I, permitSpenderMaskedWord I, permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitDigestMem σ I) (UInt256.ofNat 15) ByteArray.empty
      (cA, permitAfterNonceAccountMap σ I) k C)
    (hdepth : I.depth = 1024) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd5746⟩ := hdigestEvm
  have hstructMemSize : (permitStructHashMem σ I).size = 352 := by
    simpa [permitStructHashMem] using
      permitRuntimeStructHashMem_size (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
        (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)
        (permitNonceHashMem_size I)
  have hbaseSize : (permitDigestMem σ I).size = 450 := by
    simpa [permitDigestMem] using
      permitRuntimeDigestMem_size (permitDomainSeparatorWord σ I) (permitStructHashWord σ I)
        hstructMemSize
  exact RD.uniswapPermitEcrecoverStaticcallDepthReverts
    (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (ret := ⟨570⟩) (R := [sel]) rd5746 hbaseSize (permitVWord_mask_left I) hdepth
    (by simp only [List.length_singleton]; omega)

theorem uniswapPermitX_ecrecoverStatusAndReturnDecoded
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hstatic : ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (permitAfterNonceAccountMap σ I) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute (permitAfterNonceAccountMap σ I)
            (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitEcrecoverInputMem σ I).readWithPadding 482 128)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨5814⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨610⟩, ⟨1⟩, ⟨0⟩,
            permitDigestWord σ I, permitSWord I, permitRWord I, permitVWord I,
            permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
            permitOwnerMaskedWord I, ⟨570⟩, sel]
          (permitEcrecoverStaticcallMem σ I o)
          (UInt256.ofNat 20) o (cA', σ') k C
      ∧ o.size < UInt256.size) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (permitAfterNonceAccountMap σ I) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute (permitAfterNonceAccountMap σ I)
            (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitEcrecoverInputMem σ I).readWithPadding 482 128)
          (I.depth + 1) I.header false)
      ∧ (z = false →
        RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I))
      ∧ (z = true → 32 ≤ o.size →
        ∃ k' C', RD uniswapV2PairBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
          (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) ::
            permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
            permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
            permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
          (permitEcrecoverStaticcallMem σ I o)
          (UInt256.ofNat 20) o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5814, hoSize⟩ := hstatic
  refine ⟨cA', σ', z, o, A_in, callGas, hΘ, ?_, ?_, hoSize⟩
  · intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      simp [hz]
    exact RD.solcCallSuccessGuardMissing (okPc := ⟨5830⟩) rd5814 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) hoSize
      (by simp only [List.length_cons, List.length_nil]; omega)
  · intro hz ho32
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    obtain ⟨_, _, rd5832⟩ :=
      RD.solcCallSuccessGuardOk (okPc := ⟨5830⟩) rd5814 hstatus
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        (by simp only [List.length_cons, List.length_nil]; omega)
    have hstructMemSize : (permitStructHashMem σ I).size = 352 := by
      simpa [permitStructHashMem] using
        permitRuntimeStructHashMem_size (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
          (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)
          (permitNonceHashMem_size I)
    have hbaseSize : (permitDigestMem σ I).size = 450 := by
      simpa [permitDigestMem] using
        permitRuntimeDigestMem_size (permitDomainSeparatorWord σ I) (permitStructHashWord σ I)
          hstructMemSize
    obtain ⟨k', C', rd5844⟩ :=
      RD.uniswapPermitEcrecoverReturnWordDecoded
        (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
        (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
        (deadline := permitDeadlineWord I) (value := permitValueWord I)
        (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
        (ret := ⟨570⟩) (R := [sel]) rd5832 hbaseSize ho32 hoSize
        (by simp only [List.length_singleton]; omega)
    exact ⟨k', C', by
      simpa [permitEcrecoverStaticcallMem] using rd5844⟩

theorem uniswapPermitX_ecrecoverStatusAndReturnDecodedAll
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hstatic : ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (permitAfterNonceAccountMap σ I) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute (permitAfterNonceAccountMap σ I)
            (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitEcrecoverInputMem σ I).readWithPadding 482 128)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨5814⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨610⟩, ⟨1⟩, ⟨0⟩,
            permitDigestWord σ I, permitSWord I, permitRWord I, permitVWord I,
            permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
            permitOwnerMaskedWord I, ⟨570⟩, sel]
          (permitEcrecoverStaticcallMem σ I o)
          (UInt256.ofNat 20) o (cA', σ') k C
      ∧ o.size < UInt256.size) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (permitAfterNonceAccountMap σ I) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute (permitAfterNonceAccountMap σ I)
            (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitEcrecoverInputMem σ I).readWithPadding 482 128)
          (I.depth + 1) I.header false)
      ∧ (z = false →
        RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I))
      ∧ (z = true → o.size < 32 →
        ∃ k' C', RD uniswapV2PairBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
          (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)) ::
            permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
            permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
            permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
          (permitEcrecoverStaticcallMem σ I o)
          (UInt256.ofNat 20) o (cA', σ') k' C')
      ∧ (z = true → 32 ≤ o.size →
        ∃ k' C', RD uniswapV2PairBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
          (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) ::
            permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
            permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
            permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
          (permitEcrecoverStaticcallMem σ I o)
          (UInt256.ofNat 20) o (cA', σ') k' C')
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5814, hoSize⟩ := hstatic
  have hstructMemSize : (permitStructHashMem σ I).size = 352 := by
    simpa [permitStructHashMem] using
      permitRuntimeStructHashMem_size (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
        (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)
        (permitNonceHashMem_size I)
  have hbaseSize : (permitDigestMem σ I).size = 450 := by
    simpa [permitDigestMem] using
      permitRuntimeDigestMem_size (permitDomainSeparatorWord σ I) (permitStructHashWord σ I)
        hstructMemSize
  have hguardOk : z = true → ∃ k' C', RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5832⟩
      (⟨610⟩ :: ⟨1⟩ :: ⟨0⟩ :: permitDigestWord σ I :: permitSWord I ::
        permitRWord I :: permitVWord I :: permitDeadlineWord I :: permitValueWord I ::
        permitSpenderMaskedWord I :: permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k' C' := by
    intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    exact RD.solcCallSuccessGuardOk (okPc := ⟨5830⟩) rd5814 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨cA', σ', z, o, A_in, callGas, hΘ, ?_, ?_, ?_, hoSize⟩
  · intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      simp [hz]
    exact RD.solcCallSuccessGuardMissing (okPc := ⟨5830⟩) rd5814 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) hoSize
      (by simp only [List.length_cons, List.length_nil]; omega)
  · intro hz hshort
    obtain ⟨_, _, rd5832⟩ := hguardOk hz
    obtain ⟨k', C', rd5844⟩ :=
      RD.uniswapPermitEcrecoverReturnWordDecodedShort
        (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
        (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
        (deadline := permitDeadlineWord I) (value := permitValueWord I)
        (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
        (ret := ⟨570⟩) (R := [sel]) rd5832 hbaseSize hshort hoSize
        (by simp only [List.length_singleton]; omega)
    exact ⟨k', C', by
      simpa [permitEcrecoverStaticcallMem] using rd5844⟩
  · intro hz ho32
    obtain ⟨_, _, rd5832⟩ := hguardOk hz
    obtain ⟨k', C', rd5844⟩ :=
      RD.uniswapPermitEcrecoverReturnWordDecoded
        (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
        (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
        (deadline := permitDeadlineWord I) (value := permitValueWord I)
        (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
        (ret := ⟨570⟩) (R := [sel]) rd5832 hbaseSize ho32 hoSize
        (by simp only [List.length_singleton]; omega)
    exact ⟨k', C', by
      simpa [permitEcrecoverStaticcallMem] using rd5844⟩

theorem uniswapPermitX_ecrecoverStatusAndReturnDecodedAllAt
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {z : Bool} {o : ByteArray} {k C : ℕ}
    (rd5814 : RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5814⟩
      [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨610⟩, ⟨1⟩, ⟨0⟩,
        permitDigestWord σ I, permitSWord I, permitRWord I, permitVWord I,
        permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
        permitOwnerMaskedWord I, ⟨570⟩, sel]
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hoSize : o.size < UInt256.size) :
    (z = false →
      RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I))
    ∧ (z = true → o.size < 32 →
      ∃ k' C', RD uniswapV2PairBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
        (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)) ::
          permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
          permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
          permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
        (permitEcrecoverStaticcallMem σ I o)
        (UInt256.ofNat 20) o (cA', σ') k' C')
    ∧ (z = true → 32 ≤ o.size →
      ∃ k' C', RD uniswapV2PairBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
        (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) ::
          permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
          permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
          permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
        (permitEcrecoverStaticcallMem σ I o)
        (UInt256.ofNat 20) o (cA', σ') k' C') := by
  have hstructMemSize : (permitStructHashMem σ I).size = 352 := by
    simpa [permitStructHashMem] using
      permitRuntimeStructHashMem_size (permitOwnerMaskedWord I) (permitSpenderMaskedWord I)
        (permitValueWord I) (permitNonceWord σ I) (permitDeadlineWord I)
        (permitNonceHashMem_size I)
  have hbaseSize : (permitDigestMem σ I).size = 450 := by
    simpa [permitDigestMem] using
      permitRuntimeDigestMem_size (permitDomainSeparatorWord σ I) (permitStructHashWord σ I)
        hstructMemSize
  have hguardOk : z = true → ∃ k' C', RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5832⟩
      (⟨610⟩ :: ⟨1⟩ :: ⟨0⟩ :: permitDigestWord σ I :: permitSWord I ::
        permitRWord I :: permitVWord I :: permitDeadlineWord I :: permitValueWord I ::
        permitSpenderMaskedWord I :: permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k' C' := by
    intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
      rw [hz]
      decide
    exact RD.solcCallSuccessGuardOk (okPc := ⟨5830⟩) rd5814 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hstatus : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
      simp [hz]
    exact RD.solcCallSuccessGuardMissing (okPc := ⟨5830⟩) rd5814 hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) hoSize
      (by simp only [List.length_cons, List.length_nil]; omega)
  · intro hz hshort
    obtain ⟨_, _, rd5832⟩ := hguardOk hz
    obtain ⟨k', C', rd5844⟩ :=
      RD.uniswapPermitEcrecoverReturnWordDecodedShort
        (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
        (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
        (deadline := permitDeadlineWord I) (value := permitValueWord I)
        (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
        (ret := ⟨570⟩) (R := [sel]) rd5832 hbaseSize hshort hoSize
        (by simp only [List.length_singleton]; omega)
    exact ⟨k', C', by
      simpa [permitEcrecoverStaticcallMem] using rd5844⟩
  · intro hz ho32
    obtain ⟨_, _, rd5832⟩ := hguardOk hz
    obtain ⟨k', C', rd5844⟩ :=
      RD.uniswapPermitEcrecoverReturnWordDecoded
        (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
        (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
        (deadline := permitDeadlineWord I) (value := permitValueWord I)
        (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
        (ret := ⟨570⟩) (R := [sel]) rd5832 hbaseSize ho32 hoSize
        (by simp only [List.length_singleton]; omega)
    exact ⟨k', C', by
      simpa [permitEcrecoverStaticcallMem] using rd5844⟩

theorem uniswapPermitEcrecoverTypedCall_source
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {z : Bool} {o : ByteArray} {A_in : Substate} {callGas : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hdepth : I.depth.val < 1024)
    (hsz228 : 228 ≤ I.calldata.size)
    (hΘ : ∃ (g'' : UInt256) (A'_evm : Substate),
      (cA', σ', g'', A'_evm, z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
        (permitAfterNonceAccountMap σ_evm I) σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
        (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
        (toExecute (permitAfterNonceAccountMap σ_evm I)
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
        callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
        ((permitEcrecoverInputMem σ_evm I).readWithPadding 482 128)
        (I.depth + 1) I.header false) :
    ∃ evmCallS : EVM.State,
      typedCallViaEVM config
        (permitAfterNonceState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
        (AccountAddress.ofNat 1) "ecrecover" 0
        [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I]
        (z, evmCallS, o) false ∧
      accountMapEquiv σ' evmCallS.accountMap ∧
      evmCallS.createdAccounts = cA' ∧
      evmCallS.σ₀ = σ₀ ∧
      evmCallS.genesisBlockHeader = gh ∧
      evmCallS.blocks = bl ∧
      evmCallS.executionEnv = I := by
  obtain ⟨g'', A'_evm, hΘeq⟩ := hΘ
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmNonceS := permitAfterNonceState evmS I
  let evmE : EVM.State :=
    { evmNonceS with
      accountMap := permitAfterNonceAccountMap σ_evm I
      createdAccounts := cA
      σ₀ := σ₀
      genesisBlockHeader := gh
      blocks := bl
      executionEnv := I }
  have hdepthE : evmE.executionEnv.depth.val < 1024 := by
    simpa [evmE] using hdepth
  have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
    intro hEq
    rw [hEq] at hdepthE
    exact absurd hdepthE (by decide)
  have hdigestEq : permitDigestWord σ_evm I = permitDigestWord σ_solm I :=
    permitDigestWord_equiv hAccounts
  have hreadEq :
      (permitEcrecoverInputMem σ_solm I).readWithPadding 482 128 =
        (permitEcrecoverInputMem σ_evm I).readWithPadding 482 128 := by
    rw [permitEcrecoverInputMem_read482_128, permitEcrecoverInputMem_read482_128,
      hdigestEq]
  have hcdE :
      config.externalABI.encode? "ecrecover"
          [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I] =
        some ((permitEcrecoverInputMem σ_evm I).readWithPadding 482 128) := by
    have hcd := uniswapEcrecoverEncode_eq σ_solm I hsz228
    rwa [hreadEq] at hcd
  have hΘE :
      (cA', σ', g'', A'_evm, z, o) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes
          evmE.createdAccounts evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute evmE.accountMap (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitEcrecoverInputMem σ_evm I).readWithPadding 482 128)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header false := by
    simpa [evmE] using hΘeq
  have hStateAccounts : accountMapEquiv evmE.accountMap evmNonceS.accountMap := by
    rw [show evmNonceS.accountMap = permitAfterNonceAccountMap σ_solm I from by
      simpa [evmNonceS, evmS] using
        (permitAfterNonceState_init_accountMap
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (A := A) (I := I) (g := Sat256.ofUInt256 g))]
    simpa [evmE] using permitAfterNonceAccountMap_equiv hAccounts
  obtain ⟨σS, AS, hcallSolm, hPost⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmE) (evm_solm := evmNonceS)
      (tgt := AccountAddress.ofNat 1) (targetWord := (⟨1⟩ : UInt256))
      (name := "ecrecover")
      (args := [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I])
      (cA' := cA') (σ' := σ') (A' := A'_evm) (A_in := A_in)
      (z := z) (out := o) (g'' := g'') (callGas := callGas)
      (mem := permitEcrecoverInputMem σ_evm I) (inOff := ⟨482⟩) (inSize := ⟨128⟩)
      (callPerm := false)
      hdepthNe rfl hcdE hΘE
      hStateAccounts
      (by simp [evmE, evmNonceS, evmS, permitAfterNonceState, permitStorageStore_sigma0,
        initState])
      (by simp [evmE, evmNonceS, evmS, permitAfterNonceState_init_createdAccounts])
      (by simp [evmE, evmNonceS, evmS, permitAfterNonceState,
        permitStorageStore_genesisBlockHeader, initState])
      (by simp [evmE, evmNonceS, evmS, permitAfterNonceState, permitStorageStore_blocks,
        initState])
      (by simp [evmE])
      (by simp [evmE, evmNonceS, evmS, permitAfterNonceState, storageStore_executionEnv,
        initState])
  let evmCallS : EVM.State :=
    { evmNonceS with accountMap := σS, substate := AS, createdAccounts := cA' }
  refine ⟨evmCallS, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [evmCallS] using hcallSolm
  · simpa [evmCallS] using hPost
  · simp [evmCallS]
  · simp [evmCallS, evmNonceS, evmS, permitAfterNonceState, permitStorageStore_sigma0,
      initState]
  · simp [evmCallS, evmNonceS, evmS, permitAfterNonceState,
      permitStorageStore_genesisBlockHeader, initState]
  · simp [evmCallS, evmNonceS, evmS, permitAfterNonceState, permitStorageStore_blocks,
      initState]
  · simp [evmCallS, evmNonceS, evmS, permitAfterNonceState, storageStore_executionEnv,
      initState]

theorem uniswapPermitEcrecoverStaticcallTyped_source
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hdepth : I.depth.val < 1024)
    (hsz228 : 228 ≤ I.calldata.size)
    (hstatic : ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (permitAfterNonceAccountMap σ_evm I) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute (permitAfterNonceAccountMap σ_evm I)
            (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitEcrecoverInputMem σ_evm I).readWithPadding 482 128)
          (I.depth + 1) I.header false)
      ∧ RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5814⟩
          [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨610⟩, ⟨1⟩, ⟨0⟩,
            permitDigestWord σ_evm I, permitSWord I, permitRWord I, permitVWord I,
            permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
            permitOwnerMaskedWord I, ⟨570⟩, sel]
          (permitEcrecoverStaticcallMem σ_evm I o)
          (UInt256.ofNat 20) o (cA', σ') k C
  ∧ o.size < UInt256.size) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (k C : ℕ) (evmCallS : EVM.State),
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5814⟩
        [(if z then (⟨1⟩ : UInt256) else ⟨0⟩), ⟨610⟩, ⟨1⟩, ⟨0⟩,
          permitDigestWord σ_evm I, permitSWord I, permitRWord I, permitVWord I,
          permitDeadlineWord I, permitValueWord I, permitSpenderMaskedWord I,
          permitOwnerMaskedWord I, ⟨570⟩, sel]
        (permitEcrecoverStaticcallMem σ_evm I o)
        (UInt256.ofNat 20) o (cA', σ') k C
      ∧ typedCallViaEVM config
          (permitAfterNonceState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
          (AccountAddress.ofNat 1) "ecrecover" 0
          [permitDigestValue σ_solm I, permitVValue I, permitRValue I, permitSValue I]
          (z, evmCallS, o) false
      ∧ accountMapEquiv σ' evmCallS.accountMap
      ∧ evmCallS.createdAccounts = cA'
      ∧ evmCallS.σ₀ = σ₀
      ∧ evmCallS.genesisBlockHeader = gh
      ∧ evmCallS.blocks = bl
      ∧ evmCallS.executionEnv = I
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k, C, hΘ, rd5814, hoSize⟩ := hstatic
  obtain ⟨evmCallS, hcall, hPost, hcreated, hσ0, hgenesis, hblocks, henv⟩ :=
    uniswapPermitEcrecoverTypedCall_source (g := g) hAccounts hdepth hsz228 hΘ
  exact ⟨cA', σ', z, o, k, C, evmCallS, rd5814, hcall, hPost,
    hcreated, hσ0, hgenesis, hblocks, henv, hoSize⟩

theorem uniswapPermitX_ecrecoverSignatureGuardOk
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel recovered : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hnz : UInt256.land recovered solcAddrMask ≠ ⟨0⟩)
    (hmatch : UInt256.land recovered solcAddrMask = permitOwnerMaskedWord I) :
    ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5965⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C := by
  obtain ⟨_, _, rd5844⟩ := hdecoded
  have hownerClean :
      UInt256.land (permitOwnerMaskedWord I) solcAddrMask = permitOwnerMaskedWord I := by
    apply solcAddrMask_clean
    simpa [permitOwnerMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitOwnerWord I)
  have hmatchRuntime :
      UInt256.land recovered solcAddrMask =
        UInt256.land (permitOwnerMaskedWord I) solcAddrMask := by
    rw [hownerClean]
    exact hmatch
  obtain ⟨k', C', rd5965⟩ :=
    RD.uniswapPermitEcrecoverSignatureGuardOk
      (digest := permitDigestWord σ I)
      (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
      (deadline := permitDeadlineWord I) (value := permitValueWord I)
      (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
      (ret := ⟨570⟩) (R := [sel]) rd5844 hnz hmatchRuntime
      (by simp only [List.length_singleton]; omega)
  exact ⟨k', C', by
    simpa [permitEcrecoverStaticcallMem] using rd5965⟩

theorem uniswapPermitX_approveAndReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel recovered : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    (hok : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5965⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hperm : I.perm = true)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', sstoreAccountMap I.codeOwner σ'
        (mapSlot (permitSpenderMaskedWord I) (mapSlot (permitOwnerMaskedWord I) ⟨2⟩))
        (permitValueWord I))
      ByteArray.empty := by
  obtain ⟨_, _, rd5965⟩ := hok
  have hmem :
      514 ≤ (permitEcrecoverStaticcallMem σ I o).size := by
    have hs := permitRuntimeEcrecoverStaticcallMem_size_of_size_ge
      (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
      (v := permitVWord I) (r := permitRWord I) (s := permitSWord I) (o := o)
      (permitDigestMem_size σ I) ho32 hoSize
    rw [permitEcrecoverStaticcallMem, hs]
    omega
  have hfree :
      (permitEcrecoverStaticcallMem σ I o).readWithPadding 64 32 =
        UInt256.toByteArray (⟨482⟩ : UInt256) := by
    simpa [permitEcrecoverStaticcallMem] using
      permitRuntimeEcrecoverStaticcallMem_read64_of_size_ge
        (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
        (v := permitVWord I) (r := permitRWord I) (s := permitSWord I) (o := o)
        (permitDigestMem_size σ I) ho32 hoSize
  have hcanonOwner : (permitOwnerMaskedWord I).toNat < EVM.addressModulus := by
    simpa [permitOwnerMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitOwnerWord I)
  have hcanonSpender : (permitSpenderMaskedWord I).toNat < EVM.addressModulus := by
    simpa [permitSpenderMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitSpenderWord I)
  exact _root_.UniswapV2Pair.RD.uniswapPermitApproveAndReturn20
    (recovered := recovered) (digest := permitDigestWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (R := [sel]) rd5965 hmem hfree hperm hcanonOwner hcanonSpender
    (by simp only [List.length_singleton]; omega)

theorem uniswapPermitX_approveAndReturnShort
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel recovered : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    (hok : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5965⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hperm : I.perm = true)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA', sstoreAccountMap I.codeOwner σ'
        (mapSlot (permitSpenderMaskedWord I) (mapSlot (permitOwnerMaskedWord I) ⟨2⟩))
        (permitValueWord I))
      ByteArray.empty := by
  obtain ⟨_, _, rd5965⟩ := hok
  have hmem :
      514 ≤ (permitEcrecoverStaticcallMem σ I o).size := by
    have hs := permitRuntimeEcrecoverStaticcallMem_size_of_size_lt
      (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
      (v := permitVWord I) (r := permitRWord I) (s := permitSWord I) (o := o)
      (permitDigestMem_size σ I) hshort hoSize
    rw [permitEcrecoverStaticcallMem, hs]
    omega
  have hfree :
      (permitEcrecoverStaticcallMem σ I o).readWithPadding 64 32 =
        UInt256.toByteArray (⟨482⟩ : UInt256) := by
    simpa [permitEcrecoverStaticcallMem] using
      permitRuntimeEcrecoverStaticcallMem_read64_of_size_lt
        (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
        (v := permitVWord I) (r := permitRWord I) (s := permitSWord I) (o := o)
        (permitDigestMem_size σ I) hshort hoSize
  have hcanonOwner : (permitOwnerMaskedWord I).toNat < EVM.addressModulus := by
    simpa [permitOwnerMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitOwnerWord I)
  have hcanonSpender : (permitSpenderMaskedWord I).toNat < EVM.addressModulus := by
    simpa [permitSpenderMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitSpenderWord I)
  exact _root_.UniswapV2Pair.RD.uniswapPermitApproveAndReturn20
    (recovered := recovered) (digest := permitDigestWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (R := [sel]) rd5965 hmem hfree hperm hcanonOwner hcanonSpender
    (by simp only [List.length_singleton]; omega)

theorem uniswapPermitX_ecrecoverSignatureGuardZeroReverts
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel recovered : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hzero : UInt256.land recovered solcAddrMask = ⟨0⟩)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd5844⟩ := hdecoded
  exact RD.uniswapPermitEcrecoverSignatureGuardZeroReverts
    (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (ret := ⟨570⟩) (R := [sel]) rd5844 hzero (permitDigestMem_size σ I) ho32 hoSize
    (by simp only [List.length_singleton]; omega)

theorem uniswapPermitX_ecrecoverSignatureGuardZeroRevertsShort
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel recovered : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hzero : UInt256.land recovered solcAddrMask = ⟨0⟩)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd5844⟩ := hdecoded
  exact RD.uniswapPermitEcrecoverSignatureGuardZeroRevertsShort
    (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (ret := ⟨570⟩) (R := [sel]) rd5844 hzero (permitDigestMem_size σ I) hshort hoSize
    (by simp only [List.length_singleton]; omega)

theorem uniswapPermitX_ecrecoverSignatureGuardMismatchReverts
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel recovered : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hnz : UInt256.land recovered solcAddrMask ≠ ⟨0⟩)
    (hmismatch : UInt256.land recovered solcAddrMask ≠ permitOwnerMaskedWord I)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd5844⟩ := hdecoded
  have hownerClean :
      UInt256.land (permitOwnerMaskedWord I) solcAddrMask = permitOwnerMaskedWord I := by
    apply solcAddrMask_clean
    simpa [permitOwnerMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitOwnerWord I)
  have hmismatchRuntime :
      UInt256.land recovered solcAddrMask ≠
        UInt256.land (permitOwnerMaskedWord I) solcAddrMask := by
    intro hsame
    apply hmismatch
    rwa [hownerClean] at hsame
  exact RD.uniswapPermitEcrecoverSignatureGuardMismatchReverts
    (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (ret := ⟨570⟩) (R := [sel]) rd5844 hnz hmismatchRuntime
    (permitDigestMem_size σ I) ho32 hoSize
    (by simp only [List.length_singleton]; omega)

theorem uniswapPermitX_ecrecoverSignatureGuardMismatchRevertsShort
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel recovered : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {o : ByteArray}
    (hdecoded : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5844⟩
      (recovered :: permitDigestWord σ I :: permitSWord I :: permitRWord I :: permitVWord I ::
        permitDeadlineWord I :: permitValueWord I :: permitSpenderMaskedWord I ::
        permitOwnerMaskedWord I :: ⟨570⟩ :: [sel])
      (permitEcrecoverStaticcallMem σ I o)
      (UInt256.ofNat 20) o (cA', σ') k C)
    (hnz : UInt256.land recovered solcAddrMask ≠ ⟨0⟩)
    (hmismatch : UInt256.land recovered solcAddrMask ≠ permitOwnerMaskedWord I)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd5844⟩ := hdecoded
  have hownerClean :
      UInt256.land (permitOwnerMaskedWord I) solcAddrMask = permitOwnerMaskedWord I := by
    apply solcAddrMask_clean
    simpa [permitOwnerMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (permitOwnerWord I)
  have hmismatchRuntime :
      UInt256.land recovered solcAddrMask ≠
        UInt256.land (permitOwnerMaskedWord I) solcAddrMask := by
    intro hsame
    apply hmismatch
    rwa [hownerClean] at hsame
  exact RD.uniswapPermitEcrecoverSignatureGuardMismatchRevertsShort
    (baseMem := permitDigestMem σ I) (digest := permitDigestWord σ I)
    (s := permitSWord I) (r := permitRWord I) (v := permitVWord I)
    (deadline := permitDeadlineWord I) (value := permitValueWord I)
    (spender := permitSpenderMaskedWord I) (owner := permitOwnerMaskedWord I)
    (ret := ⟨570⟩) (R := [sel]) rd5844 hnz hmismatchRuntime
    (permitDigestMem_size σ I) hshort hoSize
    (by simp only [List.length_singleton]; omega)

end UniswapV2Pair
