import Benchmarks.EAS.Attester.MultiRevokeProgress
import Benchmarks.EAS.Attester.MultiRevokeEVM
import Benchmarks.EAS.Attester.MultiRevokeEncoderLayout
import Benchmarks.EAS.Attester.MultiSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

/-- Coupled variant-indexed loop rule for a Solm `while` loop and the matching EVM loop.

This is the `while` analogue of `Reasoning.Reach.RD.execForLoopOrRevertCarryFull`: each
successful source body step must produce the next carried source/EVM state, while a reverting
source body may be paired directly with an EVM `RDrev`.
-/
theorem attesterExecWhileOrRevertCarryFull {cfg : Config} {contract : ContractDecl}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {α : Type}
    (header bodyHeader exit : UInt256) (condExpr : Expr) (body : List Stmt)
    (Inv : Nat → α → Store → EVM.State → Prop) (stk : α → List UInt256)
    (mem : α → ByteArray) (aw : α → UInt256)
    (acc : α → Batteries.RBSet AccountAddress compare × AccountMap)
    (exitStk : α → List UInt256) (exitMem : α → ByteArray) (exitAw : α → UInt256)
    (hfalse : ∀ a L evm, Inv 0 a L evm →
      evalExpr? cfg { contract := contract, locals := L } evm condExpr = .ok (.bool false))
    (hexit : ∀ a L evm, Inv 0 a L evm → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
      ∃ k' C',
        RD code ee g s0 exit (exitStk a) (exitMem a) (exitAw a) rdata (acc a) k' C')
    (htrue : ∀ v a L evm, Inv (v + 1) a L evm →
      evalExpr? cfg { contract := contract, locals := L } evm condExpr = .ok (.bool true))
    (henter : ∀ v a L evm, Inv (v + 1) a L evm → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
      ∃ k' C',
        RD code ee g s0 bodyHeader (stk a) (mem a) (aw a) rdata (acc a) k' C')
    (hbody : ∀ v a L evm, Inv (v + 1) a L evm → ∀ k C,
      RD code ee g s0 bodyHeader (stk a) (mem a) (aw a) rdata (acc a) k C →
      (ExecBlock cfg { contract := contract, locals := L } evm body .reverted ∧
        RDrev code g s0) ∨
      ∃ a' L' evm' k' C',
        (ExecBlock cfg { contract := contract, locals := L } evm body
            (.ok { contract := contract, locals := L' } evm') ∨
          ExecBlock cfg { contract := contract, locals := L } evm body
            (.continue { contract := contract, locals := L' } evm')) ∧
        Inv v a' L' evm' ∧
        RD code ee g s0 header (stk a') (mem a') (aw a') rdata (acc a') k' C') :
    ∀ v a L evm, Inv v a L evm → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
      (∃ a' L' evm' k' C',
        ExecStmt cfg { contract := contract, locals := L } evm (.while condExpr body)
          (.ok { contract := contract, locals := L' } evm') ∧
        Inv 0 a' L' evm' ∧
        RD code ee g s0 exit (exitStk a') (exitMem a') (exitAw a') rdata
          (acc a') k' C') ∨
      (ExecStmt cfg { contract := contract, locals := L } evm (.while condExpr body)
          .reverted ∧
        RDrev code g s0) := by
  intro v
  induction v with
  | zero =>
      intro a L evm hInv k C rd
      obtain ⟨k', C', rdExit⟩ := hexit a L evm hInv k C rd
      exact .inl ⟨a, L, evm, k', C', ExecStmt.whileFalse (hfalse a L evm hInv),
        hInv, rdExit⟩
  | succ v ih =>
      intro a L evm hInv k C rd
      obtain ⟨k1, C1, rdBody⟩ := henter v a L evm hInv k C rd
      rcases hbody v a L evm hInv k1 C1 rdBody with hrev | hstep
      · exact .inr ⟨ExecStmt.whileRevert (htrue v a L evm hInv) hrev.1, hrev.2⟩
      · rcases hstep with ⟨a', L', evm', k2, C2, hbodyStep, hInv', rdNext⟩
        rcases ih a' L' evm' hInv' k2 C2 rdNext with hdone | hloopRev
        · rcases hdone with ⟨a'', L'', evm'', k', C', hloop, hInv0, rdExit⟩
          rcases hbodyStep with hbodyOk | hbodyCont
          · exact .inl ⟨a'', L'', evm'', k', C',
              ExecStmt.whileTrue (htrue v a L evm hInv) hbodyOk hloop, hInv0, rdExit⟩
          · exact .inl ⟨a'', L'', evm'', k', C',
              ExecStmt.whileContinue (htrue v a L evm hInv) hbodyCont hloop, hInv0,
              rdExit⟩
        · rcases hloopRev with ⟨hloop, hrdRev⟩
          rcases hbodyStep with hbodyOk | hbodyCont
          · exact .inr
              ⟨ExecStmt.whileTrue (htrue v a L evm hInv) hbodyOk hloop, hrdRev⟩
          · exact .inr
              ⟨ExecStmt.whileContinue (htrue v a L evm hInv) hbodyCont hloop, hrdRev⟩

structure AttesterMultiRevokeOuterLoopCursor where
  idx : UInt256
  outerBase : UInt256
  schemaLen : UInt256
  secondLen : UInt256
  secondPayload : UInt256
  schemaPayload : UInt256
  ret : UInt256
  selector : UInt256
  mem : ByteArray
  aw : UInt256
  acc : Batteries.RBSet AccountAddress compare × AccountMap

def attesterMultiRevokeOuterLoopStack
    (a : AttesterMultiRevokeOuterLoopCursor) : List UInt256 :=
  [a.idx, a.outerBase, a.schemaLen, a.secondLen, a.secondPayload, a.schemaLen,
    a.schemaPayload, a.ret, a.selector]

def attesterMultiRevokeOuterLoopBudgetChunk : Nat :=
  128 + 160 * solcMaxU64

def attesterMultiRevokeEncoderOutputBudget (schemaLen : Nat) : Nat :=
  4 + 64 + attesterMultiRevokeOuterLoopBudgetChunk * schemaLen

def AttesterReadPreservedBefore (mem₀ mem₁ : ByteArray) (bound : Nat) : Prop :=
  ∀ {read : Nat} {word : UInt256},
    read + 32 ≤ mem₀.size →
    mem₀.readWithPadding read 32 = word.toByteArray →
    64 + 32 ≤ read →
    read + 32 ≤ bound →
      read + 32 ≤ mem₁.size ∧
      mem₁.readWithPadding read 32 = word.toByteArray

theorem AttesterReadPreservedBefore_innerAlloc
    {len : UInt256} {mem : ByteArray} {aw base : UInt256}
    (hbase : base = attesterInnerArrayAllocFreeWord mem aw) :
    AttesterReadPreservedBefore mem (attesterInnerArrayAllocMem len mem aw) base.toNat := by
  intro read word hmem hread hread64 hbefore
  have hreadLt : read < UInt256.size := by
    have hbaseLt : base.toNat < UInt256.size := base.val.isLt
    omega
  let readWord : UInt256 := UInt256.ofNat read
  have hreadWordToNat : readWord.toNat = read := ulit_toNat' read hreadLt
  constructor
  · exact le_trans hmem attesterInnerArrayAllocMem_size_ge
  · have hpreserve :=
      attesterInnerArrayAllocMem_readWithPadding_at_nat
        (readBase := readWord) (len := len) (readLen := word)
        (mem := mem) (aw := aw)
        (by simpa [readWord, hreadWordToNat] using hmem)
        (by simpa [readWord, hreadWordToNat] using hread)
        (by simpa [readWord, hreadWordToNat] using hread64)
        (by simpa [readWord, hreadWordToNat, hbase] using hbefore)
    simpa [readWord, hreadWordToNat] using hpreserve

def AttesterMultiRevokeOuterLoopInv
    (cA : Batteries.RBSet AccountAddress compare) (σ : AccountMap)
    (I : ExecutionEnv) (schemas schemaUids : List Value)
    (fuel : Nat) (a : AttesterMultiRevokeOuterLoopCursor)
    (L : Store) (_evm : EVM.State) : Prop :=
  ∃ i : Nat,
    L.get? "schemas" = some (.array schemas) ∧
    L.get? "schemaUids" = some (.array schemaUids) ∧
    L.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) ∧
    L.get? "multiRequests" =
      some (.array (attesterMultiRevokeRequestValuesPrefix i schemas schemaUids)) ∧
    L.get? "i" = some (.int (Int.ofNat i)) ∧
    i + fuel = schemas.length ∧
    i ≤ schemas.length ∧
    (∀ {idx value}, idx < i → lookupNth? schemaUids idx = some value →
      ∃ uids,
        value = .array uids ∧
        uids.length ≠ 0 ∧
        uids.length ≤ solcMaxU64 ∧
        uids.length < 2 ^ 256 ∧
        (∀ {j uid}, lookupNth? uids j = some uid →
          normalizeRawBoolWord? uid = .ok uid)) ∧
    i < UInt256.size ∧
    a.idx = UInt256.ofNat i ∧
    a.idx.toNat = i ∧
    a.outerBase = (⟨128⟩ : UInt256) ∧
    a.schemaLen = attesterFirstArrayLengthWord I ∧
    a.schemaLen.toNat = schemas.length ∧
    a.secondLen = attesterSecondArrayLengthWord I ∧
    a.secondLen.toNat = schemaUids.length ∧
    a.secondPayload = attesterSecondArrayPayloadStartWord I ∧
    a.schemaPayload = (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩ ∧
    a.ret = (⟨97⟩ : UInt256) ∧
    a.selector = solcSelectorWord I ∧
    a.acc = (cA, σ) ∧
    3 ≤ a.aw.toNat ∧
    a.aw.toNat * 32 < UInt256.size ∧
    a.mem.readWithPadding a.outerBase.toNat 32 = UInt256.toByteArray a.schemaLen ∧
    a.outerBase.toNat + 32 ≤ a.mem.size ∧
    64 + 32 ≤ a.outerBase.toNat ∧
    64 + 32 ≤ (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat ∧
    a.outerBase.toNat + 32 ≤ (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat ∧
    a.outerBase.toNat + 32 + 32 * schemas.length ≤
      (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat ∧
    AttesterMultiRevokeRequestsReadLayoutBounded schemas schemaUids i a.mem a.outerBase
      (a.outerBase.toNat + 32 + 32 * schemas.length)
      (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat ∧
    (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat +
      attesterMultiRevokeEncoderOutputBudget schemas.length + 128 +
      attesterMultiRevokeOuterLoopBudgetChunk * fuel < UInt256.size

theorem AttesterMultiRevokeOuterLoopInv.source
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {I : ExecutionEnv} {schemas schemaUids : List Value}
    {fuel : Nat} {a : AttesterMultiRevokeOuterLoopCursor} {L : Store} {evm : EVM.State}
    (hInv : AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids fuel a L evm) :
    attesterMultiRevokeOuterSourceLoopInv schemas schemaUids fuel L := by
  rcases hInv with
    ⟨i, hschemas, hschemaUids, hschemaLength, hrequests, hi, hvariant, hile,
      _hprocessed, _hisize, _hidx, _hidxToNat, _houterBase, _hschemaLen,
      _hschemaLenToNat, _hsecondLen, _hsecondLenToNat, _hsecondPayload,
      _hschemaPayload, _hret, _hselector, _hacc, _hawGe, _hawMul, _houterRead,
      _houterMemSize, _houter64, _hbaseGe, _houterBeforeBase,
      _houterSlotsBeforeBase, _hreadLayout, _hfreeBudget⟩
  exact ⟨i, hschemas, hschemaUids, hschemaLength, hrequests, hi, hvariant, hile⟩

theorem AttesterMultiRevokeOuterLoopInv.done
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {I : ExecutionEnv} {schemas schemaUids : List Value}
    {a : AttesterMultiRevokeOuterLoopCursor} {L : Store} {evm : EVM.State}
    (hInv : AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids 0 a L evm) :
    L.get? "multiRequests" =
        some (.array (attesterMultiRevokeRequestValuesPrefix schemas.length schemas schemaUids)) ∧
    L.get? "i" = some (.int (Int.ofNat schemas.length)) ∧
    a.idx = UInt256.ofNat schemas.length ∧
    a.idx.toNat = schemas.length ∧
    a.acc = (cA, σ) := by
  rcases hInv with
    ⟨i, _hschemas, _hschemaUids, _hschemaLength, hrequests, hi, hvariant, _hile,
      _hprocessed, _hisize, hidx, hidxToNat, _houterBase, _hschemaLen,
      _hschemaLenToNat, _hsecondLen, _hsecondLenToNat, _hsecondPayload,
      _hschemaPayload, _hret, _hselector, hacc, _hawGe, _hawMul, _houterRead,
      _houterMemSize, _houter64, _hbaseGe, _houterBeforeBase,
      _houterSlotsBeforeBase, _hreadLayout, _hfreeBudget⟩
  have hidone : i = schemas.length := by omega
  subst hidone
  exact ⟨hrequests, hi, hidx, hidxToNat, hacc⟩

theorem AttesterMultiRevokeOuterLoopInv.cond_false
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {I : ExecutionEnv} {schemas schemaUids : List Value}
    {a : AttesterMultiRevokeOuterLoopCursor} {L : Store} {evm : EVM.State}
    (hInv : AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids 0 a L evm) :
    UInt256.lt a.idx a.schemaLen = ⟨0⟩ := by
  rcases hInv with
    ⟨i, _hschemas, _hschemaUids, _hschemaLength, _hrequests, _hi, hvariant,
      _hile, _hprocessed, _hisize, _hidx, hidxToNat, _houterBase, _hschemaLen,
      hschemaLenToNat, _hsecondLen, _hsecondLenToNat, _hsecondPayload,
      _hschemaPayload, _hret, _hselector, _hacc, _hawGe, _hawMul, _houterRead,
      _houterMemSize, _houter64, _hbaseGe, _houterBeforeBase,
      _houterSlotsBeforeBase, _hreadLayout, _hfreeBudget⟩
  apply ult_zero
  rw [hidxToNat, hschemaLenToNat]
  omega

theorem AttesterMultiRevokeOuterLoopInv.cond_true
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {I : ExecutionEnv} {schemas schemaUids : List Value}
    {fuel : Nat} {a : AttesterMultiRevokeOuterLoopCursor} {L : Store} {evm : EVM.State}
    (hInv : AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids (fuel + 1) a L evm) :
    UInt256.lt a.idx a.schemaLen = ⟨1⟩ := by
  rcases hInv with
    ⟨i, _hschemas, _hschemaUids, _hschemaLength, _hrequests, _hi, hvariant,
      _hile, _hprocessed, _hisize, _hidx, hidxToNat, _houterBase, _hschemaLen,
      hschemaLenToNat, _hsecondLen, _hsecondLenToNat, _hsecondPayload,
      _hschemaPayload, _hret, _hselector, _hacc, _hawGe, _hawMul, _houterRead,
      _houterMemSize, _houter64, _hbaseGe, _houterBeforeBase,
      _houterSlotsBeforeBase, _hreadLayout, _hfreeBudget⟩
  apply ult_one
  rw [hidxToNat, hschemaLenToNat]
  omega

/-- BlindAuction-style runner for the `multiRevoke` outer source loop.

The only loop-specific proof obligation is `hbody`: one source body execution from PC 344
must either pair with an EVM revert, or produce the next cursor back at PC 335. The false
branch exits through PC 698 and the true branch enters PC 344.
-/
theorem attesterMultiRevokeOuterLoop_from_bodyOutcome_or_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} (imm : AttesterImmutables)
    (Inv : Nat → AttesterMultiRevokeOuterLoopCursor → Store → EVM.State → Prop)
    (hfalse : ∀ a L evm, Inv 0 a L evm →
      evalExpr? (config imm) { contract := contract imm, locals := L } evm
        attesterMultiRevokeOuterSourceLoopCond = .ok (.bool false))
    (hexit : ∀ a L evm, Inv 0 a L evm → ∀ k C,
      RD (patchedRuntime imm) I g (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        (attesterMultiRevokeOuterLoopStack a) a.mem a.aw ByteArray.empty a.acc k C →
      ∃ k' C',
        RD (patchedRuntime imm) I g (initState cA gh bl σ σ₀ g A I) (⟨698⟩ : UInt256)
          (attesterMultiRevokeOuterLoopStack a) a.mem a.aw ByteArray.empty a.acc k' C')
    (htrue : ∀ fuel a L evm, Inv (fuel + 1) a L evm →
      evalExpr? (config imm) { contract := contract imm, locals := L } evm
        attesterMultiRevokeOuterSourceLoopCond = .ok (.bool true))
    (henter : ∀ fuel a L evm, Inv (fuel + 1) a L evm → ∀ k C,
      RD (patchedRuntime imm) I g (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        (attesterMultiRevokeOuterLoopStack a) a.mem a.aw ByteArray.empty a.acc k C →
      ∃ k' C',
        RD (patchedRuntime imm) I g (initState cA gh bl σ σ₀ g A I) (⟨344⟩ : UInt256)
          (attesterMultiRevokeOuterLoopStack a) a.mem a.aw ByteArray.empty a.acc k' C')
    (hbody : ∀ fuel a L evm, Inv (fuel + 1) a L evm → ∀ k C,
      RD (patchedRuntime imm) I g (initState cA gh bl σ σ₀ g A I) (⟨344⟩ : UInt256)
        (attesterMultiRevokeOuterLoopStack a) a.mem a.aw ByteArray.empty a.acc k C →
      (ExecBlock (config imm) { contract := contract imm, locals := L } evm
          attesterMultiRevokeOuterSourceLoopBody .reverted ∧
        RDrev (patchedRuntime imm) g (initState cA gh bl σ σ₀ g A I)) ∨
      ∃ a' L' evm' k' C',
        (ExecBlock (config imm) { contract := contract imm, locals := L } evm
            attesterMultiRevokeOuterSourceLoopBody
            (.ok { contract := contract imm, locals := L' } evm') ∨
          ExecBlock (config imm) { contract := contract imm, locals := L } evm
            attesterMultiRevokeOuterSourceLoopBody
            (.continue { contract := contract imm, locals := L' } evm')) ∧
        Inv fuel a' L' evm' ∧
        RD (patchedRuntime imm) I g (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
          (attesterMultiRevokeOuterLoopStack a') a'.mem a'.aw ByteArray.empty a'.acc k' C') :
    ∀ fuel a L evm, Inv fuel a L evm → ∀ k C,
      RD (patchedRuntime imm) I g (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        (attesterMultiRevokeOuterLoopStack a) a.mem a.aw ByteArray.empty a.acc k C →
      (∃ a' L' evm' k' C',
        ExecStmt (config imm) { contract := contract imm, locals := L } evm
          (.while attesterMultiRevokeOuterSourceLoopCond attesterMultiRevokeOuterSourceLoopBody)
          (.ok { contract := contract imm, locals := L' } evm') ∧
        Inv 0 a' L' evm' ∧
        RD (patchedRuntime imm) I g (initState cA gh bl σ σ₀ g A I) (⟨698⟩ : UInt256)
          (attesterMultiRevokeOuterLoopStack a') a'.mem a'.aw ByteArray.empty a'.acc k' C') ∨
      (ExecStmt (config imm) { contract := contract imm, locals := L } evm
          (.while attesterMultiRevokeOuterSourceLoopCond attesterMultiRevokeOuterSourceLoopBody)
          .reverted ∧
        RDrev (patchedRuntime imm) g (initState cA gh bl σ σ₀ g A I)) := by
  exact
    attesterExecWhileOrRevertCarryFull
      (cfg := config imm) (contract := contract imm)
      (code := patchedRuntime imm) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := ByteArray.empty)
      (header := (⟨335⟩ : UInt256)) (bodyHeader := (⟨344⟩ : UInt256))
      (exit := (⟨698⟩ : UInt256))
      (condExpr := attesterMultiRevokeOuterSourceLoopCond)
      (body := attesterMultiRevokeOuterSourceLoopBody)
      (Inv := Inv) (stk := attesterMultiRevokeOuterLoopStack)
      (mem := fun a => a.mem) (aw := fun a => a.aw) (acc := fun a => a.acc)
      (exitStk := attesterMultiRevokeOuterLoopStack)
      (exitMem := fun a => a.mem) (exitAw := fun a => a.aw)
      hfalse hexit htrue henter hbody

/-- Variant of `attesterMultiRevokeOuterLoop_from_bodyOutcome_or_revert` for iteration
lemmas that start from the loop header itself. This matches the current `multiRevoke`
EVM helpers, which include the bytecode guard step in the per-iteration theorem.
-/
theorem attesterMultiRevokeOuterLoop_from_headerBodyOutcome_or_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} (imm : AttesterImmutables)
    (Inv : Nat → AttesterMultiRevokeOuterLoopCursor → Store → EVM.State → Prop)
    (hfalse : ∀ a L evm, Inv 0 a L evm →
      evalExpr? (config imm) { contract := contract imm, locals := L } evm
        attesterMultiRevokeOuterSourceLoopCond = .ok (.bool false))
    (hexit : ∀ a L evm, Inv 0 a L evm → ∀ k C,
      RD (patchedRuntime imm) I g (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        (attesterMultiRevokeOuterLoopStack a) a.mem a.aw ByteArray.empty a.acc k C →
      ∃ k' C',
        RD (patchedRuntime imm) I g (initState cA gh bl σ σ₀ g A I) (⟨698⟩ : UInt256)
          (attesterMultiRevokeOuterLoopStack a) a.mem a.aw ByteArray.empty a.acc k' C')
    (htrue : ∀ fuel a L evm, Inv (fuel + 1) a L evm →
      evalExpr? (config imm) { contract := contract imm, locals := L } evm
        attesterMultiRevokeOuterSourceLoopCond = .ok (.bool true))
    (hbody : ∀ fuel a L evm, Inv (fuel + 1) a L evm → ∀ k C,
      RD (patchedRuntime imm) I g (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        (attesterMultiRevokeOuterLoopStack a) a.mem a.aw ByteArray.empty a.acc k C →
      (ExecBlock (config imm) { contract := contract imm, locals := L } evm
          attesterMultiRevokeOuterSourceLoopBody .reverted ∧
        RDrev (patchedRuntime imm) g (initState cA gh bl σ σ₀ g A I)) ∨
      ∃ a' L' evm' k' C',
        (ExecBlock (config imm) { contract := contract imm, locals := L } evm
            attesterMultiRevokeOuterSourceLoopBody
            (.ok { contract := contract imm, locals := L' } evm') ∨
          ExecBlock (config imm) { contract := contract imm, locals := L } evm
            attesterMultiRevokeOuterSourceLoopBody
            (.continue { contract := contract imm, locals := L' } evm')) ∧
        Inv fuel a' L' evm' ∧
        RD (patchedRuntime imm) I g (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
          (attesterMultiRevokeOuterLoopStack a') a'.mem a'.aw ByteArray.empty a'.acc k' C') :
    ∀ fuel a L evm, Inv fuel a L evm → ∀ k C,
      RD (patchedRuntime imm) I g (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        (attesterMultiRevokeOuterLoopStack a) a.mem a.aw ByteArray.empty a.acc k C →
      (∃ a' L' evm' k' C',
        ExecStmt (config imm) { contract := contract imm, locals := L } evm
          (.while attesterMultiRevokeOuterSourceLoopCond attesterMultiRevokeOuterSourceLoopBody)
          (.ok { contract := contract imm, locals := L' } evm') ∧
        Inv 0 a' L' evm' ∧
        RD (patchedRuntime imm) I g (initState cA gh bl σ σ₀ g A I) (⟨698⟩ : UInt256)
          (attesterMultiRevokeOuterLoopStack a') a'.mem a'.aw ByteArray.empty a'.acc k' C') ∨
      (ExecStmt (config imm) { contract := contract imm, locals := L } evm
          (.while attesterMultiRevokeOuterSourceLoopCond attesterMultiRevokeOuterSourceLoopBody)
          .reverted ∧
        RDrev (patchedRuntime imm) g (initState cA gh bl σ σ₀ g A I)) := by
  refine
    attesterExecWhileOrRevertCarryFull
      (cfg := config imm) (contract := contract imm)
      (code := patchedRuntime imm) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := ByteArray.empty)
      (header := (⟨335⟩ : UInt256)) (bodyHeader := (⟨335⟩ : UInt256))
      (exit := (⟨698⟩ : UInt256))
      (condExpr := attesterMultiRevokeOuterSourceLoopCond)
      (body := attesterMultiRevokeOuterSourceLoopBody)
      (Inv := Inv) (stk := attesterMultiRevokeOuterLoopStack)
      (mem := fun a => a.mem) (aw := fun a => a.aw) (acc := fun a => a.acc)
      (exitStk := attesterMultiRevokeOuterLoopStack)
      (exitMem := fun a => a.mem) (exitAw := fun a => a.aw)
      hfalse hexit htrue ?_ hbody
  intro _fuel _a _L _evm _hInv k C rd
  exact ⟨k, C, rd⟩

theorem attesterUInt256_lt_zero_of_toNat_ne_zero {x : UInt256}
    (hne : x.toNat ≠ 0) :
    UInt256.lt (⟨0⟩ : UInt256) x = ⟨1⟩ := by
  apply ult_one
  rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
  omega

private theorem attester_slt_one_low_at {a b : UInt256}
    (hlt : a.toNat < b.toNat) (hb : b.toNat < 2 ^ 255) :
    UInt256.slt a b = ⟨1⟩ := by
  unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
  rw [if_neg (by omega : ¬ a.toNat ≥ 2 ^ 255),
      if_neg (by omega : ¬ b.toNat ≥ 2 ^ 255)]
  rw [decide_eq_true (show a < b by
    show a.toNat < b.toNat
    exact hlt)]
  native_decide

private theorem attester_sgt_zero_low_at {a b : UInt256}
    (hle : a.toNat ≤ b.toNat) (hb : b.toNat < 2 ^ 255) :
    UInt256.sgt a b = ⟨0⟩ := by
  unfold UInt256.sgt UInt256.sgtBool UInt256.fromBool Bool.toUInt256
  rw [if_neg (by omega : ¬ a.toNat ≥ 2 ^ 255),
      if_neg (by omega : ¬ b.toNat ≥ 2 ^ 255)]
  rw [decide_eq_false (show ¬ a > b by
    show ¬ a.toNat > b.toNat
    omega)]
  native_decide

set_option maxHeartbeats 1000000 in
theorem attesterMultiRevokeInnerArrayGuardFacts_of_decode_at {I : ExecutionEnv}
    {idx len relativeOffset : Nat} {inner : List Value} {innerEnd : Nat}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenRead : readNat? (I.calldata.toList.drop 4)
        (calldataWord I.calldata 36).toNat = some len)
    (hlenMax : ¬ solcMaxLen DecodeMode.modern < len)
    (hidx : idx < len)
    (hreadAt : readNat? (I.calldata.toList.drop 4)
        ((calldataWord I.calldata 36).toNat + 32 + 32 * idx) =
      some relativeOffset)
    (hinner : decodeABIValue? (.dynamicArray bytes32) (I.calldata.toList.drop 4)
        ((calldataWord I.calldata 36).toNat + 32 + relativeOffset) =
      some (.array inner, innerEnd))
    (hsizeSigned : I.calldata.size < 2 ^ 255) :
    UInt256.lt (UInt256.ofNat idx) (attesterSecondArrayLengthWord I) = ⟨1⟩ ∧
    UInt256.slt
        (attesterMultiRevokeInnerArrayOffsetWord I
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)))
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size)
            (attesterSecondArrayPayloadStartWord I))
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩ ∧
    UInt256.gt
        (attesterMultiRevokeInnerArrayLengthWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) =
      ⟨0⟩ ∧
    UInt256.sgt
        (attesterMultiRevokeInnerArrayPayloadWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)))
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft
            (attesterMultiRevokeInnerArrayLengthWord I
              (attesterSecondArrayPayloadStartWord I)
              (attesterMultiRevokeInnerArrayHeadWord
                (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))) ⟨5⟩)) =
      ⟨0⟩ ∧
    (attesterMultiRevokeInnerArrayLengthWord I
        (attesterSecondArrayPayloadStartWord I)
        (attesterMultiRevokeInnerArrayHeadWord
          (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat =
      inner.length := by
  have hinner' :
      decodeABIValue? (.dynamicArray (.elem (ElemType.bytes bytes32Width)))
          (I.calldata.toList.drop 4)
          ((calldataWord I.calldata 36).toNat + 32 + relativeOffset) =
        some (.array inner, innerEnd) := by
    simpa [bytes32] using hinner
  obtain ⟨innerLen, hreadLen, hinnerLenMax, hend, hendLe, hlenValues⟩ :=
    decodeABIValue_dynamicArray_elem32_facts hinner'
  have hsize : I.calldata.size < UInt256.size := lt_size_of_lt_sign hsizeSigned
  have hdropLen : (I.calldata.toList.drop 4).length = I.calldata.size - 4 := by
    rw [List.length_drop]
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
  have hbaseToNat :
      (attesterSecondArrayPayloadStartWord I).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 :=
    attesterSecondArrayPayloadStart_toNat (I := I) hoffMax
  have hlenReadEq :
      len = (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat :=
    readNat_drop4_at_some_eq_calldataWord (cd := I.calldata) hlenRead
  have hsecondLenToNat :
      (attesterSecondArrayLengthWord I).toNat = len := by
    rw [attesterSecondArrayLengthWord_toNat (I := I) hoffMax, ← hlenReadEq]
  have hlenLeU64 : len ≤ solcMaxU64 := by
    exact Nat.le_of_not_gt (by simpa [solcMaxLen] using hlenMax)
  have hidxSize : idx < UInt256.size := by
    norm_num [solcMaxU64, UInt256.size] at hlenLeU64 ⊢
    omega
  have hidxWordToNat : (UInt256.ofNat idx).toNat = idx :=
    ulit_toNat' idx hidxSize
  have hidxSecond :
      UInt256.lt (UInt256.ofNat idx) (attesterSecondArrayLengthWord I) = ⟨1⟩ := by
    apply ult_one
    rw [hidxWordToNat, hsecondLenToNat]
    exact hidx
  have hoffLe : (calldataWord I.calldata 36).toNat ≤ solcMaxU64 :=
    Nat.le_of_not_gt hoffMax
  have hinnerLenReadSizeEarly := readNat?_some_length hreadLen
  have hinnerHeadInCalldataEarly :
      4 + ((calldataWord I.calldata 36).toNat + 32 + relativeOffset) + 32 ≤
        I.calldata.size := by
    rw [hdropLen] at hinnerLenReadSizeEarly
    omega
  have hmulToNat :
      (UInt256.mul (⟨32⟩ : UInt256) (UInt256.ofNat idx)).toNat =
        32 * idx := by
    rw [u256_mul_toNat]
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide, hidxWordToNat]
    exact Nat.mod_eq_of_lt (by
      norm_num [solcMaxU64, UInt256.size] at hlenLeU64 ⊢
      omega)
  have hheadToNat :
      (attesterMultiRevokeInnerArrayHeadWord
          (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 + 32 * idx := by
    unfold attesterMultiRevokeInnerArrayHeadWord
    rw [uadd_toNat, hbaseToNat, hmulToNat]
    exact Nat.mod_eq_of_lt (by
      norm_num [solcMaxU64, UInt256.size] at hoffLe hlenLeU64 ⊢
      omega)
  have hoffWordToNat :
      (attesterMultiRevokeInnerArrayOffsetWord I
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat =
        relativeOffset := by
    unfold attesterMultiRevokeInnerArrayOffsetWord
    rw [hheadToNat]
    have hreadEq :=
      readNat_drop4_at_some_eq_calldataWord (cd := I.calldata) hreadAt
    simpa [Nat.add_assoc] using hreadEq.symm
  have hstartToNat :
      (attesterMultiRevokeInnerArrayStartWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 + relativeOffset := by
    unfold attesterMultiRevokeInnerArrayStartWord
    rw [uadd_toNat, hbaseToNat, hoffWordToNat]
    exact Nat.mod_eq_of_lt (by
      omega)
  have hlenWordToNat :
      (attesterMultiRevokeInnerArrayLengthWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat =
        innerLen := by
    unfold attesterMultiRevokeInnerArrayLengthWord
    rw [hstartToNat]
    have hreadEq :=
      readNat_drop4_at_some_eq_calldataWord (cd := I.calldata) hreadLen
    simpa [Nat.add_assoc] using hreadEq.symm
  have hinnerLenWordOk :
      UInt256.gt
          (attesterMultiRevokeInnerArrayLengthWord I
            (attesterSecondArrayPayloadStartWord I)
            (attesterMultiRevokeInnerArrayHeadWord
              (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) =
        ⟨0⟩ := by
    apply ugt_zero
    have hmaxToNat :
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat =
          solcMaxU64 := by
      native_decide
    rw [hlenWordToNat, hmaxToNat]
    exact Nat.le_of_not_gt hinnerLenMax
  have hinnerLenReadSize := readNat?_some_length hreadLen
  have hinnerHeadInCalldata :
      4 + ((calldataWord I.calldata 36).toNat + 32 + relativeOffset) + 32 ≤
        I.calldata.size := by
    rw [hdropLen] at hinnerLenReadSize
    omega
  have hpayloadInCalldata :
      4 + ((calldataWord I.calldata 36).toNat + 32 + relativeOffset + 32 +
          32 * innerLen) ≤ I.calldata.size := by
    rw [hend] at hendLe
    rw [hdropLen] at hendLe
    omega
  have hsubHeadToNat :
      (UInt256.sub (UInt256.ofNat I.calldata.size)
          (attesterSecondArrayPayloadStartWord I)).toNat =
        I.calldata.size - (4 + (calldataWord I.calldata 36).toNat + 32) := by
    rw [usub_toNat]
    · rw [ulit_toNat' I.calldata.size hsize, hbaseToNat]
    · rw [ulit_toNat' I.calldata.size hsize, hbaseToNat]
      omega
  have hrhsOffsetToNat :
      (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size)
            (attesterSecondArrayPayloadStartWord I))
          (UInt256.lnot (⟨30⟩ : UInt256))).toNat =
        I.calldata.size - (4 + (calldataWord I.calldata 36).toNat + 32) - 31 := by
    change ((UInt256.sub (UInt256.ofNat I.calldata.size)
        (attesterSecondArrayPayloadStartWord I) + UInt256.lnot (⟨30⟩ : UInt256)).toNat =
      I.calldata.size - (4 + (calldataWord I.calldata 36).toNat + 32) - 31)
    rw [uadd_toNat, hsubHeadToNat]
    have hlnot : (UInt256.lnot (⟨30⟩ : UInt256)).toNat = UInt256.size - 31 := by
      native_decide
    rw [hlnot]
    have hsplit :
        I.calldata.size - (4 + (calldataWord I.calldata 36).toNat + 32) +
            (UInt256.size - 31) =
          UInt256.size +
            (I.calldata.size - (4 + (calldataWord I.calldata 36).toNat + 32) - 31) := by
      omega
    rw [hsplit, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by
      have hleSub :
          I.calldata.size - (4 + (calldataWord I.calldata 36).toNat + 32) - 31 ≤
            I.calldata.size := by
        omega
      exact lt_of_le_of_lt hleSub hsize)
  have hoffsetGuard :
      UInt256.slt
          (attesterMultiRevokeInnerArrayOffsetWord I
            (attesterMultiRevokeInnerArrayHeadWord
              (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)))
          (UInt256.add
            (UInt256.sub (UInt256.ofNat I.calldata.size)
              (attesterSecondArrayPayloadStartWord I))
            (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩ := by
    apply attester_slt_one_low_at
    · rw [hoffWordToNat, hrhsOffsetToNat]
      omega
    · rw [hrhsOffsetToNat]
      omega
  have hinnerPayloadStartToNat :
      (attesterMultiRevokeInnerArrayPayloadWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 + relativeOffset + 32 := by
    unfold attesterMultiRevokeInnerArrayPayloadWord
    rw [uadd_toNat, hstartToNat]
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    exact Nat.mod_eq_of_lt (by
      omega)
  have hshiftLenToNat :
      (UInt256.shiftLeft
          (attesterMultiRevokeInnerArrayLengthWord I
            (attesterSecondArrayPayloadStartWord I)
            (attesterMultiRevokeInnerArrayHeadWord
              (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))) ⟨5⟩).toNat =
        32 * innerLen := by
    have hle :
        (attesterMultiRevokeInnerArrayLengthWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat ≤
          solcMaxU64 := by
      rw [hlenWordToNat]
      exact Nat.le_of_not_gt hinnerLenMax
    simpa [hlenWordToNat] using
      attesterShiftLeft5_toNat_of_le
        (attesterMultiRevokeInnerArrayLengthWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))) hle
  have hsubPayloadToNat :
      (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft
            (attesterMultiRevokeInnerArrayLengthWord I
              (attesterSecondArrayPayloadStartWord I)
              (attesterMultiRevokeInnerArrayHeadWord
                (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))) ⟨5⟩)).toNat =
        I.calldata.size - 32 * innerLen := by
    rw [usub_toNat]
    · rw [ulit_toNat' I.calldata.size hsize, hshiftLenToNat]
    · rw [ulit_toNat' I.calldata.size hsize, hshiftLenToNat]
      omega
  have hpayloadGuard :
      UInt256.sgt
          (attesterMultiRevokeInnerArrayPayloadWord I
            (attesterSecondArrayPayloadStartWord I)
            (attesterMultiRevokeInnerArrayHeadWord
              (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)))
          (UInt256.sub (UInt256.ofNat I.calldata.size)
            (UInt256.shiftLeft
              (attesterMultiRevokeInnerArrayLengthWord I
                (attesterSecondArrayPayloadStartWord I)
                (attesterMultiRevokeInnerArrayHeadWord
                  (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))) ⟨5⟩)) =
        ⟨0⟩ := by
    apply attester_sgt_zero_low_at
    · rw [hinnerPayloadStartToNat, hsubPayloadToNat]
      omega
    · rw [hsubPayloadToNat]
      omega
  exact ⟨hidxSecond, hoffsetGuard, hinnerLenWordOk, hpayloadGuard, by
    rw [hlenWordToNat, hlenValues]⟩

theorem attesterMultiRevokeInnerArrayCurrentFacts_of_decode_at
    (v : AttesterImmutables) {I : ExecutionEnv} {callargs : Store}
    {schemaUids inner : List Value} {idx : Nat}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs)
    (hSchemaUids : callargs.get? "schemaUids" = some (.array schemaUids))
    (hlookup : lookupNth? schemaUids idx = some (.array inner))
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsizeSigned : I.calldata.size < 2 ^ 255) :
    UInt256.lt (UInt256.ofNat idx) (attesterSecondArrayLengthWord I) = ⟨1⟩ ∧
    UInt256.slt
        (attesterMultiRevokeInnerArrayOffsetWord I
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)))
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size)
            (attesterSecondArrayPayloadStartWord I))
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩ ∧
    UInt256.gt
        (attesterMultiRevokeInnerArrayLengthWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) =
      ⟨0⟩ ∧
    UInt256.sgt
        (attesterMultiRevokeInnerArrayPayloadWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)))
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft
            (attesterMultiRevokeInnerArrayLengthWord I
              (attesterSecondArrayPayloadStartWord I)
              (attesterMultiRevokeInnerArrayHeadWord
                (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))) ⟨5⟩)) =
      ⟨0⟩ ∧
    (attesterMultiRevokeInnerArrayLengthWord I
        (attesterSecondArrayPayloadStartWord I)
        (attesterMultiRevokeInnerArrayHeadWord
          (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx))).toNat =
      inner.length ∧
    inner.length ≤ solcMaxU64 ∧
    (inner.length = 0 →
      attesterMultiRevokeInnerArrayLengthWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)) =
        ⟨0⟩) ∧
    (inner.length ≠ 0 →
      attesterMultiRevokeInnerArrayLengthWord I
          (attesterSecondArrayPayloadStartWord I)
          (attesterMultiRevokeInnerArrayHeadWord
            (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)) ≠
        ⟨0⟩) := by
  obtain ⟨len, relativeOffset, innerEnd, hlenRead, hlenMax, hidx, hreadAt,
      hinner⟩ :=
    attesterDecode_multiRevoke_inner_decode_at v hdec hSchemaUids hlookup
  obtain ⟨hidxSecond, hoffsetOk, hlenOk, hpayloadOk, hlenToNat⟩ :=
    attesterMultiRevokeInnerArrayGuardFacts_of_decode_at
      (I := I) (idx := idx) (len := len) (relativeOffset := relativeOffset)
      (inner := inner) (innerEnd := innerEnd)
      hoffMax hlenRead hlenMax hidx hreadAt hinner hsizeSigned
  have hinnerLengthLe : inner.length ≤ solcMaxU64 := by
    rw [← hlenToNat]
    apply Nat.le_of_not_gt
    intro hgt
    have hmaxToNat :
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat =
          solcMaxU64 := by
      native_decide
    have hgtWord : UInt256.gt
          (attesterMultiRevokeInnerArrayLengthWord I
            (attesterSecondArrayPayloadStartWord I)
            (attesterMultiRevokeInnerArrayHeadWord
              (attesterSecondArrayPayloadStartWord I) (UInt256.ofNat idx)))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) =
        ⟨1⟩ := by
      apply ugt_one
      rw [hmaxToNat]
      exact hgt
    rw [hgtWord] at hlenOk
    exact (by decide : (⟨1⟩ : UInt256) ≠ (⟨0⟩ : UInt256)) hlenOk
  refine ⟨hidxSecond, hoffsetOk, hlenOk, hpayloadOk, hlenToNat, hinnerLengthLe, ?_, ?_⟩
  · intro hzero
    exact uint256_toNat_eq_zero (by rw [hlenToNat, hzero])
  · intro hne hzero
    have hzeroNat := congrArg UInt256.toNat hzero
    rw [hlenToNat] at hzeroNat
    exact hne hzeroNat

abbrev attesterMultiRevokeInnerArrayInitStackAt
    (base len payload : UInt256) (tail : List UInt256)
    (a : AttesterMultiRevokeInnerArrayInitState) : List UInt256 :=
  a.slot :: a.remaining :: base :: ⟨0⟩ :: len :: len :: payload :: tail

abbrev attesterMultiRevokeInnerArrayInitExitStackAt
    (base len payload : UInt256) (tail : List UInt256)
    (_a : AttesterMultiRevokeInnerArrayInitState) : List UInt256 :=
  ⟨0⟩ :: base :: len :: len :: payload :: tail

structure attesterMultiRevokeInnerInitReadInvAt
    (I : ExecutionEnv) (base len outerBase schemaLen : UInt256)
    (n : Nat) (b : AttesterMultiRevokeInnerArrayInitState) : Prop where
  remaining : b.remaining = UInt256.ofNat (n + 1)
  bound : n + 1 < UInt256.size
  awGe : 3 ≤ b.aw.toNat
  awMul : b.aw.toNat * 32 < UInt256.size
  read : b.mem.readWithPadding base.toNat 32 = UInt256.toByteArray len
  memSize : base.toNat + 32 ≤ b.mem.size
  le : n + 1 ≤ len.toNat
  baseGe : 64 + 32 ≤ base.toNat
  freeGe : base.toNat + 32 ≤ (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat
  freeExact :
    (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat =
      base.toNat + 32 + 32 * len.toNat + 64 * (len.toNat - (n + 1))
  freeBound :
    (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat +
      64 * (n + 1) < UInt256.size
  freeSpare :
    (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat +
      64 * (n + 1) + 64 * len.toNat + 96 < UInt256.size
  slotGe : base.toNat + 32 ≤ b.slot.toNat
  slotBound : b.slot.toNat + 32 * (n + 1) + 63 < UInt256.size
  baseSlot63 : base.toNat + 32 + 32 * len.toNat + 63 < UInt256.size
  outerRead : b.mem.readWithPadding outerBase.toNat 32 = UInt256.toByteArray schemaLen
  outerMemSize : outerBase.toNat + 32 ≤ b.mem.size
  outer64 : 64 + 32 ≤ outerBase.toNat
  outerBeforeBase : outerBase.toNat + 32 ≤ base.toNat

theorem attesterMultiRevokeInnerInitReadInvAt_remaining
    {I : ExecutionEnv} {base len outerBase schemaLen : UInt256}
    {n : Nat} {b : AttesterMultiRevokeInnerArrayInitState}
    (hInv : attesterMultiRevokeInnerInitReadInvAt I base len outerBase schemaLen n b) :
    b.remaining = UInt256.ofNat (n + 1) := by
  exact hInv.remaining

theorem attesterMultiRevokeInnerInitReadInvAt_bound
    {I : ExecutionEnv} {base len outerBase schemaLen : UInt256}
    {n : Nat} {b : AttesterMultiRevokeInnerArrayInitState}
    (hInv : attesterMultiRevokeInnerInitReadInvAt I base len outerBase schemaLen n b) :
    n + 1 < UInt256.size := by
  exact hInv.bound

set_option maxHeartbeats 1000000 in
theorem attesterMultiRevokeInnerInitReadInvAt_step
    {I : ExecutionEnv} {base len outerBase schemaLen : UInt256}
    {n : Nat} {b : AttesterMultiRevokeInnerArrayInitState}
    (hInv :
      attesterMultiRevokeInnerInitReadInvAt I base len outerBase schemaLen (n + 1) b) :
    attesterMultiRevokeInnerInitReadInvAt I base len outerBase schemaLen n
      (attesterMultiRevokeInnerArrayInitStepState b) := by
  have hbound := hInv.bound
  have hfreeBound := hInv.freeBound
  have hfreeSpare := hInv.freeSpare
  have hslotBound := hInv.slotBound
  have hfree63 :
      (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 63 <
        UInt256.size := by
    have hmul : 63 ≤ 64 * ((n + 1) + 1) := by nlinarith
    omega
  have hfree32 :
      (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 32 <
        UInt256.size := by
    omega
  have hsecondToNat :
      (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat =
        (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 32 :=
    attesterMultiRevokeInnerArrayInitSecondZeroWord_toNat
      (mem := b.mem) (aw := b.aw) hfree32
  have hsecondGe :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat := by
    rw [hsecondToNat]
    exact le_trans hInv.freeGe (Nat.le_add_right _ _)
  have houterFree :
      outerBase.toNat + 32 ≤ (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat := by
    exact le_trans hInv.outerBeforeBase
      (le_trans (Nat.le_add_right base.toNat 32) hInv.freeGe)
  have houterSecond :
      outerBase.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat := by
    rw [hsecondToNat]
    exact le_trans houterFree (Nat.le_add_right _ _)
  have houterSlot : outerBase.toNat + 32 ≤ b.slot.toNat := by
    exact le_trans hInv.outerBeforeBase
      (le_trans (Nat.le_add_right base.toNat 32) hInv.slotGe)
  have hsecond63 :
      (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat + 63 <
        UInt256.size := by
    rw [hsecondToNat]
    have hmul : 95 ≤ 64 * ((n + 1) + 1) := by nlinarith
    omega
  have hslot63 : b.slot.toNat + 63 < UInt256.size := by
    have hmul : 63 ≤ 32 * ((n + 1) + 1) := by nlinarith
    omega
  have hawStep :=
    attesterMultiRevokeInnerArrayInitStepAw_bounds
      (slot := b.slot) (mem := b.mem) (aw := b.aw)
      hInv.awGe hInv.awMul hfree63 hsecond63 hslot63
  have hreadStep :
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).readWithPadding
          base.toNat 32 =
        UInt256.toByteArray len :=
    attesterMultiRevokeInnerArrayInitStep_readWithPadding_nat
      (base := base) (slot := b.slot) (len := len) (mem := b.mem) (aw := b.aw)
      hInv.memSize hInv.read hInv.baseGe hInv.freeGe hsecondGe hInv.slotGe
  have hmemStep :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).size :=
    attesterMultiRevokeInnerArrayInitStep_base_size
      (base := base) (slot := b.slot) (len := len) (mem := b.mem) (aw := b.aw)
      hInv.memSize
  have hreadOuterStep :
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).readWithPadding
          outerBase.toNat 32 =
        UInt256.toByteArray schemaLen :=
    attesterMultiRevokeInnerArrayInitStep_readWithPadding_nat
      (base := outerBase) (slot := b.slot) (len := schemaLen)
      (mem := b.mem) (aw := b.aw)
      hInv.outerMemSize hInv.outerRead hInv.outer64 houterFree houterSecond houterSlot
  have houterMemStep :
      outerBase.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).size :=
    le_trans hInv.outerMemSize attesterMultiRevokeInnerArrayInitStep_size_ge
  have hfree96 :
      64 + 32 ≤ (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat := by
    have hbase96 : 64 + 32 ≤ base.toNat + 32 :=
      le_trans hInv.baseGe (Nat.le_add_right base.toNat 32)
    exact le_trans hbase96 hInv.freeGe
  have hsecond96 :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat := by
    have hbase96 : 64 + 32 ≤ base.toNat + 32 :=
      le_trans hInv.baseGe (Nat.le_add_right base.toNat 32)
    exact le_trans hbase96 hsecondGe
  have hslot96 : 64 + 32 ≤ b.slot.toNat := by
    have hbase96 : 64 + 32 ≤ base.toNat + 32 :=
      le_trans hInv.baseGe (Nat.le_add_right base.toNat 32)
    exact le_trans hbase96 hInv.slotGe
  have hfree64 :
      (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 64 <
        UInt256.size := by
    omega
  have hfreeStepToNat :
      (attesterMultiOuterArrayInitFreeWord
          (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw)
          (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw)).toNat =
        (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 64 :=
    attesterMultiRevokeInnerArrayInitStep_freeWord_toNat
      (slot := b.slot) (mem := b.mem) (aw := b.aw)
      hfree96 hsecond96 hslot96 hawStep.2 hawStep.1 hfree64
  have hslot32 : b.slot.toNat + 32 < UInt256.size := by
    omega
  have hslotStepToNat :
      (((⟨32⟩ : UInt256) + b.slot).toNat) = b.slot.toNat + 32 :=
    uadd_lit32_toNat b.slot hslot32
  exact
    { remaining := by
        change UInt256.sub b.remaining (⟨1⟩ : UInt256) = UInt256.ofNat (n + 1)
        rw [hInv.remaining]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          attester_u256_ofNat_succ_sub_one (n := n + 1) hInv.bound
      bound := by omega
      awGe := by
        change 3 ≤ (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw).toNat
        exact hawStep.1
      awMul := by
        change
          (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw).toNat * 32 <
            UInt256.size
        exact hawStep.2
      read := by
        change
          (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).readWithPadding
              base.toNat 32 =
            UInt256.toByteArray len
        exact hreadStep
      memSize := by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).size
        exact hmemStep
      le := by
        have hle := hInv.le
        omega
      baseGe := hInv.baseGe
      freeGe := by
        change base.toNat + 32 ≤
          (attesterMultiOuterArrayInitFreeWord
            (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw)
            (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw)).toNat
        rw [hfreeStepToNat]
        omega
      freeExact := by
        change
          (attesterMultiOuterArrayInitFreeWord
            (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw)
            (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw)).toNat =
              base.toNat + 32 + 32 * len.toNat + 64 * (len.toNat - (n + 1))
        rw [hfreeStepToNat, hInv.freeExact]
        have hsub :
            len.toNat - (n + 1) =
              len.toNat - ((n + 1) + 1) + 1 := by
          have hle := hInv.le
          omega
        rw [hsub]
        nlinarith
      freeBound := by
        change
          (attesterMultiOuterArrayInitFreeWord
            (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw)
            (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw)).toNat +
              64 * (n + 1) <
            UInt256.size
        rw [hfreeStepToNat]
        omega
      freeSpare := by
        change
          (attesterMultiOuterArrayInitFreeWord
            (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw)
            (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw)).toNat +
              64 * (n + 1) + 64 * len.toNat + 96 <
            UInt256.size
        rw [hfreeStepToNat]
        have hspare :
            (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat +
                64 * ((n + 1) + 1) + 64 * len.toNat + 96 <
              UInt256.size := by
          simpa using hInv.freeSpare
        omega
      slotGe := by
        change base.toNat + 32 ≤ (((⟨32⟩ : UInt256) + b.slot).toNat)
        rw [hslotStepToNat]
        exact le_trans hInv.slotGe (Nat.le_add_right _ _)
      slotBound := by
        change (((⟨32⟩ : UInt256) + b.slot).toNat) + 32 * (n + 1) + 63 <
          UInt256.size
        rw [hslotStepToNat]
        omega
      baseSlot63 := hInv.baseSlot63
      outerRead := by
        change
          (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).readWithPadding
              outerBase.toNat 32 =
            UInt256.toByteArray schemaLen
        exact hreadOuterStep
      outerMemSize := by
        change outerBase.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).size
        exact houterMemStep
      outer64 := hInv.outer64
      outerBeforeBase := hInv.outerBeforeBase }

theorem AttesterReadPreservedBefore_innerInitStep
    {I : ExecutionEnv} {mem₀ : ByteArray}
    {base len outerBase schemaLen : UInt256}
    {n : Nat} {b : AttesterMultiRevokeInnerArrayInitState}
    (hInv :
      attesterMultiRevokeInnerInitReadInvAt I base len outerBase schemaLen (n + 1) b)
    (hpres : AttesterReadPreservedBefore mem₀ b.mem base.toNat) :
    AttesterReadPreservedBefore mem₀
      (attesterMultiRevokeInnerArrayInitStepState b).mem base.toNat := by
  intro read word hmem0 hread0 hread64 hbefore
  rcases hpres hmem0 hread0 hread64 hbefore with ⟨hmem, hread⟩
  have hreadLt : read < UInt256.size := by
    have hbaseLt : base.toNat < UInt256.size := base.val.isLt
    omega
  let readWord : UInt256 := UInt256.ofNat read
  have hreadWordToNat : readWord.toNat = read := ulit_toNat' read hreadLt
  have hfree32 :
      (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 32 <
        UInt256.size := by
    have hfb := hInv.freeBound
    omega
  have hsecondToNat :
      (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat =
        (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 32 :=
    attesterMultiRevokeInnerArrayInitSecondZeroWord_toNat
      (mem := b.mem) (aw := b.aw) hfree32
  have hfree :
      read + 32 ≤ (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat := by
    exact le_trans hbefore (le_trans (Nat.le_add_right base.toNat 32) hInv.freeGe)
  have hsecond :
      read + 32 ≤
        (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat := by
    rw [hsecondToNat]
    exact le_trans hfree (Nat.le_add_right _ _)
  have hslot : read + 32 ≤ b.slot.toNat := by
    exact le_trans hbefore
      (le_trans (Nat.le_add_right base.toNat 32) hInv.slotGe)
  constructor
  · change read + 32 ≤
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).size
    exact le_trans hmem attesterMultiRevokeInnerArrayInitStep_size_ge
  · change
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).readWithPadding
          read 32 =
        UInt256.toByteArray word
    have hstep :=
      attesterMultiRevokeInnerArrayInitStep_readWithPadding_nat
        (base := readWord) (slot := b.slot) (len := word)
        (mem := b.mem) (aw := b.aw)
        (by simpa [readWord, hreadWordToNat] using hmem)
        (by simpa [readWord, hreadWordToNat] using hread)
        (by simpa [readWord, hreadWordToNat] using hread64)
        (by simpa [readWord, hreadWordToNat] using hfree)
        (by simpa [readWord, hreadWordToNat] using hsecond)
        (by simpa [readWord, hreadWordToNat] using hslot)
    simpa [readWord, hreadWordToNat] using hstep

theorem AttesterReadPreservedBefore_innerInitFinal
    {I : ExecutionEnv} {mem₀ : ByteArray}
    {base len outerBase schemaLen : UInt256}
    {b : AttesterMultiRevokeInnerArrayInitState}
    (hInv : attesterMultiRevokeInnerInitReadInvAt I base len outerBase schemaLen 0 b)
    (hpres : AttesterReadPreservedBefore mem₀ b.mem base.toNat) :
    AttesterReadPreservedBefore mem₀
      (attesterMultiRevokeInnerArrayInitFinalMem b) base.toNat := by
  intro read word hmem0 hread0 hread64 hbefore
  rcases hpres hmem0 hread0 hread64 hbefore with ⟨hmem, hread⟩
  have hreadLt : read < UInt256.size := by
    have hbaseLt : base.toNat < UInt256.size := base.val.isLt
    omega
  let readWord : UInt256 := UInt256.ofNat read
  have hreadWordToNat : readWord.toNat = read := ulit_toNat' read hreadLt
  have hfree32 :
      (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 32 <
        UInt256.size := by
    have hfb := hInv.freeBound
    omega
  have hsecondToNat :
      (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat =
        (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 32 :=
    attesterMultiRevokeInnerArrayInitSecondZeroWord_toNat
      (mem := b.mem) (aw := b.aw) hfree32
  have hfree :
      read + 32 ≤ (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat := by
    exact le_trans hbefore (le_trans (Nat.le_add_right base.toNat 32) hInv.freeGe)
  have hsecond :
      read + 32 ≤
        (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat := by
    rw [hsecondToNat]
    exact le_trans hfree (Nat.le_add_right _ _)
  have hslot : read + 32 ≤ b.slot.toNat := by
    exact le_trans hbefore
      (le_trans (Nat.le_add_right base.toNat 32) hInv.slotGe)
  constructor
  · change read + 32 ≤
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).size
    exact le_trans hmem attesterMultiRevokeInnerArrayInitStep_size_ge
  · change
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).readWithPadding
          read 32 =
        UInt256.toByteArray word
    have hstep :=
      attesterMultiRevokeInnerArrayInitStep_readWithPadding_nat
        (base := readWord) (slot := b.slot) (len := word)
        (mem := b.mem) (aw := b.aw)
        (by simpa [readWord, hreadWordToNat] using hmem)
        (by simpa [readWord, hreadWordToNat] using hread)
        (by simpa [readWord, hreadWordToNat] using hread64)
        (by simpa [readWord, hreadWordToNat] using hfree)
        (by simpa [readWord, hreadWordToNat] using hsecond)
        (by simpa [readWord, hreadWordToNat] using hslot)
    simpa [readWord, hreadWordToNat] using hstep

set_option maxHeartbeats 1000000 in
theorem attesterMultiRevokeInnerInitReadInvAt_init
    {I : ExecutionEnv} {base len outerBase schemaLen : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hlenNe : len.toNat ≠ 0)
    (hawGe : 3 ≤ aw.toNat)
    (hawMul : aw.toNat * 32 < UInt256.size)
    (hbaseGe : 64 + 32 ≤ base.toNat)
    (hbaseSpare : base.toNat + 32 + 160 * len.toNat + 96 < UInt256.size)
    (houterRead : mem.readWithPadding outerBase.toNat 32 = UInt256.toByteArray schemaLen)
    (houterMemSize : outerBase.toNat + 32 ≤ mem.size)
    (houter64 : 64 + 32 ≤ outerBase.toNat)
    (houterBeforeBase : outerBase.toNat + 32 ≤ base.toNat)
    (hbaseEq : base = attesterInnerArrayAllocFreeWord mem aw) :
    attesterMultiRevokeInnerInitReadInvAt I base len outerBase schemaLen
      (len.toNat - 1)
      { slot := ((⟨32⟩ : UInt256) + base),
        remaining := len,
        mem := attesterInnerArrayAllocMem len mem aw,
        aw := attesterInnerArrayAllocAw len mem aw } := by
  have hlenSucc : len.toNat - 1 + 1 = len.toNat := by omega
  have hbase63 : base.toNat + 63 < UInt256.size := by
    have hpos : 1 ≤ len.toNat := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hlenNe)
    nlinarith
  have hallocAw :=
    attesterInnerArrayAllocAw_bounds
      (len := len) (mem := mem) (aw := aw)
      hawGe hawMul (by simpa [← hbaseEq] using hbase63)
  have hallocBound :
      base.toNat + 32 + 32 * len.toNat < UInt256.size := by
    have hpos : 0 ≤ len.toNat := Nat.zero_le _
    nlinarith
  have hallocFreeToNat :
      (attesterInnerArrayAllocFreeWord
          (attesterInnerArrayAllocMem len mem aw)
          (attesterInnerArrayAllocAw len mem aw)).toNat =
        base.toNat + 32 + 32 * len.toNat := by
    rw [hbaseEq]
    exact attesterInnerArrayAllocMem_freeWord_toNat
      (len := len) (mem := mem) (aw := aw)
      hallocAw.2 hallocAw.1 (by simpa [hbaseEq] using hallocBound)
  have hslotToNat :
      (((⟨32⟩ : UInt256) + base).toNat) = base.toNat + 32 :=
    uadd_lit32_toNat base (by omega)
  have hallocOuterRead :
      (attesterInnerArrayAllocMem len mem aw).readWithPadding outerBase.toNat 32 =
        UInt256.toByteArray schemaLen := by
    simpa [hbaseEq] using
      (attesterInnerArrayAllocMem_readWithPadding_at_nat
        (readBase := outerBase) (len := len)
        (readLen := schemaLen) (mem := mem) (aw := aw)
        houterMemSize houterRead houter64
        (by simpa [hbaseEq] using houterBeforeBase))
  have hallocOuterMem :
      outerBase.toNat + 32 ≤ (attesterInnerArrayAllocMem len mem aw).size :=
    le_trans houterMemSize attesterInnerArrayAllocMem_size_ge
  exact
    { remaining := by
        simpa [hlenSucc] using (u256_ofNat_toNat len).symm
      bound := by
        rw [hlenSucc]
        exact len.val.isLt
      awGe := by
        change 3 ≤ (attesterInnerArrayAllocAw len mem aw).toNat
        exact hallocAw.1
      awMul := by
        change (attesterInnerArrayAllocAw len mem aw).toNat * 32 < UInt256.size
        exact hallocAw.2
      read := by
        simpa [← hbaseEq] using
          (attesterInnerArrayAllocMem_readWithPadding_len_nat
            (len := len) (mem := mem) (aw := aw)
            (by simpa [← hbaseEq] using hbaseGe))
      memSize := by
        simpa [← hbaseEq] using
          (attesterInnerArrayAllocMem_base_size
            (len := len) (mem := mem) (aw := aw))
      le := by
        rw [hlenSucc]
      baseGe := hbaseGe
      freeGe := by
        change base.toNat + 32 ≤
          (attesterInnerArrayAllocFreeWord
            (attesterInnerArrayAllocMem len mem aw)
            (attesterInnerArrayAllocAw len mem aw)).toNat
        rw [hallocFreeToNat]
        omega
      freeExact := by
        change
          (attesterInnerArrayAllocFreeWord
            (attesterInnerArrayAllocMem len mem aw)
            (attesterInnerArrayAllocAw len mem aw)).toNat =
              base.toNat + 32 + 32 * len.toNat +
                64 * (len.toNat - (len.toNat - 1 + 1))
        rw [hallocFreeToNat]
        have hzero : len.toNat - (len.toNat - 1 + 1) = 0 := by
          omega
        rw [hzero]
        omega
      freeBound := by
        change
          (attesterInnerArrayAllocFreeWord
            (attesterInnerArrayAllocMem len mem aw)
            (attesterInnerArrayAllocAw len mem aw)).toNat +
              64 * (len.toNat - 1 + 1) < UInt256.size
        rw [hallocFreeToNat, hlenSucc]
        nlinarith
      freeSpare := by
        change
          (attesterInnerArrayAllocFreeWord
            (attesterInnerArrayAllocMem len mem aw)
            (attesterInnerArrayAllocAw len mem aw)).toNat +
              64 * (len.toNat - 1 + 1) + 64 * len.toNat + 96 <
            UInt256.size
        rw [hallocFreeToNat, hlenSucc]
        nlinarith
      slotGe := by
        change base.toNat + 32 ≤ (((⟨32⟩ : UInt256) + base).toNat)
        rw [hslotToNat]
      slotBound := by
        change (((⟨32⟩ : UInt256) + base).toNat) +
          32 * (len.toNat - 1 + 1) + 63 < UInt256.size
        rw [hslotToNat, hlenSucc]
        have hpos : 0 ≤ len.toNat := Nat.zero_le _
        nlinarith
      baseSlot63 := by
        have hpos : 0 ≤ len.toNat := Nat.zero_le _
        nlinarith
      outerRead := hallocOuterRead
      outerMemSize := hallocOuterMem
      outer64 := houter64
      outerBeforeBase := houterBeforeBase }

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeInnerArrayInitFinalIterationAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len payload : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨475⟩ : UInt256)
      (slot :: (⟨1⟩ : UInt256) :: base :: ⟨0⟩ :: len :: len :: payload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
      ((⟨0⟩ : UInt256) :: base :: len :: len :: payload :: tail)
      (attesterMultiRevokeInnerArrayInitStepMem slot mem aw)
      (attesterMultiRevokeInnerArrayInitStepAw slot mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  let free := attesterMultiOuterArrayInitFreeWord mem aw
  let aw1 := attesterMultiOuterArrayInitAwAfterMload aw
  let mem1 := attesterMultiOuterArrayInitFreeMem mem aw
  let aw2 := attesterMultiOuterArrayInitFreeAw aw
  let mem2 := attesterMultiOuterArrayInitZeroMem mem aw
  let aw3 := attesterMultiOuterArrayInitZeroAw mem aw
  let second := attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw
  let mem3 := attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw
  let aw4 := attesterMultiRevokeInnerArrayInitSecondZeroAw mem aw
  let mem4 := attesterMultiRevokeInnerArrayInitStepMem slot mem aw
  let aw5 := attesterMultiRevokeInnerArrayInitStepAw slot mem aw
  have hcostMload :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: ⟨64⟩ :: slot :: (⟨1⟩ : UInt256) :: base ::
            ⟨0⟩ :: len :: len :: payload :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStore64 :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: ((⟨64⟩ : UInt256) + free) :: free :: slot ::
            (⟨1⟩ : UInt256) :: base :: ⟨0⟩ :: len :: len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreZero :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          free :: (⟨0⟩ : UInt256) :: ⟨0⟩ :: free :: slot ::
            (⟨1⟩ : UInt256) :: base :: ⟨0⟩ :: len :: len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreSecondZero :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack =
          second :: (⟨0⟩ : UInt256) :: free :: slot :: (⟨1⟩ : UInt256) ::
            base :: ⟨0⟩ :: len :: len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw4 - Cₘ aw3 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreSlot :
      ∀ s : State,
        s.machineState.activeWords = aw4 →
        s.machineState.stack =
          slot :: free :: slot :: (⟨1⟩ : UInt256) :: base :: ⟨0⟩ ::
            len :: len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw5 - Cₘ aw4 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hrd497 : ∃ k497 C497, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨497⟩ : UInt256)
      (slot :: (⟨1⟩ : UInt256) :: base :: ⟨0⟩ :: len :: len :: payload :: tail)
      mem4 aw5 ByteArray.empty (cA, σ) k497 C497 := by
    exact ⟨_, _, by
      simpa [free, aw1, mem1, aw2, mem2, aw3, second, mem3, aw4, mem4, aw5] using
        evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨475⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨476⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨478⟩, 0x80, .DUP1) (by evm_ov),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨479⟩, 0x51, .MLOAD)
      hcostMload (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨480⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨481⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨482⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨483⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨484⟩, 0x91, .SWAP2) (by evm_ov),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨485⟩, 0x52, .MSTORE)
      hcostStore64 (by rfl) (by rfl) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨486⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨487⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨488⟩, 0x82, .DUP3) (by evm_ov),
    raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3
      (by attester_decode_at v, ⟨489⟩, 0x52, .MSTORE)
      hcostStoreZero (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨490⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨492⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨493⟩, 0x01, .ADD) (by evm_ov),
    raw mstore (Cₘ aw4 - Cₘ aw3) mem3 aw4
      (by attester_decode_at v, ⟨494⟩, 0x52, .MSTORE)
      hcostStoreSecondZero (by rfl) (by rfl) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨495⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw5 - Cₘ aw4) mem4 aw5
      (by attester_decode_at v, ⟨496⟩, 0x52, .MSTORE)
      hcostStoreSlot (by rfl) (by rfl) (by evm_ov)]⟩
  obtain ⟨_, _, rd497⟩ := hrd497
  have hrd511 : ∃ k511 C511, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨511⟩ : UInt256)
      (((⟨32⟩ : UInt256) + slot) :: ⟨0⟩ :: base :: ⟨0⟩ ::
        len :: len :: payload :: tail)
      mem4 aw5 ByteArray.empty (cA, σ) k511 C511 := by
    exact ⟨_, _, by
      simpa using
        evm_run rd497 with [
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨497⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨499⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨500⟩, 0x90, .SWAP1) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨501⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨503⟩, 0x90, .SWAP1) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨504⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨505⟩, 0x90, .SWAP1) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨506⟩, 0x81, .DUP2) (by evm_ov),
    raw push2 ⟨475⟩ (by attester_decode_at v, ⟨507⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨510⟩, 0x57, .JUMPI)
      (by native_decide) (by evm_ov)]⟩
  obtain ⟨_, _, rd511⟩ := hrd511
  have rd518 := evm_run rd511 with [
    raw swap1 (by attester_decode_at v, ⟨511⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨512⟩, 0x50, .POP) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨513⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨514⟩, 0x50, .POP) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨515⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨516⟩, 0x50, .POP) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨517⟩, 0x5f, .PUSH0) (by evm_ov)]
  exact ⟨_, _, by
    simpa [free, aw1, mem1, aw2, mem2, aw3, second, mem3, aw4, mem4, aw5] using rd518⟩

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeInnerArrayInitNonFinalIterationAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len payload remaining : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hnext : UInt256.sub remaining (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨475⟩ : UInt256)
      (slot :: remaining :: base :: ⟨0⟩ :: len :: len :: payload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨475⟩ : UInt256)
      (((⟨32⟩ : UInt256) + slot) :: UInt256.sub remaining ⟨1⟩ ::
        base :: ⟨0⟩ :: len :: len :: payload :: tail)
      (attesterMultiRevokeInnerArrayInitStepMem slot mem aw)
      (attesterMultiRevokeInnerArrayInitStepAw slot mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  let free := attesterMultiOuterArrayInitFreeWord mem aw
  let aw1 := attesterMultiOuterArrayInitAwAfterMload aw
  let mem1 := attesterMultiOuterArrayInitFreeMem mem aw
  let aw2 := attesterMultiOuterArrayInitFreeAw aw
  let mem2 := attesterMultiOuterArrayInitZeroMem mem aw
  let aw3 := attesterMultiOuterArrayInitZeroAw mem aw
  let second := attesterMultiRevokeInnerArrayInitSecondZeroWord mem aw
  let mem3 := attesterMultiRevokeInnerArrayInitSecondZeroMem mem aw
  let aw4 := attesterMultiRevokeInnerArrayInitSecondZeroAw mem aw
  let mem4 := attesterMultiRevokeInnerArrayInitStepMem slot mem aw
  let aw5 := attesterMultiRevokeInnerArrayInitStepAw slot mem aw
  have hcostMload :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: ⟨64⟩ :: slot :: remaining :: base ::
            ⟨0⟩ :: len :: len :: payload :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStore64 :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: ((⟨64⟩ : UInt256) + free) :: free :: slot ::
            remaining :: base :: ⟨0⟩ :: len :: len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreZero :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          free :: (⟨0⟩ : UInt256) :: ⟨0⟩ :: free :: slot ::
            remaining :: base :: ⟨0⟩ :: len :: len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreSecondZero :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack =
          second :: (⟨0⟩ : UInt256) :: free :: slot :: remaining ::
            base :: ⟨0⟩ :: len :: len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw4 - Cₘ aw3 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreSlot :
      ∀ s : State,
        s.machineState.activeWords = aw4 →
        s.machineState.stack =
          slot :: free :: slot :: remaining :: base :: ⟨0⟩ ::
            len :: len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw5 - Cₘ aw4 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hrd497 : ∃ k497 C497, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨497⟩ : UInt256)
      (slot :: remaining :: base :: ⟨0⟩ :: len :: len :: payload :: tail)
      mem4 aw5 ByteArray.empty (cA, σ) k497 C497 := by
    exact ⟨_, _, by
      simpa [free, aw1, mem1, aw2, mem2, aw3, second, mem3, aw4, mem4, aw5] using
        evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨475⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨476⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨478⟩, 0x80, .DUP1) (by evm_ov),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨479⟩, 0x51, .MLOAD)
      hcostMload (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨480⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨481⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨482⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨483⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨484⟩, 0x91, .SWAP2) (by evm_ov),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨485⟩, 0x52, .MSTORE)
      hcostStore64 (by rfl) (by rfl) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨486⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨487⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨488⟩, 0x82, .DUP3) (by evm_ov),
    raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3
      (by attester_decode_at v, ⟨489⟩, 0x52, .MSTORE)
      hcostStoreZero (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨490⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨492⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨493⟩, 0x01, .ADD) (by evm_ov),
    raw mstore (Cₘ aw4 - Cₘ aw3) mem3 aw4
      (by attester_decode_at v, ⟨494⟩, 0x52, .MSTORE)
      hcostStoreSecondZero (by rfl) (by rfl) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨495⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw5 - Cₘ aw4) mem4 aw5
      (by attester_decode_at v, ⟨496⟩, 0x52, .MSTORE)
      hcostStoreSlot (by rfl) (by rfl) (by evm_ov)]⟩
  obtain ⟨_, _, rd497⟩ := hrd497
  exact ⟨_, _, by
    simpa [free, aw1, mem1, aw2, mem2, aw3, second, mem3, aw4, mem4, aw5] using
      evm_run rd497 with [
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨497⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨499⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨500⟩, 0x90, .SWAP1) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨501⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨503⟩, 0x90, .SWAP1) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨504⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨505⟩, 0x90, .SWAP1) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨506⟩, 0x81, .DUP2) (by evm_ov),
    raw push2 ⟨475⟩ (by attester_decode_at v, ⟨507⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨510⟩, 0x57, .JUMPI)
      (by simpa using hnext)
      (attesterMultiRevokeInnerArrayInitLoopJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeInnerArrayInitLoopWithStateInvariantAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {slot base len payload : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (Inv : Nat → AttesterMultiRevokeInnerArrayInitState → Prop)
    (hremaining :
      ∀ n a, Inv n a → a.remaining = UInt256.ofNat (n + 1))
    (hbound :
      ∀ n a, Inv n a → n + 1 < UInt256.size)
    (hstep :
      ∀ n a, Inv (n + 1) a → Inv n (attesterMultiRevokeInnerArrayInitStepState a))
    (hinit :
      Inv (len.toNat - 1)
        { slot := slot, remaining := len, mem := mem, aw := aw })
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨475⟩ : UInt256)
      (slot :: len :: base :: ⟨0⟩ :: len :: len :: payload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ a' k' C',
      a'.remaining = (⟨1⟩ : UInt256) ∧
      Inv 0 a' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
        (attesterMultiRevokeInnerArrayInitExitStackAt base len payload tail a')
        (attesterMultiRevokeInnerArrayInitFinalMem a')
        (attesterMultiRevokeInnerArrayInitFinalAw a')
        ByteArray.empty (cA, σ) k' C' := by
  let stk := attesterMultiRevokeInnerArrayInitStackAt base len payload tail
  let memOf : AttesterMultiRevokeInnerArrayInitState → ByteArray := fun a => a.mem
  let awOf : AttesterMultiRevokeInnerArrayInitState → UInt256 := fun a => a.aw
  let exitStk := attesterMultiRevokeInnerArrayInitExitStackAt base len payload tail
  let exitMem := attesterMultiRevokeInnerArrayInitFinalMem
  let exitAw := attesterMultiRevokeInnerArrayInitFinalAw
  have hexit :
      ∀ a, Inv 0 a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨475⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ k' C',
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨518⟩ : UInt256) (exitStk a) (exitMem a) (exitAw a)
            ByteArray.empty (cA, σ) k' C' := by
    intro a hInv k C rd
    have hrem : a.remaining = (⟨1⟩ : UInt256) := by
      simpa using hremaining 0 a hInv
    exact attesterX_multiRevokeInnerArrayInitFinalIterationAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
      (payload := payload) (tail := tail) (mem := a.mem) (aw := a.aw)
      (k := k) (C := C) htail
      (by
        simpa [stk, memOf, awOf, exitStk, exitMem, exitAw, hrem,
          attesterMultiRevokeInnerArrayInitStackAt] using rd)
  have hbody :
      ∀ n a, Inv (n + 1) a → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨475⟩ : UInt256) (stk a) (memOf a) (awOf a)
          ByteArray.empty (cA, σ) k C →
        ∃ a' k' C',
          Inv n a' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨475⟩ : UInt256) (stk a') (memOf a') (awOf a')
            ByteArray.empty (cA, σ) k' C' := by
    intro n a hInv k C rd
    let a' := attesterMultiRevokeInnerArrayInitStepState a
    have hsub :
        UInt256.sub a.remaining (⟨1⟩ : UInt256) = UInt256.ofNat (n + 1) := by
      rw [hremaining (n + 1) a hInv]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        attester_u256_ofNat_succ_sub_one (n := n + 1)
          (hbound (n + 1) a hInv)
    have hnext : UInt256.sub a.remaining (⟨1⟩ : UInt256) ≠ ⟨0⟩ := by
      rw [hsub]
      exact attester_u256_ofNat_pos_ne_zero
        (n := n + 1) (by omega) (by
          have := hbound (n + 1) a hInv
          omega)
    obtain ⟨k', C', rd'⟩ :=
      attesterX_multiRevokeInnerArrayInitNonFinalIterationAt
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) v (slot := a.slot) (base := base) (len := len)
        (payload := payload) (remaining := a.remaining) (tail := tail)
        (mem := a.mem) (aw := a.aw) (k := k) (C := C) htail hnext
        (by
          simpa [stk, memOf, awOf, attesterMultiRevokeInnerArrayInitStackAt]
            using rd)
    refine ⟨a', k', C', hstep n a hInv, ?_⟩
    simpa [a', stk, memOf, awOf, attesterMultiRevokeInnerArrayInitStackAt,
      attesterMultiRevokeInnerArrayInitStepState] using rd'
  let a0 : AttesterMultiRevokeInnerArrayInitState :=
    { slot := slot, remaining := len, mem := mem, aw := aw }
  obtain ⟨a', k', C', hInvFinal, rdFinal⟩ :=
    RD.whileLoopCarryExit
      (code := patchedRuntime v) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := ByteArray.empty) (acc := (cA, σ))
      (header := (⟨475⟩ : UInt256)) (exit := (⟨518⟩ : UInt256))
      Inv stk memOf awOf exitStk exitMem exitAw hexit hbody
      (len.toNat - 1) a0 (by simpa [a0] using hinit) k C
      (by
        simpa [a0, stk, memOf, awOf, attesterMultiRevokeInnerArrayInitStackAt]
          using hreach)
  exact ⟨a', k', C', by simpa using hremaining 0 a' hInvFinal,
    hInvFinal, rdFinal⟩

theorem attesterX_multiRevokeInnerArrayReturnCleanupAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {len payload sz idx outerBase schemaLen secondLen secondPayload schemaPayload
      ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨381⟩ : UInt256)
      [len, payload, ⟨0⟩, sz, idx, outerBase, schemaLen, secondLen,
        secondPayload, schemaLen, schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨387⟩ : UInt256)
      [len, payload, idx, outerBase, schemaLen, secondLen, secondPayload,
        schemaLen, schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨381⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨382⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨383⟩, 0x92, .SWAP3) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨384⟩, 0x50, .POP) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨385⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨386⟩, 0x50, .POP) (by evm_ov)]⟩

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeInnerArrayLengthZeroRevertsAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {len payload sz idx outerBase schemaLen secondLen secondPayload schemaPayload
      ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hlenZero : len = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨381⟩ : UInt256)
      [len, payload, ⟨0⟩, sz, idx, outerBase, schemaLen, secondLen,
        secondPayload, schemaLen, schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, rd3870⟩ :=
    attesterX_multiRevokeInnerArrayReturnCleanupAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (len := len) (payload := payload) (sz := sz) (idx := idx)
      (outerBase := outerBase) (schemaLen := schemaLen) (secondLen := secondLen)
      (secondPayload := secondPayload) (schemaPayload := schemaPayload)
      (ret := ret) (selector := selector) (mem := mem) (aw := aw)
      (k := k) (C := C) hreach
  let tail := [schemaLen, secondLen, secondPayload, schemaLen, schemaPayload, ret, selector]
  have rd387 : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨387⟩ : UInt256)
      (len :: payload :: idx :: outerBase :: tail)
      mem aw ByteArray.empty (cA, σ) k0 C0 := by
    simpa [tail] using rd3870
  let free :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then
      (⟨0⟩ : UInt256)
    else
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let revertSelector := UInt256.shiftLeft (⟨3036299187⟩ : UInt256) ⟨224⟩
  let mem1 := revertSelector.toByteArray.write 0 mem free.toNat 32
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat free.toNat 32)
  let freeAfter :=
    if (⟨64⟩ : UInt256).toNat ≥ mem1.size ∨ (⟨64⟩ : UInt256) ≥ aw2 * ⟨32⟩ then
      (⟨0⟩ : UInt256)
    else
      UInt256.ofNat (fromByteArrayBigEndian (mem1.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
  let revLen := UInt256.sub ((⟨4⟩ : UInt256) + free) freeAfter
  let revAw := UInt256.ofNat (MachineState.M aw3.toNat freeAfter.toNat revLen.toNat)
  have hcostMload64 :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: len :: len :: payload :: idx :: outerBase :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostMstoreSelector :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          free :: revertSelector :: free :: len :: len :: payload :: idx :: outerBase :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostMload64After :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: ((⟨4⟩ : UInt256) + free) :: len :: len ::
            payload :: idx :: outerBase :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostRevert :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack =
          freeAfter :: revLen :: len :: len :: payload :: idx :: outerBase :: tail →
        memoryExpansionCost s .REVERT = Cₘ revAw - Cₘ aw3 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    rfl
  exact evm_run rd387 with [
    raw dup1 (by attester_decode_at v, ⟨387⟩, 0x80, .DUP1) (by simp [tail]),
    raw push0 (by attester_decode_at v, ⟨388⟩, 0x5f, .PUSH0) (by simp [tail]),
    raw dup2 (by attester_decode_at v, ⟨389⟩, 0x81, .DUP2) (by simp [tail]),
    raw swap1 (by attester_decode_at v, ⟨390⟩, 0x90, .SWAP1) (by simp [tail]),
    raw sub (by attester_decode_at v, ⟨391⟩, 0x03, .SUB) (by simp [tail]),
    raw push2 ⟨420⟩ (by attester_decode_at v, ⟨392⟩, 0x61, (.Push .PUSH2))
      (by simp [tail]),
    raw jumpiNT (by attester_decode_at v, ⟨395⟩, 0x57, .JUMPI)
      (by
        rw [show len = (⟨0⟩ : UInt256) by simpa using hlenZero]
        native_decide)
      (by simp [tail]),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨396⟩, 0x60, (.Push .PUSH1))
      (by simp [tail]),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨398⟩, 0x51, .MLOAD)
      hcostMload64 (by rfl) (by rfl) (by simp [tail]),
    raw push4 ⟨3036299187⟩ (by attester_decode_at v, ⟨399⟩, 0x63, (.Push .PUSH4))
      (by simp [tail]),
    raw push1 ⟨224⟩ (by attester_decode_at v, ⟨404⟩, 0x60, (.Push .PUSH1))
      (by simp [tail]),
    raw shl (by attester_decode_at v, ⟨406⟩, 0x1b, .SHL) (by simp [tail]),
    raw dup2 (by attester_decode_at v, ⟨407⟩, 0x81, .DUP2) (by simp [tail]),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨408⟩, 0x52, .MSTORE)
      hcostMstoreSelector (by rfl) (by rfl) (by simp [tail]),
    raw push1 ⟨4⟩ (by attester_decode_at v, ⟨409⟩, 0x60, (.Push .PUSH1))
      (by simp [tail]),
    raw add (by attester_decode_at v, ⟨411⟩, 0x01, .ADD) (by simp [tail]),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨412⟩, 0x60, (.Push .PUSH1))
      (by simp [tail]),
    raw mload (Cₘ aw3 - Cₘ aw2) freeAfter aw3
      (by attester_decode_at v, ⟨414⟩, 0x51, .MLOAD)
      hcostMload64After (by rfl) (by rfl) (by simp [tail]),
    raw dup1 (by attester_decode_at v, ⟨415⟩, 0x80, .DUP1) (by simp [tail]),
    raw swap2 (by attester_decode_at v, ⟨416⟩, 0x91, .SWAP2) (by simp [tail]),
    raw sub (by attester_decode_at v, ⟨417⟩, 0x03, .SUB) (by simp [tail]),
    raw swap1 (by attester_decode_at v, ⟨418⟩, 0x90, .SWAP1) (by simp [tail]),
    raw rev (Cₘ revAw - Cₘ aw3)
      (by attester_decode_at v, ⟨419⟩, 0xfd, .REVERT)
      hcostRevert (by simp [tail])]

theorem attesterX_multiRevokeInnerArrayNonemptyGuardOkAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {len payload idx outerBase schemaLen secondLen secondPayload schemaPayload
      ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hlenNe : len ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨387⟩ : UInt256)
      [len, payload, idx, outerBase, schemaLen, secondLen, secondPayload,
        schemaLen, schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨420⟩ : UInt256)
      [len, len, payload, idx, outerBase, schemaLen, secondLen, secondPayload,
        schemaLen, schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  have rd388 := RD.dup1 hreach
    (by attester_decode_at v, ⟨387⟩, 0x80, .DUP1) (by evm_ov)
  have rd389 := RD.push0 rd388
    (by attester_decode_at v, ⟨388⟩, 0x5f, .PUSH0) (by evm_ov)
  have rd390 := RD.dup2 rd389
    (by attester_decode_at v, ⟨389⟩, 0x81, .DUP2) (by evm_ov)
  have rd391 := RD.swap1 rd390
    (by attester_decode_at v, ⟨390⟩, 0x90, .SWAP1) (by evm_ov)
  have rd392 := RD.sub rd391
    (by attester_decode_at v, ⟨391⟩, 0x03, .SUB) (by evm_ov)
  have rd395 := RD.push2 rd392 ⟨420⟩
    (by attester_decode_at v, ⟨392⟩, 0x61, (.Push .PUSH2)) (by evm_ov)
  have hcond : UInt256.sub (⟨0⟩ : UInt256) len ≠ ⟨0⟩ :=
    u256_zero_sub_ne_zero hlenNe
  have rd420 := RD.jumpiT rd395
    (by attester_decode_at v, ⟨395⟩, 0x57, .JUMPI)
    hcond (attesterMultiRevokeInnerNonemptyOkJumpdest v) (by evm_ov)
  exact ⟨_, _, by simpa using rd420⟩

theorem attesterX_multiRevokeInnerArrayNonemptyOkAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {len payload sz idx outerBase schemaLen secondLen secondPayload schemaPayload
      ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hlenNe : len ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨381⟩ : UInt256)
      [len, payload, ⟨0⟩, sz, idx, outerBase, schemaLen, secondLen,
        secondPayload, schemaLen, schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨420⟩ : UInt256)
      [len, len, payload, idx, outerBase, schemaLen, secondLen, secondPayload,
        schemaLen, schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd387⟩ :=
    attesterX_multiRevokeInnerArrayReturnCleanupAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (len := len) (payload := payload) (sz := sz) (idx := idx)
      (outerBase := outerBase) (schemaLen := schemaLen) (secondLen := secondLen)
      (secondPayload := secondPayload) (schemaPayload := schemaPayload)
      (ret := ret) (selector := selector) (mem := mem) (aw := aw)
      (k := k) (C := C) hreach
  exact attesterX_multiRevokeInnerArrayNonemptyGuardOkAt
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) v
    (len := len) (payload := payload) (idx := idx) (outerBase := outerBase)
    (schemaLen := schemaLen) (secondLen := secondLen)
    (secondPayload := secondPayload) (schemaPayload := schemaPayload)
    (ret := ret) (selector := selector) (mem := mem) (aw := aw)
    (k := k0) (C := C0) hlenNe rd387

theorem attesterX_multiRevokeInnerArrayLengthAllocMaxOkAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {len payload : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hgt :
      UInt256.gt len
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨420⟩ : UInt256)
      (len :: len :: payload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨445⟩ : UInt256)
      (len :: ⟨0⟩ :: len :: len :: payload :: tail)
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨420⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨421⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨422⟩, 0x81, .DUP2) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨423⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨425⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨427⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨429⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨430⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨431⟩, 0x81, .DUP2) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨432⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨433⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨445⟩ (by attester_decode_at v, ⟨434⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨437⟩, 0x57, .JUMPI)
      (by
        rw [hgt]
        decide)
      (attesterMultiRevokeInnerLengthMaxOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeInnerArrayNonemptyAndLengthOkAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {len payload sz idx outerBase schemaLen secondLen secondPayload schemaPayload
      ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hlenNe : len ≠ ⟨0⟩)
    (hgt :
      UInt256.gt len
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨381⟩ : UInt256)
      [len, payload, ⟨0⟩, sz, idx, outerBase, schemaLen, secondLen,
        secondPayload, schemaLen, schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨445⟩ : UInt256)
      [len, ⟨0⟩, len, len, payload, idx, outerBase, schemaLen, secondLen,
        secondPayload, schemaLen, schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd420⟩ :=
    attesterX_multiRevokeInnerArrayNonemptyOkAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (len := len) (payload := payload) (sz := sz) (idx := idx)
      (outerBase := outerBase) (schemaLen := schemaLen) (secondLen := secondLen)
      (secondPayload := secondPayload) (schemaPayload := schemaPayload)
      (ret := ret) (selector := selector) (mem := mem) (aw := aw)
      (k := k) (C := C) hlenNe hreach
  exact attesterX_multiRevokeInnerArrayLengthAllocMaxOkAt
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) v
    (len := len) (payload := payload)
    (tail := [idx, outerBase, schemaLen, secondLen, secondPayload,
      schemaLen, schemaPayload, ret, selector])
    (mem := mem) (aw := aw) (k := k0) (C := C0) (by simp) hgt
    (by simpa using rd420)

theorem attesterX_multiRevokeInnerDecoderToAllocAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx outerBase schemaLen secondLen secondPayload schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hoffsetOk :
      UInt256.slt
        (attesterMultiRevokeInnerArrayOffsetWord I
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size) secondPayload)
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩)
    (hlenOk :
      UInt256.gt
        (attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩)
    (hpayloadOk :
      UInt256.sgt
        (attesterMultiRevokeInnerArrayPayloadWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft
            (attesterMultiRevokeInnerArrayLengthWord I secondPayload
              (attesterMultiRevokeInnerArrayHeadWord secondPayload idx)) ⟨5⟩)) = ⟨0⟩)
    (hlenNe :
      attesterMultiRevokeInnerArrayLengthWord I secondPayload
        (attesterMultiRevokeInnerArrayHeadWord secondPayload idx) ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨363⟩ : UInt256)
      [idx, secondLen, secondPayload, ⟨0⟩, UInt256.ofNat I.calldata.size,
        idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
        schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨445⟩ : UInt256)
      [attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx),
        ⟨0⟩,
        attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx),
        attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx),
        attesterMultiRevokeInnerArrayPayloadWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx),
        idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
        schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  let head := attesterMultiRevokeInnerArrayHeadWord secondPayload idx
  let innerLen := attesterMultiRevokeInnerArrayLengthWord I secondPayload head
  let innerPayload := attesterMultiRevokeInnerArrayPayloadWord I secondPayload head
  let tail :=
    [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
      schemaPayload, ret, selector]
  obtain ⟨k0, C0, rd2353⟩ :=
    attesterX_multiRevokeInnerArrayDecoderEntryAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (l := secondLen) (p := secondPayload)
      (sz := UInt256.ofNat I.calldata.size) (base := outerBase)
      (len := schemaLen) (fp := schemaPayload) (ret := ret) (sel := selector)
      (mem := mem) (aw := aw) (k := k) (C := C) hreach
  obtain ⟨k1, C1, rd2374⟩ :=
    attesterX_multiRevokeInnerArrayOffsetOkAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := secondPayload) (head := head) (ret := ⟨381⟩)
      (sz := UInt256.ofNat I.calldata.size) (tail := tail)
      (mem := mem) (aw := aw) (k := k0) (C := C0)
      (by simp [tail]) (by simpa [head] using hoffsetOk)
      (by simpa [head, tail] using rd2353)
  obtain ⟨k2, C2, rd2399⟩ :=
    attesterX_multiRevokeInnerArrayLengthMaxOkAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := secondPayload) (head := head) (ret := ⟨381⟩)
      (sz := UInt256.ofNat I.calldata.size) (tail := tail)
      (mem := mem) (aw := aw) (k := k1) (C := C1)
      (by simp [tail]) (by simpa [head, innerLen] using hlenOk)
      (by simpa [head, tail] using rd2374)
  obtain ⟨k3, C3, rd381⟩ :=
    attesterX_multiRevokeInnerArrayPayloadOkToReturnAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := secondPayload) (head := head) (ret := ⟨381⟩)
      (sz := UInt256.ofNat I.calldata.size) (tail := tail)
      (mem := mem) (aw := aw) (k := k2) (C := C2)
      (by simp [tail]) (by simpa [head, innerLen, innerPayload] using hpayloadOk)
      (attesterMultiRevokeInnerArrayReturnJumpdest v)
      (by simpa [head, innerLen, tail] using rd2399)
  exact attesterX_multiRevokeInnerArrayNonemptyAndLengthOkAt
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) v
    (len := innerLen) (payload := innerPayload)
    (sz := UInt256.ofNat I.calldata.size) (idx := idx) (outerBase := outerBase)
    (schemaLen := schemaLen) (secondLen := secondLen)
    (secondPayload := secondPayload) (schemaPayload := schemaPayload)
    (ret := ret) (selector := selector) (mem := mem) (aw := aw)
    (k := k3) (C := C3) (by simpa [head, innerLen] using hlenNe)
    (by simpa [head, innerLen] using hlenOk)
    (by simpa [head, innerLen, innerPayload, tail] using rd381)

theorem attesterX_multiRevokeOuterIterationLengthZeroRevertsAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx outerBase schemaLen secondLen secondPayload schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hidxSchema : UInt256.lt idx schemaLen = ⟨1⟩)
    (hidxSecond : UInt256.lt idx secondLen = ⟨1⟩)
    (hoffsetOk :
      UInt256.slt
        (attesterMultiRevokeInnerArrayOffsetWord I
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size) secondPayload)
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩)
    (hlenOk :
      UInt256.gt
        (attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩)
    (hpayloadOk :
      UInt256.sgt
        (attesterMultiRevokeInnerArrayPayloadWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft
            (attesterMultiRevokeInnerArrayLengthWord I secondPayload
              (attesterMultiRevokeInnerArrayHeadWord secondPayload idx)) ⟨5⟩)) = ⟨0⟩)
    (hlenZero :
      attesterMultiRevokeInnerArrayLengthWord I secondPayload
        (attesterMultiRevokeInnerArrayHeadWord secondPayload idx) = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
      [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
        schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  let head := attesterMultiRevokeInnerArrayHeadWord secondPayload idx
  let innerLen := attesterMultiRevokeInnerArrayLengthWord I secondPayload head
  let innerPayload := attesterMultiRevokeInnerArrayPayloadWord I secondPayload head
  let tail :=
    [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
      schemaPayload, ret, selector]
  obtain ⟨k0, C0, rd344⟩ :=
    attesterX_multiRevokeOuterSourceLoopGuard
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
      (secondLen := secondLen) (secondPayload := secondPayload)
      (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
      (mem := mem) (aw := aw) (k := k) (C := C) hidxSchema hreach
  obtain ⟨k1, C1, rd363⟩ :=
    attesterX_multiRevokeOuterSecondArrayAccessOkAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
      (secondLen := secondLen) (secondPayload := secondPayload)
      (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
      (mem := mem) (aw := aw) (k := k0) (C := C0) hidxSecond rd344
  obtain ⟨k2, C2, rd2353⟩ :=
    attesterX_multiRevokeInnerArrayDecoderEntryAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (l := secondLen) (p := secondPayload)
      (sz := UInt256.ofNat I.calldata.size) (base := outerBase)
      (len := schemaLen) (fp := schemaPayload) (ret := ret) (sel := selector)
      (mem := mem) (aw := aw) (k := k1) (C := C1) rd363
  obtain ⟨k3, C3, rd2374⟩ :=
    attesterX_multiRevokeInnerArrayOffsetOkAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := secondPayload) (head := head) (ret := ⟨381⟩)
      (sz := UInt256.ofNat I.calldata.size) (tail := tail)
      (mem := mem) (aw := aw) (k := k2) (C := C2)
      (by simp [tail]) (by simpa [head] using hoffsetOk)
      (by simpa [head, tail] using rd2353)
  obtain ⟨k4, C4, rd2399⟩ :=
    attesterX_multiRevokeInnerArrayLengthMaxOkAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := secondPayload) (head := head) (ret := ⟨381⟩)
      (sz := UInt256.ofNat I.calldata.size) (tail := tail)
      (mem := mem) (aw := aw) (k := k3) (C := C3)
      (by simp [tail]) (by simpa [head, innerLen] using hlenOk)
      (by simpa [head, tail] using rd2374)
  obtain ⟨k5, C5, rd381⟩ :=
    attesterX_multiRevokeInnerArrayPayloadOkToReturnAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := secondPayload) (head := head) (ret := ⟨381⟩)
      (sz := UInt256.ofNat I.calldata.size) (tail := tail)
      (mem := mem) (aw := aw) (k := k4) (C := C4)
      (by simp [tail]) (by simpa [head, innerLen, innerPayload] using hpayloadOk)
      (attesterMultiRevokeInnerArrayReturnJumpdest v)
      (by simpa [head, innerLen, tail] using rd2399)
  exact attesterX_multiRevokeInnerArrayLengthZeroRevertsAt
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) v
    (len := innerLen) (payload := innerPayload) (sz := UInt256.ofNat I.calldata.size)
    (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
    (secondLen := secondLen) (secondPayload := secondPayload)
    (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
    (mem := mem) (aw := aw) (k := k5) (C := C5)
    (by simpa [head, innerLen] using hlenZero)
    (by simpa [head, innerLen, innerPayload, tail] using rd381)

theorem attesterX_multiRevokeOuterIterationOffsetRevertsAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx outerBase schemaLen secondLen secondPayload schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hidxSchema : UInt256.lt idx schemaLen = ⟨1⟩)
    (hidxSecond : UInt256.lt idx secondLen = ⟨1⟩)
    (hoffsetBad :
      UInt256.slt
        (attesterMultiRevokeInnerArrayOffsetWord I
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size) secondPayload)
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
      [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
        schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  let head := attesterMultiRevokeInnerArrayHeadWord secondPayload idx
  let tail :=
    [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
      schemaPayload, ret, selector]
  obtain ⟨k0, C0, rd344⟩ :=
    attesterX_multiRevokeOuterSourceLoopGuard
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
      (secondLen := secondLen) (secondPayload := secondPayload)
      (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
      (mem := mem) (aw := aw) (k := k) (C := C) hidxSchema hreach
  obtain ⟨k1, C1, rd363⟩ :=
    attesterX_multiRevokeOuterSecondArrayAccessOkAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
      (secondLen := secondLen) (secondPayload := secondPayload)
      (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
      (mem := mem) (aw := aw) (k := k0) (C := C0) hidxSecond rd344
  obtain ⟨k2, C2, rd2353⟩ :=
    attesterX_multiRevokeInnerArrayDecoderEntryAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (l := secondLen) (p := secondPayload)
      (sz := UInt256.ofNat I.calldata.size) (base := outerBase)
      (len := schemaLen) (fp := schemaPayload) (ret := ret) (sel := selector)
      (mem := mem) (aw := aw) (k := k1) (C := C1) rd363
  exact
    attesterX_multiRevokeInnerArrayOffsetRevertsAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := secondPayload) (head := head) (ret := ⟨381⟩)
      (sz := UInt256.ofNat I.calldata.size) (tail := tail)
      (mem := mem) (aw := aw) (k := k2) (C := C2)
      (by simp [tail]) (by simpa [head] using hoffsetBad)
      (by simpa [head, tail] using rd2353)

theorem attesterX_multiRevokeOuterIterationLengthMaxRevertsAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx outerBase schemaLen secondLen secondPayload schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hidxSchema : UInt256.lt idx schemaLen = ⟨1⟩)
    (hidxSecond : UInt256.lt idx secondLen = ⟨1⟩)
    (hoffsetOk :
      UInt256.slt
        (attesterMultiRevokeInnerArrayOffsetWord I
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size) secondPayload)
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩)
    (hlenBad :
      UInt256.gt
        (attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨1⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
      [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
        schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  let head := attesterMultiRevokeInnerArrayHeadWord secondPayload idx
  let tail :=
    [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
      schemaPayload, ret, selector]
  obtain ⟨k0, C0, rd344⟩ :=
    attesterX_multiRevokeOuterSourceLoopGuard
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
      (secondLen := secondLen) (secondPayload := secondPayload)
      (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
      (mem := mem) (aw := aw) (k := k) (C := C) hidxSchema hreach
  obtain ⟨k1, C1, rd363⟩ :=
    attesterX_multiRevokeOuterSecondArrayAccessOkAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
      (secondLen := secondLen) (secondPayload := secondPayload)
      (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
      (mem := mem) (aw := aw) (k := k0) (C := C0) hidxSecond rd344
  obtain ⟨k2, C2, rd2353⟩ :=
    attesterX_multiRevokeInnerArrayDecoderEntryAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (l := secondLen) (p := secondPayload)
      (sz := UInt256.ofNat I.calldata.size) (base := outerBase)
      (len := schemaLen) (fp := schemaPayload) (ret := ret) (sel := selector)
      (mem := mem) (aw := aw) (k := k1) (C := C1) rd363
  obtain ⟨k3, C3, rd2374⟩ :=
    attesterX_multiRevokeInnerArrayOffsetOkAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := secondPayload) (head := head) (ret := ⟨381⟩)
      (sz := UInt256.ofNat I.calldata.size) (tail := tail)
      (mem := mem) (aw := aw) (k := k2) (C := C2)
      (by simp [tail]) (by simpa [head] using hoffsetOk)
      (by simpa [head, tail] using rd2353)
  exact
    attesterX_multiRevokeInnerArrayLengthMaxRevertsAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := secondPayload) (head := head) (ret := ⟨381⟩)
      (sz := UInt256.ofNat I.calldata.size) (tail := tail)
      (mem := mem) (aw := aw) (k := k3) (C := C3)
      (by simp [tail]) (by simpa [head] using hlenBad)
      (by simpa [head, tail] using rd2374)

theorem attesterX_multiRevokeOuterIterationPayloadRevertsAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx outerBase schemaLen secondLen secondPayload schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hidxSchema : UInt256.lt idx schemaLen = ⟨1⟩)
    (hidxSecond : UInt256.lt idx secondLen = ⟨1⟩)
    (hoffsetOk :
      UInt256.slt
        (attesterMultiRevokeInnerArrayOffsetWord I
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size) secondPayload)
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩)
    (hlenOk :
      UInt256.gt
        (attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩)
    (hpayloadBad :
      UInt256.sgt
        (attesterMultiRevokeInnerArrayPayloadWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft
            (attesterMultiRevokeInnerArrayLengthWord I secondPayload
              (attesterMultiRevokeInnerArrayHeadWord secondPayload idx)) ⟨5⟩)) = ⟨1⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
      [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
        schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  let head := attesterMultiRevokeInnerArrayHeadWord secondPayload idx
  let innerLen := attesterMultiRevokeInnerArrayLengthWord I secondPayload head
  let tail :=
    [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
      schemaPayload, ret, selector]
  obtain ⟨k0, C0, rd344⟩ :=
    attesterX_multiRevokeOuterSourceLoopGuard
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
      (secondLen := secondLen) (secondPayload := secondPayload)
      (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
      (mem := mem) (aw := aw) (k := k) (C := C) hidxSchema hreach
  obtain ⟨k1, C1, rd363⟩ :=
    attesterX_multiRevokeOuterSecondArrayAccessOkAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
      (secondLen := secondLen) (secondPayload := secondPayload)
      (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
      (mem := mem) (aw := aw) (k := k0) (C := C0) hidxSecond rd344
  obtain ⟨k2, C2, rd2353⟩ :=
    attesterX_multiRevokeInnerArrayDecoderEntryAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (l := secondLen) (p := secondPayload)
      (sz := UInt256.ofNat I.calldata.size) (base := outerBase)
      (len := schemaLen) (fp := schemaPayload) (ret := ret) (sel := selector)
      (mem := mem) (aw := aw) (k := k1) (C := C1) rd363
  obtain ⟨k3, C3, rd2374⟩ :=
    attesterX_multiRevokeInnerArrayOffsetOkAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := secondPayload) (head := head) (ret := ⟨381⟩)
      (sz := UInt256.ofNat I.calldata.size) (tail := tail)
      (mem := mem) (aw := aw) (k := k2) (C := C2)
      (by simp [tail]) (by simpa [head] using hoffsetOk)
      (by simpa [head, tail] using rd2353)
  obtain ⟨k4, C4, rd2399⟩ :=
    attesterX_multiRevokeInnerArrayLengthMaxOkAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := secondPayload) (head := head) (ret := ⟨381⟩)
      (sz := UInt256.ofNat I.calldata.size) (tail := tail)
      (mem := mem) (aw := aw) (k := k3) (C := C3)
      (by simp [tail]) (by simpa [head, innerLen] using hlenOk)
      (by simpa [head, tail] using rd2374)
  obtain ⟨k5, C5, rd2405⟩ :=
    attesterX_multiRevokeInnerArrayPayloadSetupAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := secondPayload) (head := head) (ret := ⟨381⟩)
      (sz := UInt256.ofNat I.calldata.size) (tail := tail)
      (mem := mem) (aw := aw) (k := k4) (C := C4)
      (by simp [tail])
      (by simpa [head, innerLen, tail] using rd2399)
  exact
    attesterX_multiRevokeInnerArrayPayloadGuardRevertsAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := secondPayload) (head := head) (ret := ⟨381⟩)
      (sz := UInt256.ofNat I.calldata.size) (tail := tail)
      (mem := mem) (aw := aw) (k := k5) (C := C5)
      (by simp [tail]) (by simpa [head, innerLen] using hpayloadBad)
      (by simpa [head, innerLen, tail] using rd2405)

theorem attesterX_multiRevokeOuterIterationToAllocAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx outerBase schemaLen secondLen secondPayload schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hidxSchema : UInt256.lt idx schemaLen = ⟨1⟩)
    (hidxSecond : UInt256.lt idx secondLen = ⟨1⟩)
    (hoffsetOk :
      UInt256.slt
        (attesterMultiRevokeInnerArrayOffsetWord I
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size) secondPayload)
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩)
    (hlenOk :
      UInt256.gt
        (attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩)
    (hpayloadOk :
      UInt256.sgt
        (attesterMultiRevokeInnerArrayPayloadWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft
            (attesterMultiRevokeInnerArrayLengthWord I secondPayload
              (attesterMultiRevokeInnerArrayHeadWord secondPayload idx)) ⟨5⟩)) = ⟨0⟩)
    (hlenNe :
      attesterMultiRevokeInnerArrayLengthWord I secondPayload
        (attesterMultiRevokeInnerArrayHeadWord secondPayload idx) ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
      [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
        schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨445⟩ : UInt256)
      [attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx),
        ⟨0⟩,
        attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx),
        attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx),
        attesterMultiRevokeInnerArrayPayloadWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx),
        idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
        schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd344⟩ :=
    attesterX_multiRevokeOuterSourceLoopGuard
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
      (secondLen := secondLen) (secondPayload := secondPayload)
      (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
      (mem := mem) (aw := aw) (k := k) (C := C) hidxSchema hreach
  obtain ⟨k1, C1, rd363⟩ :=
    attesterX_multiRevokeOuterSecondArrayAccessOkAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
      (secondLen := secondLen) (secondPayload := secondPayload)
      (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
      (mem := mem) (aw := aw) (k := k0) (C := C0) hidxSecond rd344
  exact attesterX_multiRevokeInnerDecoderToAllocAt
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) v
    (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
    (secondLen := secondLen) (secondPayload := secondPayload)
    (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
    (mem := mem) (aw := aw) (k := k1) (C := C1)
    hoffsetOk hlenOk hpayloadOk hlenNe rd363

theorem attesterX_multiRevokeOuterIterationToInnerInitAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx outerBase schemaLen secondLen secondPayload schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hidxSchema : UInt256.lt idx schemaLen = ⟨1⟩)
    (hidxSecond : UInt256.lt idx secondLen = ⟨1⟩)
    (hoffsetOk :
      UInt256.slt
        (attesterMultiRevokeInnerArrayOffsetWord I
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size) secondPayload)
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩)
    (hlenOk :
      UInt256.gt
        (attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩)
    (hpayloadOk :
      UInt256.sgt
        (attesterMultiRevokeInnerArrayPayloadWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft
            (attesterMultiRevokeInnerArrayLengthWord I secondPayload
              (attesterMultiRevokeInnerArrayHeadWord secondPayload idx)) ⟨5⟩)) = ⟨0⟩)
    (hlenNe :
      attesterMultiRevokeInnerArrayLengthWord I secondPayload
        (attesterMultiRevokeInnerArrayHeadWord secondPayload idx) ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
      [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
        schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨475⟩ : UInt256)
      [((⟨32⟩ : UInt256) + attesterInnerArrayAllocFreeWord mem aw),
        attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx),
        attesterInnerArrayAllocFreeWord mem aw,
        ⟨0⟩,
        attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx),
        attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx),
        attesterMultiRevokeInnerArrayPayloadWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx),
        idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
        schemaPayload, ret, selector]
      (attesterInnerArrayAllocMem
        (attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        mem aw)
      (attesterInnerArrayAllocAw
        (attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  let head := attesterMultiRevokeInnerArrayHeadWord secondPayload idx
  let innerLen := attesterMultiRevokeInnerArrayLengthWord I secondPayload head
  let innerPayload := attesterMultiRevokeInnerArrayPayloadWord I secondPayload head
  let tail :=
    [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
      schemaPayload, ret, selector]
  obtain ⟨k0, C0, rd445⟩ :=
    attesterX_multiRevokeOuterIterationToAllocAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
      (secondLen := secondLen) (secondPayload := secondPayload)
      (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
      (mem := mem) (aw := aw) (k := k) (C := C)
      hidxSchema hidxSecond hoffsetOk hlenOk hpayloadOk hlenNe hreach
  obtain ⟨k1, C1, rd475⟩ :=
    attesterX_multiRevokeFirstInnerArrayAllocToInitLoop
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (len := innerLen) (payload := innerPayload) (tail := tail)
      (mem := mem) (aw := aw) (k := k0) (C := C0)
      (by simp [tail]) (by simpa [head, innerLen] using hlenNe)
      (by simpa [head, innerLen, innerPayload, tail] using rd445)
  exact ⟨k1, C1, by
    simpa [head, innerLen, innerPayload, tail] using rd475⟩

theorem attesterX_multiRevokeInnerCopyToOuterLoopAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {innerIdx base innerLen payload idx outerBase schemaLen secondLen secondPayload
      schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hidxSchema : UInt256.lt idx schemaLen = ⟨1⟩)
    (hmem : outerBase.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding outerBase.toNat 32 =
      UInt256.toByteArray schemaLen)
    (hawMul : aw.toNat * 32 < UInt256.size)
    (houter64 : 64 + 32 ≤ outerBase.toNat)
    (hbase : outerBase.toNat + 32 ≤ base.toNat)
    (hfree :
      base.toNat + 32 ≤ (attesterMultiRevokePostCopyFreeWord mem aw).toNat)
    (hfree96 :
      (attesterMultiRevokePostCopyFreeWord mem aw).toNat + 96 < UInt256.size)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨608⟩ : UInt256)
      [innerIdx, base, innerLen, innerLen, payload, idx, outerBase, schemaLen,
        secondLen, secondPayload, schemaLen, schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        [attesterMultiRevokePostCopyNextIdx idx, outerBase, schemaLen,
          secondLen, secondPayload, schemaLen, schemaPayload, ret, selector]
        (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx mem aw)
        ByteArray.empty (cA, σ) k' C' := by
  have hmloadOuter :
      attesterMloadWord
        (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyDataAw base I schemaPayload idx mem aw)
        outerBase = schemaLen := by
    exact attesterMultiRevokePostCopyDataMem_mloadOuter
      (base := base) (outerBase := outerBase) (len := schemaLen)
      (schemaPayload := schemaPayload) (idx := idx) (mem := mem) (aw := aw)
      hmem hread hawMul houter64 hbase hfree hfree96
  have hidxOuter :
      UInt256.lt idx
        (attesterMloadWord
          (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
          (attesterMultiRevokePostCopyDataAw base I schemaPayload idx mem aw)
          outerBase) = ⟨1⟩ := by
    rw [hmloadOuter]
    exact hidxSchema
  exact attesterX_multiRevokePostInnerCopyToOuterLoop
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) v
    (innerIdx := innerIdx) (base := base) (innerLen := innerLen)
    (payload := payload) (idx := idx) (outerBase := outerBase)
    (schemaLen := schemaLen) (secondLen := secondLen)
    (secondPayload := secondPayload) (schemaPayload := schemaPayload)
    (ret := ret) (selector := selector) (mem := mem) (aw := aw)
    (k := k) (C := C) hidxSchema hidxOuter hreach

structure attesterMultiRevokeInnerCopyReadInvAt
    (I : ExecutionEnv) (base len payload outerBase schemaLen : UInt256)
    (n : Nat) (s : AttesterMultiRevokeInnerArrayCopyState) : Prop where
  idx : s.idx = UInt256.ofNat (len.toNat - n)
  le : n ≤ len.toNat
  awGe : 3 ≤ s.aw.toNat
  awMul : s.aw.toNat * 32 < UInt256.size
  read : s.mem.readWithPadding base.toNat 32 = UInt256.toByteArray len
  memSize : base.toNat + 32 ≤ s.mem.size
  baseGe : 64 + 32 ≤ base.toNat
  base63 : base.toNat + 63 < UInt256.size
  freeGe : base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat
  freeExact :
    (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat =
      base.toNat + 32 + 96 * len.toNat + 64 * (len.toNat - n)
  freeSpare :
    (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat +
      64 * n + 96 < UInt256.size
  zeroGe : base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord s.mem s.aw).toNat
  slotGe : base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayCopySlotWord base s.idx).toNat
  slot63 : (attesterMultiRevokeInnerArrayCopySlotWord base s.idx).toNat + 63 < UInt256.size
  baseSlot63 : base.toNat + 32 + 32 * len.toNat + 63 < UInt256.size
  outerRead : s.mem.readWithPadding outerBase.toNat 32 = UInt256.toByteArray schemaLen
  outerMemSize : outerBase.toNat + 32 ≤ s.mem.size
  outer64 : 64 + 32 ≤ outerBase.toNat
  outerBeforeBase : outerBase.toNat + 32 ≤ base.toNat
  layout : AttesterMultiRevokeInnerCopyReadLayout I base len payload (len.toNat - n) s.mem

theorem attesterMultiRevokeInnerCopyReadInvAt_idx
    {I : ExecutionEnv} {base len payload outerBase schemaLen : UInt256}
    {n : Nat} {s : AttesterMultiRevokeInnerArrayCopyState}
    (hInv : attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen n s) :
    s.idx = UInt256.ofNat (len.toNat - n) := by
  exact hInv.idx

theorem attesterMultiRevokeInnerCopyReadInvAt_le
    {I : ExecutionEnv} {base len payload outerBase schemaLen : UInt256}
    {n : Nat} {s : AttesterMultiRevokeInnerArrayCopyState}
    (hInv : attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen n s) :
    n ≤ len.toNat := by
  exact hInv.le

set_option maxHeartbeats 1000000 in
theorem attesterMultiRevokeInnerCopyReadInvAt_init
    {I : ExecutionEnv} {base len payload outerBase schemaLen : UInt256}
    {b : AttesterMultiRevokeInnerArrayInitState}
    (hInv : attesterMultiRevokeInnerInitReadInvAt I base len outerBase schemaLen 0 b) :
    attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen len.toNat
      (attesterMultiRevokeInnerCopyInitState b) := by
  have hInvOrig := hInv
  have hfree63 :
      (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 63 <
        UInt256.size := by
    have hfb := hInv.freeBound
    omega
  have hfree32 :
      (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 32 <
        UInt256.size := by
    omega
  have hsecondToNat :
      (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat =
        (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 32 :=
    attesterMultiRevokeInnerArrayInitSecondZeroWord_toNat
      (mem := b.mem) (aw := b.aw) hfree32
  have hsecondGe :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat := by
    rw [hsecondToNat]
    exact le_trans hInv.freeGe (Nat.le_add_right _ _)
  have hsecond63 :
      (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat + 63 <
        UInt256.size := by
    rw [hsecondToNat]
    have hspare := hInv.freeSpare
    omega
  have hslot63 : b.slot.toNat + 63 < UInt256.size := by
    have hslotBound := hInv.slotBound
    omega
  have hawStep :=
    attesterMultiRevokeInnerArrayInitStepAw_bounds
      (slot := b.slot) (mem := b.mem) (aw := b.aw)
      hInv.awGe hInv.awMul hfree63 hsecond63 hslot63
  have hreadStep :
      (attesterMultiRevokeInnerArrayInitFinalMem b).readWithPadding base.toNat 32 =
        UInt256.toByteArray len := by
    change
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).readWithPadding
          base.toNat 32 =
        UInt256.toByteArray len
    exact attesterMultiRevokeInnerArrayInitStep_readWithPadding_nat
      (base := base) (slot := b.slot) (len := len) (mem := b.mem) (aw := b.aw)
      hInv.memSize hInv.read hInv.baseGe hInv.freeGe hsecondGe hInv.slotGe
  have hmemStep :
      base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayInitFinalMem b).size := by
    change base.toNat + 32 ≤
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).size
    exact attesterMultiRevokeInnerArrayInitStep_base_size
      (base := base) (slot := b.slot) (len := len) (mem := b.mem) (aw := b.aw)
      hInv.memSize
  have houterFree :
      outerBase.toNat + 32 ≤ (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat := by
    exact le_trans hInv.outerBeforeBase
      (le_trans (Nat.le_add_right base.toNat 32) hInv.freeGe)
  have houterSecond :
      outerBase.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat := by
    rw [hsecondToNat]
    exact le_trans houterFree (Nat.le_add_right _ _)
  have houterSlot : outerBase.toNat + 32 ≤ b.slot.toNat := by
    exact le_trans hInv.outerBeforeBase
      (le_trans (Nat.le_add_right base.toNat 32) hInv.slotGe)
  have hreadOuterStep :
      (attesterMultiRevokeInnerArrayInitFinalMem b).readWithPadding outerBase.toNat 32 =
        UInt256.toByteArray schemaLen := by
    change
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).readWithPadding
          outerBase.toNat 32 =
        UInt256.toByteArray schemaLen
    exact attesterMultiRevokeInnerArrayInitStep_readWithPadding_nat
      (base := outerBase) (slot := b.slot) (len := schemaLen)
      (mem := b.mem) (aw := b.aw)
      hInv.outerMemSize hInv.outerRead hInv.outer64 houterFree houterSecond houterSlot
  have houterMemStep :
      outerBase.toNat + 32 ≤ (attesterMultiRevokeInnerArrayInitFinalMem b).size := by
    change outerBase.toNat + 32 ≤
      (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw).size
    exact le_trans hInv.outerMemSize attesterMultiRevokeInnerArrayInitStep_size_ge
  have hfree96 :
      64 + 32 ≤ (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat := by
    have hbase96 : 64 + 32 ≤ base.toNat + 32 :=
      le_trans hInv.baseGe (Nat.le_add_right base.toNat 32)
    exact le_trans hbase96 hInv.freeGe
  have hsecond96 :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayInitSecondZeroWord b.mem b.aw).toNat := by
    have hbase96 : 64 + 32 ≤ base.toNat + 32 :=
      le_trans hInv.baseGe (Nat.le_add_right base.toNat 32)
    exact le_trans hbase96 hsecondGe
  have hslot96 : 64 + 32 ≤ b.slot.toNat := by
    have hbase96 : 64 + 32 ≤ base.toNat + 32 :=
      le_trans hInv.baseGe (Nat.le_add_right base.toNat 32)
    exact le_trans hbase96 hInv.slotGe
  have hfree64 :
      (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 64 <
        UInt256.size := by
    have hfb := hInv.freeBound
    omega
  have hfreeStepToNat :
      (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat =
        (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 64 := by
    change
      (attesterMultiOuterArrayInitFreeWord
          (attesterMultiRevokeInnerArrayInitStepMem b.slot b.mem b.aw)
          (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw)).toNat =
        (attesterMultiOuterArrayInitFreeWord b.mem b.aw).toNat + 64
    exact attesterMultiRevokeInnerArrayInitStep_freeWord_toNat
      (slot := b.slot) (mem := b.mem) (aw := b.aw)
      hfree96 hsecond96 hslot96 hawStep.2 hawStep.1 hfree64
  have hfreeFinalGe :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat := by
    rw [hfreeStepToNat]
    exact le_trans hInv.freeGe (Nat.le_add_right _ _)
  have hfreeFinalSpare :
      (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat +
          64 * len.toNat + 96 < UInt256.size := by
    rw [hfreeStepToNat]
    have hspare := hInv.freeSpare
    omega
  have hfreeFinal32 :
      (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat + 32 <
        UInt256.size := by
    omega
  have hzeroToNat :
      (attesterMultiRevokeInnerArrayCopyZeroWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat =
        (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat + 32 :=
    attesterMultiRevokeInnerArrayCopyZeroWord_toNat hfreeFinal32
  have hzeroGe :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroWord
          (attesterMultiRevokeInnerArrayInitFinalMem b)
          (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat := by
    rw [hzeroToNat]
    exact le_trans hfreeFinalGe (Nat.le_add_right _ _)
  have hbase63 : base.toNat + 63 < UInt256.size := by
    have hbaseSlot := hInv.baseSlot63
    omega
  have hslot0Bound :
      base.toNat + 32 + 32 * (⟨0⟩ : UInt256).toNat + 63 < UInt256.size := by
    change base.toNat + 32 + 32 * 0 + 63 < UInt256.size
    have hbaseSlot := hInv.baseSlot63
    omega
  have hslot0ToNat :
      (attesterMultiRevokeInnerArrayCopySlotWord base (⟨0⟩ : UInt256)).toNat =
        base.toNat + 32 + 32 * (⟨0⟩ : UInt256).toNat :=
    attesterMultiRevokeInnerArrayCopySlotWord_toNat (by omega)
  have hslot0Ge :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopySlotWord base (⟨0⟩ : UInt256)).toNat :=
    attesterMultiRevokeInnerArrayCopySlotWord_above_base (by omega)
  have hslot0_63 :
      (attesterMultiRevokeInnerArrayCopySlotWord base (⟨0⟩ : UInt256)).toNat + 63 <
        UInt256.size := by
    rw [hslot0ToNat]
    simpa using hslot0Bound
  have hidx0 :
      (⟨0⟩ : UInt256) = UInt256.ofNat (len.toNat - len.toNat) := by
    rw [show len.toNat - len.toNat = 0 by omega]
    apply u256_inj
    rfl
  exact
    { idx := by simpa using hidx0
      le := le_rfl
      awGe := by
        change 3 ≤ (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw).toNat
        exact hawStep.1
      awMul := by
        change
          (attesterMultiRevokeInnerArrayInitStepAw b.slot b.mem b.aw).toNat * 32 <
            UInt256.size
        exact hawStep.2
      read := by
        change
          (attesterMultiRevokeInnerArrayInitFinalMem b).readWithPadding base.toNat 32 =
            UInt256.toByteArray len
        exact hreadStep
      memSize := by
        change base.toNat + 32 ≤ (attesterMultiRevokeInnerArrayInitFinalMem b).size
        exact hmemStep
      baseGe := hInv.baseGe
      base63 := hbase63
      freeGe := by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyFreeWord
            (attesterMultiRevokeInnerArrayInitFinalMem b)
            (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat
        exact hfreeFinalGe
      freeExact := by
        change
          (attesterMultiRevokeInnerArrayCopyFreeWord
            (attesterMultiRevokeInnerArrayInitFinalMem b)
            (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat =
              base.toNat + 32 + 96 * len.toNat + 64 * (len.toNat - len.toNat)
        rw [hfreeStepToNat, hInv.freeExact]
        have hsub : len.toNat - (0 + 1) + 1 = len.toNat := by
          have hle := hInv.le
          omega
        have hzero : len.toNat - len.toNat = 0 := by omega
        rw [hzero]
        nlinarith
      freeSpare := by
        change
          (attesterMultiRevokeInnerArrayCopyFreeWord
              (attesterMultiRevokeInnerArrayInitFinalMem b)
              (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat +
              64 * len.toNat + 96 <
            UInt256.size
        exact hfreeFinalSpare
      zeroGe := by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyZeroWord
            (attesterMultiRevokeInnerArrayInitFinalMem b)
            (attesterMultiRevokeInnerArrayInitFinalAw b)).toNat
        exact hzeroGe
      slotGe := by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopySlotWord base (⟨0⟩ : UInt256)).toNat
        exact hslot0Ge
      slot63 := by
        change
          (attesterMultiRevokeInnerArrayCopySlotWord base (⟨0⟩ : UInt256)).toNat + 63 <
            UInt256.size
        exact hslot0_63
      baseSlot63 := hInv.baseSlot63
      outerRead := by
        change (attesterMultiRevokeInnerArrayInitFinalMem b).readWithPadding outerBase.toNat 32 =
          UInt256.toByteArray schemaLen
        exact hreadOuterStep
      outerMemSize := by
        change outerBase.toNat + 32 ≤ (attesterMultiRevokeInnerArrayInitFinalMem b).size
        exact houterMemStep
      outer64 := hInv.outer64
      outerBeforeBase := hInv.outerBeforeBase
      layout := by
        intro j hj
        omega }

set_option maxHeartbeats 1000000 in
theorem attesterMultiRevokeInnerCopyReadInvAt_step
    {I : ExecutionEnv} {base len payload outerBase schemaLen : UInt256}
    {n : Nat} {s : AttesterMultiRevokeInnerArrayCopyState}
    (hInv : attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen
      (n + 1) s) :
    attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen n
      (attesterMultiRevokeInnerArrayCopyStepState I base payload s) := by
  have hbaseGe' : 64 + 32 ≤ base.toNat := hInv.baseGe
  have hbase63' : base.toNat + 63 < UInt256.size := hInv.base63
  have hfreeGe' :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat := hInv.freeGe
  have hzeroGe' :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroWord s.mem s.aw).toNat := hInv.zeroGe
  have hslotGe' :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopySlotWord base s.idx).toNat := hInv.slotGe
  have hslot63' :
      (attesterMultiRevokeInnerArrayCopySlotWord base s.idx).toNat + 63 <
        UInt256.size := hInv.slot63
  have hnextIdx :
      attesterMultiRevokeInnerArrayCopyNextIdx s.idx =
        UInt256.ofNat (len.toNat - n) := by
    rw [hInv.idx]
    exact attesterMultiRevokeInnerArrayCopyNextIdx_ofNat_progress
      (len := len.toNat) (n := n) hInv.le len.val.isLt
  have hnextIdxToNat :
      (attesterMultiRevokeInnerArrayCopyNextIdx s.idx).toNat = len.toNat - n := by
    rw [hnextIdx]
    exact ulit_toNat' (len.toNat - n)
      (lt_of_le_of_lt (Nat.sub_le _ _) len.val.isLt)
  have hfree63 :
      (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat + 63 <
        UInt256.size := by
    have hspare := hInv.freeSpare
    omega
  have hfree32 :
      (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat + 32 <
        UInt256.size := by
    have hspare := hInv.freeSpare
    omega
  have hzeroToNat :
      (attesterMultiRevokeInnerArrayCopyZeroWord s.mem s.aw).toNat =
        (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat + 32 :=
    attesterMultiRevokeInnerArrayCopyZeroWord_toNat hfree32
  have hzero63 :
      (attesterMultiRevokeInnerArrayCopyZeroWord s.mem s.aw).toNat + 63 <
        UInt256.size := by
    rw [hzeroToNat]
    have hspare := hInv.freeSpare
    omega
  have hawStep :=
    attesterMultiRevokeInnerArrayCopyStepAw_bounds
      (I := I) (base := base) (payload := payload) (idx := s.idx)
      (mem := s.mem) (aw := s.aw)
      hInv.awGe hInv.awMul hbase63' hfree63 hzero63 hslot63'
  have hreadStep :
      (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).readWithPadding
          base.toNat 32 =
        UInt256.toByteArray len :=
    attesterMultiRevokeInnerArrayCopyStep_readWithPadding_nat
      (I := I) (base := base) (payload := payload) (idx := s.idx)
      (len := len) (mem := s.mem) (aw := s.aw)
      hInv.memSize hInv.read hbaseGe' hfreeGe' hzeroGe' hslotGe'
  have hmemStep :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).size :=
    attesterMultiRevokeInnerArrayCopyStep_base_size
      (I := I) (base := base) (payload := payload) (idx := s.idx)
      (mem := s.mem) (aw := s.aw) hInv.memSize
  have houterFree :
      outerBase.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat := by
    exact le_trans hInv.outerBeforeBase (by omega)
  have houterZero :
      outerBase.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroWord s.mem s.aw).toNat := by
    exact le_trans hInv.outerBeforeBase (by omega)
  have houterSlot :
      outerBase.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopySlotWord base s.idx).toNat := by
    exact le_trans hInv.outerBeforeBase (by omega)
  have hreadOuterStep :
      (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).readWithPadding
          outerBase.toNat 32 =
        UInt256.toByteArray schemaLen := by
    exact attesterMultiRevokeInnerArrayCopyStep_readWithPadding_at_nat
      (I := I) (readBase := outerBase) (base := base) (payload := payload)
      (idx := s.idx) (len := schemaLen) (mem := s.mem) (aw := s.aw)
      hInv.outerMemSize hInv.outerRead hInv.outer64 houterFree houterZero houterSlot
  have houterMemStep :
      outerBase.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).size :=
    le_trans hInv.outerMemSize attesterMultiRevokeInnerArrayCopyStep_size_ge
  have hfree96 :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat := by
    have hbase96 : 64 + 32 ≤ base.toNat + 32 := by omega
    exact le_trans hbase96 hfreeGe'
  have hzero96 :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord s.mem s.aw).toNat := by
    have hbase96 : 64 + 32 ≤ base.toNat + 32 := by omega
    exact le_trans hbase96 hzeroGe'
  have hslot96 :
      64 + 32 ≤ (attesterMultiRevokeInnerArrayCopySlotWord base s.idx).toNat := by
    have hbase96 : 64 + 32 ≤ base.toNat + 32 := by omega
    exact le_trans hbase96 hslotGe'
  have hfree64 :
      (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat + 64 <
        UInt256.size := by
    omega
  have hfreeStepToNat :
      (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat =
        (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat + 64 :=
    attesterMultiRevokeInnerArrayCopyStep_freeWord_toNat
      (I := I) (base := base) (payload := payload) (idx := s.idx)
      (mem := s.mem) (aw := s.aw)
      hfree96 hzero96 hslot96 hawStep.2 hawStep.1 hfree64
  have hfreeStepGe :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat := by
    rw [hfreeStepToNat]
    exact le_trans hfreeGe' (Nat.le_add_right _ _)
  have hfreeStepSpare :
      (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat +
          64 * n + 96 < UInt256.size := by
    rw [hfreeStepToNat]
    have hspare := hInv.freeSpare
    omega
  have hfreeStep32 :
      (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat +
          32 < UInt256.size := by
    omega
  have hzeroStepToNat :
      (attesterMultiRevokeInnerArrayCopyZeroWord
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat =
        (attesterMultiRevokeInnerArrayCopyFreeWord
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat +
          32 :=
    attesterMultiRevokeInnerArrayCopyZeroWord_toNat hfreeStep32
  have hzeroStepGe :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopyZeroWord
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat := by
    rw [hzeroStepToNat]
    exact le_trans hfreeStepGe (Nat.le_add_right _ _)
  have hslotNextBound :
      base.toNat + 32 +
          32 * (attesterMultiRevokeInnerArrayCopyNextIdx s.idx).toNat + 63 <
        UInt256.size := by
    rw [hnextIdxToNat]
    have hleLen : 32 * (len.toNat - n) ≤ 32 * len.toNat :=
      Nat.mul_le_mul_left 32 (Nat.sub_le _ _)
    exact lt_of_le_of_lt (by omega) hInv.baseSlot63
  have hslotNextToNat :
      (attesterMultiRevokeInnerArrayCopySlotWord base
          (attesterMultiRevokeInnerArrayCopyNextIdx s.idx)).toNat =
        base.toNat + 32 +
          32 * (attesterMultiRevokeInnerArrayCopyNextIdx s.idx).toNat :=
    attesterMultiRevokeInnerArrayCopySlotWord_toNat (by omega)
  have hslotNextGe :
      base.toNat + 32 ≤
        (attesterMultiRevokeInnerArrayCopySlotWord base
          (attesterMultiRevokeInnerArrayCopyNextIdx s.idx)).toNat :=
    attesterMultiRevokeInnerArrayCopySlotWord_above_base (by omega)
  have hslotNext63 :
      (attesterMultiRevokeInnerArrayCopySlotWord base
          (attesterMultiRevokeInnerArrayCopyNextIdx s.idx)).toNat + 63 <
        UInt256.size := by
    rw [hslotNextToNat]
    exact hslotNextBound
  exact
    { idx := by
        change attesterMultiRevokeInnerArrayCopyNextIdx s.idx =
          UInt256.ofNat (len.toNat - n)
        exact hnextIdx
      le := by
        have hle := hInv.le
        omega
      awGe := by
        change 3 ≤ (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw).toNat
        exact hawStep.1
      awMul := by
        change
          (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw).toNat *
              32 <
            UInt256.size
        exact hawStep.2
      read := by
        change
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).readWithPadding
              base.toNat 32 =
            UInt256.toByteArray len
        exact hreadStep
      memSize := by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).size
        exact hmemStep
      baseGe := hInv.baseGe
      base63 := hInv.base63
      freeGe := by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyFreeWord
            (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
            (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat
        exact hfreeStepGe
      freeExact := by
        change
          (attesterMultiRevokeInnerArrayCopyFreeWord
            (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
            (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat =
              base.toNat + 32 + 96 * len.toNat + 64 * (len.toNat - n)
        rw [hfreeStepToNat, hInv.freeExact]
        have hsub :
            len.toNat - n = len.toNat - (n + 1) + 1 := by
          have hle := hInv.le
          omega
        rw [hsub]
        nlinarith
      freeSpare := by
        change
          (attesterMultiRevokeInnerArrayCopyFreeWord
            (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
            (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat +
              64 * n + 96 <
            UInt256.size
        exact hfreeStepSpare
      zeroGe := by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyZeroWord
            (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
            (attesterMultiRevokeInnerArrayCopyStepAw I base payload s.idx s.mem s.aw)).toNat
        exact hzeroStepGe
      slotGe := by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopySlotWord base
            (attesterMultiRevokeInnerArrayCopyNextIdx s.idx)).toNat
        exact hslotNextGe
      slot63 := by
        change
          (attesterMultiRevokeInnerArrayCopySlotWord base
            (attesterMultiRevokeInnerArrayCopyNextIdx s.idx)).toNat + 63 <
            UInt256.size
        exact hslotNext63
      baseSlot63 := hInv.baseSlot63
      outerRead := by
        change
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).readWithPadding
              outerBase.toNat 32 =
            UInt256.toByteArray schemaLen
        exact hreadOuterStep
      outerMemSize := by
        change outerBase.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).size
        exact houterMemStep
      outer64 := hInv.outer64
      outerBeforeBase := hInv.outerBeforeBase
      layout := by
        change AttesterMultiRevokeInnerCopyReadLayout I base len payload
          (len.toNat - n)
          (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw)
        exact AttesterMultiRevokeInnerCopyReadLayout_step
          (I := I) (base := base) (len := len) (payload := payload)
          (idx := s.idx) (mem := s.mem) (aw := s.aw) (n := n)
          hInv.idx hInv.le hInv.baseGe hInv.baseSlot63 hInv.freeExact
          hInv.freeSpare hInv.layout }

theorem AttesterReadPreservedBefore_innerCopyStep
    {I : ExecutionEnv} {mem₀ : ByteArray}
    {base len payload outerBase schemaLen : UInt256}
    {n : Nat} {s : AttesterMultiRevokeInnerArrayCopyState}
    (hInv : attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen
      (n + 1) s)
    (hpres : AttesterReadPreservedBefore mem₀ s.mem base.toNat) :
    AttesterReadPreservedBefore mem₀
      (attesterMultiRevokeInnerArrayCopyStepState I base payload s).mem base.toNat := by
  intro read word hmem0 hread0 hread64 hbefore
  rcases hpres hmem0 hread0 hread64 hbefore with ⟨hmem, hread⟩
  have hreadLt : read < UInt256.size := by
    have hbaseLt : base.toNat < UInt256.size := base.val.isLt
    omega
  let readWord : UInt256 := UInt256.ofNat read
  have hreadWordToNat : readWord.toNat = read := ulit_toNat' read hreadLt
  have hfree :
      read + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat := by
    exact le_trans hbefore (le_trans (Nat.le_add_right base.toNat 32) hInv.freeGe)
  have hzero :
      read + 32 ≤ (attesterMultiRevokeInnerArrayCopyZeroWord s.mem s.aw).toNat := by
    exact le_trans hbefore (le_trans (Nat.le_add_right base.toNat 32) hInv.zeroGe)
  have hslot :
      read + 32 ≤ (attesterMultiRevokeInnerArrayCopySlotWord base s.idx).toNat := by
    exact le_trans hbefore (le_trans (Nat.le_add_right base.toNat 32) hInv.slotGe)
  constructor
  · change read + 32 ≤
      (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).size
    exact le_trans hmem attesterMultiRevokeInnerArrayCopyStep_size_ge
  · change
      (attesterMultiRevokeInnerArrayCopyStepMem I base payload s.idx s.mem s.aw).readWithPadding
          read 32 =
        UInt256.toByteArray word
    have hstep :=
      attesterMultiRevokeInnerArrayCopyStep_readWithPadding_at_nat
        (I := I) (readBase := readWord) (base := base) (payload := payload)
        (idx := s.idx) (len := word) (mem := s.mem) (aw := s.aw)
        (by simpa [readWord, hreadWordToNat] using hmem)
        (by simpa [readWord, hreadWordToNat] using hread)
        (by simpa [readWord, hreadWordToNat] using hread64)
        (by simpa [readWord, hreadWordToNat] using hfree)
        (by simpa [readWord, hreadWordToNat] using hzero)
        (by simpa [readWord, hreadWordToNat] using hslot)
    simpa [readWord, hreadWordToNat] using hstep

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeInnerArrayCopyLoopWithReadInvariantAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base len payload outerBase schemaLen : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hinit :
      attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen len.toNat
        { idx := (⟨0⟩ : UInt256), mem := mem, aw := aw })
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
      ((⟨0⟩ : UInt256) :: base :: len :: len :: payload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ s' k' C',
      s'.idx = len ∧
      attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen 0 s' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨608⟩ : UInt256)
        (attesterMultiRevokeInnerArrayCopyStack base len payload tail s')
        s'.mem s'.aw ByteArray.empty (cA, σ) k' C' := by
  let Inv := attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen
  have hload :
      ∀ n s, Inv n s →
        attesterMloadWord
          (attesterMultiRevokeInnerArrayCopyZeroMem I payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyZeroAw I payload s.idx s.mem s.aw)
          base = len := by
    intro n s hInv
    have hfree96 :
        (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat + 96 <
          UInt256.size := by
      have hspare := hInv.freeSpare
      omega
    exact attesterMultiRevokeInnerArrayCopyZero_mloadLen_of_bounds_nat
      (I := I) (base := base) (payload := payload) (idx := s.idx)
      (len := len) (mem := s.mem) (aw := s.aw)
      hInv.memSize hInv.read hInv.awGe hInv.awMul hfree96 hInv.baseGe hInv.freeGe hInv.zeroGe
  exact attesterX_multiRevokeInnerArrayCopyLoopWithStateInvariant
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) v
    (base := base) (len := len) (payload := payload) (tail := tail)
    (mem := mem) (aw := aw) (k := k) (C := C) htail
    (Inv := Inv)
    (fun n s hInv => attesterMultiRevokeInnerCopyReadInvAt_idx hInv)
    (fun n s hInv => attesterMultiRevokeInnerCopyReadInvAt_le hInv)
    hload
    (fun n s hInv => attesterMultiRevokeInnerCopyReadInvAt_step hInv)
    (by simpa [Inv] using hinit)
    hreach

theorem attesterX_multiRevokeInnerCopyLoopToOuterLoopAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base len payload idx outerBase schemaLen secondLen secondPayload schemaPayload
      ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hidxSchema : UInt256.lt idx schemaLen = ⟨1⟩)
    (hinit :
      attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen len.toNat
        { idx := (⟨0⟩ : UInt256), mem := mem, aw := aw })
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
      ((⟨0⟩ : UInt256) :: base :: len :: len :: payload ::
        [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
          schemaPayload, ret, selector])
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ s' k' C',
      s'.idx = len ∧
      attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen 0 s' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        [attesterMultiRevokePostCopyNextIdx idx, outerBase, schemaLen,
          secondLen, secondPayload, schemaLen, schemaPayload, ret, selector]
        (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx s'.mem s'.aw)
        (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx s'.mem s'.aw)
        ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨s', k0, C0, hsidx, hInv, rd608⟩ :=
    attesterX_multiRevokeInnerArrayCopyLoopWithReadInvariantAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := base) (len := len) (payload := payload)
      (outerBase := outerBase) (schemaLen := schemaLen)
      (tail := [idx, outerBase, schemaLen, secondLen, secondPayload,
        schemaLen, schemaPayload, ret, selector])
      (mem := mem) (aw := aw) (k := k) (C := C) (by simp) hinit hreach
  obtain ⟨k1, C1, rd335⟩ :=
    attesterX_multiRevokeInnerCopyToOuterLoopAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (innerIdx := s'.idx) (base := base) (innerLen := len)
      (payload := payload) (idx := idx) (outerBase := outerBase)
      (schemaLen := schemaLen) (secondLen := secondLen)
      (secondPayload := secondPayload) (schemaPayload := schemaPayload)
      (ret := ret) (selector := selector) (mem := s'.mem) (aw := s'.aw)
      (k := k0) (C := C0) hidxSchema
      hInv.outerMemSize hInv.outerRead hInv.awMul hInv.outer64
      hInv.outerBeforeBase hInv.freeGe hInv.freeSpare
      (by simpa [hsidx, attesterMultiRevokeInnerArrayCopyStack] using rd608)
  exact ⟨s', k1, C1, hsidx, hInv, rd335⟩

theorem attesterX_multiRevokeInnerCopyLoopToOuterLoopPreservedAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base len payload idx outerBase schemaLen secondLen secondPayload schemaPayload
      ret selector : UInt256}
    {mem₀ mem : ByteArray} {aw : UInt256} {k C}
    (hidxSchema : UInt256.lt idx schemaLen = ⟨1⟩)
    (hinit :
      attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen len.toNat
        { idx := (⟨0⟩ : UInt256), mem := mem, aw := aw })
    (hpresInit :
      AttesterReadPreservedBefore mem₀ mem base.toNat)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨518⟩ : UInt256)
      ((⟨0⟩ : UInt256) :: base :: len :: len :: payload ::
        [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
          schemaPayload, ret, selector])
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ s' k' C',
      s'.idx = len ∧
      attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen 0 s' ∧
      AttesterReadPreservedBefore mem₀ s'.mem base.toNat ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        [attesterMultiRevokePostCopyNextIdx idx, outerBase, schemaLen,
          secondLen, secondPayload, schemaLen, schemaPayload, ret, selector]
        (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx s'.mem s'.aw)
        (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx s'.mem s'.aw)
        ByteArray.empty (cA, σ) k' C' := by
  let Inv : Nat → AttesterMultiRevokeInnerArrayCopyState → Prop :=
    fun n s =>
      attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen n s ∧
      AttesterReadPreservedBefore mem₀ s.mem base.toNat
  have hload :
      ∀ n s, Inv n s →
        attesterMloadWord
          (attesterMultiRevokeInnerArrayCopyZeroMem I payload s.idx s.mem s.aw)
          (attesterMultiRevokeInnerArrayCopyZeroAw I payload s.idx s.mem s.aw)
          base = len := by
    intro n s hInv
    have hfree96 :
        (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat + 96 <
          UInt256.size := by
      have hspare := hInv.1.freeSpare
      omega
    exact attesterMultiRevokeInnerArrayCopyZero_mloadLen_of_bounds_nat
      (I := I) (base := base) (payload := payload) (idx := s.idx)
      (len := len) (mem := s.mem) (aw := s.aw)
      hInv.1.memSize hInv.1.read hInv.1.awGe hInv.1.awMul hfree96
      hInv.1.baseGe hInv.1.freeGe hInv.1.zeroGe
  obtain ⟨s', k0, C0, hsidx, hInv, rd608⟩ :=
    attesterX_multiRevokeInnerArrayCopyLoopWithStateInvariant
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := base) (len := len) (payload := payload)
      (tail := [idx, outerBase, schemaLen, secondLen, secondPayload,
        schemaLen, schemaPayload, ret, selector])
      (mem := mem) (aw := aw) (k := k) (C := C) (by simp)
      (Inv := Inv)
      (fun n s hInv => attesterMultiRevokeInnerCopyReadInvAt_idx hInv.1)
      (fun n s hInv => attesterMultiRevokeInnerCopyReadInvAt_le hInv.1)
      hload
      (fun n s hInv =>
        ⟨attesterMultiRevokeInnerCopyReadInvAt_step hInv.1,
          AttesterReadPreservedBefore_innerCopyStep hInv.1 hInv.2⟩)
      (by exact ⟨hinit, hpresInit⟩)
      hreach
  obtain ⟨k1, C1, rd335⟩ :=
    attesterX_multiRevokeInnerCopyToOuterLoopAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (innerIdx := s'.idx) (base := base) (innerLen := len)
      (payload := payload) (idx := idx) (outerBase := outerBase)
      (schemaLen := schemaLen) (secondLen := secondLen)
      (secondPayload := secondPayload) (schemaPayload := schemaPayload)
      (ret := ret) (selector := selector) (mem := s'.mem) (aw := s'.aw)
      (k := k0) (C := C0) hidxSchema
      hInv.1.outerMemSize hInv.1.outerRead hInv.1.awMul hInv.1.outer64
      hInv.1.outerBeforeBase hInv.1.freeGe hInv.1.freeSpare
      (by simpa [hsidx, attesterMultiRevokeInnerArrayCopyStack] using rd608)
  exact ⟨s', k1, C1, hsidx, hInv.1, hInv.2, rd335⟩

theorem attesterMultiRevokePostCopyOuterMem_readOuter_from_copyInvAt
    {I : ExecutionEnv} {base len payload outerBase schemaLen schemaPayload idx : UInt256}
    {s : AttesterMultiRevokeInnerArrayCopyState}
    (hInv : attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen 0 s)
    (hslotBound : outerBase.toNat + 32 + 32 * idx.toNat < UInt256.size) :
    (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx s.mem s.aw).readWithPadding
        outerBase.toNat 32 =
      UInt256.toByteArray schemaLen ∧
    outerBase.toNat + 32 ≤
      (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx s.mem s.aw).size := by
  exact attesterMultiRevokePostCopyOuterMem_readOuter_and_size
    (base := base) (outerBase := outerBase) (len := schemaLen)
    (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
    hInv.outerMemSize hInv.outerRead hInv.outer64 hInv.outerBeforeBase
    (by
      simpa [attesterMultiRevokePostCopyFreeWord,
        attesterMultiRevokeInnerArrayCopyFreeWord] using hInv.freeGe)
    (by
      simpa [attesterMultiRevokePostCopyFreeWord,
        attesterMultiRevokeInnerArrayCopyFreeWord] using hInv.freeSpare)
    hslotBound

theorem attesterMultiRevokePostCopyOuter_cursorFacts_from_copyInvAt
    {I : ExecutionEnv} {base len payload outerBase schemaLen schemaPayload idx : UInt256}
    {s : AttesterMultiRevokeInnerArrayCopyState}
    (hInv : attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen 0 s)
    (hslotBound : outerBase.toNat + 32 + 32 * idx.toNat + 63 < UInt256.size) :
    ((attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx s.mem s.aw).readWithPadding
        outerBase.toNat 32 =
      UInt256.toByteArray schemaLen ∧
    outerBase.toNat + 32 ≤
      (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx s.mem s.aw).size) ∧
    3 ≤ (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx s.mem s.aw).toNat ∧
    (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx s.mem s.aw).toNat *
        32 < UInt256.size ∧
    (attesterInnerArrayAllocFreeWord
        (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx s.mem s.aw)
        (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx s.mem s.aw)).toNat =
      (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat + 64 ∧
    64 + 32 ≤
      (attesterInnerArrayAllocFreeWord
        (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx s.mem s.aw)
        (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx s.mem s.aw)).toNat ∧
    outerBase.toNat + 32 ≤
      (attesterInnerArrayAllocFreeWord
        (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx s.mem s.aw)
        (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx s.mem s.aw)).toNat := by
  have hfree96 :
      64 + 32 ≤ (attesterMultiRevokePostCopyFreeWord s.mem s.aw).toNat := by
    change 64 + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat
    have hbaseGe := hInv.baseGe
    have hbase96 : 64 + 32 ≤ base.toNat + 32 := by omega
    exact le_trans hbase96 hInv.freeGe
  have hfreeSpare96 :
      (attesterMultiRevokePostCopyFreeWord s.mem s.aw).toNat + 96 <
        UInt256.size := by
    simpa [attesterMultiRevokePostCopyFreeWord,
      attesterMultiRevokeInnerArrayCopyFreeWord] using hInv.freeSpare
  have hfree32 :
      (attesterMultiRevokePostCopyFreeWord s.mem s.aw).toNat + 32 <
        UInt256.size := by
    omega
  have hfree64 :
      (attesterMultiRevokePostCopyFreeWord s.mem s.aw).toNat + 64 <
        UInt256.size := by
    omega
  have hfree95 :
      (attesterMultiRevokePostCopyFreeWord s.mem s.aw).toNat + 95 <
        UInt256.size := by
    omega
  have hdataToNat :
      (attesterMultiRevokePostCopyDataOffsetWord s.mem s.aw).toNat =
        (attesterMultiRevokePostCopyFreeWord s.mem s.aw).toNat + 32 := by
    unfold attesterMultiRevokePostCopyDataOffsetWord
    exact uadd_lit32_toNat (attesterMultiRevokePostCopyFreeWord s.mem s.aw) hfree32
  have hdata96 :
      64 + 32 ≤ (attesterMultiRevokePostCopyDataOffsetWord s.mem s.aw).toNat := by
    rw [hdataToNat]
    omega
  have hslotToNat :
      (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat =
        outerBase.toNat + 32 + 32 * idx.toNat := by
    exact attesterMultiRevokePostCopyOuterSlotWord_toNat (by omega)
  have hslot96 :
      64 + 32 ≤ (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat := by
    rw [hslotToNat]
    have houter64 := hInv.outer64
    omega
  have hslot63 :
      (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat + 63 <
        UInt256.size := by
    rw [hslotToNat]
    omega
  have houter63 : outerBase.toNat + 63 < UInt256.size := by
    have hbase63 := hInv.base63
    have houterBeforeBase := hInv.outerBeforeBase
    omega
  have hawBounds :=
    attesterMultiRevokePostCopyOuterAw_bounds
      (I := I) (base := base) (outerBase := outerBase)
      (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
      hInv.awGe hInv.awMul hfree95 houter63 hslot63
  have hfreeToNat :
      (attesterInnerArrayAllocFreeWord
          (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx s.mem s.aw)
          (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx s.mem s.aw)).toNat =
        (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat + 64 := by
    have h :=
      attesterMultiRevokePostCopyOuterMem_freeWord_toNat
        (I := I) (base := base) (outerBase := outerBase)
        (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
        hfree96 hdata96 hslot96 hawBounds.2 hawBounds.1 hfree64
    simpa [attesterMultiRevokePostCopyFreeWord,
      attesterMultiRevokeInnerArrayCopyFreeWord] using h
  constructor
  · exact attesterMultiRevokePostCopyOuterMem_readOuter_from_copyInvAt
      (I := I) (base := base) (len := len) (payload := payload)
      (outerBase := outerBase) (schemaLen := schemaLen)
      (schemaPayload := schemaPayload) (idx := idx) (s := s)
      hInv (by omega)
  · constructor
    · exact hawBounds.1
    · constructor
      · exact hawBounds.2
      · constructor
        · exact hfreeToNat
        · constructor
          · rw [hfreeToNat]
            have hfreeGe := hfree96
            change 64 + 32 ≤ (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat at hfreeGe
            omega
          · rw [hfreeToNat]
            have houterBeforeBase := hInv.outerBeforeBase
            have hbaseBeforeFree := hInv.freeGe
            omega

theorem attesterMultiRevokePostCopyOuter_freeWordExact_from_copyInvAt
    {I : ExecutionEnv} {base len payload outerBase schemaLen schemaPayload idx : UInt256}
    {s : AttesterMultiRevokeInnerArrayCopyState}
    (hInv : attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen 0 s)
    (hslotBound : outerBase.toNat + 32 + 32 * idx.toNat + 63 < UInt256.size) :
    (attesterInnerArrayAllocFreeWord
        (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx s.mem s.aw)
        (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx s.mem s.aw)).toNat =
      base.toNat + 96 + 160 * len.toNat := by
  have hfacts :=
    attesterMultiRevokePostCopyOuter_cursorFacts_from_copyInvAt
      (I := I) (base := base) (len := len) (payload := payload)
      (outerBase := outerBase) (schemaLen := schemaLen)
      (schemaPayload := schemaPayload) (idx := idx) (s := s)
      hInv hslotBound
  rcases hfacts with ⟨_houter, _hawGe, _hawMul, hfreeToNat, _hfreeGe, _houterBefore⟩
  rw [hfreeToNat, hInv.freeExact]
  omega

set_option maxHeartbeats 1000000 in
theorem attesterMultiRevokePostCopyOuter_currentRequestReadLayout_from_copyInvAt
    {I : ExecutionEnv} {callargs : Store}
    {schemas schemaUids uids : List Value} {i : Nat} {schema : Value}
    {base len payload outerBase schemaLen schemaPayload idx : UInt256}
    {contentLo bound : Nat}
    {s : AttesterMultiRevokeInnerArrayCopyState}
    (v : AttesterImmutables)
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs)
    (hSchemas : callargs.get? "schemas" = some (.array schemas))
    (hlookupSchema : lookupNth? schemas i = some schema)
    (hlookupOuter : lookupNth? schemaUids i = some (.array uids))
    (hoff0 : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hiMax : i ≤ solcMaxU64)
    (hidx : idx = UInt256.ofNat i)
    (hschemaPayload :
      schemaPayload = (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩)
    (hlenToNat : len.toNat = uids.length)
    (huidWords :
      ∀ {j uid}, lookupNth? uids j = some uid →
        ∃ uidWord,
          attesterBytes32ValueWord? uid = some uidWord ∧
          uidWord =
            calldataWord I.calldata
              (attesterMultiRevokeInnerArrayCopyCalldataOffset payload
                (UInt256.ofNat j)).toNat)
    (hInv : attesterMultiRevokeInnerCopyReadInvAt I base len payload outerBase schemaLen 0 s)
    (hslotBeforeBase :
      (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat + 32 ≤ base.toNat)
    (hcontentLoBase : contentLo ≤ base.toNat)
    (hbound :
      base.toNat + 96 + 160 * len.toNat ≤ bound)
    (hslotBound : outerBase.toNat + 32 + 32 * idx.toNat + 63 < UInt256.size) :
    AttesterMultiRevokeRequestReadLayoutAtBounded schemas schemaUids
      (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx s.mem s.aw)
      outerBase contentLo bound i := by
  intro schema' uids' hschema' huids'
  rw [hlookupSchema] at hschema'
  cases hschema'
  rw [hlookupOuter] at huids'
  cases huids'
  let finalMem := attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx
    s.mem s.aw
  let free := attesterMultiRevokePostCopyFreeWord s.mem s.aw
  let dataOff := attesterMultiRevokePostCopyDataOffsetWord s.mem s.aw
  let slot := attesterMultiRevokePostCopyOuterSlotWord outerBase idx
  have hslotToNat :
      slot.toNat = outerBase.toNat + 32 + 32 * idx.toNat := by
    dsimp [slot]
    exact attesterMultiRevokePostCopyOuterSlotWord_toNat (by omega)
  have hfree32 : free.toNat + 32 < UInt256.size := by
    have hspare : free.toNat + 96 < UInt256.size := by
      simpa [free, attesterMultiRevokePostCopyFreeWord,
        attesterMultiRevokeInnerArrayCopyFreeWord] using hInv.freeSpare
    omega
  have hdataToNat : dataOff.toNat = free.toNat + 32 := by
    unfold dataOff attesterMultiRevokePostCopyDataOffsetWord
    exact uadd_lit32_toNat free hfree32
  have hslotBelowFree : slot.toNat + 32 ≤ free.toNat := by
    exact le_trans (by simpa [slot] using hslotBeforeBase)
      (by
        change base.toNat ≤ (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat
        have h := hInv.freeGe
        omega)
  obtain ⟨schemaWord, hschemaWord, hschemaWordEq⟩ :=
    attesterDecode_multiRevoke_schema_word_at_payload
      (v := v) (I := I) (callargs := callargs) (schemas := schemas)
      (idx := i) (schema := schema) hdec hSchemas hlookupSchema hoff0 hiMax
  have hschemaReadWord :
      attesterMultiRevokePostCopySchemaWord I schemaPayload idx = schemaWord := by
    rw [hschemaWordEq, hschemaPayload, hidx]
  have hreqDataToNat : ((⟨32⟩ : UInt256) + free).toNat = dataOff.toNat := by
    rfl
  have hlenSize : uids.length < UInt256.size := by
    rw [← hlenToNat]
    exact len.val.isLt
  have hlenWord : UInt256.ofNat uids.length = len := by
    apply u256_inj
    rw [ulit_toNat' uids.length hlenSize, hlenToNat]
  have hfreeToNat :
      free.toNat = base.toNat + 32 + 160 * len.toNat := by
    dsimp [free, attesterMultiRevokePostCopyFreeWord,
      attesterMultiRevokeInnerArrayCopyFreeWord]
    rw [hInv.freeExact]
    omega
  have hbaseReqBound : base.toNat + 32 ≤ bound := by
    have hlenNonneg : 0 ≤ len.toNat := Nat.zero_le _
    nlinarith
  refine ⟨schemaWord, free, base, hschemaWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [slot]
    have hslot64Idx :
        64 + 32 ≤ (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat := by
      change 64 + 32 ≤ slot.toNat
      rw [hslotToNat]
      exact le_trans hInv.outer64 (by omega)
    simpa [hidx] using hslot64Idx
  · dsimp [slot]
    have hslotBoundIdx :
        (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat + 32 ≤
          bound := by
      exact le_trans (by simpa [slot] using hslotBeforeBase)
        (le_trans (Nat.le_add_right base.toNat 32) hbaseReqBound)
    simpa [hidx] using hslotBoundIdx
  · dsimp [slot]
    rw [← hidx]
    exact attesterMultiRevokePostCopyOuterMem_current_slot_size
      (I := I) (base := base) (outerBase := outerBase)
      (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
  · dsimp [slot, finalMem]
    rw [← hidx]
    exact attesterMultiRevokePostCopyOuterMem_read_current_slot
      (I := I) (base := base) (outerBase := outerBase)
      (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
  · rw [hfreeToNat]
    exact le_trans hcontentLoBase (by omega)
  · rw [hfreeToNat]
    omega
  · dsimp [finalMem]
    exact attesterMultiRevokePostCopyOuterMem_current_schema_size
      (I := I) (base := base) (outerBase := outerBase)
      (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
  · rw [hreqDataToNat, hdataToNat, hfreeToNat]
    exact le_trans hcontentLoBase (by omega)
  · rw [hreqDataToNat, hdataToNat, hfreeToNat]
    omega
  · rw [hreqDataToNat]
    dsimp [finalMem, dataOff]
    exact attesterMultiRevokePostCopyOuterMem_current_data_size
      (I := I) (base := base) (outerBase := outerBase)
      (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
  · dsimp [finalMem]
    rw [← hschemaReadWord]
    exact attesterMultiRevokePostCopyOuterMem_read_current_schema
      (I := I) (base := base) (outerBase := outerBase)
      (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
      hdataToNat (Or.inr (by simpa [slot] using hslotBelowFree))
  · rw [hreqDataToNat]
    dsimp [finalMem, dataOff]
    exact attesterMultiRevokePostCopyOuterMem_read_current_data_ptr
      (I := I) (base := base) (outerBase := outerBase)
      (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
      (Or.inr (by
        rw [hdataToNat]
        exact le_trans (by simpa [slot] using hslotBelowFree) (by omega)))
  · exact hcontentLoBase
  · exact hbaseReqBound
  · dsimp [finalMem]
    exact attesterMultiRevokePostCopyOuterMem_size_ge
      (I := I) (base := base) (outerBase := outerBase)
      (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
      hInv.memSize
  · constructor
    · dsimp [finalMem]
      have hreadLen :
          finalMem.readWithPadding base.toNat 32 = UInt256.toByteArray len := by
        dsimp [finalMem]
        exact attesterMultiRevokePostCopyOuterMem_read_preserved_before_free
          (I := I) (base := base) (outerBase := outerBase)
          (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
          hInv.memSize hInv.read hInv.baseGe hInv.freeGe hdataToNat
          (Or.inr (by simpa [slot] using hslotBeforeBase))
      simpa [hlenWord] using hreadLen
    · intro j uid hlookupUid
      have hjLtUids : j < uids.length := lookupNth?_some_length hlookupUid
      have hjLtLen : j < len.toNat := by
        rw [hlenToNat]
        exact hjLtUids
      obtain ⟨uidWord, huidWord, huidWordEq⟩ :=
        huidWords hlookupUid
      have hcopyElem := hInv.layout (j := j) hjLtLen
      dsimp only [AttesterMultiRevokeInnerCopyReadLayout] at hcopyElem
      let copySlot := attesterMultiRevokeInnerArrayCopySlotWord base (UInt256.ofNat j)
      let elemPtr := attesterMultiRevokeInnerCopyTuplePtr base len j
      rcases hcopyElem with
        ⟨hcopySlotMem, hcopyPtrMem, hcopyPtr32Mem,
          hcopySlotRead, hcopyPtrRead, hcopyPtr32Read⟩
      have hjSize : j < UInt256.size := lt_trans hjLtLen len.val.isLt
      have hjWordToNat : (UInt256.ofNat j).toNat = j :=
        ulit_toNat' j hjSize
      have hcopySlotBound : base.toNat + 32 + 32 * j + 63 < UInt256.size := by
        have hmul : 32 * j ≤ 32 * len.toNat :=
          Nat.mul_le_mul_left 32 (le_of_lt hjLtLen)
        have hbaseSlot63 := hInv.baseSlot63
        omega
      have hcopySlotToNat : copySlot.toNat = base.toNat + 32 + 32 * j := by
        unfold copySlot
        rw [attesterMultiRevokeInnerArrayCopySlotWord_toNat]
        · rw [hjWordToNat]
        · rw [hjWordToNat]
          omega
      have hcopyPtrToNat :
          elemPtr.toNat = base.toNat + 32 + 96 * len.toNat + 64 * j := by
        unfold elemPtr
        exact attesterMultiRevokeInnerCopyTuplePtr_toNat (by
          unfold attesterMultiRevokeInnerCopyTuplePtrNat
          have hmul : 64 * j ≤ 64 * len.toNat :=
            Nat.mul_le_mul_left 64 (le_of_lt hjLtLen)
          have hfreeSpare := hInv.freeSpare
          rw [hInv.freeExact] at hfreeSpare
          omega)
      have hcopyPtr32ToNat :
          ((⟨32⟩ : UInt256) + elemPtr).toNat =
            base.toNat + 32 + 96 * len.toNat + 64 * j + 32 := by
        rw [attesterMultiRevokeInnerCopyTuplePtr_add32_toNat]
        · unfold attesterMultiRevokeInnerCopyTuplePtrNat
          rfl
        · unfold attesterMultiRevokeInnerCopyTuplePtrNat
          have hmul : 64 * j ≤ 64 * len.toNat :=
            Nat.mul_le_mul_left 64 (le_of_lt hjLtLen)
          have hfreeSpare := hInv.freeSpare
          rw [hInv.freeExact] at hfreeSpare
          omega
      let elemSlot := (⟨32⟩ : UInt256) +
        UInt256.mul (⟨32⟩ : UInt256) (UInt256.ofNat j) + base
      have hmulJToNat :
          (UInt256.mul (⟨32⟩ : UInt256) (UInt256.ofNat j)).toNat = 32 * j := by
        rw [u256_mul_toNat]
        rw [show (⟨32⟩ : UInt256).toNat = 32 by decide, hjWordToNat]
        exact Nat.mod_eq_of_lt (by omega)
      have hprefixToNat :
          ((⟨32⟩ : UInt256) +
              UInt256.mul (⟨32⟩ : UInt256) (UInt256.ofNat j)).toNat =
            32 + 32 * j := by
        rw [uadd_toNat, hmulJToNat]
        rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
        exact Nat.mod_eq_of_lt (by omega)
      have helemSlotToNat : elemSlot.toNat = base.toNat + 32 + 32 * j := by
        unfold elemSlot
        rw [uadd_toNat, hprefixToNat]
        rw [show 32 + 32 * j + base.toNat = base.toNat + 32 + 32 * j by omega]
        exact Nat.mod_eq_of_lt (by omega)
      have helemSlotEqNat : elemSlot.toNat = copySlot.toNat := by
        rw [helemSlotToNat, hcopySlotToNat]
      have hcopySlotBeforeFree : copySlot.toNat + 32 ≤ free.toNat := by
        rw [hcopySlotToNat]
        change base.toNat + 32 + 32 * j + 32 ≤
          (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat
        rw [hInv.freeExact]
        have hmul : 32 * j ≤ 96 * len.toNat := by
          have hmul32 : 32 * j ≤ 32 * len.toNat :=
            Nat.mul_le_mul_left 32 (le_of_lt hjLtLen)
          nlinarith
        omega
      have hcopyPtrBeforeFree : elemPtr.toNat + 32 ≤ free.toNat := by
        rw [hcopyPtrToNat]
        change base.toNat + 32 + 96 * len.toNat + 64 * j + 32 ≤
          (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat
        rw [hInv.freeExact]
        omega
      have hcopyPtr32BeforeFree :
          ((⟨32⟩ : UInt256) + elemPtr).toNat + 32 ≤ free.toNat := by
        rw [hcopyPtr32ToNat]
        change base.toNat + 32 + 96 * len.toNat + 64 * j + 32 + 32 ≤
          (attesterMultiRevokeInnerArrayCopyFreeWord s.mem s.aw).toNat
        rw [hInv.freeExact]
        omega
      have hcurrentSlotBelowCopySlot : slot.toNat + 32 ≤ copySlot.toNat := by
        rw [hcopySlotToNat]
        exact le_trans (by simpa [slot] using hslotBeforeBase) (by omega)
      have hcurrentSlotBelowPtr : slot.toNat + 32 ≤ elemPtr.toNat := by
        rw [hcopyPtrToNat]
        exact le_trans (by simpa [slot] using hslotBeforeBase) (by omega)
      have hcurrentSlotBelowPtr32 : slot.toNat + 32 ≤ ((⟨32⟩ : UInt256) + elemPtr).toNat := by
        rw [hcopyPtr32ToNat]
        exact le_trans (by simpa [slot] using hslotBeforeBase) (by omega)
      refine ⟨uidWord, elemPtr, huidWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [helemSlotToNat]
        exact le_trans hcontentLoBase (by omega)
      · rw [helemSlotToNat]
        omega
      · rw [helemSlotEqNat]
        exact attesterMultiRevokePostCopyOuterMem_size_ge
          (I := I) (base := base) (outerBase := outerBase)
          (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
          hcopySlotMem
      · rw [helemSlotEqNat]
        exact attesterMultiRevokePostCopyOuterMem_read_preserved_before_free
          (I := I) (base := base) (outerBase := outerBase)
          (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
          hcopySlotMem hcopySlotRead
          (by
            rw [hcopySlotToNat]
            have hbaseGe := hInv.baseGe
            omega)
          hcopySlotBeforeFree hdataToNat
          (Or.inr (by simpa [slot] using hcurrentSlotBelowCopySlot))
      · rw [hcopyPtrToNat]
        exact le_trans hcontentLoBase (by omega)
      · rw [hcopyPtrToNat]
        omega
      · exact attesterMultiRevokePostCopyOuterMem_size_ge
          (I := I) (base := base) (outerBase := outerBase)
          (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
          hcopyPtrMem
      · rw [hcopyPtr32ToNat]
        exact le_trans hcontentLoBase (by omega)
      · rw [hcopyPtr32ToNat]
        omega
      · exact attesterMultiRevokePostCopyOuterMem_size_ge
          (I := I) (base := base) (outerBase := outerBase)
          (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
          hcopyPtr32Mem
      · have hreadPtr :
            finalMem.readWithPadding elemPtr.toNat 32 =
              UInt256.toByteArray
                (calldataWord I.calldata
                  (attesterMultiRevokeInnerArrayCopyCalldataOffset payload
                    (UInt256.ofNat j)).toNat) := by
          dsimp [finalMem]
          exact attesterMultiRevokePostCopyOuterMem_read_preserved_before_free
            (I := I) (base := base) (outerBase := outerBase)
            (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
            hcopyPtrMem hcopyPtrRead
            (by
              rw [hcopyPtrToNat]
              omega)
            hcopyPtrBeforeFree hdataToNat
            (Or.inr (by simpa [slot] using hcurrentSlotBelowPtr))
        have hwordEq :
            calldataWord I.calldata
                (attesterMultiRevokeInnerArrayCopyCalldataOffset payload
                  (UInt256.ofNat j)).toNat =
              uidWord := by
          exact huidWordEq.symm
        simpa [hwordEq] using hreadPtr
      · dsimp [finalMem]
        exact attesterMultiRevokePostCopyOuterMem_read_preserved_before_free
          (I := I) (base := base) (outerBase := outerBase)
          (schemaPayload := schemaPayload) (idx := idx) (mem := s.mem) (aw := s.aw)
          hcopyPtr32Mem hcopyPtr32Read
          (by
            rw [hcopyPtr32ToNat]
            omega)
          hcopyPtr32BeforeFree hdataToNat
          (Or.inr (by simpa [slot] using hcurrentSlotBelowPtr32))

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeOuterIterationToOuterLoopWithReadInvariantAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx outerBase schemaLen secondLen secondPayload schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hidxSchema : UInt256.lt idx schemaLen = ⟨1⟩)
    (hidxSecond : UInt256.lt idx secondLen = ⟨1⟩)
    (hoffsetOk :
      UInt256.slt
        (attesterMultiRevokeInnerArrayOffsetWord I
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size) secondPayload)
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩)
    (hlenOk :
      UInt256.gt
        (attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩)
    (hpayloadOk :
      UInt256.sgt
        (attesterMultiRevokeInnerArrayPayloadWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft
            (attesterMultiRevokeInnerArrayLengthWord I secondPayload
              (attesterMultiRevokeInnerArrayHeadWord secondPayload idx)) ⟨5⟩)) = ⟨0⟩)
    (hlenNe :
      attesterMultiRevokeInnerArrayLengthWord I secondPayload
        (attesterMultiRevokeInnerArrayHeadWord secondPayload idx) ≠ ⟨0⟩)
    (hawGe : 3 ≤ aw.toNat)
    (hawMul : aw.toNat * 32 < UInt256.size)
    (houterRead : mem.readWithPadding outerBase.toNat 32 = UInt256.toByteArray schemaLen)
    (houterMemSize : outerBase.toNat + 32 ≤ mem.size)
    (houter64 : 64 + 32 ≤ outerBase.toNat)
    (hbaseGe : 64 + 32 ≤ (attesterInnerArrayAllocFreeWord mem aw).toNat)
    (houterBeforeBase :
      outerBase.toNat + 32 ≤ (attesterInnerArrayAllocFreeWord mem aw).toNat)
    (hbaseSpare :
      (attesterInnerArrayAllocFreeWord mem aw).toNat + 32 +
        160 *
          (attesterMultiRevokeInnerArrayLengthWord I secondPayload
            (attesterMultiRevokeInnerArrayHeadWord secondPayload idx)).toNat +
        96 < UInt256.size)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
      [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
        schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ b' s' k' C',
      b'.remaining = (⟨1⟩ : UInt256) ∧
      attesterMultiRevokeInnerInitReadInvAt I
        (attesterInnerArrayAllocFreeWord mem aw)
        (attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        outerBase schemaLen 0 b' ∧
      s'.idx =
        (attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx)) ∧
      attesterMultiRevokeInnerCopyReadInvAt I
        (attesterInnerArrayAllocFreeWord mem aw)
        (attesterMultiRevokeInnerArrayLengthWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        (attesterMultiRevokeInnerArrayPayloadWord I secondPayload
          (attesterMultiRevokeInnerArrayHeadWord secondPayload idx))
        outerBase schemaLen 0 s' ∧
      AttesterReadPreservedBefore mem s'.mem
        (attesterInnerArrayAllocFreeWord mem aw).toNat ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        [attesterMultiRevokePostCopyNextIdx idx, outerBase, schemaLen,
          secondLen, secondPayload, schemaLen, schemaPayload, ret, selector]
        (attesterMultiRevokePostCopyOuterMem
          (attesterInnerArrayAllocFreeWord mem aw) outerBase I schemaPayload idx s'.mem s'.aw)
        (attesterMultiRevokePostCopyOuterAw
          (attesterInnerArrayAllocFreeWord mem aw) outerBase I schemaPayload idx s'.mem s'.aw)
        ByteArray.empty (cA, σ) k' C' := by
  let head := attesterMultiRevokeInnerArrayHeadWord secondPayload idx
  let innerLen := attesterMultiRevokeInnerArrayLengthWord I secondPayload head
  let innerPayload := attesterMultiRevokeInnerArrayPayloadWord I secondPayload head
  let base := attesterInnerArrayAllocFreeWord mem aw
  let tail :=
    [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
      schemaPayload, ret, selector]
  obtain ⟨k0, C0, rd475⟩ :=
    attesterX_multiRevokeOuterIterationToInnerInitAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
      (secondLen := secondLen) (secondPayload := secondPayload)
      (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
      (mem := mem) (aw := aw) (k := k) (C := C)
      hidxSchema hidxSecond hoffsetOk hlenOk hpayloadOk hlenNe hreach
  have hlenNatNe : innerLen.toNat ≠ 0 := by
    intro hzero
    apply hlenNe
    apply u256_inj
    simpa [innerLen] using hzero
  have hinit :
      attesterMultiRevokeInnerInitReadInvAt I base innerLen outerBase schemaLen
        (innerLen.toNat - 1)
        { slot := ((⟨32⟩ : UInt256) + base),
          remaining := innerLen,
          mem := attesterInnerArrayAllocMem innerLen mem aw,
          aw := attesterInnerArrayAllocAw innerLen mem aw } := by
    exact attesterMultiRevokeInnerInitReadInvAt_init
      (I := I) (base := base) (len := innerLen)
      (outerBase := outerBase) (schemaLen := schemaLen)
      (mem := mem) (aw := aw)
      hlenNatNe hawGe hawMul (by simpa [base] using hbaseGe)
      (by simpa [base, innerLen, head] using hbaseSpare)
      houterRead houterMemSize houter64
      (by simpa [base] using houterBeforeBase) rfl
  have hpresAlloc :
      AttesterReadPreservedBefore mem (attesterInnerArrayAllocMem innerLen mem aw)
        base.toNat := by
    exact AttesterReadPreservedBefore_innerAlloc
      (len := innerLen) (mem := mem) (aw := aw) (base := base) rfl
  let InitInv : Nat → AttesterMultiRevokeInnerArrayInitState → Prop :=
    fun n b =>
      attesterMultiRevokeInnerInitReadInvAt I base innerLen outerBase schemaLen n b ∧
      AttesterReadPreservedBefore mem b.mem base.toNat
  obtain ⟨b', k1, C1, hbrem, hInitFinalPair, rd518⟩ :=
    attesterX_multiRevokeInnerArrayInitLoopWithStateInvariantAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (slot := ((⟨32⟩ : UInt256) + base)) (base := base)
      (len := innerLen) (payload := innerPayload) (tail := tail)
      (mem := attesterInnerArrayAllocMem innerLen mem aw)
      (aw := attesterInnerArrayAllocAw innerLen mem aw)
      (k := k0) (C := C0) (by simp [tail])
      InitInv
      (fun n b hInv => attesterMultiRevokeInnerInitReadInvAt_remaining hInv.1)
      (fun n b hInv => attesterMultiRevokeInnerInitReadInvAt_bound hInv.1)
      (fun n b hInv =>
        ⟨attesterMultiRevokeInnerInitReadInvAt_step hInv.1,
          AttesterReadPreservedBefore_innerInitStep hInv.1 hInv.2⟩)
      (by exact ⟨hinit, hpresAlloc⟩)
      (by simpa [base, innerLen, innerPayload, head, tail] using rd475)
  have hInitFinal :
      attesterMultiRevokeInnerInitReadInvAt I base innerLen outerBase schemaLen 0 b' :=
    hInitFinalPair.1
  have hpresInitFinal :
      AttesterReadPreservedBefore mem b'.mem base.toNat :=
    hInitFinalPair.2
  have hpresInitFinalMem :
      AttesterReadPreservedBefore mem
        (attesterMultiRevokeInnerArrayInitFinalMem b') base.toNat :=
    AttesterReadPreservedBefore_innerInitFinal hInitFinal hpresInitFinal
  have hcopyInit :
      attesterMultiRevokeInnerCopyReadInvAt I base innerLen innerPayload outerBase schemaLen
        innerLen.toNat (attesterMultiRevokeInnerCopyInitState b') :=
    attesterMultiRevokeInnerCopyReadInvAt_init (payload := innerPayload) hInitFinal
  have hpresCopyInit :
      AttesterReadPreservedBefore mem
        (attesterMultiRevokeInnerCopyInitState b').mem base.toNat := by
    change AttesterReadPreservedBefore mem
      (attesterMultiRevokeInnerArrayInitFinalMem b') base.toNat
    exact hpresInitFinalMem
  obtain ⟨s', k2, C2, hsidx, hCopy, hpresCopy, rd335⟩ :=
    attesterX_multiRevokeInnerCopyLoopToOuterLoopPreservedAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := base) (len := innerLen) (payload := innerPayload)
      (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
      (secondLen := secondLen) (secondPayload := secondPayload)
      (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
      (mem := attesterMultiRevokeInnerArrayInitFinalMem b')
      (aw := attesterMultiRevokeInnerArrayInitFinalAw b')
      (k := k1) (C := C1) hidxSchema hcopyInit hpresCopyInit
      (by
        simpa [attesterMultiRevokeInnerCopyInitState, base, innerLen, innerPayload,
          tail, attesterMultiRevokeInnerArrayInitExitStackAt] using rd518)
  have hpresCopyFree :
      AttesterReadPreservedBefore mem s'.mem
        (attesterInnerArrayAllocFreeWord mem aw).toNat := by
    change AttesterReadPreservedBefore mem s'.mem base.toNat
    exact hpresCopy
  exact ⟨b', s', k2, C2, hbrem, by simpa [base, innerLen] using hInitFinal,
    by simpa [innerLen] using hsidx, by simpa [base, innerLen, innerPayload] using hCopy,
    hpresCopyFree, by simpa [base, innerLen, innerPayload, head] using rd335⟩

set_option maxHeartbeats 1000000 in
theorem AttesterMultiRevokeOuterLoopInv.body_or_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {callargs : Store} {schemas schemaUids : List Value}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs)
    (hSchemas : callargs.get? "schemas" = some (.array schemas))
    (hSchemaUids : callargs.get? "schemaUids" = some (.array schemaUids))
    (hoff0 : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hoff1 : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsizeSigned : I.calldata.size < 2 ^ 255)
    (hschemasBound : schemas.length < 2 ^ 256)
    (hschemasLenMax : schemas.length ≤ solcMaxU64)
    (hlenEq : schemaUids.length = schemas.length)
    (hschemaNorm : ∀ {idx schema}, lookupNth? schemas idx = some schema →
      normalizeRawBoolWord? schema = .ok schema)
    (huidssShape : ∀ {idx value}, lookupNth? schemaUids idx = some value →
      ∃ uids,
        value = .array uids ∧
        uids.length < 2 ^ 256 ∧
        (∀ {j uid}, lookupNth? uids j = some uid →
          normalizeRawBoolWord? uid = .ok uid)) :
    ∀ {fuel : Nat} {a : AttesterMultiRevokeOuterLoopCursor} {L : Store}
      {evm : EVM.State},
      AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids (fuel + 1) a L evm →
      ∀ k C,
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        (attesterMultiRevokeOuterLoopStack a) a.mem a.aw ByteArray.empty a.acc k C →
      (ExecBlock (config v) { contract := contract v, locals := L } evm
          attesterMultiRevokeOuterSourceLoopBody .reverted ∧
        RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I)) ∨
      ∃ a' L' evm' k' C',
        (ExecBlock (config v) { contract := contract v, locals := L } evm
            attesterMultiRevokeOuterSourceLoopBody
            (.ok { contract := contract v, locals := L' } evm') ∨
          ExecBlock (config v) { contract := contract v, locals := L } evm
            attesterMultiRevokeOuterSourceLoopBody
            (.continue { contract := contract v, locals := L' } evm')) ∧
        AttesterMultiRevokeOuterLoopInv cA σ I schemas schemaUids fuel a' L' evm' ∧
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
          (attesterMultiRevokeOuterLoopStack a') a'.mem a'.aw ByteArray.empty a'.acc k' C' := by
  intro fuel a L evm hInv k C hreach
  rcases hInv with
    ⟨i, hschemas, hschemaUids, hschemaLength, hrequests, hi, hvariant, hile,
      hprocessed, hisize, hidx, hidxToNat, houterBase, hschemaLen,
      hschemaLenToNat, hsecondLen, hsecondLenToNat, hsecondPayload,
      hschemaPayload, hret, hselector, hacc, hawGe, hawMul, houterRead,
      houterMemSize, houter64, hbaseGe, houterBeforeBase,
      houterSlotsBeforeBase, hreadLayout, hfreeBudget⟩
  have hreachInit : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
      (attesterMultiRevokeOuterLoopStack a) a.mem a.aw ByteArray.empty (cA, σ) k C := by
    simpa [hacc] using hreach
  have hltSchemas : i < schemas.length := by omega
  have hiMax : i ≤ solcMaxU64 := by omega
  have hltSchemaUids : i < schemaUids.length := by omega
  obtain ⟨schema, hschemaLookup⟩ :=
    attesterLookupNth?_exists (xs := schemas) (i := i) hltSchemas
  obtain ⟨schemaUidValue, hschemaUidLookupValue⟩ :=
    attesterLookupNth?_exists (xs := schemaUids) (i := i) hltSchemaUids
  obtain ⟨uids, hschemaUidValue, huidsBound, huidsNorm⟩ :=
    huidssShape hschemaUidLookupValue
  have hschemaUidLookup : lookupNth? schemaUids i = some (.array uids) := by
    simpa [hschemaUidValue] using hschemaUidLookupValue
  obtain ⟨hidxSecond0, hoffsetOk0, hlenOk0, hpayloadOk0, hlenToNat0,
      hinnerLenMax, hlenZeroOf, hlenNeOf⟩ :=
    attesterMultiRevokeInnerArrayCurrentFacts_of_decode_at
      (v := v) (I := I) (callargs := callargs) (schemaUids := schemaUids)
      (inner := uids) (idx := i) hdec hSchemaUids hschemaUidLookup hoff1 hsizeSigned
  have hidxSchema : UInt256.lt a.idx a.schemaLen = ⟨1⟩ :=
    AttesterMultiRevokeOuterLoopInv.cond_true
      (cA := cA) (σ := σ) (I := I) (schemas := schemas)
      (schemaUids := schemaUids) (fuel := fuel) (a := a) (L := L)
      (evm := evm)
      ⟨i, hschemas, hschemaUids, hschemaLength, hrequests, hi, hvariant, hile,
        hprocessed, hisize, hidx, hidxToNat, houterBase, hschemaLen,
        hschemaLenToNat, hsecondLen, hsecondLenToNat, hsecondPayload,
        hschemaPayload, hret, hselector, hacc, hawGe, hawMul, houterRead,
        houterMemSize, houter64, hbaseGe, houterBeforeBase,
        houterSlotsBeforeBase, hreadLayout, hfreeBudget⟩
  have hidxSecond : UInt256.lt a.idx a.secondLen = ⟨1⟩ := by
    simpa [hidx, hsecondLen] using hidxSecond0
  have hoffsetOk :
      UInt256.slt
        (attesterMultiRevokeInnerArrayOffsetWord I
          (attesterMultiRevokeInnerArrayHeadWord a.secondPayload a.idx))
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size) a.secondPayload)
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩ := by
    simpa [hidx, hsecondPayload] using hoffsetOk0
  have hlenOk :
      UInt256.gt
        (attesterMultiRevokeInnerArrayLengthWord I a.secondPayload
          (attesterMultiRevokeInnerArrayHeadWord a.secondPayload a.idx))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩ := by
    simpa [hidx, hsecondPayload] using hlenOk0
  have hpayloadOk :
      UInt256.sgt
        (attesterMultiRevokeInnerArrayPayloadWord I a.secondPayload
          (attesterMultiRevokeInnerArrayHeadWord a.secondPayload a.idx))
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft
            (attesterMultiRevokeInnerArrayLengthWord I a.secondPayload
              (attesterMultiRevokeInnerArrayHeadWord a.secondPayload a.idx)) ⟨5⟩)) =
      ⟨0⟩ := by
    simpa [hidx, hsecondPayload] using hpayloadOk0
  cases uids with
  | nil =>
      have hbodyRevert :=
        attesterMultiRevokeOuterSourceLoopBody_revert_emptyCurrent
          (imm := v) (evm := evm) (locals := L) (schemaUids := schemaUids)
          (i := i) hschemaUids hi hltSchemaUids (by simpa using hschemaUidLookup)
      have hlenZero :
          attesterMultiRevokeInnerArrayLengthWord I a.secondPayload
            (attesterMultiRevokeInnerArrayHeadWord a.secondPayload a.idx) = ⟨0⟩ := by
        simpa [hidx, hsecondPayload] using hlenZeroOf (by simp)
      exact .inl ⟨hbodyRevert,
        attesterX_multiRevokeOuterIterationLengthZeroRevertsAt
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) v
          (idx := a.idx) (outerBase := a.outerBase) (schemaLen := a.schemaLen)
          (secondLen := a.secondLen) (secondPayload := a.secondPayload)
          (schemaPayload := a.schemaPayload) (ret := a.ret) (selector := a.selector)
          (mem := a.mem) (aw := a.aw) (k := k) (C := C)
          hidxSchema hidxSecond hoffsetOk hlenOk hpayloadOk hlenZero
          (by simpa [attesterMultiRevokeOuterLoopStack] using hreachInit)⟩
  | cons uid rest =>
      have huidsNe : (uid :: rest).length ≠ 0 := by simp
      obtain ⟨L', hbodyOk, hsourceInv'⟩ :=
        attesterMultiRevokeOuterSourceLoop_step_current
          (imm := v) (evm := evm) (schemas := schemas) (schemaUids := schemaUids)
          hschemasBound hlenEq hschemaNorm fuel L
          ⟨i, hschemas, hschemaUids, hschemaLength, hrequests, hi, hvariant, hile⟩
          (by
            intro idx value hlookup hidxVar
            have hidxEq : idx = i := by omega
            subst idx
            have hvalueEq : value = .array (uid :: rest) := by
              have hs : some value = some (.array (uid :: rest)) := by
                rw [← hlookup]
                simpa [hschemaUidValue] using hschemaUidLookupValue
              cases hs
              rfl
            exact ⟨uid :: rest, hvalueEq, huidsNe, huidsBound, huidsNorm⟩)
      have hlenNe :
          attesterMultiRevokeInnerArrayLengthWord I a.secondPayload
            (attesterMultiRevokeInnerArrayHeadWord a.secondPayload a.idx) ≠ ⟨0⟩ := by
        simpa [hidx, hsecondPayload] using hlenNeOf huidsNe
      have hbaseSpare :
          (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat + 32 +
            160 *
              (attesterMultiRevokeInnerArrayLengthWord I a.secondPayload
                (attesterMultiRevokeInnerArrayHeadWord a.secondPayload a.idx)).toNat +
            96 < UInt256.size := by
        have hmul := Nat.mul_le_mul_left 160 hinnerLenMax
        have hchunkLe :
            128 + 160 * (uid :: rest).length ≤
              attesterMultiRevokeOuterLoopBudgetChunk := by
          unfold attesterMultiRevokeOuterLoopBudgetChunk
          omega
        have hbudgetStep :
            128 + 160 * (uid :: rest).length ≤
              attesterMultiRevokeOuterLoopBudgetChunk * (fuel + 1) := by
          have hone : 1 ≤ fuel + 1 := by omega
          have hmulFuel :=
            Nat.mul_le_mul_left attesterMultiRevokeOuterLoopBudgetChunk hone
          omega
        rw [show
          (attesterMultiRevokeInnerArrayLengthWord I a.secondPayload
            (attesterMultiRevokeInnerArrayHeadWord a.secondPayload a.idx)).toNat =
              (uid :: rest).length by simpa [hidx, hsecondPayload] using hlenToNat0]
        omega
      obtain ⟨b', s', k', C', _hbrem, _hInit, _hsidx, hCopy, hpresCopy, rd335⟩ :=
        attesterX_multiRevokeOuterIterationToOuterLoopWithReadInvariantAt
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) v
          (idx := a.idx) (outerBase := a.outerBase) (schemaLen := a.schemaLen)
          (secondLen := a.secondLen) (secondPayload := a.secondPayload)
          (schemaPayload := a.schemaPayload) (ret := a.ret) (selector := a.selector)
          (mem := a.mem) (aw := a.aw) (k := k) (C := C)
          hidxSchema hidxSecond hoffsetOk hlenOk hpayloadOk hlenNe
          hawGe hawMul houterRead houterMemSize houter64 hbaseGe houterBeforeBase
          hbaseSpare
          (by simpa [attesterMultiRevokeOuterLoopStack] using hreachInit)
      let aNext : AttesterMultiRevokeOuterLoopCursor :=
        { a with
          idx := attesterMultiRevokePostCopyNextIdx a.idx,
          mem := attesterMultiRevokePostCopyOuterMem
            (attesterInnerArrayAllocFreeWord a.mem a.aw) a.outerBase I a.schemaPayload
            a.idx s'.mem s'.aw,
          aw := attesterMultiRevokePostCopyOuterAw
            (attesterInnerArrayAllocFreeWord a.mem a.aw) a.outerBase I a.schemaPayload
            a.idx s'.mem s'.aw }
      rcases hsourceInv' with
        ⟨i', hschemas', hschemaUids', hschemaLength', hrequests', hi',
          hvariant', hile'⟩
      have hi' : i' = i + 1 := by omega
      subst i'
      have hschemasSize : schemas.length < UInt256.size := by
        rw [← hschemaLenToNat]
        exact a.schemaLen.val.isLt
      have hiSuccSize : i + 1 < UInt256.size := by
        omega
      have hnextIdx :
          attesterMultiRevokePostCopyNextIdx a.idx = UInt256.ofNat (i + 1) := by
        rw [attesterMultiRevokePostCopyNextIdx, hidx]
        exact u256_one_add_ofNat i
      have hnextIdxToNat :
          (attesterMultiRevokePostCopyNextIdx a.idx).toNat = i + 1 := by
        rw [hnextIdx]
        exact ulit_toNat' (i + 1) hiSuccSize
      have hslotBound :
          a.outerBase.toNat + 32 + 32 * a.idx.toNat + 63 < UInt256.size := by
        have hidxLeMax : a.idx.toNat ≤ solcMaxU64 := by
          rw [hidxToNat]
          omega
        have hnextLeMax :
            (attesterMultiRevokePostCopyNextIdx a.idx).toNat ≤ solcMaxU64 := by
          rw [hnextIdxToNat]
          omega
        have hmul := Nat.mul_le_mul_left 32 hidxLeMax
        have hmulNext := Nat.mul_le_mul_left 32 hnextLeMax
        have houterToNat : a.outerBase.toNat = 128 := by
          rw [houterBase]
          rfl
        rw [houterToNat]
        norm_num [solcMaxU64, UInt256.size] at hmul hmulNext ⊢
        omega
      have hpostFacts :=
        attesterMultiRevokePostCopyOuter_cursorFacts_from_copyInvAt
          (I := I) (base := attesterInnerArrayAllocFreeWord a.mem a.aw)
          (len := attesterMultiRevokeInnerArrayLengthWord I a.secondPayload
            (attesterMultiRevokeInnerArrayHeadWord a.secondPayload a.idx))
          (payload := attesterMultiRevokeInnerArrayPayloadWord I a.secondPayload
            (attesterMultiRevokeInnerArrayHeadWord a.secondPayload a.idx))
          (outerBase := a.outerBase) (schemaLen := a.schemaLen)
          (schemaPayload := a.schemaPayload) (idx := a.idx) (s := s')
          hCopy hslotBound
      rcases hpostFacts with
        ⟨houterPost, hawGePost, hawMulPost, _hfreeToNatPost,
          hbaseGePost, houterBeforeBasePost⟩
      have hpostFreeExact :=
        attesterMultiRevokePostCopyOuter_freeWordExact_from_copyInvAt
          (I := I) (base := attesterInnerArrayAllocFreeWord a.mem a.aw)
          (len := attesterMultiRevokeInnerArrayLengthWord I a.secondPayload
            (attesterMultiRevokeInnerArrayHeadWord a.secondPayload a.idx))
          (payload := attesterMultiRevokeInnerArrayPayloadWord I a.secondPayload
            (attesterMultiRevokeInnerArrayHeadWord a.secondPayload a.idx))
          (outerBase := a.outerBase) (schemaLen := a.schemaLen)
          (schemaPayload := a.schemaPayload) (idx := a.idx) (s := s')
          hCopy hslotBound
      have hcurrentSlotToNat :
          (attesterMultiRevokePostCopyOuterSlotWord a.outerBase a.idx).toNat =
            a.outerBase.toNat + 32 + 32 * a.idx.toNat := by
        exact attesterMultiRevokePostCopyOuterSlotWord_toNat (by omega)
      have hcurrentSlotBeforeBase :
          (attesterMultiRevokePostCopyOuterSlotWord a.outerBase a.idx).toNat + 32 ≤
            (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat := by
        rw [hcurrentSlotToNat, hidxToNat]
        have hmul : 32 * (i + 1) ≤ 32 * schemas.length :=
          Nat.mul_le_mul_left 32 (by omega)
        omega
      have hcurrentRequestReadLayoutBounded :
          AttesterMultiRevokeRequestReadLayoutAtBounded schemas schemaUids
            aNext.mem a.outerBase
            (a.outerBase.toNat + 32 + 32 * schemas.length)
            (attesterInnerArrayAllocFreeWord aNext.mem aNext.aw).toNat i := by
        dsimp [aNext]
        exact
          attesterMultiRevokePostCopyOuter_currentRequestReadLayout_from_copyInvAt
            (I := I) (callargs := callargs) (schemas := schemas)
            (schemaUids := schemaUids) (uids := uid :: rest) (i := i)
            (schema := schema)
            (base := attesterInnerArrayAllocFreeWord a.mem a.aw)
            (len :=
              attesterMultiRevokeInnerArrayLengthWord I a.secondPayload
                (attesterMultiRevokeInnerArrayHeadWord a.secondPayload a.idx))
            (payload :=
              attesterMultiRevokeInnerArrayPayloadWord I a.secondPayload
                (attesterMultiRevokeInnerArrayHeadWord a.secondPayload a.idx))
            (outerBase := a.outerBase) (schemaLen := a.schemaLen)
            (schemaPayload := a.schemaPayload) (idx := a.idx) (s := s') v
            hdec hSchemas hschemaLookup hschemaUidLookup hoff0 hiMax hidx hschemaPayload
            (by
              simpa [hidx, hsecondPayload] using hlenToNat0)
            (by
              intro j uidVal hlookupUid
              simpa [hidx, hsecondPayload] using
                (attesterDecode_multiRevoke_uid_word_at_copy_payload
                  (v := v) (I := I) (callargs := callargs)
                  (schemaUids := schemaUids) (uids := uid :: rest)
                  (idx := i) (j := j) (uid := uidVal)
                  hdec hSchemaUids hschemaUidLookup hlookupUid hoff1 hsizeSigned))
            hCopy hcurrentSlotBeforeBase
            houterSlotsBeforeBase
            (by rw [hpostFreeExact])
            hslotBound
      have hcurrentRequestReadLayout :
          AttesterMultiRevokeRequestReadLayoutAt schemas schemaUids aNext.mem a.outerBase i :=
        AttesterMultiRevokeRequestReadLayoutAtBounded.to_readLayout
          hcurrentRequestReadLayoutBounded
      have hfreeBudgetNext :
          (attesterInnerArrayAllocFreeWord aNext.mem aNext.aw).toNat +
              attesterMultiRevokeEncoderOutputBudget schemas.length + 128 +
            attesterMultiRevokeOuterLoopBudgetChunk * fuel < UInt256.size := by
        dsimp [aNext]
        rw [hpostFreeExact]
        rw [show
          (attesterMultiRevokeInnerArrayLengthWord I a.secondPayload
            (attesterMultiRevokeInnerArrayHeadWord a.secondPayload a.idx)).toNat =
              (uid :: rest).length by simpa [hidx, hsecondPayload] using hlenToNat0]
        have hstep :
            96 + 160 * (uid :: rest).length +
                attesterMultiRevokeEncoderOutputBudget schemas.length + 128 +
              attesterMultiRevokeOuterLoopBudgetChunk * fuel ≤
              attesterMultiRevokeEncoderOutputBudget schemas.length + 128 +
              attesterMultiRevokeOuterLoopBudgetChunk * (fuel + 1) := by
          rw [Nat.mul_succ]
          have hmulLen := Nat.mul_le_mul_left 160 hinnerLenMax
          unfold attesterMultiRevokeOuterLoopBudgetChunk
          omega
        omega
      have houterSlotsBeforeBaseNext :
          aNext.outerBase.toNat + 32 + 32 * schemas.length ≤
            (attesterInnerArrayAllocFreeWord aNext.mem aNext.aw).toNat := by
        dsimp [aNext]
        rw [hpostFreeExact]
        exact le_trans houterSlotsBeforeBase (by omega)
      have hprocessedNext :
          ∀ {idx value}, idx < i + 1 → lookupNth? schemaUids idx = some value →
            ∃ uids,
            value = .array uids ∧
            uids.length ≠ 0 ∧
            uids.length ≤ solcMaxU64 ∧
            uids.length < 2 ^ 256 ∧
            (∀ {j uid}, lookupNth? uids j = some uid →
              normalizeRawBoolWord? uid = .ok uid) := by
        intro idx value hidxLt hlookup
        by_cases hlt : idx < i
        · exact hprocessed hlt hlookup
        · have hidxEq : idx = i := by omega
          subst idx
          have hvalueEq : value = .array (uid :: rest) := by
            have hs : some value = some (.array (uid :: rest)) := by
              rw [← hlookup]
              simpa [hschemaUidValue] using hschemaUidLookupValue
            cases hs
            rfl
          exact ⟨uid :: rest, hvalueEq, huidsNe, hinnerLenMax, huidsBound, huidsNorm⟩
      let currentSlot := attesterMultiRevokePostCopyOuterSlotWord a.outerBase a.idx
      have hcontentLo64 :
          64 + 32 ≤ a.outerBase.toNat + 32 + 32 * schemas.length := by
        omega
      have hcurrentSlotBeforeContent :
          currentSlot.toNat + 32 ≤ a.outerBase.toNat + 32 + 32 * schemas.length := by
        dsimp [currentSlot]
        rw [hcurrentSlotToNat, hidxToNat]
        omega
      have hboundOldLeNext :
          (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat ≤
            (attesterInnerArrayAllocFreeWord aNext.mem aNext.aw).toNat := by
        dsimp [aNext]
        rw [hpostFreeExact]
        omega
      have hpostDataToNat :
          (attesterMultiRevokePostCopyDataOffsetWord s'.mem s'.aw).toNat =
            (attesterMultiRevokePostCopyFreeWord s'.mem s'.aw).toNat + 32 := by
        have hfree32 :
            (attesterMultiRevokePostCopyFreeWord s'.mem s'.aw).toNat + 32 <
              UInt256.size := by
          have hspare :
              (attesterMultiRevokePostCopyFreeWord s'.mem s'.aw).toNat + 96 <
                UInt256.size := by
            simpa [attesterMultiRevokePostCopyFreeWord,
              attesterMultiRevokeInnerArrayCopyFreeWord] using hCopy.freeSpare
          omega
        unfold attesterMultiRevokePostCopyDataOffsetWord
        exact uadd_lit32_toNat (attesterMultiRevokePostCopyFreeWord s'.mem s'.aw)
          hfree32
      have hpreserveToNext :
          AttesterReadPreservedBeforeExcept a.mem aNext.mem
            (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat currentSlot.toNat := by
        intro read word hmem hread hread64 hbefore hdisj
        rcases hpresCopy hmem hread hread64 hbefore with ⟨hmemCopy, hreadCopy⟩
        constructor
        · dsimp [aNext]
          exact attesterMultiRevokePostCopyOuterMem_size_ge
            (I := I) (base := attesterInnerArrayAllocFreeWord a.mem a.aw)
            (outerBase := a.outerBase) (schemaPayload := a.schemaPayload)
            (idx := a.idx) (mem := s'.mem) (aw := s'.aw) hmemCopy
        · dsimp [aNext]
          exact attesterMultiRevokePostCopyOuterMem_read_preserved_before_free
            (I := I) (base := attesterInnerArrayAllocFreeWord a.mem a.aw)
            (outerBase := a.outerBase) (schemaPayload := a.schemaPayload)
            (idx := a.idx) (mem := s'.mem) (aw := s'.aw)
            hmemCopy hreadCopy hread64
            (by
              have hfreeGe := hCopy.freeGe
              change
                (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat + 32 ≤
                  (attesterMultiRevokeInnerArrayCopyFreeWord s'.mem s'.aw).toNat
                at hfreeGe
              simpa [attesterMultiRevokePostCopyFreeWord,
                attesterMultiRevokeInnerArrayCopyFreeWord] using
                  (le_trans hbefore (by omega : (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat ≤
                    (attesterMultiRevokeInnerArrayCopyFreeWord s'.mem s'.aw).toNat)))
            hpostDataToNat
            (by simpa [currentSlot] using hdisj)
      have hreadLayoutNext :
          AttesterMultiRevokeRequestsReadLayoutBounded schemas schemaUids (i + 1)
            aNext.mem aNext.outerBase
            (aNext.outerBase.toNat + 32 + 32 * schemas.length)
            (attesterInnerArrayAllocFreeWord aNext.mem aNext.aw).toNat := by
        intro idxOld hidxOld
        by_cases hltOld : idxOld < i
        · have hidxOldSize : idxOld < UInt256.size := by omega
          have hidxOldToNat : (UInt256.ofNat idxOld).toNat = idxOld :=
            ulit_toNat' idxOld hidxOldSize
          have hslotOldToNat :
              (attesterMultiRevokePostCopyOuterSlotWord a.outerBase
                (UInt256.ofNat idxOld)).toNat =
                a.outerBase.toNat + 32 + 32 * idxOld := by
            rw [attesterMultiRevokePostCopyOuterSlotWord_toNat]
            · rw [hidxOldToNat]
            · rw [hidxOldToNat]
              have hidxOldMax : idxOld ≤ solcMaxU64 := by omega
              have hmul : 32 * idxOld ≤ 32 * solcMaxU64 :=
                Nat.mul_le_mul_left 32 hidxOldMax
              have houterToNat : a.outerBase.toNat = 128 := by
                rw [houterBase]
                rfl
              rw [houterToNat]
              norm_num [solcMaxU64, UInt256.size] at hmul ⊢
              omega
          have hownSlotBefore :
              (attesterMultiRevokePostCopyOuterSlotWord a.outerBase
                (UInt256.ofNat idxOld)).toNat + 32 ≤ currentSlot.toNat := by
            dsimp [currentSlot]
            rw [hslotOldToNat, hcurrentSlotToNat, hidxToNat]
            omega
          have hOld :
              AttesterMultiRevokeRequestReadLayoutAtBounded schemas schemaUids
                a.mem a.outerBase
                (a.outerBase.toNat + 32 + 32 * schemas.length)
                (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat idxOld :=
            hreadLayout hltOld
          have hpreserved :
              AttesterMultiRevokeRequestReadLayoutAtBounded schemas schemaUids
                aNext.mem a.outerBase
                (a.outerBase.toNat + 32 + 32 * schemas.length)
                (attesterInnerArrayAllocFreeWord aNext.mem aNext.aw).toNat idxOld :=
            AttesterMultiRevokeRequestReadLayoutAtBounded.preserve_except
              (schemas := schemas) (schemaUids := schemaUids)
              (mem := a.mem) (mem' := aNext.mem) (outerBase := a.outerBase)
              (contentLo := a.outerBase.toNat + 32 + 32 * schemas.length)
              (bound := (attesterInnerArrayAllocFreeWord a.mem a.aw).toNat)
              (bound' := (attesterInnerArrayAllocFreeWord aNext.mem aNext.aw).toNat)
              (protectedSlot := currentSlot.toNat) (idx := idxOld)
              hcontentLo64 hboundOldLeNext hownSlotBefore
              hcurrentSlotBeforeContent hpreserveToNext hOld
          simpa [aNext] using hpreserved
        · have hidxEq : idxOld = i := by omega
          subst idxOld
          simpa [aNext] using hcurrentRequestReadLayoutBounded
      exact .inr ⟨aNext, L', evm, k', C', .inl hbodyOk,
        ⟨i + 1, hschemas', hschemaUids', hschemaLength', hrequests', hi',
          hvariant', hile', hprocessedNext, hiSuccSize,
          by simpa [aNext] using hnextIdx,
          by simpa [aNext] using hnextIdxToNat,
          by simpa [aNext] using houterBase,
          by simpa [aNext] using hschemaLen,
          by simpa [aNext] using hschemaLenToNat,
          by simpa [aNext] using hsecondLen,
          by simpa [aNext] using hsecondLenToNat,
          by simpa [aNext] using hsecondPayload,
          by simpa [aNext] using hschemaPayload,
          by simpa [aNext] using hret,
          by simpa [aNext] using hselector,
          by simpa [aNext] using hacc,
          by simpa [aNext] using hawGePost,
          by simpa [aNext] using hawMulPost,
          by simpa [aNext] using houterPost.1,
          by simpa [aNext] using houterPost.2,
          by simpa [aNext] using houter64,
          by simpa [aNext] using hbaseGePost,
          by simpa [aNext] using houterBeforeBasePost,
          houterSlotsBeforeBaseNext,
          hreadLayoutNext,
          hfreeBudgetNext⟩,
        by
          simpa [aNext, attesterMultiRevokeOuterLoopStack, hacc] using rd335⟩

theorem attesterX_multiRevokeFirstInnerCopyToOuterLoopWithReadInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (hidxSchema : UInt256.lt (⟨0⟩ : UInt256) (attesterFirstArrayLengthWord I) = ⟨1⟩)
    (hprogress :
      ∃ (a' : AttesterMultiOuterArrayInitState),
      ∃ (b' : AttesterMultiRevokeInnerArrayInitState),
      ∃ (c' : AttesterMultiRevokeInnerArrayCopyState),
      ∃ k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
        attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
        b'.remaining = (⟨1⟩ : UInt256) ∧
        attesterMultiRevokeInnerInitReadInv I a' 0 b' ∧
        c'.idx = attesterFirstInnerArrayLengthWord I ∧
        attesterMultiRevokeInnerCopyReadInv I a' b' 0 c' ∧
        RD (patchedRuntime v) I g
          (initState cA gh bl σ σ₀ g A I) (⟨608⟩ : UInt256)
          (attesterMultiRevokeInnerArrayCopyStack
            (attesterInnerArrayAllocFreeWord
              (attesterMultiOuterArrayInitFinalMem a')
              (attesterMultiOuterArrayInitFinalAw a'))
            (attesterFirstInnerArrayLengthWord I)
            (attesterFirstInnerArrayStartWord I + ⟨32⟩)
            [⟨0⟩, ⟨128⟩,
              attesterFirstArrayLengthWord I,
              attesterSecondArrayLengthWord I,
              attesterSecondArrayPayloadStartWord I,
              attesterFirstArrayLengthWord I,
              (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
              ⟨97⟩, solcSelectorWord I]
            c')
          c'.mem c'.aw ByteArray.empty (cA, σ) k C) :
    ∃ (a' : AttesterMultiOuterArrayInitState),
    ∃ (b' : AttesterMultiRevokeInnerArrayInitState),
    ∃ (c' : AttesterMultiRevokeInnerArrayCopyState),
    ∃ k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      attesterMultiRevokeOuterInitFreeInv I 0 a' ∧
      b'.remaining = (⟨1⟩ : UInt256) ∧
      attesterMultiRevokeInnerInitReadInv I a' 0 b' ∧
      c'.idx = attesterFirstInnerArrayLengthWord I ∧
      attesterMultiRevokeInnerCopyReadInv I a' b' 0 c' ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        [attesterMultiRevokePostCopyNextIdx (⟨0⟩ : UInt256), ⟨128⟩,
          attesterFirstArrayLengthWord I,
          attesterSecondArrayLengthWord I,
          attesterSecondArrayPayloadStartWord I,
          attesterFirstArrayLengthWord I,
          (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
          ⟨97⟩, solcSelectorWord I]
        (attesterMultiRevokePostCopyOuterMem
          (attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a'))
          ⟨128⟩ I ((UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩)
          (⟨0⟩ : UInt256) c'.mem c'.aw)
        (attesterMultiRevokePostCopyOuterAw
          (attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a'))
          ⟨128⟩ I ((UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩)
          (⟨0⟩ : UInt256) c'.mem c'.aw)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨a', b', c', k0, C0, harem, hOuter, hbrem, hInit, hcidx, hCopy, rd0⟩ :=
    hprogress
  let base :=
    attesterInnerArrayAllocFreeWord
      (attesterMultiOuterArrayInitFinalMem a')
      (attesterMultiOuterArrayInitFinalAw a')
  let schemaPayload := (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩
  have hmloadOuter :
      attesterMloadWord
        (attesterMultiRevokePostCopyDataMem base I schemaPayload (⟨0⟩ : UInt256)
          c'.mem c'.aw)
        (attesterMultiRevokePostCopyDataAw base I schemaPayload (⟨0⟩ : UInt256)
          c'.mem c'.aw)
        (⟨128⟩ : UInt256) =
          attesterFirstArrayLengthWord I := by
    exact attesterMultiRevokePostCopyDataMem_mloadOuter
      (base := base) (outerBase := (⟨128⟩ : UInt256))
      (len := attesterFirstArrayLengthWord I) (schemaPayload := schemaPayload)
      (idx := (⟨0⟩ : UInt256)) (mem := c'.mem) (aw := c'.aw)
      (by simpa using hCopy.outerMemSize)
      (by simpa using hCopy.outerRead)
      (by simpa using hCopy.awMul)
      (by decide)
      (by simpa [base] using hCopy.base160)
      (by
        change base.toNat + 32 ≤
          (attesterMultiRevokeInnerArrayCopyFreeWord c'.mem c'.aw).toNat
        simpa [base] using hCopy.freeGe)
      (by
        change
          (attesterMultiRevokeInnerArrayCopyFreeWord c'.mem c'.aw).toNat + 96 <
            UInt256.size
        have hspare := hCopy.freeSpare
        simpa using hspare)
  have hidxOuter :
      UInt256.lt (⟨0⟩ : UInt256)
        (attesterMloadWord
          (attesterMultiRevokePostCopyDataMem base I schemaPayload (⟨0⟩ : UInt256)
            c'.mem c'.aw)
          (attesterMultiRevokePostCopyDataAw base I schemaPayload (⟨0⟩ : UInt256)
            c'.mem c'.aw)
          (⟨128⟩ : UInt256)) = ⟨1⟩ := by
    rw [hmloadOuter]
    exact hidxSchema
  obtain ⟨k1, C1, rd1⟩ :=
    attesterX_multiRevokePostInnerCopyToOuterLoop
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (innerIdx := c'.idx) (base := base)
      (innerLen := attesterFirstInnerArrayLengthWord I)
      (payload := attesterFirstInnerArrayStartWord I + ⟨32⟩)
      (idx := (⟨0⟩ : UInt256)) (outerBase := (⟨128⟩ : UInt256))
      (schemaLen := attesterFirstArrayLengthWord I)
      (secondLen := attesterSecondArrayLengthWord I)
      (secondPayload := attesterSecondArrayPayloadStartWord I)
      (schemaPayload := schemaPayload) (ret := ⟨97⟩)
      (selector := solcSelectorWord I) (mem := c'.mem) (aw := c'.aw)
      (k := k0) (C := C0)
      hidxSchema hidxOuter
      (by
        simpa [base, schemaPayload, hcidx,
          attesterMultiRevokeInnerArrayCopyStack] using rd0)
  exact ⟨a', b', c', k1, C1, harem, hOuter, hbrem, hInit, hcidx, hCopy, by
    simpa [base, schemaPayload] using rd1⟩

end Benchmarks.EAS.Attester
