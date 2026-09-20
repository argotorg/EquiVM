import Solidity.Semantics.Ops

/-!
# EVM bridges for external calls and creation

Mirrors `Solm.callViaEVM` / `delegateCallViaEVM` / `newViaEVM`, but deterministic given the
oracle (gas and the non-log substate come from `Oracle`, advancing `tick`) and with the input log
series pinned to the current one, so the log series threads through sub-calls exactly as in the
EVM (a failed callee leaves it unchanged, since `Θ` returns its input substate).  The static flag
of the current context is inherited by every callee (`STATICCALL` and view/pure callees clear it).
-/

namespace Solidity

/-- The substate handed to a sub-call: the oracle's non-log fields with the current logs. -/
def subInput (o : Oracle) (m : Machine) : Ethereum.Substate :=
  { o.substateIn m.tick with logSeries := m.evm.substate.logSeries }

def afterCall (m : Machine) (cA' : Batteries.RBSet Ethereum.AccountAddress compare)
    (σ' : Ethereum.AccountMap) (A' : Ethereum.Substate) : Machine :=
  { m with evm := { m.evm with accountMap := σ', substate := A', createdAccounts := cA' }, tick := m.tick + 1 }

/-- Gas handed to a callee (EIP-150): the requested amount (`none` = all) capped by the cap `o.callGas`,
    plus the 2300 stipend when value is transferred. -/
def calleeGas (o : Oracle) (m : Machine) (request : Option Nat) (value : Nat) : Ethereum.UInt256 :=
  let cap := o.callGas m.tick
  let capped := match request with
    | some r => if Ethereum.UInt256.ofNat r ≤ cap then Ethereum.UInt256.ofNat r else cap
    | none => cap
  if value = 0 then capped else capped + ⟨2300⟩

/-- `CALL`/`STATICCALL` of `calldata` to `target` with `value` wei and `gas`: `(success, machine, returndata)`. -/
inductive callViaEVM (o : Oracle) (m : Machine) (target : EVM.Address) (value : Nat)
    (calldata : EVM.Bytes) (perm : Bool) (gas : Ethereum.UInt256) : (Bool × Machine × EVM.Bytes) → Prop where
  | callMade :
      valueWord = EVM.Word.ofNat value →
      valueWord ≤ (m.evm.accountMap.find? m.this |>.getD default).balance →
      m.evm.executionEnv.depth ≠ 1024 →
      (cA', σ', g', A', z, out)
        = Ethereum.EVM.Θ
            m.evm.executionEnv.blobVersionedHashes
            m.evm.createdAccounts
            m.evm.genesisBlockHeader
            m.evm.blocks
            m.evm.accountMap
            m.evm.σ₀
            (subInput o m)
            m.this
            m.evm.executionEnv.sender
            target
            (Ethereum.toExecute m.evm.accountMap target)
            gas
            (.ofNat m.evm.executionEnv.gasPrice)
            valueWord
            valueWord
            calldata
            (m.evm.executionEnv.depth + 1)
            m.evm.executionEnv.header
            perm →
      callViaEVM o m target value calldata perm gas (z, afterCall m cA' σ' A', out)
  | callNotMade :
      valueWord = EVM.Word.ofNat value →
      (valueWord > (m.evm.accountMap.find? m.this |>.getD default).balance ∨
        m.evm.executionEnv.depth = 1024) →
      callViaEVM o m target value calldata perm gas
        (false, { m with evm := m.evm.addAccessedAccount target, tick := m.tick + 1 }, ByteArray.empty)

/-- `DELEGATECALL`: callee code runs in this contract's context. -/
inductive delegateCallViaEVM (o : Oracle) (m : Machine) (target : EVM.Address) (calldata : EVM.Bytes)
    (gas : Ethereum.UInt256) : (Bool × Machine × EVM.Bytes) → Prop where
  | callMade :
      m.evm.executionEnv.depth ≠ 1024 →
      (cA', σ', g', A', z, out)
        = Ethereum.EVM.Θ
            m.evm.executionEnv.blobVersionedHashes
            m.evm.createdAccounts
            m.evm.genesisBlockHeader
            m.evm.blocks
            m.evm.accountMap
            m.evm.σ₀
            (subInput o m)
            m.evm.executionEnv.source
            m.evm.executionEnv.sender
            m.this
            (Ethereum.toExecute m.evm.accountMap target)
            gas
            (.ofNat m.evm.executionEnv.gasPrice)
            ⟨0⟩
            m.evm.executionEnv.weiValue
            calldata
            (m.evm.executionEnv.depth + 1)
            m.evm.executionEnv.header
            m.evm.executionEnv.perm →
      delegateCallViaEVM o m target calldata gas (z, afterCall m cA' σ' A', out)
  | callNotMade :
      m.evm.executionEnv.depth = 1024 →
      delegateCallViaEVM o m target calldata gas
        (false, { m with evm := m.evm.addAccessedAccount target, tick := m.tick + 1 }, ByteArray.empty)

/-- Contract creation (`new`) via `Λ`: `(address, machine, success, returndata)`. -/
inductive newViaEVM (cfg : Config) (o : Oracle) (m : Machine) (name : Ident) (value : Nat)
    (args : List ABI.ABIValue) (salt : Option ByteArray) : (EVM.Address × Machine × Bool × EVM.Bytes) → Prop where
  | created :
      cfg.creationCode name args = .some initCode →
      valueWord = EVM.Word.ofNat value →
      creator = (m.evm.accountMap.find? m.this |>.getD default) →
      valueWord ≤ creator.balance →
      m.evm.executionEnv.depth ≠ 1024 →
      creator.nonce.toNat < 2 ^ 64 - 1 →
      initCode.size ≤ 49152 →
      σStar = m.evm.accountMap.insert m.this { creator with nonce := creator.nonce + ⟨1⟩ } →
      (addr, cA', σ', g', A', z, out)
        = Ethereum.EVM.Lambda
            m.evm.executionEnv.blobVersionedHashes
            m.evm.createdAccounts
            m.evm.genesisBlockHeader
            m.evm.blocks
            σStar
            m.evm.σ₀
            (subInput o m)
            m.this
            m.evm.executionEnv.sender
            (o.callGas m.tick)
            (.ofNat m.evm.executionEnv.gasPrice)
            valueWord
            initCode
            (m.evm.executionEnv.depth + 1)
            salt
            m.evm.executionEnv.header
            m.evm.executionEnv.perm →
      newViaEVM cfg o m name value args salt (addr, afterCall m cA' σ' A', z, out)
  | notCreated :
      cfg.creationCode name args = .some initCode →
      valueWord = EVM.Word.ofNat value →
      creator = (m.evm.accountMap.find? m.this |>.getD default) →
      (valueWord > creator.balance ∨ m.evm.executionEnv.depth = 1024 ∨
        creator.nonce.toNat ≥ 2 ^ 64 - 1 ∨ initCode.size > 49152) →
      newViaEVM cfg o m name value args salt (EVM.address 0, { m with tick := m.tick + 1 }, false, ByteArray.empty)

end Solidity
