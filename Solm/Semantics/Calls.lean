import Solm.Semantics.Types

/-! EVM bridges for external calls and contract creation (`Θ`/`Λ`). -/

namespace Solm

open ABI

def externalValueToWord? : Value -> Option EVM.Word
  | .int i => some (EVM.wordOfInt i)
  | .bool b => some b.toUInt256
  | .address a => some (EVM.word a)
  | .unit => some ⟨0⟩
  | _ => none

def wordsOfValues? (values : List Value) : Option (List EVM.Word) :=
  match values with
  | [] => some []
  | value :: rest => do
      let word <- externalValueToWord? value
      let words <- wordsOfValues? rest
      some (word :: words)

def defaultEncodeCall? (_name : Ident) (args : List Value) : Option EVM.Bytes := do
  let words <- wordsOfValues? args
  some (words.foldl (fun bytes word => bytes ++ (Ethereum.UInt256.toByteArray word)) ByteArray.empty)

def defaultDecodeReturn? (_name : Ident) (bytes : EVM.Bytes) : Option (List Value) :=
  -- Default typed external calls expect one `uint256` return word.  The ABI decoder models solc's
  -- generated signed-size guard, so under-length and huge return data both decode to `none`.
  ABI.decodeReturnValues? [.elem (.int (.uint ⟨256, by decide⟩))] bytes

def defaultExternalCallABI : ExternalCallABI :=
  { encode? := defaultEncodeCall?, decode? := defaultDecodeReturn? }

/-- A raw message call to `target` with the given `value` and `calldata`, bridged directly to the
    EVM `Θ`.  No ABI encoding — calldata is supplied verbatim — and the boolean result is the raw
    call success flag.  The final optional parameter is the callee permission bit passed to `Θ`;
    ordinary `CALL` uses the default `true`, while `STATICCALL` uses `false`.  Both the low-level
    `.call` and (via `typedCallViaEVM`) typed external calls are built on this. -/
inductive callViaEVM (evm : EVM.State) (target : EVM.Address)
    (value : ℤ) (calldata : EVM.Bytes) :
    (Bool × EVM.State × EVM.Bytes) → (perm : Bool := true) → Prop where
  | callMade :
      valueWord = EVM.wordOfInt value
      → (∃ (callGas : Ethereum.UInt256) (A_in : Ethereum.Substate),
        -- The external call bridges directly to the EVM `Θ`.  Solm tracks neither gas nor the
        -- substate, so — exactly as `callGas` is already existential — the *entire* input
        -- substate `A_in` is existentially quantified: the call "behaves as `Θ` would for some
        -- gas and substate".  (The result substate `A'` is discarded; `execResultsEquiv` ignores
        -- it.)  `g'` is the (discarded) returned gas; named so it is a plain implicit.
          (cA', σ', g', A', z, o)
            = Ethereum.EVM.Θ
            evm.executionEnv.blobVersionedHashes
            evm.createdAccounts
            evm.genesisBlockHeader
            evm.blocks
            evm.accountMap
            evm.σ₀
            A_in
            evm.executionEnv.codeOwner  -- sender (msg.sender): `this`, as a CALL does
            evm.executionEnv.sender      -- original transactor (tx.origin)
            target
            (Ethereum.toExecute evm.accountMap target) -- this is the code
            callGas
            (.ofNat evm.executionEnv.gasPrice)
            valueWord -- actual value sent
            valueWord -- value reported to queries
            calldata
            (evm.executionEnv.depth + 1)
            evm.executionEnv.header
            perm -- permission to modify state;
                 -- true for call/delegatecall/callcode, false for staticcall
        )

      → evm' = { evm with accountMap := σ', substate := A', createdAccounts := cA' }

      → valueWord ≤ (evm.accountMap.find? evm.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))
      → evm.executionEnv.depth ≠ 1024
      → callViaEVM evm target value calldata (z, evm', o) perm

  | callNotMade :
      A' = ((evm.addAccessedAccount target) |>.substate )
      → evm' = { evm with substate := A' }
      → (¬ (EVM.wordOfInt value ≤ (evm.accountMap.find? evm.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))
         ∧ evm.executionEnv.depth ≠ 1024))
      → callViaEVM evm target value calldata (false, evm', ByteArray.empty) perm

/-- A raw `DELEGATECALL` to `target` with verbatim `calldata`, bridged directly to EVM `Θ`.
    Delegatecall executes the target's code in the current contract's context: `address(this)` and
    storage owner stay `codeOwner`, `msg.sender` and `msg.value` are preserved, no ETH is
    transferred, and the current static permission bit is preserved. -/
inductive delegateCallViaEVM (evm : EVM.State) (target : EVM.Address)
    (calldata : EVM.Bytes) : (Bool × EVM.State × EVM.Bytes) → Prop where
  | callMade :
      (∃ (callGas : Ethereum.UInt256) (A_in : Ethereum.Substate),
          (cA', σ', g', A', z, o)
            = Ethereum.EVM.Θ
            evm.executionEnv.blobVersionedHashes
            evm.createdAccounts
            evm.genesisBlockHeader
            evm.blocks
            evm.accountMap
            evm.σ₀
            A_in
            evm.executionEnv.source
            evm.executionEnv.sender
            evm.executionEnv.codeOwner
            (Ethereum.toExecute evm.accountMap target)
            callGas
            (.ofNat evm.executionEnv.gasPrice)
            (⟨0⟩ : EVM.Word)
            evm.executionEnv.weiValue
            calldata
            (evm.executionEnv.depth + 1)
            evm.executionEnv.header
            evm.executionEnv.perm)
      → evm' = { evm with accountMap := σ', substate := A', createdAccounts := cA' }
      → evm.executionEnv.depth ≠ 1024
      → delegateCallViaEVM evm target calldata (z, evm', o)
  | callNotMade :
      A' = ((evm.addAccessedAccount target) |>.substate)
      → evm' = { evm with substate := A' }
      → evm.executionEnv.depth = 1024
      → delegateCallViaEVM evm target calldata (false, evm', ByteArray.empty)

/-- A typed external call: ABI-encode `name`/`args` into calldata, then make a raw `callViaEVM`.
    This is the call form `externalCall` uses.  The return *decode* (and its failure) stays in the
    `ExecStmt` rules over the raw output bytes `o`, so decode-failure handling is unchanged. -/
def typedCallViaEVM (cfg : Config) (evm : EVM.State) (target : EVM.Address)
    (name : Ident) (value : ℤ) (args : List Value)
    (result : Bool × EVM.State × EVM.Bytes) (perm : Bool := true) : Prop :=
  ∃ calldata, cfg.externalABI.encode? name args = some calldata
            ∧ callViaEVM evm target value calldata result perm

/-- Preconditions under which a `new` (the `CREATE` opcode) actually runs the init code,
    mirroring the guards the opcode checks before calling `Lambda`. -/
def newCanCreate (evm : EVM.State) (value : ℤ) (initCode : EVM.Bytes) : Prop :=
  let creator := evm.accountMap.find? evm.executionEnv.codeOwner |>.getD default
  EVM.wordOfInt value ≤ creator.balance        -- creator can afford the endowment
    ∧ evm.executionEnv.depth ≠ 1024            -- call-depth limit not reached
    ∧ creator.nonce.toNat < 2 ^ 64 - 1         -- creator nonce below the cap (EIP-2681)
    ∧ initCode.size ≤ 49152                     -- init code within the limit (EIP-3860)

/-- Contract creation (`new`) via the EVM `Λ` (Lambda) function. The result triple is
    `(addr, evm', success)`: the created contract's address, the resulting EVM state,
    and whether creation succeeded. Mirrors `callViaEVM`, but `Λ` runs the
    initialisation code instead of a message call and returns the new address. -/
inductive newViaEVM (cfg : Config) (evm : EVM.State)
    (name : Ident) (value : ℤ) (args : List Value) (salt : Option ByteArray) :
    (EVM.Address × EVM.State × Bool) → Prop where
  | created :
      cfg.creationCode name args = .some initCode
      → newCanCreate evm value initCode
      → valueWord = EVM.wordOfInt value
      → (∃ createGas refunds accessedStorageKeys,
          -- As in `callViaEVM`, existentially quantify over substate fields
          -- whose value we do not track accurately but which creation can change.
          let A_exist := { evm.substate with
                      refundBalance := refunds
                      accessedStorageKeys := accessedStorageKeys }
          -- Mirror the CREATE opcode: bump the creator's nonce before calling `Lambda`,
          -- which derives the new address from `sender.nonce - 1` and so expects the
          -- already-incremented nonce.
          let creator := evm.accountMap.find? evm.executionEnv.codeOwner |>.getD default
          let σStar := evm.accountMap.insert evm.executionEnv.codeOwner
                        { creator with nonce := creator.nonce + ⟨1⟩ }
          (addr, cA', σ', _, A', z, _)
            = Ethereum.EVM.Lambda
            evm.executionEnv.blobVersionedHashes
            evm.createdAccounts
            evm.genesisBlockHeader
            evm.blocks
            σStar
            evm.σ₀
            A_exist
            evm.executionEnv.codeOwner  -- sender (msg.sender): `this`, as CREATE does
            evm.executionEnv.sender     -- original transactor (tx.origin)
            createGas
            (.ofNat evm.executionEnv.gasPrice)
            valueWord                   -- endowment
            initCode                    -- initialisation EVM code
            (evm.executionEnv.depth + 1)
            salt                        -- `none` ⇒ CREATE; `some s` ⇒ CREATE2 with salt `s`
            evm.executionEnv.header
            true)                       -- permission to modify state
      → evm' = { evm with accountMap := σ', substate := A', createdAccounts := cA' }
      → newViaEVM cfg evm name value args salt (addr, evm', z)
  | notCreated :
      cfg.creationCode name args = .some initCode
      → ¬ newCanCreate evm value initCode
      → newViaEVM cfg evm name value args salt (EVM.address 0, evm, false)

end Solm
