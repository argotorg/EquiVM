import Solidity.Test.Specs.ERC20
import Solidity.Examples.ERC20.Bytecode
import Solidity.Theory.Derivations
import EVMReasoning.SolcTrace

/-!
# ERC20 — the elaborated Solidity spec, its static facts, and the dispatcher of the bytecode

`erc20Flat` is `elabProgram` of the transcribed source; every fact about it is proved by kernel
evaluation (`rfl`).  The selectors come from the declared keccak facts of `Bytecode.lean`.  The
EVM side: the solc dispatcher prefix and the six selector arms of `erc20Runtime`, and the runs from
`initState` to each function body.
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Trace

set_option maxRecDepth 2000000

namespace ERC20.Opt

def erc20Flat : FlatContract :=
  match elabProgram SoliditySpec.program SoliditySpec.target with
  | .ok fc => fc
  | .error _ => default

theorem erc20Flat_ok : elabProgram SoliditySpec.program SoliditySpec.target = .ok erc20Flat := rfl

abbrev u256 : Ty := u256Ty
abbrev addrTy : Ty := .address false
abbrev abiU256 : ABI.ABIType := .elem (.int (.uint ⟨256, by decide⟩))
abbrev abiAddr : ABI.ABIType := .elem .address

/-! ## State variables and layout -/

def varBalanceOf : FlatVar :=
  { key := "balanceOf", name := "balanceOf", declaredIn := "ERC20", ty := .mapping addrTy u256,
    visibility := .pub, mutability := .mutable, init := none }

def varAllowance : FlatVar :=
  { key := "allowance", name := "allowance", declaredIn := "ERC20",
    ty := .mapping addrTy (.mapping addrTy u256), visibility := .pub, mutability := .mutable, init := none }

def varTotalSupply : FlatVar :=
  { key := "totalSupply", name := "totalSupply", declaredIn := "ERC20", ty := u256,
    visibility := .pub, mutability := .mutable, init := none }

def erc20Table : LayoutTable :=
  [ (varBalanceOf, 0, 0, .mapping addrTy (.leaf uint256Elem 32)),
    (varAllowance, 1, 0, .mapping addrTy (.mapping addrTy (.leaf uint256Elem 32))),
    (varTotalSupply, 2, 0, .leaf uint256Elem 32) ]

def erc20Cfg : Config :=
  { storage := storageLayout erc20Table, selfDeployment := solcDeployment erc20Flat }

theorem erc20Cfg_eq : defaultConfig erc20Flat = some erc20Cfg := rfl

@[simp] theorem erc20Flat_stateVars : erc20Flat.stateVars = [varBalanceOf, varAllowance, varTotalSupply] := rfl
@[simp] theorem erc20Flat_var_balanceOf : erc20Flat.varIn "ERC20" "balanceOf" = some varBalanceOf := rfl
@[simp] theorem erc20Flat_var_allowance : erc20Flat.varIn "ERC20" "allowance" = some varAllowance := rfl
@[simp] theorem erc20Flat_var_totalSupply : erc20Flat.varIn "ERC20" "totalSupply" = some varTotalSupply := rfl
@[simp] theorem erc20Flat_receive : erc20Flat.receive? = none := rfl
@[simp] theorem erc20Flat_fallback : erc20Flat.fallback? = none := rfl
@[simp] theorem erc20Flat_name : erc20Flat.name = "ERC20" := rfl

/-- The slot of `balanceOf[a]`. -/
def balSlot (a : EVM.Address) : UInt256 := mappingSlot (.address a) ⟨0⟩
/-- The slot of `allowance[a][b]`. -/
def alwSlot (a b : EVM.Address) : UInt256 := mappingSlot (.address b) (mappingSlot (.address a) ⟨1⟩)

theorem erc20Layout_totalSupply (evm : EVM.State) :
    erc20Cfg.storage.layout ⟨"totalSupply", []⟩ evm = some (uint256Loc ⟨2⟩) := rfl

theorem erc20Layout_balanceOf (a : EVM.Address) (evm : EVM.State) :
    erc20Cfg.storage.layout ⟨"balanceOf", [.mindex (.address a)]⟩ evm = some (uint256Loc (balSlot a)) := rfl

theorem erc20Layout_allowance (a b : EVM.Address) (evm : EVM.State) :
    erc20Cfg.storage.layout ⟨"allowance", [.mindex (.address a), .mindex (.address b)]⟩ evm =
      some (uint256Loc (alwSlot a b)) := rfl

@[simp] theorem keyRef_balanceOf (a : EVM.Address) :
    keyRef ⟨"balanceOf", []⟩ (.address a) = ⟨"balanceOf", [.mindex (.address a)]⟩ := rfl
@[simp] theorem keyRef_allowance (a : EVM.Address) :
    keyRef ⟨"allowance", []⟩ (.address a) = ⟨"allowance", [.mindex (.address a)]⟩ := rfl
@[simp] theorem keyRef_allowance2 (a b : EVM.Address) :
    keyRef ⟨"allowance", [.mindex (.address a)]⟩ (.address b) =
      ⟨"allowance", [.mindex (.address a), .mindex (.address b)]⟩ := rfl

/-- The spec's mapping slot is the bytecode's `keccak256(key ++ slot)`. -/
theorem balSlot_eq (a : EVM.Address) : balSlot a = solcMappingSlot ⟨0⟩ (UInt256.ofNat a.val) := by
  simp only [balSlot, mappingSlot, solcMappingSlot, keyValueToWord_address]

theorem alwSlot_eq (a b : EVM.Address) :
    alwSlot a b = solcMappingSlot (solcMappingSlot ⟨1⟩ (UInt256.ofNat a.val)) (UInt256.ofNat b.val) := by
  simp only [alwSlot, mappingSlot, solcMappingSlot, keyValueToWord_address]

/-! ## Functions -/

def msgSender : Expr := .member (.ident "msg") "sender"

def fnCtor : FnDef :=
  { id := 0, declaredIn := "ERC20",
    decl := { kind := .ctor, name := "",
              params := [{ ty := u256, name := some "initialSupply" }],
              body := some
                [ .exprStmt (.assign .assign (.index (.ident "balanceOf") msgSender) (.ident "initialSupply")),
                  .exprStmt (.assign .assign (.ident "totalSupply") (.ident "initialSupply")),
                  .emit (.ident "Transfer") (.positional
                    [ .call (.typeExpr addrTy) [] (.positional [.lit (.number 0 none none)]), msgSender,
                      .ident "initialSupply" ]) ] } }

def fnTransfer : FnDef :=
  { id := 1, declaredIn := "ERC20",
    decl := { kind := .function, name := "transfer",
              params := [{ ty := addrTy, name := some "to" }, { ty := u256, name := some "value" }],
              returns := [{ ty := .bool }], visibility := some .external, mutability := .nonpayable,
              body := some
                [ .exprStmt (.call (.ident "require") [] (.positional
                    [ .binary .ge (.index (.ident "balanceOf") msgSender) (.ident "value"),
                      .lit (.str "ERC20: insufficient balance") ])),
                  .exprStmt (.assign .sub (.index (.ident "balanceOf") msgSender) (.ident "value")),
                  .exprStmt (.assign .add (.index (.ident "balanceOf") (.ident "to")) (.ident "value")),
                  .emit (.ident "Transfer") (.positional [msgSender, .ident "to", .ident "value"]),
                  .return (some (.lit (.bool true))) ] } }

def fnApprove : FnDef :=
  { id := 2, declaredIn := "ERC20",
    decl := { kind := .function, name := "approve",
              params := [{ ty := addrTy, name := some "spender" }, { ty := u256, name := some "value" }],
              returns := [{ ty := .bool }], visibility := some .external, mutability := .nonpayable,
              body := some
                [ .exprStmt (.assign .assign (.index (.index (.ident "allowance") msgSender) (.ident "spender"))
                    (.ident "value")),
                  .emit (.ident "Approval") (.positional [msgSender, .ident "spender", .ident "value"]),
                  .return (some (.lit (.bool true))) ] } }

def fnTransferFrom : FnDef :=
  { id := 3, declaredIn := "ERC20",
    decl := { kind := .function, name := "transferFrom",
              params := [{ ty := addrTy, name := some "from" }, { ty := addrTy, name := some "to" },
                         { ty := u256, name := some "value" }],
              returns := [{ ty := .bool }], visibility := some .external, mutability := .nonpayable,
              body := some
                [ .varDecl u256 none "currentAllowance"
                    (some (.index (.index (.ident "allowance") (.ident "from")) msgSender)),
                  .exprStmt (.call (.ident "require") [] (.positional
                    [ .binary .ge (.ident "currentAllowance") (.ident "value"),
                      .lit (.str "ERC20: insufficient allowance") ])),
                  .exprStmt (.call (.ident "require") [] (.positional
                    [ .binary .ge (.index (.ident "balanceOf") (.ident "from")) (.ident "value"),
                      .lit (.str "ERC20: insufficient balance") ])),
                  .exprStmt (.assign .assign (.index (.index (.ident "allowance") (.ident "from")) msgSender)
                    (.binary .sub (.ident "currentAllowance") (.ident "value"))),
                  .exprStmt (.assign .sub (.index (.ident "balanceOf") (.ident "from")) (.ident "value")),
                  .exprStmt (.assign .add (.index (.ident "balanceOf") (.ident "to")) (.ident "value")),
                  .emit (.ident "Transfer") (.positional [.ident "from", .ident "to", .ident "value"]),
                  .return (some (.lit (.bool true))) ] } }

def fnBalanceOf : FnDef :=
  { id := 4, declaredIn := "ERC20",
    decl := { kind := .function, name := "balanceOf", params := [{ ty := addrTy, name := some "arg0" }],
              returns := [{ ty := u256 }], visibility := some .external, mutability := .view,
              body := some [.return (some (.index (.ident "balanceOf") (.ident "arg0")))] } }

def fnAllowance : FnDef :=
  { id := 5, declaredIn := "ERC20",
    decl := { kind := .function, name := "allowance",
              params := [{ ty := addrTy, name := some "arg0" }, { ty := addrTy, name := some "arg1" }],
              returns := [{ ty := u256 }], visibility := some .external, mutability := .view,
              body := some [.return (some (.index (.index (.ident "allowance") (.ident "arg0")) (.ident "arg1")))] } }

def fnTotalSupply : FnDef :=
  { id := 6, declaredIn := "ERC20",
    decl := { kind := .function, name := "totalSupply", params := [], returns := [{ ty := u256 }],
              visibility := some .external, mutability := .view,
              body := some [.return (some (.ident "totalSupply"))] } }

@[simp] theorem erc20Flat_fns0 : erc20Flat.fns[0]? = some fnCtor := rfl
@[simp] theorem erc20Flat_fns1 : erc20Flat.fns[1]? = some fnTransfer := rfl
@[simp] theorem erc20Flat_fns2 : erc20Flat.fns[2]? = some fnApprove := rfl
@[simp] theorem erc20Flat_fns3 : erc20Flat.fns[3]? = some fnTransferFrom := rfl
@[simp] theorem erc20Flat_fns4 : erc20Flat.fns[4]? = some fnBalanceOf := rfl
@[simp] theorem erc20Flat_fns5 : erc20Flat.fns[5]? = some fnAllowance := rfl
@[simp] theorem erc20Flat_fns6 : erc20Flat.fns[6]? = some fnTotalSupply := rfl
@[simp] theorem erc20Flat_ctorChain : erc20Flat.ctorChain = [CtorStep.mk "ERC20" (some 0) none] := rfl

/-! ## Events -/

def evTransfer : EventInfo :=
  { declaredIn := "ERC20",
    decl := { name := "Transfer",
              params := [{ ty := addrTy, indexed := true, name := some "from" },
                         { ty := addrTy, indexed := true, name := some "to" },
                         { ty := u256, name := some "value" }] },
    sig := ⟨"Transfer", [abiAddr, abiAddr, abiU256]⟩,
    sigStr := ABI.printSignature ⟨"Transfer", [abiAddr, abiAddr, abiU256]⟩ }

def evApproval : EventInfo :=
  { declaredIn := "ERC20",
    decl := { name := "Approval",
              params := [{ ty := addrTy, indexed := true, name := some "owner" },
                         { ty := addrTy, indexed := true, name := some "spender" },
                         { ty := u256, name := some "value" }] },
    sig := ⟨"Approval", [abiAddr, abiAddr, abiU256]⟩,
    sigStr := ABI.printSignature ⟨"Approval", [abiAddr, abiAddr, abiU256]⟩ }

@[simp] theorem erc20Flat_eventsNamed_Transfer : erc20Flat.eventsNamedIn "ERC20" "Transfer" = [evTransfer] := rfl
@[simp] theorem erc20Flat_eventsNamed_Approval : erc20Flat.eventsNamedIn "ERC20" "Approval" = [evApproval] := rfl

/-- The signature strings (`ABI.printSignature` does not reduce in the kernel). -/
theorem evTransfer_sigStr : evTransfer.sigStr = "Transfer(address,address,uint256)" := by native_decide
theorem evApproval_sigStr : evApproval.sigStr = "Approval(address,address,uint256)" := by native_decide

theorem evTransfer_topic : hashWord evTransfer.sigStr.toUTF8 =
    ⟨0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef⟩ := by
  rw [evTransfer_sigStr]; exact topic_Transfer
theorem evApproval_topic : hashWord evApproval.sigStr.toUTF8 =
    ⟨0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925⟩ := by
  rw [evApproval_sigStr]; exact topic_Approval

/-! ## Dispatch table and selectors -/

def sigTransferFrom : ABI.Signature := ⟨"transferFrom", [abiAddr, abiAddr, abiU256]⟩
def sigApprove : ABI.Signature := ⟨"approve", [abiAddr, abiU256]⟩
def sigTransfer : ABI.Signature := ⟨"transfer", [abiAddr, abiU256]⟩
def sigBalanceOf : ABI.Signature := ⟨"balanceOf", [abiAddr]⟩
def sigAllowance : ABI.Signature := ⟨"allowance", [abiAddr, abiAddr]⟩
def sigTotalSupply : ABI.Signature := ⟨"totalSupply", []⟩

def entryOf (sig : ABI.Signature) (fn : FnId) (isGetter : Bool) : DispatchEntry :=
  { sigStr := ABI.printSignature sig, sig := sig, fn := fn, isGetter := isGetter }

def entryTransferFrom : DispatchEntry := entryOf sigTransferFrom 3 false
def entryApprove : DispatchEntry := entryOf sigApprove 2 false
def entryTransfer : DispatchEntry := entryOf sigTransfer 1 false
def entryBalanceOf : DispatchEntry := entryOf sigBalanceOf 4 true
def entryAllowance : DispatchEntry := entryOf sigAllowance 5 true
def entryTotalSupply : DispatchEntry := entryOf sigTotalSupply 6 true

theorem printSig_transferFrom : ABI.printSignature sigTransferFrom = "transferFrom(address,address,uint256)" := by native_decide
theorem printSig_approve : ABI.printSignature sigApprove = "approve(address,uint256)" := by native_decide
theorem printSig_transfer : ABI.printSignature sigTransfer = "transfer(address,uint256)" := by native_decide
theorem printSig_balanceOf : ABI.printSignature sigBalanceOf = "balanceOf(address)" := by native_decide
theorem printSig_allowance : ABI.printSignature sigAllowance = "allowance(address,address)" := by native_decide
theorem printSig_totalSupply : ABI.printSignature sigTotalSupply = "totalSupply()" := by native_decide

/-- The declared selectors on the dispatch table's signature strings. -/
theorem selApprove : selectorOf (ABI.printSignature sigApprove) = ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ := by
  rw [printSig_approve]; exact sel_approve
theorem selTotalSupply : selectorOf (ABI.printSignature sigTotalSupply) = ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ := by
  rw [printSig_totalSupply]; exact sel_totalSupply
theorem selTransferFrom : selectorOf (ABI.printSignature sigTransferFrom) = ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ := by
  rw [printSig_transferFrom]; exact sel_transferFrom
theorem selBalanceOf : selectorOf (ABI.printSignature sigBalanceOf) = ⟨#[0x70, 0xa0, 0x82, 0x31]⟩ := by
  rw [printSig_balanceOf]; exact sel_balanceOf
theorem selTransfer : selectorOf (ABI.printSignature sigTransfer) = ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ := by
  rw [printSig_transfer]; exact sel_transfer
theorem selAllowance : selectorOf (ABI.printSignature sigAllowance) = ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ := by
  rw [printSig_allowance]; exact sel_allowance

@[simp] theorem erc20Flat_entries : erc20Flat.entries =
    [entryTransferFrom, entryApprove, entryTransfer, entryBalanceOf, entryAllowance, entryTotalSupply] := rfl

/-- The six selectors in the bytecode's arm order: approve, totalSupply, transferFrom, balanceOf,
    transfer, allowance. -/
def selBytes : ℕ → ByteArray
  | 0 => ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
  | 1 => ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩
  | 2 => ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩
  | 3 => ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
  | 4 => ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩
  | _ => ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩

/-- The 4-byte selector of `I`'s calldata is `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop := (sel == I.calldata.extract 0 4) = true

theorem size_ge_of_sel {cd sel : ByteArray} (hsz : sel.size = 4) (hsel : (sel == cd.extract 0 4) = true) :
    4 ≤ cd.size := by
  have h := byteArray_size_eq_of_beq hsel
  rw [hsz, ByteArray.size_extract] at h
  omega

/-- The dispatch table scanned by `List.find?`, with the declared selectors. -/
macro "erc20_dispatch" : tactic => `(tactic|
  (simp only [selectorDispatch_of_size ‹4 ≤ _›, erc20Flat_entries, List.find?_cons, List.find?_nil,
     entryTransferFrom, entryApprove, entryTransfer, entryBalanceOf, entryAllowance, entryTotalSupply, entryOf,
     selTransferFrom, selApprove, selTransfer, selBalanceOf, selAllowance, selTotalSupply, *] <;> rfl))

theorem erc20Dispatch_approve {cd : ByteArray} (hsel : (selBytes 0 == cd.extract 0 4) = true) :
    selectorDispatch erc20Flat cd = some entryApprove := by
  have hsz : 4 ≤ cd.size := size_ge_of_sel rfl hsel
  have hcd : cd.extract 0 4 = ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ := (byteArray_eq_of_beq hsel).symm
  erc20_dispatch

theorem erc20Dispatch_totalSupply {cd : ByteArray} (hsel : (selBytes 1 == cd.extract 0 4) = true) :
    selectorDispatch erc20Flat cd = some entryTotalSupply := by
  have hsz : 4 ≤ cd.size := size_ge_of_sel rfl hsel
  have hcd : cd.extract 0 4 = ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ := (byteArray_eq_of_beq hsel).symm
  erc20_dispatch

theorem erc20Dispatch_transferFrom {cd : ByteArray} (hsel : (selBytes 2 == cd.extract 0 4) = true) :
    selectorDispatch erc20Flat cd = some entryTransferFrom := by
  have hsz : 4 ≤ cd.size := size_ge_of_sel rfl hsel
  have hcd : cd.extract 0 4 = ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ := (byteArray_eq_of_beq hsel).symm
  erc20_dispatch

theorem erc20Dispatch_balanceOf {cd : ByteArray} (hsel : (selBytes 3 == cd.extract 0 4) = true) :
    selectorDispatch erc20Flat cd = some entryBalanceOf := by
  have hsz : 4 ≤ cd.size := size_ge_of_sel rfl hsel
  have hcd : cd.extract 0 4 = ⟨#[0x70, 0xa0, 0x82, 0x31]⟩ := (byteArray_eq_of_beq hsel).symm
  erc20_dispatch

theorem erc20Dispatch_transfer {cd : ByteArray} (hsel : (selBytes 4 == cd.extract 0 4) = true) :
    selectorDispatch erc20Flat cd = some entryTransfer := by
  have hsz : 4 ≤ cd.size := size_ge_of_sel rfl hsel
  have hcd : cd.extract 0 4 = ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ := (byteArray_eq_of_beq hsel).symm
  erc20_dispatch

theorem erc20Dispatch_allowance {cd : ByteArray} (hsel : (selBytes 5 == cd.extract 0 4) = true) :
    selectorDispatch erc20Flat cd = some entryAllowance := by
  have hsz : 4 ≤ cd.size := size_ge_of_sel rfl hsel
  have hcd : cd.extract 0 4 = ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ := (byteArray_eq_of_beq hsel).symm
  erc20_dispatch

/-- No selector matches. -/
theorem erc20Dispatch_none {cd : ByteArray} (hsz : 4 ≤ cd.size)
    (hnm : ∀ i, i < 6 → (selBytes i == cd.extract 0 4) = false) :
    selectorDispatch erc20Flat cd = none := by
  have h0 := hnm 0 (by omega); have h1 := hnm 1 (by omega); have h2 := hnm 2 (by omega)
  have h3 := hnm 3 (by omega); have h4 := hnm 4 (by omega); have h5 := hnm 5 (by omega)
  simp only [selBytes] at h0 h1 h2 h3 h4 h5
  simp only [selectorDispatch_of_size hsz, erc20Flat_entries, List.find?_cons, List.find?_nil,
    entryTransferFrom, entryApprove, entryTransfer, entryBalanceOf, entryAllowance, entryTotalSupply, entryOf,
    selTransferFrom, selApprove, selTransfer, selBalanceOf, selAllowance, selTotalSupply, h0, h1, h2, h3, h4, h5]

theorem erc20Dispatches_false {cd : ByteArray} (hsel : selectorDispatch erc20Flat cd = none) :
    dispatches erc20Flat cd = false :=
  dispatches_eq_false hsel (Or.inl erc20Flat_receive) erc20Flat_fallback

/-! ## Argument decoding -/

@[simp] theorem ofAbi_address (env : TypeEnv) (fuel : Nat) (a : EVM.Address) (h : Heap) :
    ofAbi env (fuel + 1) (.address false) (.address a) h = some (.address a, h) := by
  simp [ofAbi]

@[simp] theorem ofAbi_u256 (env : TypeEnv) (fuel : Nat) (w : UInt256) (h : Heap) :
    ofAbi env (fuel + 1) u256 (.int (w.toNat : Int)) h = some (u256Val w.toNat, h) := by
  show ofAbi env (fuel + 1) u256 (.int (Int.ofNat w.toNat)) h = _
  simp only [ofAbi]
  rw [scalarOfAbi_u256]
  rfl

theorem decodeArgs_approve (cd : ByteArray) :
    decodeArgs erc20Cfg erc20Flat.types fnApprove.decl cd = ABI.decodeCalldataValues? [abiAddr, abiU256] cd .modern :=
  decodeArgs_eq rfl
theorem decodeArgs_transfer (cd : ByteArray) :
    decodeArgs erc20Cfg erc20Flat.types fnTransfer.decl cd = ABI.decodeCalldataValues? [abiAddr, abiU256] cd .modern :=
  decodeArgs_eq rfl
theorem decodeArgs_transferFrom (cd : ByteArray) :
    decodeArgs erc20Cfg erc20Flat.types fnTransferFrom.decl cd =
      ABI.decodeCalldataValues? [abiAddr, abiAddr, abiU256] cd .modern :=
  decodeArgs_eq rfl
theorem decodeArgs_balanceOf (cd : ByteArray) :
    decodeArgs erc20Cfg erc20Flat.types fnBalanceOf.decl cd = ABI.decodeCalldataValues? [abiAddr] cd .modern :=
  decodeArgs_eq rfl
theorem decodeArgs_allowance (cd : ByteArray) :
    decodeArgs erc20Cfg erc20Flat.types fnAllowance.decl cd = ABI.decodeCalldataValues? [abiAddr, abiAddr] cd .modern :=
  decodeArgs_eq rfl
theorem decodeArgs_totalSupply (cd : ByteArray) :
    decodeArgs erc20Cfg erc20Flat.types fnTotalSupply.decl cd = ABI.decodeCalldataValues? [] cd .modern :=
  decodeArgs_eq rfl

/-! ## The dispatcher of the bytecode -/

/-- The six selector arms begin at pc 30 (`approve`). -/
abbrev firstArmPc : UInt256 := ⟨30⟩

theorem prefixWf : solcDispatchPrefixWellFormed erc20Runtime firstArmPc := by solc_dispatch_prefix

theorem armsWf : ∀ j, j ≤ 5 → armWellFormed erc20Runtime (nthArmPc erc20Runtime firstArmPc j) := by
  intro j hj
  interval_cases j <;> exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Arm `j`'s `EQ` is `1`/`0` exactly as the `j`-th selector's bytes match `calldata[0:4]`. -/
theorem armEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 6) :
    UInt256.eq (armSelNat erc20Runtime (nthArmPc erc20Runtime firstArmPc j)) (solcSelectorWord I)
      = if (selBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

/-- When `calldata[0:4]` is the `i`-th selector, the earlier arms' `EQ`s are `0` and arm `i`'s is not. -/
theorem armMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 6) (hsz : 4 ≤ I.calldata.size)
    (hsel : (selBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i → UInt256.eq (armSelNat erc20Runtime (nthArmPc erc20Runtime firstArmPc j))
        (solcSelectorWord I) = ⟨0⟩)
    ∧ UInt256.eq (armSelNat erc20Runtime (nthArmPc erc20Runtime firstArmPc i)) (solcSelectorWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = selBytes i := (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [armEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [armEq I hsz i hi, hci]
    interval_cases i <;> decide

/-- From `initState` to the body entry of arm `i`, the selector word on the stack. -/
theorem reachBody {cA gh bl σ σ₀ A I} {g : Sat256} (i : ℕ) (hi5 : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat erc20Runtime (nthArmPc erc20Runtime firstArmPc j)) (solcSelectorWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat erc20Runtime (nthArmPc erc20Runtime firstArmPc i)) (solcSelectorWord I) ≠ ⟨0⟩)
    (hjd : (D_J erc20Runtime 0).contains bodyPC = true)
    (hbody : armTgt erc20Runtime (nthArmPc erc20Runtime firstArmPc i) = bodyPC) :
    ∃ k C, Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨bodyPC, [solcSelectorWord I], solcFreePtrMem, UInt256.ofNat 3, ByteArray.empty, ⟨cA, σ, A.logSeries⟩⟩ k C := by
  obtain ⟨_, _, h⟩ := Run.solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hcode hwv hsz hsize prefixWf (by jump_dest)
  obtain ⟨_, _, h'⟩ := Run.dispatchNoMatch i h (fun j hj => armsWf j (by omega)) heq0 (by simp)
  subst hbody
  exact ⟨_, _, h'.selectorArmTakenAuto (armsWf i hi5) htake hjd (by simp)⟩

/-- The run to a body, from the selector match alone. -/
theorem reachBodyOf {cA gh bl σ σ₀ A I} {g : Sat256} (i : ℕ) (hi : i < 6) (bodyPC : UInt256)
    (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (selBytes i))
    (hjd : (D_J erc20Runtime 0).contains bodyPC = true)
    (hbody : armTgt erc20Runtime (nthArmPc erc20Runtime firstArmPc i) = bodyPC) :
    ∃ k C, Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨bodyPC, [solcSelectorWord I], solcFreePtrMem, UInt256.ofNat 3, ByteArray.empty, ⟨cA, σ, A.logSeries⟩⟩ k C := by
  have hsz : 4 ≤ I.calldata.size := size_ge_of_sel (by interval_cases i <;> rfl) hsel
  obtain ⟨heq0, htake⟩ := armMatches i hi hsz hsel
  exact reachBody i (by omega) bodyPC hcode hwv hsz hsize heq0 htake hjd hbody

/-! ### The dispatcher's reverts -/

theorem revertNonPayable {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue ≠ ⟨0⟩) :
    Reverted erc20Runtime (initState cA gh bl σ σ₀ g A I) ByteArray.empty :=
  Run.solcDispatchNonPayableRevert hcode hwv prefixWf (by decide) (by decide) (by decide)

theorem revertShort {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hshort : I.calldata.size < 4) :
    Reverted erc20Runtime (initState cA gh bl σ σ₀ g A I) ByteArray.empty :=
  Run.solcDispatchShortRevert hcode hwv hshort prefixWf (by jump_dest) (by decide) (by jump_dest) (by decide)
    (by decide) (by decide)

theorem revertNoMatch {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 6 → (selBytes i == I.calldata.extract 0 4) = false) :
    Reverted erc20Runtime (initState cA gh bl σ σ₀ g A I) ByteArray.empty := by
  have heq0 : ∀ j, j < 6 →
      UInt256.eq (armSelNat erc20Runtime (nthArmPc erc20Runtime firstArmPc j)) (solcSelectorWord I) = ⟨0⟩ := by
    intro j hj
    rw [armEq I hsz j hj, hnm j hj]
    rfl
  exact Run.solcDispatchNoMatchRevert (n := 6) hcode hwv hsz hsize prefixWf (by jump_dest)
    (fun j hj => armsWf j (by omega)) heq0 (by decide) (by decide) (by decide) (by decide)

end ERC20.Opt
