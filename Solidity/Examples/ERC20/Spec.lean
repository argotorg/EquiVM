import Solidity

/-!
# ERC20 in the Solidity spec language

Transcribed from `Examples/ERC20/ERC20.sol` (`from`/`to` are Lean keywords, hence «from»/«to»).
The Sol⁻ spec is `Examples/ERC20/Spec.lean`; the refinement proof against this spec is in the sibling files.
-/

namespace ERC20.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def erc20 : SourceUnit := sol% contract ERC20 {
  mapping(address => uint256) public balanceOf;
  mapping(address => mapping(address => uint256)) public allowance;
  uint256 public totalSupply;

  event Transfer(address indexed «from», address indexed «to», uint256 value);
  event Approval(address indexed owner, address indexed spender, uint256 value);

  constructor(uint256 initialSupply) {
    balanceOf[msg.sender] = initialSupply;
    totalSupply = initialSupply;
    emit Transfer(address(0), msg.sender, initialSupply);
  }

  function transfer(address «to», uint256 value) external returns (bool) {
    require(balanceOf[msg.sender] >= value, "ERC20: insufficient balance");

    balanceOf[msg.sender] -= value;
    balanceOf[«to»] += value;

    emit Transfer(msg.sender, «to», value);
    return true;
  }

  function approve(address spender, uint256 value) external returns (bool) {
    allowance[msg.sender][spender] = value;

    emit Approval(msg.sender, spender, value);
    return true;
  }

  function transferFrom(address «from», address «to», uint256 value) external returns (bool) {
    uint256 currentAllowance = allowance[«from»][msg.sender];
    require(currentAllowance >= value, "ERC20: insufficient allowance");
    require(balanceOf[«from»] >= value, "ERC20: insufficient balance");

    allowance[«from»][msg.sender] = currentAllowance - value;
    balanceOf[«from»] -= value;
    balanceOf[«to»] += value;

    emit Transfer(«from», «to», value);
    return true;
  }
}

def program : Program := [erc20]
def target : String := "ERC20"

/-- The DSL output for `transfer`, spelled out by hand. -/
def transferHand : FnDecl :=
  let sender : Expr := .member (.ident "msg") "sender"
  let u256 : Ty := .uint ⟨256, by decide⟩
  { kind := .function, name := "transfer",
    params := [{ ty := .address false, name := some "to" }, { ty := u256, name := some "value" }],
    returns := [{ ty := .bool }], visibility := some .external, mutability := .nonpayable,
    body := some
      [ .exprStmt (.call (.ident "require") [] (.positional
          [ .binary .ge (.index (.ident "balanceOf") sender) (.ident "value"),
            .lit (.str "ERC20: insufficient balance") ])),
        .exprStmt (.assign .sub (.index (.ident "balanceOf") sender) (.ident "value")),
        .exprStmt (.assign .add (.index (.ident "balanceOf") (.ident "to")) (.ident "value")),
        .emit (.ident "Transfer") (.positional [sender, .ident "to", .ident "value"]),
        .return (some (.lit (.bool true))) ] }

example : (erc20.contract?.bind (·.fn? "transfer")) = some transferHand := rfl

#guard (erc20.contract?.map (·.functions.length)) = some 3
#guard (erc20.contract?.map (·.events.length)) = some 2
#guard (erc20.contract?.map (·.stateVars.length)) = some 3
#guard (erc20.contract?.bind (·.ctor?)).isSome

/-- Selectors as reported by `solc 0.8.35 --hashes` (checked natively by `solidity-diff --selectors`). -/
def selectors : List (String × String) :=
  [ ("allowance(address,address)", "dd62ed3e"),
    ("approve(address,uint256)", "095ea7b3"),
    ("balanceOf(address)", "70a08231"),
    ("totalSupply()", "18160ddd"),
    ("transfer(address,uint256)", "a9059cbb"),
    ("transferFrom(address,address,uint256)", "23b872dd") ]

end ERC20.SoliditySpec
