import Benchmarks.Scaffolds.Klima.Spec
import Solm.Notation

/-!
# KlimaToken spec in the Solidity-faithful Solm frontend

The whole KlimaToken benchmark spec, written with `solidity%` and proven definitionally equal to
the AST spec in `Benchmarks/Klima/Spec.lean`.

Notes mirroring the AST spec:
* SafeMath checked add/sub are the explicit `require` + `(… ) as uint256` range-cast forms.
* The `_beforeTokenTransfer` TWAP hook is inlined at every mint/burn/transfer site: the doubled
  `dexIndexes[bytes32(uint256(x))] != 0` test (`_beforeTokenTransfer` then `_uodateTWAPOracle`),
  the `EXTCODESIZE` guard, and the `twapOracle.updateTWAP` external call.
* EnumerableSet keys are `bytes32(uint256(addr))` casts, exactly as the library stores them.
* `permit`'s ecrecover precompile call targets `address(1)` (a cast), which the surface low-level
  call cannot express, so that one statement is spliced; its `ecrecoverSuccess`/`ecrecoverData`
  binders are then referenced via `${…}`.  `PERMIT_TYPEHASH` and the EIP-191 prefix reuse the
  spec's `permitTypehashExpr`/`eip191Prefix` defs.
* Transition order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation

namespace Benchmarks.Klima.Syntax

def contractSyntax : ContractDecl := solidity% contract KlimaToken {
  mapping(address => uint256) balances;
  mapping(address => mapping(address => uint256)) allowances;
  uint256 totalSupply;
  string name;
  string symbol;
  uint8 decimals;
  mapping(address => uint256) nonces;
  bytes32 DOMAIN_SEPARATOR;
  address owner;
  address vault;
  bytes32[] dexValues;
  mapping(bytes32 => uint256) dexIndexes;
  address twapOracle;
  uint256 twapEpochPeriod;

  constructor() {
    name = "Klima DAO";
    symbol = "KLIMA";
    decimals = 9;
    DOMAIN_SEPARATOR = keccak256(abi.encodePacked(
      bytes32(keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)")),
      bytes32(keccak256("Klima DAO")),
      bytes32(keccak256("1")),
      uint256(block.chainid),
      uint256(uint256(this))));
    owner = msg.sender;
  }

  function addTWAPSource(address newSource) external {
    require(owner == msg.sender);
    require(dexIndexes[bytes32(uint256(newSource))] == 0);
    dexValues.push(bytes32(uint256(newSource)));
    dexIndexes[bytes32(uint256(newSource))] = dexValues.length;
  }

  function allowance(address owner, address spender) external returns (uint256) {
    return allowances[owner][spender];
  }

  function approve(address spender, uint256 amount) external returns (bool) {
    require(msg.sender != address(0));
    require(spender != address(0));
    allowances[msg.sender][spender] = amount;
    return true;
  }

  function balanceOf(address account) external returns (uint256) {
    return balances[account];
  }

  function burn(uint256 amount) external {
    require(msg.sender != address(0));
    if (dexIndexes[bytes32(uint256(msg.sender))] != 0) {
      if (dexIndexes[bytes32(uint256(msg.sender))] != 0) {
        require(twapOracle.code.length > 0);
        var _twapRet = twapOracle.updateTWAP(msg.sender, twapEpochPeriod);
      }
    } else {
      if (dexIndexes[bytes32(uint256(address(0)))] != 0) {
        if (dexIndexes[bytes32(uint256(address(0)))] != 0) {
          require(twapOracle.code.length > 0);
          var _twapRet = twapOracle.updateTWAP(address(0), twapEpochPeriod);
        }
      }
    }
    require(amount <= balances[msg.sender]);
    balances[msg.sender] = (balances[msg.sender] - amount) as uint256;
    require(amount <= totalSupply);
    totalSupply = (totalSupply - amount) as uint256;
  }

  function burnFrom(address account, uint256 amount) external {
    require(amount <= allowances[account][msg.sender]);
    require(account != address(0));
    require(msg.sender != address(0));
    allowances[account][msg.sender] = (allowances[account][msg.sender] - amount) as uint256;
    require(account != address(0));
    if (dexIndexes[bytes32(uint256(account))] != 0) {
      if (dexIndexes[bytes32(uint256(account))] != 0) {
        require(twapOracle.code.length > 0);
        var _twapRet = twapOracle.updateTWAP(account, twapEpochPeriod);
      }
    } else {
      if (dexIndexes[bytes32(uint256(address(0)))] != 0) {
        if (dexIndexes[bytes32(uint256(address(0)))] != 0) {
          require(twapOracle.code.length > 0);
          var _twapRet = twapOracle.updateTWAP(address(0), twapEpochPeriod);
        }
      }
    }
    require(amount <= balances[account]);
    balances[account] = (balances[account] - amount) as uint256;
    require(amount <= totalSupply);
    totalSupply = (totalSupply - amount) as uint256;
  }

  function _burnFrom(address account, uint256 amount) external {
    require(amount <= allowances[account][msg.sender]);
    require(account != address(0));
    require(msg.sender != address(0));
    allowances[account][msg.sender] = (allowances[account][msg.sender] - amount) as uint256;
    require(account != address(0));
    if (dexIndexes[bytes32(uint256(account))] != 0) {
      if (dexIndexes[bytes32(uint256(account))] != 0) {
        require(twapOracle.code.length > 0);
        var _twapRet = twapOracle.updateTWAP(account, twapEpochPeriod);
      }
    } else {
      if (dexIndexes[bytes32(uint256(address(0)))] != 0) {
        if (dexIndexes[bytes32(uint256(address(0)))] != 0) {
          require(twapOracle.code.length > 0);
          var _twapRet = twapOracle.updateTWAP(address(0), twapEpochPeriod);
        }
      }
    }
    require(amount <= balances[account]);
    balances[account] = (balances[account] - amount) as uint256;
    require(amount <= totalSupply);
    totalSupply = (totalSupply - amount) as uint256;
  }

  function changeTWAPEpochPeriod(uint256 newTWAPEpochPeriod) external {
    require(owner == msg.sender);
    require(newTWAPEpochPeriod > 0);
    twapEpochPeriod = newTWAPEpochPeriod;
  }

  function changeTWAPOracle(address newTWAPOracle) external {
    require(owner == msg.sender);
    twapOracle = newTWAPOracle;
  }

  function decimals() external returns (uint8) {
    return decimals;
  }

  function decreaseAllowance(address spender, uint256 subtractedValue) external returns (bool) {
    require(subtractedValue <= allowances[msg.sender][spender]);
    require(msg.sender != address(0));
    require(spender != address(0));
    allowances[msg.sender][spender] = (allowances[msg.sender][spender] - subtractedValue) as uint256;
    return true;
  }

  function DOMAIN_SEPARATOR() external returns (bytes32) {
    return DOMAIN_SEPARATOR;
  }

  function increaseAllowance(address spender, uint256 addedValue) external returns (bool) {
    require(((allowances[msg.sender][spender] + addedValue) as uint256) >= allowances[msg.sender][spender]);
    require(msg.sender != address(0));
    require(spender != address(0));
    allowances[msg.sender][spender] = (allowances[msg.sender][spender] + addedValue) as uint256;
    return true;
  }

  function mint(address account, uint256 amount) external {
    require(vault == msg.sender);
    require(account != address(0));
    if (dexIndexes[bytes32(uint256(address(this)))] != 0) {
      if (dexIndexes[bytes32(uint256(address(this)))] != 0) {
        require(twapOracle.code.length > 0);
        var _twapRet = twapOracle.updateTWAP(address(this), twapEpochPeriod);
      }
    } else {
      if (dexIndexes[bytes32(uint256(account))] != 0) {
        if (dexIndexes[bytes32(uint256(account))] != 0) {
          require(twapOracle.code.length > 0);
          var _twapRet = twapOracle.updateTWAP(account, twapEpochPeriod);
        }
      }
    }
    require(((totalSupply + amount) as uint256) >= totalSupply);
    totalSupply = (totalSupply + amount) as uint256;
    require(((balances[account] + amount) as uint256) >= balances[account]);
    balances[account] = (balances[account] + amount) as uint256;
  }

  function name() external returns (string) {
    return name;
  }

  function nonces(address owner) external returns (uint256) {
    return nonces[owner];
  }

  function owner() external returns (address) {
    return owner;
  }

  function permit(address owner, address spender, uint256 amount, uint256 deadline,
      uint8 v, bytes32 r, bytes32 s) external {
    require(block.timestamp <= deadline);
    bytes32 hashStruct = keccak256(abi.encodePacked(
      bytes32(${permitTypehashExpr}),
      uint256(uint256(owner)),
      uint256(uint256(spender)),
      uint256(amount),
      uint256(nonces[owner]),
      uint256(deadline)));
    bytes32 digest = keccak256(abi.encodePacked(
      bytes(${eip191Prefix}),
      bytes32(DOMAIN_SEPARATOR),
      bytes32(hashStruct)));
    ${[Stmt.lowLevelCall ecrecoverPrecompile (.intLit 0) ecrecoverCalldataExpr
        "ecrecoverSuccess" "ecrecoverData" false]}
    require(${Expr.var "ecrecoverSuccess"});
    address signer = abi.decode(${Expr.var "ecrecoverData"}, (address));
    require(signer != address(0) && signer == owner);
    nonces[owner] = (nonces[owner] + 1) as uint256;
    require(owner != address(0));
    require(spender != address(0));
    allowances[owner][spender] = amount;
  }

  function PERMIT_TYPEHASH() external returns (bytes32) {
    return ${permitTypehashExpr};
  }

  function removeTWAPSource(address rm) external {
    require(owner == msg.sender);
    uint256 valueIndex = dexIndexes[bytes32(uint256(rm))];
    require(valueIndex != 0);
    uint256 toDeleteIndex = (valueIndex - 1) as uint256;
    uint256 lastIndex = (dexValues.length - 1) as uint256;
    bytes32 lastvalue = dexValues[lastIndex];
    dexValues[toDeleteIndex] = lastvalue;
    dexIndexes[lastvalue] = (toDeleteIndex + 1) as uint256;
    dexValues.pop();
    delete dexIndexes[bytes32(uint256(rm))];
  }

  function renounceOwnership() external {
    require(owner == msg.sender);
    owner = address(0);
  }

  function setVault(address vault_) external returns (bool) {
    require(owner == msg.sender);
    vault = vault_;
    return true;
  }

  function symbol() external returns (string) {
    return symbol;
  }

  function totalSupply() external returns (uint256) {
    return totalSupply;
  }

  function transfer(address recipient, uint256 amount) external returns (bool) {
    require(msg.sender != address(0));
    require(recipient != address(0));
    if (dexIndexes[bytes32(uint256(msg.sender))] != 0) {
      if (dexIndexes[bytes32(uint256(msg.sender))] != 0) {
        require(twapOracle.code.length > 0);
        var _twapRet = twapOracle.updateTWAP(msg.sender, twapEpochPeriod);
      }
    } else {
      if (dexIndexes[bytes32(uint256(recipient))] != 0) {
        if (dexIndexes[bytes32(uint256(recipient))] != 0) {
          require(twapOracle.code.length > 0);
          var _twapRet = twapOracle.updateTWAP(recipient, twapEpochPeriod);
        }
      }
    }
    require(amount <= balances[msg.sender]);
    balances[msg.sender] = (balances[msg.sender] - amount) as uint256;
    require(((balances[recipient] + amount) as uint256) >= balances[recipient]);
    balances[recipient] = (balances[recipient] + amount) as uint256;
    return true;
  }

  function transferFrom(address sender_, address recipient, uint256 amount) external returns (bool) {
    require(sender_ != address(0));
    require(recipient != address(0));
    if (dexIndexes[bytes32(uint256(sender_))] != 0) {
      if (dexIndexes[bytes32(uint256(sender_))] != 0) {
        require(twapOracle.code.length > 0);
        var _twapRet = twapOracle.updateTWAP(sender_, twapEpochPeriod);
      }
    } else {
      if (dexIndexes[bytes32(uint256(recipient))] != 0) {
        if (dexIndexes[bytes32(uint256(recipient))] != 0) {
          require(twapOracle.code.length > 0);
          var _twapRet = twapOracle.updateTWAP(recipient, twapEpochPeriod);
        }
      }
    }
    require(amount <= balances[sender_]);
    balances[sender_] = (balances[sender_] - amount) as uint256;
    require(((balances[recipient] + amount) as uint256) >= balances[recipient]);
    balances[recipient] = (balances[recipient] + amount) as uint256;
    require(amount <= allowances[sender_][msg.sender]);
    require(sender_ != address(0));
    require(msg.sender != address(0));
    allowances[sender_][msg.sender] = (allowances[sender_][msg.sender] - amount) as uint256;
    return true;
  }

  function transferOwnership(address newOwner) external {
    require(owner == msg.sender);
    require(newOwner != address(0));
    owner = newOwner;
  }

  function twapEpochPeriod() external returns (uint256) {
    return twapEpochPeriod;
  }

  function twapOracle() external returns (address) {
    return twapOracle;
  }

  function vault() external returns (address) {
    return vault;
  }
}

theorem contractSyntax_eq : contractSyntax = Benchmarks.Klima.contract := by rfl

end Benchmarks.Klima.Syntax
