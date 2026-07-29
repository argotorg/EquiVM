import Examples.UniswapV2Pair.Spec
import Solm.Notation

/-!
# UniswapV2Pair spec in the Solidity-faithful Solm frontend

The whole Pair benchmark spec (LP-token surface, permit, and the mutating AMM entry points),
written with `solidity%` and proven definitionally equal to the AST spec in
`Examples/UniswapV2Pair/Spec.lean`.

Escapes, where the surface cannot express the AST:
* `extCodeSize` guards on *storage* receivers (`factory`, `token0`, `token1`): the surface
  `x.code.length` builtin only resolves locals, so those guards use `${Expr.extCodeSize …}`.
* `permit`'s `ecrecover` is an external call whose receiver is the precompile address
  `.cast (.intLit 1) addrSt` — not an identifier — so that statement is a `${[…]}` splice, and
  the spliced binder `recoveredAddress` is referenced via `${Expr.var …}` afterwards.
* `mint` binds `liquidity` inside both `if` branches; the frontend's scope does not carry
  branch-local binders past the `if`, so later uses are `${Expr.var "liquidity"}`.
* Spec `Int` constants (`q112`, `twoPow32`, `twoPow256`) are embedded with `#`.

`from`/`to` are Lean keywords, hence «from»/«to».  Transition order matches
`UniswapV2Pair.contract.transitions` (selector order).
-/

open Solm Solm.Notation

namespace UniswapV2Pair.Syntax

def contractSyntax : ContractDecl := solidity% contract UniswapV2Pair {
  uint256 totalSupply;
  mapping(address => uint256) balanceOf;
  mapping(address => mapping(address => uint256)) allowance;
  bytes32 DOMAIN_SEPARATOR;
  mapping(address => uint256) nonces;
  address factory;
  address token0;
  address token1;
  uint112 reserve0;
  uint112 reserve1;
  uint32 blockTimestampLast;
  uint256 price0CumulativeLast;
  uint256 price1CumulativeLast;
  uint256 kLast;
  uint256 unlocked;

  constructor() payable {
    DOMAIN_SEPARATOR = keccak256(abi.encodePacked(
      bytes32(keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)")),
      bytes32(keccak256("Uniswap V2")),
      bytes32(keccak256("1")),
      uint256(block.chainid),
      uint256(uint256(this))));
    unlocked = 1;
    factory = msg.sender;
  }

  function _approve(address owner, address spender, uint256 value) internal {
    allowance[owner][spender] = value;
  }

  function _transfer(address «from», address «to», uint256 value) internal {
    uint256 fromBalance = balanceOf[«from»];
    require(fromBalance >= value);
    balanceOf[«from»] = fromBalance - value;
    uint256 toBalance = balanceOf[«to»];
    balanceOf[«to»] = (toBalance + value) as uint256;
  }

  function _mint(address «to», uint256 value) internal {
    totalSupply = (totalSupply + value) as uint256;
    balanceOf[«to»] = (balanceOf[«to»] + value) as uint256;
  }

  function _burn(address «from», uint256 value) internal {
    uint256 fromBalance = balanceOf[«from»];
    require(fromBalance >= value);
    balanceOf[«from»] = fromBalance - value;
    uint256 _totalSupply = totalSupply;
    require(_totalSupply >= value);
    totalSupply = _totalSupply - value;
  }

  function _safeTransfer(address token, address «to», uint256 value) internal {
    (bool _success, bytes memory _data) = token.call(abi.encodeWithSelector(transfer, «to», value));
    require(_success ? (_data.length == 0 ? true : abi.decode(_data, (bool))) : false);
  }

  function _update(uint256 balance0, uint256 balance1, uint112 _reserve0, uint112 _reserve1) internal {
    require(balance0 <= type(uint112).max && balance1 <= type(uint112).max);
    uint32 blockTimestamp = (block.timestamp % #twoPow32) as uint32;
    uint32 timeElapsed = ((blockTimestamp - blockTimestampLast + #twoPow32) % #twoPow32) as uint32;
    if (timeElapsed > 0 && _reserve0 != 0 && _reserve1 != 0) {
      price0CumulativeLast =
        (price0CumulativeLast + _reserve1 * #q112 / _reserve0 * timeElapsed) % #twoPow256;
      price1CumulativeLast =
        (price1CumulativeLast + _reserve0 * #q112 / _reserve1 * timeElapsed) % #twoPow256;
    }
    reserve0 = balance0 as uint112;
    reserve1 = balance1 as uint112;
    blockTimestampLast = blockTimestamp;
  }

  function sqrt(uint256 y) internal returns (uint256) {
    if (y > 3) {
      uint256 z = y;
      uint256 x = y / 2 + 1;
      while (x < z) {
        z = x;
        x = (y / x + x) / 2;
      }
      return z;
    } else if (y != 0) {
      return 1;
    } else {
      return 0;
    }
  }

  function min(uint256 x, uint256 y) internal returns (uint256) {
    return x < y ? x : y;
  }

  function _mintFee(uint112 _reserve0, uint112 _reserve1) internal returns (bool) {
    require(${Expr.extCodeSize (.storage factoryRef)} > 0);
    var feeTo = factory.feeTo{view}();
    bool feeOn = feeTo != address(0);
    uint256 _kLast = kLast;
    if (feeOn) {
      if (_kLast != 0) {
        var rootK = sqrt((_reserve0 * _reserve1) as uint256);
        var rootKLast = sqrt(_kLast);
        if (rootK > rootKLast) {
          uint256 numerator = (totalSupply * ((rootK - rootKLast) as uint256)) as uint256;
          uint256 denominator = (((rootK * 5) as uint256) + rootKLast) as uint256;
          uint256 liquidity = numerator / denominator;
          if (liquidity > 0) {
            var _feeMint = _mint(feeTo, liquidity);
          }
        }
      }
    } else {
      if (_kLast != 0) {
        kLast = 0;
      }
    }
    return feeOn;
  }

  function swap(uint256 amount0Out, uint256 amount1Out, address «to», bytes calldata data) external {
    require(unlocked == 1);
    unlocked = 0;
    require(amount0Out > 0 || amount1Out > 0);
    uint112 _reserve0 = reserve0;
    uint112 _reserve1 = reserve1;
    require(amount0Out < _reserve0 && amount1Out < _reserve1);
    address _token0 = token0;
    address _token1 = token1;
    require(«to» != _token0 && «to» != _token1);
    if (amount0Out > 0) {
      var ok0 = _safeTransfer(_token0, «to», amount0Out);
    }
    if (amount1Out > 0) {
      var ok1 = _safeTransfer(_token1, «to», amount1Out);
    }
    if (data.length > 0) {
      require(«to».code.length > 0);
      var _callback = «to».uniswapV2Call(msg.sender, amount0Out, amount1Out, data);
    }
    require(_token0.code.length > 0);
    var balance0 = _token0.balanceOf{view}(this);
    require(_token1.code.length > 0);
    var balance1 = _token1.balanceOf{view}(this);
    uint256 amount0In = balance0 > _reserve0 - amount0Out
      ? ((balance0 - (_reserve0 - amount0Out)) as uint256) : 0;
    uint256 amount1In = balance1 > _reserve1 - amount1Out
      ? ((balance1 - (_reserve1 - amount1Out)) as uint256) : 0;
    require(amount0In > 0 || amount1In > 0);
    uint256 balance0Adjusted = (((balance0 * 1000) as uint256) - ((amount0In * 3) as uint256)) as uint256;
    uint256 balance1Adjusted = (((balance1 * 1000) as uint256) - ((amount1In * 3) as uint256)) as uint256;
    require(((balance0Adjusted * balance1Adjusted) as uint256) >=
      ((((_reserve0 * _reserve1) as uint256) * 1000000) as uint256));
    var _updateResult = _update(balance0, balance1, reserve0, reserve1);
    unlocked = 1;
  }

  function name() external returns (string) {
    return "Uniswap V2";
  }

  function getReserves() external returns (uint112, uint112, uint32) {
    return (reserve0, reserve1, blockTimestampLast);
  }

  function approve(address spender, uint256 value) external returns (bool) {
    allowance[msg.sender][spender] = value;
    return true;
  }

  function token0() external returns (address) {
    return token0;
  }

  function totalSupply() external returns (uint256) {
    return totalSupply;
  }

  function transferFrom(address «from», address «to», uint256 value) external returns (bool) {
    uint256 currentAllowance = allowance[«from»][msg.sender];
    if (currentAllowance != type(uint256).max) {
      require(currentAllowance >= value);
      allowance[«from»][msg.sender] = currentAllowance - value;
    }
    uint256 fromBalance = balanceOf[«from»];
    require(fromBalance >= value);
    balanceOf[«from»] = fromBalance - value;
    uint256 toBalance = balanceOf[«to»];
    balanceOf[«to»] = (toBalance + value) as uint256;
    return true;
  }

  function PERMIT_TYPEHASH() external returns (bytes32) {
    return bytes32(0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9);
  }

  function decimals() external returns (uint8) {
    return 18;
  }

  function DOMAIN_SEPARATOR() external returns (bytes32) {
    return DOMAIN_SEPARATOR;
  }

  function «initialize»(address _token0, address _token1) external {
    require(msg.sender == factory);
    token0 = _token0;
    token1 = _token1;
  }

  function price0CumulativeLast() external returns (uint256) {
    return price0CumulativeLast;
  }

  function price1CumulativeLast() external returns (uint256) {
    return price1CumulativeLast;
  }

  function mint(address «to») external returns (uint256) {
    require(unlocked == 1);
    unlocked = 0;
    uint112 _reserve0 = reserve0;
    uint112 _reserve1 = reserve1;
    require(${Expr.extCodeSize (.storage token0Ref)} > 0);
    var balance0 = token0.balanceOf{view}(this);
    require(${Expr.extCodeSize (.storage token1Ref)} > 0);
    var balance1 = token1.balanceOf{view}(this);
    uint256 amount0 = (balance0 - _reserve0) as uint256;
    uint256 amount1 = (balance1 - _reserve1) as uint256;
    var feeOn = _mintFee(_reserve0, _reserve1);
    uint256 _totalSupply = totalSupply;
    if (_totalSupply == 0) {
      var rootLiquidity = sqrt((amount0 * amount1) as uint256);
      uint256 liquidity = (rootLiquidity - 1000) as uint256;
      var _minimumMint = _mint(address(0), 1000);
    } else {
      uint256 liquidity0 = ((amount0 * _totalSupply) as uint256) / _reserve0;
      uint256 liquidity1 = ((amount1 * _totalSupply) as uint256) / _reserve1;
      var liquidity = min(liquidity0, liquidity1);
    }
    require(${Expr.var "liquidity"} > 0);
    var _mintResult = _mint(«to», ${Expr.var "liquidity"});
    var _updateResult = _update(balance0, balance1, _reserve0, _reserve1);
    if (feeOn) {
      kLast = (reserve0 * reserve1) as uint256;
    }
    unlocked = 1;
    return ${Expr.var "liquidity"};
  }

  function balanceOf(address owner) external returns (uint256) {
    return balanceOf[owner];
  }

  function kLast() external returns (uint256) {
    return kLast;
  }

  function nonces(address owner) external returns (uint256) {
    return nonces[owner];
  }

  function burn(address «to») external returns (uint256, uint256) {
    require(unlocked == 1);
    unlocked = 0;
    uint112 _reserve0 = reserve0;
    uint112 _reserve1 = reserve1;
    address _token0 = token0;
    address _token1 = token1;
    require(_token0.code.length > 0);
    var balance0 = _token0.balanceOf{view}(this);
    require(_token1.code.length > 0);
    var balance1 = _token1.balanceOf{view}(this);
    uint256 liquidity = balanceOf[this];
    var feeOn = _mintFee(_reserve0, _reserve1);
    uint256 _totalSupply = totalSupply;
    uint256 amount0 = ((liquidity * balance0) as uint256) / _totalSupply;
    uint256 amount1 = ((liquidity * balance1) as uint256) / _totalSupply;
    require(amount0 > 0 && amount1 > 0);
    var _burnResult = _burn(this, liquidity);
    var ok0 = _safeTransfer(_token0, «to», amount0);
    var ok1 = _safeTransfer(_token1, «to», amount1);
    require(_token0.code.length > 0);
    var newBalance0 = _token0.balanceOf{view}(this);
    require(_token1.code.length > 0);
    var newBalance1 = _token1.balanceOf{view}(this);
    var _updateResult = _update(newBalance0, newBalance1, reserve0, reserve1);
    if (feeOn) {
      kLast = (reserve0 * reserve1) as uint256;
    }
    unlocked = 1;
    return (amount0, amount1);
  }

  function symbol() external returns (string) {
    return "UNI-V2";
  }

  function transfer(address «to», uint256 value) external returns (bool) {
    uint256 fromBalance = balanceOf[msg.sender];
    require(fromBalance >= value);
    balanceOf[msg.sender] = fromBalance - value;
    uint256 toBalance = balanceOf[«to»];
    balanceOf[«to»] = (toBalance + value) as uint256;
    return true;
  }

  function MINIMUM_LIQUIDITY() external returns (uint256) {
    return 1000;
  }

  function skim(address «to») external {
    require(unlocked == 1);
    unlocked = 0;
    address _token0 = token0;
    address _token1 = token1;
    require(_token0.code.length > 0);
    var balance0 = _token0.balanceOf{view}(this);
    uint256 excess0 = (balance0 - reserve0) as uint256;
    var ok0 = _safeTransfer(_token0, «to», excess0);
    require(_token1.code.length > 0);
    var balance1 = _token1.balanceOf{view}(this);
    uint256 excess1 = (balance1 - reserve1) as uint256;
    var ok1 = _safeTransfer(_token1, «to», excess1);
    unlocked = 1;
  }

  function factory() external returns (address) {
    return factory;
  }

  function token1() external returns (address) {
    return token1;
  }

  function permit(address owner, address spender, uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s) external {
    require(deadline >= block.timestamp);
    bytes32 domainSeparator = DOMAIN_SEPARATOR;
    uint256 nonce = nonces[owner];
    nonces[owner] = (nonce + 1) % #twoPow256;
    bytes32 structHash = keccak256(abi.encodePacked(
      bytes32(bytes32(0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9)),
      uint256(uint256(owner)),
      uint256(uint256(spender)),
      uint256(value),
      uint256(nonce),
      uint256(deadline)));
    bytes32 digest = keccak256(abi.encodePacked(
      bytes2(bytes2(0x1901)),
      bytes32(domainSeparator),
      bytes32(structHash)));
    ${[Stmt.externalCall (Expr.cast (.intLit 1) addrSt) "ecrecover" (.intLit 0)
        [.var "digest", .var "v", .var "r", .var "s"] "recoveredAddress" (perm := false)]}
    require(${Expr.var "recoveredAddress"} != address(0) && ${Expr.var "recoveredAddress"} == owner);
    var _approveResult = _approve(owner, spender, value);
  }

  function allowance(address owner, address spender) external returns (uint256) {
    return allowance[owner][spender];
  }

  function sync() external {
    require(unlocked == 1);
    unlocked = 0;
    require(${Expr.extCodeSize (.storage token0Ref)} > 0);
    var balance0 = token0.balanceOf{view}(this);
    require(${Expr.extCodeSize (.storage token1Ref)} > 0);
    var balance1 = token1.balanceOf{view}(this);
    var _updateResult = _update(balance0, balance1, reserve0, reserve1);
    unlocked = 1;
  }
}

theorem contractSyntax_eq : contractSyntax = UniswapV2Pair.contract := by rfl

end UniswapV2Pair.Syntax
