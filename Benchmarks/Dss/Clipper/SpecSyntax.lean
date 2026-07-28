import Benchmarks.Dss.Clipper.Spec
import Solm.Notation

/-!
# Clipper spec in the Solidity-faithful Solm frontend

The whole `clip.sol` spec written with `solidity%` and proven definitionally equal to the AST
spec in `Spec.lean`.  Checked DSMath helpers keep their inlined spec shapes (`(…) as uint256`
plus the overflow `require`), built-in wrapping arithmetic is the explicit `% #wordModulus`
(resp. `#uint96Modulus`/`#uint64Modulus`/`#uint192Modulus`), `bytes32` file keys are big-endian
ASCII literals, and immutable `vat`/`ilk` reads plus the external calls that target them are
spliced from the spec (`${vatExpr v}`, `${checkedExternalCallStmts …}`).  Transition order
matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper.Syntax

def contractSyntax (v : ClipperImmutables) : ContractDecl := solidity% contract Clipper {
  struct Sale {
    uint256 pos;
    uint256 tab;
    uint256 lot;
    address usr;
    uint96 tic;
    uint256 top;
  }

  mapping(address => uint256) wards;
  address dog;
  address vow;
  address spotter;
  address «calc»;
  uint256 buf;
  uint256 tail;
  uint256 cusp;
  uint64 chip;
  uint192 tip;
  uint256 chost;
  uint256 kicks;
  uint256[] active;
  mapping(uint256 => Sale) sales;
  uint256 locked;
  uint256 stopped;

  constructor(address vat_, address spotter_, address dog_, bytes32 ilk_) {
    address imm_vat = vat_;
    bytes32 imm_ilk = ilk_;
    spotter = spotter_;
    dog = dog_;
    buf = #RAY;
    wards[msg.sender] = 1;
  }

  function min(uint256 x, uint256 y) internal returns (uint256) {
    if (x <= y) {
      return x;
    } else {
      return y;
    }
  }

  function add(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x + y) as uint256;
    require(z >= x);
    return z;
  }

  function sub(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x - y) as uint256;
    require(z <= x);
    return z;
  }

  function mul(uint256 x, uint256 y) internal returns (uint256) {
    uint256 z = (x * y) as uint256;
    require(y == 0 || z / y == x);
    return z;
  }

  function wmul(uint256 x, uint256 y) internal returns (uint256) {
    var xy = mul(x, y);
    return xy / #WAD;
  }

  function rmul(uint256 x, uint256 y) internal returns (uint256) {
    var xy = mul(x, y);
    return xy / #RAY;
  }

  function rdiv(uint256 x, uint256 y) internal returns (uint256) {
    var xray = mul(x, #RAY);
    return xray / y;
  }

  function getFeedPrice() internal returns (uint256) {
    require(spotter.code.length > 0);
    var spotterIlk = spotter.spotterIlks(${ilkExpr v});
    address pip = spotterIlk.0;
    require(pip.code.length > 0);
    var peekRet = pip.peek();
    bytes32 val = peekRet.0;
    bool has = peekRet.1;
    require(has);
    uint256 valBln = (uint256(val) * #BLN) as uint256;
    require(#BLN == 0 || valBln / #BLN == uint256(val));
    require(spotter.code.length > 0);
    var par = spotter.par();
    var feedPrice = rdiv(valBln, par);
    return feedPrice;
  }

  function status(uint96 tic, uint256 top) internal returns (bool, uint256) {
    var ageForPrice = sub(block.timestamp, tic);
    require(«calc».code.length > 0);
    var price = «calc».price{view}(top, ageForPrice);
    var ageForDone = sub(block.timestamp, tic);
    bool done = false;
    if (ageForDone > tail) {
      done = true;
    } else {
      var ratio = rdiv(price, top);
      done = ratio < cusp;
    }
    return (done, price);
  }

  function _remove(uint256 id) internal {
    uint256 lastIndex = (active.length - 1) as uint256;
    uint256 _move = active[lastIndex];
    if (id != _move) {
      uint256 _index = sales[id].pos;
      active[_index] = _move;
      sales[_move].pos = _index;
    }
    active.pop();
    delete sales[id];
  }

  function active(uint256 arg0) external returns (uint256) {
    return active[arg0];
  }

  function buf() external returns (uint256) {
    return buf;
  }

  function «calc»() external returns (address) {
    return «calc»;
  }

  function chip() external returns (uint64) {
    return chip;
  }

  function chost() external returns (uint256) {
    return chost;
  }

  function count() external returns (uint256) {
    return active.length;
  }

  function cusp() external returns (uint256) {
    return cusp;
  }

  function deny(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 0;
  }

  function dog() external returns (address) {
    return dog;
  }

  function file(bytes32 what, uint256 data) external {
    require(wards[msg.sender] == 1);
    require(locked == 0);
    locked = 1;
    if (what == bytes32(0x6275660000000000000000000000000000000000000000000000000000000000)) {
      buf = data;
    } else if (what == bytes32(0x7461696c00000000000000000000000000000000000000000000000000000000)) {
      tail = data;
    } else if (what == bytes32(0x6375737000000000000000000000000000000000000000000000000000000000)) {
      cusp = data;
    } else if (what == bytes32(0x6368697000000000000000000000000000000000000000000000000000000000)) {
      chip = data % #uint64Modulus;
    } else if (what == bytes32(0x7469700000000000000000000000000000000000000000000000000000000000)) {
      tip = data % #uint192Modulus;
    } else if (what == bytes32(0x73746f7070656400000000000000000000000000000000000000000000000000)) {
      stopped = data;
    } else {
      require(false);
    }
    locked = 0;
  }

  function file(bytes32 what, address data) external {
    require(wards[msg.sender] == 1);
    require(locked == 0);
    locked = 1;
    if (what == bytes32(0x73706f7474657200000000000000000000000000000000000000000000000000)) {
      spotter = data;
    } else if (what == bytes32(0x646f670000000000000000000000000000000000000000000000000000000000)) {
      dog = data;
    } else if (what == bytes32(0x766f770000000000000000000000000000000000000000000000000000000000)) {
      vow = data;
    } else if (what == bytes32(0x63616c6300000000000000000000000000000000000000000000000000000000)) {
      «calc» = data;
    } else {
      require(false);
    }
    locked = 0;
  }

  function getStatus(uint256 id) external returns (bool, uint256, uint256, uint256) {
    address usr = sales[id].usr;
    uint96 tic = sales[id].tic;
    var st = status(tic, sales[id].top);
    bool done = st.0;
    uint256 price = st.1;
    bool needsRedo = usr != address(0) && done;
    return (needsRedo, price, sales[id].lot, sales[id].tab);
  }

  function ilk() external returns (bytes32) {
    return ${ilkExpr v};
  }

  function kick(uint256 tab, uint256 lot, address usr, address kpr) external returns (uint256) {
    require(wards[msg.sender] == 1);
    require(locked == 0);
    locked = 1;
    require(stopped < 1);
    require(tab > 0);
    require(lot > 0);
    require(usr != address(0));
    uint256 id = (kicks + 1) % #wordModulus;
    kicks = id;
    require(id > 0);
    active.push(id);
    uint256 activePos = (active.length - 1) % #wordModulus;
    sales[id].pos = activePos;
    sales[id].tab = tab;
    sales[id].lot = lot;
    sales[id].usr = usr;
    sales[id].tic = block.timestamp % #uint96Modulus;
    var feedPrice = getFeedPrice();
    var top = rmul(feedPrice, buf);
    require(top > 0);
    sales[id].top = top;
    uint256 _tip = tip;
    uint256 _chip = chip;
    uint256 coin = 0;
    if (_tip > 0 || _chip > 0) {
      var chipCoin = wmul(tab, _chip);
      uint256 coinNew = (_tip + chipCoin) as uint256;
      require(coinNew >= _tip);
      coin = coinNew;
      ${checkedExternalCallStmts (vatExpr v) "suck" (.intLit 0)
        [.storage vowRef, .var "kpr", .var "coin"] "_suckRet"}
    }
    locked = 0;
    return id;
  }

  function kicks() external returns (uint256) {
    return kicks;
  }

  function list() external returns (uint256[]) {
    return active;
  }

  function redo(uint256 id, address kpr) external {
    require(locked == 0);
    locked = 1;
    require(stopped < 2);
    address usr = sales[id].usr;
    uint96 tic = sales[id].tic;
    uint256 top = sales[id].top;
    require(usr != address(0));
    var st = status(tic, top);
    require(st.0);
    uint256 tab = sales[id].tab;
    uint256 lot = sales[id].lot;
    sales[id].tic = block.timestamp % #uint96Modulus;
    var feedPrice = getFeedPrice();
    var topNew = rmul(feedPrice, buf);
    require(topNew > 0);
    sales[id].top = topNew;
    uint256 _tip = tip;
    uint256 _chip = chip;
    if (_tip > 0 || _chip > 0) {
      uint256 _chost = chost;
      if (tab >= _chost) {
        uint256 lotFeed = (lot * feedPrice) as uint256;
        require(feedPrice == 0 || lotFeed / feedPrice == lot);
        if (lotFeed >= _chost) {
          var chipCoin = wmul(tab, _chip);
          uint256 coin = (_tip + chipCoin) as uint256;
          require(coin >= _tip);
          ${checkedExternalCallStmts (vatExpr v) "suck" (.intLit 0)
            [.storage vowRef, .var "kpr", .var "coin"] "_suckRet"}
        }
      }
    }
    locked = 0;
  }

  function rely(address usr) external {
    require(wards[msg.sender] == 1);
    wards[usr] = 1;
  }

  function sales(uint256 arg0) external returns (uint256, uint256, uint256, address, uint96, uint256) {
    return (sales[arg0].pos, sales[arg0].tab, sales[arg0].lot,
            sales[arg0].usr, sales[arg0].tic, sales[arg0].top);
  }

  function spotter() external returns (address) {
    return spotter;
  }

  function stopped() external returns (uint256) {
    return stopped;
  }

  function tail() external returns (uint256) {
    return tail;
  }

  function take(uint256 id, uint256 amt, uint256 max, address who, bytes memory data) external {
    require(locked == 0);
    locked = 1;
    require(stopped < 3);
    address usr = sales[id].usr;
    uint96 tic = sales[id].tic;
    require(usr != address(0));
    var st = status(tic, sales[id].top);
    bool done = st.0;
    uint256 price = st.1;
    require(!done);
    require(max >= price);
    uint256 lot = sales[id].lot;
    uint256 tab = sales[id].tab;
    var slice = min(lot, amt);
    uint256 owe0 = (slice * price) as uint256;
    require(price == 0 || owe0 / price == slice);
    uint256 owe = owe0;
    if (owe > tab) {
      owe = tab;
      slice = owe / price;
    } else {
      if (owe < tab && slice < lot) {
        uint256 _chost = chost;
        uint256 remainingTab = (tab - owe) % #wordModulus;
        if (remainingTab < _chost) {
          require(tab > _chost);
          uint256 oweAdjusted = (tab - _chost) % #wordModulus;
          owe = oweAdjusted;
          slice = owe / price;
        }
      }
    }
    uint256 tabNew = (tab - owe) % #wordModulus;
    uint256 lotNew = (lot - slice) % #wordModulus;
    tab = tabNew;
    lot = lotNew;
    ${checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
      [ilkExpr v, thisAddr, .var "who", .var "slice"] "_fluxBuyerRet"}
    address dog_ = dog;
    if (data.length > 0 && who != ${vatExpr v} && who != dog_) {
      require(who.code.length > 0);
      var _clipperCallRet = who.clipperCall(msg.sender, owe, slice, data);
    }
    ${checkedExternalCallStmts (vatExpr v) "move" (.intLit 0)
      [sender, .storage vowRef, .var "owe"] "_moveRet"}
    if (lot == 0) {
      uint256 digsAmt = (tab + owe) % #wordModulus;
      require(dog_.code.length > 0);
      var _digsRet = dog_.digs(${ilkExpr v}, digsAmt);
    } else {
      require(dog_.code.length > 0);
      var _digsRet = dog_.digs(${ilkExpr v}, owe);
    }
    if (lot == 0) {
      var _removeRet = _remove(id);
    } else {
      if (tab == 0) {
        ${checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet"}
        var _removeRet2 = _remove(id);
      } else {
        sales[id].tab = tab;
        sales[id].lot = lot;
      }
    }
    locked = 0;
  }

  function tip() external returns (uint192) {
    return tip;
  }

  function upchost() external {
    ${checkedExternalCallStmts (vatExpr v) "vatIlks" (.intLit 0) [ilkExpr v] "vatIlk"}
    uint256 _dust = ${Expr.tupleGet (Expr.var "vatIlk") 4};
    require(dog.code.length > 0);
    var chop = dog.chop(${ilkExpr v});
    var chostNew = wmul(_dust, chop);
    chost = chostNew;
  }

  function vat() external returns (address) {
    return ${vatExpr v};
  }

  function vow() external returns (address) {
    return vow;
  }

  function wards(address arg0) external returns (uint256) {
    return wards[arg0];
  }

  function yank(uint256 id) external {
    require(wards[msg.sender] == 1);
    require(locked == 0);
    locked = 1;
    require(sales[id].usr != address(0));
    require(dog.code.length > 0);
    var _digsRet = dog.digs(${ilkExpr v}, sales[id].tab);
    ${checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
      [ilkExpr v, thisAddr, sender, .storage (salesF (.var "id") "lot")] "_fluxRet"}
    var _removeRet = _remove(id);
    locked = 0;
  }
}

theorem contractSyntax_eq (v : ClipperImmutables) :
    contractSyntax v = Benchmarks.Dss.Clipper.contract v := by rfl

end Benchmarks.Dss.Clipper.Syntax
