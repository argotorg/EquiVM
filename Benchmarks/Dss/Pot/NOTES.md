# Pot proof working notes (agent)

Compiler: solc 0.6.12 --optimize --optimize-runs 200 --metadata-hash none. Runtime 2595 bytes.
Template: **Benchmarks/Dss/Jug** (fully proved sibling; shares _rpow/_rmul/_add/_sub/_mul, DSS auth,
external calls, binary-search dispatch). READ Jug, do not import/build it; reprove in Pot/, flag
contract-independent lemmas for Reasoning/ promotion.

## Phase 0 verdict: SPEC IS FAITHFUL (dispatch, storage order, math helpers, external calls all match)

## Storage layout (slots)
wards 0 (mapping addr→uint), pie 1 (mapping addr→uint), Pie 2, dsr 3, chi 4, vat 5 (addr),
vow 6 (addr), rho 7, live 8.  ONE = 10^27 = 0x33b2e3c9fd0803ce8000000.

## Dispatch tree (binary search, depth 2). selector -> dispatch-body PC
Root@32 pivot 0x65fae35e (GT): sel<pivot -> 162 ; else -> 43
 @43 pivot 0x9c52a7f1 (GT): sel<piv -> 113 ; else -> 54 (linear)
 @162 pivot 0x2c69ed58 (GT): sel<piv -> 222 ; else -> 174 (linear)
Groups (linear scan leaves):
 @222 (sel<0x2c69ed58):  049878f3 join@272 | 0bebac86 pie@303 | 20aba08b rho@359 | 29ae8114 file_bu@367
 @174 (0x2c69ed58..0x65fae35e): 2c69ed58 Pie@402 | 36569e77 vat@410 | 487bf082 dsr@446 | 626cb3c5 vow@454
 @113 (0x65fae35e..0x9c52a7f1): 65fae35e rely@462 | 69245009 cage@500 | 7f8661a1 exit@508 | 957aa58c live@537
 @54  (sel>=0x9c52a7f1): 9c52a7f1 deny@545 | 9f678cca drip@583 | bf353dbb wards@591 | c92aecc4 chi@629 | d4e8be83 file_ba@637
No-match revert JUMPDEST @267.  Global: callvalue guard @16 revert; calldatasize<4 -> 267.

## Selectors (17) — cast/keccak verified
join(uint256) 049878f3 | pie(address) 0bebac86 | rho() 20aba08b | file(bytes32,uint256) 29ae8114
Pie() 2c69ed58 | vat() 36569e77 | dsr() 487bf082 | vow() 626cb3c5 | rely(address) 65fae35e
cage() 69245009 | exit(uint256) 7f8661a1 | live() 957aa58c | deny(address) 9c52a7f1 | drip() 9f678cca
wards(address) bf353dbb | chi() c92aecc4 | file(bytes32,address) d4e8be83
External: move(address,address,uint256) bb35783b | suck(address,address,uint256) f24e23eb

## Function LOGIC block PCs (dispatch body -> logic)
join body@272 -> decode uint256 -> logic@681 (0x2a9), ret@301(STOP)
exit body@508 -> decode uint256 -> logic@1602 (0x642), ret@301(STOP)
drip body@583 -> logic@1819 (0x71b), ret@341(0x155)
file_bu body@367, file_ba body@637, cage body@500, rely@462, deny@545 (auth writers)

## Math helper block PCs (shared epilogue 0x8f6=2294: SWAP3 SWAP2 POP POP JUMP)
_add @2278 (0x8e6): z=x+y; require z>=x
_mul @2300 (0x8fc): require y==0 || (x*y)/y==x ; z=x*y   (INVALID div-guard @2323)
_sub @2336 (0x920): z=x-y; require z<=x
_rpow@2352 (0x930): loop head @2395(0x95b); x==0 case @2512(0x9d0); return epilogue @2534(0x9e6)
  odd/even z-init @2379(0x94b)/@2383(0x94f); loop-odd branch skip @2495(0x9bf); loop exit @2506(0x9ca)
_rmul@2542 (0x9ee): z=_mul(x,y)/ONE (calls _mul@2300, div-guard INVALID @2573)

## join logic@681 order: req(now==rho)@682 | load pie[snd](kec snd++1)@758 _add write pie[snd]@783
  | load Pie@800 _add write Pie@812 | load vat,chi _mul move(snd,this,rad) selector bb35783b
## exit logic@1602: load pie[snd] _sub write pie[snd] | load Pie _sub write Pie | _mul move(this,snd,rad)
## drip logic@1819: req(now>=rho) | _rpow(dsr,now-rho,ONE)@1894 | _rmul(pow,chi)@1926 | _sub(tmp,chi)@1937
  | write chi=tmp@1950 | write rho=now@1956 | load vat,vow,Pie _mul(Pie,chi_) suck(vow,this,rad) f24e23eb ret tmp

## Jug reuse map (files to mirror)
Common/Trusted/Bytecode-selfacts, Dispatch (adapt depth-2), getters via RD.solcWordGetterExternal /
RD.solcAddressGetterExternal + solcZeroSlotMappingGetter (LIBRARY CANDIDATE in Jug Common),
Rpow/RpowGeneric/ArithmeticRpowLoop (loop induction), Drip* (internal-call composition + external call).

## Getter (entry,returnPc,routine,slot) + dispatch group/arm  [returnPc: uint256=341, addr=418]
Pie   sel0  entry402 ret341 routine1330 slot2  grp@174 arm0  0x2c69ed58
chi   sel2  entry629 ret341 routine2137 slot4  grp@54  arm3  0xc92aecc4
dsr   sel5  entry446 ret341 routine1351 slot3  grp@174 arm2  0x487bf082
rho   sel13 entry359 ret341 routine984  slot7  grp@223 arm2  0x20aba08b
live  sel10 entry537 ret341 routine1698 slot8  grp@114 arm3  0x957aa58c
vat   sel14 entry410 ret418 routine1336 slot5(addr) grp@174 arm1  0x36569e77
vow   sel15 entry454 ret418 routine1357 slot6(addr) grp@174 arm3  0x626cb3c5
pie   sel11 entry303 ret341 routine966(map slot1) grp@223 arm1  0x0bebac86  [solcSingleMappingGetter ⟨1⟩]
wards sel16 entry591 ret341 routine2119(map slot0) grp@54  arm2  0xbf353dbb  [solcZeroSlotMappingGetter]
## Mutating (entry -> logic PC)  ret STOP=301 (drip ret 341)
rely  sel12 entry462 grp@114 arm0  logic1372
deny  sel3  entry545 grp@54  arm0  logic1704
cage  sel1  entry500 grp@114 arm1  logic1490
file_bu sel7 entry367 grp@223 arm3 logic990
file_ba sel8 entry637 grp@54  arm4 logic2143
join  sel9  entry272 grp@223 arm0 logic681
exit  sel6  entry508 grp@114 arm2 logic1602
drip  sel4  entry583 grp@54  arm1 logic1819
## Group arm order: @223[join,pie,rho,file_bu] @174[Pie,vat,dsr,vow] @114[rely,cage,exit,live] @54[deny,drip,wards,chi,file_ba]
## Root pivot 0x65fae35e; split163 pivot 0x2c69ed58; split43 pivot 0x9c52a7f1

## Auth-write / setter logic PCs (all auth funcs: CALLER kec(caller++0) SLOAD PUSH1 1 EQ PUSH2 <authOK> JUMPI else inline revert "Pot/not-authorized" 0x141bdd0bdb9bdd...)
rely  logic1372 authOK->1461 : store wards[guy]=1 @1461 (mask,kec(guy++0),PUSH1 1,SSTORE,JUMP->ret301)
deny  logic1704 authOK->1793 : store wards[guy]=0 @1793 (mask,kec(guy++0),SSTORE,JUMP->ret301)
cage  logic1490 authOK->1579 : live(8)=0 @1580, dsr(3)=ONE @1598, JUMP->ret301
file_bu logic990  authOK->1079 : then require live==1, require now==rho, if what=="dsr" dsr=data else revert. decode(bytes32,uint256): entry367 decoded 389(=367+22)
file_ba logic2143 authOK->?    : if what=="vow" vow=addr else revert. decode(bytes32,address): entry637 decoded 659(=637+22)
_rpow: Pot block @2352 == Jug block @2153 (offset +199), IDENTICAL opcode structure. Jug uses Solm var "b", Pot uses "base".
  Jug _rpow files: Rpow.lean(1593) RpowGeneric.lean(440) ArithmeticRpowLoop.lean(340). Source lemmas rename b->base; bytecode PCs +199.
## internal-fn ExecFuncBody pattern: `ExecFuncBody config {contract,locals} evm fn.body (.returned {..} evm (some [val]))` ; callers use internalCallFunctionReturn/Revert

## Constructor (creation bytecode, 2746 bytes) — SPEC FAITHFUL
prologue 0-15 nonpayable; 16-52 CODECOPY+decode vat_ arg (appended after initcode, len check @43->51);
53 MLOAD vat_; 54-74 wards[caller]=1 (slot0 kec(caller++0)); 75-108 vat=vat_ (slot5 addr pack);
109-126 dsr(3)=ONE chi(4)=ONE (PUSH12 ONE reused); 130-133 rho(7)=now(TIMESTAMP); 134-136 live(8)=1;
137-149 CODECOPY runtime (size 0xa23=2595) from offset 0x97=151, RETURN. Runtime deployed @151.
Store order matches spec: wards,vat,dsr,chi,rho,live. Jug Constructor*.lean templates. constructorEquivalence.
