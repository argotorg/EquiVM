import Solm.Notation

/-!
# RIPEMD-160 behavior in Solm

This is an executable Solm description of the RIPEMD-160 computation performed by the deployed
contract.  The fallback consumes raw calldata and returns the digest right-aligned in a 32-byte
word, matching the interface of the native precompile.
-/

open Solm Solm.Notation

namespace Ripemd160.Syntax

def contractSyntax : ContractDecl := solidity% contract Ripemd160Deployed {
  function f0(uint256 x, uint256 y, uint256 z) internal pure returns (uint256) {
    return (x ^ y) ^ z;
  }

  function f1(uint256 x, uint256 y, uint256 z) internal pure returns (uint256) {
    return (x & y) | ((~x) & z);
  }

  function f2(uint256 x, uint256 y, uint256 z) internal pure returns (uint256) {
    return (x | (~y)) ^ z;
  }

  function f3(uint256 x, uint256 y, uint256 z) internal pure returns (uint256) {
    return (x & z) | (y & (~z));
  }

  function f4(uint256 x, uint256 y, uint256 z) internal pure returns (uint256) {
    return x ^ (y | (~z));
  }

  function rotl32(uint256 x, uint256 n) internal pure returns (uint256) {
    return ((x << n) | (x >> (32 - n))) & 0xffffffff;
  }

  function wordRowL(uint256 g) internal pure returns (uint256) {
    if (g == 0) { return 0x0123456789abcdef; }
    if (g == 1) { return 0x74d1a6f3c0952eb8; }
    if (g == 2) { return 0x3ae49f812706db5c; }
    if (g == 3) { return 0x19ba08c4d37fe562; }
    return 0x40597c2ae138b6fd;
  }

  function rotRowL(uint256 g) internal pure returns (uint256) {
    if (g == 0) { return 0xbefc5879bdef6798; }
    if (g == 1) { return 0x768db97f7cf9b7dc; }
    if (g == 2) { return 0xbd67e9dfe8d65c75; }
    if (g == 3) { return 0xbcefef989e56865c; }
    return 0x9f5b68dc5cdeb856;
  }

  function wordRowR(uint256 g) internal pure returns (uint256) {
    if (g == 0) { return 0x5e7092b4d6f81a3c; }
    if (g == 1) { return 0x6b370d5aef8c4912; }
    if (g == 2) { return 0xf5137e69b8c2a04d; }
    if (g == 3) { return 0x86413bf05c2d97ae; }
    return 0xcfa4158762de039b;
  }

  function rotRowR(uint256 g) internal pure returns (uint256) {
    if (g == 0) { return 0x899bdff5778beec6; }
    if (g == 1) { return 0x9df7c89b77c76fdb; }
    if (g == 2) { return 0x97fb866ecd5edd75; }
    if (g == 3) { return 0xf58bee6e69c9c5f8; }
    return 0x85c9c5e68d65fdbb;
  }

  function nibble(uint256 row, uint256 idx) internal pure returns (uint256) {
    return (row >> (60 - idx * 4)) & 15;
  }

  function paddedByte(
    bytes memory data,
    uint256 pos,
    uint256 bitLen,
    uint256 paddedLen
  ) internal pure returns (uint256) {
    if (pos < data.length) {
      return uint8(data[pos]);
    }
    if (pos == data.length) {
      return 128;
    }
    if (pos >= paddedLen - 8) {
      return (bitLen >> (8 * (pos - (paddedLen - 8)))) & 255;
    }
    return 0;
  }

  function swap32(uint256 x) internal pure returns (uint256) {
    return ((x & 0xff) << 24)
      | (((x >> 8) & 0xff) << 16)
      | (((x >> 16) & 0xff) << 8)
      | ((x >> 24) & 0xff);
  }

  function hash(bytes memory data) internal pure returns (bytes20) {
    uint256 mask32 = 0xffffffff;
    uint256 dataLen = data.length;
    uint256 bitLen = dataLen * 8;
    uint256 paddedLen = ((dataLen + 72) / 64) * 64;
    uint256 numBlocks = paddedLen / 64;

    uint256 h0 = 0x67452301;
    uint256 h1 = 0xefcdab89;
    uint256 h2 = 0x98badcfe;
    uint256 h3 = 0x10325476;
    uint256 h4 = 0xc3d2e1f0;
    uint256[] memory words = new uint256[](16);

    for (uint256 blk = 0; blk < numBlocks; blk = blk + 1) {
      for (uint256 wordNo = 0; wordNo < 16; wordNo = wordNo + 1) {
        uint256 off = blk * 64 + wordNo * 4;
        uint256 b0 = paddedByte(data, off, bitLen, paddedLen);
        uint256 b1 = paddedByte(data, off + 1, bitLen, paddedLen);
        uint256 b2 = paddedByte(data, off + 2, bitLen, paddedLen);
        uint256 b3 = paddedByte(data, off + 3, bitLen, paddedLen);
        words[wordNo] = b0 | (b1 << 8) | (b2 << 16) | (b3 << 24);
      }

      uint256 al = h0;
      uint256 bl = h1;
      uint256 cl = h2;
      uint256 dl = h3;
      uint256 el = h4;

      for (uint256 groupL = 0; groupL < 5; groupL = groupL + 1) {
        uint256 wordTableL = wordRowL(groupL);
        uint256 rotTableL = rotRowL(groupL);
        uint256 kL = 0;
        if (groupL == 1) { kL = 0x5a827999; }
        if (groupL == 2) { kL = 0x6ed9eba1; }
        if (groupL == 3) { kL = 0x8f1bbcdc; }
        if (groupL == 4) { kL = 0xa953fd4e; }

        for (uint256 roundL = 0; roundL < 16; roundL = roundL + 1) {
          uint256 fL = 0;
          if (groupL == 0) {
            uint256 fL0 = f0(bl, cl, dl);
            fL = fL0;
          }
          if (groupL == 1) {
            uint256 fL1 = f1(bl, cl, dl);
            fL = fL1;
          }
          if (groupL == 2) {
            uint256 fL2 = f2(bl, cl, dl);
            fL = fL2;
          }
          if (groupL == 3) {
            uint256 fL3 = f3(bl, cl, dl);
            fL = fL3;
          }
          if (groupL == 4) {
            uint256 fL4 = f4(bl, cl, dl);
            fL = fL4;
          }
          uint256 idxL = roundL % 16;
          uint256 wordIdxL = nibble(wordTableL, idxL);
          uint256 shiftL = nibble(rotTableL, idxL);
          uint256 sumL = (al + (fL & mask32) + words[wordIdxL] + kL) & mask32;
          uint256 rotatedL = rotl32(sumL, shiftL);
          uint256 nextL = (rotatedL + el) & mask32;
          uint256 clRot = rotl32(cl, 10);
          al = el;
          el = dl;
          dl = clRot;
          cl = bl;
          bl = nextL;
        }
      }

      uint256 ar = h0;
      uint256 br = h1;
      uint256 cr = h2;
      uint256 dr = h3;
      uint256 er = h4;

      for (uint256 groupR = 0; groupR < 5; groupR = groupR + 1) {
        uint256 wordTableR = wordRowR(groupR);
        uint256 rotTableR = rotRowR(groupR);
        uint256 kR = 0x50a28be6;
        if (groupR == 1) { kR = 0x5c4dd124; }
        if (groupR == 2) { kR = 0x6d703ef3; }
        if (groupR == 3) { kR = 0x7a6d76e9; }
        if (groupR == 4) { kR = 0; }

        for (uint256 roundR = 0; roundR < 16; roundR = roundR + 1) {
          uint256 fR = 0;
          if (groupR == 0) {
            uint256 fR0 = f4(br, cr, dr);
            fR = fR0;
          }
          if (groupR == 1) {
            uint256 fR1 = f3(br, cr, dr);
            fR = fR1;
          }
          if (groupR == 2) {
            uint256 fR2 = f2(br, cr, dr);
            fR = fR2;
          }
          if (groupR == 3) {
            uint256 fR3 = f1(br, cr, dr);
            fR = fR3;
          }
          if (groupR == 4) {
            uint256 fR4 = f0(br, cr, dr);
            fR = fR4;
          }
          uint256 idxR = roundR % 16;
          uint256 wordIdxR = nibble(wordTableR, idxR);
          uint256 shiftR = nibble(rotTableR, idxR);
          uint256 sumR = (ar + (fR & mask32) + words[wordIdxR] + kR) & mask32;
          uint256 rotatedR = rotl32(sumR, shiftR);
          uint256 nextR = (rotatedR + er) & mask32;
          uint256 crRot = rotl32(cr, 10);
          ar = er;
          er = dr;
          dr = crRot;
          cr = br;
          br = nextR;
        }
      }

      uint256 nextH0 = (h1 + cl + dr) & mask32;
      uint256 nextH1 = (h2 + dl + er) & mask32;
      uint256 nextH2 = (h3 + el + ar) & mask32;
      uint256 nextH3 = (h4 + al + br) & mask32;
      uint256 nextH4 = (h0 + bl + cr) & mask32;
      h0 = nextH0;
      h1 = nextH1;
      h2 = nextH2;
      h3 = nextH3;
      h4 = nextH4;
    }

    uint256 r0 = swap32(h0);
    uint256 r1 = swap32(h1);
    uint256 r2 = swap32(h2);
    uint256 r3 = swap32(h3);
    uint256 r4 = swap32(h4);
    uint256 digest = (r0 << 128) | (r1 << 96) | (r2 << 64) | (r3 << 32) | r4;
    return bytes20(digest);
  }

  fallback(bytes calldata data) external returns (bytes) {
    require(data.length <= 18446744073709551424);
    bytes20 digest = hash(data);
    return abi.encodePacked(uint96(0), bytes20(digest));
  }
}

end Ripemd160.Syntax
