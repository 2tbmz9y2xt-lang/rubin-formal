import Std
import RubinFormal.CompactSize

namespace RubinFormal

abbrev Byte := UInt8
abbrev Bytes := List Byte

def leBytesOfNat (n : Nat) : Nat → Bytes
  | 0 => []
  | (k + 1) => UInt8.ofNat (n % 256) :: leBytesOfNat (n / 256) k

def u16le (x : UInt16) : Bytes :=
  leBytesOfNat x.toNat 2

def u32le (x : UInt32) : Bytes :=
  leBytesOfNat x.toNat 4

def u64le (x : UInt64) : Bytes :=
  leBytesOfNat x.toNat 8

def bytes32? (bs : Bytes) : Bool :=
  bs.length = 32

def encCompactSize (n : Nat) : Option Bytes :=
  encodeCompactSize n

def concat (xss : List Bytes) : Bytes :=
  xss.foldl (fun acc xs => acc ++ xs) []

end RubinFormal

