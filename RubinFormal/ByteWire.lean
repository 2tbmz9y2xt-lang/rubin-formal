import RubinFormal.ByteWireLegacy

/-
Deprecated compatibility shim.

`RubinFormal.ByteWire` no longer carries the legacy toy `CompactSize` model directly,
because the old unqualified names were easy to confuse with the real proof surface.

- Use `RubinFormal.ByteWireV2` for the byte-accurate parser/CompactSize theorems that
  back current wire claims.
- Use `RubinFormal.ByteWireLegacy` only when a proof explicitly needs the toy
  bootstrap model restricted to the single-byte `CompactSize` case.
-/
