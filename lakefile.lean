import Lake
open Lake DSL

package rubinFormal where
  -- Keep the project Std-only (no Mathlib) to reduce friction in early development.
  -- When the external repo is created, we can add Mathlib and pin it via lake-manifest.json.

lean_lib RubinFormal where
  roots := #[`RubinFormal]

