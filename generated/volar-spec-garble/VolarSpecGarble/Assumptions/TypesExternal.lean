-- [volar_spec]: external types.
-- Seeded by hax from Extraction/TypesExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048


/- typenum models (foreign crate, reached through the array shim's
   `ArraySize: typenum::Unsigned` bound). Only the pieces the extraction
   references: the marker types and the `Unsigned` dictionary's USIZE. -/

/-- Model of `typenum::uint::UTerm` (zero-size type-level marker). -/
structure typenum.uint.UTerm where

/-- Model of `typenum::uint::UInt` (type-level binary natural). -/
structure typenum.uint.UInt (U : Type) (B : Type) where

/-- Model of `typenum::bit::B0`. -/
structure typenum.bit.B0 : Type where

/-- Model of `typenum::bit::B1`. -/
structure typenum.bit.B1 : Type where

/-- Model of `typenum::marker_traits::Unsigned`. `USIZE` is a RustM
computation, as Aeneas models associated constants; the `Copy` supertrait
dictionary is included (the extraction projects it). -/
structure typenum.marker_traits.Unsigned (Self : Type) where
  coremarkerCopyInst : core.marker.Copy Self
  USIZE : RustM Std.Usize
