-- [volar_ir_common]: external types.
-- Seeded by hax from Extraction/TypesExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
import VolarSide.Extraction
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


namespace volar_ir_common

/-- Opaque model of Rust `volar_ir_common::complexity::MeasureSpec`. The Rust
enum recurses through `Vec` (Digits) and through `(usize, MeasureSpec)` pairs
(Structural), which is not a strictly-positive occurrence for the Lean
kernel, so the extracted inductive cannot be emitted. Abstract until a
mutual-inductive model is written (plan §8 M2 coverage work). -/
axiom complexity.MeasureSpec : Type

end volar_ir_common

namespace CoreModels.alloc

/-- Model of Rust `alloc::collections::btree_map::BTreeMap`: an association
list, ordered by key (matching BTreeMap's iteration-order contract). The
allocator parameter is present but not modeled (the model is
allocator-agnostic). -/
abbrev collections.btree.map.BTreeMap (K V A : Type) : Type := List (K × V)

end CoreModels.alloc
