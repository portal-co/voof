-- [volar_side]: external functions.
-- Seeded by hax from Extraction/FunsExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
import VolarSide.Extraction.Types
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
open volar_side

/-- [volar_side::generated::{impl core::fmt::Debug for volar_side::generated::SideId}::fmt]:
    Source: 'crates/ir/volar-side/src/generated.rs', lines 9:60-9:65
    Visibility: public -/
-- Aeneas computes a borrow back-reference triple for the opaque fmt; the
-- core.fmt.Debug model wants a pair. Debug formatting is immaterial to our
-- proofs, so model it as a no-op write (cf. U8.Insts.CoreFmtDebug.fmt).
def generated.SideId.Insts.CoreFmtDebug.fmt
  :
  generated.SideId → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter) := fun _ f =>
  ok (core.result.Result.Ok (), f)

