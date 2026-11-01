-- [volar_ir]: external types.
-- Seeded by hax from Extraction/TypesExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
import VolarIrCommon.Extraction
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

/-- Model of the `volar_provenance::ProvenanceHandler` trait dictionary. The
aeneas extraction of the real trait emits a duplicate `corecloneCloneInst`
field (multi-Clone-bound naming bug), so it cannot be extracted; the dict is
only ever consumed, never constructed, in the extracted surface. Field names
match the generated call sites (`map`, `gate_degree`). -/
structure volar_provenance.ProvenanceHandler (Self : Type) (P : Type)
    (Self_Output : Type) where
  cloneP : core.clone.Clone P
  cloneOut : core.clone.Clone Self_Output
  map : Self → P → RustM Self_Output
  gate_degree : Self → P → RustM Std.Usize
