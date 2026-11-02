-- [volar_spec]: external functions.
-- Seeded by hax from Extraction/FunsExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
import VolarSpecGarble.Extraction.Types
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
open volar_spec

/-- [volar_spec::garble::{impl core::fmt::Debug for volar_spec::garble::GramOutput}::fmt]:
    Source: 'crates/spec/volar-spec/src/garble.rs', lines 328:37-328:42
    Visibility: public -/
axiom garble.GramOutput.Insts.CoreFmtDebug.fmt
  :
  garble.GramOutput → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)


/-- Blanket `impl AsRef<U> for &T`: shared borrows are erased to values in
the extraction, so this is the identity dictionary transformer. -/
@[reducible]
def core.Shared0T.Insts.CoreConvertAsRef {T U : Type}
    (inner : core.convert.AsRef T U) : core.convert.AsRef T U := inner

/-- PhantomData Clone (model): it is `Unit` here, so clone is the identity. -/
def core.marker.PhantomData.Insts.CoreCloneClone.clone {T : Type}
    (self : core.marker.PhantomData T) : RustM (core.marker.PhantomData T) :=
  pure self

/-- Trait implementation (model). -/
@[reducible]
impl_def core.marker.PhantomData.Insts.CoreCloneClone {T : Type} :
    core.clone.Clone (core.marker.PhantomData T) := {
  clone := core.marker.PhantomData.Insts.CoreCloneClone.clone
  clone_from := core.clone.Clone.clone_from.default
    core.marker.PhantomData.Insts.CoreCloneClone
}

/-- Model of `<[T]>::split_first` (missing from the pinned CoreModels):
head/tail over the slice's list spine. -/
def core.slice.Slice.split_first {T : Type} (s : Slice T) :
    RustM (core.option.Option (T × Slice T)) := do
  match hv : s.val with
  | [] => ok core.option.Option.None
  | x :: rest =>
    ok (core.option.Option.Some (x, ⟨rest, by
      have h := s.property
      rw [hv] at h
      simp only [List.length_cons] at h
      omega⟩))
