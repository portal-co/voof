//! MINIMAL volar-spec lib.rs for voof extraction (replaces the real lib.rs
//! in the scratch checkout only — see sources-patches/volar/apply.sh).
//!
//! The real crate pulls in hybrid_array (untranslatable mutual recursion)
//! across ~14 modules. Extraction scenarios each cover a narrow module set;
//! this root only declares what the current scenarios need. Extend the
//! module list as scenarios grow.
#![no_std]

extern crate alloc;

pub mod array;
pub use array::{Array, ArraySize};

/// Minimal digest trait replacing `digest::Digest` in extracted code: the
/// real trait's `Output` type is hardwired to `hybrid_array::Array` (via
/// crypto-common), which Aeneas cannot translate. Same shape: new/update/
/// finalize, with the output length tracked by our shim's `Array`.
pub trait SpecDigest<N: ArraySize> {
    /// Fresh digest state.
    fn new() -> Self;
    /// Absorb bytes. Takes `impl AsRef<[u8]>` like `digest::Digest` so spec
    /// call sites (byte literals, `&Array`, byte arrays) work unmodified.
    fn update(&mut self, data: impl AsRef<[u8]>);
    /// Finalize into an `N`-sized digest.
    fn finalize(self) -> Array<u8, N>;
}

/// Trimmed to the marker trait `volar_spec::garble` needs. The real module
/// tree (memory/bridge/poly/setup/…) uses the full hybrid_array API and is
/// out of scope for current scenarios.
pub mod vole {
    /// Marker: array sizes usable for VOLE arrays.
    pub trait VoleArray<T>: crate::ArraySize {}
    impl<T, X: crate::ArraySize> VoleArray<T> for X {}
}

pub mod garble;
