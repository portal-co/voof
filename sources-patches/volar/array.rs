//! Aeneas-friendly stand-in for `hybrid_array`, used ONLY by voof's
//! extraction patch (see `sources-patches/volar/apply.sh` in the voof repo).
//!
//! `hybrid_array::Array<T, N>` is mutually recursive with the
//! `ArraySize`/`AssocArraySize` traits (typenum-linked encoding), which
//! Aeneas cannot translate. This module provides the same surface over a
//! `Vec` spine with `N` kept only as a length marker via
//! `typenum::Unsigned`, so the spec extracts cleanly. It is semantically
//! equivalent for the spec's purposes: a fixed-length byte/element vector.
//!
//! Divergence from the real `hybrid_array`, tracked for the equivalence
//! work: lengths are not type-checked at compile time here (construction
//! sites still use `N::USIZE`), and the real crate's `AsRef`/layout
//! guarantees are not modeled.

extern crate alloc;

use alloc::vec::Vec;
use core::marker::PhantomData;
use core::ops::{Index, IndexMut};

pub use hybrid_array::typenum;

/// Size aliases used in volar-spec (mirrors `hybrid_array::sizes`).
pub mod sizes {
    pub use hybrid_array::typenum::{U16, U100};
}

/// Size marker, replacing `hybrid_array::ArraySize`. Keeps the typenum
/// linkage (`Unsigned::USIZE`) without the mutually recursive traits.
pub trait ArraySize: typenum::Unsigned {}
impl<T: typenum::Unsigned> ArraySize for T {}

/// Fixed-length array, Vec-backed. `N` is a phantom length marker.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Array<T, N: ArraySize> {
    data: Vec<T>,
    _n: PhantomData<N>,
}

impl<T, N: ArraySize> Array<T, N> {
    /// Build from a per-index function (spec-construction primitive).
    pub fn from_fn(mut f: impl FnMut(usize) -> T) -> Self {
        let mut data = Vec::new();
        let mut i = 0;
        while i < N::USIZE {
            data.push(f(i));
            i += 1;
        }
        Array { data, _n: PhantomData }
    }

    /// View as a slice.
    pub fn as_slice(&self) -> &[T] {
        &self.data
    }

    /// View as a mutable slice.
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.data
    }
}

impl<T: Default + Clone, N: ArraySize> Default for Array<T, N> {
    fn default() -> Self {
        let mut data = Vec::new();
        let mut i = 0;
        while i < N::USIZE {
            data.push(T::default());
            i += 1;
        }
        Array { data, _n: PhantomData }
    }
}

impl<T, N: ArraySize> Index<usize> for Array<T, N> {
    type Output = T;
    fn index(&self, i: usize) -> &T {
        &self.data[i]
    }
}

impl<T, N: ArraySize> IndexMut<usize> for Array<T, N> {
    fn index_mut(&mut self, i: usize) -> &mut T {
        &mut self.data[i]
    }
}

impl<T, N: ArraySize> AsRef<[T]> for Array<T, N> {
    fn as_ref(&self) -> &[T] {
        &self.data
    }
}

impl<T, N: ArraySize> AsMut<[T]> for Array<T, N> {
    fn as_mut(&mut self) -> &mut [T] {
        &mut self.data
    }
}

impl<T: Clone, N: ArraySize> TryFrom<&[T]> for Array<T, N> {
    type Error = core::convert::Infallible;
    fn try_from(data: &[T]) -> Result<Self, Self::Error> {
        Ok(Array { data: data.to_vec(), _n: PhantomData })
    }
}
