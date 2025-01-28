# A lockstep iterator adaptor
The *lockstep* iterator adaptor is an adapter similar to [`zip`](core::iter::zip), but instead
uses a control flow closure to selectively skip elements from either the left or the right
iterator, or yield the pair. This adaptor is primarily useful when working with sorted data.

The main entrypoint is the [`lockstep`] function; see its documentation for more detail and
examples.

This crate is `#![no_std]` and `#![forbid(unsafe_code)]`.

## Examples
Re-implement [`zip`](core::iter::zip).
```rust
use lockstep::{lockstep, Control};

pub fn zip<L, R>(left: L, right: R) -> impl Iterator<Item = (L::Item, R::Item)>
where
    L: IntoIterator,
    R: IntoIterator,
{
    lockstep(left.into_iter(), right.into_iter(), |_, _| Control::Yield)
}
```
Compose two sorted iterators to only yield elements which they have in common.
```rust
use core::cmp::Ordering;

use lockstep::{lockstep, Control};

/// Assumes that `left` and `right` are sorted.
pub fn intersection<L, R, T>(left: L, right: R) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    T: Ord,
{
    lockstep(left.into_iter(), right.into_iter(), |l, r| {
        match l.cmp(r) {
            Ordering::Less => Control::SkipLeft,
            Ordering::Equal => Control::Yield,
            Ordering::Greater => Control::SkipRight,
        }
    })
    .map(|(l, _)| l)
}
```
