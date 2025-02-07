//! # A lockstep iterator adaptor
//! The *lockstep* iterator adaptor is an adapter similar to [`zip`](core::iter::zip), but instead
//! uses a control flow closure to selectively skip elements from either the left or the right
//! iterator, or yield the pair. This adaptor is primarily useful when working with sorted data.
//!
//! The main entrypoint is the [`lockstep`] function; see its documentation for more detail and
//! examples.
//!
//! This crate is `#![no_std]` and `#![forbid(unsafe_code)]`.

#![deny(missing_docs)]
#![forbid(unsafe_code)]
#![no_std]

/// Returns a new [`Lockstep`] iterator adaptor.
///
/// The closure is called for each pair `(l, r)`:
/// - If [`Control::SkipLeft`] is returned, `l` is replaced by the next element from the left iterator
///   (if any).
/// - If [`Control::SkipRight`] is returned, `r` is replaced by the next element from the right iterator
///   (if any). If
/// - If [`Control::Yield`] is returned, `(l, r)` is returned as an element in the resulting
///   iterator.
///
/// If either internal iterator is exhausted, this iterator terminates.
///
/// ## Examples
/// Re-implement [`zip`](core::iter::zip).
/// ```
/// use lockstep::{lockstep, Control};
///
/// pub fn zip<L, R>(left: L, right: R) -> impl Iterator<Item = (L::Item, R::Item)>
/// where
///     L: IntoIterator,
///     R: IntoIterator,
/// {
///     lockstep(left, right, |_, _| Control::Yield)
/// }
/// ```
/// Compose two sorted iterators to only yield elements which they have in common.
/// ```
/// use core::cmp::Ordering;
///
/// use lockstep::{lockstep, Control};
///
/// /// Assumes that `left` and `right` are sorted.
/// pub fn intersection<L, R, T>(left: L, right: R) -> impl Iterator<Item = T>
/// where
///     L: IntoIterator<Item = T>,
///     R: IntoIterator<Item = T>,
///     T: Ord,
/// {
///     lockstep(left, right, |l, r| {
///         match l.cmp(r) {
///             Ordering::Less => Control::SkipLeft,
///             Ordering::Equal => Control::Yield,
///             Ordering::Greater => Control::SkipRight,
///         }
///     })
///     .map(|(l, _)| l)
/// }
/// ```
pub fn lockstep<L, R, F>(left: L, right: R, f: F) -> Lockstep<L::IntoIter, R::IntoIter, F>
where
    L: IntoIterator,
    R: IntoIterator,
    F: FnMut(&L::Item, &R::Item) -> Control,
{
    Lockstep {
        left: left.into_iter(),
        right: right.into_iter(),
        stepper: f,
    }
}

/// The action to take given the current pair of items.
///
/// This is the return value of the closure passed to the [`lockstep`] function. See its
/// documentation for more detail.
#[derive(Debug, Clone, Copy)]
pub enum Control {
    /// Skip the current item from the left iterator.
    SkipLeft,
    /// Skip the current item from the right iterator.
    SkipRight,
    /// Yield the pair and step both the left and the right iterator.
    Yield,
    /// Stop iteration and return [`None`].
    Break,
}

/// An iterator which selectively increments either the left or right iterator, or yields elements
/// from both.
///
/// This struct is created by the [`lockstep`] function. See its documentation for more detail.
#[derive(Debug, Clone, Copy)]
pub struct Lockstep<L, R, F> {
    left: L,
    right: R,
    stepper: F,
}

impl<L, R, F> Iterator for Lockstep<L, R, F>
where
    L: Iterator,
    R: Iterator,
    F: FnMut(&L::Item, &R::Item) -> Control,
{
    type Item = (L::Item, R::Item);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut next_left = self.left.next()?;
        let mut next_right = self.right.next()?;
        loop {
            match (self.stepper)(&next_left, &next_right) {
                Control::SkipLeft => {
                    next_left = self.left.next()?;
                }
                Control::SkipRight => {
                    next_right = self.right.next()?;
                }
                Control::Yield => return Some((next_left, next_right)),
                Control::Break => return None,
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, l_max) = self.left.size_hint();
        let (_, r_max) = self.right.size_hint();

        let upper = match (l_max, r_max) {
            (None, None) => None,
            (None, Some(v)) | (Some(v), None) => Some(v),
            (Some(l), Some(r)) => Some(l.min(r)),
        };

        (0, upper)
    }
}

#[cfg(test)]
mod tests {
    use core::{cmp::Ordering, fmt::Debug};

    use super::*;

    #[track_caller]
    fn assert_equal<I, J>(a: I, b: J)
    where
        I: IntoIterator,
        J: IntoIterator,
        I::Item: Debug + PartialEq<J::Item>,
        J::Item: Debug,
    {
        let mut ia = a.into_iter();
        let mut ib = b.into_iter();
        let mut i: usize = 0;
        loop {
            match (ia.next(), ib.next()) {
                (None, None) => return,
                (a, b) => {
                    let equal = match (&a, &b) {
                        (Some(a), Some(b)) => a == b,
                        _ => false,
                    };
                    assert!(equal, "Failed assertion {a:?} == {b:?} for iteration {i}");
                    i += 1;
                }
            }
        }
    }

    #[test]
    fn intersection() {
        fn intersection_<L, R, T>(left: L, right: R) -> impl Iterator<Item = T>
        where
            L: IntoIterator<Item = T>,
            R: IntoIterator<Item = T>,
            T: Ord,
        {
            lockstep(left, right, |l, r| match l.cmp(r) {
                Ordering::Less => Control::SkipLeft,
                Ordering::Equal => Control::Yield,
                Ordering::Greater => Control::SkipRight,
            })
            .map(|(l, _)| l)
        }

        assert_equal(
            intersection_([0, 1, 4, 5, 6], [1, 3, 6, 6]),
            [1, 6].into_iter(),
        );
        assert_equal(intersection_([0, 0], [0, 0]), [0, 0].into_iter());
        assert_equal(intersection_([0], [0, 0]), [0].into_iter());
        assert_equal(intersection_([0, 0, 0], [0, 0]), [0, 0].into_iter());
    }

    #[test]
    fn zip() {
        fn zip_<L, R>(left: L, right: R) -> impl Iterator<Item = (L::Item, R::Item)>
        where
            L: IntoIterator,
            R: IntoIterator,
        {
            lockstep(left, right, |_, _| Control::Yield)
        }

        assert_equal(zip_([0, 1, 2], [3, 4, 5]), [(0, 3), (1, 4), (2, 5)]);
        assert_equal(zip_([0, 1, 2], [3, 4]), [(0, 3), (1, 4)]);
        assert_equal(zip_::<[i32; 0], [i32; 2]>([], [3, 4]), []);
        assert_equal(zip_::<[i32; 0], [i32; 0]>([], []), []);
    }

    #[test]
    fn size_hint() {
        let ls = lockstep([0, 1, 2, 3], [0, 1, 2], |_, _| Control::SkipLeft);
        assert_eq!(ls.size_hint(), (0, Some(3)));
    }
}
