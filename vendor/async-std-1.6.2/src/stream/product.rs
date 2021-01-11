use core::pin::Pin;
use core::future::Future;

use crate::stream::Stream;

/// Trait to represent types that can be created by multiplying the elements of a stream.
///
/// This trait is used to implement the [`product`] method on streams. Types which
/// implement the trait can be generated by the [`product`] method. Like
/// [`FromStream`] this trait should rarely be called directly and instead
/// interacted with through [`Stream::product`].
///
/// [`product`]: trait.Product.html#tymethod.product
/// [`FromStream`]: trait.FromStream.html
/// [`Stream::product`]: trait.Stream.html#method.product
#[cfg(feature = "unstable")]
#[cfg_attr(feature = "docs", doc(cfg(unstable)))]
pub trait Product<A = Self>: Sized {
    /// Method which takes a stream and generates `Self` from the elements by
    /// multiplying the items.
    fn product<'a, S>(stream: S) -> Pin<Box<dyn Future<Output = Self> + 'a>>
    where
        S: Stream<Item = A> + 'a;
}

use core::ops::Mul;
use core::num::Wrapping;
use crate::stream::stream::StreamExt;

macro_rules! integer_product {
    (@impls $one: expr, $($a:ty)*) => ($(
        impl Product for $a {
            fn product<'a, S>(stream: S) -> Pin<Box<dyn Future<Output = Self>+ 'a>>
            where
                S: Stream<Item = $a> + 'a,
            {
                Box::pin(async move { stream.fold($one, Mul::mul).await } )
            }
        }
        impl<'a> Product<&'a $a> for $a {
            fn product<'b, S>(stream: S) -> Pin<Box<dyn Future<Output = Self> + 'b>>
            where
                S: Stream<Item = &'a $a> + 'b,
            {
                Box::pin(async move { stream.fold($one, Mul::mul).await } )
            }
        }
    )*);
    ($($a:ty)*) => (
        integer_product!(@impls 1, $($a)*);
        integer_product!(@impls Wrapping(1), $(Wrapping<$a>)*);
    );
}

macro_rules! float_product {
    ($($a:ty)*) => ($(
        impl Product for $a {
            fn product<'a, S>(stream: S) -> Pin<Box<dyn Future<Output = Self>+ 'a>>
                where S: Stream<Item = $a> + 'a,
            {
                Box::pin(async move { stream.fold(1.0, |a, b| a * b).await } )
            }
        }
        impl<'a> Product<&'a $a> for $a {
            fn product<'b, S>(stream: S) -> Pin<Box<dyn Future<Output = Self>+ 'b>>
                where S: Stream<Item = &'a $a> + 'b,
            {
                Box::pin(async move { stream.fold(1.0, |a, b| a * b).await } )
            }
        }
    )*);
    ($($a:ty)*) => (
        float_product!($($a)*);
        float_product!($(Wrapping<$a>)*);
    );
}

integer_product!{ i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize }
float_product!{ f32 f64 }
