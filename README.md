# `Warned<T, W>`; represents a value with warnings

The `Warned<T, W>` type represents a value with warnings, while the `Result<T, E>` type represents a value or error.

## Basic
```rust
// new
let pi = warned::Warned::new(3.14, vec!`"bad precision"`);
assert_eq!(pi.value, 3.14);
assert_eq!(pi.warnings, vec!`"bad precision"`);

// dereference
assert_eq!(*pi, 3.14);

// unwrap
let mut warnings = vec!`"several", "existing", "warnings"`;
assert_eq!(pi.unwrap(&mut warnings), 3.14);
assert_eq!(warnings, vec!`"several", "existing", "warnings", "bad precision"`);

// into
let a: warned::Warned<i32, String> = 123.into();
assert_eq!(a.value, 123);
assert!(a.warnings.is_empty());
```

## Conversion between `Warned<T, W>` and `Result<T, W>`
* `Warned::into_result` returns `Ok` only if `self` has no warnings.
  Otherwise, returns `Err`.
* `From<Warned<T, W>>` trait is implemented for `Result<T, Vec<W>>` with the `Warned::into_result`.
* `Warned::from_result_or_else` returns a value with no warnings if the `src` is `Ok`.
  Otherwise, returns a value of `f()` with single warning.
* `Warned::from_result_or` returns a value with no warnings if the `src` is `Ok`.
  Otherwise, returns a given `default` value with single warning.
* `Warned::from_result_or_default` Returns a value with no warnings if the `src` is `Ok`.
  Otherwise, returns a `T::default()` value with single warning.
* `Warned::from_result` returns a `Some` value with no warnings if the `src` is `Ok`.
  Otherwise, returns `None` with single warning.

## `FromIterator` implementation
### `FromIterator<Warned<T, W>>`
A sequence of `Warned<T, W>` can be collected as a `Warned<Vec<T>, W>`.
```rust
let src = vec!`
    warned::Warned::new(111, vec!``),
    warned::Warned::new(222, vec!`"oops"`),
    warned::Warned::new(333, vec!`"foo", "bar"`)
`;
let dst = src.into_iter().collect::<warned::Warned<Vec<_>, _>>();
assert_eq!(dst.value, vec!`111, 222, 333`);
assert_eq!(dst.warnings, vec!`"oops", "foo", "bar"`);
```
### `FromIterator<Result<T, E>>`
A sequence of `Result<T, E>` can be collected as a `Warned<Vec<T>, E>`.
```rust
let src = vec!`Ok(111), Err("oops"), Err("oops2"), Ok(222)`;
let dst = src.into_iter().collect::<warned::Warned<Vec<_>, _>>();
assert_eq!(dst.value, vec!`111, 222`);
assert_eq!(dst.warnings, vec!`"oops", "oops2"`);
```

## `ForceFrom` trait, `ForceInto` trait
The pair of the traits are similar to `TryFrom`/`TryInto` traits pair.
`ForceFrom`/`ForceInto` returns `Warned` value, while `TryFrom`/`TryInto`
returns `Result`, as follows.
```rust
pub trait ForceFrom<T>: Sized {
   type Warning;
   fn force_from(src: T) -> Warned<Self, Self::Warning>;
//!}
pub trait ForceInto<T> {
    type Warning;
    fn force_into(self) -> Warned<T, Self::Warning>;
}
```
When you implement `ForceFrom` conversion, `ForceInto` implementation is
automatically defined by the blanket implementation below:
```rust
impl<T, U: ForceFrom<T>> ForceInto<U> for T {
   type Warning = U::Warning;
   fn force_into(self) -> Warned<U, Self::Warning> {
       U::force_from(self)
   }
}
```
And the following blanket implementation is also supported.
```rust
impl<T: Into<U>, U> ForceFrom<T> for U {
    type Warning = std::convert::Infallible;
    fn force_from(src: T) -> Warned<Self, Self::Warning> {
        src.into().into()
    }
}
```
