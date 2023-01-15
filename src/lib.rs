/// Represents a value with warnings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Warned<T, W> {
    pub value: T,
    pub warnings: Vec<W>,
}

impl<T, W> Warned<T, W> {
    /// ```
    /// use warned::*;
    /// let a = Warned::new(123, vec!["x", "y"]);
    /// assert_eq!(a.value, 123);
    /// assert_eq!(a.warnings, vec!["x", "y"]);
    /// ```
    pub fn new(value: T, warnings: impl IntoIterator<Item = W>) -> Self {
        Self {
            value,
            warnings: Vec::from_iter(warnings),
        }
    }

    /// ```
    /// use warned::*;
    /// let mut warnings = vec![];
    /// assert_eq!(Warned::new(123, vec!["x", "y"]).unwrap(&mut warnings), 123);
    /// assert_eq!(warnings, vec!["x", "y"]);
    /// ```
    pub fn unwrap(self, warnings: &mut impl Extend<W>) -> T {
        warnings.extend(self.warnings);
        self.value
    }

    /// ```
    /// use warned::*;
    /// let a = Warned::new(123, vec!["x", "y"]);
    /// let b = a.map(|value| 2 * value);
    /// assert_eq!(b.value, 246);
    /// assert_eq!(b.warnings, vec!["x", "y"]);
    /// ```
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Warned<U, W> {
        Warned {
            value: f(self.value),
            warnings: self.warnings,
        }
    }

    /// ```
    /// use warned::*;
    /// let a = Warned::new(123, vec!["x", "y"]);
    /// let b = a.and_then(|value| Warned::new(value as f64 / 2.0, vec!["z"]));
    /// assert_eq!(b.value, 123.0 / 2.0);
    /// assert_eq!(b.warnings, vec!["x", "y", "z"]);
    /// ```
    pub fn and_then<U>(mut self, f: impl Fn(T) -> Warned<U, W>) -> Warned<U, W> {
        Warned::new(f(self.value).unwrap(&mut self.warnings), self.warnings)
    }

    /// ```
    /// use warned::*;
    /// assert_eq!(Warned::<_, &str>::new(123, []).into_result(), Ok(123));
    /// assert_eq!(Warned::new(123, ["warning"]).into_result(), Err(vec!["warning"]));
    /// ```
    pub fn into_result(self) -> Result<T, Vec<W>> {
        if self.warnings.is_empty() {
            Ok(self.value)
        } else {
            Err(self.warnings)
        }
    }
}

impl<T, W> std::ops::Deref for Warned<T, W> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.value
    }
}

impl<T: Default, W> Default for Warned<T, W> {
    /// ```
    /// use warned::*;
    /// let a = Warned::<Vec<i32>, String>::default();
    /// assert!(a.value.is_empty());
    /// assert!(a.warnings.is_empty());
    /// ```
    fn default() -> Self {
        Self::new(T::default(), vec![])
    }
}

impl<T, W> From<T> for Warned<T, W> {
    /// ```
    /// use warned::*;
    /// let a: Warned<i32, String> = (111).into();
    /// assert_eq!(a.value, 111);
    /// assert!(a.warnings.is_empty());
    /// ```
    fn from(value: T) -> Self {
        Self::new(value, vec![])
    }
}

impl<T, W, E: Into<W>> From<Result<T, E>> for Warned<Option<T>, W> {
    /// ```
    /// use warned::Warned;
    ///
    /// let a: Warned<Option<i32>, &str> = Ok::<i32, &str>(111).into();
    /// assert_eq!(a.value, Some(111));
    /// assert!(a.warnings.is_empty());
    ///
    /// let b: Warned<Option<i32>, &str> = Err::<i32, &str>("oops").into();
    /// assert!(b.value.is_none());
    /// assert_eq!(b.warnings, vec!["oops"]);
    /// ```
    fn from(result: Result<T, E>) -> Self {
        match result {
            Ok(x) => Self::new(Some(x), vec![]),
            Err(e) => Self::new(None, vec![e.into()]),
        }
    }
}

impl<T: Default, W, E: Into<W>> From<Result<T, E>> for Warned<T, W> {
    /// ```
    /// use warned::Warned;
    ///
    /// let a: Warned<i32, &str> = Ok::<_, &str>(111).into();
    /// assert_eq!(a.value, 111);
    /// assert!(a.warnings.is_empty());
    ///
    /// let b: Warned<i32, &str> = Err("oops").into();
    /// assert_eq!(b.value, 0);
    /// assert_eq!(b.warnings, vec!["oops"]);
    /// ```
    fn from(result: Result<T, E>) -> Self {
        match result {
            Ok(x) => Self::new(x, vec![]),
            Err(e) => Self::new(T::default(), vec![e.into()]),
        }
    }
}

impl<T, W> From<Warned<T, W>> for Result<T, Vec<W>> {
    /// ```
    /// use warned::*;
    /// assert_eq!(Ok(123), Warned::<_, &str>::new(123, []).into());
    /// assert_eq!(Err(vec!["warning"]), Warned::new(123, ["warning"]).into());
    /// ```
    fn from(src: Warned<T, W>) -> Self {
        src.into_result()
    }
}

impl<T1, T2, W> From<(Warned<T1, W>, Warned<T2, W>)> for Warned<(T1, T2), W> {
    /// ```
    /// use warned::Warned;
    /// let a = Warned::new(123, vec!["x", "xx"]);
    /// let b = Warned::new(321, vec!["y", "yy"]);
    /// let c: Warned<(_, _), _> = (a, b).into();
    /// assert_eq!(c.value, (123, 321));
    /// assert_eq!(c.warnings, vec!["x", "xx", "y", "yy"]);
    /// ```
    fn from((a, b): (Warned<T1, W>, Warned<T2, W>)) -> Self {
        Self::new((a.value, b.value), a.warnings.into_iter().chain(b.warnings))
    }
}

impl<T, Ts: std::iter::FromIterator<T>, W> std::iter::FromIterator<Warned<T, W>> for Warned<Ts, W> {
    /// ```
    /// use warned::Warned;
    /// let src: Vec<Warned<i32, &str>> = vec![
    ///     Warned::new(111, vec![]),
    ///     Warned::new(222, vec!["oops"]),
    ///     Warned::new(333, vec!["foo", "bar"])
    /// ];
    /// let dst = src.into_iter().collect::<Warned<Vec<_>, _>>();
    /// assert_eq!(dst.value, vec![111, 222, 333]);
    /// assert_eq!(dst.warnings, vec!["oops", "foo", "bar"]);
    /// ```
    fn from_iter<I: IntoIterator<Item = Warned<T, W>>>(iter: I) -> Self {
        let mut warnings = vec![];
        let value = iter.into_iter().map(|x| x.unwrap(&mut warnings)).collect();
        Self { value, warnings }
    }
}

impl<T, Ts: std::iter::FromIterator<T>, W> std::iter::FromIterator<Result<T, W>> for Warned<Ts, W> {
    /// ```
    /// use warned::Warned;
    /// let src = vec![Ok(111), Err("oops"), Err("oops2"), Ok(222)];
    /// let dst = src.into_iter().collect::<Warned<Vec<_>, _>>();
    /// assert_eq!(dst.value, vec![111, 222]);
    /// assert_eq!(dst.warnings, vec!["oops", "oops2"]);
    /// ```
    fn from_iter<I: IntoIterator<Item = Result<T, W>>>(iter: I) -> Self {
        let mut warnings = vec![];
        Self {
            value: iter
                .into_iter()
                .filter_map(|item| item.warned_ok(&mut warnings))
                .collect(),
            warnings,
        }
    }
}

pub trait ForceFrom<T>: Sized {
    type Warning;
    fn force_from(src: T) -> Warned<Self, Self::Warning>;
}

pub trait ForceFromOr<T>: Sized {
    type Warning;
    fn force_from_or(src: T, default: Self) -> Warned<Self, Self::Warning>;
    fn force_from_or_else(src: T, f: impl FnOnce() -> Self) -> Warned<Self, Self::Warning>;
}

pub trait ForceInto<T> {
    type Warning;
    fn force_into(self) -> Warned<T, Self::Warning>;
}

pub trait ForceIntoOr<T> {
    type Warning;
    fn force_into_or(self, default: T) -> Warned<T, Self::Warning>;
    fn force_into_or_else(self, f: impl FnOnce() -> T) -> Warned<T, Self::Warning>;
}

impl<T, U: ForceFrom<T>> ForceInto<U> for T {
    type Warning = U::Warning;
    fn force_into(self) -> Warned<U, Self::Warning> {
        U::force_from(self)
    }
}

impl<T, U: ForceFromOr<T>> ForceIntoOr<U> for T {
    type Warning = U::Warning;
    fn force_into_or(self, default: U) -> Warned<U, Self::Warning> {
        U::force_from_or(self, default)
    }
    fn force_into_or_else(self, f: impl FnOnce() -> U) -> Warned<U, Self::Warning> {
        U::force_from_or_else(self, f)
    }
}

impl<T: Default, U: TryInto<T>> ForceFrom<U> for T {
    type Warning = U::Error;
    fn force_from(src: U) -> Warned<T, Self::Warning> {
        src.try_into().into()
    }
}

impl<T, U: TryInto<T>> ForceFromOr<U> for T {
    type Warning = U::Error;
    fn force_from_or(src: U, default: T) -> Warned<T, Self::Warning> {
        match src.try_into() {
            Ok(value) => value.into(),
            Err(e) => Warned::new(default, vec![e]),
        }
    }
    fn force_from_or_else(src: U, f: impl FnOnce() -> T) -> Warned<T, Self::Warning> {
        match src.try_into() {
            Ok(value) => value.into(),
            Err(e) => Warned::new(f(), vec![e]),
        }
    }
}

pub trait ResultExtension<T, E>: Sized {
    fn into_warned<W>(self) -> Warned<Option<T>, W>
    where
        E: Into<W>;

    fn into_warned_or<W>(self, default: T) -> Warned<T, W>
    where
        E: Into<W>,
    {
        self.into_warned().map(|value| value.unwrap_or(default))
    }

    fn into_warned_or_else<W>(self, f: impl FnOnce() -> T) -> Warned<T, W>
    where
        E: Into<W>,
    {
        self.into_warned().map(|value| value.unwrap_or_else(f))
    }

    fn into_warned_or_default<W>(self) -> Warned<T, W>
    where
        E: Into<W>,
        T: Default,
    {
        self.into_warned().map(|value| value.unwrap_or_default())
    }

    fn warned_ok<W>(self, warnings: &mut Vec<W>) -> Option<T>
    where
        E: Into<W>,
    {
        self.into_warned().unwrap(warnings)
    }

    fn warned_unwrap_or(self, warnings: &mut Vec<E>, default: T) -> T {
        self.warned_ok(warnings).unwrap_or(default)
    }
    fn warned_unwrap_or_else(self, warnings: &mut Vec<E>, f: impl FnOnce(&E) -> T) -> T {
        self.warned_ok(warnings)
            .unwrap_or_else(|| f(&warnings.last().unwrap()))
    }
    fn warned_unwrap_or_default(self, warnings: &mut Vec<E>) -> T
    where
        T: Default,
    {
        self.warned_ok(warnings).unwrap_or_default()
    }
}

impl<T, E> ResultExtension<T, E> for Result<T, E> {
    fn into_warned<W>(self) -> Warned<Option<T>, W>
    where
        E: Into<W>,
    {
        self.into()
    }
}
