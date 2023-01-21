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
    /// let mut warnings: Vec<&str> = vec![];
    /// assert_eq!(Warned::new(123, vec!["x", "y"]).unwrap(&mut warnings), 123);
    /// assert_eq!(warnings, vec!["x", "y"]);
    /// ```
    pub fn unwrap<V>(self, warnings: &mut Vec<V>) -> T
    where
        W: Into<V>,
    {
        warnings.extend(self.warnings.into_iter().map(Into::into));
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

    pub fn map_warnings<V>(self, f: impl Fn(W) -> V) -> Warned<T, V> {
        Warned {
            value: self.value,
            warnings: self.warnings.into_iter().map(f).collect(),
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

    /// ```
    /// use warned::Warned;
    ///
    /// let a = Warned::<_, &str>::from_result_or_else(Ok(1), || 2);
    /// assert_eq!(a.value, 1);
    /// assert!(a.warnings.is_empty());
    ///
    /// let b = Warned::<_, &str>::from_result_or_else(Err("oops"), || 2);
    /// assert_eq!(b.value, 2);
    /// assert_eq!(b.warnings, vec!["oops"]);
    /// ```
    pub fn from_result_or_else(src: Result<T, W>, f: impl FnOnce() -> T) -> Self {
        match src {
            Ok(x) => x.into(),
            Err(e) => Self::new(f(), vec![e]),
        }
    }

    /// ```
    /// use warned::Warned;
    ///
    /// let a = Warned::<_, &str>::from_result_or(Ok(1), 2);
    /// assert_eq!(a.value, 1);
    /// assert!(a.warnings.is_empty());
    ///
    /// let b = Warned::<_, &str>::from_result_or(Err("oops"), 2);
    /// assert_eq!(b.value, 2);
    /// assert_eq!(b.warnings, vec!["oops"]);
    /// ```
    pub fn from_result_or(src: Result<T, W>, default: T) -> Self {
        Self::from_result_or_else(src, || default)
    }

    /// ```
    /// use warned::Warned;
    ///
    /// let a = Warned::<i32, &str>::from_result_or_default(Ok(1));
    /// assert_eq!(a.value, 1);
    /// assert!(a.warnings.is_empty());
    ///
    /// let b = Warned::<i32, &str>::from_result_or_default(Err("oops"));
    /// assert_eq!(b.value, 0);
    /// assert_eq!(b.warnings, vec!["oops"]);
    /// ```
    pub fn from_result_or_default(src: Result<T, W>) -> Self
    where
        T: Default,
    {
        Self::from_result_or_else(src, T::default)
    }
}

impl<T, W> Warned<Option<T>, W> {
    /// ```
    /// use warned::Warned;
    ///
    /// let a = Warned::<Option<i32>, &str>::from_result(Ok(111));
    /// assert_eq!(a.value, Some(111));
    /// assert!(a.warnings.is_empty());
    ///
    /// let b = Warned::<Option<i32>, &str>::from_result(Err("oops"));
    /// assert!(b.value.is_none());
    /// assert_eq!(b.warnings, vec!["oops"]);
    /// ```
    pub fn from_result(src: Result<T, W>) -> Self {
        match src {
            Ok(x) => Self::new(Some(x), vec![]),
            Err(e) => Self::new(None, vec![e.into()]),
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

impl<T, E> From<Result<T, E>> for Warned<Option<T>, E> {
    /// ```
    /// use warned::Warned;
    ///
    /// let a: Warned<Option<i32>, &str> = Ok(111).into();
    /// assert_eq!(a.value, Some(111));
    /// assert!(a.warnings.is_empty());
    ///
    /// let b: Warned<Option<i32>, &str> = Err::<i32, _>("oops").into();
    /// assert!(b.value.is_none());
    /// assert_eq!(b.warnings, vec!["oops"]);
    /// ```
    fn from(result: Result<T, E>) -> Self {
        Self::from_result(result)
    }
}

impl<T: Default, E> From<Result<T, E>> for Warned<T, E> {
    /// ```
    /// use warned::Warned;
    ///
    /// let a: Warned<i32, &str> = Ok(111).into();
    /// assert_eq!(a.value, 111);
    /// assert!(a.warnings.is_empty());
    ///
    /// let b: Warned<i32, &str> = Err::<i32, _>("oops").into();
    /// assert_eq!(b.value, 0);
    /// assert_eq!(b.warnings, vec!["oops"]);
    /// ```
    fn from(result: Result<T, E>) -> Self {
        match result {
            Ok(x) => x.into(),
            Err(e) => Self::new(T::default(), vec![e]),
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
                .filter_map(|item| Warned::from_result(item).unwrap(&mut warnings))
                .collect(),
            warnings,
        }
    }
}

pub trait ForceFrom<T>: Sized {
    type Warning;
    fn force_from(src: T) -> Warned<Self, Self::Warning>;
}

pub trait ForceInto<T> {
    type Warning;
    fn force_into(self) -> Warned<T, Self::Warning>;
}

impl<T, U: ForceFrom<T>> ForceInto<U> for T {
    type Warning = U::Warning;
    fn force_into(self) -> Warned<U, Self::Warning> {
        U::force_from(self)
    }
}

impl<T: Into<U>, U> ForceFrom<T> for U {
    type Warning = std::convert::Infallible;
    fn force_from(src: T) -> Warned<Self, Self::Warning> {
        src.into().into()
    }
}
