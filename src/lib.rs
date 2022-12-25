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
    /// assert_eq!(a.warnings.len(), 2);
    /// assert_eq!(a.warnings[0], "x");
    /// assert_eq!(a.warnings[1], "y");
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
    /// let a = Warned::new(123, vec!["x", "y"]);
    /// assert_eq!(a.unwrap(&mut warnings), 123);
    /// assert_eq!(warnings.len(), 2);
    /// assert_eq!(warnings[0], "x");
    /// assert_eq!(warnings[1], "y");
    /// ```
    pub fn unwrap(self, warnings: &mut impl Extend<W>) -> T {
        warnings.extend(self.warnings);
        self.value
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
    /// let a: Warned::<i32, String> = (111).into();
    /// assert_eq!(a.value, 111);
    /// assert!(a.warnings.is_empty());
    /// ```
    fn from(value: T) -> Self {
        Self::new(value, vec![])
    }
}

impl<T, W> From<Result<T, W>> for Warned<Option<T>, W> {
    /// ```
    /// use warned::Warned;
    ///
    /// let a: Warned::<Option<i32>, &str> = Ok(111).into();
    /// assert_eq!(a.value, Some(111));
    /// assert!(a.warnings.is_empty());
    ///
    /// let b: Warned::<Option<i32>, &str> = Err("oops").into();
    /// assert!(b.value.is_none());
    /// assert_eq!(b.warnings, vec!["oops"]);
    /// ```
    fn from(result: Result<T, W>) -> Self {
        match result {
            Ok(x) => Self::new(Some(x), vec![]),
            Err(e) => Self::new(None, vec![e]),
        }
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

pub trait ResultExtension<T, E>: Sized {
    fn warned_ok(self, warnings: &mut Vec<impl From<E>>) -> Option<T>;

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
    fn warned_ok(self, warnings: &mut Vec<impl From<E>>) -> Option<T> {
        match self {
            Ok(x) => Some(x),
            Err(e) => {
                warnings.push(e.into());
                None
            }
        }
    }
}
