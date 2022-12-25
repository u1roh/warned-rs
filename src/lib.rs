#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Warned<T, W> {
    pub value: T,
    pub warnings: Vec<W>,
}

impl<T, W> Warned<T, W> {
    /// ```
    /// use warned::*;
    /// let w = Warned::<i32, String>::new(123);
    /// assert_eq!(w.value, 123);
    /// assert!(w.warnings.is_empty());
    /// ```
    pub fn new(value: T) -> Self {
        Self {
            value,
            warnings: vec![],
        }
    }
    pub fn unwrap(self, warnings: &mut Vec<W>) -> T {
        warnings.extend(self.warnings);
        self.value
    }
}

impl<T, W> std::ops::Deref for Warned<T, W> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.value
    }
}

impl<T: Default, W> Default for Warned<T, W> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T, W> From<T> for Warned<T, W> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T, Ts, W> std::iter::FromIterator<Warned<T, W>> for Warned<Ts, W>
where
    Ts: std::iter::FromIterator<T>,
{
    fn from_iter<I: IntoIterator<Item = Warned<T, W>>>(iter: I) -> Self {
        let mut warnings = vec![];
        let value = iter.into_iter().map(|x| x.unwrap(&mut warnings)).collect();
        Self { value, warnings }
    }
}

impl<T, Ts, W> std::iter::FromIterator<Result<T, W>> for Warned<Ts, W>
where
    Ts: std::iter::FromIterator<T>,
{
    fn from_iter<I: IntoIterator<Item = Result<T, W>>>(iter: I) -> Self {
        let (mut value, mut warnings) = (vec![], vec![]);
        for item in iter {
            match item {
                Ok(x) => value.push(x),
                Err(w) => warnings.push(w),
            }
        }
        Self {
            value: Ts::from_iter(value),
            warnings,
        }
    }
}
