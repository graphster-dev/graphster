use std::ops::Deref;

/// An enum that provides a way to wrap a reference or an owned value.
///
/// `RefWrapper` is used to handle situations where a value can be either owned or borrowed.
#[derive(Debug, PartialEq)]
pub enum RefWrapper<'a, T> {
    Owned(T),
    Borrowed(&'a T),
}

impl<'a, T> AsRef<T> for RefWrapper<'a, T> {
    fn as_ref(&self) -> &T {
        match self {
            RefWrapper::Owned(value) => value,
            RefWrapper::Borrowed(value) => value,
        }
    }
}

impl<'a, T> From<&'a T> for RefWrapper<'a, T> {
    fn from(value: &'a T) -> Self {
        RefWrapper::Borrowed(value)
    }
}

impl<T> Deref for RefWrapper<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ref_wrapper_asref() {
        let value = 42;
        let owned = RefWrapper::Owned(value);
        assert_eq!(owned.as_ref(), &42);

        let borrowed = RefWrapper::Borrowed(&value);
        assert_eq!(borrowed.as_ref(), &42);
    }

    #[test]
    fn test_ref_wrapper_from() {
        let value = 42;
        let borrowed = RefWrapper::from(&value);
        assert_eq!(borrowed, RefWrapper::Borrowed(&value));
    }

    #[test]
    fn test_ref_wrapper_deref() {
        let value = 42;
        let owned = RefWrapper::Owned(value);
        assert_eq!(*owned, 42);

        let borrowed = RefWrapper::Borrowed(&value);
        assert_eq!(*borrowed, 42);
    }
}
