pub trait FromMarker<T>: Sized {}
pub trait IntoMarker<T>: Sized {}

impl<T, U> IntoMarker<U> for T where U: FromMarker<T> {}
