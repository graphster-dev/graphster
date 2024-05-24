#[doc(hidden)]
#[macro_export]
macro_rules! implement_from_wrapper {
    ($for:ty, $variant:ident, $from:ty) => {
        impl From<$from> for $for {
            fn from(value: $from) -> Self {
                Self::$variant(value)
            }
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! implement_from_marker {
    ($for:ty, $from: ty) => {
        impl FromMarker<$from> for $for {}
    };
}
