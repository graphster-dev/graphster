use crate::{
    errors::GraphsterError,
    from_marker::{FromMarker, IntoMarker},
    implement_from_marker, implement_from_wrapper,
    ref_wrapper::RefWrapper,
};
use std::fmt::Display;

use super::AttributeValue;

/// An enumeration of possible keys for attributes in a graph.
///
/// `AttributeKey` defines various types of keys that are used in Graphster.
/// Each variant supports the `.into()` method for easy conversion from the respective data type.
///
/// # Examples
///
/// ```rust
/// use graphster::prelude::AttributeKey;
///
/// // Creating AttributeKey instances directly
/// let key1 = AttributeKey::String("example_key".to_string());
/// let key2 = AttributeKey::Int32(42);
///
/// // Creating AttributeKey instances using .into()
/// let key3: AttributeKey = "another_key".into();
/// let key4: AttributeKey = 100u64.into();
/// ```
///
/// The variants are:
///
/// * `Boolean(bool)`: Represents a boolean key.
/// * `Int8(i8)`: Represents an 8-bit signed integer key.
/// * `Int16(i16)`: Represents a 16-bit signed integer key.
/// * `Int32(i32)`: Represents a 32-bit signed integer key.
/// * `Int64(i64)`: Represents a 64-bit signed integer key.
/// * `String(String)`: Represents a string key.
/// * `UInt8(u8)`: Represents an 8-bit unsigned integer key.
/// * `UInt16(u16)`: Represents a 16-bit unsigned integer key.
/// * `UInt32(u32)`: Represents a 32-bit unsigned integer key.
/// * `UInt64(u64)`: Represents a 64-bit unsigned integer key.
/// * `Usize(usize)`: Represents a `usize` key.
#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum AttributeKey {
    Boolean(bool),
    Int128(i128),
    Int16(i16),
    Int32(i32),
    Int64(i64),
    Int8(i8),
    String(String),
    UInt128(u128),
    UInt16(u16),
    UInt32(u32),
    UInt64(u64),
    UInt8(u8),
    Usize(usize),
}

implement_from_wrapper!(AttributeKey, Boolean, bool);
implement_from_wrapper!(AttributeKey, Int128, i128);
implement_from_wrapper!(AttributeKey, Int16, i16);
implement_from_wrapper!(AttributeKey, Int32, i32);
implement_from_wrapper!(AttributeKey, Int64, i64);
implement_from_wrapper!(AttributeKey, Int8, i8);
implement_from_wrapper!(AttributeKey, String, String);
implement_from_wrapper!(AttributeKey, UInt128, u128);
implement_from_wrapper!(AttributeKey, UInt16, u16);
implement_from_wrapper!(AttributeKey, UInt32, u32);
implement_from_wrapper!(AttributeKey, UInt64, u64);
implement_from_wrapper!(AttributeKey, UInt8, u8);
implement_from_wrapper!(AttributeKey, Usize, usize);

impl From<&str> for AttributeKey {
    fn from(value: &str) -> Self {
        value.to_string().into()
    }
}

implement_from_marker!(AttributeKey, bool);
implement_from_marker!(AttributeKey, i128);
implement_from_marker!(AttributeKey, i16);
implement_from_marker!(AttributeKey, i32);
implement_from_marker!(AttributeKey, i64);
implement_from_marker!(AttributeKey, i8);
implement_from_marker!(AttributeKey, String);
implement_from_marker!(AttributeKey, u16);
implement_from_marker!(AttributeKey, u32);
implement_from_marker!(AttributeKey, u64);
implement_from_marker!(AttributeKey, u8);
implement_from_marker!(AttributeKey, usize);
implement_from_marker!(AttributeKey, &str);

impl TryFrom<AttributeValue> for AttributeKey {
    type Error = GraphsterError;

    fn try_from(value: AttributeValue) -> Result<Self, Self::Error> {
        match value {
            AttributeValue::Boolean(value) => Ok(AttributeKey::Boolean(value)),
            AttributeValue::Int128(value) => Ok(AttributeKey::Int128(value)),
            AttributeValue::Int16(value) => Ok(AttributeKey::Int16(value)),
            AttributeValue::Int32(value) => Ok(AttributeKey::Int32(value)),
            AttributeValue::Int64(value) => Ok(AttributeKey::Int64(value)),
            AttributeValue::Int8(value) => Ok(AttributeKey::Int8(value)),
            AttributeValue::String(value) => Ok(AttributeKey::String(value)),
            AttributeValue::UInt16(value) => Ok(AttributeKey::UInt16(value)),
            AttributeValue::UInt32(value) => Ok(AttributeKey::UInt32(value)),
            AttributeValue::UInt64(value) => Ok(AttributeKey::UInt64(value)),
            AttributeValue::UInt8(value) => Ok(AttributeKey::UInt8(value)),
            AttributeValue::Usize(value) => Ok(AttributeKey::Usize(value)),
            _ => Err(GraphsterError::ConversionError(
                "Could not convert AttributeValue to AttributeKey".to_string(),
            )),
        }
    }
}

impl Display for AttributeKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AttributeKey::Boolean(value) => write!(f, "{}", value),
            AttributeKey::Int128(value) => write!(f, "{}", value),
            AttributeKey::Int16(value) => write!(f, "{}", value),
            AttributeKey::Int32(value) => write!(f, "{}", value),
            AttributeKey::Int64(value) => write!(f, "{}", value),
            AttributeKey::Int8(value) => write!(f, "{}", value),
            AttributeKey::String(value) => write!(f, "{}", value),
            AttributeKey::UInt128(value) => write!(f, "{}", value),
            AttributeKey::UInt16(value) => write!(f, "{}", value),
            AttributeKey::UInt32(value) => write!(f, "{}", value),
            AttributeKey::UInt64(value) => write!(f, "{}", value),
            AttributeKey::UInt8(value) => write!(f, "{}", value),
            AttributeKey::Usize(value) => write!(f, "{}", value),
        }
    }
}

pub type AttributeKeyRef<'a> = RefWrapper<'a, AttributeKey>;

impl<'a, T: Into<AttributeKey> + IntoMarker<AttributeKey>> From<T> for AttributeKeyRef<'a> {
    fn from(value: T) -> Self {
        Self::Owned(value.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_attribute_key_from() {
        assert_eq!(AttributeKey::from(false), AttributeKey::Boolean(false));
        assert_eq!(AttributeKey::from(0_i128), AttributeKey::Int128(0_i128));
        assert_eq!(AttributeKey::from(0_i16), AttributeKey::Int16(0_i16));
        assert_eq!(AttributeKey::from(0_i32), AttributeKey::Int32(0_i32));
        assert_eq!(AttributeKey::from(0_i64), AttributeKey::Int64(0_i64));
        assert_eq!(AttributeKey::from(0_i8), AttributeKey::Int8(0_i8));
        assert_eq!(
            AttributeKey::from("foo".to_string()),
            AttributeKey::String("foo".to_string())
        );
        assert_eq!(AttributeKey::from(0_u128), AttributeKey::UInt128(0_u128));
        assert_eq!(AttributeKey::from(0_u16), AttributeKey::UInt16(0_u16));
        assert_eq!(AttributeKey::from(0_u32), AttributeKey::UInt32(0_u32));
        assert_eq!(AttributeKey::from(0_u64), AttributeKey::UInt64(0_u64));
        assert_eq!(AttributeKey::from(0_u8), AttributeKey::UInt8(0_u8));
        assert_eq!(AttributeKey::from(0_usize), AttributeKey::Usize(0_usize));
        assert_eq!(
            AttributeKey::from("foo"),
            AttributeKey::String("foo".to_string())
        );
    }

    #[test]
    fn test_attribute_key_display() {
        assert_eq!(format!("{}", AttributeKey::Boolean(false)), "false");
        assert_eq!(format!("{}", AttributeKey::Int128(0_i128)), "0");
        assert_eq!(format!("{}", AttributeKey::Int16(0_i16)), "0");
        assert_eq!(format!("{}", AttributeKey::Int32(0_i32)), "0");
        assert_eq!(format!("{}", AttributeKey::Int64(0_i64)), "0");
        assert_eq!(format!("{}", AttributeKey::Int8(0_i8)), "0");
        assert_eq!(
            format!("{}", AttributeKey::String("foo".to_string())),
            "foo"
        );
        assert_eq!(format!("{}", AttributeKey::UInt128(0_u128)), "0");
        assert_eq!(format!("{}", AttributeKey::UInt16(0_u16)), "0");
        assert_eq!(format!("{}", AttributeKey::UInt32(0_u32)), "0");
        assert_eq!(format!("{}", AttributeKey::UInt64(0_u64)), "0");
        assert_eq!(format!("{}", AttributeKey::UInt8(0_u8)), "0");
        assert_eq!(format!("{}", AttributeKey::Usize(0_usize)), "0");
    }
}
