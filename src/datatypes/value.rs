use crate::implement_from_wrapper;
use std::fmt::Display;

/// An enumeration of possible values for attributes in a graph.
///
/// `AttributeValue` defines various types of values that are used in Graphster.
/// Each variant supports the `.into()` method for easy conversion from the respective data type.
///
/// # Examples
///
/// ```rust
/// use graphster::prelude::AttributeValue;
///
/// // Creating AttributeValue instances directly
/// let value1 = AttributeValue::String("example_value".to_string());
/// let value2 = AttributeValue::Int32(42);
/// let value3 = AttributeValue::Null;
///
/// // Creating AttributeValue instances using .into()
/// let value4: AttributeValue = "another_value".into();
/// let value5: AttributeValue = 100u64.into();
/// let value6: AttributeValue = 3.14f64.into();
/// ```
///
/// The variants are:
///
/// * `Boolean(bool)`: Represents a boolean value.
/// * `Float32(f32)`: Represents a 32-bit floating point value.
/// * `Float64(f64)`: Represents a 64-bit floating point value.
/// * `Int128(i128)`: Represents an 128-bit signed integer value.
/// * `Int8(i8)`: Represents an 8-bit signed integer value.
/// * `Int16(i16)`: Represents a 16-bit signed integer value.
/// * `Int32(i32)`: Represents a 32-bit signed integer value.
/// * `Int64(i64)`: Represents a 64-bit signed integer value.
/// * `Null`: Represents a null value.
/// * `String(String)`: Represents a string value.
/// * `UInt8(u8)`: Represents an 8-bit unsigned integer value.
/// * `UInt16(u16)`: Represents a 16-bit unsigned integer value.
/// * `UInt32(u32)`: Represents a 32-bit unsigned integer value.
/// * `UInt64(u64)`: Represents a 64-bit unsigned integer value.
/// * `Usize(usize)`: Represents a `usize` value.
#[derive(Debug, Clone, PartialEq)]
pub enum AttributeValue {
    Boolean(bool),
    Float32(f32),
    Float64(f64),
    Int128(i128),
    Int16(i16),
    Int32(i32),
    Int64(i64),
    Int8(i8),
    Null,
    String(String),
    UInt128(u128),
    UInt16(u16),
    UInt32(u32),
    UInt64(u64),
    UInt8(u8),
    Usize(usize),
}

implement_from_wrapper!(AttributeValue, Boolean, bool);
implement_from_wrapper!(AttributeValue, Float32, f32);
implement_from_wrapper!(AttributeValue, Float64, f64);
implement_from_wrapper!(AttributeValue, Int128, i128);
implement_from_wrapper!(AttributeValue, Int16, i16);
implement_from_wrapper!(AttributeValue, Int32, i32);
implement_from_wrapper!(AttributeValue, Int64, i64);
implement_from_wrapper!(AttributeValue, Int8, i8);
implement_from_wrapper!(AttributeValue, String, String);
implement_from_wrapper!(AttributeValue, UInt128, u128);
implement_from_wrapper!(AttributeValue, UInt16, u16);
implement_from_wrapper!(AttributeValue, UInt32, u32);
implement_from_wrapper!(AttributeValue, UInt64, u64);
implement_from_wrapper!(AttributeValue, UInt8, u8);
implement_from_wrapper!(AttributeValue, Usize, usize);

impl From<&str> for AttributeValue {
    fn from(value: &str) -> Self {
        value.to_string().into()
    }
}

impl<T: Into<AttributeValue>> From<Option<T>> for AttributeValue {
    fn from(value: Option<T>) -> Self {
        match value {
            Some(value) => value.into(),
            None => AttributeValue::Null,
        }
    }
}

impl Display for AttributeValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AttributeValue::Boolean(value) => write!(f, "{}", value),
            AttributeValue::Float32(value) => write!(f, "{}", value),
            AttributeValue::Float64(value) => write!(f, "{}", value),
            AttributeValue::Int128(value) => write!(f, "{}", value),
            AttributeValue::Int16(value) => write!(f, "{}", value),
            AttributeValue::Int32(value) => write!(f, "{}", value),
            AttributeValue::Int64(value) => write!(f, "{}", value),
            AttributeValue::Int8(value) => write!(f, "{}", value),
            AttributeValue::Null => write!(f, "null"),
            AttributeValue::String(value) => write!(f, "{}", value),
            AttributeValue::UInt128(value) => write!(f, "{}", value),
            AttributeValue::UInt16(value) => write!(f, "{}", value),
            AttributeValue::UInt32(value) => write!(f, "{}", value),
            AttributeValue::UInt64(value) => write!(f, "{}", value),
            AttributeValue::UInt8(value) => write!(f, "{}", value),
            AttributeValue::Usize(value) => write!(f, "{}", value),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_attribute_value_from() {
        assert_eq!(AttributeValue::from(false), AttributeValue::Boolean(false));
        assert_eq!(AttributeValue::from(0_f32), AttributeValue::Float32(0_f32));
        assert_eq!(AttributeValue::from(0_f64), AttributeValue::Float64(0_f64));
        assert_eq!(AttributeValue::from(0_i128), AttributeValue::Int128(0_i128));
        assert_eq!(AttributeValue::from(0_i16), AttributeValue::Int16(0_i16));
        assert_eq!(AttributeValue::from(0_i32), AttributeValue::Int32(0_i32));
        assert_eq!(AttributeValue::from(0_i64), AttributeValue::Int64(0_i64));
        assert_eq!(AttributeValue::from(0_i8), AttributeValue::Int8(0_i8));
        assert_eq!(
            AttributeValue::from("foo".to_string()),
            AttributeValue::String("foo".to_string())
        );
        assert_eq!(
            AttributeValue::from(0_u128),
            AttributeValue::UInt128(0_u128)
        );
        assert_eq!(AttributeValue::from(0_u16), AttributeValue::UInt16(0_u16));
        assert_eq!(AttributeValue::from(0_u32), AttributeValue::UInt32(0_u32));
        assert_eq!(AttributeValue::from(0_u64), AttributeValue::UInt64(0_u64));
        assert_eq!(AttributeValue::from(0_u8), AttributeValue::UInt8(0_u8));
        assert_eq!(
            AttributeValue::from(0_usize),
            AttributeValue::Usize(0_usize)
        );
        assert_eq!(
            AttributeValue::from("foo"),
            AttributeValue::String("foo".to_string())
        );
    }

    #[test]
    fn test_attribute_value_from_option() {
        assert_eq!(
            AttributeValue::from(Some(false)),
            AttributeValue::Boolean(false)
        );
        assert_eq!(
            AttributeValue::from(Some(0_f32)),
            AttributeValue::Float32(0_f32)
        );
        assert_eq!(
            AttributeValue::from(Some(0_f64)),
            AttributeValue::Float64(0_f64)
        );
        assert_eq!(
            AttributeValue::from(Some(0_i128)),
            AttributeValue::Int128(0_i128)
        );
        assert_eq!(
            AttributeValue::from(Some(0_i16)),
            AttributeValue::Int16(0_i16)
        );
        assert_eq!(
            AttributeValue::from(Some(0_i32)),
            AttributeValue::Int32(0_i32)
        );
        assert_eq!(
            AttributeValue::from(Some(0_i64)),
            AttributeValue::Int64(0_i64)
        );
        assert_eq!(AttributeValue::from(Some(0_i8)), AttributeValue::Int8(0_i8));
        assert_eq!(
            AttributeValue::from(Some("foo".to_string())),
            AttributeValue::String("foo".to_string())
        );
        assert_eq!(
            AttributeValue::from(Some(0_u128)),
            AttributeValue::UInt128(0_u128)
        );
        assert_eq!(
            AttributeValue::from(Some(0_u16)),
            AttributeValue::UInt16(0_u16)
        );
        assert_eq!(
            AttributeValue::from(Some(0_u32)),
            AttributeValue::UInt32(0_u32)
        );
        assert_eq!(
            AttributeValue::from(Some(0_u64)),
            AttributeValue::UInt64(0_u64)
        );
        assert_eq!(
            AttributeValue::from(Some(0_u8)),
            AttributeValue::UInt8(0_u8)
        );
        assert_eq!(
            AttributeValue::from(Some(0_usize)),
            AttributeValue::Usize(0_usize)
        );
        assert_eq!(
            AttributeValue::from(Some("foo")),
            AttributeValue::String("foo".to_string())
        );

        assert_eq!(AttributeValue::from(None::<bool>), AttributeValue::Null);
        assert_eq!(AttributeValue::from(None::<f32>), AttributeValue::Null);
        assert_eq!(AttributeValue::from(None::<f64>), AttributeValue::Null);
        assert_eq!(AttributeValue::from(None::<i128>), AttributeValue::Null);
        assert_eq!(AttributeValue::from(None::<i16>), AttributeValue::Null);
        assert_eq!(AttributeValue::from(None::<i32>), AttributeValue::Null);
        assert_eq!(AttributeValue::from(None::<i64>), AttributeValue::Null);
        assert_eq!(AttributeValue::from(None::<i8>), AttributeValue::Null);
        assert_eq!(AttributeValue::from(None::<String>), AttributeValue::Null);
        assert_eq!(AttributeValue::from(None::<u128>), AttributeValue::Null);
        assert_eq!(AttributeValue::from(None::<u16>), AttributeValue::Null);
        assert_eq!(AttributeValue::from(None::<u32>), AttributeValue::Null);
        assert_eq!(AttributeValue::from(None::<u64>), AttributeValue::Null);
        assert_eq!(AttributeValue::from(None::<u8>), AttributeValue::Null);
        assert_eq!(AttributeValue::from(None::<usize>), AttributeValue::Null);
        assert_eq!(AttributeValue::from(None::<&str>), AttributeValue::Null);
    }

    #[test]
    fn test_attribute_value_display() {
        assert_eq!(format!("{}", AttributeValue::Boolean(false)), "false");
        assert_eq!(format!("{}", AttributeValue::Float32(0_f32)), "0");
        assert_eq!(format!("{}", AttributeValue::Float64(0_f64)), "0");
        assert_eq!(format!("{}", AttributeValue::Int128(0_i128)), "0");
        assert_eq!(format!("{}", AttributeValue::Int16(0_i16)), "0");
        assert_eq!(format!("{}", AttributeValue::Int32(0_i32)), "0");
        assert_eq!(format!("{}", AttributeValue::Int64(0_i64)), "0");
        assert_eq!(format!("{}", AttributeValue::Int8(0_i8)), "0");
        assert_eq!(format!("{}", AttributeValue::Null), "null");
        assert_eq!(
            format!("{}", AttributeValue::String("foo".to_string())),
            "foo"
        );
        assert_eq!(format!("{}", AttributeValue::UInt128(0_u128)), "0");
        assert_eq!(format!("{}", AttributeValue::UInt16(0_u16)), "0");
        assert_eq!(format!("{}", AttributeValue::UInt32(0_u32)), "0");
        assert_eq!(format!("{}", AttributeValue::UInt64(0_u64)), "0");
        assert_eq!(format!("{}", AttributeValue::UInt8(0_u8)), "0");
        assert_eq!(format!("{}", AttributeValue::Usize(0_usize)), "0");
    }
}
