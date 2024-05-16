use crate::implement_from_wrapper;

#[derive(Debug, Clone, PartialEq)]
pub enum AttributeValue {
    Boolean(bool),
    Float(f64),
    Int16(i16),
    Int32(i32),
    Int64(i64),
    Int8(i8),
    String(String),
    Usize(usize),
}

implement_from_wrapper!(AttributeValue, Boolean, bool);
implement_from_wrapper!(AttributeValue, Float, f64);
implement_from_wrapper!(AttributeValue, Int16, i16);
implement_from_wrapper!(AttributeValue, Int32, i32);
implement_from_wrapper!(AttributeValue, Int64, i64);
implement_from_wrapper!(AttributeValue, Int8, i8);
implement_from_wrapper!(AttributeValue, String, String);
implement_from_wrapper!(AttributeValue, Usize, usize);
