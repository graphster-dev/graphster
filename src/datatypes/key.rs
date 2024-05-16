use crate::implement_from_wrapper;

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum AttributeKey {
    Int16(i16),
    Int32(i32),
    Int64(i64),
    Int8(i8),
    String(String),
    Usize(usize),
}

implement_from_wrapper!(AttributeKey, Int16, i16);
implement_from_wrapper!(AttributeKey, Int32, i32);
implement_from_wrapper!(AttributeKey, Int64, i64);
implement_from_wrapper!(AttributeKey, Int8, i8);
implement_from_wrapper!(AttributeKey, String, String);
implement_from_wrapper!(AttributeKey, Usize, usize);
