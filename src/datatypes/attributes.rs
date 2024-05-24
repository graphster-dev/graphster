use super::{key::AttributeKeyRef, AttributeKey, AttributeValue};
#[cfg(feature = "rayon")]
use rayon::iter::IntoParallelIterator;
use std::collections::HashMap;

/// A collection of key-value pairs representing attributes associated with nodes or edges
/// in a graph.
///
/// The `Attributes` struct is a thin wrapper around a `HashMap` where the keys are
/// of type `AttributeKey`
/// and the values are of type `AttributeValue`. It provides convenience methods for
/// manipulating these attributes.
///
/// # Examples
///
/// ```rust
/// use graphster::prelude::Attributes;
/// use std::collections::HashMap;
///
/// let mut attrs = Attributes::new();
/// attrs.insert("key1", "value1");
/// attrs.insert("key2", "value2");
///
/// assert_eq!(attrs.get("key1"), Some(&"value1".into()));
/// assert_eq!(attrs.get("key3"), None);
/// ```
#[derive(Debug, Clone, PartialEq)]
#[repr(transparent)]
pub struct Attributes(HashMap<AttributeKey, AttributeValue>);

impl<K: Into<AttributeKey>, V: Into<AttributeValue>> From<HashMap<K, V>> for Attributes {
    fn from(map: HashMap<K, V>) -> Self {
        Attributes(
            map.into_iter()
                .map(|(key, value)| (key.into(), value.into()))
                .collect(),
        )
    }
}

impl<K: Into<AttributeKey>, V: Into<AttributeValue>, const N: usize> From<[(K, V); N]>
    for Attributes
{
    fn from(array: [(K, V); N]) -> Self {
        Self::from_iter(array)
    }
}

impl<K: Into<AttributeKey>, V: Into<AttributeValue>> FromIterator<(K, V)> for Attributes {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Attributes(
            iter.into_iter()
                .map(|(key, value)| (key.into(), value.into()))
                .collect(),
        )
    }
}

impl Default for Attributes {
    /// Creates a new, empty set of attributes using the `Attributes::new` function.
    ///
    /// This is the default implementation for the `Attributes` struct.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let attrs: Attributes = Default::default();
    /// assert!(attrs.iter().count() == 0);
    /// ```
    fn default() -> Self {
        Self::new()
    }
}

impl IntoIterator for Attributes {
    type Item = (AttributeKey, AttributeValue);
    type IntoIter = std::collections::hash_map::IntoIter<AttributeKey, AttributeValue>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[cfg(feature = "rayon")]
#[cfg_attr(docsrs, doc(cfg(feature = "rayon")))]
impl IntoParallelIterator for Attributes {
    type Item = (AttributeKey, AttributeValue);
    type Iter = rayon::collections::hash_map::IntoIter<AttributeKey, AttributeValue>;

    fn into_par_iter(self) -> Self::Iter {
        self.0.into_par_iter()
    }
}

#[cfg(feature = "rayon")]
#[cfg_attr(docsrs, doc(cfg(feature = "rayon")))]
impl<'a> IntoParallelIterator for &'a Attributes {
    type Item = (&'a AttributeKey, &'a AttributeValue);
    type Iter = rayon::collections::hash_map::Iter<'a, AttributeKey, AttributeValue>;

    fn into_par_iter(self) -> Self::Iter {
        (&self.0).into_par_iter()
    }
}

impl Attributes {
    /// Creates a new, empty set of attributes.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let attrs = Attributes::new();
    /// assert!(attrs.iter().count() == 0);
    /// ```
    pub fn new() -> Self {
        Attributes(HashMap::new())
    }

    /// Retrieves the value associated with the specified key.
    ///
    /// Returns `Some(&AttributeValue)` if the key exists in the attributes,
    /// or `None` if the key is not found.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut attrs = Attributes::new();
    /// attrs.insert("key1", "value1");
    ///
    /// assert_eq!(attrs.get("key1"), Some(&AttributeValue::from("value1")));
    /// assert_eq!(attrs.get("key2"), None);
    /// ```
    pub fn get<'a, K: Into<AttributeKeyRef<'a>>>(&self, key: K) -> Option<&AttributeValue> {
        self.0.get(key.into().as_ref())
    }

    /// Inserts a key-value pair into the attributes.
    ///
    /// If the key already exists, the value is updated.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut attrs = Attributes::new();
    /// attrs.insert("key1", "value1");
    ///
    /// assert_eq!(attrs.get("key1"), Some(&AttributeValue::from("value1")));
    ///
    /// attrs.insert("key1", "new_value");
    /// assert_eq!(attrs.get("key1"), Some(&AttributeValue::from("new_value")));
    /// ```
    pub fn insert<K: Into<AttributeKey>, V: Into<AttributeValue>>(&mut self, key: K, value: V) {
        self.0.insert(key.into(), value.into());
    }

    /// Removes the key-value pair associated with the specified key from the attributes.
    ///
    /// Returns `Some(AttributeValue)` if the key was present, or `None` if the key was not found.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut attrs = Attributes::new();
    /// attrs.insert("key1", "value1");
    ///
    /// assert_eq!(attrs.remove("key1"), Some(AttributeValue::from("value1")));
    /// assert_eq!(attrs.get("key1"), None);
    /// ```
    pub fn remove<'a, K: Into<AttributeKeyRef<'a>>>(&mut self, key: K) -> Option<AttributeValue> {
        self.0.remove(key.into().as_ref())
    }

    /// Returns an iterator over the key-value pairs in the attributes.
    ///
    /// The iterator's items are of type `(&AttributeKey, &AttributeValue)`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut attrs = Attributes::new();
    /// attrs.insert("key1", "value1");
    /// attrs.insert("key2", "value2");
    ///
    /// for (key, value) in attrs.iter() {
    ///     println!("{}: {}", key, value);
    /// }
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = (&AttributeKey, &AttributeValue)> {
        self.0.iter()
    }

    /// Returns an iterator over the keys in the attributes.
    ///
    /// The iterator's items are of type `&AttributeKey`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut attrs = Attributes::new();
    /// attrs.insert("key1", "value1");
    /// attrs.insert("key2", "value2");
    ///
    /// for key in attrs.keys() {
    ///     println!("{}", key);
    /// }
    /// ```
    pub fn keys(&self) -> impl Iterator<Item = &AttributeKey> {
        self.0.keys()
    }

    /// Returns the number attributes.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut attrs = Attributes::new();
    /// attrs.insert("key1", "value1");
    /// attrs.insert("key2", "value2");
    ///
    /// assert_eq!(attrs.attribute_count(), 2);
    /// ```
    pub fn attribute_count(&self) -> usize {
        self.0.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_attributes_new() {
        let attrs = Attributes::new();
        assert_eq!(attrs.attribute_count(), 0);
    }

    #[test]
    fn test_attributes_insert() {
        let mut attrs = Attributes::new();
        attrs.insert("key1", "value1");
        assert_eq!(attrs.get("key1"), Some(&AttributeValue::from("value1")));

        attrs.insert("key1", "new_value");
        assert_eq!(attrs.get("key1"), Some(&AttributeValue::from("new_value")));
    }

    #[test]
    fn test_attributes_remove() {
        let mut attrs = Attributes::new();
        attrs.insert("key1", "value1");

        assert_eq!(attrs.remove("key1"), Some(AttributeValue::from("value1")));
        assert_eq!(attrs.get("key1"), None);
    }

    #[test]
    fn test_attributes_iter() {
        let mut attrs = Attributes::new();
        attrs.insert("key1", "value1");

        let mut iter = attrs.iter();
        assert_eq!(
            iter.next(),
            Some((
                &AttributeKey::String("key1".to_string()),
                &AttributeValue::from("value1")
            ))
        );
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_attributes_keys() {
        let mut attrs = Attributes::new();
        attrs.insert("key1", "value1");

        let mut iter = attrs.keys();
        assert_eq!(iter.next(), Some(&AttributeKey::String("key1".to_string())));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_attributes_attribute_count() {
        let mut attrs = Attributes::new();
        attrs.insert("key1", "value1");
        attrs.insert("key2", "value2");

        assert_eq!(attrs.attribute_count(), 2);
    }
}
