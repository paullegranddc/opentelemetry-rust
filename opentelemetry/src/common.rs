use std::borrow::{Borrow, Cow};
use std::mem::ManuallyDrop;
use std::ptr;
use std::sync::Arc;
use std::{fmt, hash};

use std::hash::{Hash, Hasher};

/// The key part of attribute [KeyValue] pairs.
///
/// See the [attribute naming] spec for guidelines.
///
/// [attribute naming]: https://github.com/open-telemetry/semantic-conventions/blob/main/docs/general/attribute-naming.md
#[non_exhaustive]
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Key(OtelString);

impl Key {
    /// Create a new `Key`.
    ///
    /// # Examples
    ///
    /// ```
    /// use opentelemetry::Key;
    /// use std::sync::Arc;
    ///
    /// let key1 = Key::new("my_static_str");
    /// let key2 = Key::new(String::from("my_owned_string"));
    /// let key3 = Key::new(Arc::from("my_ref_counted_str"));
    /// ```
    pub fn new(value: impl Into<Key>) -> Self {
        value.into()
    }

    /// Create a new const `Key`.
    pub const fn from_static_str(value: &'static str) -> Self {
        Key(OtelString::from_static(value))
    }

    /// Returns a reference to the underlying key name
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl From<&'static str> for Key {
    /// Convert a `&str` to a `Key`.
    fn from(key_str: &'static str) -> Self {
        Key(OtelString::from_static(key_str))
    }
}

impl From<String> for Key {
    /// Convert a `String` to a `Key`.
    fn from(string: String) -> Self {
        Key(OtelString::from_owned(string))
    }
}

impl From<Arc<str>> for Key {
    /// Convert a `String` to a `Key`.
    fn from(string: Arc<str>) -> Self {
        Key(OtelString::from_shared(string))
    }
}

impl From<Cow<'static, str>> for Key {
    /// Convert a `Cow<'static, str>` to a `Key`
    fn from(string: Cow<'static, str>) -> Self {
        Key(OtelString::from_cow(string))
    }
}

impl fmt::Debug for Key {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(fmt)
    }
}

impl From<Key> for String {
    fn from(key: Key) -> Self {
        key.0.into_string()
    }
}

impl fmt::Display for Key {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0.as_str(), fmt)
    }
}

impl Borrow<str> for Key {
    fn borrow(&self) -> &str {
        self.0.as_str()
    }
}

impl AsRef<str> for Key {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

#[derive(Eq)]
/// OtelString contains a utf-8 encoded string.
/// It is a tagged union over 3 variants: Box<str> / &'static str / Arc<str>
///
/// This representation offers multiple advantages over a normal enum
/// * 16 bytes instead of 24 bytes
/// * No pointer chasing or branching when dereferencing to &str
/// (which would not be the case with the Arc variant)
struct OtelString {
    /// points to the start of the underlying string buffer
    ptr: ptr::NonNull<u8>,
    /// Contains the length of the underlying string in the first OtelString::LENGTH_BITS
    /// lower weight bits, and the enum tag in the rest of the bits
    tagged_len: usize,
}

#[derive(Debug, PartialEq)]
#[repr(usize)]
enum OtelStringTag {
    Owned = OtelString::OWNED_VARIANT_TAG,
    Static = OtelString::STATIC_VARIANT_TAG,
    Shared = OtelString::SHARED_VARIANT_TAG,
}

impl Drop for OtelString {
    fn drop(&mut self) {
        // Safety:
        // to drop this, we create an owned OtelString from the mut ref.
        // after this line, self is invalid to use.
        #[allow(unused_unsafe)]
        unsafe {
            let s: ManuallyDrop<OtelString> = ManuallyDrop::new(Self {
                ptr: self.ptr,
                tagged_len: self.tagged_len,
            });

            match s.tag() {
                OtelStringTag::Owned => drop(ManuallyDrop::into_inner(s).owned()),
                OtelStringTag::Static => drop(ManuallyDrop::into_inner(s).static_opt()),
                OtelStringTag::Shared => drop(ManuallyDrop::into_inner(s).shared()),
            }
        }
    }
}

impl OtelString {
    const OWNED_VARIANT_TAG: usize = 0;
    const STATIC_VARIANT_TAG: usize = 1;
    const SHARED_VARIANT_TAG: usize = 2;

    /// Number of bits in tagged_len used to store the length of the string
    const LENGTH_BITS: i32 = 62;
    const LENGTH_MASK: usize = (1 << Self::LENGTH_BITS) - 1;

    #[inline]
    fn tag(&self) -> OtelStringTag {
        match self.tagged_len >> Self::LENGTH_BITS {
            Self::OWNED_VARIANT_TAG => OtelStringTag::Owned,
            Self::SHARED_VARIANT_TAG => OtelStringTag::Shared,
            Self::STATIC_VARIANT_TAG => OtelStringTag::Static,
            tag => unreachable!("unknown tag for otel string: {tag}"),
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.tagged_len & Self::LENGTH_MASK
    }

    #[inline]
    fn owned(self) -> Option<String> {
        match self.tag() {
            OtelStringTag::Owned => {
                let s = ManuallyDrop::new(self);
                Some(unsafe { String::from_raw_parts(s.ptr.as_ptr(), s.len(), s.len()) })
            }
            _ => None,
        }
    }

    #[inline]
    fn shared(self) -> Option<Arc<str>> {
        match self.tag() {
            OtelStringTag::Shared => {
                let s = ManuallyDrop::new(self);
                Some(unsafe {
                    Arc::from_raw(std::str::from_utf8_unchecked(std::slice::from_raw_parts(
                        s.ptr.as_ptr().cast(),
                        s.len(),
                    )) as *const str)
                })
            }
            _ => None,
        }
    }

    #[inline]
    fn static_opt(self) -> Option<&'static str> {
        match self.tag() {
            OtelStringTag::Static => {
                let s = ManuallyDrop::new(self);
                Some(unsafe {
                    std::str::from_utf8_unchecked(std::slice::from_raw_parts(
                        s.ptr.as_ptr().cast(),
                        s.len(),
                    ))
                })
            }
            _ => None,
        }
    }

    fn from_owned(s: String) -> Self {
        let s = ManuallyDrop::new(s.into_boxed_str());
        unsafe {
            Self::from_pointer_tag(
                ptr::NonNull::new_unchecked(s.as_ptr().cast_mut()),
                s.len(),
                Self::OWNED_VARIANT_TAG,
            )
        }
    }

    const fn from_static(s: &'static str) -> Self {
        unsafe {
            Self::from_pointer_tag(
                ptr::NonNull::new_unchecked(s.as_ptr().cast_mut()),
                s.len(),
                Self::STATIC_VARIANT_TAG,
            )
        }
    }

    fn from_shared(s: Arc<str>) -> Self {
        let s = ManuallyDrop::new(s);
        unsafe {
            Self::from_pointer_tag(
                ptr::NonNull::new_unchecked(Arc::as_ptr(&*s).cast::<u8>().cast_mut()),
                s.len(),
                Self::SHARED_VARIANT_TAG,
            )
        }
    }

    fn from_cow(s: Cow<'static, str>) -> Self {
        match s {
            Cow::Borrowed(s) => Self::from_static(s),
            Cow::Owned(s) => Self::from_owned(s),
        }
    }

    /// Safety:
    /// * ptr must be a valid pointer to a &str. It must be derived from one of the variant.
    ///   the underlying memory stay valid until drop is called on this instance
    /// * len must be the length of the associated str
    /// * tag must be the associated tag for the variant that produced the ptr
    const unsafe fn from_pointer_tag(ptr: ptr::NonNull<u8>, len: usize, tag: usize) -> Self {
        Self {
            ptr,
            tagged_len: len | tag << Self::LENGTH_BITS,
        }
    }

    fn as_str(&self) -> &str {
        unsafe {
            std::str::from_utf8_unchecked(std::slice::from_raw_parts(
                self.ptr.as_ptr().cast(),
                self.len(),
            ))
        }
    }

    fn into_string(self) -> String {
        match self.tag() {
            OtelStringTag::Owned => self.owned().unwrap(),
            OtelStringTag::Static | OtelStringTag::Shared => self.as_str().to_owned(),
        }
    }
}

impl fmt::Debug for OtelString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.tag() {
            OtelStringTag::Owned => f
                .debug_tuple("OtelString::Owned")
                .field(&self.as_str())
                .finish(),
            OtelStringTag::Static => f
                .debug_tuple("OtelString::Static")
                .field(&self.as_str())
                .finish(),
            OtelStringTag::Shared => f
                .debug_tuple("OtelString::Shared")
                .field(&self.as_str())
                .finish(),
        }
    }
}

impl fmt::Display for OtelString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.as_str(), f)
    }
}

/// # Safety
/// All variants are sync and send
/// Note that this wouldnt be the case if it contained and Rc instead of an Arc
/// for instance.
unsafe impl Sync for OtelString {}
unsafe impl Send for OtelString {}

impl Clone for OtelString {
    fn clone(&self) -> Self {
        match self.tag() {
            OtelStringTag::Owned => Self::from_owned(self.as_str().to_owned()),
            OtelStringTag::Static => Self {
                ptr: self.ptr,
                tagged_len: self.tagged_len,
            },
            OtelStringTag::Shared => Self::from_shared(unsafe {
                let arc = ManuallyDrop::new(Arc::from_raw(std::str::from_utf8_unchecked(
                    std::slice::from_raw_parts(self.ptr.as_ptr().cast(), self.len()),
                ) as *const str));
                Arc::clone(&arc)
            }),
        }
    }
}

impl PartialEq for OtelString {
    fn eq(&self, other: &Self) -> bool {
        self.as_str().eq(other.as_str())
    }
}

impl PartialOrd for OtelString {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OtelString {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl hash::Hash for OtelString {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

/// A [Value::Array] containing homogeneous values.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq)]
pub enum Array {
    /// Array of bools
    Bool(Vec<bool>),
    /// Array of integers
    I64(Vec<i64>),
    /// Array of floats
    F64(Vec<f64>),
    /// Array of strings
    String(Vec<StringValue>),
}

impl fmt::Display for Array {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Array::Bool(values) => display_array_str(values, fmt),
            Array::I64(values) => display_array_str(values, fmt),
            Array::F64(values) => display_array_str(values, fmt),
            Array::String(values) => {
                write!(fmt, "[")?;
                for (i, t) in values.iter().enumerate() {
                    if i > 0 {
                        write!(fmt, ",")?;
                    }
                    write!(fmt, "\"{}\"", t)?;
                }
                write!(fmt, "]")
            }
        }
    }
}

fn display_array_str<T: fmt::Display>(slice: &[T], fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(fmt, "[")?;
    for (i, t) in slice.iter().enumerate() {
        if i > 0 {
            write!(fmt, ",")?;
        }
        write!(fmt, "{}", t)?;
    }
    write!(fmt, "]")
}

macro_rules! into_array {
    ($(($t:ty, $val:expr),)+) => {
        $(
            impl From<$t> for Array {
                fn from(t: $t) -> Self {
                    $val(t)
                }
            }
        )+
    }
}

into_array!(
    (Vec<bool>, Array::Bool),
    (Vec<i64>, Array::I64),
    (Vec<f64>, Array::F64),
    (Vec<StringValue>, Array::String),
);

/// The value part of attribute [KeyValue] pairs.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    /// bool values
    Bool(bool),
    /// i64 values
    I64(i64),
    /// f64 values
    F64(f64),
    /// String values
    String(StringValue),
    /// Array of homogeneous values
    Array(Array),
}

/// Wrapper for string-like values
#[non_exhaustive]
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct StringValue(OtelString);

impl fmt::Debug for StringValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::Display for StringValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl AsRef<str> for StringValue {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}

impl StringValue {
    /// Returns a string slice to this value
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl From<StringValue> for String {
    fn from(s: StringValue) -> Self {
        s.0.into_string()
    }
}

impl From<&'static str> for StringValue {
    fn from(s: &'static str) -> Self {
        StringValue(OtelString::from_static(s))
    }
}

impl From<String> for StringValue {
    fn from(s: String) -> Self {
        StringValue(OtelString::from_owned(s))
    }
}

impl From<Arc<str>> for StringValue {
    fn from(s: Arc<str>) -> Self {
        StringValue(OtelString::from_shared(s))
    }
}

impl From<Cow<'static, str>> for StringValue {
    fn from(s: Cow<'static, str>) -> Self {
        StringValue(OtelString::from_cow(s))
    }
}

impl From<Value> for StringValue {
    fn from(s: Value) -> Self {
        match s {
            Value::Bool(v) => format!("{}", v).into(),
            Value::I64(v) => format!("{}", v).into(),
            Value::F64(v) => format!("{}", v).into(),
            Value::String(v) => v,
            Value::Array(v) => format!("{}", v).into(),
        }
    }
}

impl Value {
    /// String representation of the `Value`
    ///
    /// This will allocate if the underlying value is not a `String`.
    pub fn as_str(&self) -> Cow<'_, str> {
        match self {
            Value::Bool(v) => format!("{}", v).into(),
            Value::I64(v) => format!("{}", v).into(),
            Value::F64(v) => format!("{}", v).into(),
            Value::String(v) => Cow::Borrowed(v.as_str()),
            Value::Array(v) => format!("{}", v).into(),
        }
    }
}

macro_rules! from_values {
   (
        $(
            ($t:ty, $val:expr);
        )+
    ) => {
        $(
            impl From<$t> for Value {
                fn from(t: $t) -> Self {
                    $val(t)
                }
            }
        )+
    }
}

from_values!(
    (bool, Value::Bool);
    (i64, Value::I64);
    (f64, Value::F64);
    (StringValue, Value::String);
);

impl From<&'static str> for Value {
    fn from(s: &'static str) -> Self {
        Value::String(s.into())
    }
}

impl From<String> for Value {
    fn from(s: String) -> Self {
        Value::String(s.into())
    }
}

impl From<Arc<str>> for Value {
    fn from(s: Arc<str>) -> Self {
        Value::String(s.into())
    }
}

impl From<Cow<'static, str>> for Value {
    fn from(s: Cow<'static, str>) -> Self {
        Value::String(s.into())
    }
}

impl fmt::Display for Value {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Bool(v) => v.fmt(fmt),
            Value::I64(v) => v.fmt(fmt),
            Value::F64(v) => v.fmt(fmt),
            Value::String(v) => fmt.write_str(v.as_str()),
            Value::Array(v) => v.fmt(fmt),
        }
    }
}

/// A key-value pair describing an attribute.
#[derive(Clone, Debug, PartialEq)]
#[non_exhaustive]
pub struct KeyValue {
    /// The attribute name
    pub key: Key,

    /// The attribute value
    pub value: Value,
}

impl KeyValue {
    /// Create a new `KeyValue` pair.
    pub fn new<K, V>(key: K, value: V) -> Self
    where
        K: Into<Key>,
        V: Into<Value>,
    {
        KeyValue {
            key: key.into(),
            value: value.into(),
        }
    }
}

struct F64Hashable(f64);

impl PartialEq for F64Hashable {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}

impl Eq for F64Hashable {}

impl Hash for F64Hashable {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Hash for KeyValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key.hash(state);
        match &self.value {
            Value::F64(f) => F64Hashable(*f).hash(state),
            Value::Array(a) => match a {
                Array::Bool(b) => b.hash(state),
                Array::I64(i) => i.hash(state),
                Array::F64(f) => f.iter().for_each(|f| F64Hashable(*f).hash(state)),
                Array::String(s) => s.hash(state),
            },
            Value::Bool(b) => b.hash(state),
            Value::I64(i) => i.hash(state),
            Value::String(s) => s.hash(state),
        };
    }
}

impl Eq for KeyValue {}

/// Information about a library or crate providing instrumentation.
///
/// An instrumentation scope should be named to follow any naming conventions
/// of the instrumented library (e.g. 'middleware' for a web framework).
///
/// See the [instrumentation libraries] spec for more information.
///
/// [instrumentation libraries]: https://github.com/open-telemetry/opentelemetry-specification/blob/v1.9.0/specification/overview.md#instrumentation-libraries
#[derive(Debug, Default, Clone)]
#[non_exhaustive]
pub struct InstrumentationScope {
    /// The library name.
    ///
    /// This should be the name of the crate providing the instrumentation.
    name: Cow<'static, str>,

    /// The library version.
    version: Option<Cow<'static, str>>,

    /// [Schema URL] used by this library.
    ///
    /// [Schema URL]: https://github.com/open-telemetry/opentelemetry-specification/blob/v1.9.0/specification/schemas/overview.md#schema-url
    schema_url: Option<Cow<'static, str>>,

    /// Specifies the instrumentation scope attributes to associate with emitted telemetry.
    attributes: Vec<KeyValue>,
}

impl PartialEq for InstrumentationScope {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.version == other.version
            && self.schema_url == other.schema_url
            && {
                let mut self_attrs = self.attributes.clone();
                let mut other_attrs = other.attributes.clone();
                self_attrs.sort_unstable_by(|a, b| a.key.cmp(&b.key));
                other_attrs.sort_unstable_by(|a, b| a.key.cmp(&b.key));
                self_attrs == other_attrs
            }
    }
}

impl Eq for InstrumentationScope {}

impl hash::Hash for InstrumentationScope {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.version.hash(state);
        self.schema_url.hash(state);
        let mut sorted_attrs = self.attributes.clone();
        sorted_attrs.sort_unstable_by(|a, b| a.key.cmp(&b.key));
        for attribute in sorted_attrs {
            attribute.hash(state);
        }
    }
}

impl InstrumentationScope {
    /// Create a new builder to create an [InstrumentationScope]
    pub fn builder<T: Into<Cow<'static, str>>>(name: T) -> InstrumentationScopeBuilder {
        InstrumentationScopeBuilder {
            name: name.into(),
            version: None,
            schema_url: None,
            attributes: None,
        }
    }

    /// Returns the instrumentation library name.
    #[inline]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the instrumentation library version.
    #[inline]
    pub fn version(&self) -> Option<&str> {
        self.version.as_deref()
    }

    /// Returns the [Schema URL] used by this library.
    ///
    /// [Schema URL]: https://github.com/open-telemetry/opentelemetry-specification/blob/v1.9.0/specification/schemas/overview.md#schema-url
    #[inline]
    pub fn schema_url(&self) -> Option<&str> {
        self.schema_url.as_deref()
    }

    /// Returns the instrumentation scope attributes to associate with emitted telemetry.
    #[inline]
    pub fn attributes(&self) -> impl Iterator<Item = &KeyValue> {
        self.attributes.iter()
    }
}

/// Configuration options for [InstrumentationScope].
///
/// An instrumentation scope is a library or crate providing instrumentation.
/// It should be named to follow any naming conventions of the instrumented
/// library (e.g. 'middleware' for a web framework).
///
/// Apart from the name, all other fields are optional.
///
/// See the [instrumentation libraries] spec for more information.
///
/// [instrumentation libraries]: https://github.com/open-telemetry/opentelemetry-specification/blob/v1.9.0/specification/overview.md#instrumentation-libraries
#[derive(Debug)]
pub struct InstrumentationScopeBuilder {
    name: Cow<'static, str>,
    version: Option<Cow<'static, str>>,
    schema_url: Option<Cow<'static, str>>,
    attributes: Option<Vec<KeyValue>>,
}

impl InstrumentationScopeBuilder {
    /// Configure the version for the instrumentation scope
    ///
    /// # Examples
    ///
    /// ```
    /// let scope = opentelemetry::InstrumentationScope::builder("my-crate")
    ///     .with_version("v0.1.0")
    ///     .build();
    /// ```
    pub fn with_version(mut self, version: impl Into<Cow<'static, str>>) -> Self {
        self.version = Some(version.into());
        self
    }

    /// Configure the Schema URL for the instrumentation scope
    ///
    /// # Examples
    ///
    /// ```
    /// let scope = opentelemetry::InstrumentationScope::builder("my-crate")
    ///     .with_schema_url("https://opentelemetry.io/schemas/1.17.0")
    ///     .build();
    /// ```
    pub fn with_schema_url(mut self, schema_url: impl Into<Cow<'static, str>>) -> Self {
        self.schema_url = Some(schema_url.into());
        self
    }

    /// Configure the attributes for the instrumentation scope
    ///
    /// # Examples
    ///
    /// ```
    /// use opentelemetry::KeyValue;
    ///
    /// let scope = opentelemetry::InstrumentationScope::builder("my-crate")
    ///     .with_attributes([KeyValue::new("k", "v")])
    ///     .build();
    /// ```
    pub fn with_attributes<I>(mut self, attributes: I) -> Self
    where
        I: IntoIterator<Item = KeyValue>,
    {
        self.attributes = Some(attributes.into_iter().collect());
        self
    }

    /// Create a new [InstrumentationScope] from this configuration
    pub fn build(self) -> InstrumentationScope {
        InstrumentationScope {
            name: self.name,
            version: self.version,
            schema_url: self.schema_url,
            attributes: self.attributes.unwrap_or_default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::hash::{Hash, Hasher};
    use std::sync::Arc;

    use crate::{InstrumentationScope, KeyValue};

    use rand::random;
    use std::collections::hash_map::DefaultHasher;
    use std::f64;

    use super::OtelString;

    #[test]
    fn test_otel_str_traits() {
        let otel_strs = [
            OtelString::from_static("otel string"),
            OtelString::from_owned("otel string".to_string()),
            OtelString::from_shared("otel string".into()),
        ];
        for otel_str1 in otel_strs.iter() {
            for otel_str2 in otel_strs.iter() {
                // Equal
                assert_eq!(otel_str1, otel_str2);
                // Hash
                assert_eq!(hash_helper(otel_str1), hash_helper(otel_str2));
            }
        }

        for otel_str in otel_strs.iter() {
            // Display
            assert_eq!(format!("{otel_str}"), "otel string");
        }

        for otel_str in otel_strs.iter() {
            // Clone
            let cloned = otel_str.clone();
            assert_eq!(&cloned, otel_str);
            assert_eq!(cloned.tag(), otel_str.tag());
            if matches!(otel_str.tag(), super::OtelStringTag::Shared) {
                assert_eq!(Arc::strong_count(&cloned.shared().unwrap()), 2);
            }
        }
    }

    #[test]
    fn test_otel_str_tag() {
        let static_str = OtelString::from_static("otel string");
        let owned = OtelString::from_owned("otel string".to_string());
        let shared = OtelString::from_shared("otel string".into());

        assert_eq!(static_str.tag(), super::OtelStringTag::Static);
        assert_eq!(owned.tag(), super::OtelStringTag::Owned);
        assert_eq!(shared.tag(), super::OtelStringTag::Shared);

        assert_eq!(static_str.static_opt(), Some("otel string"));
        assert_eq!(owned.owned(), Some("otel string".to_string()));
        let shared_inner = shared.shared().unwrap();
        assert_eq!(Arc::strong_count(&shared_inner), 1);
        assert_eq!(shared_inner, "otel string".into());
    }

    #[test]
    fn kv_float_equality() {
        let kv1 = KeyValue::new("key", 1.0);
        let kv2 = KeyValue::new("key", 1.0);
        assert_eq!(kv1, kv2);

        let kv1 = KeyValue::new("key", 1.0);
        let kv2 = KeyValue::new("key", 1.01);
        assert_ne!(kv1, kv2);

        let kv1 = KeyValue::new("key", f64::NAN);
        let kv2 = KeyValue::new("key", f64::NAN);
        assert_ne!(kv1, kv2, "NAN is not equal to itself");

        for float_val in [
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::MAX,
            f64::MIN,
            f64::MIN_POSITIVE,
        ]
        .iter()
        {
            let kv1 = KeyValue::new("key", *float_val);
            let kv2 = KeyValue::new("key", *float_val);
            assert_eq!(kv1, kv2);
        }

        for _ in 0..100 {
            let random_value = random::<f64>();
            let kv1 = KeyValue::new("key", random_value);
            let kv2 = KeyValue::new("key", random_value);
            assert_eq!(kv1, kv2);
        }
    }

    #[test]
    fn kv_float_hash() {
        for float_val in [
            f64::NAN,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::MAX,
            f64::MIN,
            f64::MIN_POSITIVE,
        ]
        .iter()
        {
            let kv1 = KeyValue::new("key", *float_val);
            let kv2 = KeyValue::new("key", *float_val);
            assert_eq!(hash_helper(&kv1), hash_helper(&kv2));
        }

        for _ in 0..100 {
            let random_value = random::<f64>();
            let kv1 = KeyValue::new("key", random_value);
            let kv2 = KeyValue::new("key", random_value);
            assert_eq!(hash_helper(&kv1), hash_helper(&kv2));
        }
    }

    fn hash_helper<T: Hash>(item: &T) -> u64 {
        let mut hasher = DefaultHasher::new();
        item.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn instrumentation_scope_equality() {
        let scope1 = InstrumentationScope::builder("my-crate")
            .with_version("v0.1.0")
            .with_schema_url("https://opentelemetry.io/schemas/1.17.0")
            .with_attributes([KeyValue::new("k", "v")])
            .build();
        let scope2 = InstrumentationScope::builder("my-crate")
            .with_version("v0.1.0")
            .with_schema_url("https://opentelemetry.io/schemas/1.17.0")
            .with_attributes([KeyValue::new("k", "v")])
            .build();
        assert_eq!(scope1, scope2);
    }

    #[test]
    fn instrumentation_scope_equality_attributes_diff_order() {
        let scope1 = InstrumentationScope::builder("my-crate")
            .with_version("v0.1.0")
            .with_schema_url("https://opentelemetry.io/schemas/1.17.0")
            .with_attributes([KeyValue::new("k1", "v1"), KeyValue::new("k2", "v2")])
            .build();
        let scope2 = InstrumentationScope::builder("my-crate")
            .with_version("v0.1.0")
            .with_schema_url("https://opentelemetry.io/schemas/1.17.0")
            .with_attributes([KeyValue::new("k2", "v2"), KeyValue::new("k1", "v1")])
            .build();
        assert_eq!(scope1, scope2);

        // assert hash are same for both scopes
        let mut hasher1 = std::collections::hash_map::DefaultHasher::new();
        scope1.hash(&mut hasher1);
        let mut hasher2 = std::collections::hash_map::DefaultHasher::new();
        scope2.hash(&mut hasher2);
        assert_eq!(hasher1.finish(), hasher2.finish());
    }

    #[test]
    fn instrumentation_scope_equality_different_attributes() {
        let scope1 = InstrumentationScope::builder("my-crate")
            .with_version("v0.1.0")
            .with_schema_url("https://opentelemetry.io/schemas/1.17.0")
            .with_attributes([KeyValue::new("k1", "v1"), KeyValue::new("k2", "v2")])
            .build();
        let scope2 = InstrumentationScope::builder("my-crate")
            .with_version("v0.1.0")
            .with_schema_url("https://opentelemetry.io/schemas/1.17.0")
            .with_attributes([KeyValue::new("k2", "v3"), KeyValue::new("k4", "v5")])
            .build();
        assert_ne!(scope1, scope2);

        // assert hash are same for both scopes
        let mut hasher1 = std::collections::hash_map::DefaultHasher::new();
        scope1.hash(&mut hasher1);
        let mut hasher2 = std::collections::hash_map::DefaultHasher::new();
        scope2.hash(&mut hasher2);
        assert_ne!(hasher1.finish(), hasher2.finish());
    }
}
