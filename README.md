# carchive

This library defines an encoding for immutable key-value data where keys are small, fixed-size, and approximately
uniformly distributed. It provides random key lookups in O(log log n) average time using interpolation search.

These properties make this encoding a good solution for content-addressed storage, where keys are the stored data's
hash.

## Storage Layout

The last 4 bytes of an archive are a little-endian encoding of the key length, preceded by an 8 byte little-endian
encoding of the number `n` of key-value pairs encoded. Preceding that is the index: a list of `n` unpadded `(key, start,
length)` tuples. Entries are ordered by `key`, `start` represents the offset from the beginning of the archive at which
the corresponding value begins, and `length` represents the length of the value in bytes. Unstructured extension data
can be stored prior to the index.
