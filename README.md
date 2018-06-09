# carchive

This library defines an encoding for immutable key-value data where keys are small and approximately uniformly
distributed. It provides constant-time average-case random reads based on key by storing a list of key-offset tuples
sorted by key. When performing a lookup, the key is used to compute an approximate offset into this list, then linearly
scanning towards the target key until the direction changes or the end of the list is reached.

These properties make this encoding a good solution for content-addressed storage, where keys are the stored data's
hash.

## Storage Layout

The last 4 bytes of an archive are a little-endian encoding of the key length, preceded by an 8 byte little-endian
encoding of the number `n` of key-value pairs encoded. Preceding that is the index: a list of `n` unpadded `(key, start,
length)` tuples. Entries are ordered by `key`, `start` represents the offset from the beginning of the archive at which
the corresponding value begins, and `length` represents the length of the value in bytes. Unstructured extension data
can be stored prior to the index.
