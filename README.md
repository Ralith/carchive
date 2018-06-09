# carchive

This library defines an encoding for immutable key-value data where keys are small and approximately uniformly
distributed. It provides constant-time average-case random reads based on key by storing a list of key-offset tuples
sorted by key. When performing a lookup, the key is used to compute an approximate offset into this list, then linearly
scanning towards the target key until the direction changes or the end of the list is reached.

These properties make this encoding a good solution for content-addressed storage, where keys are the stored data's
hash.
