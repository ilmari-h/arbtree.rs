# arbtree

`arbtree` is a library for general purpose tree data structures.

The library provides an interface for working with trees of arbitrary depth and width.
The implementation is simple and uses arena allocation where nodes are stored in a `Vec`.
No unsafe blocks and no additional overhead from using smart pointers.
