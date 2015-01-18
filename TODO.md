* Finish off re-implementing all mtl classes.

* Make it easier to add newtype wrappers around transformer stacks.

* Implement being able to change out the underlying stack from a
  transformer (e.g. `StateT s m a -> StateT s n a`).

* Clean up API.

    - Determine what needs to be exported
    - Should variadic-functions be exported from Levels.hs?
    - Change Constraint synonyms to type-classes for better error
      reporting?

* Documentation

    - Document modules
    - Add extra documentation modules:
        + How to use the library
        + How to add extra base monads
        + How to add extra levels
        + How to add a new transformer class
        + Dealing with variadic functions

* Test suite

* Benchmarking and performance enhancements
