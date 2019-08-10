# Design notes for the inevitable Cubical rewrite

- Use Cubical Agda, take univalent categories as the basic notion.
- Categories should have one level instead of 3 (one each for
  objects/arrows/equalities).
  - pro: Things like the Yoneda functor only work for 'one-level' categories.
  - con: Have to explicitly lift lots of stuff when defining constructions.
  - con: Current situation can be worked around by constructing a lifted
    category when necessary. With the proposal, the same applies, but we may
    have to lift even more.
- See what happens if we use Category as a typeclass. Is instance resolution
  smart enough to make that work? Similar for products/exponentials/...
- Define constructions (functors, natural transformations, limits etc.) in the
  same module as the associated category/functor/... (?).
  - pro: Minimises the number of modules you have to import to work with these
    structures.
  - con: Is there always an 'obvious' location for these structures?
- Look at Paolo Capriotti's library for inspiration.
- Have uniform notation for things that can be applied. Suggestion:

  record Functor (C D : Category) where
    field
      _$_ : Obj C -> Obj D
      _<$>_ : Hom C c d -> Hom D (_$_ c) (_$_ d)

  If we take advantage of Agda's overloaded record projections, we don't even
  need to use typeclasses for this.
- It's annoying that a category can only contain things at some specific level.
  This means, for example, that the composition from Cat can only be used if
  all participating functors are at the same level -- even though we can easily
  define a composition operator that composes functors at different levels.
  Can we do something about that?
- Forward composition as default?!???!!!1
- disable eta for records?
  - what are pros/cons of this?
