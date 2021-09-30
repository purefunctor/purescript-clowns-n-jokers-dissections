{ name = "clowns-n-jokers-dissections"
, dependencies =
  [ "bifunctors"
  , "console"
  , "effect"
  , "either"
  , "fixed-points"
  , "foldable-traversable"
  , "functors"
  , "lists"
  , "partial"
  , "prelude"
  , "psci-support"
  , "tailrec"
  , "tuples"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
