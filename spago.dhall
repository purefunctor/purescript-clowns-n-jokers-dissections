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
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
