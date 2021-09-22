{ name = "clowns-n-jokers-dissections"
, dependencies =
  [ "bifunctors"
  , "console"
  , "effect"
  , "either"
  , "fixed-points"
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
