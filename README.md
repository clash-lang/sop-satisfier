# SoP Satisfier

~~Kind of SMT solver with only Non-linear Natural Arithmetic.~~

Library with an SMTlib like interface to declare and assert SoP (kind of) expressions.

Interface:
- `declare` - to declare expression to the state
- `assert` - to assert that expression holds in the state
- `unify` - to get a list of expressions that need to hold for the given expression to hold (only equalities are supported)
- `range` - to get a range (a pair of minimum and maximum possible values) of expression
