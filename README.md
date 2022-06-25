An experiment in modeling CBneed
==

I'm trying to learn Agda, and understand modeling a little better, so I started
modeling this little call-by-need language in Agda.

The idea is to provide a model of call-by-need in the state monad.
The state uses a map from names to monadic computations.

This causes some problems in my model that I don't know how to solve yet:

The model had a universe problem.
The encoding of the monad, `M`, involves an environment, `Store`.
`Store` is a map from Names to computations of type `M` because the computations are call-by-need.

To solve this, we define the universe of types to consider, `U`, and two element
functions `ElV`, for the types of values, and `ElC`, for the types of
computations.

Unfortunately, `ElV` calls `ElC` in a non-positive position since functions are
call-by-need, since `M` contains the store which contains elements of `ElC`, the
whole mutual definition is not terminating (and indeed, typechecking does not
terminate when we claim it is).

Second, `Store` is indexed by a scope, to ensure well-scoped dereferencing.
The monad tracks this; it is indexed by a starting and ending scope.
Unfortunately, this means at branch points, `if`, both branches must produce
the same ending scope, which is impossible in general.
Consider an `if V then ((lambda (x) x) 5) else 5`
The consequent branch creates a different environment than the alternative,
by design.
Operationally, this should evaluate as:
```
   env; if true then ((lambda (x) x) 5) else 5
-> env; ((lambda (x) x) 5)
-> env[x -> 5]; x
```
Or
```
   env; if false then ((lambda (x) x) 5) else 5
-> env; 5
```
Maybe something.. sets-of-scopey? Or some kind of weakening lemma?

This can be worked around, it seems, by leaving the new environment as a
unification variable.
