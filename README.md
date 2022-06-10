An experiment in modeling CBneed
==

I'm trying to learn Agda, and understand modeling a little better, so I started
modeling this little call-by-need language in Agda.

The idea is to provide a model of call-by-need in the state monad.
The state uses a map from names to monadic computations.

This causes two problems in my model that I don't know how to solve yet:

First, the model has some universe problems.
The encoding of the monad, `M`, involves an environment, `Env`.
`Env` is a map from Names to computations of type `M` because the computations are call-by-need.
This seems only resolved if we admit `Type : Type`, since the universe of the
environment must be large enough to contain `M`, but the universe of `M` must
large enough to contain `Env`, so...
Possibly, it would be resolved if I could describe the universe of
computations allowed in the monad, which is not the universe of all Agda terms?

Second, `Env` is indexed by a scope, to ensure well-scoped dereferencing.
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
Maybe something.. sets-of-scopey? Can we promote the alternative scope to the
former scope, at least in this case?
