# Stratified higher-order state for a call-by-need STLC model

## Summary

A layered heap gives a shallow embedding of call-by-need STLC in Agda that
passes the termination checker with no `TERMINATING` pragma, fuel or
postulates (`Stratified.agda`). The caveat: it covers a stratified fragment of
STLC, not all of it.

The obstruction is not termination but memoization. A call-by-need variable
names one heap cell holding one semantic value, so that value must live at one
level. Some STLC programs need the same stored function at two different
levels, and no single level works (see the expanded example below).

## The construction

The heap is split into layers, the way the paper stratifies worlds: a thunk in
layer `j` is a computation over the layers below `j` only.

```
World (suc k) = World k × List (Ty k)            -- shapes only, no semantic content
Heap  (suc k) = Heap k × cells of (Val k ⊎ Comp k)
Comp k A W    = ∀ W' ≥ W → Heap k W' → Σ W'' ≥ W'. Heap k W'' × Val k A W''
Val k (fun p A B) W = ∀ W' ≥ W → Loc W' j A → Comp k B W'
```

- **Why it terminates:** `Heap k` only mentions `Val`/`Comp` at level `k-1`.
  Recursion is ordered by level, then by type, so `Store ≅ Store → Store × Val`
  never arises.
- **No type-world circularity:** worlds are first-order lists of syntactic
  types.
- **No black-holing:** a thunk being forced runs on lower layers only, so it
  cannot see its own cell.
- **Typing:** as in λPR, function types carry levels. `fun p A B : Ty m` puts
  the parameter cell in a layer `j < m`.
- **Weakening:** arguments are typed under a thinning of the context (the
  paper's free-variable λ rule), and a `lift` former gives cumulativity.

## Tests

The source language has no effects, so sharing is checked by inspecting the
final heap. Each test reports the result and the number of forced and unforced
cells. Each test is checked by `refl`; changing one expected number makes Agda
reject the file.

| Program                                | Result | Forced | Unforced | Shows                                                  |
| -------------------------------------- | ------ | ------ | -------- | ------------------------------------------------------ |
| `(λx. x + x) (2 + 3)`                  | 10     | 1      | 0        | one cell for `x`, used twice                           |
| `(λx. 3) (2 + 3)`                      | 3      | 0      | 1        | unused argument never forced                           |
| `(λf. f 1 + f 2) (λy. y + 1)`          | 5      | 3      | 0        | function value memoized in `f`'s cell                  |
| `(λf. f 0 + f 0) ((λy.λz.y) 7)`        | 14     | 2      | 2        | memoized closure shares a cell allocated while forcing |

## Why it can't cover all of STLC

The two closures in the example could live at different levels. The problem
is `g`. Both calls go through the same `g`, which is one cell holding one
memoized value. So `g` has one level, and that level fixes where its arguments
must live.

### The program

```
(λg. g (λn. g (λm. m)))  G        where  G = (λh. h) (λf. f 0)
```

Here `g : (nat → nat) → nat`. `G` is not a value, so `g`'s cell starts as a
thunk. Call-by-need forces it once and memoizes the result, however many times
`g` is used.

### By translation to λPR

The easiest way to see the problem is to translate call-by-need into λPR with
the usual memoizing-thunk encoding, packaged as promises. Only functions and
references are needed:

A promise `⌈e⌉` has type `⌈τ⌉ᵏ`, and `⌊x⌋` forces it:

```
⌈τ⌉ᵏ  ≜ Ref (Unit →ᵏ τ)
⌈e⌉   ≜ new (λ_:Unit. e)
⌊x⌋   ≜ let v = (!x) () in x := (λ_:Unit. v); v

⟦nat⟧    = Nat
⟦A → B⟧  = ⌈⟦A⟧⌉ → ⟦B⟧                      -- every argument is a promise
x : A    ↦ x : ⌈⟦A⟧⌉                        -- every variable is a promise

⟦x⟧      = ⌊x⌋
⟦λx. e⟧  = λx. ⟦e⟧
⟦e₁ e₂⟧  = ⟦e₁⟧ ⌈⟦e₂⟧⌉
```

`⌈τ⌉ᵏ :: Type_{k+1}` when `τ :: Type_i` and `k ≥ i`. The memo write in `⌊x⌋`
type-checks, because `λ_:Unit. v` only captures `v : τ`.

The program becomes

```
(λg. ⌊g⌋ ⌈λn. ⌊g⌋ ⌈λm. ⌊m⌋⌉⌉)  ⌈(λh. ⌊h⌋) ⌈λf. ⌊f⌋ ⌈0⌉⌉⌉
```

`counterexample.tex` (built as `counterexample.pdf`) typesets the translation
and the failing λPR derivation, with the unsatisfiable side condition
highlighted. Write `N` for a `nat` cell, `F = ⟦nat → nat⟧`, `R` for `g`'s
argument cell, `τg = ⟦(nat → nat) → nat⟧`, and `T` for `g`'s own cell, with
level variables `a, b, c, d`. Kinding `T` gives `c ≥ 1`, `b ≥ c`, `d ≥ b+1` and
`a ≥ d`. Typing the closure `λn. ⌊g⌋ ⌈…⌉` gives `c ≥ a+1`, because it
captures `g`. Chaining these gives `c ≥ a+1 ≥ d+1 ≥ b+2 ≥ c+2`, so λPR rejects the
translation. The two `+1`s are both the Ref rule: one from `g`'s argument
being a cell (`d ≥ b+1`), one from the closure capturing `g`'s cell
(`c ≥ a+1`). The plain CBV translation, the identity, types with every level
at 0.

The Agda model is a semantics of this image. Its three facts below line up
with the rows of the table.

### Three facts about the layered model

These are not typing choices. Each follows from what the denotations quantify
over.

1. **A cell's layer bounds its value's level** (`a ≥ d`). A cell in layer `jg`
   is part of `Heap (jg+1)`, which may only mention `Val`/`Comp` at levels ≤
   `jg`. So `g`'s value is a function at some level `m ≤ jg`.
2. **A level-`m` function only accepts arguments in layers below `m`**
   (`d ≥ b+1`). Its denotation is `∀ W' : World m → Loc W' i A → …`, and
   `World m` has no layers ≥ `m`. A pointer into a higher layer is not a value
   of that type at all.
3. **A thunk lives above every cell it captures** (`c ≥ a+1`). Its computation
   runs on the layers below its own.

### The chase

Let `i` be the layer of `g`'s parameter. Both arguments to `g` must be
allocated there.

- The inner argument `λm. m` captures nothing, so it fits in any layer.
- The outer argument `c = λn. g (λm. m)` captures `g`'s cell. By fact 3 it
  needs a layer above `jg`.
- By facts 1 and 2, `i < m ≤ jg`. So `c` needs a layer above `jg`, but it must
  sit in layer `i`, which is below `jg`.

Raising the level of `g`'s parameter type doesn't help, because `g`'s own
level rises with it:

| Parameter layer `i` | `g`'s level `m` | `g`'s cell layer `jg` | `c` needs layer | Fits in `i`? |
| ------------------- | --------------- | --------------------- | --------------- | ------------ |
| 0                   | ≥ 1             | ≥ 1                   | ≥ 2             | no           |
| 1                   | ≥ 2             | ≥ 2                   | ≥ 3             | no           |
| 5                   | ≥ 6             | ≥ 6                   | ≥ 7             | no           |
| L                   | ≥ L+1           | ≥ L+1                 | ≥ L+2           | no           |

The gap is always at least 2, so the chase never closes.

### Why implicit levels don't rescue it

Since STLC has no level annotations, the model needs an elaboration that picks
levels. Using `g` at two levels has only two possible meanings, and both fail:

- **One level-polymorphic stored value.** `g`'s value would quantify over
  heaps at every level, including layers above its own cell. That is the
  circular `Store ≅ Store → …` again.
- **Two copies of `g`, one per level.** Elaborate `g`'s thunk once per use.
  Then `G` is evaluated twice, which is call-by-name for `g`. The source
  language cannot observe the difference, but the heap no longer models
  call-by-need: there are two cells where there should be one.

### Contrast with call-by-value

**Plain CBV STLC has no such problem.** In λPR, a function's level only has
to satisfy `k ≥ max-level(FV(e), τ1, τ2)`. That bound is non-strict, because
functions are immutable (§3 of the paper). In the program above:

- `g : (nat →^i nat) →^m nat` needs `m ≥ i`.
- `c = λn. g (λm. m)` captures the *variable* `g`, so `c`'s level is ≥ `m`.
- `c` is `g`'s argument, so `c`'s level is `i`, giving `i ≥ m`.

`i = m` satisfies all three. Without `Ref` everything is in `Type0` anyway.
Semantically `Val (A → B) = Val A → Val B`: `g` takes a value, not a pointer
into a layer, so one value of `g` serves both calls.

**CBV with references fails in the same way.** The translation above is just
CBV λPR with every binder turned into a `Ref` by hand. Its failure has the
shape of the stratified Landin's knot (§5 of the paper), but the program
terminates.

**Where the gap of 2 comes from.** Both strict inequalities are the Ref rule's
+1, applied to variables that are cells:

1. *Arguments are locations.* `⟦A → B⟧` has a `Ref` domain, so the function
   sits strictly above its argument cell. In CBV it takes a `Val`, which
   allows `i ≤ m`.
2. *Capturing a variable captures a cell.* A closure sits strictly above the
   cells it captures.

Under CBV with the free-variable λ rule both are non-strict, and the gap
is 0.

**Surface reading.** `g`'s memoized function is applied to `c`, and `c`
reaches back into `g`'s own cell. So a stored function has a heap effect on a
cell allocated after it (forcing `c`). That is a value that refers to a future
allocation, the impredicative case that the stratified model rules out by
construction. The self-reference is harmless here: `g`'s cell is already a
value by the time `c` reads it. That is a run-time fact, though, and levels
come from types. As in λPR, a cell's level is fixed by the type of its
contents, whether or not it is ever written again.

We conjecture that the stratified model of call-by-need is total on exactly
the programs whose translation λPR accepts. This is not proved. In CBV, the programmer chooses
which variables become refs and pays for them knowingly. Call-by-need makes
every variable a ref, so the restriction hits programs that never look
stateful.

The heap at run time is still acyclic here. Its dependency order is real; it
just isn't determined by the types.

## Next steps and notes

Possible directions:

1. **Don't memoize syntactic values.** A thunk that is already a λ can be
   copied per level without losing sharing, though its captured cells still
   constrain it. This handles `g` bound to a literal λ, but not to `G` above.
2. **Defunctionalize.** Store syntax plus environments of locations, so the
   heap is first-order. There is no circularity, but termination then needs a
   logical relation instead of structural recursion.
3. **Impredicativity.** The level-polymorphic reading of `g` is impredicative
   instantiation, so something like impredicative `Set` might work.

Practical notes:

- The file uses the standard library (2.2). It checks with Agda 2.7.0.1 as
  `agda -l standard-library -i . Stratified.agda`, in about 8s, most of which
  is loading the library.
- `model.agda` is untouched, and nothing is committed.
