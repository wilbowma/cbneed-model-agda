open import Data.Nat
open import Data.Product using (_×_; _,_; Σ) renaming (proj₁ to fst) renaming (proj₂ to snd)
open import Data.Bool
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Level renaming (_⊔_ to lmax; suc to lsuc)
open import Data.String using (String)
open import Data.List using (List; _∷_; [])
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality

-- Model requirements

Name = String

-- A Scope is a map from Names to some Type
Scope : ∀ {l} -> (Set l) -> (Set l)
Scope A = List (Name × A)

-- A well-scoped Environment is a map from Names to *elements* of the Type
-- indicated by the Scope.
data Env {l : Level} {U : Set l} {El : U -> Set l} :
         (scope : Scope U) -> Set l
  where
  env-empty : Env []
  env-add : {A : U} {scope : Scope U}
          -> Env {El = El} scope -> (key : String) -> (El A)
          -> Env ((key , A) ∷ scope)

module Examples where
  -- A scope mapping names to types
  test-scope : Scope Set
  test-scope = (("meow" , ℕ) ∷ [])

  -- A scope mapping names to higher types
  test-scope1 : Scope Set₁
  test-scope1 = (("meow" , Set) ∷ [])

  -- A scope mapping names to nats
  -- Note that Scopes are meant to be type-level, so, these are type-level nat.
  -- The nats do not live in the environment.
  -- This would be a weird scope.
  test-scope2 : Scope ℕ
  test-scope2 = (("meow" , 5) ∷ [])

  -- A typing environment, mapping Names to Types
  -- only valid with cumulativity
  -- test-env : Env {El = λ x -> Set} (("meow" , Set₁) ∷ [])
  -- test-env = env-add env-empty "meow" ℕ

  -- A store. The scope maps Names to Types, while the environment maps each
  -- Names to an elements of those Types.
  -- only valid with cumulativity
  -- test-env1 : Env {El = λ x -> ℕ} (("meow" , Set) ∷ [])
  -- test-env1 = env-add env-empty "meow" 5

  -- Extremely weird environment, where we large eliminate numbers to types
  weirdEl : ℕ -> Set
  weirdEl 5 = ℕ
  weirdEl x = Bool

  -- So the type "5" actually means a value of type ℕ
  test-env2 : Env {El = weirdEl} (("meow" , 5) ∷ [])
  test-env2 = env-add env-empty "meow" 0

  -- The type "1", or any other nat, actually means a value of type Bool
  test-env3 : Env {El = weirdEl} (("meow" , 1) ∷ [])
  test-env3 = env-add env-empty "meow" true

-- eom

-- InScope is a proof that key is bound to A in scope.
-- Probably could replaced with Decidability.
data InScope {l : Level} {U : Set l}
     (scope : Scope U) (key : Name) (A : U) : (Set l)
  where
  scope-found : (S : Scope U) -> scope ≡ ((key , A) ∷ S)
              -> InScope scope key A
  scope-cons : {C : U} -> (S : Scope U) (key' : Name)
             -> scope ≡ (key' , C) ∷ S -> ((key' ≡ key) -> ⊥)
             -> InScope S key A -> InScope scope key A

impossibleScope : {l : Level} {key : Name} {U : Set l} {A : U} -> InScope [] key A -> ⊥
impossibleScope (scope-found S ())
impossibleScope (scope-cons S key' () x₁ pf)

module Test where
  test-InScope : InScope (("meow" , Set) ∷ []) "meow" Set
  test-InScope = scope-found [] refl

  -- only valid with cumulativity
  -- test-InScope1 : InScope {U = Set₁} (("bark", Bool) ∷ ("meow" , Set) ∷ []) "meow" Set
  -- test-InScope1 = scope-cons (("meow" , Set) ∷ []) "bark" refl absurd test-InScope
  --   where
  --   absurd : "bark" ≡ "meow" -> ⊥
  --   absurd ()

  test-InScope2 : {k1 k2 : String} {A : Set}
                -> InScope (("bark" , A) ∷ (k1 , A) ∷ []) k2 A
                -> (k2 ≡ k1) ⊎ (k2 ≡ "bark")
  test-InScope2 {k1} {."bark"} {A} (scope-found .((k1 , A) ∷ []) refl) =
    inj₂ refl
  test-InScope2 {k1} {.k1} {A}
    (scope-cons .((k1 , A) ∷ []) ."bark" refl x₁ (scope-found .[] refl))
    = inj₁ refl
  test-InScope2 {.key'} {k2} {A}
    (scope-cons .((key' , A) ∷ []) ."bark" refl x₁
      (scope-cons .[] key' refl x₂ pf)) with impossibleScope {key = k2} pf
  ... | ()

-- eom

env-get : {l : Level} {U : Set l} {A : U} {S : Scope U} {El : U -> Set l}
        -> Env {El = El} S -> (key : String) -> (InScope S key A)
        -> El A
env-get (env-add env key₁ x) .key₁ (scope-found S refl) = x
env-get (env-add env key₁ x) key (scope-cons S .key₁ refl x₂ in-scope) =
  env-get env key in-scope
env-get {S = .[]} env-empty key scope with impossibleScope scope
... | ()

-- My universe
data U : Set where
  tNat : U
  tBool : U
  tFun : U -> U -> U

-- This would let me create cycles in the store, so the termination checker
-- rejects it.
-- It is not safe to consider (ElC U) consistent as a logic, or terminating,
-- based on this model construction.
-- I'd be okay with that, but I also can't seem to get the definition of El to
-- terminate... maybe something with a later modality?
mutual
  ElV : U -> Set
  --{-# TERMINATING #-}
  ElV tNat = ℕ
  ElV tBool = Bool
  ElV (tFun x x₁) = ElC x -> ElC x₁

  ElC : U -> Set
  ElC x = {!!}
  -- Definitely doesn't terminate.. hmmm... how can I thunk this?
  -- See Problem 1
  --ElC x = M (ElV x)

  Store = Env {U = U} {El = ElC}

  record Config {S : Scope U} (A : Set) : Set where
    inductive
    constructor state
    field
      ele : A
      env : Store S

  -- (well-scoped) State Monad
  M : {S S' : Scope U} -> Set -> Set
  M {S} {S'} A = (env : Store S) -> Config {S'} A

return : {S : Scope U} {A : Set} -> A -> M A
return {A = A} a e = (state a e)

bindf : {A B : Set} {S1 S2 S3 : Scope U}
      -> M {S1} {S2} A
      -> (A -> M {S2} {S3} B)
      -> M {S1} {S3} B
bindf a f =
  λ e -> let r = (a e) in ((f (Config.ele r)) (Config.env r))

set : {S : Scope U} {A : U}
    -> (key : String) -> ElC A
    -> M {S} {(key , A) ∷ S} ⊤
set key x env = state tt (env-add env key x)

local : {S S' : Scope U} {A : Set} -> M {S} {S} A -> M {S} {S} A
local e env = (state (Config.ele (e env)) env)

get : {S : Scope U}  {A : U}
    -> (key : String) -> (InScope S key A)
    -> M {S} (ElV A)
-- Tie's Landin's Knot
get key pf env = (env-get env key pf) env

run : {A : Set} -> M {S = []} A -> A
run {A} f = Config.ele (f (env-empty))

test1 : run (return 5) ≡ 5
test1 = refl

-- Syntax and model construction
Type = U

-- Scope is really just a list of names
gScope = Scope ⊤

Gamma : {S : gScope} -> Set
Gamma {S} = Env {U = ⊤} {El = (λ x -> Type)} S

testG : Gamma
testG = env-add env-empty "meow" tNat

test-get : env-get testG "meow" _ ≡ tNat
test-get = refl


data Term {S : gScope} (G : Gamma) : Type -> Set where
  var : {A : Type}
      -> (n : Name) -> (pf : InScope S n tt)
      -> Term G (env-get G n pf)
  nlit : ℕ -> Term G tNat
  blit : Bool -> Term G tBool
  tif : {A : Type} -> Term G tBool -> Term G A -> Term G A -> Term G A
  top : {A B C : Type}
      -> (ElV A -> ElV B -> ElV C)
      -> Term G A -> Term G B -> Term G C
  tlam : {B : Type}
       -> (n : Name) -> (A : Type) -> Term (env-add G n A) B
       -> Term G (tFun A B)
  tapp : {A B : Type} -> Term G (tFun A B) -> Term G A -> Term G B

model-env : {S : gScope} -> Gamma {S} -> Scope U
model-env env-empty = []
model-env (env-add x key x₁) = (key , x₁) ∷ (model-env x)

scope-preservation : {S : gScope} {key : Name}
                   -> {G : Gamma {S}}
                   -> (pf : (InScope S key tt))
                   -> (InScope (model-env G) key (env-get G key pf))
scope-preservation {G = env-empty} S with (impossibleScope S)
... | ()
scope-preservation {G = env-add G key x} (scope-found S refl) =
  scope-found (model-env G) refl
scope-preservation {G = env-add G key x} (scope-cons S .key refl x₂ pf) =
  scope-cons (model-env G) key refl x₂ (scope-preservation pf)


-- Leave S' as a unification variable to avoid annoying environment passing of
-- the new S', and to avoid Problem 2.
model : {S : gScope} {G : Gamma {S}} {A : Type}
      -> Term G A
      -> M {(model-env G)} (ElV A)
model (var n pf) =
  let th = (get n (scope-preservation pf)) in
    (bindf th (λ e -> bindf (set n (return e)) (λ tt -> (return e))))
model (nlit x) = return x
model (blit x) = return x
model (tif term term₁ term₂) =
  let r = model term in
  let r1 = model term₁ in
  let r2 = model term₂ in
  (bindf r (λ v -> (if v then r1 else r2)))
  -- See problem 2 in README
model {S = S} (top op term₁ term₂) =
  let r1 = model term₁ in
  let r2 = model term₂ in
  (bindf (local r1)
    λ x -> (bindf (local r2) λ y -> return (op x y)))
model {S} (tlam n A e) =
  let body = model e in
    return (λ x → bindf x (λ v -> bindf (set n v) (λ ⊤ -> body)))
model (tapp term₁ term₂) =
  let r1 = (model term₁) in
  let r2 = (model term₂) in
    bindf r1 (λ f -> (f r2))

-- For closed terms
model' : {A : Type}
      -> Term env-empty A
      -> M {[]} (ElV A)
model' e = model e

test : (run (model' (nlit 5))) ≡ 5
test = refl
