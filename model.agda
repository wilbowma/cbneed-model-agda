-- {-# OPTIONS --type-in-type #-}
{-# OPTIONS --cumulativity #-}
-- See Problem 1 in README

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

module Exmaples where
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

record Config {l2 : Level} {l : Level} {U : Set l} {El : U -> Set l}
  (A : Set l2) (scope : Scope U) : (Set (lmax l l2)) where
  inductive
  constructor state
  field
    ele : A
    env : Env {El = El} scope

-- (well-scoped) State Monad
M : ∀ {l1 l2} {U : Set l1} {S1 : Scope U} {S2 : Scope U} {El : U -> Set l1}
  -> Set l2 -> Set (lmax l1 l2)
M {S1 = S1} {S2 = S2} {El} A = (env : Env {El = El} S1) -> Config {El = El} A S2

return : {l : Level} {U : Set l} {El : U -> Set l} {S : Scope U} -> {A : Set l}
       -> A -> M {S1 = S} {S2 = S} A
return {A = A} a e = (state a e)

bindf : ∀ {l1 l2} {A : Set l1} {B : Set l2} {S1 S2 S3 : Scope (Set l1)}
      -> M {S1 = S1} {S2 = S2} A
      -> (A -> M {S1 = S2} {S2 = S3} B)
      -> M {S1 = S1} {S2 = S3} B
bindf {_} {_} {A} {B} a f =
  λ e -> let r = (a e) in ((f (Config.ele r)) (Config.env r))

set : ∀ {l} {U : (Set l)} {S : Scope U} {A : U} {El : U -> Set l}
    -> (key : String) -> El A -> M {S1 = S} {S2 = (key , A) ∷ S} ⊤
set key x env = state tt (env-add env key x)

local : ∀ {l} {S1 S2 : Scope (Set l)} {A : Set} -> M {S1 = S1} {S2} A -> M {S1 = S1} {S1} A
local e env = (state (Config.ele (e env)) env)

-- Requires at least --cumulativity?
-- test-r : ∀ {l1 l2} {S : Scope (Set l1)} {A : Set l1} -> {B : Set l2}
--        -> M {S1 = ("foo" , A) ∷ S} {("foo" , A) ∷ S} B
--        -> M {S1 = S} {S} (A -> M {S1 = S} {("foo" , A) ∷ S} B)
-- test-r e = return (λ x → bindf (set "foo" x) (λ ⊤ -> e))

get : {l : Level} {U : (Set l)} {S : Scope U} {El : U -> Set l} {A : U}
    -> (key : String) -> {InScope S key A} -> M {S1 = S} (El A)
get key {scope} env = (state (env-get env key scope) env)

run : ∀ {l} {S2 : Scope (Set l)} {A : Set l} -> M {S1 = []} {S2} A -> A
run {A} f = Config.ele (f (env-empty))

test1 : run (return {El = λ x -> Set} 5) ≡ 5
test1 = refl

-- Syntax and model construction

data Type : Set where
  tNat : Type
  tBool : Type
  tFun : Type -> Type -> Type

Gamma : {S : Scope Set} -> Set₁
Gamma {S = S} = Env {El = λ x -> Type} S

testG : Gamma
testG = env-add env-empty "meow" tNat

test-get : env-get testG "meow" _ ≡ tNat
test-get = refl

El : Type -> Set
El tNat = ℕ
El tBool = Bool
-- Source of Type : Type problem.
-- Really, what do I want here?
El (tFun x x₁) = M (El x) -> M (El x₁)

data Term : {S : Scope Set} -> Gamma {S = S} -> Type -> Set₁ where
  var : {S : Scope Set} {s : Gamma {S = S}} {A : Type}
      -> (n : Name) -> (pf : InScope S n Type)
      -> Term s (env-get s n pf)
  nlit : {s : Gamma} -> ℕ -> Term s tNat
  blit : {s : Gamma} -> Bool -> Term s tBool
  tif : {s : Gamma} {A : Type} -> Term s tBool -> Term s A -> Term s A -> Term s A
  top : {s : Gamma} {A B C : Type}
      -> (El A -> El B -> El C)
      -> Term s A -> Term s B -> Term s C
  tlam : {s : Gamma} {B : Type}
       -> (n : Name) -> (A : Type) -> Term (env-add s n A) B
       -> Term s (tFun A B)
  tapp : {S : Gamma} {A B : Type} -> Term S (tFun A B) -> Term S A -> Term S B

-- modelG : Gamma -> Scope Set
-- modelG [] = []
-- modelG ((fst₁ , snd₁) ∷ x₁) = (fst₁ , (El snd₁)) ∷ (modelG x₁)

model : {S : Scope Set} {G : Gamma {S = S}} {A : Type}
      -> Term G A
      -> Σ (Scope Set) (λ S2 -> M {S1 = S} {S2} (El A))
model {S} {G} {A = A} (var n x) = (n , (M (El A))) ∷ S ,
  bindf (get n {model-in-scope x})
        λ v -> (bindf (set n (return v)) (λ ⊤ -> (return v)))
  where
  model-in-scope : {S : Scope Set} {G : Gamma {S = S}} {n : Name}
                 -> (pf : InScope S n Type) -> InScope S n (El (env-get G n pf))
  model-in-scope pf = {!!}
model {S = S} (nlit x) = S , return x
model {S = S} (blit x) = S , return x
model {S = S} (tif {G} term term₁ term₂) =
  let r = model term in
  let r1 = model term₁ in
  let r2 = model term₂ in
    -- See problem 2 in README
    ((fst r2) , (bindf {S2 = S} (local (snd r))
                       -- if x then snd r1 else snd r2)))
                       (λ x -> if x then {!!} else snd r2)))
model {S = S} (top op term₁ term₂) =
  let r1 = model term₁ in
  let r2 = model term₂ in
  S , (bindf (local (snd r1))
                      λ x -> (bindf (local (snd r2)) λ y -> return (op x y)))
model {S} (tlam n A e) =
  let body = model e in
    S , return (λ x → bindf x (λ v -> bindf (set n v) (λ ⊤ -> (snd body))))
model (tapp term₁ term₂) =
  let r1 = (model term₁) in
  let r2 = (model term₂) in
    (fst r1) , bindf (snd r1) (λ f -> (f (snd r2)))

-- For closed terms
model' : {A : Type}
      -> Term env-empty A
      -> Σ (Scope Set) (λ S2 -> M {S1 = []} {S2} (El A))
model' e = model e

test : (run (snd (model' (nlit 5)))) ≡ 5
test = refl
