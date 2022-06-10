{-# OPTIONS --type-in-type #-}
-- See Problem 1 in README

open import Data.Nat
open import Data.Product using (_×_; _,_; Σ) renaming (proj₁ to fst) renaming (proj₂ to snd)
open import Data.Bool
open import Data.Sum renaming (map to sum-map)
open import Agda.Primitive renaming (_⊔_ to lmax)
open import Data.String renaming (length to string-length) renaming (_++_ to string-append)
open import Data.List using (List; _∷_; []; length; map; _++_)
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Relation.Binary.PropositionalEquality using (refl; cong; subst)

-- Model requirements

Name = String

Scope : ∀ {l} -> (Set l) -> (Set l)
Scope A = List (Name × A)

data Env {l : Level} : (scope : Scope (Set l)) -> Set l where
  env-empty : {scope : Scope (Set l)} -> Env []
  env-add : {A : Set l} {scope : Scope (Set l)}
          -> Env scope -> (key : String) -> (a : A)
          -> Env ((key , A) ∷ scope)

data ⊥ : Set where

data InScope {l : Level} {A : Set l} (scope : Scope A) (key : Name) (B : A) : (Set l) where
  scope-found : (S : Scope A) -> scope ≡ ((key , B) ∷ S) -> InScope scope key B
  scope-cons : {C : A} -> (S : Scope A) (key' : Name)
             -> scope ≡ (key' , C) ∷ S -> ((key' ≡ key) -> ⊥)
             -> InScope S key B -> InScope scope key B

test-InScope : InScope (("meow" , ℕ) ∷ []) "meow" ℕ
test-InScope = scope-found [] refl

test-InScope1 : InScope (("bark", Bool) ∷ ("meow" , ℕ) ∷ []) "meow" ℕ
test-InScope1 = scope-cons (("meow" , ℕ) ∷ []) "bark" refl absurd test-InScope
  where
  absurd : "bark" ≡ "meow" -> ⊥
  absurd ()

impossibleScope : {l : Level} {key : Name} {A : Set l} -> InScope [] key A -> ⊥
impossibleScope (scope-found S ())
impossibleScope (scope-cons S key' () x₁ pf)

test-InScope2 : {k1 k2 : String} {A : Set}
              -> InScope (("bark" , A) ∷ (k1 , A) ∷ []) k2 A
              -> (k2 ≡ k1) ⊎ (k2 ≡ "bark")
test-InScope2 {k1} {."bark"} {A} (scope-found .((k1 , A) ∷ []) refl) = inj₂ refl
test-InScope2 {k1} {.k1} {A} (scope-cons .((k1 , A) ∷ []) ."bark" refl x₁ (scope-found .[] refl)) = inj₁ refl
test-InScope2 {.key'} {k2} {A} (scope-cons .((key' , A) ∷ []) ."bark" refl x₁ (scope-cons .[] key' refl x₂ pf)) with impossibleScope {key = k2} pf
... | ()

env-get : {l : Level} {S : Scope (Set l)} {A : Set l} -> Env S -> (key : String) -> (InScope S key A)
        -> A
env-get (env-add env key₁ x) .key₁ (scope-found S refl) = x
env-get (env-add env key₁ x) key (scope-cons S .key₁ refl x₂ in-scope) = env-get env key in-scope
env-get {S = .[]} env-empty key scope with impossibleScope scope
... | ()

record Config {l2 : Level} {l : Level} (A : Set l2) (scope : Scope (Set l)) : (Set (lsuc (lsuc (lmax l l2)))) where
  inductive
  constructor state
  field
    ele : A
    env : Env scope

-- (well-scoped) State Monad
M : {l1 : Level} {S1 : Scope (Set l1)} {S2 : Scope (Set l1)} {l : Level} -> Set l -> Set (lsuc (lmax l l1))
M {S1 = S1} {S2 = S2} A = (env : Env S1) -> Config A S2

return : {l : Level} {S : Scope (Set l)} -> {A : Set l} -> A -> M {S1 = S} {S2 = S} A
return {A = A} a e = (state a e)

bindf : ∀ {l1 l2} {A : Set l1} {B : Set l2} {S1 S2 S3 : Scope (Set l1)}
      -> M {S1 = S1} {S2 = S2} A -> (A -> M {S1 = S2} {S2 = S3} B) -> M {S1 = S1} {S2 = S3} B
bindf {_} {_} {A} {B} a f =
  λ e -> let r = (a e) in ((f (Config.ele r)) (Config.env r))

set : ∀ {l1} {S : Scope (Set l1)} {A : Set} -> (key : String) -> A -> M {S1 = S} {S2 = (key , A) ∷ S} A
set {S} {A} key x env = state x (env-add env key x)

local : ∀ {l} {S1 S2 : Scope (Set l)} {A : Set} -> M {S1 = S1} {S2} A -> M {S1 = S1} {S1} A
local e env = (state (Config.ele (e env)) env)

test-r : ∀ {l} {S : Scope (Set l)} {A : Set} -> {B : Set}
       -> M {S1 = ("foo" , A) ∷ S} {("foo" , A) ∷ S} B
       -> M {S1 = S} {S} (A -> M {S1 = S} {("foo" , A) ∷ S} B)
test-r {S} {A} e = return (λ x → bindf (set "foo" x) (λ ⊤ -> e))

get : {l : Level} {S : Scope (Set l)} {A : Set l} -> (key : String) -> {InScope S key A} -> M {S1 = S} A
get key {scope} env = (state (env-get env key scope) env)

run : ∀ {l} {S2 : Scope (Set l)} {A : Set} -> M {S1 = []} {S2} A -> A
run {A} f = Config.ele (f (env-empty {_} {[]}))

test1 : run (return 5) ≡ 5
test1 = refl

-- Syntax and model construction

data Type : Set where
  tNat : Type
  tBool : Type
  tFun : Type -> Type -> Type

Gamma = Scope Type

El : Type -> Set
El tNat = ℕ
El tBool = Bool
El (tFun x x₁) = M (El x) -> M (El x₁)

data Term : Gamma -> Type -> Set₃ where
  var : {s : Gamma} {A : Type} -> (n : Name) -> InScope s n A -> Term s A
  nlit : {s : Gamma} -> ℕ -> Term s tNat
  blit : {s : Gamma} -> Bool -> Term s tBool
  tif : {s : Gamma} {A : Type} -> Term s tBool -> Term s A -> Term s A -> Term s A
  top : {s : Gamma} {A B C : Type}
      -> (El A -> El B -> El C)
      -> Term s A -> Term s B -> Term s C
  tlam : {s : Gamma} {B : Type} -> (n : Name) -> (A : Type) -> Term ((n , A) ∷ s) B -> Term s (tFun A B)
  tapp : {S : Gamma} {A B : Type} -> Term S (tFun A B) -> Term S A -> Term S B

modelG : Gamma -> Scope Set
modelG [] = []
modelG ((fst₁ , snd₁) ∷ x₁) = (fst₁ , (El snd₁)) ∷ (modelG x₁)

model : {G : Gamma} {A : Type}
      -> Term G A
      -> Σ (Scope Set) (λ S2 -> M {S1 = (modelG G)} {S2} (El A))
model {G} {A = A} (var n x) = (modelG G) , get n {model-in-scope G x}
  where
  model-in-scope : Gamma -> InScope G n A -> InScope (modelG G) n (El A)
  model-in-scope = {!!}
model {G} (nlit x) = (modelG G) , return x
model {G} (blit x) = (modelG G) , return x
model {G} (tif {G} term term₁ term₂) =
  let r = model {G} term in
  let r1 = model {G} term₁ in
  let r2 = model {G} term₂ in
    -- See problem 2 in README
    ((fst r2) , (bindf {S2 = (modelG G)} (local (snd r)) (λ x -> if x then {!!} else snd r2))) -- if x then snd r1 else snd r2)))
model {G} (top op term₁ term₂) =
  let r1 = model term₁ in
  let r2 = model term₂ in
  (modelG G) , (bindf (local (snd r1)) λ x -> (bindf (local (snd r2)) λ y -> return (op x y)))
model {G} (tlam n A e) =
  let body = model e in
    (modelG G) , return (λ x → bindf x (λ v -> bindf (set n v) (λ ⊤ -> (snd body))))
model (tapp term₁ term₂) =
  let r1 = (model term₁) in
  let r2 = (model term₂) in
    (fst r1) , bindf (snd r1) (λ f -> (f (snd r2)))
