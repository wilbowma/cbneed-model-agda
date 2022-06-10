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
Scope : {l : Level} -> Set (lsuc l)
Scope {l} = List (Name × Set l)

data Env {l : Level} : (scope : Scope {l}) -> Set (lsuc (lsuc l)) where
  env-empty : {scope : Scope {l}} -> Env []
  env-add : {A : Set l} -> {scope : Scope} -> Env scope -> (key : String) -> A
          -> Env ((key , A) ∷ scope)

data ⊥ : Set where

data InScope {l : Level} (scope : Scope {l}) (key : String) (A : Set l) : Set (lsuc l) where
  scope-found : (S : Scope {l}) -> scope ≡ ((key , A) ∷ S) -> InScope scope key A
  scope-cons : {B : Set l} -> (S : Scope) (key' : String) -> scope ≡ (key' , B) ∷ S -> ((key' ≡ key) -> ⊥) ->
    InScope S key A -> InScope scope key A

-- InScope : Scope -> String -> Set
-- InScope [] k = ⊥
-- InScope (k' ∷ S) k = if (k == k') then k ≡ k' else InScope S k

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

env-get : {l : Level} {S : Scope} {A : Set l} -> Env S -> (key : String) -> (InScope S key A)
        -> A
env-get (env-add env key₁ x) .key₁ (scope-found S refl) = x
env-get (env-add env key₁ x) key (scope-cons S .key₁ refl x₂ in-scope) = env-get env key in-scope
env-get {S = .[]} env-empty key scope with impossibleScope scope
... | ()

record Config {l2 : Level} {l : Level} (A : Set l2) (scope : Scope {l}) : (Set (lsuc (lsuc (lmax l l2)))) where
  inductive
  constructor state
  field
    ele : A
    env : Env scope

-- (well-scoped) State Monad
M : {l1 : Level} {S1 : Scope {l1}} {S2 : Scope {l1}} {l : Level} -> Set l -> Set (lsuc (lmax l l1))
M {S1 = S1} {S2 = S2} A = (env : Env S1) -> Config A S2

return : {S : Scope} {l : Level} -> {A : Set l} -> A -> M {S1 = S} {S2 = S} A
return {A = A} a e = (state a e)

bindf : ∀ {l1 l2} {A : Set l1} {B : Set l2} {S1 S2 S3 : Scope}
      -> M {S1 = S1} {S2 = S2} A -> (A -> M {S1 = S2} {S2 = S3} B) -> M {S1 = S1} {S2 = S3} B
bindf {_} {_} {A} {B} a f =
  λ e -> let r = (a e) in ((f (Config.ele r)) (Config.env r))

set : {S : Scope} {A : Set} -> (key : String) -> A -> M {S1 = S} {S2 = (key , A) ∷ S} A
set {S} {A} key x env = state x (env-add env key x)

local : {S1 S2 : Scope} {A : Set} -> M {S1 = S1} {S2} A -> M {S1 = S1} {S1} A
local e env = (state (Config.ele (e env)) env)

test-r : {S : Scope} {A : Set} -> {B : Set}
       -> M {S1 = ("foo" , A) ∷ S} {("foo" , A) ∷ S} B
       -> M {S1 = S} {S} (A -> M {S1 = S} {("foo" , A) ∷ S} B)
test-r {S} {A} e = return (λ x → bindf (set "foo" x) (λ ⊤ -> e))

get : {l : Level} {S : Scope {l}} {A : Set l} -> (key : String) -> {InScope S key A} -> M {S1 = S} A
get key {scope} env = (state (env-get env key scope) env)

run : {S2 : Scope} {A : Set} -> M {S1 = []} {S2} A -> A
run {A} f = Config.ele (f (env-empty {_} {[]}))

test1 : run (return 5) ≡ 5
test1 = refl

-- Syntax and model construction

data Type : Set where
  tNat : Type
  tBool : Type
  tFun : Type -> Type -> Type

El : Type -> Set
El tNat = ℕ
El tBool = Bool
El (tFun x x₁) = M (El x) -> M (El x₁)

data Term : Scope -> Type -> Set₃ where
  var : {s : Scope} {A : Type} -> (n : Name) -> InScope s n (El A) -> Term s A
  nlit : {s : Scope} -> ℕ -> Term s tNat
  blit : {s : Scope} -> Bool -> Term s tBool
  tif : {s : Scope} {A : Type} -> Term s tBool -> Term s A -> Term s A -> Term s A
  top : {s : Scope} {A B C : Type}
      -> (El A -> El B -> El C)
      -> Term s A -> Term s B -> Term s C
  tlam : {s : Scope} {B : Type} -> (n : Name) -> (A : Type) -> Term ((n , El A) ∷ s) B -> Term s (tFun A B)
  tapp : {S : Scope} {A B : Type} -> Term S (tFun A B) -> Term S A -> Term S B

model : {l1 l2 : Level} {S : Scope {l1}} {A : Type}
      -> Term S A
      -> Σ Scope (λ S2 -> M {S1 = S} {S2} (El A))
model {S = S} {A = A} (var n x) = S , get n {x}
model {S = S} (nlit x) = S , return x
model {S = S} (blit x) = S , return x
model {S = S} (tif {S} term term₁ term₂) =
  let r = model {S = S} term in
  let r1 = model {S = S} term₁ in
  let r2 = model {S = S} term₂ in
    -- See problem 2 in README
    ((fst r2) , (bindf {S2 = S} (local (snd r)) (λ x -> if x then {!!} else snd r2))) -- if x then snd r1 else snd r2)))
model {S = S} (top op term₁ term₂) =
  let r1 = model term₁ in
  let r2 = model term₂ in
  S , (bindf (local (snd r1)) λ x -> (bindf (local (snd r2)) λ y -> return (op x y)))
model {S = S} (tlam n A e) =
  let body = model e in
    S , return (λ x → bindf x (λ v -> bindf (set n v) (λ ⊤ -> (snd body))))
model (tapp term₁ term₂) =
  let r1 = (model term₁) in
  let r2 = (model term₂) in
    (fst r1) , bindf (snd r1) (λ f -> (f (snd r2)))
