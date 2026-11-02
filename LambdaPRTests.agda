------------------------------------------------------------------------
-- Tests for LambdaPR.agda.  Each test runs a closed program in the
-- shallow model and checks (result , cells left in the final heap) by
-- refl, so changing an expected number makes Agda reject the file.
------------------------------------------------------------------------

module LambdaPRTests where

open import Data.Nat using (ℕ; _≤′_; ≤′-refl; ≤′-step)
open import Data.Product using (Σ; _,_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Binary.Sublist.Propositional
  using (_⊆_; []; _∷_; _∷ʳ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import LambdaPR

0≤1 : 0 ≤′ 1
0≤1 = ≤′-step ≤′-refl

-- The empty thinning: a closed λ in any context.
none : ∀ {Γ : Ctx} → [] ⊆ Γ
none {[]}    = []
none {x ∷ Γ} = x ∷ʳ none

-- (λ⁰ x : Nat. x) 5  ⇒  5
idApp : [] ⊢ nat
idApp = app (lam {A = nat} {B = nat} [] ≤′-refl ≤′-refl [] (var (here refl))) (num 5)

_ : runNat idApp ≡ (5 , 0)
_ = refl

-- (λ¹ r : Ref Nat. (λ¹ _ : Unit. !r) (r := 4)) (new 3)  ⇒  4, one cell
refUpdate : [] ⊢ nat
refUpdate =
  app (lam {A = ref nat} {B = nat} [] ≤′-refl 0≤1 []
         (app (lam {A = unit} {B = nat} (refl ∷ []) 0≤1 0≤1 (≤′-refl ∷ [])
                 (get (var (there (here refl)))))
              (put (var (here refl)) (num 4))))
      (new (num 3))

_ : runNat refUpdate ≡ (4 , 1)
_ = refl

-- A function in the heap:
--   (λ¹ r : Ref F. (λ¹ _ : Unit. (!r) 0) (r := λ⁰ x. 7)) (new (λ⁰ x. x))
--   ⇒  7, one cell
-- λ⁰ x. 7 is built in r's scope.  It does not use r, so under the
-- free-variable λ rule it stays at level 0 and fits in a cell of type
-- Ref F.  Under the whole-context rule it would be at level 1.
F : Ty 0
F = arr ≤′-refl ≤′-refl nat nat

storeFun : [] ⊢ nat
storeFun =
  app (lam {A = ref F} {B = nat} [] ≤′-refl 0≤1 []
         (app (lam {A = unit} {B = nat} (refl ∷ []) 0≤1 0≤1 (≤′-refl ∷ [])
                 (app (get (var (there (here refl)))) (num 0)))
              (put (var (here refl)) (lam none ≤′-refl ≤′-refl [] (num 7)))))
      (new (lam [] ≤′-refl ≤′-refl [] (var (here refl))))

_ : runNat storeFun ≡ (7 , 1)
_ = refl

-- Allocation inside a level-0 function is local to the call:
--   (λ⁰ x : Nat. (λ¹ r : Ref Nat. !r) (new x)) 5  ⇒  5, no cells left
-- whereas the same allocation at top level leaves its cell:
--   (λ¹ r : Ref Nat. !r) (new 5)  ⇒  5, one cell
deref : ∀ {Γ} → Γ ⊢ arr ≤′-refl 0≤1 (ref nat) nat
deref = lam none ≤′-refl 0≤1 [] (get (var (here refl)))

local : [] ⊢ nat
local =
  app (lam {A = nat} {B = nat} [] ≤′-refl ≤′-refl []
         (app deref (new (var (here refl)))))
      (num 5)

_ : runNat local ≡ (5 , 0)
_ = refl

global : [] ⊢ nat
global = app deref (new (num 5))

_ : runNat global ≡ (5 , 1)
_ = refl
