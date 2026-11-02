{-# OPTIONS --erasure #-}
------------------------------------------------------------------------
-- Feasibility probe for a cost-preserving representation of the model in
-- LambdaPR.agda (see expressiveness.tex, "Design decisions").
--
-- It checks the pieces a redesign needs, in Agda 2.7 with --erasure:
--   * worlds and Kripke proofs erased (@0), so they cost nothing at run time;
--   * references as indices counted from the oldest cell of their layer,
--     with an erased validity proof, so weakening a reference is O(1);
--   * weakening a function is O(1): it wraps the closure;
--   * reading a cell by index: a walk driven by run-time numbers, with the
--     cell's type fixed up by an erased proof.
-- This is not yet the model itself; LambdaPR.agda has not been ported.
------------------------------------------------------------------------

module ErasureProbe where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.List using (List; []; _∷_; length)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Ty : ℕ → Set where
  nat : Ty 0
  ↑   : ∀ {k} → Ty k → Ty (suc k)
  ref : ∀ {k} → Ty k → Ty (suc k)
  arr : ∀ {k} → Ty k → Ty k → Ty k

World : ℕ → Set
World zero = ⊤
World (suc k) = World k × List (Ty k)

-- position counted from the oldest cell
data _∋[_]_ {X : Set} : List X → ℕ → X → Set where
  here  : ∀ {x xs} → (x ∷ xs) ∋[ length xs ] x
  there : ∀ {x y xs n} → xs ∋[ n ] y → (x ∷ xs) ∋[ n ] y

data Suf {X : Set} : List X → List X → Set where
  stop : ∀ {xs} → Suf xs xs
  more : ∀ {x xs ys} → Suf xs ys → Suf xs (x ∷ ys)

@0 wk∋ : ∀ {X : Set} {xs ys : List X} {n y} → Suf xs ys → xs ∋[ n ] y → ys ∋[ n ] y
wk∋ stop p = p
wk∋ (more q) p = there (wk∋ q p)

@0 _≤W_ : ∀ {k} → @0 World k → @0 World k → Set
_≤W_ {zero} _ _ = ⊤
_≤W_ {suc k} (W , L) (W' , L') = (W ≤W W') × Suf L L'

record Ref {k} (A : Ty k) (@0 L : List (Ty k)) : Set where
  constructor mkRef
  field
    idx : ℕ
    @0 ok : L ∋[ idx ] A

mutual
  @0 Val : (k : ℕ) → Ty k → @0 World k → Set
  Val _ nat _ = ℕ
  Val (suc k) (↑ A) (W , L) = Val k A W
  Val (suc k) (ref A) (W , L) = Ref A L
  Val k (arr A B) W = (@0 W' : World k) → @0 W ≤W W' → Val k A W' → Val k B W'

mono-Val : ∀ {k} (A : Ty k) {@0 W W' : World k} → @0 W ≤W W' → Val k A W → Val k A W'
mono-Val nat q v = v
mono-Val (↑ A) {W , L} {W' , L'} q v = mono-Val A (Data.Product.proj₁ q) v
mono-Val (ref A) {W , L} {W' , L'} q (mkRef n p) = mkRef n (wk∋ (Data.Product.proj₂ q) p)
mono-Val (arr A B) q f = λ W'' q' → f W'' (trans q q')
  where
  @0 trans : ∀ {k} {W₁ W₂ W₃ : World k} → W₁ ≤W W₂ → W₂ ≤W W₃ → W₁ ≤W W₃
  trans {zero} _ _ = tt
  trans {suc k} (a , b) (c , d) = trans a c , suf-trans b d
    where
    @0 suf-trans : ∀ {X : Set} {xs ys zs : List X} → Suf xs ys → Suf ys zs → Suf xs zs
    suf-trans p stop = p
    suf-trans p (more q) = more (suf-trans p q)

open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (_≟_)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
import Data.Nat.Properties

@0 ∋-bound : ∀ {X : Set} {y : X} {xs : List X} {n} → xs ∋[ n ] y → n Data.Nat.< length xs
∋-bound here = Data.Nat.Properties.≤-refl
∋-bound (there p) = Data.Nat.Properties.m<n⇒m<1+n (∋-bound p)

@0 ∋-head : ∀ {X : Set} {x y : X} {xs : List X} → (x ∷ xs) ∋[ length xs ] y → y ≡ x
∋-head here = refl
∋-head (there p) = ⊥-elim (Data.Nat.Properties.<-irrefl refl (∋-bound p))

@0 ∋-tail : ∀ {X : Set} {x y : X} {xs : List X} {n} → (x ∷ xs) ∋[ n ] y → (n ≡ length xs → Data.Empty.⊥) → xs ∋[ n ] y
∋-tail here ne = ⊥-elim (ne refl)
∋-tail (there p) ne = p

cast : ∀ {X : Set} {P : X → Set} {@0 x y : X} → @0 x ≡ y → P x → P y
cast refl v = v

absurd0 : ∀ {@0 A : Set} → @0 Data.Empty.⊥ → A
absurd0 ()

-- Read the cell at an index counted from the oldest cell.  The walk is
-- driven by run-time numbers (the index and the layer's cell count); the
-- type of the cell found is fixed up by an erased proof.
lookupFE : ∀ {X : Set} {P : X → Set} {@0 xs : List X} {@0 y : X} →
           All P xs → (m : ℕ) → @0 m ≡ length xs → (n : ℕ) → @0 xs ∋[ n ] y → P y
lookupFE {P = P} []       m       e n p = absurd0 (no-cell p)
  where @0 no-cell : ∀ {X : Set} {y : X} {n} → [] ∋[ n ] y → Data.Empty.⊥
        no-cell ()
lookupFE {P = P} (c ∷ cs) zero    e n p = absurd0 (zero≢suc e)
  where @0 zero≢suc : ∀ {a} → zero ≡ suc a → Data.Empty.⊥
        zero≢suc ()
lookupFE {P = P} {xs = x ∷ xs} {y} (c ∷ cs) (suc m) e n p = go (n ≟ m) p
  where
  go : Relation.Nullary.Dec (n ≡ m) → @0 (x ∷ xs) ∋[ n ] y → P y
  go (yes refl) p = cast (Relation.Binary.PropositionalEquality.sym
                        (∋-head (Relation.Binary.PropositionalEquality.subst
                                  (λ k → (x ∷ xs) ∋[ k ] _) (Data.Nat.Properties.suc-injective e) p))) c
  go (no ne) p = lookupFE cs m (Data.Nat.Properties.suc-injective e) n
                   (∋-tail p (λ q → ne (Relation.Binary.PropositionalEquality.trans q
                                         (Relation.Binary.PropositionalEquality.sym
                                           (Data.Nat.Properties.suc-injective e)))))
