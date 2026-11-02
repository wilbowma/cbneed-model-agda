------------------------------------------------------------------------
-- Adequacy of the shallow model of λPR (LambdaPR.agda) with respect to
-- λPR's operational semantics.
--
-- The operational semantics is the paper's (Fig. 5) in big-step,
-- environment style: one flat heap, fresh locations appended at the end,
-- no stratification.
--
-- The simulation relates semantic values to runtime values, and semantic
-- heaps to runtime heaps through a map from semantic cells to runtime
-- addresses.  A semantic cell is named by its key: its layer and its
-- position counted from the oldest cell of that layer.  Keys do not change
-- as worlds grow, so maps are plain functions on keys.
--
-- Main results:
--   fundamental : every semantic computation is matched by an operational
--                 run with related results, related heaps, an injective
--                 map from semantic cells to runtime cells, and a frame
--                 condition: runtime cells outside the map are untouched.
--   adequacy    : for a closed program of type Nat, the operational
--                 semantics returns exactly the number the model computes.
--   termination : every closed, well-typed program evaluates.
------------------------------------------------------------------------

module LambdaPRAdequacy where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat
  using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; <-≤-trans; <-irrefl; n<1+n; m<n⇒m<1+n; m≤n⇒m≤1+n;
         suc-injective; <⇒≢; ≤′-trans; m≤m⊔n; m≤n⊔m)
  renaming (_≟_ to _≟ℕ_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise-≡⇒≡)
open import Data.List.Relation.Binary.Suffix.Heterogeneous as Suffix
  using (Suffix)
open import Data.List.Relation.Binary.Sublist.Propositional
  using (_⊆_; []; _∷_; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import LambdaPR

------------------------------------------------------------------------
-- Operational semantics
------------------------------------------------------------------------

data RVal : Set where
  num  : ℕ → RVal
  unit : RVal
  clo  : ∀ {Δ i j} {A : Ty i} {B : Ty j} →
         (i , A) ∷ Δ ⊢ B → All (λ _ → RVal) Δ → RVal
  loc  : ℕ → RVal

REnv : Ctx → Set
REnv Γ = All (λ _ → RVal) Γ

RHeap : Set
RHeap = List RVal

_!_ : RHeap → ℕ → Maybe RVal
[]       ! _     = nothing
(v ∷ rh) ! zero  = just v
(v ∷ rh) ! suc a = rh ! a

snoc : RHeap → RVal → RHeap
snoc []       v = v ∷ []
snoc (w ∷ rh) v = w ∷ snoc rh v

upd : RHeap → ℕ → RVal → RHeap
upd []       _       _ = []
upd (w ∷ rh) zero    v = v ∷ rh
upd (w ∷ rh) (suc a) v = w ∷ upd rh a v

data Eval : ∀ {Γ i} {A : Ty i} → RHeap → REnv Γ → Γ ⊢ A → RHeap → RVal → Set where
  e-var : ∀ {Γ i} {A : Ty i} {rh} {ρ : REnv Γ} {x : (i , A) ∈ Γ} →
          Eval rh ρ (var x) rh (All.lookup ρ x)
  e-num : ∀ {Γ rh} {ρ : REnv Γ} {n} → Eval rh ρ (num n) rh (num n)
  e-unit : ∀ {Γ rh} {ρ : REnv Γ} → Eval rh ρ ⟨⟩ rh unit
  e-lam : ∀ {Γ Δ i j k} {A : Ty i} {B : Ty j} {rh} {ρ : REnv Γ}
            {θ : Δ ⊆ Γ} {p : i ≤′ k} {q : j ≤′ k} {c : Below Δ k}
            {d : (i , A) ∷ Δ ⊢ B} →
          Eval rh ρ (lam θ p q c d) rh (clo d (proj θ ρ))
  e-app : ∀ {Γ i j k} {A : Ty i} {B : Ty j} {p : i ≤′ k} {q : j ≤′ k}
            {d₁ : Γ ⊢ arr p q A B} {d₂ : Γ ⊢ A} {rh rh₁ rh₂ rh₃} {ρ : REnv Γ}
            {Δ i' j'} {A' : Ty i'} {B' : Ty j'} {body : (i' , A') ∷ Δ ⊢ B'}
            {ρ' : REnv Δ} {v₂ v} →
          Eval rh ρ d₁ rh₁ (clo body ρ') → Eval rh₁ ρ d₂ rh₂ v₂ →
          Eval rh₂ (v₂ ∷ ρ') body rh₃ v → Eval rh ρ (app d₁ d₂) rh₃ v
  e-new : ∀ {Γ i} {A : Ty i} {d : Γ ⊢ A} {rh rh₁} {ρ : REnv Γ} {v} →
          Eval rh ρ d rh₁ v → Eval rh ρ (new d) (snoc rh₁ v) (loc (length rh₁))
  e-get : ∀ {Γ i} {A : Ty i} {d : Γ ⊢ ref A} {rh rh₁} {ρ : REnv Γ} {ℓ v} →
          Eval rh ρ d rh₁ (loc ℓ) → rh₁ ! ℓ ≡ just v → Eval rh ρ (get d) rh₁ v
  e-put : ∀ {Γ i} {A : Ty i} {d₁ : Γ ⊢ ref A} {d₂ : Γ ⊢ A} {rh rh₁ rh₂}
            {ρ : REnv Γ} {ℓ v} →
          Eval rh ρ d₁ rh₁ (loc ℓ) → Eval rh₁ ρ d₂ rh₂ v → ℓ < length rh₂ →
          Eval rh ρ (put d₁ d₂) (upd rh₂ ℓ v) unit

-- Runtime heap lemmas ----------------------------------------------------

length-snoc : ∀ rh v → length (snoc rh v) ≡ suc (length rh)
length-snoc []       v = refl
length-snoc (w ∷ rh) v = cong suc (length-snoc rh v)

length-upd : ∀ rh a v → length (upd rh a v) ≡ length rh
length-upd []       a       v = refl
length-upd (w ∷ rh) zero    v = refl
length-upd (w ∷ rh) (suc a) v = cong suc (length-upd rh a v)

!-snoc-old : ∀ rh v {a} → a < length rh → snoc rh v ! a ≡ rh ! a
!-snoc-old (w ∷ rh) v {zero}  _       = refl
!-snoc-old (w ∷ rh) v {suc a} (s≤s p) = !-snoc-old rh v p

!-snoc-new : ∀ rh v → snoc rh v ! length rh ≡ just v
!-snoc-new []       v = refl
!-snoc-new (w ∷ rh) v = !-snoc-new rh v

!-upd-same : ∀ rh {a} v → a < length rh → upd rh a v ! a ≡ just v
!-upd-same (w ∷ rh) {zero}  v _       = refl
!-upd-same (w ∷ rh) {suc a} v (s≤s p) = !-upd-same rh v p

!-upd-other : ∀ rh {a b} v → a ≢ b → upd rh a v ! b ≡ rh ! b
!-upd-other []       {a}     {b}     v ne = refl
!-upd-other (w ∷ rh) {zero}  {zero}  v ne = ⊥-elim (ne refl)
!-upd-other (w ∷ rh) {zero}  {suc b} v ne = refl
!-upd-other (w ∷ rh) {suc a} {zero}  v ne = refl
!-upd-other (w ∷ rh) {suc a} {suc b} v ne = !-upd-other rh v (λ e → ne (cong suc e))

------------------------------------------------------------------------
-- Semantic cells and their keys
------------------------------------------------------------------------

-- Position of a cell counted from the oldest cell in its layer.  Newer
-- cells are consed onto the front, so this does not change as layers grow.
fromEnd : ∀ {X : Set} {x : X} {xs : List X} → x ∈ xs → ℕ
fromEnd {xs = _ ∷ xs} (here _) = length xs
fromEnd (there i)              = fromEnd i

fromEnd< : ∀ {X : Set} {x : X} {xs : List X} (i : x ∈ xs) → fromEnd i < length xs
fromEnd< (here _)  = ≤-refl
fromEnd< (there i) = m<n⇒m<1+n (fromEnd< i)

fromEnd-wk : ∀ {X : Set} {x : X} {xs ys : List X} (q : xs ⊑ ys) (i : x ∈ xs) →
             fromEnd (∈-wk q i) ≡ fromEnd i
fromEnd-wk (Suffix.here eqs) i with Pointwise-≡⇒≡ eqs
... | refl = refl
fromEnd-wk (Suffix.there q) i = fromEnd-wk q i

-- Two positions in one list with the same key are the same position.
fromEnd-inj : ∀ {X : Set} {x y : X} {xs : List X} (i : x ∈ xs) (j : y ∈ xs) →
              fromEnd i ≡ fromEnd j → Σ (x ≡ y) λ { refl → i ≡ j }
fromEnd-inj (here refl) (here refl) _ = refl , refl
fromEnd-inj (here refl) (there j) e = ⊥-elim (<-irrefl (sym e) (fromEnd< j))
fromEnd-inj (there i) (here refl) e = ⊥-elim (<-irrefl e (fromEnd< i))
fromEnd-inj (there i) (there j) e with fromEnd-inj i j e
... | refl , refl = refl , refl

-- Locations in a stratified world
data Loc : ∀ {k} → World k → (j : ℕ) → STy j → Set where
  top   : ∀ {k} {W : World k} {L} {A : STy k} → A ∈ L → Loc {suc k} (W , L) k A
  below : ∀ {k} {W : World k} {L} {j} {A : STy j} → Loc W j A → Loc {suc k} (W , L) j A

Key : Set
Key = ℕ × ℕ

key : ∀ {k} {W : World k} {j A} → Loc W j A → Key
key (top {k} x) = k , fromEnd x
key (below l)   = key l

key-layer : ∀ {k} {W : World k} {j A} (l : Loc W j A) → proj₁ (key l) ≡ j
key-layer (top x)   = refl
key-layer (below l) = key-layer l

loc< : ∀ {k} {W : World k} {j A} → Loc W j A → j < k
loc< (top x)   = ≤-refl
loc< (below l) = m<n⇒m<1+n (loc< l)

mono-Loc : ∀ {k} {W W' : World k} {j A} → W ≤W W' → Loc W j A → Loc W' j A
mono-Loc {W = W , L} {W' , L'} (q , qL) (top x)   = top (∈-wk qL x)
mono-Loc {W = W , L} {W' , L'} (q , qL) (below l) = below (mono-Loc q l)

key-mono : ∀ {k} {W W' : World k} {j A} (q : W ≤W W') (l : Loc W j A) →
           key (mono-Loc q l) ≡ key l
key-mono {W = W , L} {W' , L'} (q , qL) (top {k} x) = cong (k ,_) (fromEnd-wk qL x)
key-mono {W = W , L} {W' , L'} (q , qL) (below l)   = key-mono q l

noLoc : ∀ {k j A} → Loc (emptyW k) j A → ⊥
noLoc {suc k} (top ())
noLoc {suc k} (below l) = noLoc l

------------------------------------------------------------------------
-- Maps from semantic cells to runtime addresses
------------------------------------------------------------------------

Map : Set
Map = Key → ℕ

-- φ' agrees with φ on the cells of W
record Ext {k} (W : World k) (φ φ' : Map) : Set where
  constructor mkExt
  field at : ∀ {j A} (l : Loc W j A) → φ' (key l) ≡ φ (key l)
open Ext

Inj : ∀ {k} → World k → Map → Set
Inj W φ = ∀ {j A j' A'} (l : Loc W j A) (l' : Loc W j' A') →
          φ (key l) ≡ φ (key l') → key l ≡ key l'

Bound : ∀ {k} → World k → Map → RHeap → Set
Bound W φ rh = ∀ {j A} (l : Loc W j A) → φ (key l) < length rh

-- a is not the address of any cell of W
Out : ∀ {k} → World k → Map → ℕ → Set
Out W φ a = ∀ {j A} (l : Loc W j A) → φ (key l) ≢ a

-- Runtime cells outside the map are untouched
Frame : ∀ {k} → World k → Map → RHeap → RHeap → Set
Frame W φ rh rh' =
  length rh ≤ length rh' × (∀ a → a < length rh → Out W φ a → rh' ! a ≡ rh ! a)

-- New cells never take an old address outside the map
NoSteal : ∀ {k} → World k → World k → Map → Map → RHeap → Set
NoSteal W W' φ φ' rh = ∀ a → a < length rh → Out W φ a → Out W' φ' a

Ext-refl : ∀ {k} {W : World k} {φ} → Ext W φ φ
Ext-refl = mkExt λ l → refl

Ext-trans : ∀ {k} {W W₁ : World k} {φ φ₁ φ₂} → W ≤W W₁ →
            Ext W φ φ₁ → Ext W₁ φ₁ φ₂ → Ext W φ φ₂
Ext-trans {φ = φ} {φ₁} {φ₂} q e₁ e₂ = mkExt λ l →
  trans (cong φ₂ (sym (key-mono q l)))
        (trans (at e₂ (mono-Loc q l)) (trans (cong φ₁ (key-mono q l)) (at e₁ l)))

Ext-below : ∀ {k} {W : World k} {L φ φ'} → Ext (W , L) φ φ' → Ext W φ φ'
Ext-below e = mkExt λ l → at e (below l)

------------------------------------------------------------------------
-- Addresses in runtime values
------------------------------------------------------------------------

-- An address occurs in a runtime value: directly, or in a closure's
-- environment.
mutual
  data Occ : RVal → ℕ → Set where
    o-loc : ∀ {a} → Occ (loc a) a
    o-clo : ∀ {Δ i j} {A : Ty i} {B : Ty j} {body : (i , A) ∷ Δ ⊢ B}
              {ρ : REnv Δ} {a} → OccEnv ρ a → Occ (clo body ρ) a

  data OccEnv : ∀ {Δ} → REnv Δ → ℕ → Set where
    o-hd : ∀ {x Δ v} {ρ : REnv Δ} {a} → Occ v a → OccEnv {x ∷ Δ} (v ∷ ρ) a
    o-tl : ∀ {x Δ v} {ρ : REnv Δ} {a} → OccEnv ρ a → OccEnv {x ∷ Δ} (v ∷ ρ) a

-- An address is reachable from a value through the runtime heap.
data Reach (rh : RHeap) : RVal → ℕ → Set where
  r-occ  : ∀ {rv a} → Occ rv a → Reach rh rv a
  r-step : ∀ {rv b v a} → Occ rv b → rh ! b ≡ just v → Reach rh v a → Reach rh rv a

-- An address is the address of a cell of W.
InImg : ∀ {k} → World k → Map → ℕ → Set
InImg W φ a = Σ[ j ∈ ℕ ] Σ[ A ∈ STy j ] Σ[ l ∈ Loc W j A ] φ (key l) ≡ a

InImg-mono : ∀ {k} {W W' : World k} {φ φ' a} (q : W ≤W W') →
             Ext W φ φ' → InImg W φ a → InImg W' φ' a
InImg-mono {φ' = φ'} q e (j , A , l , eq) =
  j , A , mono-Loc q l , trans (cong φ' (key-mono q l)) (trans (at e l) eq)

InImg-resp : ∀ {k} {W : World k} {φ φ₂ a} → Ext W φ φ₂ → InImg W φ a → InImg W φ₂ a
InImg-resp e (j , A , l , eq) = j , A , l , trans (at e l) eq

InImg-below : ∀ {k} {W : World k} {L φ a} → InImg W φ a → InImg (W , L) φ a
InImg-below (j , A , l , eq) = j , A , below l , eq

InImg-lower : ∀ {m k} (q : m ≤′ k) {W : World k} {φ a} →
              InImg (lowerW q W) φ a → InImg W φ a
InImg-lower ≤′-refl     i = i
InImg-lower (≤′-step q) {W , L} {φ} i = InImg-below {L = L} {φ = φ} (InImg-lower q {φ = φ} i)

------------------------------------------------------------------------
-- The simulation relation
------------------------------------------------------------------------

mutual
  -- Semantic and runtime values.  A related closure's environment holds
  -- only addresses of cells of W: what a function captures is in its world.
  V-rel : (k : ℕ) (X : STy k) (W : World k) → Map → Val k X W → RVal → Set
  V-rel _       nat       _       φ n  rv = rv ≡ num n
  V-rel _       unit      _       φ _  rv = rv ≡ unit
  V-rel (suc k) (↑ X)     (W , L) φ v  rv = V-rel k X W φ v rv
  V-rel (suc k) (ref X)   (W , L) φ x  rv = rv ≡ loc (φ (k , fromEnd x))
  V-rel k       (arr X Y) W       φ f  (clo body ρ) =
    (∀ a → OccEnv ρ a → InImg W φ a) ×
    (∀ (W' : World k) (q : W ≤W W') (φ' : Map) → Ext W φ φ' →
     ∀ a ra → V-rel k X W' φ' a ra →
     SimC k Y W' φ' (f W' q a) (λ rh rh' rv → Eval rh (ra ∷ ρ) body rh' rv))
  V-rel k       (arr X Y) W       φ f  _ = ⊥

  -- Every semantic cell has a runtime cell holding a related value
  HRel : (k : ℕ) (W : World k) → Map → Heap k W → RHeap → Set
  HRel zero    _       φ _        rh = ⊤
  HRel (suc k) (W , L) φ (h , cs) rh =
    HRel k W φ h rh ×
    (∀ {X} (x : X ∈ L) → Σ[ rv ∈ RVal ]
       rh ! φ (k , fromEnd x) ≡ just rv × V-rel k X W φ (All.lookup cs x) rv)

  Inv : (k : ℕ) (W : World k) → Map → Heap k W → RHeap → Set
  Inv k W φ h rh = HRel k W φ h rh × Inj W φ × Bound W φ rh

  Post : (k : ℕ) (X : STy k) (W : World k) → Map →
         (RHeap → RHeap → RVal → Set) → RHeap →
         Σ[ W' ∈ World k ] W ≤W W' × Heap k W' × Val k X W' → Set
  Post k X W φ P rh (W' , q , h' , v) =
    Σ[ φ' ∈ Map ] Σ[ rh' ∈ RHeap ] Σ[ rv ∈ RVal ]
      P rh rh' rv × Ext W φ φ' × Inv k W' φ' h' rh' × V-rel k X W' φ' v rv ×
      Frame W φ rh rh' × NoSteal W W' φ φ' rh

  -- A semantic computation is simulated by runs satisfying P
  SimC : (k : ℕ) (X : STy k) (W : World k) → Map → Comp k X W →
         (RHeap → RHeap → RVal → Set) → Set
  SimC k X W φ c P = ∀ h rh → Inv k W φ h rh → Post k X W φ P rh (c h)

------------------------------------------------------------------------
-- Properties of the relation
------------------------------------------------------------------------

-- Only the addresses of W's cells matter.
V-rel-resp : ∀ {k} (X : STy k) {W : World k} {φ φ₂ v rv} →
             Ext W φ φ₂ → V-rel k X W φ v rv → V-rel k X W φ₂ v rv
V-rel-resp nat       e r = r
V-rel-resp unit      e r = r
V-rel-resp (↑ X)     {W , L} e r = V-rel-resp X (Ext-below e) r
V-rel-resp (ref X)   {W , L} {v = x} e r = trans r (cong loc (sym (at e (top x))))
V-rel-resp (arr X Y) {rv = clo body ρ} e (img , r) =
  (λ a o → InImg-resp e (img a o)) ,
  λ W' q φ' e' a ra ar → r W' q φ' (mkExt λ l → trans (at e' l) (at e l)) a ra ar
V-rel-resp (arr X Y) {rv = num _}  e ()
V-rel-resp (arr X Y) {rv = unit}   e ()
V-rel-resp (arr X Y) {rv = loc _}  e ()

V-rel-mono : ∀ {k} (X : STy k) {W W' : World k} {φ φ' v rv} (q : W ≤W W') →
             Ext W φ φ' → V-rel k X W φ v rv → V-rel k X W' φ' (mono-Val X q v) rv
V-rel-mono nat       q e r = r
V-rel-mono unit      q e r = r
V-rel-mono (↑ X)     {W , L} {W' , L'} (q , _) e r = V-rel-mono X q (Ext-below e) r
V-rel-mono (ref X)   {W , L} {W' , L'} {φ} {φ'} {x} (q , qL) e r =
  trans r (cong loc (trans (sym (at e (top x)))
                           (cong (λ n → φ' (_ , n)) (sym (fromEnd-wk qL x)))))
V-rel-mono (arr X Y) {rv = clo body ρ} q e (img , r) =
  (λ a o → InImg-mono q e (img a o)) ,
  λ W'' q' φ'' e' a ra ar → r W'' (≤W-trans q q') φ'' (Ext-trans q e e') a ra ar
V-rel-mono (arr X Y) {rv = num _}  q e ()
V-rel-mono (arr X Y) {rv = unit}   q e ()
V-rel-mono (arr X Y) {rv = loc _}  q e ()

V-rel-cast : ∀ {k} {X Y : STy k} {W φ v rv} (eq : X ≡ Y) →
             V-rel k X W φ v rv → V-rel k Y W φ (castV eq v) rv
V-rel-cast refl r = r

V-rel-down : ∀ {m k} (q : m ≤′ k) {X : STy m} {W φ v rv} →
             V-rel k (↑≤ q X) W φ v rv → V-rel m X (lowerW q W) φ (down q v) rv
V-rel-down ≤′-refl     r = r
V-rel-down (≤′-step q) {W = W , L} r = V-rel-down q r

V-rel-up : ∀ {m k} (q : m ≤′ k) {X : STy m} {W φ v rv} →
           V-rel m X (lowerW q W) φ v rv → V-rel k (↑≤ q X) W φ (up q v) rv
V-rel-up ≤′-refl     r = r
V-rel-up (≤′-step q) {W = W , L} r = V-rel-up q r

V-rel-downCell : ∀ {i N} (s : suc i ≤′ N) {X : STy i} {W φ v rv} →
                 V-rel N (↑≤ (predS s) X) W φ v rv →
                 V-rel i X (proj₁ (lowerW s W)) φ (downCell s v) rv
V-rel-downCell ≤′-refl     {W = W , L} r = r
V-rel-downCell (≤′-step s) {W = W , L} r = V-rel-downCell s r

V-rel-upCell : ∀ {i N} (s : suc i ≤′ N) {X : STy i} {W φ v rv} →
               V-rel i X (proj₁ (lowerW s W)) φ v rv →
               V-rel N (↑≤ (predS s) X) W φ (upCell s v) rv
V-rel-upCell ≤′-refl     {W = W , L} r = r
V-rel-upCell (≤′-step s) {W = W , L} r = V-rel-upCell s r

V-rel-upE : ∀ {k N} (s : k ≤′ N) {X : STy k} {W φ v rv} →
            V-rel k X W φ v rv → V-rel N (↑≤ s X) (extendE s W) φ (upE s v) rv
V-rel-upE ≤′-refl     r = r
V-rel-upE (≤′-step s) r = V-rel-upE s r

-- Every address in a related runtime value is the address of a cell.
Occ-img : ∀ {k} (X : STy k) {W : World k} {φ v rv a} →
          V-rel k X W φ v rv → Occ rv a → InImg W φ a
Occ-img nat  refl ()
Occ-img unit refl ()
Occ-img (↑ X)   {W , L} {φ} r o = InImg-below {L = L} {φ = φ} (Occ-img X r o)
Occ-img (ref X) {W , L} {φ} {x} refl o-loc = _ , X , top x , refl
Occ-img (arr X Y) {rv = clo body ρ} (img , _) (o-clo oe) = img _ oe
Occ-img (arr X Y) {rv = num _} () o
Occ-img (arr X Y) {rv = unit}  () o
Occ-img (arr X Y) {rv = loc _} () o

lookup-map : ∀ {X : Set} {P Q : X → Set} (f : ∀ {x} → P x → Q x) {xs : List X}
             (cs : All P xs) {x} (i : x ∈ xs) →
             All.lookup (All.map f cs) i ≡ f (All.lookup cs i)
lookup-map f (c ∷ cs) (here refl) = refl
lookup-map f (c ∷ cs) (there i)   = lookup-map f cs i

-- Transport a heap relation to a map agreeing on W and a runtime heap
-- agreeing at W's addresses.
HRel-transport : ∀ {k} {W : World k} {φ φ₂ h rh rh₂} →
                 Ext W φ φ₂ → (∀ {j A} (l : Loc W j A) → rh₂ ! φ (key l) ≡ rh ! φ (key l)) →
                 HRel k W φ h rh → HRel k W φ₂ h rh₂
HRel-transport {zero} e g r = tt
HRel-transport {suc k} {W , L} {φ} {φ₂} {h , cs} {rh} {rh₂} e g (r , tops) =
  HRel-transport (Ext-below e) (λ l → g (below l)) r ,
  λ {Y} x → let (rv , look , vr) = tops x in
        rv ,
        trans (cong (rh₂ !_) (at e (top x))) (trans (g (top x)) look) ,
        V-rel-resp Y (Ext-below e) vr

------------------------------------------------------------------------
-- The monad and the heap operations are simulated
------------------------------------------------------------------------

SimC-map : ∀ {k X W φ} {c : Comp k X W} {P Q : RHeap → RHeap → RVal → Set} →
           (∀ {rh rh' rv} → P rh rh' rv → Q rh rh' rv) → SimC k X W φ c P → SimC k X W φ c Q
SimC-map f sim h rh inv with sim h rh inv
... | φ' , rh' , rv , p , rest = φ' , rh' , rv , f p , rest

SimC-cast : ∀ {k} {X Y : STy k} {W φ P} {c : Comp k X W} (eq : X ≡ Y) →
            SimC k X W φ c P → SimC k Y W φ (castC eq c) P
SimC-cast refl sim = sim

SimC-ret : ∀ {k X W φ v rv} {P : RHeap → RHeap → RVal → Set} →
           V-rel k X W φ v rv → (∀ {rh} → P rh rh rv) →
           SimC k X W φ (ret {A = X} v) P
SimC-ret {φ = φ} {rv = rv} vr p h rh inv =
  φ , rh , rv , p , Ext-refl , inv , vr , (≤-refl , λ a _ _ → refl) , (λ a _ out → out)

Frame-trans : ∀ {k} {W W₁ : World k} {φ φ₁ rh rh₁ rh₂} →
              Frame W φ rh rh₁ → NoSteal W W₁ φ φ₁ rh → Frame W₁ φ₁ rh₁ rh₂ →
              Frame W φ rh rh₂
Frame-trans (len₁ , f₁) ns (len₂ , f₂) =
  ≤-trans len₁ len₂ ,
  λ a a< out → trans (f₂ a (<-≤-trans a< len₁) (ns a a< out)) (f₁ a a< out)

NoSteal-trans : ∀ {k} {W W₁ W₂ : World k} {φ φ₁ φ₂ rh rh₁} →
                Frame W φ rh rh₁ → NoSteal W W₁ φ φ₁ rh → NoSteal W₁ W₂ φ₁ φ₂ rh₁ →
                NoSteal W W₂ φ φ₂ rh
NoSteal-trans (len₁ , _) ns₁ ns₂ a a< out =
  ns₂ a (<-≤-trans a< len₁) (ns₁ a a< out)

SimC-bind : ∀ {k} {X Y : STy k} {W φ} {c : Comp k X W}
              {f : ∀ {W'} → W ≤W W' → Val k X W' → Comp k Y W'}
              {P₁ : RHeap → RHeap → RVal → Set}
              {P₂ : RVal → RHeap → RHeap → RVal → Set} →
            SimC k X W φ c P₁ →
            (∀ {W₁} (q₁ : W ≤W W₁) φ₁ a ra → Ext W φ φ₁ → V-rel k X W₁ φ₁ a ra →
               SimC k Y W₁ φ₁ (f q₁ a) (P₂ ra)) →
            SimC k Y W φ (bind {A = X} {B = Y} c f)
              (λ rh rh₂ rv → Σ[ rh₁ ∈ RHeap ] Σ[ ra ∈ RVal ] P₁ rh rh₁ ra × P₂ ra rh₁ rh₂ rv)
SimC-bind {W = W} {φ} {c} {f} sim₁ sim₂ h rh inv with c h | sim₁ h rh inv
... | W₁ , q₁ , h₁ , a | φ₁ , rh₁ , ra , p₁ , e₁ , inv₁ , ar , fr₁ , ns₁
  with f q₁ a h₁ | sim₂ q₁ φ₁ a ra e₁ ar h₁ rh₁ inv₁
...   | W₂ , q₂ , h₂ , b | φ₂ , rh₂ , rb , p₂ , e₂ , inv₂ , br , fr₂ , ns₂ =
  φ₂ , rh₂ , rb , (rh₁ , ra , p₁ , p₂) , Ext-trans q₁ e₁ e₂ , inv₂ , br ,
  Frame-trans {W = W} {W₁} {φ} {φ₁} {rh} {rh₁} {rh₂} fr₁ ns₁ fr₂ ,
  NoSteal-trans {W = W} {W₁} {W₂} {φ} {φ₁} {φ₂} {rh} {rh₁} fr₁ ns₁ ns₂

-- Running on the lower layers ----------------------------------------------

-- Combine the map of a lower computation with the old map on layer k.
comb : ℕ → Map → Map → Map
comb k φ φ' (j , n) with j ≟ℕ k
... | yes _ = φ (j , n)
... | no  _ = φ' (j , n)

comb-top : ∀ k φ φ' n → comb k φ φ' (k , n) ≡ φ (k , n)
comb-top k φ φ' n with k ≟ℕ k
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

comb-low : ∀ {k} {W : World k} {j A} φ φ' (l : Loc W j A) →
           comb k φ φ' (key l) ≡ φ' (key l)
comb-low {k} φ φ' l with proj₁ (key l) ≟ℕ k | key-layer l
... | yes e | kl = ⊥-elim (<-irrefl (trans (sym kl) e) (loc< l))
... | no  _ | _  = refl

-- A top cell's address is outside the lower cells' addresses.
top-out : ∀ {k} {W : World k} {L} {φ} {X} (x : X ∈ L) →
          Inj (W , L) φ → Out W φ (φ (k , fromEnd x))
top-out {k} x inj l e with inj (below l) (top x) e
... | kl = <-irrefl (trans (sym (key-layer l)) (cong proj₁ kl)) (loc< l)

SimC-embed1 : ∀ {k} {X : STy k} {W L φ P} {c : Comp k X W} →
              SimC k X W φ c P → SimC (suc k) (↑ X) (W , L) φ (embed1 {A = X} {L = L} c) P
SimC-embed1 {k} {X} {W} {L} {φ} {P} {c} sim (h , cs) rh ((hr , tops) , inj , bnd)
  with c h | sim h rh (hr , (λ l l' → inj (below l) (below l')) , (λ l → bnd (below l)))
... | W' , q , h' , v | φ' , rh' , rv , p , e , (hr' , inj' , bnd') , vr , (len , fr) , ns =
  φ'' , rh' , rv , p , ext , (hrel , inj'' , bnd'') , V-rel-resp X e-low vr ,
  (len , λ a a< out → fr a a< (λ l → out (below l))) , nosteal
  where
  φ'' = comb k φ φ'
  e-low : Ext W' φ' φ''
  e-low = mkExt λ l → comb-low φ φ' l
  ext : Ext (W , L) φ φ''
  ext = mkExt λ { (top x) → comb-top k φ φ' _
             ; (below l) → trans (comb-low φ φ' l) (at e l) }
  top-same : ∀ {Y} (x : Y ∈ L) → rh' ! φ (k , fromEnd x) ≡ rh ! φ (k , fromEnd x)
  top-same x = fr _ (bnd (top x)) (top-out {φ = φ} x inj)
  hrel : HRel (suc k) (W' , L) φ'' (h' , mono-Cells q cs) rh'
  hrel = HRel-transport e-low (λ l → refl) hr' ,
         λ {Y} x → let (rv₀ , look , vr₀) = tops x in
               rv₀ ,
               trans (cong (rh' !_) (comb-top k φ φ' _)) (trans (top-same x) look) ,
               subst (λ z → V-rel k Y W' φ'' z rv₀) (sym (lookup-map (λ {A} → mono-Val A q) cs x))
                 (V-rel-resp Y e-low (V-rel-mono Y q e vr₀))
  inj'' : Inj (W' , L) φ''
  inj'' (top x) (top y) eq =
    inj (top x) (top y) (trans (sym (comb-top k φ φ' _)) (trans eq (comb-top k φ φ' _)))
  inj'' (below l) (below l') eq =
    inj' l l' (trans (sym (comb-low φ φ' l)) (trans eq (comb-low φ φ' l')))
  inj'' (top x) (below l') eq =
    ⊥-elim (ns _ (bnd (top x)) (top-out {φ = φ} x inj) l'
              (sym (trans (sym (comb-top k φ φ' _)) (trans eq (comb-low φ φ' l')))))
  inj'' (below l) (top y) eq =
    ⊥-elim (ns _ (bnd (top y)) (top-out {φ = φ} y inj) l
              (trans (sym (comb-low φ φ' l)) (trans eq (comb-top k φ φ' _))))
  bnd'' : Bound (W' , L) φ'' rh'
  bnd'' (top x)   = subst (_< length rh') (sym (comb-top k φ φ' _))
                      (<-≤-trans (bnd (top x)) len)
  bnd'' (below l) = subst (_< length rh') (sym (comb-low φ φ' l)) (bnd' l)
  nosteal : NoSteal (W , L) (W' , L) φ φ'' rh
  nosteal a a< out (top x)   = subst (_≢ a) (sym (comb-top k φ φ' _)) (out (top x))
  nosteal a a< out (below l) =
    subst (_≢ a) (sym (comb-low φ φ' l)) (ns a a< (λ l₀ → out (below l₀)) l)

SimC-embedC : ∀ {m k} (q : m ≤′ k) {X : STy m} {W φ P} {c : Comp m X (lowerW q W)} →
              SimC m X (lowerW q W) φ c P → SimC k (↑≤ q X) W φ (embedC q {A = X} c) P
SimC-embedC ≤′-refl sim = sim
SimC-embedC (≤′-step q) {X} {W , L} sim = SimC-embed1 {X = ↑≤ q X} (SimC-embedC q sim)

-- Fresh layers on top, dropped afterwards ------------------------------------

SimC-drop1 : ∀ {k} {X : STy k} {W φ P} {c : Comp (suc k) (↑ X) (W , [])} →
             SimC (suc k) (↑ X) (W , []) φ c P → SimC k X W φ (drop1 {A = X} c) P
SimC-drop1 {k} {X} {W} {φ} {P} {c} sim h rh (hr , inj , bnd)
  with c (h , []) | sim (h , []) rh ((hr , λ ()) , inj₀ , bnd₀)
  where
  inj₀ : Inj (W , []) φ
  inj₀ (below l) (below l') e = inj l l' e
  bnd₀ : Bound (W , []) φ rh
  bnd₀ (below l) = bnd l
... | (W' , L') , (q , _) , (h' , _) , v
    | φ' , rh' , rv , p , e , ((hr' , _) , inj' , bnd') , vr , (len , fr) , ns =
  φ' , rh' , rv , p , Ext-below {L = []} e ,
  (hr' , (λ l l' → inj' (below l) (below l')) , (λ l → bnd' (below l))) , vr ,
  (len , λ a a< out → fr a a< (out₀ out)) ,
  (λ a a< out l → ns a a< (out₀ out) (below l))
  where
  out₀ : ∀ {a} → Out W φ a → Out (W , []) φ a
  out₀ out (below l) = out l

SimC-localC : ∀ {m k} (q : m ≤′ k) {X : STy m} {W φ P}
                {c : Comp k (↑≤ q X) (extendE q W)} →
              SimC k (↑≤ q X) (extendE q W) φ c P → SimC m X W φ (localC q {A = X} c) P
SimC-localC ≤′-refl sim = sim
SimC-localC (≤′-step q) {X} {W} {φ} {P} {c} sim =
  SimC-localC q {c = drop1 {A = ↑≤ q X} c}
    (SimC-drop1 {X = ↑≤ q X} {W = extendE q W} {φ = φ} {P = P} {c = c} sim)

-- Allocation -----------------------------------------------------------------

-- Update a map at one key.
set : Map → Key → ℕ → Map
set φ κ a κ' with ≡-dec _≟ℕ_ _≟ℕ_ κ' κ
... | yes _ = a
... | no  _ = φ κ'

set-same : ∀ φ κ a → set φ κ a κ ≡ a
set-same φ κ a with ≡-dec _≟ℕ_ _≟ℕ_ κ κ
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

set-other : ∀ φ κ a {κ'} → κ' ≢ κ → set φ κ a κ' ≡ φ κ'
set-other φ κ a {κ'} ne with ≡-dec _≟ℕ_ _≟ℕ_ κ' κ
... | yes e = ⊥-elim (ne e)
... | no  _ = refl

SimC-alloc : ∀ {i N} (s : suc i ≤′ N) {X : STy i} {W φ v rv} →
             V-rel i X (proj₁ (lowerW s W)) φ v rv →
             SimC N (↑≤ s (ref X)) W φ (alloc s {A = X} v)
               (λ rh rh' rv' → rh' ≡ snoc rh rv × rv' ≡ loc (length rh))
SimC-alloc {i} ≤′-refl {X} {W , L} {φ} {v} {rv} vr (h , cs) rh ((hr , tops) , inj , bnd) =
  φ' , snoc rh rv , loc (length rh) , (refl , refl) , ext , (hrel , inj' , bnd') ,
  cong loc (sym (set-same φ κ₀ (length rh))) , frame , nosteal
  where
  κ₀ = (i , length L)
  φ' = set φ κ₀ (length rh)
  old : ∀ {j A} (l : Loc (W , L) j A) → key l ≢ κ₀
  old (top x)   e = <-irrefl (cong proj₂ e) (fromEnd< x)
  old (below l) e = <-irrefl (trans (sym (key-layer l)) (cong proj₁ e)) (loc< l)
  ext : Ext (W , L) φ φ'
  ext = mkExt λ l → set-other φ κ₀ (length rh) (old l)
  ext-low : Ext W φ φ'
  ext-low = mkExt λ l → at ext (below l)
  snoc-old : ∀ {j A} (l : Loc (W , L) j A) → snoc rh rv ! φ (key l) ≡ rh ! φ (key l)
  snoc-old l = !-snoc-old rh rv (bnd l)
  hrel : HRel (suc i) (W , X ∷ L) φ' (h , v ∷ cs) (snoc rh rv)
  hrel = HRel-transport ext-low (λ l → snoc-old (below l)) hr , cell
    where
    cell : ∀ {Y} (x : Y ∈ X ∷ L) → Σ[ rv' ∈ RVal ]
             snoc rh rv ! φ' (i , fromEnd x) ≡ just rv' ×
             V-rel i Y W φ' (All.lookup (v ∷ cs) x) rv'
    cell (here refl) =
      rv , trans (cong (snoc rh rv !_) (set-same φ κ₀ (length rh))) (!-snoc-new rh rv) ,
      V-rel-resp X ext-low vr
    cell {Y} (there x) = let (rv₀ , look , vr₀) = tops x in
      rv₀ , trans (cong (snoc rh rv !_) (at ext (top x))) (trans (snoc-old (top x)) look) ,
      V-rel-resp Y ext-low vr₀
  -- a cell of the new world is the new cell, or has the key of an old one
  view : ∀ {j A} (l : Loc (W , X ∷ L) j A) →
         key l ≡ κ₀ ⊎ (Σ[ j₀ ∈ ℕ ] Σ[ A₀ ∈ STy j₀ ] Σ[ l₀ ∈ Loc (W , L) j₀ A₀ ] key l ≡ key l₀)
  view (top (here refl)) = inl refl
  view (top (there x))   = inr (_ , _ , top x , refl)
  view (below l)         = inr (_ , _ , below l , refl)
  addr-old : ∀ {j A} (l₀ : Loc (W , L) j A) → φ' (key l₀) < length rh
  addr-old l₀ = subst (_< length rh) (sym (at ext l₀)) (bnd l₀)
  inj' : Inj (W , X ∷ L) φ'
  inj' l l' eq with view l | view l'
  ... | inl e | inl e' = trans e (sym e')
  ... | inl e | inr (_ , _ , l₀ , e') =
    ⊥-elim (<-irrefl (sym (trans (sym (set-same φ κ₀ (length rh)))
                            (trans (cong φ' (sym e)) (trans eq (cong φ' e')))))
                     (addr-old l₀))
  ... | inr (_ , _ , l₀ , e) | inl e' =
    ⊥-elim (<-irrefl (sym (trans (sym (set-same φ κ₀ (length rh)))
                            (trans (cong φ' (sym e')) (trans (sym eq) (cong φ' e)))))
                     (addr-old l₀))
  ... | inr (_ , _ , l₀ , e) | inr (_ , _ , l₀' , e') =
    trans e (trans (inj l₀ l₀' (trans (sym (at ext l₀))
                    (trans (cong φ' (sym e)) (trans eq (trans (cong φ' e') (at ext l₀')))))) (sym e'))
  bnd' : Bound (W , X ∷ L) φ' (snoc rh rv)
  bnd' l with view l
  ... | inl e = subst (_< length (snoc rh rv))
                  (trans (sym (set-same φ κ₀ (length rh))) (cong φ' (sym e)))
                  (subst (length rh <_) (sym (length-snoc rh rv)) ≤-refl)
  ... | inr (_ , _ , l₀ , e) =
    subst (_< length (snoc rh rv)) (cong φ' (sym e))
      (subst (φ' (key l₀) <_) (sym (length-snoc rh rv)) (m<n⇒m<1+n (addr-old l₀)))
  frame : Frame (W , L) φ rh (snoc rh rv)
  frame = subst (length rh ≤_) (sym (length-snoc rh rv)) (m≤n⇒m≤1+n ≤-refl) ,
          λ a a< _ → !-snoc-old rh rv a<
  nosteal : NoSteal (W , L) (W , X ∷ L) φ φ' rh
  nosteal a a< out l with view l
  ... | inl e = λ eq → <-irrefl (sym (trans (sym (set-same φ κ₀ (length rh)))
                                     (trans (cong φ' (sym e)) eq))) a<
  ... | inr (_ , _ , l₀ , e) =
    λ eq → out l₀ (trans (sym (at ext l₀)) (trans (cong φ' (sym e)) eq))
SimC-alloc (≤′-step s) {X} {W , L} vr = SimC-embed1 {X = ↑≤ s (ref X)} (SimC-alloc s vr)

-- A record wrapper, so that Agda can infer the computation and the
-- predicate from a simulation's type.  (SimC itself must be a function,
-- because it occurs inside the definition of V-rel.)

record ⊢Sim (k : ℕ) (X : STy k) (W : World k) (φ : Map) (c : Comp k X W)
            (P : RHeap → RHeap → RVal → Set) : Set where
  constructor sim
  field run : SimC k X W φ c P
open ⊢Sim

Sim-map : ∀ {k X W φ} {c : Comp k X W} {P Q : RHeap → RHeap → RVal → Set} →
          (∀ {rh rh' rv} → P rh rh' rv → Q rh rh' rv) → ⊢Sim k X W φ c P → ⊢Sim k X W φ c Q
Sim-map {k} {X} {W} {φ} {c} {P} {Q} f s = sim (SimC-map {k} {X} {W} {φ} {c} {P} {Q} f (run s))

Sim-cast : ∀ {k} {X Y : STy k} {W φ P} {c : Comp k X W} (eq : X ≡ Y) →
           ⊢Sim k X W φ c P → ⊢Sim k Y W φ (castC eq c) P
Sim-cast refl s = s

Sim-ret : ∀ {k X W φ v rv} {P : RHeap → RHeap → RVal → Set} →
          V-rel k X W φ v rv → (∀ {rh} → P rh rh rv) → ⊢Sim k X W φ (ret {A = X} v) P
Sim-ret {X = X} {P = P} vr p = sim (SimC-ret {X = X} {P = P} vr p)

Sim-bind : ∀ {k} {X Y : STy k} {W φ} {c : Comp k X W}
             {f : ∀ {W'} → W ≤W W' → Val k X W' → Comp k Y W'}
             {P₁ : RHeap → RHeap → RVal → Set}
             {P₂ : RVal → RHeap → RHeap → RVal → Set} →
           ⊢Sim k X W φ c P₁ →
           (∀ {W₁} (q₁ : W ≤W W₁) φ₁ a ra → Ext W φ φ₁ → V-rel k X W₁ φ₁ a ra →
              ⊢Sim k Y W₁ φ₁ (f q₁ a) (P₂ ra)) →
           ⊢Sim k Y W φ (bind {A = X} {B = Y} c f)
             (λ rh rh₂ rv → Σ[ rh₁ ∈ RHeap ] Σ[ ra ∈ RVal ] P₁ rh rh₁ ra × P₂ ra rh₁ rh₂ rv)
Sim-bind {X = X} {Y} {W} {φ} {c} {f} {P₁} {P₂} s₁ s₂ =
  sim (SimC-bind {X = X} {Y = Y} {W = W} {φ = φ} {c = c} {f = f} {P₁ = P₁} {P₂ = P₂}
        (run s₁) (λ q₁ φ₁ a ra e ar → run (s₂ q₁ φ₁ a ra e ar)))

Sim-embedC : ∀ {m k} (q : m ≤′ k) {X : STy m} {W φ P} {c : Comp m X (lowerW q W)} →
             ⊢Sim m X (lowerW q W) φ c P → ⊢Sim k (↑≤ q X) W φ (embedC q {A = X} c) P
Sim-embedC q {X} {W} {φ} {P} {c} s = sim (SimC-embedC q {X} {W} {φ} {P} {c} (run s))

Sim-localC : ∀ {m k} (q : m ≤′ k) {X : STy m} {W φ P}
               {c : Comp k (↑≤ q X) (extendE q W)} →
             ⊢Sim k (↑≤ q X) (extendE q W) φ c P → ⊢Sim m X W φ (localC q {A = X} c) P
Sim-localC q {X} {W} {φ} {P} {c} s = sim (SimC-localC q {X} {W} {φ} {P} {c} (run s))

Sim-alloc : ∀ {i N} (s : suc i ≤′ N) {X : STy i} {W φ v rv} →
            V-rel i X (proj₁ (lowerW s W)) φ v rv →
            ⊢Sim N (↑≤ s (ref X)) W φ (alloc s {A = X} v)
              (λ rh rh' rv' → rh' ≡ snoc rh rv × rv' ≡ loc (length rh))
Sim-alloc s {X} {W} {φ} {v} {rv} vr = sim (SimC-alloc s {X} {W} {φ} {v} {rv} vr)

-- Reading and writing ----------------------------------------------------------

Inv-below : ∀ {k} {W : World k} {L φ h cs rh} →
            Inv (suc k) (W , L) φ (h , cs) rh → Inv k W φ h rh
Inv-below ((hr , _) , inj , bnd) =
  hr , (λ l l' → inj (below l) (below l')) , (λ l → bnd (below l))

read-rel : ∀ {i N} (s : suc i ≤′ N) {X : STy i} {W φ h rh x rx} →
           Inv N W φ h rh → V-rel N (↑≤ s (ref X)) W φ x rx →
           Σ[ ℓ ∈ ℕ ] Σ[ rv ∈ RVal ] rx ≡ loc ℓ × rh ! ℓ ≡ just rv ×
             V-rel i X (proj₁ (lowerW s W)) φ (read s x h) rv
read-rel ≤′-refl {X} {W , L} {φ} {h , cs} {rh} {x} ((hr , tops) , inj , bnd) r =
  let (rv , look , vr) = tops x in _ , rv , r , look , vr
read-rel (≤′-step s) {X} {W , L} {φ} {h , cs} {rh} {x} {rx} inv r =
  read-rel s {X} {W} {φ} {h} {rh} {x} {rx} (Inv-below {L = L} {cs = cs} inv) r

lookup-upd-same : ∀ {X : Set} {P : X → Set} {xs : List X} (cs : All P xs) {x}
                  (i : x ∈ xs) (f : P x → P x) →
                  All.lookup (All.updateAt i f cs) i ≡ f (All.lookup cs i)
lookup-upd-same (c ∷ cs) (here refl) f = refl
lookup-upd-same (c ∷ cs) (there i)   f = lookup-upd-same cs i f

lookup-upd-other : ∀ {X : Set} {P : X → Set} {xs : List X} (cs : All P xs) {x y}
                   (i : x ∈ xs) (j : y ∈ xs) (f : P x → P x) → fromEnd j ≢ fromEnd i →
                   All.lookup (All.updateAt i f cs) j ≡ All.lookup cs j
lookup-upd-other (c ∷ cs) (here refl) (here refl) f ne = ⊥-elim (ne refl)
lookup-upd-other (c ∷ cs) (here refl) (there j)   f ne = refl
lookup-upd-other (c ∷ cs) (there i)   (here refl) f ne = refl
lookup-upd-other (c ∷ cs) (there i)   (there j)   f ne = lookup-upd-other cs i j f ne

-- A top cell's address differs from every lower cell's address.
top≢below : ∀ {k} {W : World k} {L φ X j A} → Inj (W , L) φ →
            (x : X ∈ L) (l : Loc W j A) → φ (k , fromEnd x) ≢ φ (key l)
top≢below inj x l e =
  <-irrefl (trans (sym (key-layer l)) (sym (cong proj₁ (inj (top x) (below l) e)))) (loc< l)

write-rel : ∀ {i N} (s : suc i ≤′ N) {X : STy i} {W φ h rh x rx v rv} →
            Inv N W φ h rh → V-rel N (↑≤ s (ref X)) W φ x rx →
            V-rel i X (proj₁ (lowerW s W)) φ v rv →
            Σ[ ℓ ∈ ℕ ] rx ≡ loc ℓ × ℓ < length rh × (∀ a → Out W φ a → ℓ ≢ a) ×
              Inv N W φ (write s x v h) (upd rh ℓ rv)
write-rel {i} ≤′-refl {X} {W , L} {φ} {h , cs} {rh} {x} {rx} {v} {rv}
          ((hr , tops) , inj , bnd) r vr =
  ℓ , r , bnd (top x) , (λ a out e → out (top x) e) ,
  (HRel-transport {W = W} {φ = φ} {φ₂ = φ} {h = h} {rh = rh} {rh₂ = upd rh ℓ rv} Ext-refl
     (λ l → !-upd-other rh rv (top≢below {φ = φ} inj x l)) hr , tops') ,
  inj , (λ l → subst (φ (key l) <_) (sym (length-upd rh ℓ rv)) (bnd l))
  where
  ℓ = φ (i , fromEnd x)
  tops' : ∀ {Y} (y : Y ∈ L) → Σ[ rv' ∈ RVal ]
            upd rh ℓ rv ! φ (i , fromEnd y) ≡ just rv' ×
            V-rel i Y W φ (All.lookup (All.updateAt x (λ _ → v) cs) y) rv'
  tops' {Y} y with fromEnd y ≟ℕ fromEnd x
  ... | yes e with fromEnd-inj y x e
  ...   | refl , refl =
    rv , !-upd-same rh rv (bnd (top x)) ,
    subst (λ z → V-rel i X W φ z rv) (sym (lookup-upd-same cs x (λ _ → v))) vr
  tops' {Y} y | no ne =
    let (rv₀ , look , vr₀) = tops y in
    rv₀ ,
    trans (!-upd-other rh rv (λ e → ne (sym (cong proj₂ (inj (top x) (top y) e))))) look ,
    subst (λ z → V-rel i Y W φ z rv₀) (sym (lookup-upd-other cs x y (λ _ → v) ne)) vr₀
write-rel (≤′-step s) {X} {W , L} {φ} {h , cs} {rh} {x} {rx} {v} {rv}
          inv@((hr , tops) , inj , bnd) r vr
  with write-rel s {X} {W} {φ} {h} {rh} {x} {rx} {v} {rv} (Inv-below {L = L} {cs = cs} inv) r vr
... | ℓ , eq , ℓ< , img , (hr' , _ , _) =
  ℓ , eq , ℓ< , (λ a out → img a (λ l → out (below l))) ,
  (hr' , tops') , inj , (λ l → subst (φ (key l) <_) (sym (length-upd rh ℓ rv)) (bnd l))
  where
  tops' : ∀ {Y} (y : Y ∈ L) → Σ[ rv' ∈ RVal ]
            upd rh ℓ rv ! φ (_ , fromEnd y) ≡ just rv' × V-rel _ Y W φ (All.lookup cs y) rv'
  tops' y = let (rv₀ , look , vr₀) = tops y in
    rv₀ , trans (!-upd-other rh rv (img _ (top-out {φ = φ} y inj))) look , vr₀

------------------------------------------------------------------------
-- Environments
------------------------------------------------------------------------

EnvRel : ∀ {N Γ} (W : World N) → Map → Env N Γ W → REnv Γ → Set
EnvRel W φ [] [] = ⊤
EnvRel {N} {(i , A) ∷ Γ} W φ ((q , v) ∷ ρ) (rv ∷ ρR) =
  V-rel N (↑≤ q ⌜ A ⌝) W φ v rv × EnvRel W φ ρ ρR

EnvRel-lookup : ∀ {N Γ i} {A : Ty i} {W φ} {ρ : Env N Γ W} {ρR : REnv Γ}
                (x : (i , A) ∈ Γ) → EnvRel W φ ρ ρR →
                V-rel N (↑≤ (proj₁ (All.lookup ρ x)) ⌜ A ⌝) W φ
                  (proj₂ (All.lookup ρ x)) (All.lookup ρR x)
EnvRel-lookup {ρ = _ ∷ _} {_ ∷ _} (here refl) (r , _)  = r
EnvRel-lookup {ρ = _ ∷ _} {_ ∷ _} (there x)   (_ , er) = EnvRel-lookup x er

EnvRel-mono : ∀ {N Γ} {W W' : World N} {φ φ'} {ρ : Env N Γ W} {ρR : REnv Γ}
              (q : W ≤W W') → Ext W φ φ' → EnvRel W φ ρ ρR →
              EnvRel W' φ' (mono-Env q ρ) ρR
EnvRel-mono {ρ = []} {[]} q e er = tt
EnvRel-mono {Γ = (i , A) ∷ Γ} {ρ = (s , v) ∷ ρ} {_ ∷ _} q e (r , er) =
  V-rel-mono (↑≤ s ⌜ A ⌝) q e r , EnvRel-mono q e er

EnvRel-proj : ∀ {N Γ Δ} {W : World N} {φ} {ρ : Env N Γ W} {ρR : REnv Γ}
              (θ : Δ ⊆ Γ) → EnvRel W φ ρ ρR → EnvRel W φ (proj θ ρ) (proj θ ρR)
EnvRel-proj {ρ = []} {[]} [] er = tt
EnvRel-proj {ρ = _ ∷ _} {_ ∷ _} (y ∷ʳ θ)   (_ , er) = EnvRel-proj θ er
EnvRel-proj {ρ = _ ∷ _} {_ ∷ _} (refl ∷ θ) (r , er) = r , EnvRel-proj θ er

EnvRel-shift : ∀ {N Γ k} {W : World N} {Wk : World k} {φ φk}
                 {ρ : Env N Γ W} {ρR : REnv Γ}
               (cs : Below Γ k) (s : k ≤′ N) (r : lowerW s W ≤W Wk) →
               Ext (lowerW s W) φ φk → EnvRel W φ ρ ρR →
               EnvRel (extendE s Wk) φk (shiftEnv cs s r ρ) ρR
EnvRel-shift {ρ = []} {[]} [] s r e er = tt
EnvRel-shift {Γ = (i , A) ∷ Γ} {ρ = (q , v) ∷ ρ} {_ ∷ _} (c ∷ cs) s r e (vr , er) =
  V-rel-cast (lift-trans c s)
    (V-rel-upE s
      (V-rel-mono (↑≤ c ⌜ A ⌝) r e
        (V-rel-down s
          (V-rel-cast (trans (lift-irr q (≤′-trans c s)) (sym (lift-trans c s))) vr)))) ,
  EnvRel-shift cs s r e er

-- The addresses in an environment whose variables are at levels ≤ k are
-- cells of the lowest k layers.
EnvOcc : ∀ {N Γ k} {W : World N} {φ} {ρ : Env N Γ W} {ρR : REnv Γ}
         (cs : Below Γ k) (s : k ≤′ N) → EnvRel W φ ρ ρR →
         ∀ {a} → OccEnv ρR a → InImg (lowerW s W) φ a
EnvOcc {Γ = (i , A) ∷ Γ} {ρ = (q , v) ∷ ρ} {_ ∷ _} (c ∷ cs) s (vr , er) (o-hd o) =
  Occ-img (↑≤ c ⌜ A ⌝)
    (V-rel-down s (V-rel-cast (trans (lift-irr q (≤′-trans c s)) (sym (lift-trans c s))) vr)) o
EnvOcc {ρ = _ ∷ _} {_ ∷ _} (c ∷ cs) s (_ , er) (o-tl oe) = EnvOcc cs s er oe

------------------------------------------------------------------------
-- The fundamental theorem
------------------------------------------------------------------------

-- What a run of a function body must satisfy, given the runtime closure.
BodyP : RVal → RVal → RHeap → RHeap → RVal → Set
BodyP (clo body ρ) ra rh rh' rv = Eval rh (ra ∷ ρ) body rh' rv
BodyP _            _  _  _   _  = ⊥

applyRel : ∀ {k} {X Y : STy k} {W φ} (g : Val k (arr X Y) W) (rf : RVal) a ra →
           V-rel k (arr X Y) W φ g rf → V-rel k X W φ a ra →
           ⊢Sim k Y W φ (g W ≤W-refl a) (BodyP rf ra)
applyRel {W = W} {φ} g (clo body ρ) a ra (_ , vg) va = sim (vg W ≤W-refl φ Ext-refl a ra va)
applyRel g (num _) a ra () va
applyRel g unit    a ra () va
applyRel g (loc _) a ra () va

fundamental :
  ∀ {Γ i} {A : Ty i} (d : Γ ⊢ A) {N} (b : lvl d ≤ N) {W : World N} (φ : Map)
    (ρ : Env N Γ W) (ρR : REnv Γ) → EnvRel W φ ρ ρR →
  ⊢Sim N (↑≤ (fit d b) ⌜ A ⌝) W φ (⟦ d ⟧ b ρ) (λ rh rh' rv → Eval rh ρR d rh' rv)

fundamental (var {A = A} x) b φ ρ ρR er with All.lookup ρ x | EnvRel-lookup x er
... | q , v | vr =
  Sim-ret {X = ↑≤ (fit (var x) b) ⌜ A ⌝} (V-rel-cast (lift-irr q (fit (var x) b)) vr) e-var

fundamental {Γ} (num n) b φ ρ ρR er =
  Sim-ret {X = ↑≤ (fit (num {Γ} n) b) nat} (V-rel-up (fit (num {Γ} n) b) {X = nat} refl) e-num

fundamental {Γ} ⟨⟩ b φ ρ ρR er =
  Sim-ret {X = ↑≤ (fit (⟨⟩ {Γ}) b) unit} (V-rel-up (fit (⟨⟩ {Γ}) b) {X = unit} refl) e-unit

fundamental (lam {A = A} {B} θ p q c d) {N} b {W} φ ρ ρR er =
  Sim-ret {X = ↑≤ s (arr (↑≤ p ⌜ A ⌝) (↑≤ q ⌜ B ⌝))} {rv = clo d (proj θ ρR)}
    (V-rel-up s {X = arr (↑≤ p ⌜ A ⌝) (↑≤ q ⌜ B ⌝)}
      ((λ a oe → EnvOcc c s (EnvRel-proj θ er) oe) ,
       λ Wk r φk e a ra ar → run (
        Sim-localC s {X = ↑≤ q ⌜ B ⌝}
          (Sim-cast (trans (lift-irr (fit d bd) (≤′-trans q s)) (sym (lift-trans q s)))
            (fundamental d bd φk
              ((≤′-trans p s , castV (lift-trans p s) (upE s {A = ↑≤ p ⌜ A ⌝} a))
               ∷ shiftEnv c s r (proj θ ρ))
              (ra ∷ proj θ ρR)
              (V-rel-cast (lift-trans p s) (V-rel-upE s ar) ,
               EnvRel-shift c s r e (EnvRel-proj θ er)))))))
    e-lam
  where
  s = fit (lam θ p q c d) b
  bd = ≤-trans (m≤n⊔m _ (lvl d)) b

fundamental (app {A = A} {B} {p} {q} d₁ d₂) {N} b {W} φ ρ ρR er =
  Sim-map fin
    (Sim-bind {X = ↑≤ s₁ F'} {Y = ↑≤ t ⌜ B ⌝}
       {P₂ = λ rf rh₁ rh₃ rv → Σ[ rh₂ ∈ RHeap ] Σ[ ra ∈ RVal ]
                                 Eval rh₁ ρR d₂ rh₂ ra × BodyP rf ra rh₂ rh₃ rv}
       (fundamental d₁ b₁ φ ρ ρR er)
       λ {W₁} q₁ φ₁ f rf e₁ vf →
         Sim-bind {X = ↑≤ (fit d₂ b₂) ⌜ A ⌝} {Y = ↑≤ t ⌜ B ⌝} {P₂ = BodyP rf}
           (fundamental d₂ b₂ φ₁ (mono-Env q₁ ρ) ρR (EnvRel-mono q₁ e₁ er))
           λ {W₂} q₂ φ₂ a ra e₂ va →
             Sim-cast (trans (lift-trans q s₁) (lift-irr (≤′-trans q s₁) t))
               (Sim-embedC s₁ {X = ↑≤ q ⌜ B ⌝}
                 (applyRel (down s₁ {A = F'} (mono-Val (↑≤ s₁ F') q₂ f)) rf
                   (down s₁ {A = ↑≤ p ⌜ A ⌝}
                     (castV (trans (lift-irr (fit d₂ b₂) (≤′-trans p s₁)) (sym (lift-trans p s₁))) a))
                   ra
                   (V-rel-down s₁ (V-rel-mono (↑≤ s₁ F') q₂ e₂ vf))
                   (V-rel-down s₁
                     (V-rel-cast (trans (lift-irr (fit d₂ b₂) (≤′-trans p s₁)) (sym (lift-trans p s₁)))
                       va)))))
  where
  b₁ = ≤-trans (m≤m⊔n _ _) b
  b₂ = ≤-trans (m≤n⊔m _ _) b
  s₁ = fit d₁ b₁
  t = fit (app d₁ d₂) b
  F' = arr (↑≤ p ⌜ A ⌝) (↑≤ q ⌜ B ⌝)
  fin : ∀ {rh rh₃ rv} →
        (Σ[ rh₁ ∈ RHeap ] Σ[ rf ∈ RVal ] Eval rh ρR d₁ rh₁ rf ×
           (Σ[ rh₂ ∈ RHeap ] Σ[ ra ∈ RVal ] Eval rh₁ ρR d₂ rh₂ ra × BodyP rf ra rh₂ rh₃ rv)) →
        Eval rh ρR (app d₁ d₂) rh₃ rv
  fin (rh₁ , clo body ρ' , ev₁ , rh₂ , ra , ev₂ , ev₃) = e-app ev₁ ev₂ ev₃
  fin (rh₁ , num _ , _ , _ , _ , _ , ())
  fin (rh₁ , unit  , _ , _ , _ , _ , ())
  fin (rh₁ , loc _ , _ , _ , _ , _ , ())

fundamental (new {A = A} d) {N} b {W} φ ρ ρR er =
  Sim-map fin
    (Sim-bind {X = ↑≤ r ⌜ A ⌝} {Y = ↑≤ s (ref ⌜ A ⌝)}
       {P₂ = λ ra rh₁ rh' rv' → rh' ≡ snoc rh₁ ra × rv' ≡ loc (length rh₁)}
       (fundamental d b' φ ρ ρR er)
       λ q₁ φ₁ v rv e₁ vr →
         Sim-alloc s {X = ⌜ A ⌝} (V-rel-downCell s (V-rel-cast (lift-irr r (predS s)) vr)))
  where
  s = fit (new d) b
  b' = ≤-trans (m≤n⊔m _ _) b
  r = fit d b'
  fin : ∀ {rh rh' rv'} →
        (Σ[ rh₁ ∈ RHeap ] Σ[ ra ∈ RVal ] Eval rh ρR d rh₁ ra ×
           (rh' ≡ snoc rh₁ ra × rv' ≡ loc (length rh₁))) →
        Eval rh ρR (new d) rh' rv'
  fin (rh₁ , ra , ev , refl , refl) = e-new ev

fundamental (get {A = A} d) {N} b {W} φ ρ ρR er =
  Sim-map fin
    (Sim-bind {X = ↑≤ s (ref ⌜ A ⌝)} {Y = ↑≤ r ⌜ A ⌝}
       {P₂ = λ rx rh₁ rh' rv → rh' ≡ rh₁ × Σ[ ℓ ∈ ℕ ] rx ≡ loc ℓ × rh₁ ! ℓ ≡ just rv}
       (fundamental d b φ ρ ρR er)
       cont)
  where
  s = fit d b
  r = fit (get d) b
  cont : ∀ {W₁} (q₁ : W ≤W W₁) φ₁ x rx → Ext W φ φ₁ →
         V-rel N (↑≤ s (ref ⌜ A ⌝)) W₁ φ₁ x rx →
         ⊢Sim N (↑≤ r ⌜ A ⌝) W₁ φ₁
           (λ h → W₁ , ≤W-refl , h ,
                  castV (lift-irr (predS s) r) (upCell s {A = ⌜ A ⌝} (read s {A = ⌜ A ⌝} x h)))
           (λ rh₁ rh' rv → rh' ≡ rh₁ × Σ[ ℓ ∈ ℕ ] rx ≡ loc ℓ × rh₁ ! ℓ ≡ just rv)
  cont {W₁} q₁ φ₁ x rx e₁ vx = sim λ h rh inv →
    let (ℓ , rv , eq , look , vr) = read-rel s inv vx in
    φ₁ , rh , rv , (refl , ℓ , eq , look) , Ext-refl , inv ,
    V-rel-cast (lift-irr (predS s) r) (V-rel-upCell s vr) ,
    (≤-refl , λ _ _ _ → refl) , (λ a _ out → out)
  fin : ∀ {rh rh' rv} →
        (Σ[ rh₁ ∈ RHeap ] Σ[ rx ∈ RVal ] Eval rh ρR d rh₁ rx ×
           (rh' ≡ rh₁ × Σ[ ℓ ∈ ℕ ] rx ≡ loc ℓ × rh₁ ! ℓ ≡ just rv)) →
        Eval rh ρR (get d) rh' rv
  fin (rh₁ , rx , ev , refl , ℓ , refl , look) = e-get ev look

fundamental (put {A = A} d₁ d₂) {N} b {W} φ ρ ρR er =
  Sim-map fin
    (Sim-bind {X = ↑≤ s (ref ⌜ A ⌝)} {Y = ↑≤ u unit}
       {P₂ = λ rx rh₁ rh₃ rv → Σ[ rh₂ ∈ RHeap ] Σ[ ra ∈ RVal ]
                                 Eval rh₁ ρR d₂ rh₂ ra × WriteP rx ra rh₂ rh₃ rv}
       (fundamental d₁ b₁ φ ρ ρR er)
       λ {W₁} q₁ φ₁ x rx e₁ vx →
         Sim-bind {X = ↑≤ r ⌜ A ⌝} {Y = ↑≤ u unit} {P₂ = WriteP rx}
           (fundamental d₂ b₂ φ₁ (mono-Env q₁ ρ) ρR (EnvRel-mono q₁ e₁ er))
           (cont q₁ φ₁ x rx e₁ vx))
  where
  b₁ = ≤-trans (m≤m⊔n _ _) b
  b₂ = ≤-trans (m≤n⊔m _ _) b
  s = fit d₁ b₁
  r = fit d₂ b₂
  u = fit (put d₁ d₂) b
  WriteP : RVal → RVal → RHeap → RHeap → RVal → Set
  WriteP rx ra rh₂ rh₃ rv =
    Σ[ ℓ ∈ ℕ ] rx ≡ loc ℓ × ℓ < length rh₂ × rh₃ ≡ upd rh₂ ℓ ra × rv ≡ unit
  cont : ∀ {W₁} (q₁ : W ≤W W₁) φ₁ x rx → Ext W φ φ₁ →
         V-rel N (↑≤ s (ref ⌜ A ⌝)) W₁ φ₁ x rx →
         ∀ {W₂} (q₂ : W₁ ≤W W₂) φ₂ v rv → Ext W₁ φ₁ φ₂ →
         V-rel N (↑≤ r ⌜ A ⌝) W₂ φ₂ v rv →
         ⊢Sim N (↑≤ u unit) W₂ φ₂
           (λ h → W₂ , ≤W-refl ,
                  write s {A = ⌜ A ⌝} (mono-Val (↑≤ s (ref ⌜ A ⌝)) q₂ x)
                    (downCell s {A = ⌜ A ⌝} (castV (lift-irr r (predS s)) v)) h ,
                  up u {A = unit} tt)
           (WriteP rx rv)
  cont q₁ φ₁ x rx e₁ vx {W₂} q₂ φ₂ v rv e₂ vv = sim λ h rh inv →
    let (ℓ , eq , ℓ< , img , inv') =
          write-rel s inv (V-rel-mono (↑≤ s (ref ⌜ A ⌝)) q₂ e₂ vx)
                          (V-rel-downCell s (V-rel-cast (lift-irr r (predS s)) vv)) in
    φ₂ , upd rh ℓ rv , unit , (ℓ , eq , ℓ< , refl , refl) , Ext-refl , inv' ,
    V-rel-up u {X = unit} refl ,
    (subst (length rh ≤_) (sym (length-upd rh ℓ rv)) ≤-refl ,
     λ a a< out → !-upd-other rh rv (img a out)) ,
    (λ a _ out → out)
  fin : ∀ {rh rh₃ rv} →
        (Σ[ rh₁ ∈ RHeap ] Σ[ rx ∈ RVal ] Eval rh ρR d₁ rh₁ rx ×
           (Σ[ rh₂ ∈ RHeap ] Σ[ ra ∈ RVal ] Eval rh₁ ρR d₂ rh₂ ra × WriteP rx ra rh₂ rh₃ rv)) →
        Eval rh ρR (put d₁ d₂) rh₃ rv
  fin (rh₁ , rx , ev₁ , rh₂ , ra , ev₂ , ℓ , refl , ℓ< , refl , refl) = e-put ev₁ ev₂ ℓ<

------------------------------------------------------------------------
-- Corollaries
------------------------------------------------------------------------

HRel-empty : ∀ k {φ rh} → HRel k (emptyW k) φ (emptyH k) rh
HRel-empty zero    = tt
HRel-empty (suc k) = HRel-empty k , λ ()

Inv-empty : ∀ k {φ rh} → Inv k (emptyW k) φ (emptyH k) rh
Inv-empty k = HRel-empty k , (λ l → ⊥-elim (noLoc l)) , (λ l → ⊥-elim (noLoc l))

-- The full simulation for a closed program: an operational run with a
-- related result, and an injective map from the final semantic heap into
-- the final runtime heap under which every cell's contents are related.
simulation : ∀ {i} {A : Ty i} (d : [] ⊢ A) →
             let (W , _ , h , v) = ⟦ d ⟧ ≤-refl {emptyW (lvl d)} [] (emptyH (lvl d)) in
             Σ[ φ ∈ Map ] Σ[ rh ∈ RHeap ] Σ[ rv ∈ RVal ]
               Eval [] [] d rh rv × Inv (lvl d) W φ h rh ×
               V-rel (lvl d) (↑≤ (fit d ≤-refl) ⌜ A ⌝) W φ v rv
simulation d =
  let (φ , rh , rv , ev , _ , inv , vr , _) =
        run (fundamental d ≤-refl (λ _ → 0) [] [] tt) (emptyH (lvl d)) [] (Inv-empty (lvl d))
  in φ , rh , rv , ev , inv , vr

-- Every closed, well-typed program evaluates.
termination : ∀ {i} {A : Ty i} (d : [] ⊢ A) →
              Σ[ rh ∈ RHeap ] Σ[ rv ∈ RVal ] Eval [] [] d rh rv
termination d = let (_ , rh , rv , ev , _) = simulation d in rh , rv , ev

-- A closed program of type Nat evaluates to exactly the number the model
-- computes.
adequacy : (d : [] ⊢ nat) → Σ[ rh ∈ RHeap ] Eval [] [] d rh (num (proj₁ (runNat d)))
adequacy d with ⟦ d ⟧ ≤-refl {emptyW (lvl d)} [] (emptyH (lvl d))
              | run (fundamental d ≤-refl (λ _ → 0) [] [] tt) (emptyH (lvl d)) [] (Inv-empty (lvl d))
... | W , q , h , v | φ , rh , rv , ev , _ , _ , vr , _ =
  rh , subst (Eval [] [] d rh) (V-rel-down (fit d ≤-refl) vr) ev

-- Space -------------------------------------------------------------------------

-- The world below a cell
underL : ∀ {k} {W : World k} {j A} → Loc W j A → World j
underL {W = W , L} (top x)   = W
underL {W = W , L} (below l) = underL l

InImg-under : ∀ {k} {W : World k} {j A φ a} (l : Loc W j A) →
              InImg (underL l) φ a → InImg W φ a
InImg-under {W = W , L} {φ = φ} (top x)   i = InImg-below {L = L} {φ = φ} i
InImg-under {W = W , L} {φ = φ} (below l) i = InImg-below {L = L} {φ = φ} (InImg-under {φ = φ} l i)

HRel-lookup : ∀ {k} {W : World k} {φ h rh j A} (l : Loc W j A) → HRel k W φ h rh →
              Σ[ v ∈ Val j A (underL l) ] Σ[ rv ∈ RVal ]
                rh ! φ (key l) ≡ just rv × V-rel j A (underL l) φ v rv
HRel-lookup {W = W , L} {h = h , cs} (top x) (hr , tops) =
  let (rv , look , vr) = tops x in All.lookup cs x , rv , look , vr
HRel-lookup {W = W , L} {h = h , cs} (below l) (hr , tops) = HRel-lookup l hr

-- Every address reachable from a related value, through a related heap,
-- is the address of a cell.
reach-img : ∀ {k} {W : World k} {φ h rh} → HRel k W φ h rh →
            ∀ {k'} (X : STy k') {W' : World k'} {v rv a} →
            (∀ {b} → InImg W' φ b → InImg W φ b) →
            V-rel k' X W' φ v rv → Reach rh rv a → InImg W φ a
reach-img hr X emb vr (r-occ o) = emb (Occ-img X vr o)
reach-img {φ = φ} {rh = rh} hr X emb vr (r-step o look r) with emb (Occ-img X vr o)
... | j , A , l , eq with HRel-lookup l hr
...   | v' , rv' , look' , vr' with trans (sym look') (trans (cong (rh !_) eq) look)
...     | refl = reach-img hr A (InImg-under {φ = φ} l) vr' r

-- The live runtime heap is no larger than the semantic heap: every runtime
-- cell reachable from the result is the image of a semantic cell, under an
-- injective map.
live-in-image : ∀ {i} {A : Ty i} (d : [] ⊢ A) →
  let (W , _ , h , v) = ⟦ d ⟧ ≤-refl {emptyW (lvl d)} [] (emptyH (lvl d)) in
  Σ[ φ ∈ Map ] Σ[ rh ∈ RHeap ] Σ[ rv ∈ RVal ]
    Eval [] [] d rh rv × Inj W φ × (∀ a → Reach rh rv a → InImg W φ a)
live-in-image {A = A} d =
  let (φ , rh , rv , ev , (hr , inj , _) , vr) = simulation d
  in φ , rh , rv , ev , inj , (λ a r → reach-img hr (↑≤ (fit d ≤-refl) ⌜ A ⌝) (λ i → i) vr r)

-- An address is reachable from some value in a runtime environment.
data ReachEnv (rh : RHeap) : ∀ {Γ} → REnv Γ → ℕ → Set where
  re-hd : ∀ {x Γ v} {ρ : REnv Γ} {a} → Reach rh v a → ReachEnv rh {x ∷ Γ} (v ∷ ρ) a
  re-tl : ∀ {x Γ v} {ρ : REnv Γ} {a} → ReachEnv rh ρ a → ReachEnv rh {x ∷ Γ} (v ∷ ρ) a

env-reach-img : ∀ {N Γ} {W : World N} {φ h rh} {ρ : Env N Γ W} {ρR : REnv Γ} →
                HRel N W φ h rh → EnvRel W φ ρ ρR → ∀ {a} → ReachEnv rh ρR a → InImg W φ a
env-reach-img {Γ = (i , A) ∷ Γ} {ρ = (q , v) ∷ ρ} {_ ∷ _} hr (vr , er) (re-hd r) =
  reach-img hr (↑≤ q ⌜ A ⌝) (λ i → i) vr r
env-reach-img {ρ = _ ∷ _} {_ ∷ _} hr (_ , er) (re-tl r) = env-reach-img hr er r

-- Heap adequacy at every boundary of evaluation.  Run a subterm d in a
-- related environment from a related heap.  Then the semantic heap
-- afterwards maps injectively into the runtime heap with related contents,
-- and every runtime cell still live, from the subterm's environment or its
-- result, is the image of a semantic cell.
boundary : ∀ {Γ i} {A : Ty i} (d : Γ ⊢ A) {N} (b : lvl d ≤ N) {W : World N} (φ : Map)
             (ρ : Env N Γ W) (ρR : REnv Γ) → EnvRel W φ ρ ρR →
           ∀ h rh → Inv N W φ h rh →
           let (W' , q , h' , v) = ⟦ d ⟧ b ρ h in
           Σ[ φ' ∈ Map ] Σ[ rh' ∈ RHeap ] Σ[ rv ∈ RVal ]
             Eval rh ρR d rh' rv × Inj W' φ' ×
             (∀ a → ReachEnv rh' ρR a ⊎ Reach rh' rv a → InImg W' φ' a)
boundary {A = A} d b φ ρ ρR er h rh inv =
  let (φ' , rh' , rv , ev , e , (hr , inj , _) , vr , _) = run (fundamental d b φ ρ ρR er) h rh inv
      q = proj₁ (proj₂ (⟦ d ⟧ b ρ h))
  in φ' , rh' , rv , ev , inj ,
     λ { a (inl r) → env-reach-img hr (EnvRel-mono q e er) r
       ; a (inr r) → reach-img hr (↑≤ (fit d b) ⌜ A ⌝) (λ i → i) vr r }
