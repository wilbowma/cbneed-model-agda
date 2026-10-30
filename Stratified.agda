-- A shallow embedding of a call-by-need STLC using *stratified* higher-order
-- state, following Koronkevich & Bowman, "Type Universes as Kripke Worlds"
-- (ICFP 2025).
--
-- The problem with model.agda is the domain equation
--
--   Store ≅ Name ⇀ (Store → Store × Val)
--
-- which has no solution in Set.  Here the heap is split into layers
-- 0, 1, ..., k-1.  A cell in layer j holds a thunk (or its memoized value)
-- that only depends on layers < j.  So
--
--   Heap (suc k) = Heap k × (cells holding Val k / Comp k)
--
-- and Comp k only quantifies over Heap k: everything is defined by structural
-- recursion on the level, with no TERMINATING pragma and no fuel.
--
-- As in λPR, function types are annotated: `fun p A B : Ty m` is a function
-- living at level m whose parameter cell lives in layer j < m (p : j < m).
--
-- Checked with Agda 2.7.0.1 and the standard library 2.2.

module Stratified where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤′_; _<′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤′-trans; <′⇒<; n≮n)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to ⊎-map)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise-≡⇒≡)
import Data.List.Relation.Binary.Pointwise.Properties as Pointwise
open import Data.List.Relation.Binary.Suffix.Heterogeneous as Suffix
  using (Suffix)
import Data.List.Relation.Binary.Suffix.Heterogeneous.Properties as Suffix
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_; []; _∷ʳ_)
open import Data.List.Relation.Binary.Sublist.Propositional.Properties
  using (All-resp-⊆)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

------------------------------------------------------------------------------
-- Prelude

<′⇒≤′ : ∀ {m n} → m <′ n → m ≤′ n
<′⇒≤′ = ≤′-trans (≤′-step ≤′-refl)

<′-irrefl : ∀ {n} → n <′ n → ⊥
<′-irrefl p = n≮n _ (<′⇒< p)

-- xs ⊑ ys: ys extends xs with newer cells (consed onto the front)
_⊑_ : {X : Set} → List X → List X → Set
_⊑_ = Suffix _≡_

⊑-refl : {X : Set} {xs : List X} → xs ⊑ xs
⊑-refl = Suffix.here (Pointwise.refl refl)

⊑-trans : {X : Set} {xs ys zs : List X} → xs ⊑ ys → ys ⊑ zs → xs ⊑ zs
⊑-trans = Suffix.trans trans

∈-wk : {X : Set} {x : X} {xs ys : List X} → xs ⊑ ys → x ∈ xs → x ∈ ys
∈-wk (Suffix.here eqs) i rewrite Pointwise-≡⇒≡ eqs = i
∈-wk (Suffix.there q) i = there (∈-wk q i)

------------------------------------------------------------------------------
-- Types, indexed by the level they live at.
--   ↑    : cumulativity
--   fun  : a level-m function whose parameter cell is in layer j < m

data Ty : ℕ → Set where
  nat : ∀ {n} → Ty n
  ↑   : ∀ {n} → Ty n → Ty (suc n)
  fun : ∀ {j m} → j <′ m → Ty j → Ty m → Ty m

↑≤ : ∀ {m k} → m ≤′ k → Ty m → Ty k
↑≤ ≤′-refl A = A
↑≤ (≤′-step q) A = ↑ (↑≤ q A)

-- Like ↑≤, but nat stays nat
liftTy : ∀ {m k} → m ≤′ k → Ty m → Ty k
liftTy q nat = nat
liftTy q (↑ A) = ↑≤ q (↑ A)
liftTy q (fun p A B) = ↑≤ q (fun p A B)

------------------------------------------------------------------------------
-- Worlds: the shape of a stratified heap.  Layer j holds cells of types Ty j.
-- Worlds are first-order (syntactic), so there is no type-world circularity.

World : ℕ → Set
World zero = ⊤
World (suc k) = World k × List (Ty k)

_≤W_ : ∀ {k} → World k → World k → Set
_≤W_ {zero} _ _ = ⊤
_≤W_ {suc k} (W , L) (W' , L') = (W ≤W W') × (L ⊑ L')

≤W-refl : ∀ {k} {W : World k} → W ≤W W
≤W-refl {zero} = tt
≤W-refl {suc k} = ≤W-refl , ⊑-refl

≤W-trans : ∀ {k} {W₁ W₂ W₃ : World k} → W₁ ≤W W₂ → W₂ ≤W W₃ → W₁ ≤W W₃
≤W-trans {zero} _ _ = tt
≤W-trans {suc k} (q , qL) (q' , qL') = ≤W-trans q q' , ⊑-trans qL qL'

-- A location of a cell of type A in layer j
data Loc : ∀ {k} → World k → (j : ℕ) → Ty j → Set where
  top   : ∀ {k} {W : World k} {L} {A : Ty k} →
          A ∈ L → Loc {suc k} (W , L) k A
  below : ∀ {k} {W : World k} {L} {j} {A : Ty j} →
          Loc W j A → Loc {suc k} (W , L) j A

locLt : ∀ {k} {W : World k} {j A} → Loc W j A → j <′ k
locLt (top _) = ≤′-refl
locLt (below l) = ≤′-step (locLt l)

mono-Loc : ∀ {k} {W W' : World k} {j A} → W ≤W W' → Loc W j A → Loc W' j A
mono-Loc {W = W , L} {W' , L'} (q , qL) (top x) = top (∈-wk qL x)
mono-Loc {W = W , L} {W' , L'} (q , qL) (below l) = below (mono-Loc q l)

-- Restrict a world to its lowest m layers
lowerW : ∀ {m k} → m ≤′ k → World k → World m
lowerW ≤′-refl W = W
lowerW (≤′-step q) (W , L) = lowerW q W

-- The layers strictly below layer j
under : ∀ {j k} → j <′ k → World k → World j
under ≤′-refl (W , L) = W
under (≤′-step p) (W , L) = under p W

lowerLoc : ∀ {m k} (q : m ≤′ k) {W : World k} {j A} →
           j <′ m → Loc W j A → Loc (lowerW q W) j A
lowerLoc ≤′-refl lt l = l
lowerLoc (≤′-step q) {W , L} lt (top x) = ⊥-elim (<′-irrefl (≤′-trans lt q))
lowerLoc (≤′-step q) {W , L} lt (below l) = lowerLoc q lt l

underLoc : ∀ {j k} (p : j <′ k) {W : World k} {i A} →
           i <′ j → Loc W i A → Loc (under p W) i A
underLoc ≤′-refl {W , L} lt (top x) = ⊥-elim (<′-irrefl lt)
underLoc ≤′-refl {W , L} lt (below l) = l
underLoc (≤′-step p) {W , L} lt (top x) =
  ⊥-elim (<′-irrefl (≤′-trans lt (<′⇒≤′ p)))
underLoc (≤′-step p) {W , L} lt (below l) = underLoc p lt l

------------------------------------------------------------------------------
-- The semantic domain.
--
-- This is where model.agda got stuck.  The recursion is lexicographic on
-- (level, type): Heap k only mentions Val/Comp at level k-1, and Val k only
-- recurs into Comp k at a structurally smaller type.

mutual
  Val : (k : ℕ) → Ty k → World k → Set
  Val k nat W = ℕ
  Val (suc k) (↑ A) (W , L) = Val k A W
  Val k (fun {j} p A B) W = (W' : World k) → W ≤W W' → Loc W' j A → Comp k B W'

  -- Kripke computations, so thunks in the heap can be weakened
  Comp : (k : ℕ) → Ty k → World k → Set
  Comp k A W = (W' : World k) → W ≤W W' → Step k A W'

  Step : (k : ℕ) → Ty k → World k → Set
  Step k A W = Heap k W → Σ (World k) (λ W' → (W ≤W W') × Heap k W' × Val k A W')

  Heap : (k : ℕ) → World k → Set
  Heap zero W = ⊤
  Heap (suc k) (W , L) = Heap k W × All (Cell k W) L

  Cell : (k : ℕ) → World k → Ty k → Set
  Cell k W A = Val k A W ⊎ Comp k A W

Cells : (k : ℕ) → World k → List (Ty k) → Set
Cells k W = All (Cell k W)

mono-Val : ∀ {k} (A : Ty k) {W W' : World k} → W ≤W W' → Val k A W → Val k A W'
mono-Val nat q v = v
mono-Val (↑ A) {W , L} {W' , L'} (q , _) v = mono-Val A q v
mono-Val (fun p A B) q f = λ W'' q' → f W'' (≤W-trans q q')

mono-Cells : ∀ {k} {W W' : World k} {L} → W ≤W W' → Cells k W L → Cells k W' L
mono-Cells q =
  All.map λ {A} → ⊎-map (mono-Val A q) (λ c W'' q' → c W'' (≤W-trans q q'))

lookupC : ∀ {k W L} {A : Ty k} → A ∈ L → Cells k W L → Cell k W A
lookupC x cs = All.lookup cs x

updateC : ∀ {k W L} {A : Ty k} → A ∈ L → Val k A W → Cells k W L → Cells k W L
updateC x v = All.updateAt x (λ _ → inj₁ v)

-- (forced cells , unforced cells), for inspecting a final heap
tally : ∀ {k} {W : World k} → Heap k W → ℕ × ℕ
tally {zero} _ = 0 , 0
tally {suc k} {W , L} (h , cs) = go cs (tally h)
  where
  go : ∀ {L} → Cells k W L → ℕ × ℕ → ℕ × ℕ
  go [] n = n
  go (inj₁ _ ∷ cs) (f , u) = go cs (suc f , u)
  go (inj₂ _ ∷ cs) (f , u) = go cs (f , suc u)

------------------------------------------------------------------------------
-- Monad operations

ret : ∀ {k} {A : Ty k} {W} → Val k A W → Comp k A W
ret {A = A} v W' q h = W' , ≤W-refl , h , mono-Val A q v

bind : ∀ {k} {A B : Ty k} {W} →
       Comp k A W →
       (∀ {W'} → W ≤W W' → Val k A W' → Comp k B W') →
       Comp k B W
bind c f W₁ q₁ h₁ with c W₁ q₁ h₁
... | W₂ , q₂ , h₂ , a with f (≤W-trans q₁ q₂) a W₂ ≤W-refl h₂
...   | W₃ , q₃ , h₃ , b = W₃ , ≤W-trans q₂ q₃ , h₃ , b

mapC : ∀ {k} {A B : Ty k} {W} →
       (∀ {W'} → Val k A W' → Val k B W') → Comp k A W → Comp k B W
mapC f c W' q h with c W' q h
... | W'' , q' , h' , v = W'' , q' , h' , f v

-- Run a level-k computation on the lower part of a level-(k+1) heap
embed1 : ∀ {k} {A : Ty k} {W L} → Comp k A W → Comp (suc k) (↑ A) (W , L)
embed1 c (W' , L') (q , qL) (h , cs) with c W' q h
... | W'' , q'' , h'' , v = (W'' , L') , (q'' , ⊑-refl) , (h'' , mono-Cells q'' cs) , v

embedC : ∀ {m k} (q : m ≤′ k) {A : Ty m} {W} → Comp m A (lowerW q W) → Comp k (↑≤ q A) W
embedC ≤′-refl c = c
embedC (≤′-step q) {A} {W = W , L} c = embed1 {A = ↑≤ q A} (embedC q {A} c)

valDown : ∀ {m k} (q : m ≤′ k) {A : Ty m} {W} → Val k (↑≤ q A) W → Val m A (lowerW q W)
valDown ≤′-refl v = v
valDown (≤′-step q) {W = W , L} v = valDown q v

natDown : ∀ {m k} (q : m ≤′ k) {W} → Val k (↑≤ q nat) W → ℕ
natDown ≤′-refl v = v
natDown (≤′-step q) {W , L} v = natDown q v

toLift : ∀ {m k} (q : m ≤′ k) (A : Ty m) {W} → Val k (↑≤ q A) W → Val k (liftTy q A) W
toLift q nat v = natDown q v
toLift q (↑ A) v = v
toLift q (fun p A B) v = v

------------------------------------------------------------------------------
-- Heap operations

-- Allocate a thunk in layer j.  Its computation only sees layers < j.
alloc : ∀ {j k} (p : j <′ k) {W : World k} {A : Ty j} →
        Cell j (under p W) A → Heap k W →
        Σ (World k) (λ W' → (W ≤W W') × Heap k W' × Loc W' j A)
alloc ≤′-refl {W , L} {A} c (h , cs) =
  (W , A ∷ L) , (≤W-refl , Suffix.there ⊑-refl) , (h , (c ∷ cs)) , top (here refl)
alloc (≤′-step p) {W , L} c (h , cs) with alloc p c h
... | W' , q , h' , l = (W' , L) , (q , ⊑-refl) , (h' , mono-Cells q cs) , below l

-- Force a cell: memoize on first use.  The thunk in layer j runs on
-- layers < j, so it cannot see (or loop through) its own cell; no
-- black-holing is needed.
force : ∀ {j k} (p : j <′ k) {W : World k} {A : Ty j} →
        Loc W j A → Step k (↑≤ (<′⇒≤′ p) A) W
force ≤′-refl {W , L} (top x) (h , cs) with lookupC x cs
... | inj₁ v = (W , L) , ≤W-refl , (h , cs) , v
... | inj₂ c with c W ≤W-refl h
...   | W' , q , h' , v =
  (W' , L) , (q , ⊑-refl) , (h' , updateC x v (mono-Cells q cs)) , v
force ≤′-refl {W , L} (below l) = ⊥-elim (<′-irrefl (locLt l))
force (≤′-step p) {W , L} (top x) = ⊥-elim (<′-irrefl p)
force (≤′-step p) {W , L} (below l) (h , cs) with force p l h
... | W' , q , h' , v = (W' , L) , (q , ⊑-refl) , (h' , mono-Cells q cs) , v

------------------------------------------------------------------------------
-- Syntax: intrinsically typed, level-annotated terms.
-- A context entry (j , A) is a variable whose cell lives in layer j.

Ctx : Set
Ctx = List (Σ ℕ Ty)

Var : Ctx → (j : ℕ) → Ty j → Set
Var Γ j A = (j , A) ∈ Γ

pattern vz = here refl
pattern vs x = there x

-- All variables of Δ live strictly below layer j
Below : Ctx → ℕ → Set
Below Δ j = All (λ (i , _) → i <′ j) Δ

-- A term at level k may only allocate thunks in layers < k, and a thunk
-- in layer j may only capture variables in layers < j (Below).  Thinnings
-- (⊆) play the role of the paper's free-variable-based λ rule.
data Term : (k : ℕ) → Ctx → Ty k → Set where
  var  : ∀ {k Γ j A} → Var Γ j A → (p : j <′ k) → Term k Γ (liftTy (<′⇒≤′ p) A)
  lit  : ∀ {k Γ} → ℕ → Term k Γ nat
  add  : ∀ {k Γ} → Term k Γ nat → Term k Γ nat → Term k Γ nat
  lam  : ∀ {m Γ j A B} → (p : j <′ m) → Term m ((j , A) ∷ Γ) B → Term m Γ (fun p A B)
  app  : ∀ {k m j Γ Δ A B} (q : m ≤′ k) (p : j <′ m) →
         Term k Γ (↑≤ q (fun p A B)) →
         Δ ⊆ Γ → Below Δ j → Term j Δ A →
         Term k Γ (liftTy q B)
  lift : ∀ {k m Γ Δ A} (q : m ≤′ k) →
         Δ ⊆ Γ → Below Δ m → Term m Δ A →
         Term k Γ (liftTy q A)

------------------------------------------------------------------------------
-- Environments map variables to locations

Env : (k : ℕ) → Ctx → World k → Set
Env k Γ W = All (λ (j , A) → Loc W j A) Γ

lookupE : ∀ {k Γ j A} {W : World k} → Var Γ j A → Env k Γ W → Loc W j A
lookupE x ρ = All.lookup ρ x

mono-Env : ∀ {k Γ} {W W' : World k} → W ≤W W' → Env k Γ W → Env k Γ W'
mono-Env q = All.map (mono-Loc q)

proj : ∀ {k Δ Γ} {W : World k} → Δ ⊆ Γ → Env k Γ W → Env k Δ W
proj = All-resp-⊆

lowerEnv : ∀ {m k Δ} (q : m ≤′ k) {W : World k} →
           Below Δ m → Env k Δ W → Env m Δ (lowerW q W)
lowerEnv q b ρ = All.zipWith (λ (lt , l) → lowerLoc q lt l) (b , ρ)

underEnv : ∀ {j k Δ} (p : j <′ k) {W : World k} →
           Below Δ j → Env k Δ W → Env j Δ (under p W)
underEnv p b ρ = All.zipWith (λ (lt , l) → underLoc p lt l) (b , ρ)

------------------------------------------------------------------------------
-- The model

-- Call-by-need application of an (already evaluated) function to a thunk:
-- allocate the thunk in the parameter's layer, then run the body at the
-- function's own level, embedded into the current level.
apply : ∀ {k m j} {A : Ty j} {B : Ty m} (q : m ≤′ k) (p : j <′ m) {W : World k} →
        Val k (↑≤ q (fun p A B)) W → Comp j A (under (≤′-trans p q) W) →
        Step k (liftTy q B) W
apply {A = A} {B} q p f th h with alloc (≤′-trans p q) {A = A} (inj₂ th) h
... | W₃ , q₃ , h₃ , l
  with mapC {A = ↑≤ q B} {B = liftTy q B} (toLift q B)
         (embedC q {B} (valDown q {fun p A B} (mono-Val (↑≤ q (fun p A B)) q₃ f)
                         (lowerW q W₃) ≤W-refl (lowerLoc q p l)))
         W₃ ≤W-refl h₃
...   | W₄ , q₄ , h₄ , v = W₄ , ≤W-trans q₃ q₄ , h₄ , v

⟦_⟧ : ∀ {k Γ A} → Term k Γ A → ∀ {W} → Env k Γ W → Comp k A W
⟦ var {A = A} x p ⟧ ρ =
  mapC {A = ↑≤ (<′⇒≤′ p) A} {B = liftTy (<′⇒≤′ p) A} (toLift (<′⇒≤′ p) A)
       (λ W' q → force p {A = A} (mono-Loc q (lookupE x ρ)))
⟦ lit n ⟧ ρ = ret {A = nat} n
⟦ add e₁ e₂ ⟧ ρ =
  bind {A = nat} {B = nat} (⟦ e₁ ⟧ ρ) λ q n →
  bind {A = nat} {B = nat} (⟦ e₂ ⟧ (mono-Env q ρ)) λ q' m →
  ret {A = nat} (n + m)
⟦ lam {A = A} {B} p e ⟧ ρ = ret {A = fun p A B} (λ W' q l → ⟦ e ⟧ (l ∷ mono-Env q ρ))
⟦ app {A = A} {B} q p e₁ θ b e₂ ⟧ ρ =
  bind {A = ↑≤ q (fun p A B)} {B = liftTy q B} (⟦ e₁ ⟧ ρ) λ q₁ f W₂ q₂ →
  apply q p (mono-Val (↑≤ q (fun p A B)) q₂ f)
        (⟦ e₂ ⟧ (underEnv (≤′-trans p q) b (proj θ (mono-Env (≤W-trans q₁ q₂) ρ))))
⟦ lift {A = A} q θ b e ⟧ ρ = λ W' q' →
  mapC {A = ↑≤ q A} {B = liftTy q A} (toLift q A)
       (embedC q {A} (⟦ e ⟧ (lowerEnv q b (proj θ (mono-Env q' ρ)))))
       W' ≤W-refl

------------------------------------------------------------------------------
-- Running closed programs

emptyW : (k : ℕ) → World k
emptyW zero = tt
emptyW (suc k) = emptyW k , []

emptyH : (k : ℕ) → Heap k (emptyW k)
emptyH zero = tt
emptyH (suc k) = emptyH k , []

-- (value , forced cells , unforced cells in the final heap)
runNat : ∀ {k} → Term k [] nat → ℕ × ℕ × ℕ
runNat {k} e with ⟦ e ⟧ [] (emptyW k) ≤W-refl (emptyH k)
... | W , q , h , v = v , tally h

------------------------------------------------------------------------------
-- Examples.  Sharing is checked by inspecting the final heap: each
-- argument gets exactly one cell, which holds a value once forced and a
-- thunk if never used.

module Examples where
  -- (λ¹ x. x + x) (2 + 3)  ⇒  10; x's one cell is forced
  double : Term 1 [] nat
  double = app ≤′-refl ≤′-refl
             (lam ≤′-refl (add (var vz ≤′-refl) (var vz ≤′-refl)))
             [] [] (add (lit 2) (lit 3))

  test-double : runNat double ≡ (10 , 1 , 0)
  test-double = refl

  -- (λ¹ x. 3) (2 + 3)  ⇒  3; x's cell is never forced
  unused : Term 1 [] nat
  unused = app ≤′-refl ≤′-refl (lam ≤′-refl (lit 3)) [] [] (add (lit 2) (lit 3))

  test-unused : runNat unused ≡ (3 , 0 , 1)
  test-unused = refl

  -- Functions stored in the heap (higher-order state).
  -- F = nat →¹ nat lives at level 1; a cell holding an F lives in layer 1.
  F : Ty 1
  F = fun ≤′-refl nat nat

  -- λ² f. f 1 + f 2
  callTwice : Term 2 [] (fun ≤′-refl F nat)
  callTwice = lam ≤′-refl (add (call (lit 1)) (call (lit 2)))
    where
    call : Term 0 [] nat → Term 2 ((1 , F) ∷ []) nat
    call a = app (≤′-step ≤′-refl) ≤′-refl (var vz ≤′-refl) (_ ∷ʳ []) [] a

  -- (λ² f. f 1 + f 2) (λ¹ y. y + 1)  ⇒  5.  The function value is
  -- memoized in f's cell; each call forces its own y cell.
  hoShare : Term 2 [] nat
  hoShare = app ≤′-refl ≤′-refl callTwice [] []
              (lam ≤′-refl (add (var vz ≤′-refl) (lit 1)))

  test-hoShare : runNat hoShare ≡ (5 , 3 , 0)
  test-hoShare = refl

  -- K = λ¹ y. λ¹ z. y
  K : Term 1 [] (fun ≤′-refl nat F)
  K = lam ≤′-refl (lam ≤′-refl (var (vs vz) ≤′-refl))

  -- (λ² f. f 0 + f 0) (K 7)  ⇒  14.
  -- Forcing f's cell allocates y's cell and memoizes a closure over it;
  -- both calls share y.  The two z cells are never forced.
  closureShare : Term 2 [] nat
  closureShare = app ≤′-refl ≤′-refl callTwice' [] []
                   (app ≤′-refl ≤′-refl K [] [] (lit 7))
    where
    call : Term 2 ((1 , F) ∷ []) nat
    call = app (≤′-step ≤′-refl) ≤′-refl (var vz ≤′-refl) (_ ∷ʳ []) [] (lit 0)
    callTwice' : Term 2 [] (fun ≤′-refl F nat)
    callTwice' = lam ≤′-refl (add call call)

  test-closureShare : runNat closureShare ≡ (14 , 2 , 2)
  test-closureShare = refl

------------------------------------------------------------------------------
-- What this does NOT cover: all of STLC.
--
-- Every call-by-need variable is a heap cell, so capturing a variable costs a
-- level, like capturing a `Ref` in λPR.  Some STLC programs then have no
-- consistent level assignment.  For example, with g : (nat → nat) → nat,
--
--     g (λn. g (λm. m))
--
-- Say g's cell is in layer jg and its type is a level-m function whose
-- parameter (of type nat → nat) is in layer i.  Then:
--   * i < m ≤ jg       (a parameter sits below its function, and the
--                        function's level is at most its cell's layer)
--   * jg < i           (the closure λn. g ... is a thunk in layer i, and it
--                        captures g's cell)
-- That is a contradiction.  The run-time heap is still acyclic; the
-- dependency order just isn't determined by the types.  A stored function
-- would have to accept arguments from arbitrarily higher layers, and that
-- brings back the circularity.
