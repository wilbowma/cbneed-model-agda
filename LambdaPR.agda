------------------------------------------------------------------------
-- λPR (Koronkevich & Bowman, "Type Universes as Kripke Worlds", ICFP
-- 2025) and a shallow embedding of it into Agda.
--
-- Part 1 is the syntax: types with kinding (Fig. 4) and intrinsically
-- typed terms (Fig. 3).  Part 2 is a semantics: each type denotes an Agda
-- type indexed by a stratified world, each term an Agda function over an
-- explicit heap, defined by structural recursion on the typing derivation.
-- Agda accepts everything without postulates, TERMINATING pragmas, fuel,
-- or universe levels above Set: universe levels of λPR do all the work.
--
-- The translation is
--   * typed:       ⟦ Γ ⊢ A ⟧ lands in Comp N ⟦A⟧, a type built from A;
--   * homomorphic: each case of ⟦_⟧ combines the denotations of the
--                  immediate subterms in a fixed way, never their syntax;
--   * heap-explicit: new, ! and := are cell allocation, lookup and update
--                  in a heap of semantic values.
--
-- One semantic consequence worth noting: a function at level k runs its
-- body with fresh, empty heap layers at levels ≥ k, and drops them when it
-- returns.  Cells there are unreachable once the call returns (nothing of
-- level ≤ k can point to them), so the model deallocates them.
------------------------------------------------------------------------

module LambdaPR where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; z≤n; _≤′_; _<′_; ≤′-refl; ≤′-step; _⊔_)
open import Data.Nat.Properties
  using (≤⇒≤′; ≤′⇒≤; ≤-refl; ≤-trans; n≤1+n; m≤m⊔n; m≤n⊔m; <′⇒<; n≮n;
         ≤′-trans)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise-≡⇒≡)
import Data.List.Relation.Binary.Pointwise.Properties as Pointwise
open import Data.List.Relation.Binary.Suffix.Heterogeneous as Suffix
  using (Suffix)
import Data.List.Relation.Binary.Suffix.Heterogeneous.Properties as Suffix
open import Data.List.Relation.Binary.Sublist.Propositional
  using (_⊆_; []; _∷_; _∷ʳ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- Part 1: syntax
------------------------------------------------------------------------

-- Types, indexed by their universe level: Ty i is τ :: Typeᵢ (Fig. 4).
-- Every type has exactly one level, so kinding is an index.
--
--   Nat, Unit :: Type₀
--   τ :: Typeᵢ                          ⟹  Ref τ :: Typeᵢ₊₁
--   τ₁ :: Typeᵢ, τ₂ :: Typeⱼ, i,j ≤ k   ⟹  τ₁ →ᵏ τ₂ :: Typeₖ

data Ty : ℕ → Set where
  nat  : Ty 0
  unit : Ty 0
  ref  : ∀ {i} → Ty i → Ty (suc i)
  arr  : ∀ {i j k} → i ≤′ k → j ≤′ k → Ty i → Ty j → Ty k

-- A context entry carries the level of its type.
Ctx : Set
Ctx = List (Σ ℕ Ty)

-- k ≥ max-level(Γ)
Below : Ctx → ℕ → Set
Below Γ k = All (λ x → proj₁ x ≤′ k) Γ

-- Terms are typing derivations (Fig. 3), with one change: the λ rule is
-- the free-variable variant from §3.1 of the paper.  The body is typed in a
-- sub-context Δ ⊆ Γ, and the function's level k bounds Δ rather than all
-- of Γ.  Choosing Δ = FV(e) gives k ≥ max-level(FV(e), τ₁, τ₂).

infix 4 _⊢_

data _⊢_ (Γ : Ctx) : ∀ {i} → Ty i → Set where
  var : ∀ {i} {A : Ty i} → (i , A) ∈ Γ → Γ ⊢ A
  num : ℕ → Γ ⊢ nat
  ⟨⟩  : Γ ⊢ unit
  lam : ∀ {Δ i j k} {A : Ty i} {B : Ty j} → Δ ⊆ Γ →
        (p : i ≤′ k) (q : j ≤′ k) →
        Below Δ k → (i , A) ∷ Δ ⊢ B → Γ ⊢ arr p q A B
  app : ∀ {i j k} {A : Ty i} {B : Ty j} {p : i ≤′ k} {q : j ≤′ k} →
        Γ ⊢ arr p q A B → Γ ⊢ A → Γ ⊢ B
  new : ∀ {i} {A : Ty i} → Γ ⊢ A → Γ ⊢ ref A
  get : ∀ {i} {A : Ty i} → Γ ⊢ ref A → Γ ⊢ A
  put : ∀ {i} {A : Ty i} → Γ ⊢ ref A → Γ ⊢ A → Γ ⊢ unit

-- The largest level of any type in a derivation.  A program runs in a heap
-- with that many layers.
lvl : ∀ {Γ i} {A : Ty i} → Γ ⊢ A → ℕ
lvl {i = i} (var x)       = i
lvl (num n)               = 0
lvl ⟨⟩                    = 0
lvl {i = k} (lam θ p q c d) = k ⊔ lvl d
lvl (app d₁ d₂)           = lvl d₁ ⊔ lvl d₂
lvl {i = i} (new d)       = i ⊔ lvl d
lvl (get d)               = lvl d
lvl (put d₁ d₂)           = lvl d₁ ⊔ lvl d₂

ty≤lvl : ∀ {Γ i} {A : Ty i} (d : Γ ⊢ A) → i ≤ lvl d
ty≤lvl (var x)             = ≤-refl
ty≤lvl (num n)             = z≤n
ty≤lvl ⟨⟩                  = z≤n
ty≤lvl (lam θ p q c d)     = m≤m⊔n _ _
ty≤lvl (app {q = q} d₁ d₂) =
  ≤-trans (≤′⇒≤ q) (≤-trans (ty≤lvl d₁) (m≤m⊔n _ _))
ty≤lvl (new d)             = m≤m⊔n _ (lvl d)
ty≤lvl (get d)             = ≤-trans (n≤1+n _) (ty≤lvl d)
ty≤lvl (put d₁ d₂)         = z≤n

fit : ∀ {Γ i} {A : Ty i} (d : Γ ⊢ A) {N} → lvl d ≤ N → i ≤′ N
fit d b = ≤⇒≤′ (≤-trans (ty≤lvl d) b)

------------------------------------------------------------------------
-- Part 2: semantics
------------------------------------------------------------------------

-- Levels -----------------------------------------------------------------

<′-irrefl : ∀ {n} → n <′ n → ⊥
<′-irrefl p = n≮n _ (<′⇒< p)

≤′-irr : ∀ {m n} (p q : m ≤′ n) → p ≡ q
≤′-irr ≤′-refl     ≤′-refl     = refl
≤′-irr ≤′-refl     (≤′-step q) = ⊥-elim (<′-irrefl q)
≤′-irr (≤′-step p) ≤′-refl     = ⊥-elim (<′-irrefl p)
≤′-irr (≤′-step p) (≤′-step q) = cong ≤′-step (≤′-irr p q)

-- Semantic type codes ----------------------------------------------------
--
-- STy k describes values that depend on heap layers < k.  ↑ is
-- cumulativity: arrow components are lifted to the arrow's own level, so
-- the semantic domain below is structurally recursive.

data STy : ℕ → Set where
  nat  : STy 0
  unit : STy 0
  ↑    : ∀ {k} → STy k → STy (suc k)
  ref  : ∀ {k} → STy k → STy (suc k)
  arr  : ∀ {k} → STy k → STy k → STy k

↑≤ : ∀ {m k} → m ≤′ k → STy m → STy k
↑≤ ≤′-refl     A = A
↑≤ (≤′-step q) A = ↑ (↑≤ q A)

⌜_⌝ : ∀ {i} → Ty i → STy i
⌜ nat ⌝         = nat
⌜ unit ⌝        = unit
⌜ ref A ⌝       = ref ⌜ A ⌝
⌜ arr p q A B ⌝ = arr (↑≤ p ⌜ A ⌝) (↑≤ q ⌜ B ⌝)

lift-irr : ∀ {m k} (p q : m ≤′ k) {A : STy m} → ↑≤ p A ≡ ↑≤ q A
lift-irr p q rewrite ≤′-irr p q = refl

lift-trans : ∀ {i m k} (p : i ≤′ m) (q : m ≤′ k) {A : STy i} →
             ↑≤ q (↑≤ p A) ≡ ↑≤ (≤′-trans p q) A
lift-trans p ≤′-refl     = refl
lift-trans p (≤′-step q) = cong ↑ (lift-trans p q)

-- Worlds -----------------------------------------------------------------
--
-- A world at level k is the shape of a heap with layers 0 … k-1; layer j
-- holds cells of types STy j.  Worlds are first-order lists of codes.

World : ℕ → Set
World zero    = ⊤
World (suc k) = World k × List (STy k)

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

_≤W_ : ∀ {k} → World k → World k → Set
_≤W_ {zero}  _       _         = ⊤
_≤W_ {suc k} (W , L) (W' , L') = (W ≤W W') × (L ⊑ L')

≤W-refl : ∀ {k} {W : World k} → W ≤W W
≤W-refl {zero}  = tt
≤W-refl {suc k} = ≤W-refl , ⊑-refl

≤W-trans : ∀ {k} {W₁ W₂ W₃ : World k} → W₁ ≤W W₂ → W₂ ≤W W₃ → W₁ ≤W W₃
≤W-trans {zero}  _        _          = tt
≤W-trans {suc k} (q , qL) (q' , qL') = ≤W-trans q q' , ⊑-trans qL qL'

-- The lowest m layers of a world: the paper's ⌊W⌋ₘ.
lowerW : ∀ {m k} → m ≤′ k → World k → World m
lowerW ≤′-refl     W       = W
lowerW (≤′-step q) (W , L) = lowerW q W

lowerW-mono : ∀ {m k} (q : m ≤′ k) {W W' : World k} →
              W ≤W W' → lowerW q W ≤W lowerW q W'
lowerW-mono ≤′-refl     r = r
lowerW-mono (≤′-step q) {W , L} {W' , L'} (r , _) = lowerW-mono q r

-- Add empty layers on top.
extendE : ∀ {m k} → m ≤′ k → World m → World k
extendE ≤′-refl     W = W
extendE (≤′-step q) W = extendE q W , []

-- A cell of type Ref A, with A at level i, lives in layer i.
predS : ∀ {i N} → suc i ≤′ N → i ≤′ N
predS ≤′-refl     = ≤′-step ≤′-refl
predS (≤′-step s) = ≤′-step (predS s)

-- The semantic domain ----------------------------------------------------
--
-- Recursion is lexicographic on (level, code): Heap k only mentions Val at
-- levels below k, and Val k only recurs into Comp k at a smaller code.

mutual
  Val : (k : ℕ) → STy k → World k → Set
  Val _       nat       _       = ℕ
  Val _       unit      _       = ⊤
  Val (suc k) (↑ A)     (W , L) = Val k A W
  Val (suc k) (ref A)   (W , L) = A ∈ L
  Val k       (arr A B) W       =
    (W' : World k) → W ≤W W' → Val k A W' → Comp k B W'

  Comp : (k : ℕ) → STy k → World k → Set
  Comp k A W = Heap k W → Σ[ W' ∈ World k ] W ≤W W' × Heap k W' × Val k A W'

  -- A cell in layer j holds a value that depends only on layers < j.
  Heap : (k : ℕ) → World k → Set
  Heap zero    _       = ⊤
  Heap (suc k) (W , L) = Heap k W × All (λ A → Val k A W) L

mono-Val : ∀ {k} (A : STy k) {W W' : World k} → W ≤W W' → Val k A W → Val k A W'
mono-Val nat       q v = v
mono-Val unit      q v = v
mono-Val (↑ A)     {W , L} {W' , L'} (q , _)  v = mono-Val A q v
mono-Val (ref A)   {W , L} {W' , L'} (_ , qL) x = ∈-wk qL x
mono-Val (arr A B) q f = λ W'' q' → f W'' (≤W-trans q q')

mono-Cells : ∀ {k} {W W' : World k} {L} →
             W ≤W W' → All (λ A → Val k A W) L → All (λ A → Val k A W') L
mono-Cells q = All.map λ {A} → mono-Val A q

castV : ∀ {k} {X Y : STy k} {W} → X ≡ Y → Val k X W → Val k Y W
castV refl v = v

castC : ∀ {k} {X Y : STy k} {W} → X ≡ Y → Comp k X W → Comp k Y W
castC refl c = c

-- A value of a lifted code is a value at the lower level, in the lower
-- part of the world.
down : ∀ {m k} (q : m ≤′ k) {A : STy m} {W} → Val k (↑≤ q A) W → Val m A (lowerW q W)
down ≤′-refl     v = v
down (≤′-step q) {W = W , L} v = down q v

up : ∀ {m k} (q : m ≤′ k) {A : STy m} {W} → Val m A (lowerW q W) → Val k (↑≤ q A) W
up ≤′-refl     v = v
up (≤′-step q) {W = W , L} v = up q v

-- The contents of a cell in layer i, as a value lifted to level N.
downCell : ∀ {i N} (s : suc i ≤′ N) {A : STy i} {W} →
           Val N (↑≤ (predS s) A) W → Val i A (proj₁ (lowerW s W))
downCell ≤′-refl     {W = W , L} v = v
downCell (≤′-step s) {W = W , L} v = downCell s v

upCell : ∀ {i N} (s : suc i ≤′ N) {A : STy i} {W} →
         Val i A (proj₁ (lowerW s W)) → Val N (↑≤ (predS s) A) W
upCell ≤′-refl     {W = W , L} v = v
upCell (≤′-step s) {W = W , L} v = upCell s v

-- A value moved into its world extended with empty layers.
upE : ∀ {k N} (s : k ≤′ N) {A : STy k} {W} → Val k A W → Val N (↑≤ s A) (extendE s W)
upE ≤′-refl     v = v
upE (≤′-step s) v = upE s v

-- The monad --------------------------------------------------------------

ret : ∀ {k} {A : STy k} {W} → Val k A W → Comp k A W
ret v h = _ , ≤W-refl , h , v

bind : ∀ {k} {A B : STy k} {W} → Comp k A W →
       (∀ {W'} → W ≤W W' → Val k A W' → Comp k B W') → Comp k B W
bind c f h with c h
... | W₁ , q₁ , h₁ , a with f q₁ a h₁
...   | W₂ , q₂ , h₂ , b = W₂ , ≤W-trans q₁ q₂ , h₂ , b

-- Run a lower-level computation on the lower layers of a heap.
embed1 : ∀ {k} {A : STy k} {W L} → Comp k A W → Comp (suc k) (↑ A) (W , L)
embed1 {L = L} c (h , cs) with c h
... | W' , q , h' , v = (W' , L) , (q , ⊑-refl) , (h' , mono-Cells q cs) , v

embedC : ∀ {m k} (q : m ≤′ k) {A : STy m} {W} →
         Comp m A (lowerW q W) → Comp k (↑≤ q A) W
embedC ≤′-refl     c = c
embedC (≤′-step q) {A} {W , L} c = embed1 {A = ↑≤ q A} (embedC q c)

-- Run a computation with fresh empty layers on top, and drop them after.
drop1 : ∀ {k} {A : STy k} {W} → Comp (suc k) (↑ A) (W , []) → Comp k A W
drop1 c h with c (h , [])
... | (W' , L') , (q , _) , (h' , _) , v = W' , q , h' , v

localC : ∀ {m k} (q : m ≤′ k) {A : STy m} {W} →
         Comp k (↑≤ q A) (extendE q W) → Comp m A W
localC ≤′-refl     c = c
localC (≤′-step q) {A} c = localC q (drop1 {A = ↑≤ q A} c)

-- The heap ---------------------------------------------------------------
--
-- A reference of type Ref A, with A at level i, is a cell in layer i.

alloc : ∀ {i N} (s : suc i ≤′ N) {A : STy i} {W} →
        Val i A (proj₁ (lowerW s W)) → Comp N (↑≤ s (ref A)) W
alloc ≤′-refl {A} {W , L} v (h , cs) =
  (W , A ∷ L) , (≤W-refl , Suffix.there ⊑-refl) , (h , v ∷ cs) , here refl
alloc (≤′-step s) {A} {W , L} v = embed1 {A = ↑≤ s (ref A)} (alloc s v)

read : ∀ {i N} (s : suc i ≤′ N) {A : STy i} {W} →
       Val N (↑≤ s (ref A)) W → Heap N W → Val i A (proj₁ (lowerW s W))
read ≤′-refl     {W = W , L} x (h , cs) = All.lookup cs x
read (≤′-step s) {W = W , L} x (h , cs) = read s x h

write : ∀ {i N} (s : suc i ≤′ N) {A : STy i} {W} →
        Val N (↑≤ s (ref A)) W → Val i A (proj₁ (lowerW s W)) → Heap N W → Heap N W
write ≤′-refl     {W = W , L} x v (h , cs) = h , All.updateAt x (λ _ → v) cs
write (≤′-step s) {W = W , L} x v (h , cs) = write s x v h , cs

-- Environments -----------------------------------------------------------
--
-- Programs run at a fixed level N.  A variable of type A at level i holds
-- a value of A lifted to N, which is a value at level i in the lowest i
-- layers.

Entry : (N : ℕ) → World N → Σ ℕ Ty → Set
Entry N W x = Σ[ q ∈ proj₁ x ≤′ N ] Val N (↑≤ q ⌜ proj₂ x ⌝) W

Env : (N : ℕ) → Ctx → World N → Set
Env N Γ W = All (Entry N W) Γ

mono-Env : ∀ {N Γ} {W W' : World N} → W ≤W W' → Env N Γ W → Env N Γ W'
mono-Env r = All.map λ { {i , A} (q , v) → q , mono-Val (↑≤ q ⌜ A ⌝) r v }

-- Move a captured variable, of level i ≤ k, into the world of a level-k
-- function's body: its own layers, then fresh ones.
shiftV : ∀ {i k N} (c : i ≤′ k) (s : k ≤′ N) (q : i ≤′ N) {X : STy i}
         {W : World N} {Wk : World k} →
         lowerW s W ≤W Wk → Val N (↑≤ q X) W →
         Val N (↑≤ (≤′-trans c s) X) (extendE s Wk)
shiftV c s q {X} {W} {Wk} r v =
  castV (lift-trans c s)
    (upE s {A = ↑≤ c X}
      (mono-Val (↑≤ c X) r
        (down s {A = ↑≤ c X}
          (castV (trans (lift-irr q (≤′-trans c s)) (sym (lift-trans c s))) v))))

-- Restrict an environment along a thinning.
proj : ∀ {P : Σ ℕ Ty → Set} {Δ Γ} → Δ ⊆ Γ → All P Γ → All P Δ
proj []         []      = []
proj (y ∷ʳ θ)   (_ ∷ ρ) = proj θ ρ
proj (refl ∷ θ) (v ∷ ρ) = v ∷ proj θ ρ

shiftEnv : ∀ {Γ k N} {W : World N} {Wk : World k} → Below Γ k → (s : k ≤′ N) →
           lowerW s W ≤W Wk → Env N Γ W → Env N Γ (extendE s Wk)
shiftEnv []       s r []             = []
shiftEnv (c ∷ cs) s r ((q , v) ∷ ρ) = (≤′-trans c s , shiftV c s q r v) ∷ shiftEnv cs s r ρ

-- The interpretation -------------------------------------------------------
--
-- By structural recursion on the derivation; each case uses only the
-- denotations of the immediate subderivations.

⟦_⟧ : ∀ {Γ i} {A : Ty i} (d : Γ ⊢ A) {N} (b : lvl d ≤ N) {W : World N} →
      Env N Γ W → Comp N (↑≤ (fit d b) ⌜ A ⌝) W

⟦ var {A = A} x ⟧ b ρ with All.lookup ρ x
... | q , v = ret {A = ↑≤ (fit (var x) b) ⌜ A ⌝} (castV (lift-irr q (fit (var x) b)) v)

⟦_⟧ {Γ} (num n) b ρ = ret {A = ↑≤ (fit (num {Γ} n) b) nat} (up (fit (num {Γ} n) b) {A = nat} n)

⟦_⟧ {Γ} ⟨⟩ b ρ = ret {A = ↑≤ (fit (⟨⟩ {Γ}) b) unit} (up (fit (⟨⟩ {Γ}) b) {A = unit} tt)

⟦ lam {A = A} {B} θ p q c d ⟧ {N} b {W} ρ =
  ret {A = ↑≤ s (arr (↑≤ p ⌜ A ⌝) (↑≤ q ⌜ B ⌝))} (up s {A = arr (↑≤ p ⌜ A ⌝) (↑≤ q ⌜ B ⌝)} f)
  where
  s = fit (lam θ p q c d) b
  bd = ≤-trans (m≤n⊔m _ (lvl d)) b
  f : Val _ (arr (↑≤ p ⌜ A ⌝) (↑≤ q ⌜ B ⌝)) (lowerW s W)
  f Wk r a =
    localC s {A = ↑≤ q ⌜ B ⌝}
      (castC (trans (lift-irr (fit d bd) (≤′-trans q s)) (sym (lift-trans q s)))
        (⟦ d ⟧ bd
          ((≤′-trans p s , castV (lift-trans p s) (upE s {A = ↑≤ p ⌜ A ⌝} a))
           ∷ shiftEnv c s r (proj θ ρ))))

⟦ app {A = A} {B} {p} {q} d₁ d₂ ⟧ {N} b ρ =
  bind {A = ↑≤ s₁ F'} {B = ↑≤ t ⌜ B ⌝} (⟦ d₁ ⟧ b₁ ρ) λ r₁ f →
  bind {A = ↑≤ (fit d₂ b₂) ⌜ A ⌝} {B = ↑≤ t ⌜ B ⌝} (⟦ d₂ ⟧ b₂ (mono-Env r₁ ρ)) λ {W₂} r₂ a →
  castC (trans (lift-trans q s₁) (lift-irr (≤′-trans q s₁) t))
    (embedC s₁ {A = ↑≤ q ⌜ B ⌝}
      (down s₁ {A = F'} (mono-Val (↑≤ s₁ F') r₂ f)
        (lowerW s₁ W₂) ≤W-refl
        (down s₁ {A = ↑≤ p ⌜ A ⌝}
          (castV (trans (lift-irr (fit d₂ b₂) (≤′-trans p s₁)) (sym (lift-trans p s₁))) a))))
  where
  b₁ = ≤-trans (m≤m⊔n _ _) b
  b₂ = ≤-trans (m≤n⊔m _ _) b
  s₁ = fit d₁ b₁
  t = fit (app d₁ d₂) b
  F' = arr (↑≤ p ⌜ A ⌝) (↑≤ q ⌜ B ⌝)

⟦ new {A = A} d ⟧ {N} b ρ =
  bind {A = ↑≤ r ⌜ A ⌝} {B = ↑≤ s (ref ⌜ A ⌝)} (⟦ d ⟧ b' ρ) λ {W₁} _ v →
  alloc s {A = ⌜ A ⌝} (downCell s {A = ⌜ A ⌝} (castV (lift-irr r (predS s)) v))
  where
  s = fit (new d) b
  b' = ≤-trans (m≤n⊔m _ _) b
  r = fit d b'

⟦ get {A = A} d ⟧ {N} b ρ =
  bind {A = ↑≤ s (ref ⌜ A ⌝)} {B = ↑≤ r ⌜ A ⌝} (⟦ d ⟧ b ρ) λ {W₁} _ x h →
  W₁ , ≤W-refl , h ,
  castV (lift-irr (predS s) r) (upCell s {A = ⌜ A ⌝} (read s {A = ⌜ A ⌝} x h))
  where
  s = fit d b
  r = fit (get d) b

⟦ put {A = A} d₁ d₂ ⟧ {N} b ρ =
  bind {A = ↑≤ s (ref ⌜ A ⌝)} {B = ↑≤ u unit} (⟦ d₁ ⟧ b₁ ρ) λ r₁ x →
  bind {A = ↑≤ r ⌜ A ⌝} {B = ↑≤ u unit} (⟦ d₂ ⟧ b₂ (mono-Env r₁ ρ)) λ {W₂} r₂ v h →
  W₂ , ≤W-refl ,
  write s {A = ⌜ A ⌝} (mono-Val (↑≤ s (ref ⌜ A ⌝)) r₂ x)
          (downCell s {A = ⌜ A ⌝} (castV (lift-irr r (predS s)) v)) h ,
  up u {A = unit} tt
  where
  b₁ = ≤-trans (m≤m⊔n _ _) b
  b₂ = ≤-trans (m≤n⊔m _ _) b
  s = fit d₁ b₁
  r = fit d₂ b₂
  u = fit (put d₁ d₂) b

------------------------------------------------------------------------
-- Running closed programs
------------------------------------------------------------------------

emptyW : (k : ℕ) → World k
emptyW zero    = tt
emptyW (suc k) = emptyW k , []

emptyH : (k : ℕ) → Heap k (emptyW k)
emptyH zero    = tt
emptyH (suc k) = emptyH k , []

cells : ∀ {k} {W : World k} → Heap k W → ℕ
cells {zero}  _ = 0
cells {suc k} {W , L} (h , _) = cells h + length L

-- (result , number of cells in the final heap)
runNat : (d : [] ⊢ nat) → ℕ × ℕ
runNat d with ⟦ d ⟧ ≤-refl {emptyW (lvl d)} [] (emptyH (lvl d))
... | W , _ , h , v = down (fit d ≤-refl) v , cells h
