------------------------------------------------------------------------
-- A Kripke logical relation for call-by-need with primitive promises,
-- whose worlds are histories of stores (counterexample.tex, §8).
--
-- Promises cost no universe level: there are no levels at all. The
-- relation is defined by structural recursion on types, and worlds
-- contain no types, so there is no type-world circularity.
--
-- Terms and stores are syntax. That is essential: a store of Agda
-- functions would be Store ≅ Store → …, which Agda rejects. Here the
-- meaning of a cell is carried by the type of the pointer to it, not by
-- the store. Environments replace substitution, so no substitution
-- lemmas are needed.
------------------------------------------------------------------------

module Promises where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Syntax

data Ty : Set where
  nat  : Ty
  _⇒_  : Ty → Ty → Ty
  prom : Ty → Ty

infixr 7 _⇒_

-- Untyped, well-scoped terms. `delay e` is ⌈e⌉ and `force e` is ⌊e⌋.
data Tm (n : ℕ) : Set where
  var   : Fin n → Tm n
  num   : ℕ → Tm n
  lam   : Tm (suc n) → Tm n
  app   : Tm n → Tm n → Tm n
  delay : Tm n → Tm n
  force : Tm n → Tm n

data Val : Set where
  num : ℕ → Val
  clo : ∀ {n} → Tm (suc n) → Vec Val n → Val
  loc : ℕ → Val

-- A cell holds an unforced thunk (a closure) or a memoized value.
data Cell : Set where
  thunk : ∀ {n} → Tm n → Vec Val n → Cell
  value : Val → Cell

Store : Set
Store = List Cell

Trace : Set
Trace = List Store

_!_ : Store → ℕ → Maybe Cell
[]      ! _     = nothing
(c ∷ S) ! zero  = just c
(c ∷ S) ! suc ℓ = S ! ℓ

set : Store → ℕ → Cell → Store
set []      _       _  = []
set (c ∷ S) zero    c' = c' ∷ S
set (c ∷ S) (suc ℓ) c' = c ∷ set S ℓ c'

-- Allocation appends, so the fresh location is `length S`.
snoc : Store → Cell → Store
snoc []       c = c ∷ []
snoc (c' ∷ S) c = c' ∷ snoc S c

------------------------------------------------------------------------
-- Evaluation: big-step, recording the trace of stores after each change.

data Eval {n} (S : Store) (ρ : Vec Val n) : Tm n → Store → Val → Trace → Set where
  e-var   : ∀ {i} → Eval S ρ (var i) S (lookup ρ i) []
  e-num   : ∀ {k} → Eval S ρ (num k) S (num k) []
  e-lam   : ∀ {e} → Eval S ρ (lam e) S (clo e ρ) []
  e-app   : ∀ {e₁ e₂ m} {b : Tm (suc m)} {ρ' S₁ S₂ S₃ v₂ v π₁ π₂ π₃}
          → Eval S ρ e₁ S₁ (clo b ρ') π₁
          → Eval S₁ ρ e₂ S₂ v₂ π₂
          → Eval S₂ (v₂ ∷ ρ') b S₃ v π₃
          → Eval S ρ (app e₁ e₂) S₃ v (π₁ ++ π₂ ++ π₃)
  e-delay : ∀ {e}
          → Eval S ρ (delay e) (snoc S (thunk e ρ)) (loc (length S))
                 (snoc S (thunk e ρ) ∷ [])
  e-hit   : ∀ {e S₁ ℓ v π₁}
          → Eval S ρ e S₁ (loc ℓ) π₁
          → S₁ ! ℓ ≡ just (value v)
          → Eval S ρ (force e) S₁ v π₁
  e-miss  : ∀ {e S₁ ℓ π₁ m} {t : Tm m} {ρ' S₂ v π₂}
          → Eval S ρ e S₁ (loc ℓ) π₁
          → S₁ ! ℓ ≡ just (thunk t ρ')
          → Eval S₁ ρ' t S₂ v π₂
          → Eval S ρ (force e) (set S₂ ℓ (value v)) v
                 (π₁ ++ π₂ ++ set S₂ ℓ (value v) ∷ [])

------------------------------------------------------------------------
-- Typing

infix 4 _⊢_∶_

data _⊢_∶_ {n} (Γ : Vec Ty n) : Tm n → Ty → Set where
  t-var   : ∀ {i} → Γ ⊢ var i ∶ lookup Γ i
  t-num   : ∀ {k} → Γ ⊢ num k ∶ nat
  t-lam   : ∀ {e A B} → (A ∷ Γ) ⊢ e ∶ B → Γ ⊢ lam e ∶ A ⇒ B
  t-app   : ∀ {e₁ e₂ A B} → Γ ⊢ e₁ ∶ A ⇒ B → Γ ⊢ e₂ ∶ A → Γ ⊢ app e₁ e₂ ∶ B
  t-delay : ∀ {e τ} → Γ ⊢ e ∶ τ → Γ ⊢ delay e ∶ prom τ
  t-force : ∀ {e τ} → Γ ⊢ e ∶ prom τ → Γ ⊢ force e ∶ τ

------------------------------------------------------------------------
-- Store lemmas

!-snoc-length : ∀ S c → snoc S c ! length S ≡ just c
!-snoc-length []      c = refl
!-snoc-length (x ∷ S) c = !-snoc-length S c

!-snoc : ∀ S c {ℓ c'} → S ! ℓ ≡ just c' → snoc S c ! ℓ ≡ just c'
!-snoc []      c {ℓ}     ()
!-snoc (x ∷ S) c {zero}  p = p
!-snoc (x ∷ S) c {suc ℓ} p = !-snoc S c p

!-set-≡ : ∀ S ℓ c {c'} → S ! ℓ ≡ just c' → set S ℓ c ! ℓ ≡ just c
!-set-≡ []      ℓ       c ()
!-set-≡ (x ∷ S) zero    c p = refl
!-set-≡ (x ∷ S) (suc ℓ) c p = !-set-≡ S ℓ c p

!-set-≢ : ∀ S {ℓ' ℓ} c → ℓ' ≢ ℓ → set S ℓ' c ! ℓ ≡ S ! ℓ
!-set-≢ []      {ℓ'}     {ℓ}     c ne = refl
!-set-≢ (x ∷ S) {zero}   {zero}  c ne = ⊥-elim (ne refl)
!-set-≢ (x ∷ S) {zero}   {suc ℓ} c ne = refl
!-set-≢ (x ∷ S) {suc ℓ'} {zero}  c ne = refl
!-set-≢ (x ∷ S) {suc ℓ'} {suc ℓ} c ne = !-set-≢ S c (λ p → ne (cong suc p))

!-out : ∀ S {ℓ} → length S ≤ ℓ → S ! ℓ ≡ nothing
!-out []      p       = refl
!-out (x ∷ S) (s≤s p) = !-out S p

length-snoc : ∀ S c → length (snoc S c) ≡ suc (length S)
length-snoc []      c = refl
length-snoc (x ∷ S) c = cong suc (length-snoc S c)

length-set : ∀ S ℓ c → length (set S ℓ c) ≡ length S
length-set []      ℓ       c = refl
length-set (x ∷ S) zero    c = refl
length-set (x ∷ S) (suc ℓ) c = cong suc (length-set S ℓ c)

------------------------------------------------------------------------
-- Determinism

det : ∀ {n S} {ρ : Vec Val n} {e S₁ S₂ v₁ v₂ π₁ π₂}
    → Eval S ρ e S₁ v₁ π₁ → Eval S ρ e S₂ v₂ π₂
    → S₁ ≡ S₂ × v₁ ≡ v₂ × π₁ ≡ π₂
det e-var   e-var   = refl , refl , refl
det e-num   e-num   = refl , refl , refl
det e-lam   e-lam   = refl , refl , refl
det e-delay e-delay = refl , refl , refl
det (e-app a b c) (e-app a' b' c') with det a a'
... | refl , refl , refl with det b b'
... | refl , refl , refl with det c c'
... | refl , refl , refl = refl , refl , refl
det (e-hit a l) (e-hit a' l') with det a a'
... | refl , refl , refl with trans (sym l) l'
... | refl = refl , refl , refl
det (e-hit a l) (e-miss a' l' b') with det a a'
... | refl , refl , refl with trans (sym l) l'
... | ()
det (e-miss a l b) (e-hit a' l') with det a a'
... | refl , refl , refl with trans (sym l) l'
... | ()
det (e-miss a l b) (e-miss a' l' b') with det a a'
... | refl , refl , refl with trans (sym l) l'
... | refl with det b b'
... | refl , refl , refl = refl , refl , refl

------------------------------------------------------------------------
-- Worlds are histories: the stores a computation has passed through.

data Hist : Set where
  [_] : Store → Hist
  _▷_ : Hist → Store → Hist

infixl 5 _▷_ _▷▷_

last : Hist → Store
last [ S ]   = S
last (h ▷ S) = S

_▷▷_ : Hist → Trace → Hist
h ▷▷ []      = h
h ▷▷ (S ∷ π) = (h ▷ S) ▷▷ π

-- Prefix order: the past of a world.
infix 4 _≼_

data _≼_ : Hist → Hist → Set where
  stop : ∀ {h} → h ≼ h
  step : ∀ {h h' S} → h ≼ h' → h ≼ (h' ▷ S)

≼-trans : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
≼-trans p stop     = p
≼-trans p (step q) = step (≼-trans p q)

≼-reflexive : ∀ {a b} → a ≡ b → a ≼ b
≼-reflexive refl = stop

≼-▷▷ : ∀ h π → h ≼ (h ▷▷ π)
≼-▷▷ h []      = stop
≼-▷▷ h (S ∷ π) = ≼-trans (step stop) (≼-▷▷ (h ▷ S) π)

▷▷-++ : ∀ h π₁ π₂ → h ▷▷ (π₁ ++ π₂) ≡ (h ▷▷ π₁) ▷▷ π₂
▷▷-++ h []       π₂ = refl
▷▷-++ h (S ∷ π₁) π₂ = ▷▷-++ (h ▷ S) π₁ π₂

▷▷-++³ : ∀ h π₁ π₂ π₃ → h ▷▷ (π₁ ++ π₂ ++ π₃) ≡ ((h ▷▷ π₁) ▷▷ π₂) ▷▷ π₃
▷▷-++³ h π₁ π₂ π₃ = trans (▷▷-++ h π₁ (π₂ ++ π₃)) (▷▷-++ (h ▷▷ π₁) π₂ π₃)

-- Prefixes of one history are ordered.
cmp : ∀ {a b c} → a ≼ c → b ≼ c → a ≼ b ⊎ b ≼ a
cmp stop     q        = inj₂ q
cmp (step p) stop     = inj₁ (step p)
cmp (step p) (step q) = cmp p q

≼-inv : ∀ {b h S} → b ≼ (h ▷ S) → b ≡ h ▷ S ⊎ b ≼ h
≼-inv stop     = inj₁ refl
≼-inv (step q) = inj₂ q

-- A valid history: each store arises from the previous one by
-- allocation, or by memoization justified by a run of the cell's own
-- thunk recorded earlier in the same history.
data Valid : Hist → Set where
  start : ∀ S → Valid [ S ]
  alloc : ∀ {h} → Valid h → (c : Cell) → Valid (h ▷ snoc (last h) c)
  memo  : ∀ {h hj ℓ m} {t : Tm m} {ρ : Vec Val m} {v π}
        → Valid h
        → hj ▷▷ π ≡ h
        → last hj ! ℓ ≡ just (thunk t ρ)
        → Eval (last hj) ρ t (last h) v π
        → Valid (h ▷ set (last h) ℓ (value v))

valid-inv : ∀ {h S} → Valid (h ▷ S) → Valid h
valid-inv (alloc v c)    = v
valid-inv (memo v _ _ _) = v

valid-prefix : ∀ {a b} → a ≼ b → Valid b → Valid a
valid-prefix stop     v = v
valid-prefix (step p) v = valid-prefix p (valid-inv v)

-- Domains only grow.
dom-mono : ∀ {a b} → a ≼ b → Valid b → length (last a) ≤ length (last b)
dom-mono stop     v = ≤-refl
dom-mono {a} (step p) (alloc {h} v c) =
  subst (length (last a) ≤_) (sym (length-snoc (last h) c))
        (≤-trans (dom-mono p v) (n≤1+n _))
dom-mono {a} (step p) (memo {h} {ℓ = ℓ} {v = w} v _ _ _) =
  subst (length (last a) ≤_) (sym (length-set (last h) ℓ (value w)))
        (dom-mono p v)

------------------------------------------------------------------------
-- Runs extend worlds.

last-ext : ∀ {n S} {ρ : Vec Val n} {e S' v π}
         → Eval S ρ e S' v π → ∀ h → last h ≡ S → last (h ▷▷ π) ≡ S'
last-ext e-var   h eq = eq
last-ext e-num   h eq = eq
last-ext e-lam   h eq = eq
last-ext e-delay h eq = refl
last-ext (e-app {π₁ = π₁} {π₂} {π₃} a b c) h eq
  rewrite ▷▷-++³ h π₁ π₂ π₃ =
  last-ext c _ (last-ext b _ (last-ext a h eq))
last-ext (e-hit a l) h eq = last-ext a h eq
last-ext (e-miss {ℓ = ℓ} {π₁ = π₁} {S₂ = S₂} {v} {π₂} a l b) h eq
  rewrite ▷▷-++³ h π₁ π₂ (set S₂ ℓ (value v) ∷ []) = refl

valid-ext : ∀ {n S} {ρ : Vec Val n} {e S' v π} {h}
          → Valid h → last h ≡ S → Eval S ρ e S' v π → Valid (h ▷▷ π)
valid-ext vh eq e-var = vh
valid-ext vh eq e-num = vh
valid-ext vh eq e-lam = vh
valid-ext {h = h} vh eq (e-delay {e = e}) =
  subst (λ X → Valid (h ▷ snoc X _)) eq (alloc vh _)
valid-ext {h = h} vh eq (e-app {π₁ = π₁} {π₂} {π₃} a b c)
  rewrite ▷▷-++³ h π₁ π₂ π₃ =
  let eq₁ = last-ext a h eq
      eq₂ = last-ext b _ eq₁
  in valid-ext (valid-ext (valid-ext vh eq a) eq₁ b) eq₂ c
valid-ext vh eq (e-hit a l) = valid-ext vh eq a
valid-ext {h = h} vh eq (e-miss {ℓ = ℓ} {π₁ = π₁} {t = t} {ρ'} {S₂} {v} {π₂} a l b)
  rewrite ▷▷-++³ h π₁ π₂ (set S₂ ℓ (value v) ∷ []) =
  let h₁  = h ▷▷ π₁
      h₂  = h₁ ▷▷ π₂
      eq₁ = last-ext a h eq
      eq₂ = last-ext b h₁ eq₁
      vh₂ = valid-ext (valid-ext vh eq a) eq₁ b
      l'  = subst (λ X → X ! ℓ ≡ just (thunk t ρ')) (sym eq₁) l
      b'  = subst (λ X → Eval X ρ' t (last h₂) v π₂) (sym eq₁)
              (subst (λ Y → Eval _ ρ' t Y v π₂) (sym eq₂) b)
  in subst (λ X → Valid (h₂ ▷ set X ℓ (value v))) eq₂ (memo vh₂ refl l' b')

record World : Set where
  constructor ⟨_,_⟩
  field
    hist  : Hist
    valid : Valid hist
open World

_⊑_ : World → World → Set
W ⊑ W' = hist W ≼ hist W'

lastW : World → Store
lastW W = last (hist W)

extend : ∀ {n} {ρ : Vec Val n} {e S v π} (W : World)
       → Eval (lastW W) ρ e S v π → World
extend {π = π} W ev = ⟨ hist W ▷▷ π , valid-ext (valid W) refl ev ⟩

⊑-extend : ∀ {n} {ρ : Vec Val n} {e S v π} (W : World)
           (ev : Eval (lastW W) ρ e S v π) → W ⊑ extend W ev
⊑-extend {π = π} W ev = ≼-▷▷ (hist W) π

last-extend : ∀ {n} {ρ : Vec Val n} {e S v π} (W : World)
              (ev : Eval (lastW W) ρ e S v π) → lastW (extend W ev) ≡ S
last-extend W ev = last-ext ev (hist W) refl

cast : ∀ {n S S'} {ρ : Vec Val n} {e S'' v π}
     → S ≡ S' → Eval S ρ e S'' v π → Eval S' ρ e S'' v π
cast refl ev = ev

------------------------------------------------------------------------
-- The logical relation, by recursion on types.

mutual
  V⟦_⟧ : Ty → World → Val → Set
  V⟦ nat ⟧    W (num _)   = ⊤
  V⟦ A ⇒ B ⟧  W (clo b ρ) =
    ∀ W' → W ⊑ W' → ∀ v → V⟦ A ⟧ W' v → E⟦ B ⟧ W' b (v ∷ ρ)
  V⟦ prom τ ⟧ W (loc ℓ)   =
    ∀ W' → W ⊑ W' → Σ[ c ∈ Cell ] (lastW W' ! ℓ ≡ just c) × C⟦ τ ⟧ W' c
  V⟦ _ ⟧      W _         = ⊥

  -- A cell is good when its thunk is a good computation, or its
  -- memoized value is a good value.
  C⟦_⟧ : Ty → World → Cell → Set
  C⟦ τ ⟧ W (thunk t ρ) = E⟦ τ ⟧ W t ρ
  C⟦ τ ⟧ W (value v)   = V⟦ τ ⟧ W v

  E⟦_⟧ : Ty → World → ∀ {n} → Tm n → Vec Val n → Set
  E⟦ τ ⟧ W e ρ =
    ∀ W' → W ⊑ W' →
    Σ[ S ∈ Store ] Σ[ v ∈ Val ] Σ[ π ∈ Trace ]
    Σ[ ev ∈ Eval (lastW W') ρ e S v π ] V⟦ τ ⟧ (extend W' ev) v

G⟦_⟧ : ∀ {n} → Vec Ty n → World → Vec Val n → Set
G⟦ Γ ⟧ W ρ = ∀ i → V⟦ lookup Γ i ⟧ W (lookup ρ i)

-- Monotonicity: every clause quantifies over the future.
V-mono : ∀ τ {W W' v} → W ⊑ W' → V⟦ τ ⟧ W v → V⟦ τ ⟧ W' v
V-mono nat      {v = num _}   p tt = tt
V-mono (A ⇒ B)  {v = clo b ρ} p f  = λ W'' q → f W'' (≼-trans p q)
V-mono (prom τ) {v = loc ℓ}   p g  = λ W'' q → g W'' (≼-trans p q)
V-mono nat      {v = clo _ _} p ()
V-mono nat      {v = loc _}   p ()
V-mono (A ⇒ B)  {v = num _}   p ()
V-mono (A ⇒ B)  {v = loc _}   p ()
V-mono (prom τ) {v = num _}   p ()
V-mono (prom τ) {v = clo _ _} p ()

E-mono : ∀ τ {W W' n} {e : Tm n} {ρ} → W ⊑ W' → E⟦ τ ⟧ W e ρ → E⟦ τ ⟧ W' e ρ
E-mono τ p E = λ W'' q → E W'' (≼-trans p q)

------------------------------------------------------------------------
-- The history of a freshly allocated cell: until it is forced it holds
-- its thunk; afterwards it holds a value produced by running that thunk
-- in a world no earlier than its allocation.

module CellHistory (h : Hist) {n} (t : Tm n) (ρ : Vec Val n) where

  ℓ₀ : ℕ
  ℓ₀ = length (last h)

  h₁ : Hist
  h₁ = h ▷ snoc (last h) (thunk t ρ)

  -- A cell's contents only change from its thunk to a value.
  stable : ∀ {h*} → h₁ ≼ h* → Valid h*
         → last h* ! ℓ₀ ≡ just (thunk t ρ) ⊎ Σ[ v ∈ Val ] last h* ! ℓ₀ ≡ just (value v)
  stable stop _ = inj₁ (!-snoc-length (last h) _)
  stable (step p) (alloc {h'} vh c) with stable p vh
  ... | inj₁ l       = inj₁ (!-snoc (last h') c l)
  ... | inj₂ (v , l) = inj₂ (v , !-snoc (last h') c l)
  stable (step p) (memo {h'} {ℓ = ℓ'} {v = w} vh _ _ _) with ℓ' ≟ ℓ₀ | stable p vh
  ... | yes refl | inj₁ l       = inj₂ (w , !-set-≡ (last h') ℓ₀ (value w) l)
  ... | yes refl | inj₂ (_ , l) = inj₂ (w , !-set-≡ (last h') ℓ₀ (value w) l)
  ... | no ne    | inj₁ l       = inj₁ (trans (!-set-≢ (last h') (value w) ne) l)
  ... | no ne    | inj₂ (v , l) = inj₂ (v , trans (!-set-≢ (last h') (value w) ne) l)

  record Forced (h* : Hist) : Set where
    field
      hj       : Hist
      S₂       : Store
      v        : Val
      π        : Trace
      valid-hj : Valid hj
      after    : h₁ ≼ hj
      run      : Eval (last hj) ρ t S₂ v π
      prefix   : (hj ▷▷ π) ▷ set S₂ ℓ₀ (value v) ≼ h*
      contents : last h* ! ℓ₀ ≡ just (value v)
  open Forced

  -- A memoization of ℓ₀ is justified no earlier than its allocation,
  -- because ℓ₀ is not in the domain of any earlier store.
  after-alloc : ∀ {h' hj π c} → h₁ ≼ h' → Valid h' → hj ▷▷ π ≡ h'
              → last hj ! ℓ₀ ≡ just c → h₁ ≼ hj
  after-alloc {h'} {hj} {π} p vh eq l
    with cmp p (subst (hj ≼_) eq (≼-▷▷ hj π))
  ... | inj₁ q = q
  ... | inj₂ q with ≼-inv q
  ...   | inj₁ refl = stop
  ...   | inj₂ r with trans (sym (!-out (last hj)
                      (dom-mono r (valid-prefix (≼-trans (step stop) p) vh)))) l
  ...     | ()

  forced-here : ∀ {h' hj m} {t' : Tm m} {ρ' : Vec Val m} {w π'}
              → h₁ ≼ h' → Valid h' → hj ▷▷ π' ≡ h'
              → last hj ! ℓ₀ ≡ just (thunk t' ρ')
              → Eval (last hj) ρ' t' (last h') w π'
              → Forced (h' ▷ set (last h') ℓ₀ (value w))
  forced-here {h'} {hj} {π' = π'} p vh eq l ev
    with after-alloc {π = π'} p vh eq l
  ... | q with stable q (valid-prefix (subst (hj ≼_) eq (≼-▷▷ hj π')) vh)
  ...   | inj₂ (_ , l') with trans (sym l') l
  ...     | ()
  forced-here {h'} {hj} {w = w} {π'} p vh eq l ev | q | inj₁ l' with trans (sym l') l
  ... | refl = record
    { hj       = hj
    ; S₂       = last h'
    ; v        = w
    ; π        = π'
    ; valid-hj = valid-prefix (subst (hj ≼_) eq (≼-▷▷ hj π')) vh
    ; after    = q
    ; run      = ev
    ; prefix   = subst (λ X → X ▷ set (last h') ℓ₀ (value w) ≼ h' ▷ set (last h') ℓ₀ (value w))
                       (sym eq) stop
    ; contents = present (stable p vh)
    }
    where
    present : _ → set (last h') ℓ₀ (value w) ! ℓ₀ ≡ just (value w)
    present (inj₁ l'')      = !-set-≡ (last h') ℓ₀ (value w) l''
    present (inj₂ (_ , l'')) = !-set-≡ (last h') ℓ₀ (value w) l''

  -- A later step that leaves ℓ₀ alone keeps it forced.
  later : ∀ {h* S} (F : Forced h*) → S ! ℓ₀ ≡ just (value (v F)) → Forced (h* ▷ S)
  later F l = record
    { hj = hj F ; S₂ = S₂ F ; v = v F ; π = π F ; valid-hj = valid-hj F
    ; after = after F ; run = run F ; prefix = step (prefix F) ; contents = l }

  history : ∀ {h*} → h₁ ≼ h* → Valid h*
          → last h* ! ℓ₀ ≡ just (thunk t ρ) ⊎ Forced h*
  history stop _ = inj₁ (!-snoc-length (last h) _)
  history (step p) (alloc {h'} vh c) with history p vh
  ... | inj₁ l = inj₁ (!-snoc (last h') c l)
  ... | inj₂ F = inj₂ (later F (!-snoc (last h') c (contents F)))
  history (step p) (memo {h'} {ℓ = ℓ'} {v = w} vh eq l ev) with ℓ' ≟ ℓ₀
  ... | yes refl = inj₂ (forced-here p vh eq l ev)
  ... | no ne with history p vh
  ...   | inj₁ l' = inj₁ (trans (!-set-≢ (last h') (value w) ne) l')
  ...   | inj₂ F  = inj₂ (later F (trans (!-set-≢ (last h') (value w) ne) (contents F)))

------------------------------------------------------------------------
-- The fundamental lemma.

fund : ∀ {n} {Γ : Vec Ty n} {e τ} → Γ ⊢ e ∶ τ
     → ∀ W ρ → G⟦ Γ ⟧ W ρ → E⟦ τ ⟧ W e ρ
fund {Γ = Γ} (t-var {i}) W ρ γ W' p =
  _ , _ , [] , e-var , V-mono (lookup Γ i) p (γ i)
fund t-num W ρ γ W' p = _ , _ , [] , e-num , tt
fund {Γ = Γ} (t-lam {A = A} d) W ρ γ W' p =
  _ , _ , [] , e-lam , λ W'' q v vV → fund d W'' (v ∷ ρ) (γ' (≼-trans p q) vV)
  where
  γ' : ∀ {W'' v} → W ⊑ W'' → V⟦ A ⟧ W'' v → G⟦ A ∷ Γ ⟧ W'' (v ∷ ρ)
  γ' r vV zero    = vV
  γ' r vV (suc i) = V-mono (lookup Γ i) r (γ i)

fund (t-app {A = A} {B} d₁ d₂) W ρ γ W' p with fund d₁ W ρ γ W' p
... | S₁ , clo b ρ' , π₁ , ev₁ , f
  with fund d₂ W ρ γ (extend W' ev₁) (≼-trans p (⊑-extend W' ev₁))
...   | S₂ , v₂ , π₂ , ev₂ , V₂
  with f (extend (extend W' ev₁) ev₂) (⊑-extend (extend W' ev₁) ev₂) v₂ V₂
         (extend (extend W' ev₁) ev₂) stop
...     | S₃ , v , π₃ , ev₃ , V₃ =
  S₃ , v , π₁ ++ π₂ ++ π₃
  , e-app ev₁ (cast (last-extend W' ev₁) ev₂)
              (cast (last-extend (extend W' ev₁) ev₂) ev₃)
  , V-mono B (≼-reflexive (sym (▷▷-++³ (hist W') π₁ π₂ π₃))) V₃
fund (t-app d₁ d₂) W ρ γ W' p | S₁ , num _ , π₁ , ev₁ , ()
fund (t-app d₁ d₂) W ρ γ W' p | S₁ , loc _ , π₁ , ev₁ , ()

fund (t-delay {e = e} {τ} d) W ρ γ W' p =
  _ , _ , _ , e-delay , cell
  where
  open CellHistory (hist W') e ρ
  W₁ : World
  W₁ = extend W' (e-delay {e = e})

  cell : ∀ W* → W₁ ⊑ W* → Σ[ c ∈ Cell ] (lastW W* ! ℓ₀ ≡ just c) × C⟦ τ ⟧ W* c
  cell W* q with history q (valid W*)
  ... | inj₁ l =
    thunk e ρ , l , E-mono τ {W} {W*} (≼-trans p (≼-trans (step stop) q)) (fund d W ρ γ)
  ... | inj₂ F
    with fund d W ρ γ ⟨ Forced.hj F , Forced.valid-hj F ⟩
                       (≼-trans p (≼-trans (step stop) (Forced.after F)))
  ...   | S'' , v'' , π'' , ev'' , V'' with det ev'' (Forced.run F)
  ...     | refl , refl , refl =
    value v'' , Forced.contents F
    , V-mono τ (≼-trans (step stop) (Forced.prefix F)) V''

fund (t-force {τ = τ} d) W ρ γ W' p with fund d W ρ γ W' p
... | S₁ , loc ℓ , π₁ , ev₁ , g with g (extend W' ev₁) stop
...   | value v , l , vV =
  S₁ , v , π₁ , e-hit ev₁ (subst (λ X → X ! ℓ ≡ _) (last-extend W' ev₁) l)
  , V-mono τ stop vV
...   | thunk t ρ' , l , E' with E' (extend W' ev₁) stop
...     | S₂ , v , π₂ , ev₂ , V₂ =
  _ , v , _
  , e-miss ev₁ (subst (λ X → X ! ℓ ≡ _) (last-extend W' ev₁) l)
               (cast (last-extend W' ev₁) ev₂)
  , V-mono τ (subst (λ X → _ ≼ X) (sym (▷▷-++³ (hist W') π₁ π₂ (_ ∷ [])))
                    (step stop)) V₂
fund (t-force d) W ρ γ W' p | S₁ , num _ , π₁ , ev₁ , ()
fund (t-force d) W ρ γ W' p | S₁ , clo _ _ , π₁ , ev₁ , ()

------------------------------------------------------------------------
-- Termination: every closed, well-typed term evaluates, from the empty
-- store, to a value.

W₀ : World
W₀ = ⟨ [ [] ] , start [] ⟩

run : ∀ {e τ} → [] ⊢ e ∶ τ → Store × Val
run d with fund d W₀ [] (λ ()) W₀ stop
... | S , v , _ , _ , _ = S , v

------------------------------------------------------------------------
-- The counterexample: P = λg. g (λn. g (λm. m)), translated.
-- Every argument is a promise and every variable is forced.

N F R τg T : Ty
N  = prom nat
F  = N ⇒ nat
R  = prom F
τg = R ⇒ nat
T  = prom τg

-- ⟦P⟧ = λg. ⌊g⌋ ⌈λn. ⌊g⌋ ⌈λm. ⌊m⌋⌉⌉
⟦P⟧ : Tm 0
⟦P⟧ = lam (app (force (var zero))
               (delay (lam (app (force (var (suc zero)))
                                (delay (lam (force (var zero))))))))

⊢⟦P⟧ : [] ⊢ ⟦P⟧ ∶ T ⇒ nat
⊢⟦P⟧ = t-lam (t-app (t-force t-var)
                    (t-delay (t-lam (t-app (t-force t-var)
                                           (t-delay (t-lam (t-force t-var)))))))

-- ⟦(λh. h) (λf. f 0)⟧ = (λh. ⌊h⌋) ⌈λf. ⌊f⌋ ⌈0⌉⌉, a computation of type τg
⟦G⟧ : Tm 0
⟦G⟧ = app (lam (force (var zero)))
          (delay (lam (app (force (var zero)) (delay (num 0)))))

⊢⟦G⟧ : [] ⊢ ⟦G⟧ ∶ τg
⊢⟦G⟧ = t-app {A = T} (t-lam (t-force t-var))
             (t-delay (t-lam (t-app (t-force t-var) (t-delay t-num))))

-- ⟦P G⟧ = ⟦P⟧ ⌈⟦G⟧⌉
example : [] ⊢ app ⟦P⟧ (delay ⟦G⟧) ∶ nat
example = t-app ⊢⟦P⟧ (t-delay ⊢⟦G⟧)

-- Count memoized and unforced cells.
tally : Store → ℕ × ℕ
tally []              = 0 , 0
tally (value _ ∷ S)   = let (m , u) = tally S in suc m , u
tally (thunk _ _ ∷ S) = let (m , u) = tally S in m , suc u

-- The result is 0. Six cells are allocated: g's argument is forced once
-- and then hit, and the cell for n (the 0 passed by the first call) is
-- never forced.
_ : proj₂ (run example) ≡ num 0
_ = refl

_ : tally (proj₁ (run example)) ≡ (5 , 1)
_ = refl
