module Categories.TypeTheory.SubstitutionCalculus where 

open import Prelude
open import Categories 

--------------------------------------------------------------------------------
-- Let's try to concretize

data Type : Set where 
    Nat : Type
    _`→_ : Type → Type → Type 
    -- Int : Type 
    -- Σ* : Type
data Env : Set where 
    ∅ : Env 
    _,_ : Env → Type → Env

private variable 
    Γ Γ₁ Γ₂ : Env
    τ τ₁ τ₂ : Type 

data Var : Env → Type → Set where 
    Z : ∀ {τ : Type} → Var (Γ , τ) τ 
    S : Var Γ τ₁ → Var (Γ , τ₂) τ₁

data Term : Env → Type → Set where 
    Z : ∀ {Γ : Env} → Term Γ  Nat 
    Suc : ∀ {Γ : Env} → Term Γ Nat → Term Γ Nat 
    ` : Var Γ τ → Term Γ τ
    `λ : Term (Γ , τ₁) τ₂ → Term Γ τ₂
    _∘_ : Term Γ (τ₁ `→ τ₂) → Term Γ τ₁ → Term Γ τ₂


Substitution : Env → Env → Set 
Substitution Γ₁ Γ₂ = ∀ {τ} (x : Var Γ₁ τ) → Term Γ₂ τ
sub : Substitution Γ₁ Γ₂ → Term Γ₁ τ → Term Γ₂ τ 

open Category 

SubstCategory : Category 
Obj SubstCategory = Env
_⇒_ SubstCategory = Substitution 
_□_ SubstCategory = λ σ₂ σ₁ → sub σ₂ ○ σ₁
id[_] SubstCategory = λ Γ → `
idₗ SubstCategory = {! sub-id (f x)  !}
idᵣ SubstCategory = {!   !} -- refl


-- This isn't quite right
TypeCategory : Category 
TypeCategory = record
  { Obj = Type
  ; _⇒_ = λ τ₁ τ₂ → ∀ Γ → Term Γ τ₁ → Term Γ τ₂
  ; _□_ = λ f g Γ → f Γ  ○ g Γ
  ; id[_] = λ _ _ M → M
  ; idᵣ = extensionality (λ _ → extensionality (λ _ → refl))
  ; idₗ = extensionality (λ _ → extensionality (λ _ → refl))
  ; assₗ = λ {A} {B} {C} {D} {f} {g} {h} → refl
  } 

-- Model : Functor TypeCategory SetCategory
-- Model = record 
--     { F₀ = λ { Nat → ℕ
--              ; (τ₁ `→ τ₂) → F₀ Model τ₁ → F₀ Model τ₂ }
--     ; F₁ = {!   !}
--     ; F-id = {!   !} 
--     ; F-□ = λ _ _ → {!   !} } 

-- Terms : 


-- lifts : Substitution Γ₁ Γ₂ → Substitution (Γ₁ , τ) (Γ₂ , τ) 
-- lifts σ Z = ` Z
-- lifts σ (S v) = weaken (σ v)

-- extend : ∀ (M : Term Γ₂ τ) → Substitution Γ₁ Γ₂ → Substitution (Γ₁ , τ) Γ₂
-- extend M σ Z = M
-- extend M σ (S v) = σ v

-- sub : Substitution Γ₁ Γ₂ → Term Γ₁ τ → Term Γ₂ τ 
-- sub σ (` x) = σ x
-- sub σ (`λ τ M) = `λ τ (sub (lifts σ) M)
-- sub σ (M ∘ N) = sub σ M ∘ sub σ N

-- sub-lifts-id : ∀ (M : Term (Γ , τ₂) τ₁) → sub (lifts `) M ≡ M
-- sub-lifts-id (` Z) = refl
-- sub-lifts-id (` (S x)) = refl
-- sub-lifts-id (`λ τ₁ M) = {!   !}
-- sub-lifts-id (M ∘ M₁) = {!   !}

-- sub-id : ∀ (M : Term Γ τ) → sub ` M ≡ M
-- sub-id (` x) = refl
-- sub-id (`λ τ₁ M) = {! sub-id   !}
-- sub-id (M ∘ N) = cong₂ _∘_ (sub-id M) (sub-id N)




-- Hom-ℕ : Functor (SetCategory {lzero}) SetCategory 
-- Hom-ℕ = Hom[ SetCategory , ℕ ]

-- S :  Hom-ℕ .F₀ ℕ
-- S = suc 

-- toℕ→ : Hom-ℕ .F₀ ℕ
-- toℕ→ = Hom-ℕ .F₁ (λ { zero → zero
--                     ; (suc x) → x }) S

-- y = Yoneda₂ SetCategory ℕ ListFunctor [ 1 ]
-- y′ = {! y .η  !} 

