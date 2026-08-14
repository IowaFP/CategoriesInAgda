module Categories.TypeTheory.CWF where

open import ROmega.Prelude
--------------------------------------------------------------------------------
-- This paper most closely resembles what I'm going for:
-- - https://www.cse.chalmers.se/~peterd/papers/Bremen2007.pdf
-- It is also worth reading this thesis by the paper's coauthor:
-- - http://enslyon.free.fr/rapports/info/Alexandre_Buisse_2.pdf

--------------------------------------------------------------------------------
-- Syntax 

data Env : Set
data Type : Env → Set
data Term : (Γ : Env) → Type Γ → Set
data Var : (Γ : Env) → Type Γ → Set
Renaming : Env → Env → Set 
-- Yes this all goes tits up pretty quickly
renT : ∀ {Γ₁ Γ₂} → Renaming Γ₁ Γ₂ → Type Γ₁ → Type Γ₂
renT r τ = {!   !} 

Renaming Γ₁ Γ₂ =  ∀ {τ} (x : Var Γ₁ τ) → Var Γ₂ (renT {!   !} τ) 


data Env where 
    ∅ : Env 
    _,_ : (Γ : Env) → Type Γ → Env 

private variable 
    Γ Γ₁ Γ₂ Γ₃ : Env 
    τ τ₁ τ₂ τ₃ υ υ₁ υ₂ υ₃ : Type Γ 

data Type where 
    -- Types need variables, too
    𝓤 : Type Γ 
    Π : (τ : Type Γ) → Type (Γ , τ) → Type Γ
    Σ : (τ : Type Γ) → Type (Γ , τ) → Type Γ
    Id : {τ : Type Γ} → (M N : Term Γ τ) → Type Γ

-- Here appears to be where my knowledge shits itself.
-- See 
--  - pg. 14 https://arxiv.org/pdf/1612.02462
--  - similar reference https://drops.dagstuhl.de/storage/00lipics/lipics-vol052-fscd2016/LIPIcs.FSCD.2016.6/LIPIcs.FSCD.2016.6.pdf
--  - Full formalization: https://bitbucket.org/akaposi/tt-in-tt/src/master/NBE/
--  - Nils Anders Daniellson seems to have beaten me to the punch:
--    - paper https://www.cse.chalmers.se/~nad/publications/danielsson-types2006.pdf
--    - code: https://www.cse.chalmers.se/~nad/publications/danielsson-types2006.tgz
--  - Aside: see his work on lenses 
--    - https://www.cse.chalmers.se/~nad/publications/danielsson-dependent-lenses.pdf
--    - https://www.cse.chalmers.se/~nad/publications/capriotti-danielsson-vezzosi-higher-lenses.pdf
--  - And while we're piling on work I ought to understand, but don't, Abel has a good paper on NBE for dependent type theory:
--    - https://www.cse.chalmers.se/~abela/flops10long.pdf
--  - Another paper on NbE of an effectful language, which describes in some detail
--    the particular models that I am unwittingly using:
--    - https://danel.ahman.ee/papers/mfps13.pdf

data Var where 
    Z : ∀ {τ : Type Γ} → Var (Γ , τ) {!   !} 
    -- S : Var Γ τ₁ → Var (Γ , τ₂) τ₁


-- data Term : Env → Type → Set where 
--     ` : Var Γ τ → Term Γ τ 
--     `λ : (τ₁ : Type) → Term (Γ , τ₁) τ₂ → Term Γ (τ₁ `→ τ₂) 
--     _∘_ : Term Γ (τ₁ `→ τ₂) → Term Γ τ₁ → Term Γ τ₂ 

-- --------------------------------------------------------------------------------
-- -- Renaming 

-- Renaming : Env → Env → Set 
-- Renaming Γ₁ Γ₂ =  ∀ {τ} (x : Var Γ₁ τ) → Var Γ₂ τ 

-- lift : Renaming Γ₁ Γ₂ → Renaming (Γ₁ , τ) (Γ₂ , τ) 
-- lift r Z = Z
-- lift r (S v) = S (r v)

-- ren : Renaming Γ₁ Γ₂ → Term Γ₁ τ → Term Γ₂ τ 
-- ren r (` x) = ` (r x)
-- ren r (`λ τ₁ M) = `λ τ₁ (ren (lift r) M)
-- ren r (M ∘ N) = ren r M ∘ ren r N

-- weaken : Term Γ τ → Term (Γ , υ) τ 
-- weaken = ren S 
-- --------------------------------------------------------------------------------
-- -- Substitution

-- Substitution : Env → Env → Set 
-- Substitution Γ₁ Γ₂ = ∀ {τ} (x : Var Γ₁ τ) → Term Γ₂ τ

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

-- --------------------------------------------------------------------------------
-- -- Modeling categories

-- record Category {ℓ₁ ℓ₂} : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where 
--     field
--       Obj : Set ℓ₁
--       _⇒_ : Obj → Obj → Set ℓ₂
--       _∘'_ : ∀ {A B C : Obj} → B ⇒ C → A ⇒ B → A ⇒ C 

--       -- laws 
--       id[_] : ∀ (A : Obj) → A ⇒ A 
--       idᵣ : ∀ {A B} {f : A ⇒ B} → f ∘' id[ A ] ≡ f 
--       idₗ : ∀ {A B} {f : A ⇒ B} → id[ B ] ∘' f ≡ f 
--     --   assₗ : ∀ {A B C} {f : A ⇒ B} {g : B ⇒ C} →  
--     --           g ○ f 

-- open Category

-- WeaklyInitial : ∀ {ℓ} → Category {ℓ} {ℓ} → Set ℓ
-- WeaklyInitial C = Σ[ a ∈ C .Obj ] (∀ (b : C .Obj) → C ._⇒_ a b)

-- RenCategory : Category 
-- Obj RenCategory = Env
-- _⇒_ RenCategory = Renaming 
-- _∘'_ RenCategory = λ r₂ r₁ → r₂ ○ r₁
-- id[_] RenCategory = λ Γ → id
-- idₗ RenCategory = refl
-- idᵣ RenCategory = refl

-- _ : WeaklyInitial RenCategory 
-- _ = ∅ , (λ { _ () })

-- SubstCategory : Category 
-- Obj SubstCategory = Env
-- _⇒_ SubstCategory = Substitution 
-- _∘'_ SubstCategory = λ σ₂ σ₁ → sub σ₂ ○ σ₁
-- id[_] SubstCategory = λ Γ → `
-- idₗ SubstCategory = {! sub-id (f x)  !}
-- idᵣ SubstCategory = refl

-- substInitial : WeaklyInitial SubstCategory 
-- substInitial = ∅ , (λ { _ () })

-- record CwF {ℓ} : Set (lsuc ℓ) where 
--     field 
--         C : Category {ℓ}
--         initial : WeaklyInitial C 
--         Ty : C .Obj → Set 
--         Tm : (a : C .Obj) → Ty a → Set 

-- TermModel : CwF
-- TermModel = record 
--     { C = SubstCategory 
--     ; initial = substInitial 
--     ; Ty = λ _ → Type 
--     ; Tm = Term  }


-- record Functor {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (C : Category {ℓ₁} {ℓ₂}) (D : Category {ℓ₃} {ℓ₄}) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where 
--     field 
--         F₀ : C .Obj → D .Obj 
--         F₁ : ∀ {A B : C .Obj} → (C ._⇒_) A B → (D ._⇒_) (F₀ A) (F₀ B) 
--         -- Laws go here 

-- record SetFunctor {ℓ} (C : Category {ℓ}) : Set (lsuc ℓ) where 
--     field 
--         F₀ : C .Obj → Set ℓ
--         F₁ : ∀ {A B : C .Obj} → (C ._⇒_) A B → (F₀ A) → (F₀ B) 
        
-- -- See:
-- --  - https://github.com/agda/agda-categories/blob/master/src/Categories/Category/Instance/FamilyOfSetoids.agda
-- --  - https://github.com/agda/agda-categories/blob/master/src/Categories/Category/Instance/Sets.agda
-- SetCategory : Category
-- SetCategory = record
--   { Obj = Set
--   ; _⇒_ = λ a b → a → b 
--   ; _∘'_ = λ f g → f ○ g
--   ; id[_] = λ _ x → x
--   ; idᵣ = refl
--   ; idₗ = refl
--   }

-- FamCategory : Category 
-- FamCategory = record
--   { Obj = Σ[ A ∈ Set ] (A → Set)
--   ; _⇒_ = λ { (A₁ , B₁) (A₂ , B₂) → Σ[ f ∈ (A₁ → A₂) ] (∀ (a₁ : A₁) → B₁ a₁ → B₂ (f a₁))  }
--   ; _∘'_ = {!   !}
--   ; id[_] = λ A → id , (λ _ → id)
--   ; idᵣ = {!   !}
--   ; idₗ = {!   !}
--   }



-- TermFunctor :  Functor SubstCategory FamCategory
-- TermFunctor = record 
--     { F₀ = λ Δ → Type , λ τ → Term Δ τ ; 
--     F₁ = λ σ → (λ x → x) , λ τ → sub σ }




