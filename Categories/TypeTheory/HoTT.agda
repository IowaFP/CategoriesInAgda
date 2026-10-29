module Categories.TypeTheory.HoTT where 

open import Level 
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality as Eq 
    renaming ([_] to [[_]]) hiding (naturality)

-- ----------------------------------------------------------------------------
-- A library for basic HoTT definitions

private variable
    ℓ ℓ₁ ℓ₂ : Level
    A B C : Set ℓ 

ap : (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
ap = cong

tr : ∀ (P : A → Set ℓ) → {x y : A} → x ≡ y → P x → P y
tr = subst

infixr 5 _▸_ 
_▸_ : A ≡ B → A → B
pf ▸ x = tr id pf x


module Homotopies where 
  private variable
      P : A → Set ℓ 
      f g h : (x : A) → P x

  infix 4 _∼_
  _∼_ : ((x : A) → P x) → ((x : A) → P x) → Set _
  _∼_ {A = A} f g = (x : A) → f x ≡ g x

  refl-∼ : f ∼ f
  refl-∼ _ = refl

  sym-∼ : f ∼ g → g ∼ f
  sym-∼ f∼g = sym ∘ f∼g

  trans-∼ : f ∼ g → g ∼ h → f ∼ h
  trans-∼ f∼g g∼h x = trans (f∼g x) (g∼h x)

  -- Left whiskering
  infixl 25 _·ₗ_
  _·ₗ_ : (h : B → C) → (H : f ∼ g) → (h ∘ f) ∼ (h ∘ g)
  h ·ₗ H = ap h ∘ H

  -- Right whiskering
  infixl 25 _·ᵣ_
  _·ᵣ_ : (H : g ∼ h) → (f : A → B) → (g ∘ f) ∼ (h ∘ f)
  H ·ᵣ f = H ∘ f  
  
open Homotopies public

module HomReasoning {ℓ₁} {ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} where
  -- Open setoid reasoning syntax with carriers A and B. Usage:
  -- f : foo ∼ bar
  -- f = begin
  --   foo ∼⟨ ? ⟩
  --   ...
  --   ?   ∼⟨ ? ⟩
  --   bar ∎
  open import Relation.Binary.Reasoning.Base.Single (_∼_ {A = A} {P = P})
    refl-∼
    trans-∼ public  

record has-inverse {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where 
    constructor Inv
    field
        f⁻¹ : B → A 
        rinv : f ∘ f⁻¹ ∼ id 
        linv : f⁻¹ ∘ f ∼ id 

postulate 
    fun-ext : ∀ {B : A → Set} {f g : (x : A) → B x} → f ∼ g → f ≡ g 
