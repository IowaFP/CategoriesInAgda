module Categories.Prelude.Equality.Extensionality.Heterogeneous where

open import Categories.Prelude.Base
open import Categories.Prelude.Equality.Propositional ; open PropositionalEquality
open import Categories.Prelude.Equality.Heterogeneous ; open HeterogeneousEquality
open import Categories.Prelude.Equality.Extensionality.Propositional
open import Axiom.Extensionality.Heterogeneous renaming (Extensionality to Extensionality-≅)


-- --------------------------------------------------------------------------------  
-- Extensional heterogeneous equality can be derived from the postulated extensionality
-- on propositional equality.

extensionality-≅ : ∀ {ℓ} {ι} → Extensionality-≅ ℓ ι
extensionality-≅ = ≡-ext⇒≅-ext extensionality 

--------------------------------------------------------------------------------
-- We can derive an extensionality principle for functions with differing (but convertible)
-- domains & codomains

extensionality-≅′ : ∀ {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} {B : Set ℓ₁} {C : A → Set ℓ₂} {D : B → Set ℓ₂} → 
                    {f : (x : A) → C x} {g : (x : B) → D x} → 
                    (A ≡ B) → 
                    (∀ (x : A) (y : B) → x ≅ y → C x ≅ D y) → 
                    (∀ (x : A) (y : B) → x ≅ y → f x ≅ g y) → 
                    f ≅ g
extensionality-≅′ {A = A} {B} {C} {D} {f} {g} refl C≡D fx≅gy = 
  extensionality-≅ 
    {B₁ = C} {B₂ = D} {f} {g} 
    (λ x → ≅-to-≡ (C≡D x x refl))
    (λ x → fx≅gy x x refl)

--------------------------------------------------------------------------------
-- Derived extensionality for ∀-quantification

∀-extensionality-≅ :  ∀ {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : A → Set ℓ₂} → 
                    ((x : A) → B x ≅ C x) → ((x : A) → B x) ≅ ((x : A) → C x)
∀-extensionality-≅ {B = B} {C} eq with extensionality-≅ (λ x → refl) eq
... | refl = refl