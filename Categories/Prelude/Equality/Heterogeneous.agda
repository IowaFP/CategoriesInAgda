module Categories.Prelude.Equality.Heterogeneous where 

open import Categories.Prelude.Base
open import Categories.Prelude.Equality.Propositional

module HeterogeneousEquality where
  open PropositionalEquality public
  open import Relation.Binary.HeterogeneousEquality 
    renaming (inspect to inspect-≅ ; icong to icong-≅ ; 
              setoid to ≅-setoid ; isEquivalence to ≅-isEquivalence)
    using (_≅_ ; refl ; ≡-subst-removable ; ≡-to-≅ ; 
            ≅-to-≡ ; ≅-to-type-≡ ; module ≅-Reasoning) public
  open ≅-Reasoning public

  --------------------------------------------------------------------------------
  -- The other properties     
  
  sym-≅ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {x : A} {y : B} → x ≅ y → y ≅ x
  sym-≅ refl = refl

  trans-≅ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {x : A} {y : B} {z : C} → 
            x ≅ y → y ≅ z → x ≅ z 
  trans-≅ refl refl = refl

  --------------------------------------------------------------------------------
  -- Het. equivalent terms have het. equivalent types

  ≅-to-type-≅ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {x : A} {y : B} → x ≅ y → A ≅ B
  ≅-to-type-≅ refl = refl

  --------------------------------------------------------------------------------
  -- Remove subst on both sides 

  ≡-subst-removable₂ : ∀ {A : Set ℓ₁} {x y z} →
    (P : A → Set ℓ₂) (eq₁ : x ≡ y) (eq₂ : x ≡ z) (z : P x) →
    subst P eq₁ z ≅ subst P eq₂ z
  ≡-subst-removable₂ P refl refl z = refl


  --------------------------------------------------------------------------------
  -- Subst for heterogeneous equality

  subst-≅ : ∀ {A : Set ℓ₁} {x y} →
    (P : A → Set ℓ₂) (eq : x ≅ y) (z : P x) → P y
  subst-≅ P refl z = z


  --------------------------------------------------------------------------------
  -- Congruence over 1-ary functions

  cong-≅ : ∀  {A : Set ℓ₁} {B : A → Set ℓ₂}
              {x y}
            (f : (x : A) → B x) →
            x ≅ y → f x ≅ f y
  cong-≅ f refl = refl

  -- Congruence for application.
  cong-app-≅ : ∀  {A B : Set ℓ₁} {C : A →  Set ℓ₂} {D : B → Set ℓ₂}
              {x : A} {y : B} → 
              C ≅ D → 
            (f : (x : A) → C x) →
            (g : (x : B) → D x) → 
            f ≅ g → 
            x ≅ y → 
            f x ≅ g y
  cong-app-≅ {C = C} {x = x} {y} refl f g refl refl = refl


  --------------------------------------------------------------------------------
  -- Congruence over 2-ary functions

  cong₂-≅ : ∀  {A : Set ℓ₁} {B : A → Set ℓ₂}
            {C : ∀ x → B x → Set ℓ₃} {x y u v}
            (f : (x : A) (y : B x) → C x y) →
            x ≅ y → u ≅ v → f x u ≅ f y v
  cong₂-≅ f refl refl = refl

  --------------------------------------------------------------------------------
  -- Congruence over tuples

  cong,-≅ : {a b : Level} {A : Set a} {B : A → Set b}
            {p₁ p₂ : Σ A B} →
            Σ (p₁ .fst ≅ p₂ .fst)
            (λ p → (p₁ .snd) ≅ p₂ .snd) →
            p₁ ≅ p₂
  cong,-≅ (refl  , refl) = refl
                      