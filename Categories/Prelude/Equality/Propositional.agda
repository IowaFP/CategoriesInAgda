{-# OPTIONS --without-K #-}

module Categories.Prelude.Equality.Propositional where 

open import Categories.Prelude.Base 

module PropositionalEquality where 
    open import Relation.Binary.PropositionalEquality as Eq 
        renaming ([_] to [[_]]) hiding (naturality)  public

    private 
        variable 
            A : Set ℓ₁
            B : Set ℓ₂
            C : Set ℓ₃
    
    --------------------------------------------------------------------------------
    -- Propositional equality is a groupoid

    instance 
        ≡-Groupoid : GroupoidSyntax (_≡_ {A = A})
        ≡-Groupoid = Groupoid refl sym trans

    --------------------------------------------------------------------------------
    -- Homotopies

    private variable
        P : A → Set ℓ 
        f g h j : (x : A) → P x

    infix 4 _∼_
    _∼_ : ((x : A) → P x) → ((x : A) → P x) → Set _
    _∼_ {A = A} f g = (x : A) → f x ≡ g x

    refl-∼ : f ∼ f
    refl-∼ _ = refl 

    sym-∼ : f ∼ g → g ∼ f
    sym-∼ f∼g = sym ○ f∼g

    trans-∼ : f ∼ g → g ∼ h → f ∼ h
    trans-∼ f∼g g∼h x = trans (f∼g x) (g∼h x)

    -- _∼_ is an equivalence relation
    ∼-equiv : IsEquivalence (_∼_ {A = A} {P = P})
    ∼-equiv = record { refl = refl-∼ ; sym = sym-∼ ; trans = trans-∼ }

    -- ((x : A) → B x , _∼_) is a setoid on any type A and family P.
    ∼-setoid : ∀ {A : Set ℓ₁} {P : A → Set ℓ₂} → Setoid (ℓ₁ ⊔ ℓ₂) _
    ∼-setoid {A = A} {P} .Setoid.Carrier = (x : A) → P x
    ∼-setoid {A = A} {P} .Setoid._≈_ = _∼_ {A = A} {P = P}
    ∼-setoid .Setoid.isEquivalence = ∼-equiv

    -- Groupoid syntax
    instance 
      ∼-Groupoid : GroupoidSyntax (_∼_ {A = A} {P = P})
      ∼-Groupoid = Groupoid refl-∼ sym-∼ trans-∼

    -- Left whiskering
    infixl 25 _·ₗ_
    _·ₗ_ : (h : B → C) → (H : f ∼ g) → (h ○ f) ∼ (h ○ g)
    h ·ₗ H = cong h ○ H

    -- Right whiskering
    infixl 25 _·ᵣ_
    _·ᵣ_ : (H : g ∼ h) → (f : A → B) → (g ○ f) ∼ (h ○ f)
    H ·ᵣ f = H ○ f  

    module HtpyReasoning {ℓ₁} {ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} where
      open import Relation.Binary.Reasoning.Base.Single (_∼_ {A = A} {P = P})
        refl-∼
        trans-∼ public

    --------------------------------------------------------------------------------
    -- Common functions not defined in the standard library

    cong-both : ∀ {f g : A → B} {x y : A} → 
                  (∀ (a : A) → f a ≡ g a) → x ≡ y → 
                  f x ≡ g y 
    cong-both {f = f} {g} {x} {y} f≡g x≡y = trans (f≡g x) (cong g x≡y)                   