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

    _⨾_ = trans 
    
    --------------------------------------------------------------------------------
    -- (A , _≡_) forms a setoid

    ≡-equiv : IsEquivalence (_≡_ {_} {A})
    ≡-equiv .IsEquivalence.refl = refl 
    ≡-equiv .IsEquivalence.sym = sym
    ≡-equiv .IsEquivalence.trans = trans

    `_ : ∀ (A : Set ℓ) → Setoid _ _ 
    `_ A .Setoid.Carrier = A 
    `_ A .Setoid._≈_ = _≡_
    `_ A .Setoid.isEquivalence = ≡-equiv 

    --------------------------------------------------------------------------------
    -- Common functions not defined in the standard library

    cong-both : ∀ {f g : A → B} {x y : A} → 
                  (∀ (a : A) → f a ≡ g a) → x ≡ y → 
                  f x ≡ g y 
    cong-both {f = f} {g} {x} {y} f≡g x≡y = trans (f≡g x) (cong g x≡y)                   