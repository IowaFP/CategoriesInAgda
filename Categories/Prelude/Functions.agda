{-# OPTIONS --without-K #-}

module Categories.Prelude.Functions where

open import Categories.Prelude.Base 

private 
    variable
        A B C : Set ℓ 

--------------------------------------------------------------------------------
-- Different function types


module Functions₁ (S : Setoid ℓ₁ ℓ₂) where 

  open Setoid S 
  
  --------------------------------------------------------------------------------
  -- _~_ is extensional equality of functions w.r.t. an underlying setoid.
  -- (Analogous to _≗_ from Relation.Binary.PropositionalEquality)
  -- (A → ∣ S ∣, _~_) forms a setoid, where _~_ is equivalence on S.
          
  infixr 0 _~_
  _~_ : (f g : A → ∣ S ∣) → Set _ 
  _~_ f g = ∀ x → f x ≈ g x 
  
  refl-~ : {f : A → ∣ S ∣} → f ~ f 
  refl-~ x = refl 
  
  sym-~ : {f g : A → ∣ S ∣} → f ~ g → g ~ f 
  sym-~ f~g = sym ○ f~g  
  
  trans-~ : {f g h : A → ∣ S ∣} → f ~ g → g ~ h → f ~ h 
  trans-~ f~g g~h x = trans (f~g x) (g~h x)
  
  ~-equiv : IsEquivalence (_~_ {A = A})
  ~-equiv .IsEquivalence.refl = refl-~ 
  ~-equiv .IsEquivalence.sym = sym-~
  ~-equiv .IsEquivalence.trans = trans-~
  
  ~-setoid : ∀ {A : Set ℓ₁} → Setoid _ _ 
  ~-setoid {A = A} .Setoid.Carrier = A → ∣ S ∣ 
  ~-setoid .Setoid._≈_ = _~_
  ~-setoid .Setoid.isEquivalence = ~-equiv 

  --------------------------------------------------------------------------------
  -- A handful of function flavors

  Section : (f : ∣ S ∣ → A) → Set _ 
  Section {A = A} f = Σ[ g ∈ (A → ∣ S ∣) ] (g ○ f ~ id) 

  Retraction : (f : A → ∣ S ∣) → Set _ 
  Retraction {A = A} f = Σ[ g ∈ (∣ S ∣ → A) ] (f ○ g ~ id) 

  Surjection : (f : A → ∣ S ∣) → Set _ 
  Surjection {A = A} f = ∀ (s : ∣ S ∣) → Σ[ a ∈ A ](f a ≈ s) 

  Idempotent : (f : ∣ S ∣ → ∣ S ∣) → Set _ 
  Idempotent f = ∀ (s : ∣ S ∣) → f (f s) ≈ f s

  Involution : (f : ∣ S ∣ → ∣ S ∣) → Set _ 
  Involution f = f ○ f ~ id 

--------------------------------------------------------------------------------
-- Properties that rely on an equivalence on both the domain and codomain
-- of a function.

module Functions₂ (S₁ S₂ : Setoid ℓ₁ ℓ₂) where 

  open Setoid S₁ renaming (_≈_ to _≈₁_)
  open Setoid S₂ renaming (_≈_ to _≈₂_)

  module _ where 
    open Functions₁ S₁ renaming (_~_ to _~₁_)
    open Functions₁ S₂ renaming (_~_ to _~₂_)

    Inverse : (f : ∣ S₁ ∣ → ∣ S₂ ∣) (g : ∣ S₂ ∣ → ∣ S₁ ∣) → Set _ 
    Inverse f g = (g ○ f ~₁ id) * (f ○ g ~₂ id)

    Isomorphism : (f : ∣ S₁ ∣ → ∣ S₂ ∣) → Set _ 
    Isomorphism f = Σ[ g ∈ (∣ S₂ ∣ → ∣ S₁ ∣) ] (Inverse f g)

  Injection : (f : ∣ S₁ ∣ → ∣ S₂ ∣) → Set _ 
  Injection f = ∀ (x y : ∣ S₁ ∣) → f x ≈₂ f y → x ≈₁ y

  Bijection : (f : ∣ S₁ ∣ → ∣ S₂ ∣) → Set _ 
  Bijection f = Injection f * Surjection f 
    where 
        open Functions₁ S₂ using (Surjection)

