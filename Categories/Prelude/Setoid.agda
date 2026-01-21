{-# OPTIONS --without-K #-}

module Categories.Prelude.Setoid where

open import Categories.Prelude.Base 
open import Categories.Prelude.Equality.Propositional

--------------------------------------------------------------------------------
-- (A , _≡_) forms a setoid on all types A 
module _ where 
  open PropositionalEquality

  ≡-equiv : ∀ (A : Set ℓ) → IsEquivalence (_≡_ {_} {A})
  ≡-equiv A .IsEquivalence.refl = refl 
  ≡-equiv A .IsEquivalence.sym = sym
  ≡-equiv A .IsEquivalence.trans = trans

  -- We use the shorthand (` A) for the setoid (A , _≡_).
  `_ : ∀ (A : Set ℓ) → Setoid _ _ 
  `_ A .Setoid.Carrier = A 
  `_ A .Setoid._≈_ = _≡_
  `_ A .Setoid.isEquivalence = ≡-equiv A 

--------------------------------------------------------------------------------
-- Setoid morphisms

-- Get the carrier from a setoid 
∣_∣ : Setoid ℓ₁ ℓ₂ → Set ℓ₁ 
∣ S ∣ = S .Setoid.Carrier

-- Setoid arrows (functions that preserve setoid equivalence)
infixr 6 _⇉_ 
record _⇉_ (𝒜 : Setoid o₁ e₁) (ℬ : Setoid o₂ e₂) : Set (o₁ ⊔ o₂ ⊔ e₁ ⊔ e₂) where 
  constructor _,_
  open Setoid 𝒜
  open Setoid ℬ renaming (_≈_ to _`≈_) 
  field 
    smap : ∣ 𝒜 ∣ → ∣ ℬ ∣ 
    hom : ∀ {x y : ∣ 𝒜 ∣} → x ≈ y → smap x `≈ smap y
open _⇉_ public 

--------------------------------------------------------------------------------
-- Helpers over setoid morphisms

module _ where 
  private 
    variable 
      A B C : Setoid o e 

  -- Setoid arrow composition
  _●_ : B ⇉ C → A ⇉ B → A ⇉ C 
  (f , hom-f) ● (g , hom-g) = (f ○ g) , hom-f ○ hom-g

  -- Application of a setoid-arrow to its argument 
  infixr 5 _·_ 
  _·_ : A ⇉ B → ∣ A ∣ → ∣ B ∣ 
  _·_ = smap

  -- Accessor for a setoid arrow's underlying function
  ⌊_⌋ : A ⇉ B → ∣ A ∣ → ∣ B ∣  
  ⌊_⌋ = smap

--------------------------------------------------------------------------------
-- Functions with a setoid domain or codomain (but not both)

module Functions₁ (S : Setoid ℓ₁ ℓ₂) where 

  private 
      variable
          A B C : Set ℓ 

  open Setoid S 
  
  --------------------------------------------------------------------------------
  -- _~_ is extensional equality of functions w.r.t. an underlying setoid.
  -- (Analogous to _≗_ from Relation.Binary.PropositionalEquality.)
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
-- Particular setoid morphisms (that use equivalence on both the domain and  
-- codomain)

module Functions₂ (S₁ : Setoid ℓ₁ ℓ₂) (S₂ : Setoid ℓ₃ ℓ₄) where 

  open Setoid S₁ renaming (_≈_ to _≈₁_)
  open Setoid S₂ renaming (_≈_ to _≈₂_)

  module _ where 
    open Functions₁ S₁ renaming (_~_ to _~₁_)
    open Functions₁ S₂ renaming (_~_ to _~₂_)

    Inverse : (f : S₁ ⇉ S₂) (g : S₂ ⇉ S₁) → Set _ 
    Inverse f g = (⌊ g ● f ⌋ ~₁ id) * ( ⌊ f ● g ⌋ ~₂ id)

    Isomorphism : (f : S₁ ⇉ S₂) → Set _ 
    Isomorphism f = Σ[ g ∈ (S₂ ⇉ S₁) ] (Inverse f g)

  infixr 0 _⇄_ 
  -- infix notation for setoid isomorphism
  _⇄_ = Σ[ f ∈ (S₁ ⇉ S₂) ] Σ[ g ∈ (S₂ ⇉ S₁) ] (Inverse f g)

  Injection : (f : S₁ ⇉ S₂) → Set _ 
  Injection f = ∀ (x y : ∣ S₁ ∣) → f · x ≈₂ f · y → x ≈₁ y

  Bijection : (f : S₁ ⇉ S₂) → Set _ 
  Bijection f = Injection f * Surjection ⌊ f ⌋ 
    where 
        open Functions₁ S₂ using (Surjection)

