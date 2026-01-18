{-# OPTIONS --without-K #-}
module Categories.Instances.Groups where

open import Categories.Prelude
open import Categories.Category
open import Categories.Functor 
open import Categories.NaturalTransformation
open import Categories.Constructions.Groupoid
open import Categories.Constructions.Preorder
open import Categories.Instances.Groupoids

open PropositionalEquality hiding (isPreorder)

--------------------------------------------------------------------------------
-- Groups 

record Group (A : Set o) : Set o where 
  open ≡-Reasoning 
  infixl 5 _+_

  field
    _+_ : A → A → A 
    `0 : A 

    assₗ : ∀ {x y z} → x + (y + z) ≡ (x + y) + z 
    idₗ : ∀ {x} → `0 + x ≡ x
    idᵣ : ∀ {x} → x + `0 ≡ x 
    right-inv : ∀ (x : A) → Σ[ x⁻¹ ∈ A ] (x + x⁻¹ ≡ `0) 

  _⁻¹ : A → A 
  a ⁻¹ = right-inv a .fst 

  cong-+R : ∀ {a b x} → a ≡ b → x + a ≡ x + b 
  cong-+R {x = x}= cong (x +_)
  cong-+L : ∀ {a b x} → a ≡ b → a + x ≡ b + x 
  cong-+L {x = x}= cong (_+ x)

  inverse-unique : ∀ {a b} → b + a ≡ `0 → b ≡ a ⁻¹ 
  inverse-unique {a} {b} e = begin 
    b ≡⟨ (sym idᵣ ⨾ cong-+R (sym (right-inv a .snd))) ⟩ 
    b + (a + a ⁻¹) ≡⟨ (assₗ ⨾ cong-+L e) ⟩ 
    `0 + a ⁻¹ ≡⟨ idₗ ⟩ 
    a ⁻¹ ∎ 
   
  inverse-involutive : ∀ {a} → (a ⁻¹) ⁻¹ ≡ a 
  inverse-involutive {a} = sym (inverse-unique (right-inv a .snd)) 

  left-inv : ∀ (a : A) → a ⁻¹ + a ≡ `0 
  left-inv a = begin
    ((a ⁻¹) + a) ≡⟨ cong-+R (sym inverse-involutive) ⟩ 
    (a ⁻¹ + (a ⁻¹) ⁻¹) ≡⟨ right-inv (a ⁻¹) .snd ⟩ 
    `0 ∎ 

  inverse-distribute : ∀ {a b} → (a + b) ⁻¹ ≡ b ⁻¹ + a ⁻¹ 
  inverse-distribute {a} {b} = sym (inverse-unique {a + b} (begin 
    (b ⁻¹) + (a ⁻¹) + (a + b) ≡⟨ (assₗ ⨾ cong-+L (sym assₗ ⨾ (cong-+R (left-inv a) ⨾ idᵣ))) ⟩ 
    b ⁻¹ + b ≡⟨ left-inv b ⟩ 
    `0 ∎))     


--------------------------------------------------------------------------------
-- Every group can be viewed as a single-object groupoid

module _ (A : Set o) (G : Group A) where 
  open Group G 
  open Category 
  open GroupoidCategory

  GroupGroupoid : GroupoidCategory o o o 
  GroupGroupoid .category .Obj = ⊤ 
  GroupGroupoid .category ._⇒_ =  λ _ _ → A
  GroupGroupoid .category ._∘_ = _+_
  GroupGroupoid .category .Id = `0
  GroupGroupoid .category ._≈_  = _≡_
  GroupGroupoid .category .eqv  = ≡-equiv
  GroupGroupoid .category .cong-∘ = cong₂ _+_ 
  GroupGroupoid .category .idᵣ =  G .idᵣ
  GroupGroupoid .category .idₗ = G .idₗ
  GroupGroupoid .category .assₗ = G .assₗ 
  GroupGroupoid .groupoid = Groupoid (λ a → a ⁻¹ , (right-inv a .snd) , left-inv a)

--------------------------------------------------------------------------------
-- Groups form a category

module _ where
  -- GroupGroupoid : Category o o o 
  -- GroupGroupoid .Obj = ⊤ 
  -- GroupGroupoid  ._⇒_ =  λ _ _ → A
  -- GroupGroupoid  ._∘_ = _+_
  -- GroupGroupoid  .Id = `0
  -- GroupGroupoid  ._≈_  = _≡_
  -- GroupGroupoid  .eqv  = ≡-equiv
  -- GroupGroupoid  .cong-∘ = cong₂ _+_ 
  -- GroupGroupoid  .idᵣ =  G .idᵣ
  -- GroupGroupoid  .idₗ = G .idₗ
  -- GroupGroupoid  .assₗ = G .assₗ 