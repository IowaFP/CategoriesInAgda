{-# OPTIONS --without-K #-}

module Categories.Constructions.Product where 

open import Categories.Prelude
open import Categories.Category

-- ------------------------------------------------------------------------------
{- Products
A product X × Y in 𝒞 is an object with projections 
π₁ : X × Y → X and π₂ : X × Y → Y such that, for any
f : C → X and g : C → Y there exists a unique arrow
⟨ f , g ⟩ : C → X × Y where the following diagram commutes.

                C
              / |  \
             /  |   \
            /   |    \
        f  /    | !   \ g 
          /     |      \ 
         v      v       v
        X <-- X × Y --> Y
             π₁      π₂
-}

module _ (𝒞 : Category o a e) where 
  open Category 𝒞 

  private 
    variable
      A B C D X Y : Obj 
      f g h : A ⇒ B 

  -- ------------------------------------------------------------------------------
  -- A product can exist between any two objects in a given category.
  -- The record hasProduct describes such a relation.

  record hasProduct (X₁ X₂ : Obj) : Set (o ⊔ e ⊔ a) where 
    field 
      X₁×X₂ : Obj 
      `π₁  : X₁×X₂ ⇒ X₁ 
      `π₂ : X₁×X₂  ⇒ X₂ 
      ⟨_,_⟩ : Y ⇒ X₁ → Y ⇒ X₂ → Y ⇒ X₁×X₂ 

      project₁ : `π₁ ∘ ⟨ f , g ⟩ ≈ f 
      project₂ : `π₂ ∘ ⟨ f , g ⟩ ≈ g 
      unique : `π₁ ∘ f ≈ g → `π₂ ∘ f ≈ h → ⟨ g , h ⟩ ≈ f  
  
    ×-g-η : ⟨ `π₁ ∘ f , `π₂ ∘ f ⟩ ≈ f 
    ×-g-η = unique refl-≈ refl-≈ 

    ×-η : ⟨ `π₁ , `π₂ ⟩ ≈ Id
    ×-η = unique idᵣ idᵣ 

    ∘-distrib-⟨⟩ : ∀ {q : A ⇒ Y} → ⟨ f ∘ q , g ∘ q ⟩ ≈ ⟨ f , g ⟩ ∘ q
    ∘-distrib-⟨⟩ {q = q} = unique (assₗ ⨾ project₁ ⋆ₗ q) (assₗ ⨾ project₂ ⋆ₗ q) 

  -- ------------------------------------------------------------------------------
  -- A category admits products if a product object exists between any two objects.
  -- A note on design: we could define 
  --   AdmitsProducts 𝒞 = (X Y : 𝒞 .obj) → HasProduct X Y 
  -- but this is unpleasant to work with. Given p : AdmitsProducts 𝒞, We would have to define
  -- A × B as an alias
  --   A × B := p A B .X₁×X₂. 
  -- This obfuscates the terms that appear in goals, and is less ergonomic.

  -- We will instead permit some overlap in logic to define e.g. _×_ as a primitive
  -- operator.

  record AdmitsProducts : Set (o ⊔ e ⊔ a) where 
    field 
      _×_  : Obj → Obj → Obj
      `π₁  : X × Y ⇒ X
      `π₂  : X × Y ⇒ Y
      ⟨_,_⟩ : A ⇒ B → A ⇒ C → A ⇒ B × C

      project₁ : {f : A ⇒ B} {g : A ⇒ C} → `π₁ ∘ ⟨ f , g ⟩ ≈ f 
      project₂ : {f : A ⇒ B} {g : A ⇒ C} → `π₂ ∘ ⟨ f , g ⟩ ≈ g 
      unique : {f : A ⇒ X × Y} {g : A ⇒ X} {h : A ⇒ Y} → `π₁ ∘ f ≈ g → `π₂ ∘ f ≈ h → ⟨ g , h ⟩ ≈ f  

    ⟪_,_⟫ : ∀ (f : A ⇒ X) (g : B ⇒ Y) → A × B ⇒ X × Y 
    ⟪ f , g ⟫ = ⟨ f ∘ `π₁ , g ∘ `π₂ ⟩

    ×-g-η : ⟨ `π₁ ∘ f , `π₂ ∘ f ⟩ ≈ f 
    ×-g-η = unique refl-≈ refl-≈ 

    ×-η : ⟨ `π₁ {X} {Y} , `π₂ ⟩ ≈ Id
    ×-η = unique idᵣ idᵣ 

    ∘-distrib-⟨⟩ : ∀ {q : A ⇒ Y} → ⟨ f ∘ q , g ∘ q ⟩ ≈ ⟨ f , g ⟩ ∘ q
    ∘-distrib-⟨⟩ {q = q} = unique (assₗ ⨾ project₁ ⋆ₗ q) (assₗ ⨾ project₂ ⋆ₗ q)       