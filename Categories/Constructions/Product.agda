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

  record hasProduct (X₁ X₂ : Obj) : Set (o ⊔ e ⊔ a) where 
    field 
      X₁×X₂ : Obj 
      `π₁  : X₁×X₂ ⇒ X₁ 
      `π₂ : X₁×X₂  ⇒ X₂ 
      ⟨_⨾_⟩ : Y ⇒ X₁ → Y ⇒ X₂ → Y ⇒ X₁×X₂ 

      project₁ : `π₁ ∘ ⟨ f ⨾ g ⟩ ≈ f 
      project₂ : `π₂ ∘ ⟨ f ⨾ g ⟩ ≈ g 
      unique : `π₁ ∘ f ≈ g → `π₂ ∘ f ≈ h → ⟨ g ⨾ h ⟩ ≈ f  
  
    ×-g-η : ⟨ `π₁ ∘ f ⨾ `π₂ ∘ f ⟩ ≈ f 
    ×-g-η = unique refl-≈ refl-≈ 

    ×-η : ⟨ `π₁ ⨾ `π₂ ⟩ ≈ Id
    ×-η = unique idᵣ idᵣ 

    ∘-distrib-⟨⟩ : ∀ {q : A ⇒ Y} → ⟨ f ∘ q ⨾ g ∘ q ⟩ ≈ ⟨ f ⨾ g ⟩ ∘ q
    ∘-distrib-⟨⟩ = unique (assₗ ⨾ cong-∘ₗ project₁) (assₗ ⨾ cong-∘ₗ project₂) 

  -- A category admits products if every two objects has a product 
  record AdmitsProducts : Set (o ⊔ e ⊔ a) where 
    constructor admitsProducts
    open hasProduct public
    field 
      products : ∀ (X Y : Obj) → hasProduct X Y 

    -- Re-exporting friendly accessors
    _×_ : ∀ (A B : Obj) → Obj 
    A × B = products A B .X₁×X₂ 
    ⟨_,_⟩ : ∀ (f : A ⇒ B) (g : A ⇒ C) → A ⇒ B × C
    ⟨ f , g ⟩ = products _ _ .⟨_⨾_⟩ f g 

    π₁ : A × B ⇒ A 
    π₁ {A = A} {B} = products A B .`π₁ 

    π₂ : A × B ⇒ B
    π₂ {A = A} {B} = products A B .`π₂  

    ⟪_,_⟫ : ∀ (f : A ⇒ X) (g : B ⇒ Y) → A × B ⇒ X × Y 
    ⟪ f , g ⟫ = ⟨ f ∘ π₁ , g ∘ π₂ ⟩
