{-# OPTIONS --without-K #-}

module Categories.Constructions.Coproduct where 

open import Categories.Prelude
open import Categories.Category
open import Categories.Constructions.Product

-- ------------------------------------------------------------------------------
-- Coproducts 

module _ (𝒞 : Category o a e) where 
  open Category 𝒞 

  private 
    variable
      A B C Y : Obj 
      f g h : A ⇒ B 

  record hasCoproduct (X₁ X₂ : Obj) : Set (o ⊔ e ⊔ a) where 
    field 
      X₁+X₂ : Obj 
      ι₁ : X₁ ⇒ X₁+X₂
      ι₂ : X₂ ⇒ X₁+X₂
      [_,_] : X₁ ⇒ Y → X₂ ⇒ Y → X₁+X₂ ⇒ Y

      inject₁ : [ f , g ] ∘ ι₁ ≈ f 
      inject₂ : [ f , g ] ∘ ι₂ ≈ g 
      unique : f ∘ ι₁ ≈ g → f ∘ ι₂ ≈ h → [ g , h ] ≈ f  
  
    +-g-η : [ f ∘ ι₁ , f ∘ ι₂ ] ≈ f 
    +-g-η = unique refl-≈ refl-≈ 

    +-η : [ ι₁ , ι₂ ] ≈ Id
    +-η = unique idₗ idₗ 

  -- A category admits coproducts if every two objects has a coproduct
  record AdmitsCoproducts : Set (o ⊔ e ⊔ a) where 
    constructor admitsCoproducts
    open hasCoproduct public
    field 
      coproducts : ∀ (X Y : Obj) → hasCoproduct X Y 

    _+_ : ∀ (A B : Obj) → Obj 
    A + B = coproducts A B .X₁+X₂

-- ------------------------------------------------------------------------------
-- Products and coproducts are dual

module _ (𝒞 : Category o a e) where 
  open Category 𝒞 ; private Cᵒᵖ = op 
  open AdmitsCoproducts using (coproducts)

  Productsᵒᵖ≡Coproducts : AdmitsProducts 𝒞 → AdmitsCoproducts Cᵒᵖ 
  Productsᵒᵖ≡Coproducts (admitsProducts products) .coproducts X Y = record
    { X₁+X₂ = X × Y
    ; ι₁ = `π₁
    ; ι₂ = `π₂
    ; [_,_] = ⟨_⨾_⟩
    ; inject₁ = project₁
    ; inject₂ = project₂
    ; unique = unique
    }
    where 
      open AdmitsProducts (admitsProducts products) using (_×_)
      open hasProduct (products X Y)