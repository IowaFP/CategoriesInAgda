{-# OPTIONS --without-K #-}

module Categories.Instances.Cats where 

open import Categories.Prelude
open import Categories.Category
open import Categories.Functor 
open import Categories.NaturalTransformation

--------------------------------------------------------------------------------
-- The Category of Categories  
module _ where 
  open Category 
  Cats : ∀ (o a e : Level) → Category (lsuc (o ⊔ a ⊔ e)) (lsuc o ⊔ a ⊔ e) (o ⊔ a ⊔ e) 
  Cats o a e .Obj = Category o a e
  Cats o a e ._⇒_ 𝒞 𝒟 =  Functor 𝒞 𝒟
  Cats o a e ._∘_ = _∘F_
  Cats o a e .Id = IdF 
  Cats o a e ._≈_ {𝒞} {𝒟} F G =  F ≃ₙ G
  Cats o a e .eqv  = nat-setoid .Setoid.isEquivalence
  Cats o a e .cong-∘ {A = A} {B} {C} {f = F} {H} {G} {I} η₁ η₂ = H-iso η₂ η₁
  Cats o a e .idᵣ =  IdF-idᵣ  
  Cats o a e .idₗ = IdF-idₗ   
  Cats o a e .assₗ {f = F} {G} {H} = Functor-assₗ F G H 
 
--------------------------------------------------------------------------------
-- Cats admits products

module _ {o a e} where 
  open import Categories.Category.Product renaming (_×_ to _⊗_ ; ⟨_,_⟩ to ⟨_∶_⟩)
  open import Categories.Constructions.Product 
  open hasProduct  
  open AdmitsProducts 
  
  CatsProducts : AdmitsProducts (Cats o a e) 
  CatsProducts .products X Y .X₁×X₂ = X ⊗ Y
  CatsProducts .products X Y .`π₁ = π¹
  CatsProducts .products X Y .`π₂ = π²
  CatsProducts .products X Y .⟨_⨾_⟩ = ⟨_∶_⟩
  CatsProducts .products X Y .project₁ .nat = Id , λ _ → idᵣ ⨾ sym-≈ idₗ
    where open Category X 
  CatsProducts .products X Y .project₁ .iso = Id , idₗ , idₗ
    where open Category X 
  CatsProducts .products X Y .project₂ .nat = Id , λ _ → idᵣ ⨾ sym-≈ idₗ
    where open Category Y 
  CatsProducts .products X Y .project₂ .iso = Id , idₗ , idₗ
    where open Category Y 
  CatsProducts .products X Y .unique {f = F} {G} {H} π₁∘f π₂∘f = ⟨⟩-unique G H F π₁∘f π₂∘f
    where 
      module X = Category X ; module Y = Category Y
