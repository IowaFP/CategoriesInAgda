{-# OPTIONS --without-K #-}

module Categories.Instances.Cat where 

open import Categories.Prelude
open import Categories.Category
open import Categories.Functor 
open import Categories.NaturalTransformation

--------------------------------------------------------------------------------
-- The Category of Categories  
module _ where 
  open Category  
  𝐂𝐚𝐭 : ∀ (o a e : Level) → Category (lsuc (o ⊔ a ⊔ e)) (lsuc o ⊔ a ⊔ e) (o ⊔ a ⊔ e) 
  𝐂𝐚𝐭 o a e .Obj = Category o a e
  𝐂𝐚𝐭 o a e ._⇒_ 𝒞 𝒟 =  Functor 𝒞 𝒟
  𝐂𝐚𝐭 o a e ._∘_ = _∘F_
  𝐂𝐚𝐭 o a e .Id = IdF 
  𝐂𝐚𝐭 o a e ._≈_ {𝒞} {𝒟} F G =  F ≃ₙ G
  𝐂𝐚𝐭 o a e .eqv  = nat-setoid .Setoid.isEquivalence
  𝐂𝐚𝐭 o a e .cong-∘ {A = A} {B} {C} {f = F} {H} {G} {I} η₁ η₂ = H-iso η₂ η₁
  𝐂𝐚𝐭 o a e .idᵣ =  IdF-idᵣ  
  𝐂𝐚𝐭 o a e .idₗ = IdF-idₗ   
  𝐂𝐚𝐭 o a e .assₗ {f = F} {G} {H} = Functor-assₗ F G H 
 
--------------------------------------------------------------------------------
-- 𝐂𝐚𝐭 admits products

module _ {o a e} where 
  open import Categories.Category.Product renaming (_×_ to _⊗_ ; ⟨_,_⟩ to ⟨_∶_⟩)
  open import Categories.Constructions.Product 
  open hasProduct  
  open AdmitsProducts 
  
  𝐂𝐚𝐭Products : AdmitsProducts (𝐂𝐚𝐭 o a e) 
  𝐂𝐚𝐭Products .products X Y .X₁×X₂ = X ⊗ Y
  𝐂𝐚𝐭Products .products X Y .`π₁ = π¹
  𝐂𝐚𝐭Products .products X Y .`π₂ = π²
  𝐂𝐚𝐭Products .products X Y .⟨_⨾_⟩ = ⟨_∶_⟩
  𝐂𝐚𝐭Products .products X Y .project₁ .nat = Id , λ _ → idᵣ ⨾ sym-≈ idₗ
    where open Category X 
  𝐂𝐚𝐭Products .products X Y .project₁ .iso = Id , idₗ , idₗ
    where open Category X 
  𝐂𝐚𝐭Products .products X Y .project₂ .nat = Id , λ _ → idᵣ ⨾ sym-≈ idₗ
    where open Category Y 
  𝐂𝐚𝐭Products .products X Y .project₂ .iso = Id , idₗ , idₗ
    where open Category Y 
  𝐂𝐚𝐭Products .products X Y .unique {f = F} {G} {H} π₁∘f π₂∘f = ⟨⟩-unique G H F π₁∘f π₂∘f
    where 
      module X = Category X ; module Y = Category Y
