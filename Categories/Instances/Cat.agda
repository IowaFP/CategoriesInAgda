{-# OPTIONS --without-K #-}

module Categories.Instances.Cat where 

open import Categories.Prelude hiding (ℓ)
open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Exponential
open import Categories.Functor 
open import Categories.NaturalTransformation

open import Categories.Constructions.Product 
open import Categories.Constructions.Exponential
open import Categories.Reasoning 

--------------------------------------------------------------------------------
-- The Category of Categories  
module _ o a e where 
  open Category  
  private 
    ℓ = o ⊔ a ⊔ e 

  𝐂𝐚𝐭 : Category (lsuc ℓ) ℓ ℓ 
  𝐂𝐚𝐭 .Obj = Category o a e 
  𝐂𝐚𝐭 ._⇒_ 𝒞 𝒟 =  𝒞 ⇛ 𝒟
  𝐂𝐚𝐭 ._∘_ = _∘F_
  𝐂𝐚𝐭 .Id = IdF 
  𝐂𝐚𝐭 ._≈_ {𝒞} {𝒟} F G =  F ≃ₙ G
  𝐂𝐚𝐭 .eqv {A = 𝒞} {B = 𝒟}  = Fun(𝒞 , 𝒟) .Setoid.isEquivalence
  𝐂𝐚𝐭 ._⋆_ {A = A} {B} {C} {f = F} {H} {G} {I} η₁ η₂ = H-iso η₂ η₁
  𝐂𝐚𝐭 .idᵣ =  IdF-idᵣ  
  𝐂𝐚𝐭 .idₗ = IdF-idₗ   
  𝐂𝐚𝐭 .assₗ {f = F} {G} {H} = Functor-assₗ F G H 
 
--------------------------------------------------------------------------------
-- The product of categories are products in 𝐂𝐚𝐭
module _ o a e where 

  
  𝐂𝐚𝐭Products : AdmitsProducts (𝐂𝐚𝐭 o a e) 
  𝐂𝐚𝐭Products .AdmitsProducts._×_ = _×_
  𝐂𝐚𝐭Products .AdmitsProducts.`π₁ = π¹
  𝐂𝐚𝐭Products .AdmitsProducts.`π₂ = π²
  𝐂𝐚𝐭Products .AdmitsProducts.⟨_,_⟩ = ⟨_,_⟩
  𝐂𝐚𝐭Products .AdmitsProducts.project₁ {A} {B} {f = F} {g = G} .nat = Id , λ _ → idᵣ ⨾ idₗ ⁻¹
    where open Category B
  𝐂𝐚𝐭Products .AdmitsProducts.project₁ {A} {B} {f = F} .iso = Id , Id⁻¹ B
    where open Category B 
  𝐂𝐚𝐭Products .AdmitsProducts.project₂ {A} {B} {C} {f = F} {g = G} .nat = Id , λ _ → idᵣ ⨾ idₗ ⁻¹
    where open Category C 
  𝐂𝐚𝐭Products .AdmitsProducts.project₂ {A} {B} {C} {f = F} .iso = Id , Id⁻¹ C
    where open Category C 
  𝐂𝐚𝐭Products .AdmitsProducts.unique {f = F} {G} {H} π₁∘f π₂∘f = ⟨⟩-unique G H F π₁∘f π₂∘f

-------------------------------------------------------------------------
-- Functor categories are exponentials in 𝐂𝐚𝐭 
-- N.b. we have to be a bit careful with what we are asserting because of 
-- levels. Functor records quantify over objects, arrows, and equivalences,
-- hence if (𝒞 𝒟 : Category o a e), we have:
--   𝒞 ⇛ 𝒟 : Set (o ⊔ a ⊔ e) 
-- Correspondingly, functor categories have type
--   [ 𝒞 , 𝒟 ] : Category (o ⊔ a ⊔ e) (o ⊔ a ⊔ e) (o ⊔ a ⊔ e).
-- So it is a bit incorrect to assert that "the category of categories admits
-- exponentials", as we have a stratification of category categories. Explicitly,
-- we have that the category of categories with objects, arrows, and equivalences
-- *at level (o ⊔ a ⊔ e)* admits exponentials.

module _ o a e where 
  private 
    ℓ = o ⊔ a ⊔ e 

  open AdmitsProducts (𝐂𝐚𝐭Products ℓ ℓ ℓ) hiding (_×_)
  
  𝐂𝐚𝐭Exponentials : AdmitsExponentials 
    (𝐂𝐚𝐭 ℓ ℓ ℓ) 
    (𝐂𝐚𝐭Products ℓ ℓ ℓ)
  𝐂𝐚𝐭Exponentials .AdmitsExponentials._^_ X Y = [ Y , X ]
  𝐂𝐚𝐭Exponentials .AdmitsExponentials.`eval {Z} {Y} = eval Y Z
  𝐂𝐚𝐭Exponentials .AdmitsExponentials.`curry = λ[_]
  𝐂𝐚𝐭Exponentials .AdmitsExponentials.`transpose = TODO 
  𝐂𝐚𝐭Exponentials .AdmitsExponentials.`unique = TODO 