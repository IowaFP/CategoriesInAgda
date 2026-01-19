{-# OPTIONS --without-K #-}

module Categories.Instances.Cat where 

open import Categories.Prelude hiding (ℓ)
open import Categories.Category
open import Categories.Category.Product renaming (⟨_,_⟩ to ⟨_∶_⟩)
open import Categories.Functor 
open import Categories.NaturalTransformation

open import Categories.Constructions.Product 
open import Categories.Constructions.Exponential
open import Categories.Instances.Functor
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
  𝐂𝐚𝐭 .eqv  = nat-setoid .Setoid.isEquivalence
  𝐂𝐚𝐭 ._⋆_ {A = A} {B} {C} {f = F} {H} {G} {I} η₁ η₂ = H-iso η₂ η₁
  𝐂𝐚𝐭 .idᵣ =  IdF-idᵣ  
  𝐂𝐚𝐭 .idₗ = IdF-idₗ   
  𝐂𝐚𝐭 .assₗ {f = F} {G} {H} = Functor-assₗ F G H 
 
--------------------------------------------------------------------------------
-- The product of categories are products in 𝐂𝐚𝐭
module _ o a e where 

  open hasProduct 
  open AdmitsProducts hiding (_×_)
  
  𝐂𝐚𝐭Products : AdmitsProducts (𝐂𝐚𝐭 o a e) 
  𝐂𝐚𝐭Products .products X Y .X₁×X₂ = X × Y
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
  open hasExponential
  open AdmitsExponentials
  

  𝐂𝐚𝐭Exponentials : AdmitsExponentials 
    (𝐂𝐚𝐭 ℓ ℓ ℓ) 
    (𝐂𝐚𝐭Products ℓ ℓ ℓ)
  𝐂𝐚𝐭Exponentials .exponentials 𝒞 𝒟 .Zʸ = [ 𝒟 , 𝒞 ] 
  -- We build: Functor ([ 𝒟 , 𝒞 ] × 𝒟) 𝒞
  𝐂𝐚𝐭Exponentials .exponentials 𝒞 𝒟 .`eval .Functor.F₀ (F , A) = F₀ A
    where open Functor F 
  𝐂𝐚𝐭Exponentials .exponentials 𝒞 𝒟 .`eval .Functor.fmap 
    {A = F , A} {B = G , B} ((η , naturality) , f) = gmap f ∘ η
    where open Category 𝒞 ; open Gunctor G 
  𝐂𝐚𝐭Exponentials .exponentials 𝒞 𝒟 .`eval .Functor.F-id {F , A} = F-id ⋆ₗ Id ⨾ idₗ
    where open Category 𝒞 ; open Functor F 
  𝐂𝐚𝐭Exponentials .exponentials 𝒞 𝒟 .`eval .Functor.F-∘ 
    {A = F , A} {B = G , B} {C = H , C} 
    ((η , nat-η) , f) ((ε , nat-ε) , g) = begin
      hmap (g `∘ f) ∘ (ε ∘ η)   ≈⟨ H-∘ f g ⋆ₗ (ε ∘ η) ⟩ 
      hmap g ∘ hmap f ∘ (ε ∘ η) ≈⟨ assₗ ⨾ assᵣ ⋆ₗ η ⟩ 
      hmap g ∘ (hmap f ∘ ε) ∘ η ≈⟨ hmap g ⋆ᵣ (nat-ε f) ⋆ₗ η ⟩ 
      hmap g ∘ (ε ∘ gmap f) ∘ η ≈⟨ assₗ ⋆ₗ η ⨾ assᵣ ⟩ 
      hmap g ∘ ε ∘ (gmap f ∘ η) ∎ 
    where 
      open HomReasoning 𝒞 
      open Category 𝒞 ; open `Category 𝒟 
      open Functor F ; open Gunctor G ; open Hunctor H 
  𝐂𝐚𝐭Exponentials .exponentials 𝒞 𝒟 .`eval .Functor.F-cong = {!   !} 
  𝐂𝐚𝐭Exponentials .exponentials 𝒞 𝒟 .`λ[_] {X = X}  = TODO ((X × 𝒟) ⇛ 𝒞 → X ⇛ ([ 𝒟 , 𝒞 ]))
  𝐂𝐚𝐭Exponentials .exponentials 𝒞 𝒟 .`transpose = TODO _ 
  𝐂𝐚𝐭Exponentials .exponentials 𝒞 𝒟 .`unique = TODO _ 