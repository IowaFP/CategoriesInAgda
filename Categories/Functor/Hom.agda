module Categories.Functor.Hom where 

open import Categories.Prelude
open import Categories.Category 
open import Categories.Functor 
open import Categories.NaturalTransformation 
open import Categories.Category.Product
open import Categories.Instances.Setoid
open import Categories.Reasoning.Hom 

-------------------------------------------------------------------------------
-- The hom bifunctor: 

-- For locally-small 𝒞, each object A induces a covariant hom-functor 
--   Hom(A, —) : 𝒞 → Set 
-- that maps objects B ∈ 𝒞 to the hom set of arrows from A to B:
--   Hom(A, B) = { f ∣ f : A ⇒ B } 
-- and maps arrows f : B ⇒ C via pre-composition
--   Hom(A, f) : Hom(A, B) → Hom(A, C) 
--   Hom(A, f)(g : A ⇒ B) = f ∘ g 
-- Dually, each object A in 𝒞 likewise induces a contravariant hom-functor
--   Hom(—, A) : 𝒞ᵒᵖ → Set 
-- such that:
--   Hom(B, A) = { f ∣ f : B ⇒ A } 
-- and, for g : B → C,
--   Hom(g, A) : Hom(C, A) → Hom(B, A)
--   Hom(g, A)(f : C ⇒ A) = f ∘ g 
-- More generally, each hom-functor is a projection from the bi-functor
--   - Hom(—,—) : 𝒞ᵒᵖ × 𝒞 → Set 
--   - Hom(A, B) = { f ∣ f : A ⇒ B} 
-- And for arrows f : A ⇒ B and g : C ⇒ D, 
--   - Hom(f , g) : Hom(B, C) → Hom(A, D)
--   - Hom(f, g)(h : B ⇒ C) = g ∘ h ∘ f
-------------------------------------------------------------------------------

module HomFunctor (𝒞 : Category o a e) where
  open Category 𝒞 
  open Functor
  open HomReasoning 𝒞

  private 
    𝒞ᵒᵖ = op  

  Hom[—,—] :  (𝒞ᵒᵖ × 𝒞) ⇛ (𝐒𝐞𝐭𝐨𝐢𝐝 a e)
  Hom[—,—] .F₀ (A , B) = Hom(A , B)
  Hom[—,—] .fmap {A = A , B} {B = C , D} (f , g) =  
    (λ h → g ∘ h ∘ f) , (_⋆ₗ f) ○ (g ⋆ᵣ_)
  Hom[—,—] .F-id x =  idᵣ ⨾ idₗ 
  Hom[—,—] .F-∘  (f , g) (h , k) i = begin
    k ∘ g ∘ i ∘ (f ∘ h)  ≈⟨ assₗ ⟩ 
    k ∘ g ∘ i ∘ f ∘ h    ≈⟨ (assᵣ ⋆ₗ f) ⋆ₗ h ⟩ 
    k ∘ (g ∘ i) ∘ f ∘ h  ≈⟨ (assₗ ⋆ₗ h) ⁻¹ ⟩ 
    k ∘ (g ∘ i ∘ f) ∘ h ∎ 
  Hom[—,—] .F-cong {f = f₁ , f₂} {g = g₁ , g₂} (f₁≈g₁ , f₂≈g₂) h = 
    begin 
      f₂ ∘ h ∘ f₁ ≈⟨ (f₂≈g₂ ⋆ₗ h) ⋆ f₁≈g₁ ⟩ 
      g₂ ∘ h ∘ g₁ ∎ 

  -- Covariant hom functor 
  Hom[_,—] : Obj → 𝒞 ⇛ (𝐒𝐞𝐭𝐨𝐢𝐝 a e)
  Hom[_,—] A = Bf-π₂ Hom[—,—] A 

  -- Contravariant hom functor
  Hom[—,_] : Obj → 𝒞ᵒᵖ ⇛ (𝐒𝐞𝐭𝐨𝐢𝐝 a e)
  Hom[—,_] A = Bf-π₁ Hom[—,—] A

  -- Hom[—,—] is full
  Hom[—,—]-Full : Full Hom[—,—]
  Hom[—,—]-Full = TODO 

  -- Hom[—,—] is faithful
  Hom[—,—]-Faithful : Faithful Hom[—,—]
  Hom[—,—]-Faithful = TODO

  