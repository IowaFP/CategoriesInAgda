module Categories.Functor.Hom where 

open import Categories.Prelude
open import Categories.Category 
open import Categories.Functor 
open import Categories.NaturalTransformation 
open import Categories.Category.Product
open import Categories.Instances.Setoids
open import Categories.Reasoning.Hom 

-------------------------------------------------------------------------------
-- The hom bifunctor

module _ (𝒞 : Category a o e) where
  open Category 𝒞 
  open Functor
  open HomReasoning 𝒞

  private 
    𝒞ᵒᵖ = op  

  Hom[_][—,—] :  Functor (𝒞ᵒᵖ × 𝒞) (Setoids o e)
  Hom[_][—,—] .F₀ (A , B) = hom-setoid A B 
  Hom[_][—,—] .fmap {A = A , B} {B = C , D} (f , g) =  
    (λ h → g ∘ h ∘ f) , cong-∘ₗ ○ cong-∘ᵣ
  Hom[_][—,—] .F-id x =  right-id ⨾ left-id 
  Hom[_][—,—] .F-∘  (f , g) (h , k) i = begin
    k ∘ g ∘ i ∘ (f ∘ h)  ≈⟨ assₗ ⟩ 
    k ∘ g ∘ i ∘ f ∘ h    ≈⟨ cong-∘ₗ (cong-∘ₗ assᵣ) ⟩ 
    k ∘ (g ∘ i) ∘ f ∘ h  ≈⟨ sym-≈ (cong-∘ₗ assₗ) ⟩ 
    k ∘ (g ∘ i ∘ f) ∘ h ∎ 
  Hom[_][—,—] .F-cong {f = f₁ , f₂} {g = g₁ , g₂} (f₁≈g₁ , f₂≈g₂) h = 
    begin 
      f₂ ∘ h ∘ f₁ ≈⟨ cong-∘ (cong-∘ₗ f₂≈g₂) f₁≈g₁ ⟩ 
      g₂ ∘ h ∘ g₁ ∎ 

  -- Covariant hom functor 
  Hom[_][_,—] : Obj → Functor 𝒞 (Setoids o e)
  Hom[_][_,—] A = BFPrj₂ Hom[_][—,—] A 

  -- Contravariant hom functor
  Hom[_][—,_] : Obj → Functor 𝒞ᵒᵖ (Setoids o e)
  Hom[_][—,_] A = BFPrj₁ Hom[_][—,—] A
  