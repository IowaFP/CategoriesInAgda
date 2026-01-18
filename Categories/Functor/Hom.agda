module Categories.Functor.Hom where 

open import Categories.Prelude
open import Categories.Category 
open import Categories.Functor 
open import Categories.NaturalTransformation 
open import Categories.Category.Product
open import Categories.Instances.Setoids
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
  Hom[_][—,—] .F-id x =  idᵣ ⨾ idₗ 
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
  Hom[_][_,—] A = Bf-π₂ Hom[_][—,—] A 

  -- Contravariant hom functor
  Hom[_][—,_] : Obj → Functor 𝒞ᵒᵖ (Setoids o e)
  Hom[_][—,_] A = Bf-π₁ Hom[_][—,—] A
  