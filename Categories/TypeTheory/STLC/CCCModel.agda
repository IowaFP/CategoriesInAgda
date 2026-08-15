
module Categories.TypeTheory.STLC.CCCModel where

open import Categories.Prelude
open import Categories.Category
open import Categories.Constructions.Exponential 
open import Categories.Constructions.Product
open import Categories.Constructions.Terminal
open import Categories.TypeTheory.STLC.Syntax

-------------------------------------------------------------------------------
-- Modeling the STLC into CCC's

module CCC {a o e} 
  (𝒞 : Category o a e) 
  (products : AdmitsProducts 𝒞) 
  (exponentials : AdmitsExponentials 𝒞 products)
  (⊤ : 𝒞 .Category.Obj) 
  (term : isTerminal 𝒞 ⊤)  where 

  open Category 𝒞 
  open AdmitsProducts products 
  open AdmitsExponentials exponentials
  open isTerminal term 

  ⟦_⟧t : Type → Obj 
  ⟦ τ₁ `→ τ₂ ⟧t = ⟦ τ₂ ⟧t ^ ⟦ τ₁ ⟧t 
  ⟦ `⊤ ⟧t = ⊤
  ⟦ τ₁ `× τ₂ ⟧t = ⟦ τ₁ ⟧t × ⟦ τ₂ ⟧t   
 
  ⟦_⟧ctx : Context → Obj 
  ⟦ ∅ ⟧ctx = ⊤
  ⟦ Γ , x ⟧ctx = ⟦ Γ ⟧ctx × ⟦ x ⟧t

  ⟦_⟧v : Var Γ τ → ⟦ Γ ⟧ctx ⇒ ⟦ τ ⟧t
  ⟦ `0 ⟧v = `π₂ 
  ⟦ `S x ⟧v = ⟦ x ⟧v ∘ `π₁

  ⟦_⟧ : Term Γ τ → ⟦ Γ ⟧ctx ⇒ ⟦ τ ⟧t 
  ⟦ ` x ⟧ = ⟦ x ⟧v
  ⟦ `λ {τ = τ} M ⟧ = `curry ⟦ M ⟧ 
  ⟦ M · N ⟧  = `eval ∘ ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩ 
  ⟦ fst M ⟧ = `π₁ ∘ ⟦ M ⟧
  ⟦ snd M ⟧ = `π₂ ∘ ⟦ M ⟧
  ⟦_⟧ {Γ = Γ} ⋆ = ! ⟦ Γ ⟧ctx 
  ⟦ M , N ⟧ = ⟨ ⟦ M ⟧ , ⟦ N ⟧ ⟩ 

-------------------------------------------------------------------------------
-- Recovering the Set model! 

module SetModel (ℓ : Level) where 
  open import Categories.Instances.Set 
  open PropositionalEquality
  open import Categories.Prelude.Equality.Heterogeneous
  open HeterogeneousEquality

  open Category (𝐒𝐞𝐭 lzero)
  open AdmitsProducts  (𝐒𝐞𝐭Products lzero)
  open AdmitsExponentials (𝐒𝐞𝐭Exponentials lzero)
  open isTerminal {a = lzero} SetTerminal

  open CCC (𝐒𝐞𝐭 lzero) (𝐒𝐞𝐭Products lzero) (𝐒𝐞𝐭Exponentials lzero) ⊤ SetTerminal
    renaming 
      (⟦_⟧t to ⟦_⟧₀t ; 
       ⟦_⟧v to ⟦_⟧₀v ; 
       ⟦_⟧ctx to ⟦_⟧₀ctx ; 
       ⟦_⟧ to ⟦_⟧₀) 


  open import Categories.TypeTheory.STLC.SetModel 
    renaming 
      (⟦_⟧t to ⟦_⟧₁t ; 
       ⟦_⟧v to ⟦_⟧₁v ; 
       ⟦_⟧ctx to ⟦_⟧₁ctx ; 
       ⟦_⟧ to ⟦_⟧₁)   

  -- Asserting that the construction in STLC.SetModel is identical.
  -- AH> Don't understand why normalizing the term 
  --       ⟦ τ ⟧₀t 
  --     affixes all the CCC nonsense:
  --       (CCC.⟦ 𝐒𝐞𝐭 lzero ⟧t (𝐒𝐞𝐭Products lzero)
  --       (𝐒𝐞𝐭Exponentials lzero) (Level.Lift lzero Agda.Builtin.Unit.⊤)
  --       (term (λ _ _ → Level.lift Agda.Builtin.Unit.tt) (λ f a → refl)) τ
  -- I want it to normalize to ⟦ τ ⟧₀t!!!
  same-types : ∀ (τ : Type) → ⟦ τ ⟧₀t ≡ ⟦ τ ⟧₁t 
  same-types (τ `→ τ₁) = {! same-types τ   !}
  same-types `⊤ = {! refl  !}
  same-types (τ `× τ₁) = {!   !} 
  
  same-terms : ∀ (M : Term Γ τ) 
           (H₀ : ⟦ Γ ⟧₀ctx)
           (H₁ : ⟦ Γ ⟧₁ctx) → 
           ((x : Var Γ τ) → ⟦ x ⟧₀v H₀ ≅ ⟦ x ⟧₁v H₁) → 
           ⟦ M ⟧₀ H₀ ≅ ⟦ M ⟧₁ H₁ 
  same-terms = {!   !} 

