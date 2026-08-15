{-# OPTIONS --without-K #-}

module Categories.Category.Arrows where 

open import Categories.Prelude 
open import Categories.Category.Base
open import Categories.Reasoning.Hom

--------------------------------------------------------------------------------
-- Types of arrows

module _ (𝒞 : Category o a e) where 
  open Category 𝒞 
  open HomReasoning 𝒞 
  private
    variable 
      A B C : Obj 

  record areInverse (f : A ⇒ B) (g : B ⇒ A) : Set (o ⊔ a ⊔ e) where 
    constructor _,_
    field
      linv : f ∘ g ≈ Id
      rinv : g ∘ f ≈ Id  

  open areInverse public

  record isIso (f : A ⇒ B) : Set (o ⊔ a ⊔ e) where 
    constructor _,_  
    field
      ∼  : B ⇒ A 
      iso : areInverse f ∼
 
  open isIso public

  -- A section is a right inverse, or, equivalently,
  -- a section is an arrow that *has* a left inverse.  
  -- The left inverse is called a retraction.
  record isSection (f : A ⇒ B) : Set (o ⊔ a ⊔ e) where
      constructor _,_ 
      field 
        ∼   : B ⇒ A 
        rinv : ∼ ∘ f ≈ Id

  open isSection public

  -- ---------------------------------
  -- Because I can never remember this:
  -- - A section    *s*elects an A 
  -- - A retraction *r*eturns a  B
  -- ---------------------------------

  -- A retraction is a left inverse, or, equivalently,
  -- a retraction is a function that *has* a right inverse.  
  -- The right inverse is called a section.
  record isRetraction (f : A ⇒ B) : Set (o ⊔ a ⊔ e) where 
      constructor _,_
      field 
        ∼   : B ⇒ A 
        linv : f ∘ ∼ ≈ Id

  open isRetraction public

  record isEpi (f : A ⇒ B) : Set (o ⊔ a ⊔ e) where 
    constructor Epi 
    field
      epi : ∀ (g₁ g₂ : B ⇒ A) → g₁ ∘ f ≈ g₂ ∘ f → g₁ ≈ g₂

  open isEpi public 

  record isMono (f : A ⇒ B) : Set (o ⊔ a ⊔ e) where 
    constructor Mono 
    field
      mono : ∀ (g₁ g₂ : B ⇒ A) → f ∘ g₁ ≈ f ∘ g₂ → g₁ ≈ g₂

  open isMono public 

--------------------------------------------------------------------------------
-- Some basic results on arrows

  -- The identity is its own inverse.
  -- N.b., we can prove this with idₗ or idᵣ,
  -- so the identity as its own inverse is not contractible.
  -- This can cause problems e.g. when equating natural isomorphisms.
  Id⁻¹ : areInverse (Id {A}) Id 
  Id⁻¹ = idₗ , idₗ 


  -- Every section is a monomorphism
  section⇒mono : (f : A ⇒ B) → isSection f → isMono f 
  section⇒mono f (g , rinv) = Mono (λ g₁ g₂ eq → begin 
      g₁         ≈⟨ idₗ ⁻¹ ⨾ (rinv ⋆ₗ g₁) ⁻¹ ⟩
      g ∘ f ∘ g₁ ≈⟨ assᵣ ⨾ g ⋆ᵣ eq ⨾ assₗ ⟩ 
      g ∘ f ∘ g₂ ≈⟨ rinv ⋆ₗ g₂ ⨾ idₗ ⟩         
      g₂ ∎)
  
  -- Every retraction is an epimorphism
  retraction⇒epi : (f : A ⇒ B) → isRetraction f → isEpi f 
  retraction⇒epi f (g , linv) = Epi (λ g₁ g₂ eq → begin 
      g₁         ≈⟨ (idᵣ ⁻¹ ⨾ (_ ⋆ᵣ linv) ⁻¹ ⨾ assₗ) ⟩ 
      g₁ ∘ f ∘ g ≈⟨ eq ⋆ₗ _ ⟩ 
      g₂ ∘ f ∘ g ≈⟨ (assᵣ ⨾  _ ⋆ᵣ linv ⨾ idᵣ) ⟩ 
      g₂ ∎)
  
  -- Trivially, every isomorphism is both a section & retraction
  iso⇒section : (f : A ⇒ B) → isIso f → isSection f 
  iso⇒section f (g , iso) .∼ = g
  iso⇒section f (g , iso) .rinv = iso .rinv 

  iso⇒retraction : (f : A ⇒ B) → isIso f → isRetraction f 
  iso⇒retraction f (g , iso) .∼ = g
  iso⇒retraction f (g , iso) .linv = iso .linv 

--------------------------------------------------------------------------------
-- Isomorphic relation 

module Isomorphism (𝒞 : Category o a e) where 
  open Category 𝒞 
  open HomReasoning 𝒞 

  record _≃_ (A B : Obj) : Set (o ⊔ a ⊔ e) where 
    constructor _,_
    field 
      morph   : A ⇒ B
      iso : isIso 𝒞 morph

  open _≃_ public 

  private
    variable 
      A B C : Obj 

  refl-≃ : A ≃ A 
  refl-≃ = Id , Id , idᵣ , idᵣ

  sym-≃ : A ≃ B → B ≃ A 
  sym-≃ (f , g , linv , rinv) = g , f , rinv , linv

  trans-≃ : A ≃ B → B ≃ C → A ≃ C 
  trans-≃ (f , g , linv-f , rinv-f) 
          (h , j , linv-h , rinv-h) = 
      h ∘ f , g ∘ j , 
      (begin 
          (h ∘ f ∘ (g ∘ j)) ≈⟨ assₗ ⟩ 
          (h ∘ f ∘ g ∘ j) ≈⟨ (assᵣ ⨾ _ ⋆ᵣ linv-f) ⋆ₗ _ ⟩ 
          (h ∘ Id ∘ j) ≈⟨ assᵣ ⨾ _ ⋆ᵣ idₗ ⟩ 
          (h ∘ j) ≈⟨ linv-h ⟩ 
          Id ∎) ,  
      (begin 
          (g ∘ j ∘ (h ∘ f)) ≈⟨ assₗ ⟩ 
          (g ∘ j ∘ h ∘ f) ≈⟨ (assᵣ ⨾ _ ⋆ᵣ rinv-h) ⋆ₗ _ ⟩ 
          (g ∘ Id ∘ f) ≈⟨ (assᵣ ⨾ _ ⋆ᵣ idₗ) ⟩ 
          (g ∘ f) ≈⟨ rinv-f ⟩ 
          Id ∎) 
  
  Objs : Setoid o (o ⊔ a ⊔ e)
  Objs = record
    { Carrier       = Obj
    ; _≈_           = _≃_
    ; isEquivalence = record { refl = refl-≃ ; sym = sym-≃ ; trans = trans-≃ }
    }

--------------------------------------------------------------------------------
-- ` Syntax (when you want to open two instantiations of Isomorphism)

module `Isomorphism (𝒞 : Category o a e) where 
  open Isomorphism 𝒞 
    renaming (_≃_ to _`≃_ ; 
              refl-≃ to `refl-≃ ; 
              sym-≃ to `sym-≃ ; 
              trans-≃ to `trans-≃ ; 
              Objs to `Objs) public 

-- Accessor for isomorphism when category is unopened
_[_≃_] : (𝒞 : Category o a e) → (A B : 𝒞 .Category.Obj) → Set (o ⊔ a ⊔ e)
𝒞 [ A ≃ B ] = Isomorphism._≃_ 𝒞 A B
