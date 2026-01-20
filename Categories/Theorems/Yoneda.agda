-------------------------------------------------------------------------------
-- The Yoneda Lemma
-- 
-- Reading:
-- - https://homotopytypetheory.org/2012/05/02/a-type-theoretical-yoneda-lemma/
-- - https://math.uchicago.edu/~may/REU2022/REUPapers/Stern.pdf
-- 
-- See Categories.Functor.Hom for a description of hom-functors
-------------------------------------------------------------------------------

open import Categories.Prelude
open import Categories.Category 

module Categories.Theorems.Yoneda (𝒞 : Category a o e) where 

open import Categories.Prelude.Functions
open import Categories.Functor 
open import Categories.Functor.Hom
open import Categories.NaturalTransformation 

open import Categories.Category.Product

open import Categories.Instances.Setoid
open import Categories.Category.Exponential 

open import Categories.Reasoning.Hom 

open Category 𝒞
private 
  𝒞ᵒᵖ = op 
  variable 
    A B C : Obj 
open HomFunctor 𝒞 
open Functions₂ 

-------------------------------------------------------------------------------
-- The covariant Yoneda lemma:
-- 
-- For locally small 𝒞 and functor F : 𝒞 → Set, the set 
-- of natural transformations from Hom(A,—) to F, denoted
--   Nat(Hom(A,—), F) 
-- is isomorphic to F(A). Formally:
--   Nat(Hom(A,—), F) ≃ F(A)
-- where _≃_ denotes a bijection between sets.

module CovariantYoneda (F : 𝒞 ⇛ 𝐒𝐞𝐭𝐨𝐢𝐝 o e) where
  open Functor F ; open _⇒ₛ_ 
  import Relation.Binary.Reasoning.Setoid as SetoidReasoning

  -- Mapping natural transformations to terms in F A 
  Yoneda→ : ∀ A → Hom[ A ,—] ⇒ₙ F → ∣ F₀ A ∣
  Yoneda→ A (η , η-nat) = η {A} · Id

  -- Mapping terms in F A to natural transformations
  ←Yoneda : ∀ A → ∣ F₀ A ∣ → Hom[ A ,—] ⇒ₙ F
  ←Yoneda A X = ε , natural 
    where    
      ε : ∀ {B} → Hom(A , B) ⇒ₛ F₀ B 
      ε = (_· X) ○ fmap  , (_$ X) ○ F-cong
      natural : Natural Hom[ A ,—] F ε
      natural {A = B} {C} f g = begin 
        fmap f · (fmap g · X) ≈⟨ sym (F-∘ g f X) ⟩ 
        fmap (f ∘ g) · X      ≈⟨ F-cong (idᵣ ⁻¹) X ⟩ 
        fmap (f ∘ g ∘ Id) · X ∎ 
        where 
          open Setoid (F₀ C) 
          open SetoidReasoning (F₀ C)
    
  -- The mappings Yoneda→ and ←Yoneda are mutually inverse,
  -- and so the setoid Nat(Hom(A, —), F) and (F A) are 
  -- isomorphic. 
  -- An aside: it would be neat if we could express
  -- this instead as "Nat(Hom(A, —), F) and F A are isomorphic
  -- objects in the category 𝐒𝐞𝐭𝐨𝐢𝐝", but the two setoids' levels
  -- are incompatible: (F₀ A) is an object in 
  --   𝐒𝐞𝐭𝐨𝐢𝐝 o e, 
  -- whereas Nat(Hom(A, —), F) is an object in 
  --   𝐒𝐞𝐭𝐨𝐢𝐝 (a ⊔ lsuc o ⊔ lsuc e) (a ⊔ o ⊔ e).
  Yoneda : ∀ A → Nat(Hom[ A ,—] , F) ≅ F₀ A
  Yoneda A = Yoneda→ A , ←Yoneda A , Yoneda→-section , ←Yoneda-section 
    where 
      open Functions₁ (Nat(Hom[ A ,—] , F))  renaming (_~_ to _`~_)
      open Functions₁ (F₀ A) using (_~_)
      
      Yoneda→-section : ←Yoneda A ○ Yoneda→ A `~ id
      Yoneda→-section (η , nat)  {C} f = begin 
        fmap f · (η · Id) ≈⟨ nat f Id ⟩ 
        η · (f ∘ Id ∘ Id) ≈⟨ η .hom {f ∘ Id ∘ Id} {f} (idᵣ ⨾ idᵣ) ⟩ 
        η · f ∎ 
        where 
          open Setoid (F₀ C) 
          open SetoidReasoning (F₀ C)
      
      ←Yoneda-section : Yoneda→ A ○ ←Yoneda A ~ id
      ←Yoneda-section = F-id


-------------------------------------------------------------------------------
-- The contravariant Yoneda lemma:
-- 
-- For locally small 𝒞 and functor F : 𝒞ᵒᵖ → Set, the set 
-- of natural transformations from Hom(—,A) to F, denoted
--   Nat(Hom(—,A), F) 
-- is isomorphic to F(A). Formally:
--   Nat(Hom(—,A), F) ≃ F(A)
-- where _≃_ denotes a bijection between sets.

module ContravariantYoneda (F : 𝒞ᵒᵖ ⇛ 𝐒𝐞𝐭𝐨𝐢𝐝 o e) where
  open Functor F        
  
  Yonedaᵒᵖ→ : ∀ A → (Hom[—, A ] ⇒ₙ F) → ∣ F₀ A ∣
  Yonedaᵒᵖ→ = TODO 

  ←Yonedaᵒᵖ : ∀ A → ∣ F₀ A ∣ → (Hom[—, A ] ⇒ₙ F)
  ←Yonedaᵒᵖ = TODO 

  Yonedaᵒᵖ : ∀ A → (Nat(Hom[—, A ] , F)) ≅ (F₀ A)
  Yonedaᵒᵖ A = Yonedaᵒᵖ→ A , ←Yonedaᵒᵖ A , TODO , TODO


-------------------------------------------------------------------------------
-- The Yoneda embedding:
-- 
-- The Yoneda Embedding, y, is a functor y : 𝒞ᵒᵖ → [ 𝒞 , 𝐒𝐞𝐭𝐨𝐢𝐝 ],
-- that sends an object A ∈ 𝒞 to its corresponding Hom functor Hom[A ,—],
-- and sends each morphism f : B ⇒ A to the natural transformation
-- Hom[f ,—].

module YonedaEmbedding where

  -- The Yoneda embedding can be defined simply as the curried form of
  -- the hom-bifunctor Hom[—,—].
  𝓎 : 𝒞ᵒᵖ ⇛ [ 𝒞 , 𝐒𝐞𝐭𝐨𝐢𝐝 o e ]
  𝓎 = λ[ Hom[—,—] ] 
  
  -- The Yoneda Lemma tells us that 𝓎 is full and faithful
  𝓎-Full : Full 𝓎
  𝓎-Full = λF-Full Hom[—,—] Hom[—,—]-Full   

  𝓎-Faithful : Faithful 𝓎
  𝓎-Faithful = λF-Faithful Hom[—,—] Hom[—,—]-Faithful   
  
