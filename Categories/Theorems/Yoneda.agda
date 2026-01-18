module Categories.Theorems.Yoneda where 

open import Categories.Prelude
open import Categories.Category 
open import Categories.Functor 

open import Categories.NaturalTransformation 

open import Categories.Category.Product

open import Categories.Instances.Sets

open import Categories.Reasoning.Hom 


-------------------------------------------------------------------------------
-- The Yoneda Lemma.

-- Perhaps useful reading:
-- - https://homotopytypetheory.org/2012/05/02/a-type-theoretical-yoneda-lemma/
-- - https://math.uchicago.edu/~may/REU2022/REUPapers/Stern.pdf

-------------------------------------------------------------------------------
-- See Categories.Functor.Hom for a description of hom-functors

open import Categories.Functor.Hom

-------------------------------------------------------------------------------
-- The covariant Yoneda lemma:
-- 
-- For locally small 𝒞 and functor F : 𝒞 → Set, the set 
-- of natural transformations from Hom(A,—) to F, denoted
--   Nat(Hom(A,—), F) 
-- is isomorphic to F(A). Formally:
--   Nat(Hom(A,—), F) ≃ F(A)
-- where _≃_ denotes a bijection between sets.

module CovariantYoneda {ℓ} 
      (𝒞 : Category a o e) 
      (F : Functor 𝒞 (Setoids ℓ)) where

-------------------------------------------------------------------------------
-- The contravariant Yoneda lemma:
-- 
-- For locally small 𝒞 and functor F : 𝒞ᵒᵖ → Set, the set 
-- of natural transformations from Hom(—,A) to F, denoted
--   Nat(Hom(—,A), F) 
-- is isomorphic to F(A). Formally:
--   Nat(Hom(—,A), F) ≃ F(A)
-- where _≃_ denotes a bijection between sets.

module ContravariantYoneda {ℓ}
      (𝒞 : Category a o e) (
       F : Functor (𝒞 .op) (Setoids ℓ)) where


