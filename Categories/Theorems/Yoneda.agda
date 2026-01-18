-- --------------------------------------------------------------------------------
-- -- The Yoneda lemma
-- -- (For about the millionth time I have lost the thread.)
-- -- Perhaps useful reading:
-- -- - https://homotopytypetheory.org/2012/05/02/a-type-theoretical-yoneda-lemma/
-- -- - https://math.uchicago.edu/~may/REU2022/REUPapers/Stern.pdf

-- module Yoneda (𝒞 : Category o a e) (A : 𝒞 .Category.Obj) (F : Functor 𝒞 (Setoids o e)) where 

  -- YonedaLemma : 

-- Yoneda₁ :  (𝓒 : Category {ℓ₁} {ℓ₂}) → (A : 𝓒 .Obj) → (F : Functor 𝓒 Sets) → NaturalTransformation _ _ (Hom[ 𝓒 , A ]) F → F .F₀ A 
-- Yoneda₁ 𝓒 A F record { η = η ; nat = nat } = η A (𝓒 .id[_] A) 

-- Yoneda₂ : (𝓒 : Category {ℓ₁} {ℓ₂}) → (A : 𝓒 .Obj) → (F : Functor 𝓒 Sets) → F .F₀ A → NaturalTransformation _ _ (Hom[ 𝓒 , A ]) F
-- Yoneda₂ 𝓒 A F a = record 
--     { η = λ X A⇒X → F .F₁ A⇒X a ; 
--     nat = λ A B A⇒B → extensionality (λ f → cong-app (F .F-∘ f A⇒B) a) } 