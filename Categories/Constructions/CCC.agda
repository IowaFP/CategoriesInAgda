module Categories.Constructions.CCC where 

open import Categories.Prelude
open import Categories.Category
open import Categories.Constructions.Exponential 
open import Categories.Constructions.Product
open import Categories.Constructions.Terminal

-------------------------------------------------------------------------------
-- Cartesian Closed Categories
-- 
-- There are numerous equivalent definitions of CCC's. 
-- We'll use the straightforward definition of a category that admits products, 
-- exponentials, and has a terminal object.

record IsCCC {a o e} (𝒞 : Category o a e) : Set (lsuc a ⊔ lsuc o ⊔ lsuc e)  where 
  open Category 𝒞 

  field 
    products : AdmitsProducts 𝒞
    exponentials : AdmitsExponentials 𝒞 products
    𝕋 : Obj
    isTerm : isTerminal 𝒞 𝕋

  open AdmitsProducts products public 
  open AdmitsExponentials exponentials public 
  open isTerminal isTerm public 
