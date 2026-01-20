{-# OPTIONS --without-K #-}
module Categories.Instances.Discrete where

open import Categories.Prelude
open import Categories.Category
open import Categories.Category.Subcategory
open import Categories.Functor 
open import Categories.NaturalTransformation
open import Categories.Constructions.Discrete

open import Categories.Instances.Cat

--------------------------------------------------------------------------------
-- The category of groupoids

module _ (o a e : Level) where
  open DiscreteCategory
  
  -- 𝐃𝐢𝐬𝐜𝐫𝐞𝐭𝐞 is a full subcategory of 𝐂𝐚𝐭
  𝐃𝐢𝐬𝐜𝐫𝐞𝐭𝐞 : Category (lsuc (o ⊔ a ⊔ e)) (o ⊔ a ⊔ e) (o ⊔ a ⊔ e) 
  𝐃𝐢𝐬𝐜𝐫𝐞𝐭𝐞 = FullSubcategory (𝐂𝐚𝐭 o a e) (DiscreteCategory o a e) category 

  open Category (𝐂𝐚𝐭 o a e)
  open _↪_  

  -- Full subcategory witness
  𝐃𝐢𝐬𝐜𝐫𝐞𝐭𝐞↪𝐂𝐚𝐭 : 𝐃𝐢𝐬𝐜𝐫𝐞𝐭𝐞 ↪ 𝐂𝐚𝐭 o a e
  𝐃𝐢𝐬𝐜𝐫𝐞𝐭𝐞↪𝐂𝐚𝐭 = Subcategory↪ (𝐂𝐚𝐭 o a e) category 

  -- Inclusion functor
  𝐃𝐢𝐬𝐜𝐫𝐞𝐭𝐞-ι : 𝐃𝐢𝐬𝐜𝐫𝐞𝐭𝐞 ⇛ 𝐂𝐚𝐭 o a e 
  𝐃𝐢𝐬𝐜𝐫𝐞𝐭𝐞-ι = 𝐃𝐢𝐬𝐜𝐫𝐞𝐭𝐞↪𝐂𝐚𝐭 .ι