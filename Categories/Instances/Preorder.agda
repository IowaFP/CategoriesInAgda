{-# OPTIONS --without-K #-}
module Categories.Instances.Preorder where

open import Categories.Prelude
open import Categories.Category
open import Categories.Category.Subcategory
open import Categories.Functor 
open import Categories.NaturalTransformation
open import Categories.Constructions.Preorder

open import Categories.Instances.Cat

open PropositionalEquality hiding (isPreorder)

--------------------------------------------------------------------------------
-- The category of groupoids

module _ (o a e : Level) where
  open PreorderCategory
  
  -- 𝐏𝐫𝐞 is a full subcategory of 𝐂𝐚𝐭
  𝐏𝐫𝐞 : Category (lsuc (o ⊔ a ⊔ e)) (o ⊔ a ⊔ e) (o ⊔ a ⊔ e) 
  𝐏𝐫𝐞 = FullSubcategory (𝐂𝐚𝐭 o a e) (PreorderCategory o a e) category 

  open Category (𝐂𝐚𝐭 o a e)
  open _↪_  

  -- Full subcategory witness
  𝐏𝐫𝐞↪𝐂𝐚𝐭 : 𝐏𝐫𝐞 ↪ 𝐂𝐚𝐭 o a e
  𝐏𝐫𝐞↪𝐂𝐚𝐭 = Subcategory↪ (𝐂𝐚𝐭 o a e) category 

  -- Inclusion functor
  𝐏𝐫𝐞-ι : 𝐏𝐫𝐞 ⇛ 𝐂𝐚𝐭 o a e 
  𝐏𝐫𝐞-ι = 𝐏𝐫𝐞↪𝐂𝐚𝐭 .ι