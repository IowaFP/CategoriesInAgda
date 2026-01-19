{-# OPTIONS --without-K #-}
module Categories.Prelude.Exceptions where 

open import Categories.Prelude.Base 

--------------------------------------------------------------------------------
-- This repository is intended for my own education and amusement. There are 
-- a number of auxiliary lemmas and side-conditions that aren't particularly
-- informative or enlightening, which I can't be arsed to prove. This file
-- attempts to codify the classes of goals that I am skipping.

False = ∀ {ℓ} {A : Set ℓ} → A 
postulate 
  sorry : False 

`_  : String → False  
` msg = sorry 

TODO : (A : Set ℓ) →  A 
TODO A = sorry 

Won'tProve_Because_ : (A : Set ℓ) → String → A 
Won'tProve goal Because reason = sorry 
