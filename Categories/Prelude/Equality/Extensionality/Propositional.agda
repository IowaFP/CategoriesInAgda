{-# OPTIONS --without-K #-}

module Categories.Prelude.Equality.Extensionality.Propositional where

open import Categories.Prelude.Base
open import Axiom.Extensionality.Propositional public

--------------------------------------------------------------------------------
-- Functional extensionality at all universe levels
postulate
  extensionality : ∀ {ℓ ι} → Extensionality ℓ ι

-- Extensionality of implicit function spaces
extensionality-i : ∀ {ℓ ι} → ExtensionalityImplicit ℓ ι
extensionality-i = implicit-extensionality extensionality
