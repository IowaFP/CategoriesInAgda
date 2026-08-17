
module Categories.TypeTheory.STLC.FunctorialSemantics where

open import Categories.Prelude hiding (`_) 
open import Categories.Prelude.Equality.Heterogeneous

open import Categories.Category
open import Categories.Constructions.Exponential 
open import Categories.Constructions.Product
open import Categories.Constructions.Terminal
open import Categories.Constructions.CCC

open import Categories.TypeTheory.STLC.Syntax
open import Categories.TypeTheory.STLC.CCCModel

-------------------------------------------------------------------------------
-- Functorial semantics of the STLC 
-- 
-- [CCCModel.agda] describes how, be it on paper or on Agda,
-- we can describe a meta-level denotation of the STLC into a given 
-- CCC. We can actually realize this meta-level function in the object language
-- by describing the semantics of the STLC as a *functor*.

-------------------------------------------------------------------------------
{- Syntactic categories

The first step is to realize the syntax of the STLC itself 
as a *syntactic category*, given by:
- Objects are types
- Arrows A → B are terms with type B given x : A in context,
  that is, of the form:
  - x : A ⊢ t : B, or Term (∅ , A) B 
  Note that longer contexts are not required because we 
  have product types. For example, rather than
    f : A → B , x : A ⊢ f x : B 
  we could equivalently have
    x : (A → B) × A ⊢ (fst x) (snd x) : B 
- Composition of M : Term (∅ , B) C and N : Term (∅ , A) B
  is obtained by substitution. That is, we want a term
    L : Term (∅ , A) C,
  which can be achieved by letting the free variable
  in M : Term (∅ , B) C map to N.
- The identity morphism is just the variable rule

   A ∈ ∅ , A 
   ---------
   ∅ , A ⊢ A 

AH> We no longer can ignore an equational theory of terms,
    as terms are now arrows and we must describe when
    arrows are equivalent. Hence we need 
      _≡λ_ : Term Γ τ → Term Γ τ → Set 
    so that 
      _≈_ = _≡λ_.
-} 

λCat : Category lzero lzero e 
λCat .Category.Obj = Type
λCat .Category._⇒_ A B = Term (∅ , A) B
λCat .Category._∘_ M N = sub (λ { `0 → N }) M
λCat .Category.Id = ` `0
λCat .Category._≈_ = {! _≡_  !}
λCat .Category.eqv = {!   !}
λCat .Category.idᵣ = {!   !}
λCat .Category.idₗ = {!   !}
λCat .Category.assₗ = {!   !}
λCat .Category._⋆_ = {!   !} 

-------------------------------------------------------------------------------
-- λCat is cartesian closed.
-- 
-- - the unit type is terminal, and 
--    ⋆  : Term (∅ , A) `⊤ 
--   is the unique morphism A → `⊤.
-- - The product type _×_ is the product
-- - The function type _→_ is the exponential

-------------------------------------------------------------------------------
-- Functorial semantics
-- 
-- Since λCat is cartesian closed, a given interpretation ⟦_⟧ of the STLC 
-- in a CCC 𝒞 induces a Cartesian Closed functor M : λCat → 𝒞.
-- In other words, the meta-level notion of an interpretation can be replaced
-- by an object level notion of a functor. 

-------------------------------------------------------------------------------
-- Syntactic categories *classify* models:
-- For any λ-theory 𝕋, the syntactic category of 𝕋, 𝒞𝕋, classifies
-- 𝕋-models, in the sense that for any CCC 𝒞 there is an equivalence
-- of categories:
--   Mod(𝕋, 𝒞) ≃ CCC(𝒞𝕋, 𝒞)
-- 
-- The morphisms of 𝕋-models on the left are the isomorphisms of the 
-- underlying structures, and on the right we take the natural isomorphisms
-- of CCC functors.
-- 
-- Disregarding the additional terms, types, and equations of a given
-- λ-model 𝕋, we have that:
-- For any CCC 𝒞, there is an equivalence of categories
--   Mod(STLC, 𝒞) ≃ CCC(λCat, 𝒞)
-- naturally in 𝒞.
-- 
-- AH> I'm not sure what this means. I believe
--     Mod(STLC, 𝒞) is the category of *models* of the STLC,
--     where a *model* of the STLC in 𝒞 in our case is an interpretation:
--     - ⟦_⟧t : Type → Obj(𝒞)
--     - ⟦_⟧v : Var Γ → ⟦ Γ ⟧ctx 𝒞.⇒ ⟦ τ ⟧t 
--     - ⟦_⟧ctx : Context → Obj(𝓒) 
--     - ⟦_⟧ : Term Γ τ → ⟦ Γ ⟧ctx 𝒞.⇒ ⟦ τ ⟧t 
--     That is, a four-tuple (⟦_⟧t , ⟦_⟧v, ⟦_⟧ctx, ⟦_⟧).
--     I'm not sure how one forms a category, here. 
--     Awodey writes that the arrows are the "isomorphisms
--     of the underlying structures".
--     I'll come back to this.
-- 
-- 
--     