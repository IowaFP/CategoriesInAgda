{-# OPTIONS --without-K #-}

module Categories.Constructions.FAlgebra where 

open import Categories.Prelude
open import Categories.Category 
open import Categories.Functor 
open import Categories.NaturalTransformation 
open import Categories.Constructions.Initial
open import Categories.Reasoning.Hom 
open import Categories.Category.Subcategory

--------------------------------------------------------------------------------
-- F-algebras
--
-- An F-Algebra in category 𝒞, for endofunctor F, is a 2-tuple (A , φ) where
-- A ∈ 𝒞 (the *carrier*) and φ : F A ⇒ A. F-Algebras form a category Alg 
-- whose objects are F-Algebras and a morphism from (A , φ) to (B , ψ) is 
-- an arrow f : A ⇒ b such that the following diagram commutes.
--          φ 
--     F A ----> A 
--      |        |
-- F(f) |        | f
--      v        v
--     F B ----> B 
--           ψ 
--
-- An initial F-Algebra (μF , in) is given by the least fixed-point of F. That is,
-- we have in : F μF ≃ μF : out. By initiality, we have a unique morphism 
-- ⦅ φ ⦆ : μF → C for any algebra (C , φ).
--           in 
--     F μF ----> μF
--      |        |
-- F(φ) |        | ⦅ φ ⦆ 
--      v        v
--     F C ----> C 
--           φ  

module _ (𝒞 : Category o a e)
         (F : Endofunctor 𝒞) where 
  open Category 𝒞 
  open Functor F 

  record FAlg : Set (o ⊔ a) where 
    constructor _,_
    field
      Carrier : Obj
      alg : F₀ Carrier ⇒ Carrier

  open FAlg public 

  -- A fixed-point is an isomorphic F-Algebra
  record FixedPoint : Set (o ⊔ a ⊔ e) where 
    constructor _,_ 
    field 
      alg : FAlg 
      iso : isIso 𝒞 (alg .FAlg.alg)

module _ {𝒞 : Category o a e}
         {F : Endofunctor 𝒞} where 

  open Category 𝒞 
  open Functor F 
  open HomReasoning 𝒞 

  open FAlg 
  record Hom (φ ψ : FAlg 𝒞 F) : Set (a ⊔ e) where 
    constructor _,_ 
    field 
      hom : φ .Carrier ⇒ ψ .Carrier 
      commutes : hom ∘ φ .alg ≈ ψ .alg ∘ fmap hom

  _∘FA_ : ∀ {φ ψ ζ} → Hom ψ ζ → Hom φ ψ → Hom φ ζ 
  _∘FA_ {φ = (A , φ)} {ψ = (B , ψ)} {ζ = (C , ζ)} (f , comm-f) (g , comm-g) = 
   f ∘ g , 
   (begin 
      f ∘ g ∘ φ              ≈⟨ (assᵣ ⨾ cong-∘ᵣ comm-g) ⟩ 
      f ∘ (ψ ∘ fmap g)       ≈⟨ (assₗ ⨾ cong-∘ₗ comm-f) ⟩ 
      (ζ ∘ fmap f) ∘ fmap g  ≈⟨ (assᵣ ⨾ cong-∘ᵣ (sym-≈ (F-∘ g f))) ⟩ 
      ζ ∘ fmap (f ∘ g) ∎)
  
  IdHom : ∀ {φ : FAlg 𝒞 F} → Hom φ φ 
  IdHom {φ = (A , φ)} = Id , (begin 
    Id ∘ φ  ≈⟨ left-id ⟩
    φ       ≈⟨ (sym-≈ right-id ⨾ cong-∘ᵣ (sym-≈ F-id)) ⟩ 
    φ ∘ fmap Id ∎)

-- ------------------------------------------------------------------------------
-- F-Algebras form a category

module _ (𝒞 : Category o a e)
         (F : Endofunctor 𝒞) where 
  open Category 𝒞
  open Functor F 
  open IsEquivalence
  open Hom
  open HomReasoning 𝒞 

  FAlgebras : Category (o ⊔ a) (a ⊔ e) e 
  FAlgebras .Category.Obj = FAlg 𝒞 F 
  FAlgebras .Category._⇒_ =  Hom
  FAlgebras .Category._∘_ = _∘FA_
  FAlgebras .Category.Id = IdHom
  FAlgebras .Category._≈_ (f , _) (g , _) =  f ≈ g
  FAlgebras .Category.eqv  .refl = refl-≈
  FAlgebras .Category.eqv  .sym = sym-≈
  FAlgebras .Category.eqv  .trans = trans-≈
  FAlgebras .Category.cong-∘  = cong-∘
  FAlgebras .Category.right-id =  right-id
  FAlgebras .Category.left-id = left-id
  FAlgebras .Category.assₗ = assₗ

  -- ------------------------------------------------------------------------------
  -- The fixed-points of F form a full subcategory of the category FAlgebras
  open FixedPoint 

  FixedPoints : Category (o ⊔ a ⊔ e) (a ⊔ e) e 
  FixedPoints = FullSubcategory FAlgebras (FixedPoint 𝒞 F) alg 

------------------------------------------------------------------------------
-- Initial objects in the category of F-algebras yield catamorphisms

  module _ (φ : FAlg 𝒞 F) 
           (ini : isInitial FAlgebras φ) where 
    open isInitial ini
    open FAlg φ renaming (Carrier to μF ; alg to In)

    -- The catamorphism
    ⦅_⦆ : (ψ : FAlg 𝒞 F) → Hom φ ψ 
    ⦅ ψ ⦆ = ! ψ

    -- ------------------------------------------------------------------------------
    -- Lambek's lemma: If F has an initial F-Algebra φ, then φ is a fixed-point of F.

    Lambek : FixedPoint 𝒞 F  
    Lambek = 
      φ , Out , 
      (begin 
        In ∘ Out ≈⟨ !-id  In∘Out ⟩ 
        Id ∎) , 
      (begin 
        Out ∘ In ≈⟨ Out-commutes ⟩ 
        fmap In ∘ fmap Out ≈⟨ sym-≈ (F-∘ Out In) ⟩ 
        fmap (In ∘ Out) ≈⟨ (F-cong (!-id In∘Out) ⨾ F-id) ⟩ 
        Id ∎)
      where 
        open Hom ⦅ (F₀ μF , fmap In) ⦆ renaming (hom to Out ; commutes to Out-commutes)
        In∘Out : Hom φ φ 
        In∘Out = In ∘ Out , (begin 
          In ∘ Out ∘ In             ≈⟨ (assᵣ ⨾ cong-∘ᵣ Out-commutes) ⟩ 
          In ∘ (fmap In ∘ fmap Out) ≈⟨ cong-∘ᵣ (sym-≈ (F-∘ Out In)) ⟩ 
          In ∘ fmap (In ∘ Out) ∎)

    -- ------------------------------------------------------------------------------
    -- Smyth and Plotkin's Lemma 1: an initial F-Algebra is also
    -- an initial fixed-point in the category of F-fixed points.

    SmythPlotkin : isInitial FixedPoints Lambek 
    SmythPlotkin .isInitial.! (ψ , _) = ⦅ ψ ⦆
    SmythPlotkin .isInitial.unique = unique
