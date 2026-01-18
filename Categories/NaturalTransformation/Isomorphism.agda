{-# OPTIONS --without-K #-}

module Categories.NaturalTransformation.Isomorphism where 

open import Categories.Prelude
open import Categories.Category 
open import Categories.Functor 
open import Categories.NaturalTransformation.Base
open import Categories.Reasoning.Hom

--------------------------------------------------------------------------------
-- natural transformations

module _ {𝒞 : Category o₁ a₁ e₁} 
    {𝒟 : Category o₂ a₂ e₂}
    (F G : Functor 𝒞 𝒟) where 

  open Category
  private 
    module F = Functor F 
    module G = Functor G 

  infixr 1 _≃ₙ_
  -- Natural isomorphisms
  record _≃ₙ_ : Set (o₁ ⊔ a₁ ⊔ e₁ ⊔ o₂ ⊔ a₂ ⊔ e₂) where 
    constructor _,_    
    open NaturalTransformation
    field 
      nat : NaturalTransformation F G 
      iso : ∀ {A : 𝒞 .Obj} → isIso 𝒟 (nat .η {A})
  open _≃ₙ_ public 

--------------------------------------------------------------------------------
-- Natural isomorphisms form an equivalence relation on functors

module _ 
    {𝒞 : Category o₁ a₁ e₁} 
    {𝒟 : Category o₂ a₂ e₂} where 

  open HomReasoning 𝒟 
  open Category 𝒟
  open isIso 
  open areInverse 

  -- the identity natural isomorphism
  IdN : ∀ {F : Functor 𝒞 𝒟} → F ≃ₙ F
  IdN {F} = (Id , λ f → begin 
    F.fmap f ∘ Id ≈⟨ idᵣ ⟩ 
    F.fmap f      ≈⟨ sym-≈ idₗ ⟩ 
    Id ∘ F.fmap f ∎) ,
    Id , idₗ , idₗ
    where 
      module F = Functor F 
  
  -- Natural isomorphisms form an equivalence relation on functors
  refl-≃ₙ = IdN 
  sym-≃ₙ : ∀ {F G : Functor 𝒞 𝒟} → F ≃ₙ G → G ≃ₙ F 
  sym-≃ₙ {F} {G} ((η , nat) , i) = 
    ((λ {A} → i {A} .∼) ,
    -- A subtlety: we must confirm that the inverse of a morphism
    -- induced by a natural transformation is indeed a natural transformation.
    λ f → begin 
      F.fmap f ∘ i .∼              ≈⟨ cong-∘ₗ (sym-≈ idₗ) ⟩ 
      Id ∘ F.fmap f ∘ i .∼         ≈⟨ cong-∘ₗ (cong-∘ₗ (sym-≈ (i .iso .rinv))) ⟩ 
      i .∼ ∘ η ∘ F.fmap f ∘ i .∼   ≈⟨ cong-∘ₗ assᵣ ⟩ 
      i .∼ ∘ (η ∘ F.fmap f) ∘ i .∼ ≈⟨ cong-∘ₗ (cong-∘ᵣ (sym-≈ (nat f))) ⟩ 
      i .∼ ∘ (G.fmap f ∘ η) ∘ i .∼ ≈⟨ ((cong-∘ₗ assₗ) ⨾ assᵣ) ⟩ 
      i .∼ ∘ G.fmap f ∘ (η ∘ i .∼) ≈⟨ ((cong-∘ᵣ (i .iso .linv)) ⨾ idᵣ) ⟩ 
      i .∼ ∘ G.fmap f ∎ ) , 
      λ {A} → η {A} , i {A} .iso .rinv , i {A} .iso .linv
    where 
      module F = Functor F 
      module G = Functor G 
  trans-≃ₙ : ∀ {F G H : Functor 𝒞 𝒟} → F ≃ₙ G → G ≃ₙ H → F ≃ₙ H
  trans-≃ₙ {F} {G} {H} ((η , nat-η) , i₁) ((ε , nat-ε) , i₂) = 
    ((λ {A} →  ε ∘ η) , λ f → 
      begin
        H.fmap f ∘ (ε ∘ η) ≈⟨ (assₗ ⨾ (cong-∘ₗ (nat-ε f))) ⟩ 
        ε ∘ G.fmap f ∘ η   ≈⟨ (assᵣ ⨾ cong-∘ᵣ (nat-η f) ⨾ assₗ) ⟩ 
        ε ∘ η ∘ F.fmap f ∎) , 
    λ {A} → (i₁ {A} .∼ ∘ i₂ {A} .∼) , 
      (begin 
        ε ∘ η ∘ (i₁ .∼ ∘ i₂ .∼) ≈⟨ (assₗ ⨾ cong-∘ₗ assᵣ ⨾ cong-∘ₗ (cong-∘ᵣ (i₁ .iso .linv))) ⟩ 
        ε ∘ Id ∘ i₂ .∼          ≈⟨ (assᵣ ⨾ cong-∘ᵣ idₗ) ⟩ 
        ε ∘ i₂ .∼               ≈⟨ i₂ .iso .linv ⟩ 
        Id ∎)  , 
      (begin
        i₁ .∼ ∘ i₂ .∼ ∘ (ε ∘ η) ≈⟨ (assₗ ⨾ (cong-∘ₗ assᵣ ⨾ cong-∘ₗ (cong-∘ᵣ (i₂ .iso .rinv)))) ⟩ 
        i₁ .∼ ∘ Id ∘ η          ≈⟨ cong-∘ₗ idᵣ ⟩
        i₁ .∼ ∘ η               ≈⟨ i₁ .iso .rinv ⟩ 
        Id ∎)
    where 
      module F = Functor F 
      module G = Functor G 
      module H = Functor H 
 
  nat-setoid : Setoid _ _
  nat-setoid = record
    { Carrier       = Functor 𝒞 𝒟 
    ; _≈_           = _≃ₙ_
    ; isEquivalence = record { refl = refl-≃ₙ ; sym = sym-≃ₙ ; trans = trans-≃ₙ }
    }


--------------------------------------------------------------------------------
-- The category of categories has functors as arrows and setoid equivalence 
-- given by natural isomorphism: that functor composition respect setoid 
-- equivalence is given precisely by horizontal composition of natural 
-- isomorphisms. We also prove the other laws (composition by the identity 
-- functor is an identity, and associativity.)

module _ {𝒞 : Category o₁ a₁ e₁} 
    {𝒟 : Category o₂ a₂ e₂}
    {ℰ : Category o₃ a₃ e₃}
    {F G : Functor 𝒞 𝒟}
    {J K : Functor 𝒟 ℰ} where
  private 
    module C = Category 𝒞 ; module D = Category 𝒟  ; module F = Functor F 
    module G = Functor G ; module J = Functor J ; module K = Functor K
  open Category ℰ ; open _≃ₙ_ ; open NaturalTransformation ; open isIso ; open areInverse
  open HomReasoning ℰ 
  
  -- Horizontal composition of natural isomorphisms yields 
  -- a natural isomorphism.
  H-iso : F ≃ₙ G → J ≃ₙ K → (J ∘F F) ≃ₙ (K ∘F G)
  H-iso (η₁@(μ , nat₁) , i₁) (η₂@(ε , nat₂) , i₂) = 
    let ((α , nat-α) , i-α) = α in 
    let ((β , nat-β) , i-β) = β in
    (η₂ ∘H η₁) , 
    λ {A} → ζ .η , 
      (begin 
        K.fmap μ ∘ ε ∘ (J.fmap α ∘ β) ≈⟨ (cong-∘ₗ (nat₂ μ) ⨾ assₗ) ⟩ 
        ε ∘ J.fmap μ ∘ J.fmap α ∘ β   ≈⟨ cong-∘ₗ (assᵣ ⨾ cong-∘ᵣ (sym-≈ (J.F-∘ α μ))) ⟩ 
        ε ∘ J.fmap (μ D.∘ α) ∘ β      ≈⟨ cong-∘ₗ (cong-∘ᵣ ((J.F-cong (i₁ .iso .linv)) ⨾ J.F-id)) ⟩ 
        ε ∘ Id ∘ β                    ≈⟨ (cong-∘ₗ idᵣ ⨾ i₂ .iso .linv) ⟩ 
        Id ∎) ,  
      (begin 
        J.fmap α ∘ β ∘ (K.fmap μ ∘ ε) ≈⟨ (cong-∘ₗ (nat-β α) ⨾ assₗ) ⟩ 
        β ∘ K.fmap α ∘ K.fmap μ ∘ ε   ≈⟨ cong-∘ₗ (assᵣ ⨾ cong-∘ᵣ (sym-≈ (K.F-∘ μ α))) ⟩ 
        β ∘ K.fmap (α D.∘ μ) ∘ ε      ≈⟨ cong-∘ₗ (cong-∘ᵣ ((K.F-cong (i-α .iso .linv)) ⨾ K.F-id)) ⟩ 
        β ∘ Id ∘ ε                    ≈⟨ (cong-∘ₗ idᵣ ⨾ i₂ .iso .rinv) ⟩
        Id ∎)
    where 
      α : G ≃ₙ F
      α = sym-≃ₙ (η₁ , i₁)
      β : K ≃ₙ J 
      β = sym-≃ₙ (η₂ , i₂)
      ζ : NaturalTransformation (K ∘F G) (J ∘F F) 
      ζ = (β .nat) ∘H (α .nat)

module _ {𝒞 : Category o₁ a₁ e₁} 
    {𝒟 : Category o₂ a₂ e₂}
    {F : Functor 𝒞 𝒟} where
  private 
    module C = Category 𝒞
    module D = Category 𝒟 
    module F = Functor F 

  open Category 𝒟

  IdF-idₗ : (IdF ∘F F) ≃ₙ F 
  IdF-idₗ = 
    (Id , λ f → idᵣ ⨾ (sym-≈ idₗ)) , 
    Id , idₗ , idₗ

  IdF-idᵣ : (F ∘F IdF) ≃ₙ F 
  IdF-idᵣ = 
    (Id , λ f → idᵣ ⨾ (sym-≈ idₗ)) , 
    Id , idₗ , idₗ

module _ 
    {𝒜 : Category o a e}
    {ℬ : Category o₁ a₁ e₁} 
    {𝒞 : Category o₂ a₂ e₂}
    {𝒟 : Category o₃ a₃ e₃}
    (F : Functor 𝒜 ℬ)
    (G : Functor ℬ 𝒞)
    (H : Functor 𝒞 𝒟) where
  private 
    module A = Category 𝒜 ; module B = Category ℬ ; module C = Category 𝒞 ; module D = Category 𝒟 
    module F = Functor F ; module G = Functor G ; module H = Functor H 
  open Category 𝒟 
  Functor-assₗ : H ∘F (G ∘F F) ≃ₙ (H ∘F G) ∘F F 
  Functor-assₗ = (Id , λ f → idᵣ ⨾ sym-≈ idₗ) , Id , idᵣ , idᵣ
