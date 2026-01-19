{-# OPTIONS --without-K #-}
module Categories.Constructions.Exponential where 

open import Categories.Prelude
open import Categories.Category
open import Categories.Constructions.Product

-- ------------------------------------------------------------------------------
-- Exponentials
{- 
  An object Zʸ and morphism eval : Zʸ × Y → Z is an *exponential object*
  if for any object X and morphism g : X × Y → Z there is a unique
  morphism λg : X → Zʸ (called the *tranpose* of g) such that the following
  diagram commutes:
  
         X × Y                X
          |   \               |
  λg × id |    \ g            | λg
          v      v            v
        Zʸ × Y --> Z          Zʸ 
              eval
  This is the categorical analogue to *currying*:
    λ[_]   : (X × Y → Z) → (X → Y → Z)
    λ[ g ] = (λ x y → g (x , y))
  Here, g (what we have) expects a tuple input X * Y, and 
  λ[g] gives the curried version at type X → Y → Z. Commutativity
  of the above diagram asserts, in essence, that
    λ[ g ] x y ≡ g(x , y)
  for all x : X , y : Y.
-}     


-- ------------------------------------------------------------------------------
-- Exponentials

module _ (𝒞 : Category o a e) (prods : AdmitsProducts 𝒞) where 
  open Category 𝒞 
  -- This is stronger than strictly required (we need only
  -- that Y, in Zʸ, has all binary products.)
  open AdmitsProducts prods

  private 
    variable
      A B C X Y Z : Obj 
      f g h : A ⇒ B 

  record hasExponential (Z Y : Obj)  : Set (o ⊔ e ⊔ a) where 
    field 
      Zʸ : Obj 
      `eval : Zʸ × Y ⇒ Z 
      `λ[_] : ∀ {X : Obj} (g : X × Y ⇒ Z) → X ⇒ Zʸ
      `transpose : ∀ {X : Obj} (g : X × Y ⇒ Z) → `eval ∘ ⟪ `λ[ g ] , Id ⟫ ≈ g 
      `unique : (g : X × Y ⇒ Z) (λg : X ⇒ Zʸ) → 
                `eval ∘ ⟪ λg , Id ⟫ ≈ g → 
                λg ≈ `λ[ g ] 


  record AdmitsExponentials : Set (o ⊔ e ⊔ a) where 
    constructor admitsExponentials
    open hasExponential public
    field 
      exponentials : ∀ (Z Y : Obj) → hasExponential Z Y 

    -- Re-exporting friendly accessors
    infixl 5 _^_ 
    _^_ : ∀ (Z Y : Obj) → Obj 
    Z ^ Y = exponentials Z Y .Zʸ

    eval : (Z ^ Y) × Y ⇒ Z
    eval {Z = Z} {Y = Y} = exponentials Z Y .`eval 

    λ[_] : ∀ {X : Obj} (g : X × Y ⇒ Z) → X ⇒ (Z ^ Y)
    λ[_] {Y = Y} {Z = Z}  g = exponentials Z Y .`λ[_] g 

    transpose : ∀ {X : Obj} (g : X × Y ⇒ Z) → eval ∘ ⟪ λ[ g ] , Id ⟫ ≈ g 
    transpose {Y = Y} {Z = Z} g = exponentials Z Y .`transpose g 

{- ------------------------------------------------------------------------------ 
  I find it most helpful to demonstrate exponentials in type theory:
  The universal property is simply saying that we can curry the function
    g : X × Y → Z 
  into a function
    λg : X → Y → Z 
  such that 
    eval ○ (λg × id) ≈ g.
  The function λg is the curried form of g, and the commutativity asserts that 
  the two forms are equivalent.
-------------------------------------------------------------------------------}

private module Demo where 
    variable
      X Y Z : Set 
    open PropositionalEquality
  
    -- Evaluation is simply function application
    eval : (Y → Z) * Y → Z 
    eval (f , y) = f y 

    -- We may obviously curry any tuple function
    curry′ : (g : (X * Y) → Z) → Σ[ λg ∈ (X → Y → Z) ] (eval ○ cross λg id ≡ g)
    curry′ g = (λ x y → g (x , y)) , refl 

    -- Further, λg is unique
    unique′ : (g : (X * Y) → Z) (λg : X → Y → Z) → 
              eval ○ (cross λg id) ≡ g → 
              λg ≡ curry′ g .fst 
    unique′ g λg refl = refl              

