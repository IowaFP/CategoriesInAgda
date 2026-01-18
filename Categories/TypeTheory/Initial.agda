module Categories.TypeTheory.Initial where 

open import Prelude renaming (_>>=_ to _>>=ₘ_)
open import Categories.Papers.Monad 

--------------------------------------------------------------------------------
-- 2-Functoriality of Initial Semantics, and Applications.
--   - Benedikt Ahrens, Ambroise Lafont, Thomas Lamiaux. ICFP 2025
--     - https://dl.acm.org/doi/10.1145/3747527
--
-- Other papers I'd like to read:
--   - A Unified Framework for Initial Semantics. Thomas Lamiaux, Benedikt Ahrens. 2025
--     - https://arxiv.org/pdf/2502.10811
--   - Richard S. Bird and Ross Paterson. 1999. De Bruijn notation as a nested datatype. Journal of Functional Programming
--     - https://www.cambridge.org/core/journals/journal-of-functional-programming/article/de-bruijn-notation-as-a-nested-datatype/D8BFA383FDA7EA3DC443B4C42A168F30
--   - Thorsten Altenkirch and Bernhard Reus. 1999. Monadic Presentations of Lambda Terms Using Generalized Inductive
--     Types. In Computer Science Logic, 13th International Workshop, CSL ’99, 8th Annual Conference of the EACSL, Madrid,
--     Spain, September 20-25, 1999, Proceedings (Lecture Notes in Computer Science, Vol. 1683), Jörg Flum and Mario Rodríguez-
--        Artalejo (Eds.). Springer, 453–468. 
--     - doi:10.1007/3-540-48168-0_32


--------------------------------------------------------------------------------
-- Unscoped AST 

module Unscoped where private 
  data Term : Set where
    Var : ℕ → Term
    App : Term → Term → Term
    Abs : Term → Term 

  record alg (X : Set) : Set where 
    constructor Alg
    field 
      var : ℕ → X 
      app : X → X → X 
      abs : X → X 

  open alg 

  initial : alg Term
  initial .var = Var 
  initial .app = App 
  initial .abs = Abs 

  cata : ∀ {X : Set} → alg X → Term → X 
  cata (Alg var app abs) (Var x) = var x
  cata φ@(Alg var app abs) (App M N) = app (cata φ M) (cata φ N)
  cata φ@(Alg var app abs) (Abs M) = abs (cata φ M) 

--------------------------------------------------------------------------------
-- Well-scoped / intrinsic  

module Finite where private
  variable 
    n m : ℕ 

  data Term : ℕ → Set where
    Var : Fin n → Term n
    App : Term n → Term n → Term n 
    Abs : Term (suc n)  → Term n

  record alg (F : ℕ → Set) : Set where 
    constructor Alg 
    field 
      var : Fin n → F n 
      app : F n → F n → F n 
      abs : (F ○ suc) n → F n 

  open alg 

  initial : alg Term 
  initial .var = Var
  initial .app = App
  initial .abs = Abs

  cata : ∀ {F : ℕ → Set} → alg F → Term n → F n 
  cata (Alg var app abs) (Var x) = var x
  cata φ@(Alg var app abs) (App M N) = app (cata φ M) (cata φ N)
  cata φ@(Alg var app abs) (Abs M) = abs (cata φ M) 

--------------------------------------------------------------------------------
-- Well-scoped "infinite" context 
-- N.b. the authors write (in Rocq)
--   Inductive LC : Set → Set 
-- which would only work with impredicative-set.

module Infinite where private

  data Term {ℓ} : Set ℓ → Set (lsuc ℓ) where 
    Var : ∀ {X : Set ℓ} → X → Term X 
    App : ∀ {X : Set ℓ} → Term X → Term X → Term X 
    Abs : ∀ {X : Set ℓ} → Term (Maybe X) → Term X

  record alg {ℓ₁} {ℓ₂} (F : Set ℓ₁ → Set ℓ₂) : Set (lsuc ℓ₁ ⊔ ℓ₂) where 
    constructor Alg 
    field 
      var : ∀ {X : Set ℓ₁} → X → F X 
      app : ∀ {X : Set ℓ₁} → F X → F X → F X 
      abs : ∀ {X : Set ℓ₁} → (F ○ Maybe) X → F X 

  open alg 

  initial : ∀ {ℓ} → alg (Term {ℓ})
  initial .var = Var
  initial .app = App
  initial .abs = Abs

  cata : ∀ {X : Set ℓ₁} {F : Set ℓ₁ → Set ℓ₂} → alg F → Term X → F X  
  cata (Alg var app abs) (Var x) = var x
  cata φ@(Alg var app abs) (App M N) = app (cata φ M) (cata φ N)
  cata φ@(Alg var app abs) (Abs M) = abs (cata φ M) 

  -- As observed by many, simultaneous substitution equips the λ-calculus
  -- with the structure of a monad. N.b. losing some generality here 
  -- because I'm fixing M to : Set ℓ₁ → Set ℓ₂...

  module _ {ℓ} where 
    private 
      return : ∀ {A : Set ℓ₁} → A →  Term A 
      return = Var

      _$_ : ∀ {A B : Set ℓ₁}  → (A → B) → Term A → Term B 
      f $ (Var x) = Var (f x)
      f $ (App M N) = App (f $ M) (f $ N)
      f $ (Abs M) = Abs ((mapMaybe f) $ M)

      _>>=_ : ∀ {A B : Set ℓ₁} → Term A → (A → Term B) → Term B 
      (Var x)   >>= f = f x
      (App M N) >>= f = App (M >>= f) (N >>= f)
      (Abs M)   >>= f = Abs (M >>= maybe ((just $_) ○ f) (return nothing))

    monad : Monad (Term {ℓ})
    monad .Monad.return = Var 
    monad .Monad._$_ f M = f $ M
    monad .Monad._>>=_ M f = M >>= f 
    
  open Monad monad 

