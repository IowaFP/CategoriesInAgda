module Categories.All where 

-- Import all modules for easier type-checking
open import Categories.Prelude public 
open import Categories.Prelude.Equality.Heterogeneous public 
open import Categories.Prelude.Equality.Extensionality.Propositional public 
open import Categories.Prelude.Equality.Extensionality.Heterogeneous public 

open import Categories.Category public 
open import Categories.Category.Subcategory public 
open import Categories.Category.Product public 
open import Categories.Category.Equivalence public

open import Categories.Functor public 
open import Categories.Functor.Hom public 

open import Categories.NaturalTransformation public 

open import Categories.Constructions.Initial public 
open import Categories.Constructions.Terminal public 
open import Categories.Constructions.FAlgebra public 
open import Categories.Constructions.CWF public 
open import Categories.Constructions.Product public 
open import Categories.Constructions.Coproduct public 
open import Categories.Constructions.Exponential public
open import Categories.Constructions.Pullback public 

open import Categories.Instances.Cat public 
open import Categories.Category.Exponential public 
open import Categories.Instances.Setoid public 
open import Categories.Instances.Set public 
open import Categories.Instances.Groupoid public
open import Categories.Instances.Group public
open import Categories.Instances.NatFAlgebra public

open import Categories.TypeTheory.GroupoidInterpretationOfTypes public 

open import Categories.Reasoning public