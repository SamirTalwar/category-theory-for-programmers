module Part1.Chapter09_FunctionTypes where

open import Axiom.Extensionality.Propositional
open import Data.Empty.Polymorphic
open import Data.Product
open import Data.Sum
open import Data.Unit.Polymorphic
open import Level
open import Relation.Binary.PropositionalEquality hiding (Extensionality)

open import Part1.Chapter01_Category
open import Part1.Chapter05_ProductsAndCoproducts
open import Part1.Chapter07_Functors
open import Part1.Chapter08_Functoriality

open Coproduct
open InitialObject
open Product
open TerminalObject

record FunctionObject {α β}
    (category : Category α β)
    (bifunctor : Bifunctor category category category)
    (A B : Category.Object category)
    : Set (α ⊔ β) where
  open Category category

  _××_ : (x y : Object) → Object
  x ×× y = Functor.construct bifunctor (x , y)

  field
    object : Category.Object category
    eval : object ×× A ⇒ B
    factorize : ∀ {Z : Object} → (g : Z ×× A ⇒ B) → ∃[ h ] (g ≈ eval ∘ Bifunctor.lmap bifunctor h)

record CartesianClosed {α β}
    (category : Category α β)
    : Set (α ⊔ β) where
  open Category category

  field
    bifunctor : Bifunctor category category category
    product : ∀ {A B : Object} → Product category A B
    function-object : ∀ {A B : Object} → FunctionObject category bifunctor A B
    terminal-object : TerminalObject category

record BicartesianClosed {α β}
    (category : Category α β)
    : Set (α ⊔ β) where
  open Category category

  field
    cartesian-closed : CartesianClosed category
    coproduct : ∀ {A B : Object} → Coproduct category A B
    initial-object : InitialObject category

set-is-bicartesian-closed : ∀ {ℓ} → Extensionality _ _ → BicartesianClosed (Function.category ℓ)
set-is-bicartesian-closed ext =
  record
    { cartesian-closed =
        record
          { bifunctor =
              record
                { construct = λ{ (A , B) → A × B }
                ; map = λ{ (f , g) (x , y) → f x , g y }
                ; law-map-id = refl
                ; law-composes = refl
                ; law-preserves-equality = λ{ (f , g) → cong₂ (λ{ f g (x , y) → f x , g y }) f g }
                }
          ; product = λ{ {A} {B} →
              record
                { product = A × B
                ; fst = proj₁
                ; snd = proj₂
                }
            }
          ; function-object = λ{ {A} {B} →
              record
                { object = A → B
                ; eval = λ{ (f , x) → f x }
                ; factorize = λ g → (λ z a → g (z , a)) , refl
                }
            }
          ; terminal-object =
              record
                { terminal = ⊤
                ; is-terminal = λ{ _ → tt }
                ; has-unique-morphisms = λ{ f g → refl }
                }
          }
    ; coproduct = λ{ {A} {B} →
        record
          { coproduct = A ⊎ B
          ; left = inj₁
          ; right = inj₂
          }
      }
    ; initial-object =
        record
          { initial = ⊥
          ; is-initial = λ{ () }
          ; has-unique-morphisms = λ{ f g → ext ⊥-elim }
          }
  }
