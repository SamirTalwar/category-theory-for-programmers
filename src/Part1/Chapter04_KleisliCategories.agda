module Part1.Chapter04_KleisliCategories where

open import Part1.Chapter01_Category

module PartialFunctions where
  open import Axiom.Extensionality.Propositional
  open import Relation.Binary.PropositionalEquality hiding (Extensionality)

  data Optional (A : Set) : Set where
    none : Optional A
    some : (value : A) → Optional A

  _>=>_ : ∀ {A B C : Set}
    → (A → Optional B)
    → (B → Optional C)
    → (A → Optional C)
  (a >=> b) input with a input
  ... | none = none
  ... | some value = b value

  _<=<_ : ∀ {A B C : Set}
    → (B → Optional C)
    → (A → Optional B)
    → (A → Optional C)
  b <=< a = a >=> b

  category : Extensionality _ _ → Category _ _
  category ext = record
                   { Object = Set
                   ; _⇒_ = λ A B → A → Optional B
                   ; _≈_ = _≡_
                   ; isEquivalence = isEquivalence
                   ; id = id
                   ; _∘_ = _<=<_
                   ; law-identityˡ = λ{ f → ext (law-identityˡ f) }
                   ; law-identityʳ = λ{ f → ext (law-identityʳ f) }
                   ; law-associative = λ{ h g f → ext (law-associative h g f) }
                   }
    where
    id : ∀ {A} → A → Optional A
    id = some
    law-identityˡ : ∀ {A B} → (f : A → Optional B) → (x : A) → (id <=< f) x ≡ f x
    law-identityˡ f x with f x
    ... | none = refl
    ... | some value = refl
    law-identityʳ : ∀ {A B} → (f : A → Optional B) → (x : A) → (f <=< id) x ≡ f x
    law-identityʳ f x with f x
    ... | none = refl
    ... | some value = refl
    law-associative : ∀ {A B C D}
      → (h : C → Optional D)
      → (g : B → Optional C)
      → (f : A → Optional B)
      → (x : A)
      → (h <=< (g <=< f)) x ≡ ((h <=< g) <=< f) x
    law-associative h g f x with f x
    ... | none = refl
    ... | some y with g y
    ...     | none = refl
    ...     | some value = refl
