module Part1.Chapter07_Functors where

open import Level
open import Relation.Binary.PropositionalEquality hiding (Extensionality)

open import Part1.Chapter01_Category

record Functor {α β} (C D : Category α β) : Set (α ⊔ β) where
  private module C = Category C
  private module D = Category D

  field
    construct : C.Object → D.Object
    map : ∀ {a b : C.Object} → a C.⇒ b → construct a D.⇒ construct b

    law-map-id : ∀ {a : C.Object}
      → map (C.id {a}) D.≈ D.id {construct a}
    law-composes : ∀ {a b c : C.Object} {g : b C.⇒ c} {f : a C.⇒ b}
      → map (g C.∘ f) D.≈ map g D.∘ map f
    law-preserves-equality : ∀ {a b : C.Object} {f g : a C.⇒ b}
      → f C.≈ g
      → map f D.≈ map g

infix 4 _-F->_
_-F->_ : ∀ {α β} (C D : Category α β) → Set (α ⊔ β)
_-F->_ = Functor

Endofunctor : ∀ {α β} (C : Category α β) → Set (α ⊔ β)
Endofunctor category = category -F-> category

module Id where
  open Part1.Chapter01_Category.Function

  functor : ∀ {α β} → (category : Category α β) → Endofunctor category
  functor category =
    record
      { construct = id
      ; map = id
      ; law-map-id = Category.refl category
      ; law-composes = Category.refl category
      ; law-preserves-equality = id
      }

module Maybe where
  open import Axiom.Extensionality.Propositional
  open import Data.Maybe

  functor : ∀ {ℓ} → Extensionality _ _ → Endofunctor (Function.category ℓ)
  functor ext =
    record
      { construct = Maybe
      ; map = map
      ; law-map-id = ext λ{ nothing → refl ; (just x) → refl }
      ; law-composes = ext λ{ nothing → refl ; (just x) → refl }
      ; law-preserves-equality = λ{ refl → refl }
      }

  -- not-a-functor : ∀ {ℓ} → Extensionality _ _ → (Function.category ℓ) -F-> (Function.category ℓ)
  -- not-a-functor ext =
  --   record
  --     { construct = Maybe
  --     ; map = λ _ _ → nothing
  --     ; law-map-id = ext λ{ nothing → refl ; (just x) → {!!} {- cannot prove that: just x ≡ nothing -} }
  --     ; law-composes = ext λ{ nothing → refl ; (just x) → refl }
  --     ; law-preserves-equality = λ{ refl → refl }
  --     }

module List where
  open import Axiom.Extensionality.Propositional
  open import Data.List
  open Part1.Chapter01_Category.Function

  functor : ∀ {ℓ} → Extensionality _ _ → Endofunctor (Function.category ℓ)
  functor ext =
    record
      { construct = List
      ; map = map
      ; law-map-id = ext map-id
      ; law-composes = ext composes
      ; law-preserves-equality = λ{ refl → refl }
      }
    where
    map-id : ∀ {ℓ} {A : Set ℓ} → (x : List A) → map id x ≡ x
    map-id [] = refl
    map-id (x ∷ xs) = cong (x ∷_) (map-id xs)
    composes : ∀ {ℓ} {A B C : Set ℓ} {g : B → C} {f : A → B} → (x : List A) → map (g ∘ f) x ≡ map g (map f x)
    composes [] = refl
    composes {g = g} {f = f} (x ∷ xs) = cong (g (f x) ∷_) (composes xs)

module Reader where
  open Part1.Chapter01_Category.Function

  functor : ∀ {ℓ} → (A : Set ℓ) → Endofunctor (Function.category ℓ)
  functor A =
    record
      { construct = (λ B → A → B)
      ; map = _∘_
      ; law-map-id = refl
      ; law-composes = refl
      ; law-preserves-equality = λ{ refl → refl }
      }

module Const where
  open import Axiom.Extensionality.Propositional
  open Part1.Chapter01_Category.Function

  data Const {ℓ} (C A : Set ℓ) : Set ℓ where
    const : C → Const C A

  un-const : ∀ {ℓ} {C A : Set ℓ} → Const C A → C
  un-const (const c) = c

  map : ∀ {ℓ} {C A B : Set ℓ} → (A → B) → Const C A → Const C B
  map _ (const c) = const c

  functor : ∀ {ℓ} → Extensionality _ _ → (C : Set ℓ) → Endofunctor (Function.category ℓ)
  functor ext C =
    record
      { construct = Const C
      ; map = map
      ; law-map-id = ext λ{ (const _) → refl }
      ; law-composes = ext λ{ (const _) → refl }
      ; law-preserves-equality = λ{ refl → refl }
      }
