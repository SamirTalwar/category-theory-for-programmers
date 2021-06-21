module Part1.Chapter07_Functors where

open import Level
open import Relation.Binary.PropositionalEquality hiding (Extensionality)

open import Part1.Chapter01_Category

record Functor {α β} (C D : Category α β) : Set (α ⊔ β) where
  field
    construct : Category.Object C → Category.Object D
    map : ∀ {a b : Category.Object C} → Category._⇒_ C a b → Category._⇒_ D (construct a) (construct b)

    map-id : ∀ {a : Category.Object C}
      → let open Category D in map (Category.id C {a}) ≈ id {construct a}
    composes : ∀ {a b c : Category.Object C} {g : Category._⇒_ C b c} {f : Category._⇒_ C a b}
      → let open Category D in map (Category._∘_ C g f) ≈ map g ∘ map f

infix 4 _-F->_
_-F->_ : ∀ {α β} (C D : Category α β) → Set (α ⊔ β)
_-F->_ = Functor

Endofunctor : ∀ {α β} (C : Category α β) → Set (α ⊔ β)
Endofunctor category = category -F-> category

module Id where
  open Part1.Chapter01_Category.Function

  functor : ∀ {ℓ} → Endofunctor (Function.category ℓ)
  functor =
    record
      { construct = id
      ; map = λ f x → f x
      ; map-id = refl
      ; composes = refl
      }

module Maybe where
  open import Axiom.Extensionality.Propositional
  open import Data.Maybe

  functor : ∀ {ℓ} → Extensionality _ _ → Endofunctor (Function.category ℓ)
  functor ext =
    record
      { construct = Maybe
      ; map = map
      ; map-id = ext λ{ nothing → refl ; (just x) → refl }
      ; composes = ext λ{ nothing → refl ; (just x) → refl }
      }

  -- not-a-functor : ∀ {ℓ} → Extensionality _ _ → (Function.category {ℓ}) -F-> (Function.category {ℓ})
  -- not-a-functor ext =
  --   record
  --     { construct = Maybe
  --     ; map = λ _ _ → nothing
  --     ; map-id = ext λ{ nothing → refl ; (just x) → {- cannot prove that: just x ≡ nothing -} }
  --     ; composes = ext λ{ nothing → refl ; (just x) → refl }
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
      ; map-id = ext map-id
      ; composes = ext composes
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
      ; map-id = refl
      ; composes = refl
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
      ; map-id = ext λ{ (const _) → refl }
      ; composes = ext λ{ (const _) → refl }
      }
