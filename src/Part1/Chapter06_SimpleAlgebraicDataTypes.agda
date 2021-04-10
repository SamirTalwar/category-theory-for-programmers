module Part1.Chapter06_SimpleAlgebraicDataTypes where

module Isomorphisms where
  open import Data.Bool
  open import Data.Maybe
  open import Data.Product
  open import Data.Sum
  open import Data.Unit
  open import Function using (_∘_)
  open import Relation.Binary.PropositionalEquality

  infix 4 _≈_

  record _≈_ {ℓ} (A B : Set ℓ) : Set ℓ where
    field
      to : A → B
      from : B → A
      from∘to≡id : ∀ (a : A) → (from ∘ to) a ≡ a
      to∘from≡id : ∀ (b : B) → (to ∘ from) b ≡ b

  maybe≈either : ∀ {A : Set} → Maybe A ≈ (⊤ ⊎ A)
  maybe≈either =
    record
      { to = λ{ nothing → inj₁ tt ; (just x) → inj₂ x }
      ; from = λ{ (inj₁ tt) → nothing ; (inj₂ y) → just y }
      ; from∘to≡id = λ{ nothing → refl ; (just x) → refl }
      ; to∘from≡id = λ{ (inj₁ tt) → refl ; (inj₂ y) → refl }
      }

  a+a≈2*a : ∀ {A : Set} → (A ⊎ A) ≈ (Bool × A)
  a+a≈2*a =
    record
      { to = λ{ (inj₁ x) → false , x ; (inj₂ y) → true , y }
      ; from = λ{ (false , x) → inj₁ x ; (true , y) → inj₂ y }
      ; from∘to≡id = λ{ (inj₁ x) → refl ; (inj₂ y) → refl }
      ; to∘from≡id = λ{ (false , x) → refl ; (true , y) → refl }
      }

module Pi where
  open import Data.Float

  π : Float
  π = acos 0.0 * 2.0

module ClosedShape where
  open import Data.Float

  open Pi

  -- Q2
  data Shape : Set where
    circle : Float → Shape
    rectangle : Float → Float → Shape
    -- Q4
    square : Float → Shape

  -- Q2
  area : Shape → Float
  area (circle radius) = π * radius * radius
  area (rectangle width height) = width * height
  -- Q4
  area (square width) = width * width

  -- Q3
  circumference : Shape → Float
  circumference (circle radius) = 2.0 * π * radius
  circumference (rectangle width height) = 2.0 * (width + height)
  -- Q4
  circumference (square width) = 4.0 * width

module OpenShape where
  open import Data.Float
  open import Data.Unit

  open Pi

  -- Q2
  record Shape : Set where
    field
      area : ⊤ → Float
      -- Q3
      circumference : ⊤ → Float

  -- Q2
  circle : Float → Shape
  circle radius =
    record
      { area = λ{ _ → π * radius * radius }
      -- Q3
      ; circumference = λ{ _ → 2.0 * π * radius }
      }

  -- Q2
  rectangle : Float → Float → Shape
  rectangle width height =
    record
      { area = λ{ _ → width * height }
      -- Q3
      ; circumference = λ{ _ → 2.0 * (width + height) }
      }

  -- Q4
  square : Float → Shape
  square width =
    record
      { area = λ{ _ → width * width }
      ; circumference = λ{ _ → 4.0 * width }
      }
