module Part1.Chapter01_Category where

open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.Definitions
open import Relation.Binary.Structures

record Category (α β : Level) : Set (suc α ⊔ suc β) where
  infix 10 _⇒_
  infixr 9 _∘_
  infix 4 _≈_

  field
    Object : Set α
    _⇒_ : Object → Object → Set β
    _≈_ : ∀ {A B : Object} → (A ⇒ B) → (A ⇒ B) → Set β
    isEquivalence : ∀ {A B : Object} → IsEquivalence {A = A ⇒ B} _≈_

    id : ∀ {A : Object} → A ⇒ A
    _∘_ : ∀ {A B C : Object} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

    law-identityˡ : ∀ {A B : Object} (f : A ⇒ B)
      → (id ∘ f) ≈ f
    law-identityʳ : ∀ {A B : Object} (f : A ⇒ B)
      → (f ∘ id) ≈ f
    law-associative : ∀ {A B C D : Object}
      → (h : C ⇒ D)
      → (g : B ⇒ C)
      → (f : A ⇒ B)
      → (h ∘ (g ∘ f)) ≈ ((h ∘ g) ∘ f)

  refl : ∀ {A B : Object} → Reflexive (_≈_ {A} {B})
  refl = IsEquivalence.refl isEquivalence
  sym : ∀ {A B : Object} → Symmetric (_≈_ {A} {B})
  sym = IsEquivalence.sym isEquivalence
  trans : ∀ {A B : Object} → Transitive (_≈_ {A} {B})
  trans = IsEquivalence.trans isEquivalence
  setoid : ∀ {A B : Object} → Setoid _ _
  setoid {A} {B} = record { Carrier = A ⇒ B ; _≈_ = _≈_ ; isEquivalence = isEquivalence }

Category₀ = Category Level.zero Level.zero

module Function where
  open import Relation.Binary.PropositionalEquality

  id : ∀ {ℓ} {A : Set ℓ} → A → A
  id x = x

  _∘_ : ∀ {ℓ} {A B C : Set ℓ} → (B → C) → (A → B) → (A → C)
  (g ∘ f) x = g (f x)

  category : ∀ (ℓ : Level) → Category (suc ℓ) ℓ
  category ℓ =
    record
      { Object = Set ℓ
      ; _⇒_ = λ A B → A → B
      ; _≈_ = _≡_
      ; isEquivalence = isEquivalence

      ; id = id
      ; _∘_ = _∘_
      ; law-identityˡ = λ f → refl
      ; law-identityʳ = λ f → refl
      ; law-associative = λ h g f → refl
      }
