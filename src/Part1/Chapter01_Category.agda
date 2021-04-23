module Part1.Chapter01_Category where

open import Level

record Category {α β : Level}
  : Set (suc α ⊔ suc β) where
  infix 10 _⇒_
  infixr 9 _∘_
  infix 4 _≈_

  field
    Object : Set α
    _⇒_ : Object → Object → Set β
    _≈_ : {A B : Object} → (A ⇒ B) → (A ⇒ B) → Set β

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

module Function where
  open import Relation.Binary.PropositionalEquality

  id : ∀ {ℓ} {A : Set ℓ} → A → A
  id x = x

  _∘_ : ∀ {ℓ} {A B C : Set ℓ} → (B → C) → (A → B) → (A → C)
  (g ∘ f) x = g (f x)

  category : ∀ {ℓ} → Category {suc ℓ} {ℓ}
  category {ℓ} =
    record
      { Object = Set ℓ
      ; _⇒_ = λ A B → A → B
      ; _≈_ = _≡_

      ; id = id
      ; _∘_ = _∘_
      ; law-identityˡ = λ f → refl
      ; law-identityʳ = λ f → refl
      ; law-associative = λ h g f → refl
      }
