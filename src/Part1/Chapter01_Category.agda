module Part1.Chapter01_Category where

open import Level
open import Relation.Binary hiding (_⇒_)

record Category (α β : Level) : Set (suc α ⊔ suc β) where
  infix 10 _⇒_
  infixr 9 _∘_ _⟩∘⟨_
  infix 4 _≈_

  field
    Object : Set α
    _⇒_ : Object → Object → Set β

    _≈_ : ∀ {A B : Object} → Rel (A ⇒ B) β
    isEquivalence : ∀ {A B : Object} → IsEquivalence {A = A ⇒ B} _≈_

  refl : ∀ {A B : Object} → Reflexive (_≈_ {A} {B})
  refl {A} {B} = IsEquivalence.refl (isEquivalence {A} {B})
  sym : ∀ {A B : Object} → Symmetric (_≈_ {A} {B})
  sym {A} {B} = IsEquivalence.sym (isEquivalence {A} {B})
  trans : ∀ {A B : Object} → Transitive (_≈_ {A} {B})
  trans {A} {B} = IsEquivalence.trans (isEquivalence {A} {B})
  setoid : ∀ {A B : Object} → Setoid β _
  setoid {A} {B} = record { Carrier = A ⇒ B ; _≈_ = _≈_ ; isEquivalence = isEquivalence {A} {B} }

  field
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

    _⟩∘⟨_ : ∀ {A B C} {g₁ g₂ : B ⇒ C} {f₁ f₂ : A ⇒ B}
      → g₁ ≈ g₂
      → f₁ ≈ f₂
      → g₁ ∘ f₁ ≈ g₂ ∘ f₂

Category₀ = Category Level.zero Level.zero

module Function where
  import Function as F
  open import Relation.Binary.PropositionalEquality hiding (Extensionality)
  open Relation.Binary.PropositionalEquality.≡-Reasoning

  id : ∀ {ℓ} {A : Set ℓ} → A → A
  id = F.id

  _∘_ : ∀ {ℓ} {A B C : Set ℓ} → (B → C) → (A → B) → A → C
  _∘_ = F._∘′_

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
      ; _⟩∘⟨_ = cong₂ _∘_
      }
