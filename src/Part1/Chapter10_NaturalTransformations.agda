module Part1.Chapter10_NaturalTransformations where

open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.Structures
import Relation.Binary.Reasoning.Setoid

open import Part1.Chapter01_Category
open import Part1.Chapter07_Functors as Functors

record NaturalTransformation {α β}
    {C D : Category {α} {β}}
    (F G : C -F-> D)
    : Set (α ⊔ β) where
  field
    transform-object : ∀ {x : Category.Object C} → let open Category D in Functor.construct F x ⇒ Functor.construct G x
    naturality-condition : ∀ {A B : Category.Object C} {f : Category._⇒_ C A B}
      → let open Category D in
        (Functor.map G f ∘ transform-object) ≈ (transform-object ∘ Functor.map F f)

module NaturalTransformationExamples where
  open import Axiom.Extensionality.Propositional
  open import Data.List
  open import Data.Maybe
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality hiding (Extensionality)
  open Relation.Binary.PropositionalEquality.≡-Reasoning

  list-to-maybe : ∀ {ℓ}
      (ext : Extensionality ℓ ℓ)
    → NaturalTransformation (Functors.List.functor ext) (Functors.Maybe.functor ext)
  list-to-maybe ext =
    record
      { transform-object = head
      ; naturality-condition = ext λ{ [] → refl ; (_ ∷ _) → refl }
      }

  length-to-const :
      (ext : Extensionality _ _)
    → NaturalTransformation (Functors.List.functor ext) (Functors.Const.functor ext ℕ)
  length-to-const ext =
    record
      { transform-object = length-const
      ; naturality-condition = ext naturality-condition
      }
      where
      open import Function using (_∘_)
      open Functors.Const
      length-const : ∀ {A : Set} → List A → Const ℕ A
      length-const [] = const 0
      length-const (_ ∷ xs) = const (ℕ.suc (un-const (length-const xs)))
      map-preserves-length : ∀ {A B : Set} (f : A → B) (xs : List A)
        → un-const (length-const xs) ≡ un-const (length-const (Data.List.map f xs))
      map-preserves-length f [] = refl
      map-preserves-length f (x ∷ xs) = cong ℕ.suc (map-preserves-length f xs)
      naturality-condition : ∀ {A B : Set} {f : A → B}
        → (xs : List A)
        → let open Category (Function.category {Level.zero}) in
          (Functors.Const.map f) (length-const xs) ≡ length-const (Data.List.map f xs)
      naturality-condition [] = refl
      naturality-condition {f = f} (x ∷ xs) =
        begin
          Functors.Const.map f (length-const (x ∷ xs))
        ≡⟨⟩
          const (ℕ.suc (un-const (length-const xs)))
        ≡⟨ cong (const ∘ ℕ.suc) (map-preserves-length f xs) ⟩
          const (ℕ.suc (un-const (length-const (Data.List.map f xs))))
        ≡⟨⟩
          length-const (Data.List.map f (x ∷ xs))
        ∎

  const-to-maybe : ∀ {C : Set}
    → (ext : Extensionality _ _)
    → NaturalTransformation (Functors.Const.functor ext C) (Functors.Maybe.functor ext)
  const-to-maybe ext =
    record
      { transform-object = scam
      ; naturality-condition = ext λ{ (const _) → refl }
      }
    where
    open Functors.Const
    open Functors.Maybe
    scam : ∀ {A C : Set} → Const C A → Maybe A
    scam (const _) = nothing

functor-category : ∀ {α} {β}
  → (C D : Category {α} {β})
  → (let open Category D in ∀ {A B} → IsEquivalence {A = A ⇒ B} _≈_)
  → (let open Category D in ∀ {A B C D} (f : A ⇒ B → C ⇒ D) {x y : A ⇒ B} → x ≈ y → f x ≈ f y)
  → Category {α ⊔ β} {α ⊔ β}
functor-category {α} {β} C D isEquivalence cong =
  let
    open Category D
    setoid : ∀ {A B : Object} → Setoid _ _
    setoid {A} {B} = record { Carrier = A ⇒ B ; _≈_ = _≈_ ; isEquivalence = isEquivalence }
  in
  record
    { Object = C -F-> D
    ; _⇒_ = NaturalTransformation
    ; _≈_ = λ f g → Lift (α ⊔ β) (NaturalTransformation.transform-object f ≈ NaturalTransformation.transform-object g)
    ; id = λ{ {F} →
        record
          { transform-object = id
          ; naturality-condition = λ{ {f = f} →
              let
                open Setoid setoid
                open Relation.Binary.Reasoning.Setoid setoid
              in
              begin
                Functor.map F f ∘ id
              ≈⟨ law-identityʳ (Functor.map F f) ⟩
                Functor.map F f
              ≈⟨ sym (law-identityˡ (Functor.map F f)) ⟩
                id ∘ Functor.map F f
              ∎
            }
          }
      }
    ; _∘_ = λ {A} {B} {C} g f →
        record
          { transform-object = NaturalTransformation.transform-object g ∘ NaturalTransformation.transform-object f
          ; naturality-condition = λ{ {f = morphism} →
              let
                open Setoid setoid
                open Relation.Binary.Reasoning.Setoid setoid
              in
              begin
                Functor.map C morphism ∘ (NaturalTransformation.transform-object g ∘ NaturalTransformation.transform-object f)
              ≈⟨ law-associative (Functor.map C morphism) (NaturalTransformation.transform-object g) (NaturalTransformation.transform-object f) ⟩
                (Functor.map C morphism ∘ NaturalTransformation.transform-object g) ∘ NaturalTransformation.transform-object f
              ≈⟨ cong (_∘ NaturalTransformation.transform-object f) (NaturalTransformation.naturality-condition g) ⟩
                (NaturalTransformation.transform-object g ∘ Functor.map B morphism) ∘ NaturalTransformation.transform-object f
              ≈⟨ sym (law-associative (NaturalTransformation.transform-object g) (Functor.map B morphism) (NaturalTransformation.transform-object f)) ⟩
                NaturalTransformation.transform-object g ∘ (Functor.map B morphism ∘ NaturalTransformation.transform-object f)
              ≈⟨ cong (NaturalTransformation.transform-object g ∘_) (NaturalTransformation.naturality-condition f) ⟩
                NaturalTransformation.transform-object g ∘ (NaturalTransformation.transform-object f ∘ Functor.map A morphism)
              ≈⟨ law-associative (NaturalTransformation.transform-object g) (NaturalTransformation.transform-object f) (Functor.map A morphism) ⟩
                (NaturalTransformation.transform-object g ∘ NaturalTransformation.transform-object f) ∘ Functor.map A morphism
              ∎
            }
          }
    ; law-identityˡ = λ f → lift (law-identityˡ (NaturalTransformation.transform-object f))
    ; law-identityʳ = λ f → lift (law-identityʳ (NaturalTransformation.transform-object f))
    ; law-associative = λ h g f → lift (law-associative (NaturalTransformation.transform-object h) (NaturalTransformation.transform-object g) (NaturalTransformation.transform-object f))
    }
