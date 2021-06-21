module Part1.Chapter10_NaturalTransformations where

open import Data.Product
open import Level
open import Relation.Binary hiding (_⇒_)
import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid

open import Part1.Chapter01_Category
open import Part1.Chapter07_Functors as Functors
open import Part1.Chapter08_Functoriality
open import Part1.Chapter09_FunctionTypes

record NaturalTransformation {α β}
    {C D : Category α β}
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
  open Relation.Binary.PropositionalEquality hiding (Extensionality)
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
        → let open Category (Function.category Level.zero) in
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

functor-category : ∀ {α} {β} → (C D : Category α β) → Category (α ⊔ β) (α ⊔ β)
functor-category {α} {β} C D =
  let open Category D in
  record
    { Object = C -F-> D
    ; _⇒_ = NaturalTransformation
    ; _≈_ = λ f g → ∀ {x : Category.Object C} → Lift (α ⊔ β) (NaturalTransformation.transform-object f {x} ≈ NaturalTransformation.transform-object g {x})
    ; isEquivalence =
        record
          { refl = lift refl
          ; sym = λ{ x → lift (sym (lower x)) }
          ; trans = λ{ f g → lift (trans (lower f) (lower g)) }
          }
    ; id = λ{ {F} →
        record
          { transform-object = id
          ; naturality-condition = λ{ {f = f} →
              let open Relation.Binary.Reasoning.Setoid setoid in
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
              let open Relation.Binary.Reasoning.Setoid setoid in
              begin
                Functor.map C morphism ∘ (NaturalTransformation.transform-object g ∘ NaturalTransformation.transform-object f)
              ≈⟨ law-associative (Functor.map C morphism) (NaturalTransformation.transform-object g) (NaturalTransformation.transform-object f) ⟩
                (Functor.map C morphism ∘ NaturalTransformation.transform-object g) ∘ NaturalTransformation.transform-object f
              ≈⟨ NaturalTransformation.naturality-condition g ⟩∘⟨ refl ⟩
                (NaturalTransformation.transform-object g ∘ Functor.map B morphism) ∘ NaturalTransformation.transform-object f
              ≈⟨ sym (law-associative (NaturalTransformation.transform-object g) (Functor.map B morphism) (NaturalTransformation.transform-object f)) ⟩
                NaturalTransformation.transform-object g ∘ (Functor.map B morphism ∘ NaturalTransformation.transform-object f)
              ≈⟨ refl ⟩∘⟨ NaturalTransformation.naturality-condition f ⟩
                NaturalTransformation.transform-object g ∘ (NaturalTransformation.transform-object f ∘ Functor.map A morphism)
              ≈⟨ law-associative (NaturalTransformation.transform-object g) (NaturalTransformation.transform-object f) (Functor.map A morphism) ⟩
                (NaturalTransformation.transform-object g ∘ NaturalTransformation.transform-object f) ∘ Functor.map A morphism
              ∎
            }
          }
    ; law-identityˡ = λ f → lift (law-identityˡ (NaturalTransformation.transform-object f))
    ; law-identityʳ = λ f → lift (law-identityʳ (NaturalTransformation.transform-object f))
    ; law-associative = λ h g f → lift (law-associative (NaturalTransformation.transform-object h) (NaturalTransformation.transform-object g) (NaturalTransformation.transform-object f))
    ; _⟩∘⟨_ = λ g f → lift (lower g ⟩∘⟨ lower f)
    }

natural-transformation-id : ∀ {α β} {C D : Category α β}
  → (F : C -F-> D)
  → NaturalTransformation F F
natural-transformation-id {C = C} {D = D} F =
  record
    { transform-object = Category.id D
    ; naturality-condition = λ {A} {B} {f} →
        let
          open Category D
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

record NaturalIsomorphism {α β} {C D : Category α β} (F G : C -F-> D) : Set (α ⊔ β) where
  field
    f : NaturalTransformation F G
    g : NaturalTransformation G F
    isomorphicˡ : ∀ {x : Category.Object C} →
      let open Category D in NaturalTransformation.transform-object g {x} ∘ NaturalTransformation.transform-object f {x} ≈ id
    isomorphicʳ : ∀ {x : Category.Object C} →
      let open Category D in NaturalTransformation.transform-object f {x} ∘ NaturalTransformation.transform-object g {x} ≈ id

functor-setoid : ∀ {α β} → (C D : Category α β) → Setoid _ _
functor-setoid C D =
  record
    { Carrier = C -F-> D
    ; _≈_ = NaturalIsomorphism
    ; isEquivalence = record
        { refl = λ {F} →
            let open Category D in
            record
              { f = natural-transformation-id F
              ; g = natural-transformation-id F
              ; isomorphicˡ = Category.law-identityˡ D id
              ; isomorphicʳ = Category.law-identityʳ D id
              }
        ; sym = λ iso →
            let open NaturalIsomorphism iso in
            record
              { f = g
              ; g = f
              ; isomorphicˡ = isomorphicʳ
              ; isomorphicʳ = isomorphicˡ
              }
        ; trans = λ isoA isoB →
            record
              { f = Category._∘_ (functor-category C D) (NaturalIsomorphism.f isoB) (NaturalIsomorphism.f isoA)
              ; g = Category._∘_ (functor-category C D) (NaturalIsomorphism.g isoA) (NaturalIsomorphism.g isoB)
              ; isomorphicˡ =
                  let
                    k = (NaturalTransformation.transform-object (NaturalIsomorphism.g isoA))
                    h = (NaturalTransformation.transform-object (NaturalIsomorphism.g isoB))
                    g = (NaturalTransformation.transform-object (NaturalIsomorphism.f isoB))
                    f = (NaturalTransformation.transform-object (NaturalIsomorphism.f isoA))
                    open Category D
                    open Relation.Binary.Reasoning.Setoid setoid
                  in
                  begin
                    (k ∘ h) ∘ (g ∘ f)
                  ≈⟨ law-associative (k ∘ h) g f ⟩
                    ((k ∘ h) ∘ g) ∘ f
                  ≈⟨ sym (law-associative k h g) ⟩∘⟨ refl ⟩
                    (k ∘ (h ∘ g)) ∘ f
                  ≈⟨ (refl ⟩∘⟨ NaturalIsomorphism.isomorphicˡ isoB) ⟩∘⟨ refl ⟩
                    (k ∘ id) ∘ f
                  ≈⟨ law-identityʳ k ⟩∘⟨ refl ⟩
                    k ∘ f
                  ≈⟨ NaturalIsomorphism.isomorphicˡ isoA ⟩
                    id
                  ∎
              ; isomorphicʳ =
                  let
                    k = (NaturalTransformation.transform-object (NaturalIsomorphism.f isoB))
                    h = (NaturalTransformation.transform-object (NaturalIsomorphism.f isoA))
                    g = (NaturalTransformation.transform-object (NaturalIsomorphism.g isoA))
                    f = (NaturalTransformation.transform-object (NaturalIsomorphism.g isoB))
                    open Category D
                    open Relation.Binary.Reasoning.Setoid setoid
                  in
                  begin
                    (k ∘ h) ∘ (g ∘ f)
                  ≈⟨ law-associative (k ∘ h) g f ⟩
                    ((k ∘ h) ∘ g) ∘ f
                  ≈⟨ sym (law-associative k h g) ⟩∘⟨ refl ⟩
                    (k ∘ (h ∘ g)) ∘ f
                  ≈⟨ (refl ⟩∘⟨ NaturalIsomorphism.isomorphicʳ isoA) ⟩∘⟨ refl ⟩
                    (k ∘ id) ∘ f
                  ≈⟨ law-identityʳ k ⟩∘⟨ refl ⟩
                    k ∘ f
                  ≈⟨ NaturalIsomorphism.isomorphicʳ isoB ⟩
                    id
                  ∎
              }
        }
      }

compose-functors : ∀ {α β} {C D E : Category α β} → D -F-> E → C -F-> D → C -F-> E
compose-functors {_} {_} {C} {D} {E} DE CD =
  let open Function in
  record
    { construct = Functor.construct DE ∘ Functor.construct CD
    ; map = Functor.map DE ∘ Functor.map CD
    ; map-id =
        let
          open Category E
          open Relation.Binary.Reasoning.Setoid setoid
        in
        begin
          Functor.map DE (Functor.map CD (Category.id C))
        ≈⟨ Functor.preserves-equality DE (Functor.map-id CD) ⟩
          Functor.map DE (Category.id D)
        ≈⟨ Functor.map-id DE ⟩
          Category.id E
        ∎
    ; composes = λ {_} {_} {_} {g} {f} →
        let
          module C = Category C
          module D = Category D
          module E = Category E
          open Relation.Binary.Reasoning.Setoid E.setoid
        in
        begin
          Functor.map DE (Functor.map CD (g C.∘ f))
        ≈⟨ Functor.preserves-equality DE (Functor.composes CD) ⟩
          Functor.map DE (Functor.map CD g D.∘ Functor.map CD f)
        ≈⟨ Functor.composes DE ⟩
          Functor.map DE (Functor.map CD g) E.∘ Functor.map DE (Functor.map CD f)
        ∎
    ; preserves-equality = λ {_} {_} {f} {g} f≡g →
        let
          module C = Category C
          module D = Category D
          module E = Category E
          open Relation.Binary.Reasoning.Setoid E.setoid
        in
        begin
          (Functor.map DE (Functor.map CD f))
        ≈⟨ Functor.preserves-equality DE (Functor.preserves-equality CD f≡g) ⟩
          (Functor.map DE (Functor.map CD g))
        ∎
    }
