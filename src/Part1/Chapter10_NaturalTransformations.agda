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
        ≈⟨ ilaw-identityʳ ⟩
          Functor.map F f
        ≈⟨ sym ilaw-identityˡ ⟩
          id ∘ Functor.map F f
        ∎
    }

compose-natural-transformations : ∀ {α β} {C D : Category α β} {F G H : C -F-> D}
  → NaturalTransformation G H
  → NaturalTransformation F G
  → NaturalTransformation F H
compose-natural-transformations {_} {_} {C} {D} {F} {G} {H} g f =
  let open Category D in
  record
    { transform-object = NaturalTransformation.transform-object g ∘ NaturalTransformation.transform-object f
    ; naturality-condition = λ{ {f = morphism} →
        let open Relation.Binary.Reasoning.Setoid setoid in
        begin
          Functor.map H morphism ∘ (NaturalTransformation.transform-object g ∘ NaturalTransformation.transform-object f)
        ≈⟨ ilaw-associative ⟩
          (Functor.map H morphism ∘ NaturalTransformation.transform-object g) ∘ NaturalTransformation.transform-object f
        ≈⟨ NaturalTransformation.naturality-condition g ⟩∘⟨ refl ⟩
          (NaturalTransformation.transform-object g ∘ Functor.map G morphism) ∘ NaturalTransformation.transform-object f
        ≈⟨ sym ilaw-associative ⟩
          NaturalTransformation.transform-object g ∘ (Functor.map G morphism ∘ NaturalTransformation.transform-object f)
        ≈⟨ refl ⟩∘⟨ NaturalTransformation.naturality-condition f ⟩
          NaturalTransformation.transform-object g ∘ (NaturalTransformation.transform-object f ∘ Functor.map F morphism)
        ≈⟨ ilaw-associative ⟩
          (NaturalTransformation.transform-object g ∘ NaturalTransformation.transform-object f) ∘ Functor.map F morphism
        ∎
      }
    }

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
    ; id = λ {F} → natural-transformation-id F
    ; _∘_ = compose-natural-transformations
    ; law-identityˡ = λ f → lift (law-identityˡ (NaturalTransformation.transform-object f))
    ; law-identityʳ = λ f → lift (law-identityʳ (NaturalTransformation.transform-object f))
    ; law-associative = λ h g f → lift (law-associative (NaturalTransformation.transform-object h) (NaturalTransformation.transform-object g) (NaturalTransformation.transform-object f))
    ; _⟩∘⟨_ = λ g f → lift (lower g ⟩∘⟨ lower f)
    }

record NaturalIsomorphism {α β} {C D : Category α β} (F G : C -F-> D) : Set (α ⊔ β) where
  field
    f : NaturalTransformation F G
    g : NaturalTransformation G F
    isomorphicˡ : ∀ {x : Category.Object C} →
      let open Category D in NaturalTransformation.transform-object g {x} ∘ NaturalTransformation.transform-object f {x} ≈ id
    isomorphicʳ : ∀ {x : Category.Object C} →
      let open Category D in NaturalTransformation.transform-object f {x} ∘ NaturalTransformation.transform-object g {x} ≈ id

functor-setoid : ∀ {α β} → (C D : Category α β) → Setoid (α ⊔ β) (α ⊔ β)
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
                  ≈⟨ ilaw-associative ⟩
                    ((k ∘ h) ∘ g) ∘ f
                  ≈⟨ sym ilaw-associative ⟩∘⟨ refl ⟩
                    (k ∘ (h ∘ g)) ∘ f
                  ≈⟨ (refl ⟩∘⟨ NaturalIsomorphism.isomorphicˡ isoB) ⟩∘⟨ refl ⟩
                    (k ∘ id) ∘ f
                  ≈⟨ ilaw-identityʳ ⟩∘⟨ refl ⟩
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
                  ≈⟨ ilaw-associative ⟩
                    ((k ∘ h) ∘ g) ∘ f
                  ≈⟨ sym ilaw-associative ⟩∘⟨ refl ⟩
                    (k ∘ (h ∘ g)) ∘ f
                  ≈⟨ (refl ⟩∘⟨ NaturalIsomorphism.isomorphicʳ isoA) ⟩∘⟨ refl ⟩
                    (k ∘ id) ∘ f
                  ≈⟨ ilaw-identityʳ ⟩∘⟨ refl ⟩
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
    ; law-map-id =
        let
          open Category E
          open Relation.Binary.Reasoning.Setoid setoid
        in
        begin
          Functor.map DE (Functor.map CD (Category.id C))
        ≈⟨ Functor.law-preserves-equality DE (Functor.law-map-id CD) ⟩
          Functor.map DE (Category.id D)
        ≈⟨ Functor.law-map-id DE ⟩
          Category.id E
        ∎
    ; law-composes = λ {_} {_} {_} {g} {f} →
        let
          module C = Category C
          module D = Category D
          module E = Category E
          open Relation.Binary.Reasoning.Setoid E.setoid
        in
        begin
          Functor.map DE (Functor.map CD (g C.∘ f))
        ≈⟨ Functor.law-preserves-equality DE (Functor.law-composes CD) ⟩
          Functor.map DE (Functor.map CD g D.∘ Functor.map CD f)
        ≈⟨ Functor.law-composes DE ⟩
          Functor.map DE (Functor.map CD g) E.∘ Functor.map DE (Functor.map CD f)
        ∎
    ; law-preserves-equality = λ {_} {_} {f} {g} f≡g →
        let
          module C = Category C
          module D = Category D
          module E = Category E
          open Relation.Binary.Reasoning.Setoid E.setoid
        in
        begin
          (Functor.map DE (Functor.map CD f))
        ≈⟨ Functor.law-preserves-equality DE (Functor.law-preserves-equality CD f≡g) ⟩
          (Functor.map DE (Functor.map CD g))
        ∎
    }

functors-are-associative : ∀ {α β} {C D E F : Category α β}
  → (h : E -F-> F) (g : D -F-> E) (f : C -F-> D)
  → Setoid._≈_ (functor-setoid C F) (compose-functors h (compose-functors g f)) (compose-functors (compose-functors h g) f)
functors-are-associative {_} {_} {C} {D} {E} {F} h g f =
  record
    { f =
        record
          { transform-object = Category.id F
          ; naturality-condition = NaturalTransformation.naturality-condition id
          }
    ; g =
        record
          { transform-object = Category.id F
          ; naturality-condition = NaturalTransformation.naturality-condition id
          }
    ; isomorphicˡ = Category.law-identityˡ F (NaturalTransformation.transform-object id)
    ; isomorphicʳ = Category.law-identityʳ F (NaturalTransformation.transform-object id)
    }
  where
  id = natural-transformation-id (compose-functors h (compose-functors g f))

cat : ∀ (α β : Level) → Category (suc α ⊔ suc β) (α ⊔ β)
cat α β =
  record
    { Object = Category α β
    ; _⇒_ = Functor
    ; _≈_ = λ {C} {D} → Setoid._≈_ (functor-setoid C D)
    ; isEquivalence = λ {C} {D} → Setoid.isEquivalence (functor-setoid C D)
    ; id = λ {C} → Functors.Id.functor C
    ; _∘_ = compose-functors
    ; law-identityˡ = λ {C} {D} f →
        record
          { f =
              record
                { transform-object = NaturalTransformation.transform-object (natural-transformation-id f)
                ; naturality-condition = NaturalTransformation.naturality-condition (natural-transformation-id f)
                }
          ; g =
              record
                { transform-object = NaturalTransformation.transform-object (natural-transformation-id f)
                ; naturality-condition = NaturalTransformation.naturality-condition (natural-transformation-id f)
                }
          ; isomorphicˡ = Category.law-identityˡ D (Category.id D)
          ; isomorphicʳ = Category.law-identityʳ D (Category.id D)
          }
    ; law-identityʳ = λ {C} {D} f →
        record
          { f =
              record
                { transform-object = NaturalTransformation.transform-object (natural-transformation-id f)
                ; naturality-condition = NaturalTransformation.naturality-condition (natural-transformation-id f)
                }
          ; g =
              record
                { transform-object = NaturalTransformation.transform-object (natural-transformation-id f)
                ; naturality-condition = NaturalTransformation.naturality-condition (natural-transformation-id f)
                }
          ; isomorphicˡ = Category.law-identityˡ D (Category.id D)
          ; isomorphicʳ = Category.law-identityʳ D (Category.id D)
          }
    ; law-associative = functors-are-associative
    ; _⟩∘⟨_ = λ {A} {B} {C} {g₁} {g₂} {f₁} {f₂} g≈g f≈f →
        let open Category C in
        record
          { f =
              record
                { transform-object =
                    NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                      ∘ Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f))
                ; naturality-condition = λ {_} {_} {f} →
                    let open Relation.Binary.Reasoning.Setoid setoid in
                    begin
                      Functor.map (compose-functors g₂ f₂) f
                        ∘ (NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                          ∘ Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f)))
                    ≈⟨ ilaw-associative ⟩
                      (Functor.map (compose-functors g₂ f₂) f
                          ∘ NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g))
                        ∘ Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f))
                    ≈⟨ NaturalTransformation.naturality-condition (NaturalIsomorphism.f g≈g) ⟩∘⟨ refl ⟩
                      (NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                          ∘ Functor.map (compose-functors g₁ f₂) f)
                        ∘ Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f))
                    ≈⟨ sym ilaw-associative ⟩
                      NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                        ∘ (Functor.map (compose-functors g₁ f₂) f
                          ∘ Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f)))
                    ≈⟨ refl ⟩
                      NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                        ∘ (Functor.map g₁ (Functor.map f₂ f)
                          ∘ Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f)))
                    ≈⟨ refl ⟩∘⟨ sym (Functor.law-composes g₁) ⟩
                      NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                        ∘ Functor.map g₁ (Category._∘_ B (Functor.map f₂ f) (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f)))
                    ≈⟨ refl ⟩∘⟨ Functor.law-preserves-equality g₁ (NaturalTransformation.naturality-condition (NaturalIsomorphism.f f≈f)) ⟩
                      NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                        ∘ Functor.map g₁ (Category._∘_ B (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f)) (Functor.map f₁ f))
                    ≈⟨ refl ⟩∘⟨ Functor.law-composes g₁ ⟩
                      NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                        ∘ (Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f))
                          ∘ Functor.map g₁ (Functor.map f₁ f))
                    ≈⟨ refl ⟩
                      NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                        ∘ (Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f))
                          ∘ Functor.map (compose-functors g₁ f₁) f)
                    ≈⟨ ilaw-associative ⟩
                      (NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                          ∘ Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f)))
                        ∘ Functor.map (compose-functors g₁ f₁) f
                    ∎
                }
          ; g =
              record
                { transform-object =
                    NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                      ∘ Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f))
                ; naturality-condition = λ {_} {_} {f} →
                    let open Relation.Binary.Reasoning.Setoid setoid in
                    begin
                      Functor.map (compose-functors g₁ f₁) f
                        ∘ (NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                          ∘ Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f)))
                    ≈⟨ ilaw-associative ⟩
                      (Functor.map (compose-functors g₁ f₁) f
                          ∘ NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g))
                        ∘ Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f))
                    ≈⟨ NaturalTransformation.naturality-condition (NaturalIsomorphism.g g≈g) ⟩∘⟨ refl ⟩
                      (NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                          ∘ Functor.map (compose-functors g₂ f₁) f)
                        ∘ Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f))
                    ≈⟨ sym ilaw-associative ⟩
                      NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                        ∘ (Functor.map (compose-functors g₂ f₁) f
                          ∘ Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f)))
                    ≈⟨ refl ⟩
                      NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                        ∘ (Functor.map g₂ (Functor.map f₁ f)
                          ∘ Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f)))
                    ≈⟨ refl ⟩∘⟨ sym (Functor.law-composes g₂) ⟩
                      NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                        ∘ Functor.map g₂ (Category._∘_ B (Functor.map f₁ f) (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f)))
                    ≈⟨ refl ⟩∘⟨ Functor.law-preserves-equality g₂ (NaturalTransformation.naturality-condition (NaturalIsomorphism.g f≈f)) ⟩
                      NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                        ∘ Functor.map g₂ (Category._∘_ B (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f)) (Functor.map f₂ f))
                    ≈⟨ refl ⟩∘⟨ Functor.law-composes g₂ ⟩
                      NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                        ∘ (Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f))
                          ∘ Functor.map g₂ (Functor.map f₂ f))
                    ≈⟨ refl ⟩
                      NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                        ∘ (Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f))
                          ∘ Functor.map (compose-functors g₂ f₂) f)
                    ≈⟨ ilaw-associative ⟩
                      (NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                          ∘ Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f)))
                        ∘ Functor.map (compose-functors g₂ f₂) f
                    ∎
                }
          ; isomorphicˡ =
              let open Relation.Binary.Reasoning.Setoid setoid in
              begin
                (NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                    ∘ Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f)))
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                  ∘ Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f))
              ≈⟨ refl ⟩∘⟨ sym (NaturalTransformation.naturality-condition (NaturalIsomorphism.f g≈g)) ⟩
                (NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                    ∘ Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f)))
                  ∘ Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f))
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
              ≈⟨ ilaw-associative ⟩
                ((NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                      ∘ Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f)))
                    ∘ Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f)))
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
              ≈⟨ sym ilaw-associative ⟩∘⟨ refl ⟩
                (NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                    ∘ Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f))
                    ∘ Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f)))
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
              ≈⟨ (refl ⟩∘⟨ sym (Functor.law-composes g₂)) ⟩∘⟨ refl ⟩
                (NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                    ∘ Functor.map g₂ (Category._∘_ B
                        (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f))
                        (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f))))
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
              ≈⟨ (refl ⟩∘⟨ Functor.law-preserves-equality g₂ (NaturalIsomorphism.isomorphicˡ f≈f)) ⟩∘⟨ refl ⟩
                (NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                    ∘ Functor.map g₂ (Category.id B))
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
              ≈⟨ (refl ⟩∘⟨ Functor.law-map-id g₂) ⟩∘⟨ refl ⟩
                (NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g) ∘ id)
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
              ≈⟨ ilaw-identityʳ ⟩∘⟨ refl ⟩
                NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
              ≈⟨ NaturalIsomorphism.isomorphicˡ g≈g ⟩
                id
              ∎
          ; isomorphicʳ =
              let open Relation.Binary.Reasoning.Setoid setoid in
              begin
                (NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                    ∘ Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f)))
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
                  ∘ Functor.map g₂ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f))
              ≈⟨ refl ⟩∘⟨ sym (NaturalTransformation.naturality-condition (NaturalIsomorphism.g g≈g)) ⟩
                (NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                    ∘ Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f)))
                  ∘ Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f))
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
              ≈⟨ ilaw-associative ⟩
                ((NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                      ∘ Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f)))
                    ∘ Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f)))
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
              ≈⟨ sym ilaw-associative ⟩∘⟨ refl ⟩
                (NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                    ∘ Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f))
                    ∘ Functor.map g₁ (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f)))
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
              ≈⟨ (refl ⟩∘⟨ sym (Functor.law-composes g₁)) ⟩∘⟨ refl ⟩
                (NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                    ∘ Functor.map g₁ (Category._∘_ B
                        (NaturalTransformation.transform-object (NaturalIsomorphism.f f≈f))
                        (NaturalTransformation.transform-object (NaturalIsomorphism.g f≈f))))
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
              ≈⟨ (refl ⟩∘⟨ Functor.law-preserves-equality g₁ (NaturalIsomorphism.isomorphicʳ f≈f)) ⟩∘⟨ refl ⟩
                (NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                    ∘ Functor.map g₁ (Category.id B))
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
              ≈⟨ (refl ⟩∘⟨ Functor.law-map-id g₁) ⟩∘⟨ refl ⟩
                (NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g) ∘ id)
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
              ≈⟨ ilaw-identityʳ ⟩∘⟨ refl ⟩
                NaturalTransformation.transform-object (NaturalIsomorphism.f g≈g)
                  ∘ NaturalTransformation.transform-object (NaturalIsomorphism.g g≈g)
              ≈⟨ NaturalIsomorphism.isomorphicʳ g≈g ⟩
                id
              ∎
          }
    }
