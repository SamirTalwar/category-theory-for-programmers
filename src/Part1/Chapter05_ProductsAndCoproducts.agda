module Part1.Chapter05_ProductsAndCoproducts where

open import Level

open import Part1.Chapter01_Category

module Isomorphism where
  record Isomorphic {α β} (category : Category {α} {β}) (x y : category .Category.Object) : Set (α ⊔ β) where
    field
      f : let open Category category in x ⇒ y
      g : let open Category category in y ⇒ x
      isomorphicˡ : let open Category category in g ∘ f ≈ id
      isomorphicʳ : let open Category category in f ∘ g ≈ id

  sym : ∀ {α β} {category : Category {α} {β}} {x y : category .Category.Object}
    → Isomorphic category x y
    → Isomorphic category y x
  sym record { f = f ; g = g ; isomorphicˡ = isomorphicˡ ; isomorphicʳ = isomorphicʳ }
    = record { f = g ; g = f ; isomorphicˡ = isomorphicʳ ; isomorphicʳ = isomorphicˡ }

module Opposite where
  open import Relation.Binary.Definitions
  open import Relation.Binary.PropositionalEquality hiding (Extensionality)

  opposite : ∀ {α β} (category : Category {α} {β})
    → let open Category category in (∀ {A B : Object} → Symmetric {A = A ⇒ B} _≈_)
    → Category {α} {β}
  opposite category sym =
    record
      { Object = Object
      ; _⇒_ = λ y x → x ⇒ y
      ; _≈_ = _≈_
      ; id = id
      ; _∘_ = λ g f → f ∘ g
      ; law-identityˡ = law-identityʳ
      ; law-identityʳ = law-identityˡ
      ; law-associative = λ h g f → sym (law-associative f g h)
      }
      where
      open Category category

module InitialObject where
  open import Relation.Binary.PropositionalEquality hiding (Extensionality)

  open Isomorphism

  record InitialObject {α β} (category : Category {α} {β}) : Set (α ⊔ β) where
    field
      initial : let open Category category in Object
      is-initial : let open Category category in ∀ {x : Object} → initial ⇒ x
      has-unique-morphisms : let open Category category in ∀ {x : Object} (f g : initial ⇒ x) → f ≈ g

  initial-object-is-unique :
      ∀ {α β} (category : Category {α} {β}) (x y : InitialObject category)
    → let open Category category
      in Isomorphic category (InitialObject.initial x) (InitialObject.initial y)
  initial-object-is-unique
    category
    record { initial = x-initial ; is-initial = x-is-initial ; has-unique-morphisms = x-has-unique-morphisms }
    record { initial = y-initial ; is-initial = y-is-initial ; has-unique-morphisms = y-has-unique-morphisms }
    = record
        { f = f
        ; g = g
        ; isomorphicˡ = isomorphicˡ
        ; isomorphicʳ = isomorphicʳ
        }
        where
        open Category category
        f = x-is-initial {y-initial}
        g = y-is-initial {x-initial}
        isomorphicˡ : g ∘ f ≈ id
        isomorphicˡ = x-has-unique-morphisms (g ∘ f) id
        isomorphicʳ : f ∘ g ≈ id
        isomorphicʳ = y-has-unique-morphisms (f ∘ g) id

module TerminalObject where
  open Isomorphism
  open Opposite
  open InitialObject

  record TerminalObject {α β} (category : Category {α} {β}) : Set (α ⊔ β) where
    field
      terminal : let open Category category in Object
      is-terminal : let open Category category in ∀ {x : Object} → x ⇒ terminal
      has-unique-morphisms : let open Category category in ∀ {x : Object} (f g : x ⇒ terminal) → f ≈ g

  terminal-object-is-unique :
      ∀ {α β} (category : Category {α} {β}) (x y : TerminalObject category)
    → let open Category category
      in Isomorphic category (TerminalObject.terminal x) (TerminalObject.terminal y)
  terminal-object-is-unique
    category
    record { terminal = x-terminal ; is-terminal = x-is-terminal ; has-unique-morphisms = x-has-unique-morphisms }
    record { terminal = y-terminal ; is-terminal = y-is-terminal ; has-unique-morphisms = y-has-unique-morphisms }
    = record
        { f = f
        ; g = g
        ; isomorphicˡ = isomorphicˡ
        ; isomorphicʳ = isomorphicʳ
        }
        where
        open Category category
        f = y-is-terminal {x-terminal}
        g = x-is-terminal {y-terminal}
        isomorphicˡ : g ∘ f ≈ id
        isomorphicˡ = x-has-unique-morphisms (g ∘ f) id
        isomorphicʳ : f ∘ g ≈ id
        isomorphicʳ = y-has-unique-morphisms (f ∘ g) id

module Product where
  open import Data.Product

  record Product {α β} (category : Category {α} {β}) (A B : category .Category.Object) : Set (α ⊔ β) where
    field
      product : let open Category category in Object
      fst : let open Category category in product ⇒ A
      snd : let open Category category in product ⇒ B

  function-product : ∀ {A B : Set} → Product Part1.Chapter01_Category.Function.category A B
  function-product {A} {B} = record { product = A × B ; fst = proj₁ ; snd = proj₂ }

module Coproduct where
  open import Data.Sum

  record Coproduct {α β} (category : Category {α} {β}) (A B : category .Category.Object) : Set (α ⊔ β) where
    field
      coproduct : let open Category category in Object
      left : let open Category category in A ⇒ coproduct
      right : let open Category category in B ⇒ coproduct

  function-coproduct : ∀ {A B : Set} → Coproduct Part1.Chapter01_Category.Function.category A B
  function-coproduct {A} {B} = record { coproduct = A ⊎ B ; left = inj₁ ; right = inj₂ }

module ≤-Poset where
  open import Data.Nat
  open import Data.Nat.Properties
  open import Relation.Binary.PropositionalEquality hiding (Extensionality)
  open Relation.Binary.PropositionalEquality.≡-Reasoning

  open InitialObject
  open Product
  open Coproduct

  category : Category
  category =
    record
      { Object = ℕ
      ; _⇒_ = _≤_
      ; _≈_ = _≡_
      ; id = id
      ; _∘_ = _∘_
      ; law-identityˡ = law-identityˡ
      ; law-identityʳ = law-identityʳ
      ; law-associative = law-associative
      }
    where
    id : ∀ {n : ℕ} → n ≤ n
    id {zero} = z≤n
    id {suc n} = s≤s id
    _∘_ : ∀ {m n p : ℕ} → n ≤ p → m ≤ n → m ≤ p
    n≤p ∘ m≤n = ≤-trans m≤n n≤p
    law-identityˡ : ∀ {m n : ℕ} (m≤n : m ≤ n) → id ∘ m≤n ≡ m≤n
    law-identityˡ z≤n = refl
    law-identityˡ (s≤s m≤n) = cong s≤s (law-identityˡ m≤n)
    law-identityʳ : ∀ {m n : ℕ} (m≤n : m ≤ n) → m≤n ∘ id ≡ m≤n
    law-identityʳ z≤n = refl
    law-identityʳ (s≤s m≤n) = cong s≤s (law-identityʳ m≤n)
    law-associative : ∀ {m n p q : ℕ} (p≤q : p ≤ q) (n≤p : n ≤ p) (m≤n : m ≤ n)
      → p≤q ∘ (n≤p ∘ m≤n) ≡ (p≤q ∘ n≤p) ∘ m≤n
    law-associative h g z≤n = refl
    law-associative (s≤s h) (s≤s g) (s≤s f) =
      begin
        s≤s h ∘ (s≤s g ∘ s≤s f)
      ≡⟨⟩
        ≤-trans (≤-trans (s≤s f) (s≤s g)) (s≤s h)
      ≡⟨⟩
        s≤s (≤-trans (≤-trans f g) h)
      ≡⟨ cong s≤s (law-associative h g f) ⟩
        s≤s (≤-trans f (≤-trans g h))
      ≡⟨⟩
        ≤-trans (s≤s f) (≤-trans (s≤s g) (s≤s h))
      ≡⟨⟩
        (s≤s h ∘ s≤s g) ∘ s≤s f
      ∎

  initial : InitialObject category
  initial = record { initial = 0 ; is-initial = z≤n ; has-unique-morphisms = λ{ z≤n z≤n → refl } }

  product : ∀ {m n : ℕ} (m≤n : m ≤ n) → Product category m n
  product {m} m≤n = let open Category category in record { product = m ; fst = id ; snd = m≤n }

  coproduct : ∀ {m n : ℕ} (m≤n : m ≤ n) → Coproduct category m n
  coproduct {n = n} m≤n = let open Category category in record { coproduct = n ; left = m≤n ; right = id }
