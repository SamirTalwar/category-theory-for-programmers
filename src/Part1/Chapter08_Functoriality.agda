module Part1.Chapter08_Functoriality where

open import Data.Product
open import Function
open import Level
open import Relation.Binary.Definitions
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality hiding (Extensionality)

open import Part1.Chapter01_Category
open import Part1.Chapter05_ProductsAndCoproducts
open import Part1.Chapter07_Functors

infix 5 _×ᶜ_
_×ᶜ_ : ∀ {α β} → (C D : Category α β) → Category α β
C ×ᶜ D =
  let
    module C = Category C
    module D = Category D
  in
  record
    { Object = C.Object × D.Object
    ; _⇒_ = λ{ (x₁ , y₁) (x₂ , y₂) → x₁ C.⇒ x₂ × y₁ D.⇒ y₂ }
    ; _≈_ = λ{ (x₁ , y₁) (x₂ , y₂) → x₁ C.≈ x₂ × y₁ D.≈ y₂ }
    ; isEquivalence =
        record
          { refl = C.refl , D.refl
          ; sym = λ{ (x , y) → C.sym x , D.sym y }
          ; trans = λ{ (x₁ , x₂) (y₁ , y₂) → C.trans x₁ y₁ , D.trans x₂ y₂ }
          }
    ; id = C.id , D.id
    ; _∘_ = λ{ (g₁ , g₂) (f₁ , f₂) → g₁ C.∘ f₁ , g₂ D.∘ f₂ }
    ; law-identityˡ = λ{ (f₁ , f₂) → C.law-identityˡ f₁ , D.law-identityˡ f₂ }
    ; law-identityʳ = λ{ (f₁ , f₂) → C.law-identityʳ f₁ , D.law-identityʳ f₂ }
    ; law-associative = λ{ (h₁ , h₂) (g₁ , g₂) (f₁ , f₂) → C.law-associative h₁ g₁ f₁ , D.law-associative h₂ g₂ f₂ }
    ; _⟩∘⟨_ = λ{ (g₁ , g₂) (f₁ , f₂) → (g₁ C.⟩∘⟨ f₁) , (g₂ D.⟩∘⟨ f₂) }
    }

module Bifunctor {α β} {C D E : Category α β} where
  Bifunctor : Set (α ⊔ β)
  Bifunctor = C ×ᶜ D -F-> E

  bimap :
      (functor : Bifunctor)
    → {x₁ y₁ : Category.Object C} {x₂ y₂ : Category.Object D}
    → (let open Category C in x₁ ⇒ y₁)
    → (let open Category D in x₂ ⇒ y₂)
    → (let open Category E in Functor.construct functor (x₁ , x₂) ⇒ Functor.construct functor (y₁ , y₂))
  bimap functor f g = Functor.map functor (f , g)

  lmap :
      (functor : Bifunctor)
    → {x y : Category.Object C} {z : Category.Object D}
    → (let open Category C in x ⇒ y)
    → (let open Category E in Functor.construct functor (x , z) ⇒ Functor.construct functor (y , z))
  lmap functor f = bimap functor f (Category.id D)

  rmap :
      (functor : Bifunctor)
    → {z : Category.Object C} {x y : Category.Object D}
    → (let open Category D in x ⇒ y)
    → (let open Category E in Functor.construct functor (z , x) ⇒ Functor.construct functor (z , y))
  rmap functor g = bimap functor (Category.id C) g

Bifunctor : ∀ {α β} (C D E : Category α β) → Set (α ⊔ β)
Bifunctor C D E = Bifunctor.Bifunctor {C = C} {D = D} {E = E}

Profunctor : ∀ {ℓ} → (C D : Category (suc ℓ) ℓ) → Set _
Profunctor {ℓ} C D = Bifunctor (Opposite.opposite C) D (Function.category ℓ)

module Pair where
  record Pair {ℓ} (A B : Set ℓ) : Set ℓ where
    constructor pair
    field
      x : A
      y : B

  bimap : ∀ {ℓ} {A B C D : Set ℓ} → (A → C) → (B → D) → Pair A B → Pair C D
  bimap f g (pair x y) = pair (f x) (g y)

  bifunctor : ∀ {ℓ} → Bifunctor (Function.category ℓ) (Function.category ℓ) (Function.category ℓ)
  bifunctor =
    record
      { construct = λ{ (A , B) → Pair A B }
      ; map = λ{ (f , g) → bimap f g }
      ; law-map-id = refl
      ; law-composes = refl
      ; law-preserves-equality = λ{ (f , g) → cong₂ bimap f g }
      }

module IsomorphicMaybe where
  open import Data.Maybe
  open import Data.Sum
  open import Data.Unit.Polymorphic

  import Part1.Chapter06_SimpleAlgebraicDataTypes
  open Part1.Chapter06_SimpleAlgebraicDataTypes.Isomorphisms using (_≈_)
  open Part1.Chapter07_Functors.Const using (Const)

  Identity : ∀ {ℓ} → Set ℓ → Set ℓ
  Identity A = A

  Maybe′ : ∀ {ℓ} → Set ℓ → Set ℓ
  Maybe′ A = Const ⊤ A ⊎ Identity A

  Maybe≈Maybe′ : ∀ {A : Set} → Maybe A ≈ Maybe′ A
  Maybe≈Maybe′ =
    record
      { to = λ{ nothing → inj₁ (Const.const tt) ; (just x) → inj₂ x }
      ; from = λ{ (inj₁ (Const.const tt)) → nothing ; (inj₂ x) → just x }
      ; from∘to≡id = λ{ nothing → refl ; (just x) → refl }
      ; to∘from≡id = λ{ (inj₁ (Const.const tt)) → refl ; (inj₂ x) → refl }
      }

module PreList where
  open import Axiom.Extensionality.Propositional

  data PreList {ℓ} (A B : Set ℓ) : Set ℓ where
    nil : PreList A B
    cons : (head : A) → (tail : B) → PreList A B

  bimap : ∀ {ℓ} {A B C D : Set ℓ} → (A → C) → (B → D) → PreList A B → PreList C D
  bimap f g nil = nil
  bimap f g (cons head tail) = cons (f head) (g tail)

  bifunctor : ∀ {ℓ} → Extensionality _ _ → Bifunctor (Function.category ℓ) (Function.category ℓ) (Function.category ℓ)
  bifunctor ext =
    record
      { construct = λ{ (A , B) → PreList A B }
      ; map = λ{ (f , g) → bimap f g }
      ; law-map-id = ext λ{ nil → refl ; (cons head tail) → refl }
      ; law-composes = ext λ{ nil → refl ; (cons head tail) → refl }
      ; law-preserves-equality = λ{ (f , g) → cong₂ bimap f g }
      }

module K2 where
  record K2 {ℓ} (C A B : Set ℓ) : Set ℓ where
    field
      value : C

  bimap : ∀ {ℓ} {A B C D X : Set ℓ} → (A → C) → (B → D) → K2 X A B → K2 X C D
  bimap _ _ record { value = value } = record { value = value }

  bifunctor : ∀ {ℓ} → Set ℓ → Bifunctor (Function.category ℓ) (Function.category ℓ) (Function.category ℓ)
  bifunctor C =
    record
      { construct = λ{ (A , B) → K2 C A B }
      ; map = λ{ (f , g) → bimap f g }
      ; law-map-id = refl
      ; law-composes = refl
      ; law-preserves-equality = λ{ (f , g) → cong₂ bimap f g }
      }

module Fst where
  record Fst {ℓ} (A B : Set ℓ) : Set ℓ where
    field
      value : A

  bimap : ∀ {ℓ} {A B C D : Set ℓ} → (A → C) → (B → D) → Fst A B → Fst C D
  bimap f _ record { value = value } = record { value = f value }

  bifunctor : ∀ {ℓ} → Bifunctor (Function.category ℓ) (Function.category ℓ) (Function.category ℓ)
  bifunctor =
    record
      { construct = λ{ (A , B) → Fst A B }
      ; map = λ{ (f , g) → bimap f g }
      ; law-map-id = refl
      ; law-composes = refl
      ; law-preserves-equality = λ{ (f , g) → cong₂ bimap f g }
      }

module Snd where
  record Snd {ℓ} (A B : Set ℓ) : Set ℓ where
    field
      value : B

  bimap : ∀ {ℓ} {A B C D : Set ℓ} → (A → C) → (B → D) → Snd A B → Snd C D
  bimap _ g record { value = value } = record { value = g value }

  bifunctor : ∀ {ℓ} → Bifunctor (Function.category ℓ) (Function.category ℓ) (Function.category ℓ)
  bifunctor =
    record
      { construct = λ{ (A , B) → Snd A B }
      ; map = λ{ (f , g) → bimap f g }
      ; law-map-id = refl
      ; law-composes = refl
      ; law-preserves-equality = λ{ (f , g) → cong₂ bimap f g }
      }

module Functions where
  dimap : ∀ {ℓ} {A B C D : Set ℓ} → (C → A) → (B → D) → (A → B) → (C → D)
  dimap f g func = g ∘ func ∘ f

  profunctor : ∀ {ℓ} → Profunctor (Function.category ℓ) (Function.category ℓ)
  profunctor =
    record
      { construct = λ{ (A , B) → A → B }
      ; map = λ{ (f , g) → dimap f g }
      ; law-map-id = refl
      ; law-composes = refl
      ; law-preserves-equality = λ{ (f , g) → cong₂ dimap f g }
      }
