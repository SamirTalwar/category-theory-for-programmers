module Part1.Chapter03_CategoriesGreatAndSmall where

open import Level

open import Part1.Chapter01_Category

module Empty where
  open import Data.Empty.Polymorphic
  open import Relation.Binary

  ∅ : ∀ {ℓ} → Category ℓ ℓ
  ∅ = record
        { Object = ⊥
        ; _⇒_ = λ _ _ → ⊥
        ; _≈_ = λ { {()} }
        ; isEquivalence = record { refl = λ{ {()} } ; sym = λ{ {()} } ; trans = λ{ {()} } }
        ; id = λ { {()} }
        ; _∘_ = λ{ () }
        ; law-identityˡ = λ{ () }
        ; law-identityʳ = λ{ () }
        ; law-associative = λ{ () }
        }

module Free where
  open import Axiom.Extensionality.Propositional
  open import Data.List
  open import Data.Sum
  open import Level
  open import Relation.Binary.PropositionalEquality hiding (Extensionality)

  module One where
    data Node : Set where
      x : Node

    data Edge : (a b : Node) → Set where
      -- free
      x-x : Edge x x

    category : Category₀
    category = record
                 { Object = Node
                 ; _⇒_ = Edge
                 ; _≈_ = _≡_
                 ; isEquivalence = isEquivalence
                 ; id = λ{ {x} → x-x }
                 ; _∘_ = λ{ x-x x-x → x-x }
                 ; law-identityˡ = λ{ x-x → refl }
                 ; law-identityʳ = λ{ x-x → refl }
                 ; law-associative = λ{ x-x x-x x-x → refl }
                 }

  module Two where
    data Node : Set where
      x : Node
      y : Node

    data Edge : (a b : Node) → Set where
      x-y : Edge x y
      -- free
      x-x : Edge x x
      y-y : Edge y y

    category : Category₀
    category = record
                 { Object = Node
                 ; _⇒_ = Edge
                 ; _≈_ = _≡_
                 ; isEquivalence = isEquivalence
                 ; id = λ{ {x} → x-x ; {y} → y-y }
                 ; _∘_ = λ{ a x-x → a ; y-y b → b }
                 ; law-identityˡ = λ{ x-y → refl ; x-x → refl ; y-y → refl }
                 ; law-identityʳ = λ{ x-y → refl ; x-x → refl ; y-y → refl }
                 ; law-associative = λ{ x-y x-x x-x → refl
                                      ; x-x x-x x-x → refl
                                      ; y-y x-y x-x → refl
                                      ; y-y y-y x-y → refl
                                      ; y-y y-y y-y → refl
                                      }
                 }

module Bool where
  open import Relation.Binary.PropositionalEquality hiding (Extensionality)

  data Bool : Set where
    true : Bool
    false : Bool

  _∧_ : Bool → Bool → Bool
  true ∧ b = b
  false ∧ b = false

  _∨_ : Bool → Bool → Bool
  true ∨ b = true
  false ∨ b = b

  record Monoid {α} (A : Set α) : Set α where
    field
      ε : A
      _⊗_ : A → A → A

  ∧-monoid : Monoid Bool
  ∧-monoid = record { ε = true ; _⊗_ = _∧_ }

  ∨-monoid : Monoid Bool
  ∨-monoid = record { ε = false ; _⊗_ = _∨_ }

  data And : Bool → Bool → Set where
    true∧ : (x : Bool) → And x x
    false∧ : (x : Bool) → And x false

  data Or : Bool → Bool → Set where
    true∨ : (x : Bool) → Or x true
    false∨ : (x : Bool) → Or x x

  ∧-category : Category₀
  ∧-category = record
                 { Object = Bool
                 ; _⇒_ = And
                 ; _≈_ = _≡_
                 ; isEquivalence = isEquivalence
                 ; id = λ{ {x} → true∧ x }
                 ; _∘_ = λ{ g (true∧ _) → g
                          ; (true∧ false) (false∧ true) → false∧ true
                          ; (false∧ false) (false∧ true) → false∧ true
                          ; (true∧ false) (false∧ false) → false∧ false
                          ; (false∧ false) (false∧ false) → false∧ false
                          }
                 ; law-identityˡ = λ{ (true∧ x) → refl ; (false∧ true) → refl ; (false∧ false) → refl }
                 ; law-identityʳ = λ{ (true∧ x) → refl ; (false∧ x) → refl }
                 ; law-associative = λ{ h g (true∧ x) → refl
                                      ; h (true∧ false) (false∧ true) → refl
                                      ; (true∧ false) (false∧ false) (false∧ true) → refl
                                      ; (false∧ false) (false∧ false) (false∧ true) → refl
                                      ; h (true∧ false) (false∧ false) → refl
                                      ; (true∧ false) (false∧ false) (false∧ false) → refl
                                      ; (false∧ false) (false∧ false) (false∧ false) → refl
                                      }
                 }

  ∨-category : Category₀
  ∨-category = record
                 { Object = Bool
                 ; _⇒_ = Or
                 ; _≈_ = _≡_
                 ; isEquivalence = isEquivalence
                 ; id = λ{ {x} → false∨ x }
                 ; _∘_ = λ{ (true∨ true) (true∨ true) → true∨ true
                          ; (false∨ true) (true∨ true) → true∨ true
                          ; (true∨ true) (true∨ false) → true∨ false
                          ; (false∨ true) (true∨ false) → true∨ false
                          ; g (false∨ _) → g
                          }
                 ; law-identityˡ = λ{ (true∨ true) → refl ; (true∨ false) → refl ; (false∨ true) → refl ; (false∨ false) → refl }
                 ; law-identityʳ = λ{ (true∨ true) → refl ; (true∨ false) → refl ; (false∨ true) → refl ; (false∨ false) → refl }
                 ; law-associative = λ{ (true∨ true) (true∨ true) (true∨ true) → refl
                                      ; (false∨ true) (true∨ true) (true∨ true) → refl
                                      ; (true∨ true) (false∨ true) (true∨ true) → refl
                                      ; (false∨ true) (false∨ true) (true∨ true) → refl
                                      ; (true∨ true) (true∨ true) (true∨ false) → refl
                                      ; (false∨ true) (true∨ true) (true∨ false) → refl
                                      ; (true∨ true) (false∨ true) (true∨ false) → refl
                                      ; (false∨ .true) (false∨ .true) (true∨ false) → refl
                                      ; (true∨ true) (true∨ true) (false∨ true) → refl
                                      ; (false∨ true) (true∨ true) (false∨ true) → refl
                                      ; (true∨ true) (false∨ true) (false∨ true) → refl
                                      ; (false∨ true) (false∨ true) (false∨ true) → refl
                                      ; (true∨ true) (true∨ false) (false∨ false) → refl
                                      ; (false∨ true) (true∨ false) (false∨ false) → refl
                                      ; (true∨ alse) (false∨ false) (false∨ false) → refl
                                      ; (false∨ false) (false∨ false) (false∨ false) → refl
                                      }
                 }

module Addition where
  open import Relation.Binary.PropositionalEquality hiding (Extensionality)

  data ℕ : Set where
    n0 : ℕ
    n1 : ℕ
    n2 : ℕ

  data AddMod3 : ℕ → ℕ → Set where
    0+0 : AddMod3 n0 n0
    0+1 : AddMod3 n0 n1
    0+2 : AddMod3 n0 n2
    1+0 : AddMod3 n1 n1
    1+1 : AddMod3 n1 n2
    1+2 : AddMod3 n1 n0
    2+0 : AddMod3 n2 n2
    2+1 : AddMod3 n2 n0
    2+2 : AddMod3 n2 n1

  addMod3-category : Category₀
  addMod3-category = record
                       { Object = ℕ
                       ; _⇒_ = AddMod3
                       ; _≈_ = _≡_
                       ; isEquivalence = isEquivalence
                       ; id = λ{ {n0} → 0+0 ; {n1} → 1+0 ; {n2} → 2+0 }
                       ; _∘_ = λ{ 0+0 0+0 → 0+0
                                ; 0+1 0+0 → 0+1
                                ; 0+2 0+0 → 0+2
                                ; 1+0 0+1 → 0+1
                                ; 1+1 0+1 → 0+2
                                ; 1+2 0+1 → 0+0
                                ; 2+0 0+2 → 0+2
                                ; 2+1 0+2 → 0+0
                                ; 2+2 0+2 → 0+1
                                ; 1+0 1+0 → 1+0
                                ; 1+1 1+0 → 1+1
                                ; 1+2 1+0 → 1+2
                                ; 2+0 1+1 → 1+1
                                ; 2+1 1+1 → 1+2
                                ; 2+2 1+1 → 1+0
                                ; 0+0 1+2 → 1+2
                                ; 0+1 1+2 → 1+0
                                ; 0+2 1+2 → 1+1
                                ; 2+0 2+0 → 2+0
                                ; 2+1 2+0 → 2+1
                                ; 2+2 2+0 → 2+2
                                ; 0+0 2+1 → 2+1
                                ; 0+1 2+1 → 2+2
                                ; 0+2 2+1 → 2+0
                                ; 1+0 2+2 → 2+2
                                ; 1+1 2+2 → 2+0
                                ; 1+2 2+2 → 2+1
                                }
                       ; law-identityˡ = λ{ 0+0 → refl
                                          ; 0+1 → refl
                                          ; 0+2 → refl
                                          ; 1+0 → refl
                                          ; 1+1 → refl
                                          ; 1+2 → refl
                                          ; 2+0 → refl
                                          ; 2+1 → refl
                                          ; 2+2 → refl
                                          }
                       ; law-identityʳ = λ{ 0+0 → refl
                                          ; 0+1 → refl
                                          ; 0+2 → refl
                                          ; 1+0 → refl
                                          ; 1+1 → refl
                                          ; 1+2 → refl
                                          ; 2+0 → refl
                                          ; 2+1 → refl
                                          ; 2+2 → refl
                                          }
                       ; law-associative = λ{ 0+0 0+0 0+0 → refl
                                            ; 0+1 0+0 0+0 → refl
                                            ; 0+2 0+0 0+0 → refl
                                            ; 1+0 0+1 0+0 → refl
                                            ; 1+1 0+1 0+0 → refl
                                            ; 1+2 0+1 0+0 → refl
                                            ; 2+0 0+2 0+0 → refl
                                            ; 2+1 0+2 0+0 → refl
                                            ; 2+2 0+2 0+0 → refl
                                            ; 1+0 1+0 0+1 → refl
                                            ; 1+1 1+0 0+1 → refl
                                            ; 1+2 1+0 0+1 → refl
                                            ; 2+0 1+1 0+1 → refl
                                            ; 2+1 1+1 0+1 → refl
                                            ; 2+2 1+1 0+1 → refl
                                            ; 0+0 1+2 0+1 → refl
                                            ; 0+1 1+2 0+1 → refl
                                            ; 0+2 1+2 0+1 → refl
                                            ; 2+0 2+0 0+2 → refl
                                            ; 2+1 2+0 0+2 → refl
                                            ; 2+2 2+0 0+2 → refl
                                            ; 0+0 2+1 0+2 → refl
                                            ; 0+1 2+1 0+2 → refl
                                            ; 0+2 2+1 0+2 → refl
                                            ; 1+0 2+2 0+2 → refl
                                            ; 1+1 2+2 0+2 → refl
                                            ; 1+2 2+2 0+2 → refl
                                            ; 1+0 1+0 1+0 → refl
                                            ; 1+1 1+0 1+0 → refl
                                            ; 1+2 1+0 1+0 → refl
                                            ; 2+0 1+1 1+0 → refl
                                            ; 2+1 1+1 1+0 → refl
                                            ; 2+2 1+1 1+0 → refl
                                            ; 0+0 1+2 1+0 → refl
                                            ; 0+1 1+2 1+0 → refl
                                            ; 0+2 1+2 1+0 → refl
                                            ; 2+0 2+0 1+1 → refl
                                            ; 2+1 2+0 1+1 → refl
                                            ; 2+2 2+0 1+1 → refl
                                            ; 0+0 2+1 1+1 → refl
                                            ; 0+1 2+1 1+1 → refl
                                            ; 0+2 2+1 1+1 → refl
                                            ; 1+0 2+2 1+1 → refl
                                            ; 1+1 2+2 1+1 → refl
                                            ; 1+2 2+2 1+1 → refl
                                            ; 0+0 0+0 1+2 → refl
                                            ; 0+1 0+0 1+2 → refl
                                            ; 0+2 0+0 1+2 → refl
                                            ; 1+0 0+1 1+2 → refl
                                            ; 1+1 0+1 1+2 → refl
                                            ; 1+2 0+1 1+2 → refl
                                            ; 2+0 0+2 1+2 → refl
                                            ; 2+1 0+2 1+2 → refl
                                            ; 2+2 0+2 1+2 → refl
                                            ; 2+0 2+0 2+0 → refl
                                            ; 2+1 2+0 2+0 → refl
                                            ; 2+2 2+0 2+0 → refl
                                            ; 0+0 2+1 2+0 → refl
                                            ; 0+1 2+1 2+0 → refl
                                            ; 0+2 2+1 2+0 → refl
                                            ; 1+0 2+2 2+0 → refl
                                            ; 1+1 2+2 2+0 → refl
                                            ; 1+2 2+2 2+0 → refl
                                            ; 0+0 0+0 2+1 → refl
                                            ; 0+1 0+0 2+1 → refl
                                            ; 0+2 0+0 2+1 → refl
                                            ; 1+0 0+1 2+1 → refl
                                            ; 1+1 0+1 2+1 → refl
                                            ; 1+2 0+1 2+1 → refl
                                            ; 2+0 0+2 2+1 → refl
                                            ; 2+1 0+2 2+1 → refl
                                            ; 2+2 0+2 2+1 → refl
                                            ; 1+0 1+0 2+2 → refl
                                            ; 1+1 1+0 2+2 → refl
                                            ; 1+2 1+0 2+2 → refl
                                            ; 2+0 1+1 2+2 → refl
                                            ; 2+1 1+1 2+2 → refl
                                            ; 2+2 1+1 2+2 → refl
                                            ; 0+0 1+2 2+2 → refl
                                            ; 0+1 1+2 2+2 → refl
                                            ; 0+2 1+2 2+2 → refl
                                            }
                       }
