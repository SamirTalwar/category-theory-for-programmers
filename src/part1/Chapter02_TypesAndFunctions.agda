module part1.Chapter02_TypesAndFunctions where

open import Axiom.Extensionality.Propositional
open import Data.Sum
open import Level
open import Relation.Binary.PropositionalEquality hiding (Extensionality)

data ⊥ : Set where

data ⊤ : Set where
  unit : ⊤

data Bool : Set where
  true : Bool
  false : Bool

bool→bool₁ : Bool → Bool
bool→bool₁ true = true
bool→bool₁ false = true

bool→bool₂ : Bool → Bool
bool→bool₂ true = true
bool→bool₂ false = false

bool→bool₃ : Bool → Bool
bool→bool₃ true = false
bool→bool₃ false = true

bool→bool₄ : Bool → Bool
bool→bool₄ true = false
bool→bool₄ false = false

bool→bool : ∀ (f : Bool → Bool)
  → Extensionality _ _
  →   f ≡ bool→bool₁
    ⊎ f ≡ bool→bool₂
    ⊎ f ≡ bool→bool₃
    ⊎ f ≡ bool→bool₄
bool→bool f ext with f true | inspect f true | f false | inspect f false
...                |   true |        [ eqᵗ ] |    true |         [ eqᶠ ] = inj₁ (ext λ{ true → eqᵗ ; false → eqᶠ })
...                |   true |        [ eqᵗ ] |   false |         [ eqᶠ ] = inj₂ (inj₁ (ext λ{ true → eqᵗ ; false → eqᶠ }))
...                |  false |        [ eqᵗ ] |    true |         [ eqᶠ ] = inj₂ (inj₂ (inj₁ (ext λ{ true → eqᵗ ; false → eqᶠ })))
...                |  false |        [ eqᵗ ] |   false |         [ eqᶠ ] = inj₂ (inj₂ (inj₂ (ext λ{ true → eqᵗ ; false → eqᶠ })))
