module net.cruhland.axiomatic.Logic where

open import Function using (id; _∘_)
open import Level using (Setω)
open import net.cruhland.axiomatic.Logic.Conjunction using (Conjunction)
open import net.cruhland.axiomatic.Logic.Disjunction using (Disjunction)
open import net.cruhland.axiomatic.Logic.Exists using (Exists)
open import net.cruhland.axiomatic.Logic.Falsity using (Falsity)
open import net.cruhland.axiomatic.Logic.Truth using (Truth)

record Logic
  (Σ : ∀ {α} (A : Set α) → (A → Set) → Set)
  (_∧_ _∨_ : Set → Set → Set)
  (⊤ ⊥ : Set) : Setω where
  field
    exists : Exists Σ
    conjunction : Conjunction _∧_
    disjunction : Disjunction _∨_
    truth : Truth ⊤
    falsity : Falsity ⊥

  open Exists exists public
  open Conjunction conjunction public
  open Disjunction disjunction public
  open Truth truth public
  open Falsity falsity public

record LogicBundle : Setω where
  field
    Σ : ∀ {α} (A : Set α) → (A → Set) → Set
    _∧_ _∨_ : Set → Set → Set
    ⊤ ⊥ : Set
    isLogic : Logic Σ _∧_ _∨_ ⊤ ⊥

  infixr 1 _∨_
  infixr 2 _∧_

  open Logic isLogic public

  ∨-forceᴸ : {A B : Set} → ¬ B → A ∨ B → A
  ∨-forceᴸ ¬b = ∨-recᴸ (⊥-elim ∘ ¬b)

  ∨-forceᴿ : {A B : Set} → ¬ A → A ∨ B → B
  ∨-forceᴿ ¬a = ∨-recᴿ (⊥-elim ∘ ¬a)

  _↔_ : Set → Set → Set
  A ↔ B = (A → B) ∧ (B → A)

  infixl 0 _↔_
