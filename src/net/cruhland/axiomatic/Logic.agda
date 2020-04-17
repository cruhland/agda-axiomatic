module net.cruhland.axiomatic.Logic where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import net.cruhland.axiomatic.Logic.Conjunction using (Conjunction)
open import net.cruhland.axiomatic.Logic.Disjunction using (Disjunction)
open import net.cruhland.axiomatic.Logic.Exists using (Exists)
open import net.cruhland.axiomatic.Logic.Falsity using (Falsity)
open import net.cruhland.axiomatic.Logic.Truth using (Truth)

record Logic
  (Σ : (A : Set) → (A → Set) → Set)
  (_∧_ _∨_ : Set → Set → Set)
  (⊤ ⊥ : Set) : Set₁ where
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

record LogicBundle : Set₁ where
  field
    Σ : (A : Set) → (A → Set) → Set
    _∧_ _∨_ : Set → Set → Set
    ⊤ ⊥ : Set
    isLogic : Logic Σ _∧_ _∨_ ⊤ ⊥

  infixr 1 _∨_

  open Logic isLogic public

  ¬_ : Set → Set
  ¬ A = A → ⊥
