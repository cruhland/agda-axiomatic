module net.cruhland.axiomatic.Logic where

open import Function using (id; _∘_)
open import Level using (_⊔_; Setω; Lift; lift; lower) renaming (zero to lzero)
open import net.cruhland.axiomatic.Logic.Conjunction using (Conjunction)
open import net.cruhland.axiomatic.Logic.Disjunction using (Disjunction)
open import net.cruhland.axiomatic.Logic.Exists using (Exists)
import net.cruhland.axiomatic.Logic.Falsity as Falsity
import net.cruhland.axiomatic.Logic.Truth as Truth

record Logic
  (Σ : ∀ {α β} (A : Set α) → (A → Set β) → Set (α ⊔ β))
  (_∧_ _∨_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)) : Setω where
  field
    exists : Exists Σ
    conjunction : Conjunction _∧_
    disjunction : Disjunction _∨_

  open Exists exists public
  open Conjunction conjunction public
  open Disjunction disjunction public

record LogicBundle : Setω where
  field
    Σ : ∀ {α β} (A : Set α) → (A → Set β) → Set (α ⊔ β)
    _∧_ _∨_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
    isLogic : Logic Σ _∧_ _∨_

  infixl 1 _∨_
  infixl 2 _∧_

  open Logic isLogic public
  open Falsity public
  open Truth public

  ∨-identᴸ : ∀ {α β} {B : Set β} → Lift α ⊥ ∨ B → B
  ∨-identᴸ = ∨-recᴿ (⊥-elim ∘ lower)

  ∨-identᴿ : ∀ {α β} {A : Set α} → A ∨ Lift β ⊥ → A
  ∨-identᴿ = ∨-recᴸ (⊥-elim ∘ lower)

  ∨-forceᴸ : ∀ {α β} {A : Set α} {B : Set β} → ¬ B → A ∨ B → A
  ∨-forceᴸ ¬b = ∨-identᴿ {β = lzero} ∘ ∨-mapᴿ (lift ∘ ¬b)

  ∨-forceᴿ : ∀ {α β} {A : Set α} {B : Set β} → ¬ A → A ∨ B → B
  ∨-forceᴿ ¬a = ∨-identᴸ {α = lzero} ∘ ∨-mapᴸ (lift ∘ ¬a)

  _↔_ : ∀ {α β} → Set α → Set β → Set (α ⊔ β)
  A ↔ B = (A → B) ∧ (B → A)

  infixl 0 _↔_

  ↔-refl : ∀ {α} {A : Set α} → A ↔ A
  ↔-refl = ∧-intro id id

  ↔-sym : ∀ {α β} {A : Set α} {B : Set β} → A ↔ B → B ↔ A
  ↔-sym A↔B = ∧-comm A↔B

  ↔-trans :
    ∀ {α β χ} {A : Set α} {B : Set β} {C : Set χ} → A ↔ B → B ↔ C → A ↔ C
  ↔-trans A↔B B↔C =
    ∧-intro (∧-elimᴸ B↔C ∘ ∧-elimᴸ A↔B) (∧-elimᴿ A↔B ∘ ∧-elimᴿ B↔C)

  ↔-bimap :
    ∀ {α β χ δ} {A : Set α} {B : Set β} {C : Set χ} {D : Set δ} →
      ((A → B) → (C → D)) → ((B → A) → (D → C)) → A ↔ B → C ↔ D
  ↔-bimap = ∧-map
