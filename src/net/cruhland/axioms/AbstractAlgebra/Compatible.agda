module net.cruhland.axioms.AbstractAlgebra.Compatible where

open import net.cruhland.axioms.Eq as Eq
  using (_≃_; _≄_; _≄ⁱ_; Eq; ≄ⁱ-elim; ≄ⁱ-intro)
open import net.cruhland.models.Function using (_∘_; _⟨→⟩_)
open import net.cruhland.models.Logic using (_∨_; ∨-rec)

open import net.cruhland.axioms.AbstractAlgebra.Base using
  (forHand; Hand; handᴸ; handᴿ; handRec)
open import net.cruhland.axioms.AbstractAlgebra.Reductive using (Absorptive²)

private
  record Semicompatible₂
      (hand : Hand) {A B : Set}
        (f : A → B) (_⊙_ : A → A → A) (_~_ : B → B → Set) : Set where
    constructor semicompatible₂
    _<~>_ = forHand hand _~_
    field
      _⊕_ : B → B → B
      semicompat₂ : ∀ {a b} → (f (a ⊙ b)) <~> (f a ⊕ f b)

  open Semicompatible₂ {{...}} using (semicompat₂)

record Compatible₁
    {β} {A : Set} {B : Set β}
    (f : A → B) (g : A → A) (h : B → B) (_~_ : B → B → Set)
    : Set where
  constructor compatible₁
  field
    compat₁ : ∀ {a} → f (g a) ~ h (f a)

open Compatible₁ {{...}} public using (compat₁)

record Preserves {A : Set} (P : A → Set) (_⊙_ : A → A → A) : Set where
  constructor preserves
  field
    pres : ∀ {a b} → P a → P b → P (a ⊙ b)

open Preserves {{...}} public using (pres)

record Compatible₂
    {β} {A : Set} {B : Set β}
    (f : A → B) (_⊙_ : A → A → A) (_⊕_ : B → B → B) (_~_ : B → B → Set)
    : Set where
  constructor compatible₂
  field
    compat₂ : ∀ {a b} → (f (a ⊙ b)) ~ (f a ⊕ f b)

open Compatible₂ {{...}} public using (compat₂)

record FnOpCommutative
    (hand : Hand) {A : Set} {{_ : Eq A}} (f : A → A) (_⊙_ : A → A → A)
    : Set where
  constructor fnOpCommutative
  field
    fnOpComm : ∀ {a b} → f (a ⊙ b) ≃ handRec (f a ⊙ b) (a ⊙ f b) hand

open FnOpCommutative {{...}} public using (fnOpComm)

fnOpCommSwap :
  {A : Set} {f : A → A} {_⊙_ : A → A → A} {{_ : Eq A}}
  {{_ : FnOpCommutative handᴸ f _⊙_}} {{_ : FnOpCommutative handᴿ f _⊙_}} →
  ∀ {a b} → f a ⊙ b ≃ a ⊙ f b
fnOpCommSwap = Eq.trans (Eq.sym fnOpComm) fnOpComm

record FnOpCommutative²
    {A : Set} {{_ : Eq A}} (f : A → A) (_⊙_ : A → A → A) : Set where
  constructor fnOpCommutative²
  field
    {{fnOpCommutativeᴸ}} : FnOpCommutative handᴸ f _⊙_
    {{fnOpCommutativeᴿ}} : FnOpCommutative handᴿ f _⊙_

record Distributive
    (hand : Hand) {A : Set} {{_ : Eq A}} (_⊙_ _⊕_ : A → A → A) : Set where
  constructor distributive
  _<⊙>_ = forHand hand _⊙_
  field
    distrib : ∀ {a b c} → a <⊙> (b ⊕ c) ≃ (a <⊙> b) ⊕ (a <⊙> c)

open Distributive {{...}} public using (distrib)

distribᴸ = distrib {handᴸ}
distribᴿ = distrib {handᴿ}

record Distributive² {A : Set} {{_ : Eq A}} (_⊙_ _⊕_ : A → A → A) : Set where
  constructor distributive²
  field
    {{distributiveᴸ}} : Distributive handᴸ _⊙_ _⊕_
    {{distributiveᴿ}} : Distributive handᴿ _⊙_ _⊕_

record ZeroProduct
    {A : Set} {{_ : Eq A}} (z : A) (_⊙_ : A → A → A) {{_ : Absorptive² _⊙_ z}}
    : Set where
  constructor zeroProduct
  field
    zero-prod : ∀ {a b} → a ⊙ b ≃ z → a ≃ z ∨ b ≃ z

open ZeroProduct {{...}} public using (zero-prod)

nonzero-prod :
  {A : Set} {z : A} {_⊙_ : A → A → A}
  {{_ : Eq A}} {{_ : Absorptive² _⊙_ z}} {{r : ZeroProduct z _⊙_}} →
  ∀ {a b} → a ≄ z → b ≄ z → a ⊙ b ≄ z
nonzero-prod a≄z b≄z = ∨-rec a≄z b≄z ∘ zero-prod

nonzero-prodⁱ :
  {A : Set} {z : A} {_⊙_ : A → A → A}
  {{_ : Eq A}} {{_ : Absorptive² _⊙_ z}} {{r : ZeroProduct z _⊙_}} →
  ∀ {a b} {{ca : a ≄ⁱ z}} {{cb : b ≄ⁱ z}} → a ⊙ b ≄ⁱ z
nonzero-prodⁱ = ≄ⁱ-intro (nonzero-prod ≄ⁱ-elim ≄ⁱ-elim)

{--- Equivalences ---}

module _
    {β} {A : Set} {B : Set β} {f : A → B}
      {_⊙_ : A → A → A} {_⊕_ : B → B → B} {_~_ : B → B → Set} where

  compatible₁-from-compatible₂ :
    {{_ : Compatible₂ f _⊙_ _⊕_ _~_}} →
      ∀ {b} → Compatible₁ f (_⊙ b) (_⊕ f b) _~_
  compatible₁-from-compatible₂ = compatible₁ compat₂

  compatible₂-from-compatible₁ :
    {{_ : ∀ {b} → Compatible₁ f (_⊙ b) (_⊕ f b) _~_}} →
      Compatible₂ f _⊙_ _⊕_ _~_
  compatible₂-from-compatible₁ = compatible₂ compat₁

-- TODO Equivalences for Semicompatible₂ and Preserves

module _ {A : Set} {f : A → A} {_⊙_ : A → A → A} {{_ : Eq A}} where

  compatible₁-from-fnOpCommutativeᴸ :
    {{_ : FnOpCommutative handᴸ f _⊙_}} →
      ∀ {b} → Compatible₁ f (_⊙ b) (_⊙ b) _≃_
  compatible₁-from-fnOpCommutativeᴸ = compatible₁ fnOpComm

  fnOpCommutativeᴸ-from-compatible₁ :
    {{_ : ∀ {b} → Compatible₁ f (_⊙ b) (_⊙ b) _≃_}} →
      FnOpCommutative handᴸ f _⊙_
  fnOpCommutativeᴸ-from-compatible₁ = fnOpCommutative compat₁

  compatible₁-from-fnOpCommutativeᴿ :
    {{_ : FnOpCommutative handᴿ f _⊙_}} →
      ∀ {a} → Compatible₁ f (a ⊙_) (a ⊙_) _≃_
  compatible₁-from-fnOpCommutativeᴿ = compatible₁ fnOpComm

  fnOpCommutativeᴿ-from-compatible₁ :
    {{_ : ∀ {a} → Compatible₁ f (a ⊙_) (a ⊙_) _≃_}} →
      FnOpCommutative handᴿ f _⊙_
  fnOpCommutativeᴿ-from-compatible₁ = fnOpCommutative compat₁

module _ {A : Set} {_⊙_ _⊕_ : A → A → A} {{_ : Eq A}} where

  compatible₂-from-distributiveᴸ :
    {{_ : Distributive handᴸ _⊙_ _⊕_}} →
      ∀ {a} → Compatible₂ (a ⊙_) _⊕_ _⊕_ _≃_
  compatible₂-from-distributiveᴸ {a} = compatible₂ distrib

  distributiveᴸ-from-compatible₂ :
    {{_ : ∀ {a} → Compatible₂ (a ⊙_) _⊕_ _⊕_ _≃_}} →
      Distributive handᴸ _⊙_ _⊕_
  distributiveᴸ-from-compatible₂ = distributive compat₂

  compatible₂-from-distributiveᴿ :
    {{_ : Distributive handᴿ _⊙_ _⊕_}} →
      ∀ {a} → Compatible₂ (_⊙ a) _⊕_ _⊕_ _≃_
  compatible₂-from-distributiveᴿ {a} = compatible₂ distrib

  distributiveᴿ-from-compatible₂ :
    {{_ : ∀ {a} → Compatible₂ (_⊙ a) _⊕_ _⊕_ _≃_}} →
      Distributive handᴿ _⊙_ _⊕_
  distributiveᴿ-from-compatible₂ = distributive compat₂

module _
    {A : Set} {z : A} {_⊙_ : A → A → A} {{_ : Eq A}} {{_ : Absorptive² _⊙_ z}}
    where

  compatible₂-from-zero-product :
    {{r : ZeroProduct z _⊙_}} → Compatible₂ (_≃ z) _⊙_ _∨_ _⟨→⟩_
  compatible₂-from-zero-product = compatible₂ zero-prod

  zero-product-from-compatible₂ :
    {{_ : Compatible₂ (_≃ z) _⊙_ _∨_ _⟨→⟩_}} → ZeroProduct z _⊙_
  zero-product-from-compatible₂ = zeroProduct compat₂
