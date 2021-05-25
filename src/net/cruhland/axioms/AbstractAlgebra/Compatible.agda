module net.cruhland.axioms.AbstractAlgebra.Compatible where

open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
open import net.cruhland.models.Function using (_∘_; _⟨→⟩_)
open import net.cruhland.models.Logic using (_∨_; ∨-rec)

open import net.cruhland.axioms.AbstractAlgebra.Base using
  (forHand; Hand; handᴸ; handᴿ; handRec)
open import net.cruhland.axioms.AbstractAlgebra.Reductive using (Absorptive)

private
  record IsCompatible₁
      {β} {A : Set} {B : Set β}
        (f : A → B) (g : A → A) (h : B → B) (_~_ : B → B → Set) : Set where
    constructor isCompatible₁
    field
      isCompat₁ : ∀ {a} → f (g a) ~ h (f a)

  open IsCompatible₁ {{...}} using (isCompat₁)

  record IsCompatible₂
      {β} {A : Set} {B : Set β}
        (f : A → B) (_⊙_ : A → A → A) (_⊕_ : B → B → B) (_~_ : B → B → Set)
          : Set where
    constructor isCompatible₂
    field
      isCompat₂ : ∀ {a b} → (f (a ⊙ b)) ~ (f a ⊕ f b)

  open IsCompatible₂ {{...}} using (isCompat₂)

  record Semicompatible₂
      (hand : Hand) {A B : Set}
        (f : A → B) (_⊙_ : A → A → A) (_~_ : B → B → Set) : Set where
    constructor semicompatible₂
    _<~>_ = forHand hand _~_
    field
      _⊕_ : B → B → B
      semicompat₂ : ∀ {a b} → (f (a ⊙ b)) <~> (f a ⊕ f b)

  open Semicompatible₂ {{...}} using (semicompat₂)

record Compatible₁ {A B : Set} {{_ : Eq B}} (f : A → B) (g : A → A) : Set where
  constructor compatible₁
  field
    h : B → B
    compat₁ : ∀ {a} → f (g a) ≃ h (f a)

open Compatible₁ {{...}} public using (compat₁)

record Preserves {A : Set} (P : A → Set) (_⊙_ : A → A → A) : Set where
  constructor preserves
  field
    pres : ∀ {a b} → P a → P b → P (a ⊙ b)

open Preserves {{...}} public using (pres)

record Compatible₂
    {A B : Set} {{_ : Eq B}} (f : A → B) (_⊙_ : A → A → A) : Set where
  constructor compatible₂
  field
    _⊕_ : B → B → B
    compat₂ : ∀ {a b} → f (a ⊙ b) ≃ f a ⊕ f b

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

record ZeroProduct {A : Set} {{_ : Eq A}} (_⊙_ : A → A → A) : Set where
  constructor zeroProduct
  field
    z : A
    {{absorptiveᴸ}} : Absorptive handᴸ _⊙_ z
    {{absorptiveᴿ}} : Absorptive handᴿ _⊙_ z
    zero-prod : ∀ {a b} → a ⊙ b ≃ z → a ≃ z ∨ b ≃ z

open ZeroProduct {{...}} public using (zero-prod)

nonzero-prod :
  {A : Set} {_⊙_ : A → A → A} →
    ∀ {a b} {{_ : Eq A}} {{r : ZeroProduct _⊙_}} →
      let open ZeroProduct r using (z) in a ≄ z → b ≄ z → a ⊙ b ≄ z
nonzero-prod a≄z b≄z = ∨-rec a≄z b≄z ∘ zero-prod

{--- Equivalences ---}

module _ {A B : Set} {f : A → B} {g : A → A} {{_ : Eq B}} where

  isCompatible₁-from-compatible₁ :
    {{r : Compatible₁ f g}} →
      let open Compatible₁ r using (h) in IsCompatible₁ f g h _≃_
  isCompatible₁-from-compatible₁ = isCompatible₁ compat₁

  compatible₁-from-isCompatible₁ :
    {h : B → B} {{_ : IsCompatible₁ f g h _≃_}} → Compatible₁ f g
  compatible₁-from-isCompatible₁ {h} = compatible₁ h isCompat₁

module _
    {β} {A : Set} {B : Set β} {f : A → B}
      {_⊙_ : A → A → A} {_⊕_ : B → B → B} {_~_ : B → B → Set} where

  isCompatible₁-from-isCompatible₂ :
    {{_ : IsCompatible₂ f _⊙_ _⊕_ _~_}} →
      ∀ {b} → IsCompatible₁ f (_⊙ b) (_⊕ f b) _~_
  isCompatible₁-from-isCompatible₂ = isCompatible₁ isCompat₂

  isCompatible₂-from-isCompatible₁ :
    {{_ : ∀ {b} → IsCompatible₁ f (_⊙ b) (_⊕ f b) _~_}} →
      IsCompatible₂ f _⊙_ _⊕_ _~_
  isCompatible₂-from-isCompatible₁ = isCompatible₂ isCompat₁

-- TODO Equivalences for Semicompatible₂ and Preserves

module _ {A B : Set} {f : A → B} {_⊙_ : A → A → A} {{_ : Eq B}} where

  isCompatible₂-from-compatible₂ :
    {{r : Compatible₂ f _⊙_}} →
      let open Compatible₂ r using (_⊕_) in IsCompatible₂ f _⊙_ _⊕_ _≃_
  isCompatible₂-from-compatible₂ = isCompatible₂ compat₂

  compatible₂-from-isCompatible₂ :
    {_⊕_ : B → B → B} {{_ : IsCompatible₂ f _⊙_ _⊕_ _≃_}} → Compatible₂ f _⊙_
  compatible₂-from-isCompatible₂ {_⊕_} = compatible₂ _⊕_ isCompat₂

module _ {A : Set} {f : A → A} {_⊙_ : A → A → A} {{_ : Eq A}} where

  isCompatible₁-from-fnOpCommutativeᴸ :
    {{_ : FnOpCommutative handᴸ f _⊙_}} →
      ∀ {b} → IsCompatible₁ f (_⊙ b) (_⊙ b) _≃_
  isCompatible₁-from-fnOpCommutativeᴸ = isCompatible₁ fnOpComm

  fnOpCommutativeᴸ-from-isCompatible₁ :
    {{_ : ∀ {b} → IsCompatible₁ f (_⊙ b) (_⊙ b) _≃_}} →
      FnOpCommutative handᴸ f _⊙_
  fnOpCommutativeᴸ-from-isCompatible₁ = fnOpCommutative isCompat₁

  isCompatible₁-from-fnOpCommutativeᴿ :
    {{_ : FnOpCommutative handᴿ f _⊙_}} →
      ∀ {a} → IsCompatible₁ f (a ⊙_) (a ⊙_) _≃_
  isCompatible₁-from-fnOpCommutativeᴿ = isCompatible₁ fnOpComm

  fnOpCommutativeᴿ-from-isCompatible₁ :
    {{_ : ∀ {a} → IsCompatible₁ f (a ⊙_) (a ⊙_) _≃_}} →
      FnOpCommutative handᴿ f _⊙_
  fnOpCommutativeᴿ-from-isCompatible₁ = fnOpCommutative isCompat₁

module _ {A : Set} {_⊙_ _⊕_ : A → A → A} {{_ : Eq A}} where

  isCompatible₂-from-distributiveᴸ :
    {{_ : Distributive handᴸ _⊙_ _⊕_}} →
      ∀ {a} → IsCompatible₂ (a ⊙_) _⊕_ _⊕_ _≃_
  isCompatible₂-from-distributiveᴸ {a} = isCompatible₂ distrib

  distributiveᴸ-from-isCompatible₂ :
    {{_ : ∀ {a} → IsCompatible₂ (a ⊙_) _⊕_ _⊕_ _≃_}} →
      Distributive handᴸ _⊙_ _⊕_
  distributiveᴸ-from-isCompatible₂ = distributive isCompat₂

  isCompatible₂-from-distributiveᴿ :
    {{_ : Distributive handᴿ _⊙_ _⊕_}} →
      ∀ {a} → IsCompatible₂ (_⊙ a) _⊕_ _⊕_ _≃_
  isCompatible₂-from-distributiveᴿ {a} = isCompatible₂ distrib

  distributiveᴿ-from-isCompatible₂ :
    {{_ : ∀ {a} → IsCompatible₂ (_⊙ a) _⊕_ _⊕_ _≃_}} →
      Distributive handᴿ _⊙_ _⊕_
  distributiveᴿ-from-isCompatible₂ = distributive isCompat₂

module _ {A : Set} {_⊙_ : A → A → A} {{_ : Eq A}} where

  isCompatible₂-from-zero-product :
    {{r : ZeroProduct _⊙_}} →
      let open ZeroProduct r using (z) in IsCompatible₂ (_≃ z) _⊙_ _∨_ _⟨→⟩_
  isCompatible₂-from-zero-product = isCompatible₂ zero-prod

  zero-product-from-isCompatible₂ :
    ∀ {z} {{_ : Absorptive handᴸ _⊙_ z}} {{_ : Absorptive handᴿ _⊙_ z}}
      {{_ : IsCompatible₂ (_≃ z) _⊙_ _∨_ _⟨→⟩_}} → ZeroProduct _⊙_
  zero-product-from-isCompatible₂ {z} = zeroProduct z isCompat₂
