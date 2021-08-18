open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
open Eq.≃-Reasoning
open import net.cruhland.models.Function using (_⟨→⟩_)
open import net.cruhland.models.Literals
open import net.cruhland.models.Logic using (_∨_; ∨-rec; _↯_)

module net.cruhland.axioms.AbstractAlgebra.Compatible where

private
  module AA where
    open import net.cruhland.axioms.AbstractAlgebra.Base public

  record Semicompatible₂
      (hand : AA.Hand) {A B : Set}
        (f : A → B) (_⊙_ : A → A → A) (_~_ : B → B → Set) : Set where
    constructor semicompatible₂
    _<~>_ = AA.forHand hand _~_
    field
      _⊕_ : B → B → B
      semicompat₂ : ∀ {a b} → (f (a ⊙ b)) <~> (f a ⊕ f b)

  open Semicompatible₂ {{...}} using (semicompat₂)

record Compatible₁
    {β} {A : Set} {B : Set β} {C : A → Set}
    (f : (x : A) {{_ : C x}} → B) (g : A → A) (h : B → B) (_~_ : B → B → Set)
    : Set where
  constructor compatible₁
  field
    compat₁ : ∀ {a} {{_ : C a}} {{_ : C (g a)}} → f (g a) ~ h (f a)

open Compatible₁ {{...}} public using (compat₁)

record Associative {A : Set} {{eq : Eq A}} (_⊙_ : A → A → A) : Set where
  constructor associative
  field
    assoc : ∀ {a b c} → (a ⊙ b) ⊙ c ≃ a ⊙ (b ⊙ c)

open Associative {{...}} public using (assoc)

record Preserves {A : Set} (P : A → Set) (_⊙_ : A → A → A) : Set where
  constructor preserves
  field
    pres : ∀ {a b} → P a → P b → P (a ⊙ b)

open Preserves {{...}} public using (pres)

record Compatible₂
    {β} {A : Set} {B : Set β} {C : A → Set}
    (f : (x : A) {{_ : C x}} → B) (_⊙_ : A → A → A) (_⊕_ : B → B → B)
    (_~_ : B → B → Set)
    : Set where
  constructor compatible₂
  field
    compat₂ :
      ∀ {a b} {{Cab : C (a ⊙ b)}} {{Ca : C a}} {{Cb : C b}} →
      (f (a ⊙ b)) ~ (f a ⊕ f b)

open Compatible₂ {{...}} public using (compat₂)

record FnOpCommutative
    (hand : AA.Hand) {A B : Set} {{_ : Eq A}} {C : B → B → Set}
    (f : A → A) (g : B → B) (_⊙_ : (x y : B) {{_ : C x y}} → A)
    : Set where
  constructor fnOpCommutative
  field
    fnOpComm :
      ∀ {a b} {{c₁ : C a b}} →
      AA.handRec
        ({{c₂ : C (g a) b}} → f (a ⊙ b) ≃ g a ⊙ b)
        ({{c₂ : C a (g b)}} → f (a ⊙ b) ≃ a ⊙ g b)
        hand

open FnOpCommutative {{...}} public using (fnOpComm)

fnOpCommᴸ = fnOpComm {AA.handᴸ}
fnOpCommᴿ = fnOpComm {AA.handᴿ}

fnOpCommSwap :
  {A : Set} {f : A → A} {_⊙_ : A → A → A} {{_ : Eq A}}
  {{_ : FnOpCommutative AA.handᴸ f f (AA.tc₂ _⊙_)}}
  {{_ : FnOpCommutative AA.handᴿ f f (AA.tc₂ _⊙_)}} →
  ∀ {a b} → f a ⊙ b ≃ a ⊙ f b
fnOpCommSwap {A} {f} {_⊙_} {a} {b} =
  begin
    f a ⊙ b
  ≃˘⟨ fnOpCommᴸ ⟩
    f (a ⊙ b)
  ≃⟨ fnOpCommᴿ ⟩
    a ⊙ f b
  ∎

record FnOpCommutative²
    {A B : Set} {{_ : Eq A}} {C : B → B → Set} (f : A → A) (g : B → B)
    (_⊙_ : (x y : B) {{_ : C x y}} → A)
    : Set where
  constructor fnOpCommutative²
  field
    {{fnOpCommutativeᴸ}} : FnOpCommutative AA.handᴸ f g _⊙_
    {{fnOpCommutativeᴿ}} : FnOpCommutative AA.handᴿ f g _⊙_

record Distributive
    (hand : AA.Hand) {A : Set} {{_ : Eq A}} {C : A → A → Set}
    (_⊙_ : (x y : A) {{_ : C x y}} → A) (_⊕_ : A → A → A)
    : Set where
  constructor distributive
  C˘ = AA.forHand hand C
  _⊙˘_ = AA.forHandᶜ hand _⊙_
  field
    distrib :
      ∀ {a b c} {{Cabc : C˘ a (b ⊕ c)}} {{Cab : C˘ a b}} {{Cac : C˘ a c}} →
      a ⊙˘ (b ⊕ c) ≃ (a ⊙˘ b) ⊕ (a ⊙˘ c)

open Distributive {{...}} public using (distrib)

distribᴸ = distrib {AA.handᴸ}
distribᴿ = distrib {AA.handᴿ}

record Distributive²
    {A : Set} {{_ : Eq A}} {C : A → A → Set}
    (_⊙_ : (x y : A) {{_ : C x y}} → A) (_⊕_ : A → A → A)
    : Set where
  constructor distributive²
  field
    {{distributiveᴸ}} : Distributive AA.handᴸ _⊙_ _⊕_
    {{distributiveᴿ}} : Distributive AA.handᴿ _⊙_ _⊕_

record ZeroProduct
    {A : Set} (_⊙_ : A → A → A) {{_ : Eq A}} {{_ : FromNatLiteral A}}
    : Set where
  constructor zeroProduct
  field
    zero-prod : ∀ {a b} → a ⊙ b ≃ 0 → a ≃ 0 ∨ b ≃ 0

open ZeroProduct {{...}} public using (zero-prod)

nonzero-prod :
  {A : Set} {_⊙_ : A → A → A}
  {{_ : Eq A}} {{_ : FromNatLiteral A}} {{r : ZeroProduct _⊙_}} →
  ∀ {a b} {{a≄0 : a ≄ 0}} {{b≄0 : b ≄ 0}} → a ⊙ b ≄ 0
nonzero-prod {{a≄0 = a≄0}} {{b≄0}} = Eq.≄-intro λ ab≃0 →
  ∨-rec (_↯ a≄0) (_↯ b≄0) (zero-prod ab≃0)

{--- Equivalences ---}

module _
    {β} {A : Set} {B : Set β} {f : A → B}
      {_⊙_ : A → A → A} {_⊕_ : B → B → B} {_~_ : B → B → Set} where

  compatible₁-from-compatible₂ :
    {{_ : Compatible₂ (AA.tc₁ f) _⊙_ _⊕_ _~_}} →
      ∀ {b} → Compatible₁ (AA.tc₁ f) (_⊙ b) (_⊕ f b) _~_
  compatible₁-from-compatible₂ = compatible₁ compat₂

  compatible₂-from-compatible₁ :
    {{_ : ∀ {b} → Compatible₁ (AA.tc₁ f) (_⊙ b) (_⊕ f b) _~_}} →
      Compatible₂ (AA.tc₁ f) _⊙_ _⊕_ _~_
  compatible₂-from-compatible₁ = compatible₂ compat₁

-- TODO Equivalences for Semicompatible₂ and Preserves

module _ {A : Set} {f : A → A} {_⊙_ : A → A → A} {{_ : Eq A}} where

  compatible₁-from-fnOpCommutativeᴸ :
    {{_ : FnOpCommutative AA.handᴸ f f (AA.tc₂ _⊙_)}} →
      ∀ {b} → Compatible₁ (AA.tc₁ f) (_⊙ b) (_⊙ b) _≃_
  compatible₁-from-fnOpCommutativeᴸ = compatible₁ fnOpCommᴸ

  fnOpCommutativeᴸ-from-compatible₁ :
    {{_ : ∀ {b} → Compatible₁ (AA.tc₁ f) (_⊙ b) (_⊙ b) _≃_}} →
      FnOpCommutative AA.handᴸ f f (AA.tc₂ _⊙_)
  fnOpCommutativeᴸ-from-compatible₁ = fnOpCommutative compat₁

  compatible₁-from-fnOpCommutativeᴿ :
    {{_ : FnOpCommutative AA.handᴿ f f (AA.tc₂ _⊙_)}} →
      ∀ {a} → Compatible₁ (AA.tc₁ f) (a ⊙_) (a ⊙_) _≃_
  compatible₁-from-fnOpCommutativeᴿ = compatible₁ fnOpCommᴿ

  fnOpCommutativeᴿ-from-compatible₁ :
    {{_ : ∀ {a} → Compatible₁ (AA.tc₁ f) (a ⊙_) (a ⊙_) _≃_}} →
      FnOpCommutative AA.handᴿ f f (AA.tc₂ _⊙_)
  fnOpCommutativeᴿ-from-compatible₁ = fnOpCommutative compat₁

module _ {A : Set} {_⊙_ _⊕_ : A → A → A} {{_ : Eq A}} where

  compatible₂-from-distributiveᴸ :
    {{_ : Distributive AA.handᴸ (AA.tc₂ _⊙_) _⊕_}} →
      ∀ {a} → Compatible₂ (AA.tc₁ (a ⊙_)) _⊕_ _⊕_ _≃_
  compatible₂-from-distributiveᴸ {a} = compatible₂ distrib

  distributiveᴸ-from-compatible₂ :
    {{_ : ∀ {a} → Compatible₂ (AA.tc₁ (a ⊙_)) _⊕_ _⊕_ _≃_}} →
      Distributive AA.handᴸ (AA.tc₂ _⊙_) _⊕_
  distributiveᴸ-from-compatible₂ = distributive compat₂

  compatible₂-from-distributiveᴿ :
    {{_ : Distributive AA.handᴿ (AA.tc₂ _⊙_) _⊕_}} →
      ∀ {a} → Compatible₂ (AA.tc₁ (_⊙ a)) _⊕_ _⊕_ _≃_
  compatible₂-from-distributiveᴿ {a} = compatible₂ distrib

  distributiveᴿ-from-compatible₂ :
    {{_ : ∀ {a} → Compatible₂ (AA.tc₁ (_⊙ a)) _⊕_ _⊕_ _≃_}} →
      Distributive AA.handᴿ (AA.tc₂ _⊙_) _⊕_
  distributiveᴿ-from-compatible₂ = distributive compat₂

module _ {A : Set} {_⊙_ : A → A → A} {{_ : Eq A}} {{_ : FromNatLiteral A}} where

  compatible₂-from-zero-product :
    {{r : ZeroProduct _⊙_}} → Compatible₂ (AA.tc₁ (_≃ 0)) _⊙_ _∨_ _⟨→⟩_
  compatible₂-from-zero-product = compatible₂ zero-prod

  zero-product-from-compatible₂ :
    {{_ : Compatible₂ (AA.tc₁ (_≃ 0)) _⊙_ _∨_ _⟨→⟩_}} → ZeroProduct _⊙_
  zero-product-from-compatible₂ = zeroProduct compat₂
