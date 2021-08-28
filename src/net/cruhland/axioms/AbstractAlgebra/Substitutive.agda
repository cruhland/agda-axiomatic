open import Level using (_⊔_)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
open Eq.≃-Reasoning
open import net.cruhland.models.Function using (_∘_; _⟨→⟩_; const)
import net.cruhland.models.Function.Properties
open import net.cruhland.models.Logic using (⊤; contrapositive)

module net.cruhland.axioms.AbstractAlgebra.Substitutive where

private
  module AA where
    open import net.cruhland.axioms.AbstractAlgebra.Base public
    open import net.cruhland.axioms.AbstractAlgebra.Compatible public
    open import net.cruhland.axioms.AbstractAlgebra.Swappable public

record Substitutive₁ᶜ
    {β} {A : Set} {B : A → Set β} {C : A → Set} (f : (a : A) {{_ : C a}} → B a)
    (_~_ : A → A → Set) (_≈_ : ∀ {a₁ a₂} → B a₁ → B a₂ → Set) : Set β where
  constructor substitutive₁
  field
    subst₁ : ∀ {a₁ a₂} {{c₁ : C a₁}} {{c₂ : C a₂}} → a₁ ~ a₂ → f a₁ ≈ f a₂

open Substitutive₁ᶜ {{...}} public using (subst₁)

Substitutive₁ :
  ∀ {β} {A : Set} {B : A → Set β} (f : (a : A) → B a) (_~_ : A → A → Set)
  (_≈_ : ∀ {a₁ a₂} → B a₁ → B a₂ → Set) → Set β
Substitutive₁ f = Substitutive₁ᶜ (AA.tc₁ f)

record Substitutive₂ᶜ
    (hand : AA.Hand) {α β χ δ} {A : Set α} {B : Set β} {C : A → A → Set}
    (_⊙_ : (x y : A) {{_ : C x y}} → B)
    (_~_ : A → A → Set χ) (_≈_ : B → B → Set δ) (Cb : A → Set)
    : Set (α ⊔ χ ⊔ δ) where
  constructor substitutive₂
  C˘ = AA.forHand hand C
  _⊙˘_ = AA.forHandᶜ hand _⊙_
  field
    subst₂ :
      ∀ {a₁ a₂ b} {{cb : Cb b}} {{c₁ : C˘ a₁ b}} {{c₂ : C˘ a₂ b}} →
      a₁ ~ a₂ → (a₁ ⊙˘ b) ≈ (a₂ ⊙˘ b)

open Substitutive₂ᶜ {{...}} public using (subst₂)

substᴸ = subst₂ {AA.handᴸ}
substᴿ = subst₂ {AA.handᴿ}

Substitutive₂ :
  AA.Hand → ∀ {α β χ δ} {A : Set α} {B : Set β} (_⊙_ : A → A → B)
  (_~_ : A → A → Set χ) (_≈_ : B → B → Set δ) → Set (α ⊔ χ ⊔ δ)
Substitutive₂ hand _⊙_ _~_ _≈_ =
  Substitutive₂ᶜ hand (AA.tc₂ _⊙_) _~_ _≈_ (const ⊤)

substitutiveᴿ-from-substitutiveᴸ :
  ∀ {α β χ δ} {A : Set α} {B : Set β} {_⊙_ : A → A → B} {_~_ : A → A → Set χ}
  {_≈_ : B → B → Set δ} {{_ : Eq.Transitive _≈_}} {{_ : AA.Swappable _⊙_ _≈_}} →
  {{_ : Substitutive₂ AA.handᴸ _⊙_ _~_ _≈_}} →
  Substitutive₂ AA.handᴿ _⊙_ _~_ _≈_
substitutiveᴿ-from-substitutiveᴸ = substitutive₂ (AA.with-swap ∘ subst₂)

record Substitutive²ᶜ
    {α β χ δ} {A : Set α} {B : Set β} {C : A → A → Set}
    (_⊙_ : (x y : A) {{_ : C x y}} → B)
    (_~_ : A → A → Set χ) (_≈_ : B → B → Set δ) (Cb : A → Set)
    : Set (α ⊔ χ ⊔ δ) where
  constructor substitutive²
  field
    {{substitutiveᴸ}} : Substitutive₂ᶜ AA.handᴸ _⊙_ _~_ _≈_ Cb
    {{substitutiveᴿ}} : Substitutive₂ᶜ AA.handᴿ _⊙_ _~_ _≈_ Cb

Substitutive² :
  ∀ {α β χ δ} {A : Set α} {B : Set β} (_⊙_ : A → A → B) (_~_ : A → A → Set χ)
  (_≈_ : B → B → Set δ) → Set (α ⊔ χ ⊔ δ)
Substitutive² _⊙_ _~_ _≈_ = Substitutive²ᶜ (AA.tc₂ _⊙_) _~_ _≈_ (const ⊤)

module _ {β} {A : Set} {B : Set β} {_⊙_ : A → A → B} {{_ : Eq B}} where

  swappable-from-commutative :
    {_~_ : B → B → Set β} {{_ : AA.Commutative _⊙_}} {{_ : Eq.Reflexive _~_}}
      {{_ : Substitutive₂ AA.handᴿ _~_ _≃_ _⟨→⟩_}} → AA.Swappable _⊙_ _~_
  swappable-from-commutative = AA.swappable (subst₂ AA.comm Eq.refl)

  commutative-from-swappable : {{_ : AA.Swappable _⊙_ _≃_}} → AA.Commutative _⊙_
  commutative-from-swappable = AA.commutative AA.swap

[a≃b][c≃d] :
  {A B : Set} {_⊙_ : A → A → B}
    {{_ : Eq A}} {{_ : Eq B}} {{_ : Substitutive² _⊙_ _≃_ _≃_}} →
      ∀ {a b c d} → a ≃ b → c ≃ d → a ⊙ c ≃ b ⊙ d
[a≃b][c≃d] {A} {B} {_⊙_} {a} {b} {c} {d} a≃b c≃d =
  begin
    a ⊙ c
  ≃⟨ subst₂ a≃b ⟩
    b ⊙ c
  ≃⟨ subst₂ c≃d ⟩
    b ⊙ d
  ∎

fnOpCommutativeᴿ-from-fnOpCommutativeᴸ :
  {A : Set} {f : A → A} {_⊙_ : A → A → A} {{_ : Eq A}}
  {{_ : Substitutive₁ f _≃_ _≃_}} {{_ : AA.Commutative _⊙_}}
  {{_ : AA.FnOpCommutative AA.handᴸ f f (AA.tc₂ _⊙_)}} →
  AA.FnOpCommutative AA.handᴿ f f (AA.tc₂ _⊙_)
fnOpCommutativeᴿ-from-fnOpCommutativeᴸ {A} {f} {_⊙_} = AA.fnOpCommutative commᴿ₀
  where
    commᴿ₀ : ∀ {a b} → f (a ⊙ b) ≃ a ⊙ f b
    commᴿ₀ {a} {b} =
      begin
        f (a ⊙ b)
      ≃⟨ subst₁ AA.comm ⟩
        f (b ⊙ a)
      ≃⟨ AA.fnOpCommᴸ ⟩
        f b ⊙ a
      ≃⟨ AA.comm ⟩
        a ⊙ f b
      ∎

module EqProperties {α} {A : Set α} {{_ : Eq A}} where

  ≃-substitutiveᴸ : Substitutive₂ AA.handᴸ _≃_ _≃_ _⟨→⟩_
  ≃-substitutiveᴸ = substitutive₂ ≃-substᴸ
    where
      ≃-substᴸ : {a₁ a₂ b : A} → a₁ ≃ a₂ → a₁ ≃ b → a₂ ≃ b
      ≃-substᴸ a₁≃a₂ a₁≃b = Eq.trans (Eq.sym a₁≃a₂) a₁≃b

  ≃-substitutiveᴿ : Substitutive₂ AA.handᴿ _≃_ _≃_ _⟨→⟩_
  ≃-substitutiveᴿ = substitutiveᴿ-from-substitutiveᴸ
    where
      instance ≃-swappable = AA.swappable-from-symmetric
      instance ≃-substᴸ = ≃-substitutiveᴸ

  ≃-substitutive² : Substitutive² _≃_ _≃_ _⟨→⟩_
  ≃-substitutive² = substitutive²
    where
      instance ≃-substᴸ = ≃-substitutiveᴸ
      instance ≃-substᴿ = ≃-substitutiveᴿ

module _ {A : Set} {{_ : Eq A}} where

  instance
    ≄-substitutiveᴸ : Substitutive₂ AA.handᴸ _≄_ _≃_ _⟨→⟩_
    ≄-substitutiveᴸ = substitutive₂ ≄-substᴸ
      where
        ≄-substᴸ : {a₁ a₂ b : A} → a₁ ≃ a₂ → a₁ ≄ b → a₂ ≄ b
        ≄-substᴸ a₁≃a₂ a₁≄b = contrapositive (Eq.trans a₁≃a₂) a₁≄b

    ≄-substitutiveᴿ : Substitutive₂ AA.handᴿ _≄_ _≃_ _⟨→⟩_
    ≄-substitutiveᴿ = substitutiveᴿ-from-substitutiveᴸ
      where
        instance ≄-swappable = AA.swappable-from-symmetric

    ≄-substitutive² : Substitutive² _≄_ _≃_ _⟨→⟩_
    ≄-substitutive² = substitutive²

module NeqProperties {A : Set} {{_ : Eq A}} where

  ≄-substitutive₁ᴸ : {z : A} → Substitutive₁ (_≄ z) _≃_ _⟨→⟩_
  ≄-substitutive₁ᴸ {z} = substitutive₁ ≄z-subst
    where
      ≄z-subst : {x y : A} → x ≃ y → x ≄ z → y ≄ z
      ≄z-subst = substᴸ

with-comm :
  {A : Set} {_⊙_ : A → A → A} {{_ : Eq A}} {{_ : AA.Commutative _⊙_}} →
    ∀ {a b c d} → b ⊙ a ≃ d ⊙ c → a ⊙ b ≃ c ⊙ d
with-comm = AA.with-swap
  where
    instance ⊙-swap = swappable-from-commutative
    instance ≃-substᴿ = EqProperties.≃-substitutiveᴿ

substᴿ-from-substᴸ-comm :
  ∀ {β} {A : Set} {B : Set β} {_⊙_ : A → A → B} {_~_ : A → A → Set} {{_ : Eq B}}
  {{_ : AA.Commutative _⊙_}} {{_ : Substitutive₂ AA.handᴸ _⊙_ _~_ _≃_}} →
  Substitutive₂ AA.handᴿ _⊙_ _~_ _≃_
substᴿ-from-substᴸ-comm = substitutiveᴿ-from-substitutiveᴸ
  where
    instance ⊙-swap = swappable-from-commutative
    instance ≃-substᴿ = EqProperties.≃-substitutiveᴿ

substᴿ-from-substᴸ-comm₂ :
  {A : Set} {_⊙_ : A → A → A} {_~_ : A → A → Set} {Cb : A → Set} {{_ : Eq A}}
  {{_ : AA.Commutative _⊙_}} {{_ : Substitutive² _~_ _≃_ _⟨→⟩_}}
  {{_ : Substitutive₂ᶜ AA.handᴸ (AA.tc₂ _⊙_) _~_ _~_ Cb}} →
  Substitutive₂ᶜ AA.handᴿ (AA.tc₂ _⊙_) _~_ _~_ Cb
substᴿ-from-substᴸ-comm₂ =
  substitutive₂ λ a₁~a₂ → substᴸ AA.comm (substᴿ AA.comm (subst₂ a₁~a₂))
