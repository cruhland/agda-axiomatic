module net.cruhland.axioms.AbstractAlgebra.Substitutive where

open import Level using (_⊔_; 0ℓ) renaming (suc to sℓ)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
open Eq.≃-Reasoning
open import net.cruhland.models.Function using
  (_∘_; _⟨→⟩_; ConstrainableFn; toExpFn)
import net.cruhland.models.Function.Properties
open import net.cruhland.models.Logic using (⊤; contra)

open import net.cruhland.axioms.AbstractAlgebra.Base using
  (forHand; forHandᶜ; Hand; handᴸ; handᴿ)
open import net.cruhland.axioms.AbstractAlgebra.Compatible using
  (fnOpComm; FnOpCommutative; fnOpCommutative)
open import net.cruhland.axioms.AbstractAlgebra.Swappable using
  (comm; Commutative; commutative; swap; Swappable; swappable
  ; swappable-from-symmetric; with-swap
  )

record Substitutive₁
    {β} {A : Set} {B : A → Set β} (f : (a : A) → B a)
      (_~_ : A → A → Set) (_≈_ : ∀ {a₁ a₂} → B a₁ → B a₂ → Set) : Set β where
  constructor substitutive₁
  field
    subst₁ : ∀ {a₁ a₂} → a₁ ~ a₂ → f a₁ ≈ f a₂

open Substitutive₁ {{...}} public using (subst₁)

record Substitutiveᶜ
    {β} {A F : Set} {B : A → Set β} (fn : F) (C : A → Set) (_~_ : A → A → Set)
    (_≈_ : ∀ {a₁ a₂} → B a₁ → B a₂ → Set)
    : Set β where
  constructor substitutiveᶜ
  field
    {{cf}} : ConstrainableFn F C B

  f = toExpFn fn

  field
    substᶜ : ∀ {a₁ a₂} {{c₁ : C a₁}} {{c₂ : C a₂}} → a₁ ~ a₂ → f a₁ ≈ f a₂

open Substitutiveᶜ {{...}} public using (substᶜ)

record Substitutive₂ᶜ
    (hand : Hand) {α β χ δ} {A : Set α} {B : Set β} {C : A → A → Set}
    (_⊙_ : (x y : A) {{_ : C x y}} → B)
    (_~_ : A → A → Set χ) (_≈_ : B → B → Set δ)
    : Set (α ⊔ χ ⊔ δ) where
  constructor substitutive₂
  C˘ = forHand hand C
  _⊙˘_ = forHandᶜ hand _⊙_
  field
    subst₂ :
      ∀ {a₁ a₂ b} {{c₁ : C˘ a₁ b}} {{c₂ : C˘ a₂ b}} →
      a₁ ~ a₂ → (a₁ ⊙˘ b) ≈ (a₂ ⊙˘ b)

open Substitutive₂ᶜ {{...}} public using (subst₂)

substᴸ = subst₂ {handᴸ}
substᴿ = subst₂ {handᴿ}

-- Short for "trivial constraint"
tc : ∀ {α β} {A : Set α} {B : Set β} → (A → A → B) → (A → A → {{_ : ⊤}} → B)
tc f x y = f x y

Substitutive₂ :
  Hand → ∀ {α β χ δ} {A : Set α} {B : Set β} (_⊙_ : A → A → B)
  (_~_ : A → A → Set χ) (_≈_ : B → B → Set δ) → Set (α ⊔ χ ⊔ δ)
Substitutive₂ hand _⊙_ = Substitutive₂ᶜ hand (tc _⊙_)

substitutiveᴿ-from-substitutiveᴸ :
  ∀ {α β χ δ} {A : Set α} {B : Set β} {_⊙_ : A → A → B} {_~_ : A → A → Set χ}
  {_≈_ : B → B → Set δ} {{_ : Eq.Transitive _≈_}} {{_ : Swappable _⊙_ _≈_}} →
  {{_ : Substitutive₂ handᴸ _⊙_ _~_ _≈_}} →
  Substitutive₂ handᴿ _⊙_ _~_ _≈_
substitutiveᴿ-from-substitutiveᴸ = substitutive₂ (with-swap ∘ subst₂)

record Substitutive²ᶜ
    {α β χ δ} {A : Set α} {B : Set β} {C : A → A → Set}
    (_⊙_ : (x y : A) {{_ : C x y}} → B)
    (_~_ : A → A → Set χ) (_≈_ : B → B → Set δ)
    : Set (α ⊔ χ ⊔ δ) where
  constructor substitutive²
  field
    {{substitutiveᴸ}} : Substitutive₂ᶜ handᴸ _⊙_ _~_ _≈_
    {{substitutiveᴿ}} : Substitutive₂ᶜ handᴿ _⊙_ _~_ _≈_

Substitutive² :
  ∀ {α β χ δ} {A : Set α} {B : Set β} (_⊙_ : A → A → B) (_~_ : A → A → Set χ)
  (_≈_ : B → B → Set δ) → Set (α ⊔ χ ⊔ δ)
Substitutive² _⊙_ = Substitutive²ᶜ (tc _⊙_)

module _ {β} {A : Set} {B : Set β} {_⊙_ : A → A → B} {{_ : Eq B}} where

  swappable-from-commutative :
    {_~_ : B → B → Set β} {{_ : Commutative _⊙_}} {{_ : Eq.Reflexive _~_}}
      {{_ : Substitutive₂ handᴿ _~_ _≃_ _⟨→⟩_}} → Swappable _⊙_ _~_
  swappable-from-commutative = swappable (subst₂ comm Eq.refl)

  commutative-from-swappable : {{_ : Swappable _⊙_ _≃_}} → Commutative _⊙_
  commutative-from-swappable = commutative swap

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
  {A : Set} {f : A → A} {_⊙_ : A → A → A}
    {{_ : Eq A}} {{_ : Substitutive₁ f _≃_ _≃_}}
    {{_ : Commutative _⊙_}} {{_ : FnOpCommutative handᴸ f _⊙_}} →
      FnOpCommutative handᴿ f _⊙_
fnOpCommutativeᴿ-from-fnOpCommutativeᴸ {A} {f} {_⊙_} = fnOpCommutative commᴿ₀
  where
    commᴿ₀ : ∀ {a b} → f (a ⊙ b) ≃ a ⊙ f b
    commᴿ₀ {a} {b} =
      begin
        f (a ⊙ b)
      ≃⟨ subst₁ comm ⟩
        f (b ⊙ a)
      ≃⟨ fnOpComm ⟩
        f b ⊙ a
      ≃⟨ comm ⟩
        a ⊙ f b
      ∎

module EqProperties {α} {A : Set α} {{_ : Eq A}} where

  ≃-substitutiveᴸ : Substitutive₂ handᴸ _≃_ _≃_ _⟨→⟩_
  ≃-substitutiveᴸ = substitutive₂ ≃-substᴸ
    where
      ≃-substᴸ : {a₁ a₂ b : A} → a₁ ≃ a₂ → a₁ ≃ b → a₂ ≃ b
      ≃-substᴸ a₁≃a₂ a₁≃b = Eq.trans (Eq.sym a₁≃a₂) a₁≃b

  ≃-substitutiveᴿ : Substitutive₂ handᴿ _≃_ _≃_ _⟨→⟩_
  ≃-substitutiveᴿ = substitutiveᴿ-from-substitutiveᴸ
    where
      instance ≃-swappable = swappable-from-symmetric
      instance ≃-substᴸ = ≃-substitutiveᴸ

  ≃-substitutive² : Substitutive² _≃_ _≃_ _⟨→⟩_
  ≃-substitutive² = substitutive²
    where
      instance ≃-substᴸ = ≃-substitutiveᴸ
      instance ≃-substᴿ = ≃-substitutiveᴿ

module _ {A : Set} {{_ : Eq A}} where

  instance
    ≄-substitutiveᴸ : Substitutive₂ handᴸ _≄_ _≃_ _⟨→⟩_
    ≄-substitutiveᴸ = substitutive₂ ≄-substᴸ
      where
        ≄-substᴸ : {a₁ a₂ b : A} → a₁ ≃ a₂ → a₁ ≄ b → a₂ ≄ b
        ≄-substᴸ a₁≃a₂ a₁≄b a₂≃b = contra (Eq.trans a₁≃a₂ a₂≃b) a₁≄b

    ≄-substitutiveᴿ : Substitutive₂ handᴿ _≄_ _≃_ _⟨→⟩_
    ≄-substitutiveᴿ = substitutiveᴿ-from-substitutiveᴸ
      where
        instance ≄-swappable = swappable-from-symmetric

    ≄-substitutive² : Substitutive² _≄_ _≃_ _⟨→⟩_
    ≄-substitutive² = substitutive²

with-comm :
  {A : Set} {_⊙_ : A → A → A} {{_ : Eq A}} {{_ : Commutative _⊙_}} →
    ∀ {a b c d} → b ⊙ a ≃ d ⊙ c → a ⊙ b ≃ c ⊙ d
with-comm = with-swap
  where
    instance ⊙-swap = swappable-from-commutative
    instance ≃-substᴿ = EqProperties.≃-substitutiveᴿ

substᴿ-from-substᴸ-comm :
  ∀ {β} {A : Set} {B : Set β} {_⊙_ : A → A → B} {_~_ : A → A → Set} {{_ : Eq B}}
  {{_ : Commutative _⊙_}} {{_ : Substitutive₂ handᴸ _⊙_ _~_ _≃_}} →
  Substitutive₂ handᴿ _⊙_ _~_ _≃_
substᴿ-from-substᴸ-comm = substitutiveᴿ-from-substitutiveᴸ
  where
    instance ⊙-swap = swappable-from-commutative
    instance ≃-substᴿ = EqProperties.≃-substitutiveᴿ

substᴿ-from-substᴸ-comm₂ :
  {A : Set} {_⊙_ : A → A → A} {_~_ : A → A → Set} {{_ : Eq A}}
  {{_ : Commutative _⊙_}} {{_ : Substitutive² _~_ _≃_ _⟨→⟩_}}
  {{_ : Substitutive₂ handᴸ _⊙_ _~_ _~_}} → Substitutive₂ handᴿ _⊙_ _~_ _~_
substᴿ-from-substᴸ-comm₂ =
  substitutive₂ λ a₁~a₂ → substᴸ comm (substᴿ comm (subst₂ a₁~a₂))
