module net.cruhland.axioms.AbstractAlgebra.Substitutive where

open import Level using (_⊔_; 0ℓ) renaming (suc to sℓ)
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
open Eq.≃-Reasoning
open import net.cruhland.models.Function using
  (_∘_; _⟨→⟩_; ConstrainableFn; toExpFn)
import net.cruhland.models.Function.Properties
open import net.cruhland.models.Logic using (⊤; contra)

open import net.cruhland.axioms.AbstractAlgebra.Base using
  (forHand; Hand; handᴸ; handᴿ)
open import net.cruhland.axioms.AbstractAlgebra.Compatible using
  (fnOpComm; FnOpCommutative; fnOpCommutative)
open import net.cruhland.axioms.AbstractAlgebra.Swappable using
  (comm; Commutative; Swappable; swappable-from-symmetric; with-swap)

record Substitutive₁
    {β} {A : Set} {B : A → Set β} (f : (a : A) → B a)
      (_~_ : A → A → Set) (_≈_ : ∀ {a₁ a₂} → B a₁ → B a₂ → Set) : Set β where
  constructor substitutive₁
  field
    subst₁ : ∀ {a₁ a₂} → a₁ ~ a₂ → f a₁ ≈ f a₂

open Substitutive₁ {{...}} public using (subst₁)

record Substitutiveᶜ
    {β} {A F : Set} {B : A → Set β}
      (fn : F) (_~_ : A → A → Set) (_≈_ : ∀ {a₁ a₂} → B a₁ → B a₂ → Set)
        : Set (β ⊔ sℓ 0ℓ) where
  constructor substitutiveᶜ
  field
    {{cf}} : ConstrainableFn F B

  open ConstrainableFn cf using (C)
  f = toExpFn fn

  field
    substᶜ : ∀ {a₁ a₂} {{c₁ : C a₁}} {{c₂ : C a₂}} → a₁ ~ a₂ → f a₁ ≈ f a₂

open Substitutiveᶜ {{...}} public using (substᶜ)

record Substitutive₂
    (hand : Hand) {β} {A : Set} {B : Set β}
      (_⊙_ : A → A → B) (_~_ : A → A → Set) (_≈_ : B → B → Set) : Set where
  constructor substitutive₂
  _<⊙>_ = forHand hand _⊙_
  field
    subst₂ : ∀ {a₁ a₂ b} → a₁ ~ a₂ → (a₁ <⊙> b) ≈ (a₂ <⊙> b)

open Substitutive₂ {{...}} public using (subst₂)

substᴸ = subst₂ {handᴸ}
substᴿ = subst₂ {handᴿ}

substitutiveᴿ-from-substitutiveᴸ :
  ∀ {β} {A : Set} {B : Set β} {_⊙_ : A → A → B} {_~_ : B → B → Set}
    {{_ : Eq A}} {{_ : Eq.Transitive _~_}} {{_ : Swappable _⊙_ _~_}}
      {{_ : Substitutive₂ handᴸ _⊙_ _≃_ _~_}} → Substitutive₂ handᴿ _⊙_ _≃_ _~_
substitutiveᴿ-from-substitutiveᴸ = substitutive₂ (with-swap ∘ subst₂)

record Substitutive₂²
    {β} {A : Set} {B : Set β}
      (_⊙_ : A → A → B) (_~_ : A → A → Set) (_≈_ : B → B → Set) : Set where
  constructor substitutive₂²
  field
    {{substitutiveᴸ}} : Substitutive₂ handᴸ _⊙_ _~_ _≈_
    {{substitutiveᴿ}} : Substitutive₂ handᴿ _⊙_ _~_ _≈_

[a≃b][c≃d] :
  {A B : Set} {_⊙_ : A → A → B}
    {{_ : Eq A}} {{_ : Eq B}} {{_ : Substitutive₂² _⊙_ _≃_ _≃_}} →
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

    ≄-substitutive₂² : Substitutive₂² _≄_ _≃_ _⟨→⟩_
    ≄-substitutive₂² = substitutive₂²
