open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
open Eq.≃-Reasoning
open import net.cruhland.models.Function using (_∘_; _⟨→⟩_; const; flip)
open import net.cruhland.models.Logic using (⊤; contrapositive)

module net.cruhland.axioms.AbstractAlgebra.Injective where

private
  module AA where
    open import net.cruhland.axioms.AbstractAlgebra.Base public
    open import net.cruhland.axioms.AbstractAlgebra.Substitutive public
    open import net.cruhland.axioms.AbstractAlgebra.Swappable public

record Injective
    {A B : Set} (f : A → B) (_~_ : A → A → Set) (_≈_ : B → B → Set) : Set where
  constructor injective
  field
    inject : ∀ {a₁ a₂} → f a₁ ≈ f a₂ → a₁ ~ a₂

open Injective {{...}} public using (inject)

instance
  ≄-substitutive :
    {A B : Set} {f : A → B} {{_ : Eq A}} {{_ : Eq B}}
    {{r : Injective f _≃_ _≃_}} → AA.Substitutive₁ f _≄_ _≄_
  ≄-substitutive = AA.substitutive₁ (contrapositive inject)

CancellativePropertyᶜ :
  AA.Hand →
  ∀ {ρ} {A B : Set} {R : Set ρ}
  {C : A → Set} {C★ : A → A → Set} {C⊙ : A → A → Set} {C⊡ : B → B → Set} →
  ((x y : A) {{_ : C★ x y}} → B) →
  ((x y : A) {{_ : C⊙ x y}} → R) →
  ((x y : B) {{_ : C⊡ x y}} → R) →
  (R → R → Set) → Set
CancellativePropertyᶜ hand {C = C} {C★} {C⊙} {C⊡} _★_ _⊙_ _⊡_ _⇉_ =
  let C★˘ = AA.forHand hand C★
      _★˘_ = AA.forHandᶜ hand _★_
   in ∀ {x y₁ y₂} {{cx : C x}} {{c★₁ : C★˘ x y₁}} {{c★₂ : C★˘ x y₂}}
      {{c⊙ : C⊙ y₁ y₂}} {{c⊡ : C⊡ (x ★˘ y₁) (x ★˘ y₂)}} →
      ((x ★˘ y₁) ⊡ (x ★˘ y₂)) ⇉ (y₁ ⊙ y₂)

CancellativeProperty :
  AA.Hand → {A B : Set} {C : A → Set} →
  (A → A → B) → (A → A → Set) → (B → B → Set) → Set
CancellativeProperty hand {C = C} _★_ _⊙_ _⊡_ =
  CancellativePropertyᶜ
    hand {C = C} (AA.tc₂ _★_) (AA.tc₂ _⊙_) (AA.tc₂ _⊡_) _⟨→⟩_

record Cancellativeᶜ
    (hand : AA.Hand) {ρ} {A B : Set} {R : Set ρ}
    {C★ : A → A → Set} {C⊙ : A → A → Set} {C⊡ : B → B → Set}
    (_★_ : (x y : A) {{_ : C★ x y}} → B)
    (_⊙_ : (x y : A) {{_ : C⊙ x y}} → R)
    (_⊡_ : (x y : B) {{_ : C⊡ x y}} → R)
    (_⇉_ : R → R → Set) (C : A → Set)
    : Set where
  constructor cancellative
  field
    cancel : CancellativePropertyᶜ hand {C = C} _★_ _⊙_ _⊡_ _⇉_

open Cancellativeᶜ {{...}} public using (cancel)

cancelᴸ = cancel {AA.handᴸ}
cancelᴿ = cancel {AA.handᴿ}

Cancellative :
  AA.Hand → {A B : Set} → (A → A → B) → (A → A → Set) → (B → B → Set) →
  (C : A → Set) → Set
Cancellative hand _★_ _⊙_ _⊡_ =
  Cancellativeᶜ hand (AA.tc₂ _★_) (AA.tc₂ _⊙_) (AA.tc₂ _⊡_) _⟨→⟩_

cancellativeᴿ-from-cancellativeᴸ :
  {A B : Set} {_★_ : A → A → B} {_⊙_ : A → A → Set} {_⊡_ : B → B → Set}
  {C : A → Set} {{_ : Eq.Transitive _⊡_}} {{_ : AA.Swappable _★_ _⊡_}}
  {{_ : Cancellative AA.handᴸ _★_ _⊙_ _⊡_ C}} →
  Cancellative AA.handᴿ _★_ _⊙_ _⊡_ C
cancellativeᴿ-from-cancellativeᴸ = cancellative (cancel ∘ AA.with-swap)

cancelᴿ-from-cancelᴸ-comm :
  {A : Set} {_★_ : A → A → A} {C : A → Set} {{_ : Eq A}}
  {{_ : AA.Commutative _★_}} {{c : Cancellative AA.handᴸ _★_ _≃_ _≃_ C}} →
  Cancellative AA.handᴿ _★_ _≃_ _≃_ C
cancelᴿ-from-cancelᴸ-comm = cancellativeᴿ-from-cancellativeᴸ
  where
    instance ★-swap = AA.swappable-from-commutative
    instance ≃-substᴿ = AA.EqProperties.≃-substitutiveᴿ

cancelᴿ-from-cancelᴸ-comm₂ :
  {A B : Set} {R : Set} {{_ : Eq B}} {{_ : Eq R}}
  {C : A → Set} {C⊙ : A → A → Set} {C⊡₁ : B → Set} →
  let C⊡ = const C⊡₁ in
    {_★_ : A → A → B} {{_ : AA.Commutative _★_}}
    {_⊙_ : (x y : A) {{_ : C⊙ x y}} → R}
    {_⊡_ : (x y : B) {{_ : C⊡ x y}} → R}
    {{_ : AA.Substitutive²ᶜ _⊡_ _≃_ _≃_ (const ⊤)}}
    {{_ : AA.Substitutive₁ C⊡₁ _≃_ _⟨→⟩_}}
    {{r : Cancellativeᶜ AA.handᴸ (AA.tc₂ _★_) _⊙_ _⊡_ _≃_ C}} →
    Cancellativeᶜ AA.handᴿ (AA.tc₂ _★_) _⊙_ _⊡_ _≃_ C
cancelᴿ-from-cancelᴸ-comm₂ {C = C} {_★_ = _★_} {_⊙_} {_⊡_} = cancellative proof
  where
    proof : CancellativePropertyᶜ AA.handᴿ {C = C} (AA.tc₂ _★_) _⊙_ _⊡_ _≃_
    proof {x} {y₁} {y₂} {{c⊡ = c⊡}} =
      let instance
            C⊡-comm = AA.subst₁ AA.comm c⊡
       in begin
            (y₁ ★ x) ⊡ (y₂ ★ x)
          ≃⟨ AA.subst₂ AA.comm ⟩
            (x ★ y₁) ⊡ (y₂ ★ x)
          ≃⟨ AA.subst₂ AA.comm ⟩
            (x ★ y₁) ⊡ (x ★ y₂)
          ≃⟨ cancel ⟩
            y₁ ⊙ y₂
          ∎

record Cancellative²ᶜ
    {ρ} {A B : Set} {R : Set ρ}
    {C★ : A → A → Set} {C⊙ : A → A → Set} {C⊡ : B → B → Set}
    (_★_ : (x y : A) {{_ : C★ x y}} → B)
    (_⊙_ : (x y : A) {{_ : C⊙ x y}} → R)
    (_⊡_ : (x y : B) {{_ : C⊡ x y}} → R)
    (_⇉_ : R → R → Set) (Cᴸ : A → Set) (Cᴿ : A → Set)
    : Set where
  constructor cancellative²
  field
    {{cancellativeᴸ}} : Cancellativeᶜ AA.handᴸ _★_ _⊙_ _⊡_ _⇉_ Cᴸ
    {{cancellativeᴿ}} : Cancellativeᶜ AA.handᴿ _★_ _⊙_ _⊡_ _⇉_ Cᴿ

Cancellative² :
  {A B : Set} (_★_ : A → A → B) (_⊙_ : A → A → Set) (_⊡_ : B → B → Set)
  (C : A → Set) → Set
Cancellative² _★_ _⊙_ _⊡_ C =
  Cancellative²ᶜ (AA.tc₂ _★_) (AA.tc₂ _⊙_) (AA.tc₂ _⊡_) _⟨→⟩_ C C

{--- Equivalences ---}

module _
    {A B : Set} {C : A → Set}
    {_★_ : A → A → B} {_⊙_ : A → A → Set} {_⊡_ : B → B → Set}
    where

  injective-from-cancellativeᴸ :
    ∀ {a} {{_ : Cancellative AA.handᴸ _★_ _⊙_ _⊡_ C}} {{_ : C a}} →
    Injective (a ★_) _⊙_ _⊡_
  injective-from-cancellativeᴸ = injective cancel

  cancellativeᴸ-from-injective :
    (∀ a → Injective (a ★_) _⊙_ _⊡_) → Cancellative AA.handᴸ _★_ _⊙_ _⊡_ C
  cancellativeᴸ-from-injective mkInjective =
    cancellative λ {a b₁ b₂} → inject {{r = mkInjective a}}

  cancellativeᴸ-flip :
    {{c : Cancellative AA.handᴸ _★_ _⊙_ _⊡_ C}} →
    Cancellative AA.handᴿ (flip _★_) _⊙_ _⊡_ C
  cancellativeᴸ-flip {{c}} = cancellative cancel

  cancellativeᴿ-flip :
    {{c : Cancellative AA.handᴿ _★_ _⊙_ _⊡_ C}} →
    Cancellative AA.handᴸ (flip _★_) _⊙_ _⊡_ C
  cancellativeᴿ-flip {{c}} = cancellative cancel
