import net.cruhland.axioms.AbstractAlgebra as AA
open import net.cruhland.axioms.Eq as Eq using (_≃_; _≄_; Eq)
import net.cruhland.axioms.Operators as Op
open import net.cruhland.models.Function using (_⟨→⟩_; _∘_; flip; id)
open import net.cruhland.models.Logic
  using (_∨_; ∨-introᴸ; ∨-introᴿ; _↯_; ¬_; ¬-intro)

module net.cruhland.axioms.Ordering where

record NonStrict {A : Set} {{_ : Eq A}} (_≼_ : A → A → Set) : Set₁ where
  constructor nonstrict-intro
  field
    ns-from-≃ : {x y : A} → x ≃ y → x ≼ y
    {{substitutive}} : AA.Substitutive² _≼_ _≃_ _⟨→⟩_
    {{reflexive}} : Eq.Reflexive _≼_
    {{transitive}} : Eq.Transitive _≼_
    {{antisymmetric}} : AA.Antisymmetric _≼_

open NonStrict {{...}} public using (ns-from-≃)

record NonStrict²
    {A : Set} {{_ : Eq A}} (_≼_ _≽_ : A → A → Set) : Set₁ where
  field
    {{lte}} : NonStrict _≼_
    {{gte}} : NonStrict _≽_

    lte-flip : {x y : A} → x ≼ y → y ≽ x
    gte-flip : {x y : A} → x ≽ y → y ≼ x

open NonStrict² {{...}} public using (lte-flip; gte-flip)

record Strict {A : Set} {{_ : Eq A}} (_≺_ : A → A → Set) : Set₁ where
  constructor strict-intro
  field
    {{substitutive}} : AA.Substitutive² _≺_ _≃_ _⟨→⟩_
    {{irreflexive}} : AA.Irreflexive _≺_
    {{transitive}} : Eq.Transitive _≺_

open Strict {{...}} public using ()

record Strict² {A : Set} {{_ : Eq A}} (_≺_ _≻_ : A → A → Set) : Set₁ where
  field
    {{lt}} : Strict _≺_
    {{gt}} : Strict _≻_

    lt-flip : {x y : A} → x ≺ y → y ≻ x
    gt-flip : {x y : A} → x ≻ y → y ≺ x

open Strict² {{...}} public using (lt-flip; gt-flip)

record Trichotomy
    {A : Set} (_≺_ _≻_ : A → A → Set)
    {{_ : Eq A}} {{_ : Strict² _≺_ _≻_}}
    : Set where
  constructor trichotomy-intro
  field
    trichotomy : (x y : A) → AA.ExactlyOneOfThree (x ≃ y) (x ≺ y) (x ≻ y)

open Trichotomy {{...}} public using (trichotomy)

{-# DISPLAY Trichotomy.trichotomy _ x y = trichotomy x y #-}

record TotalOrder
    {A : Set} {{_ : Eq A}} (_≼_ _≽_ _≺_ _≻_ : A → A → Set) : Set₁ where
  field
    {{nonstrict}} : NonStrict² _≼_ _≽_
    {{strict}} : Strict² _≺_ _≻_
    {{order-trichotomy}} : Trichotomy _≺_ _≻_
    lt-from-lte-≄ : {x y : A} → x ≼ y → x ≄ y → x ≺ y

open TotalOrder {{...}} public using (lt-from-lte-≄)

module ≤-Reasoning
    {A : Set} {_≤_ _≥_ : A → A → Set}
    {{_ : Eq A}} {{_ : NonStrict² _≤_ _≥_}}
    where

  infix 3 _∎
  infixr 2 _≃⟨⟩_ _≃⟨_⟩_ _≃˘⟨_⟩_ _≤⟨_⟩_ _≤˘⟨_⟩_
  infix 1 begin_

  begin_ : {x y : A} → x ≤ y → x ≤ y
  begin x≤y = x≤y

  _≃⟨⟩_ : (x {y} : A) → x ≤ y → x ≤ y
  _ ≃⟨⟩ x≤y = x≤y

  _≃⟨_⟩_ : (x {y z} : A) → x ≃ y → y ≤ z → x ≤ z
  _ ≃⟨ x≃y ⟩ y≤z = Eq.trans (ns-from-≃ x≃y) y≤z

  _≃˘⟨_⟩_ : (x {y z} : A) → y ≃ x → y ≤ z → x ≤ z
  _ ≃˘⟨ y≃x ⟩ y≤z = Eq.trans (ns-from-≃ (Eq.sym y≃x)) y≤z

  _≤⟨_⟩_ : (x {y z} : A) → x ≤ y → y ≤ z → x ≤ z
  _ ≤⟨ x≤y ⟩ y≤z = Eq.trans x≤y y≤z

  _≤˘⟨_⟩_ : (x {y z} : A) → y ≥ x → y ≤ z → x ≤ z
  _ ≤˘⟨ y≥x ⟩ y≤z = Eq.trans (gte-flip y≥x) y≤z

  _∎ : (x : A) → x ≤ x
  _ ∎ = Eq.refl

-- Default implementations
module _ {A : Set} {{_ : Eq A}} where

  nonstrict-flip :
    {_≤_ : A → A → Set} {{_ : NonStrict _≤_}} → NonStrict (flip _≤_)
  nonstrict-flip {_≤_} = nonstrict-intro (ns-from-≃ ∘ Eq.sym)
    where
      instance
        flip-≤-substitutive : AA.Substitutive² (flip _≤_) _≃_ _⟨→⟩_
        flip-≤-substitutive = AA.substitutive²-flipped

        flip-≤-reflexive : Eq.Reflexive (flip _≤_)
        flip-≤-reflexive = Eq.reflexive (Eq.refl {_~_ = _≤_})

        flip-≤-transitive : Eq.Transitive (flip _≤_)
        flip-≤-transitive = Eq.transitive (flip Eq.trans)

        flip-≤-antisymmetric : AA.Antisymmetric (flip _≤_)
        flip-≤-antisymmetric =
          AA.antisymmetric λ b≤a a≤b → Eq.sym (AA.antisym b≤a a≤b)

  strict-flip : {_<_ : A → A → Set} {{_ : Strict _<_}} → Strict (flip _<_)
  strict-flip {_<_} = strict-intro
    where
      instance
        flip-<-substitutive : AA.Substitutive² (flip _<_) _≃_ _⟨→⟩_
        flip-<-substitutive = AA.substitutive²-flipped

        flip-<-irreflexive : AA.Irreflexive (flip _<_)
        flip-<-irreflexive = AA.irreflexive (AA.irrefl {_~_ = _<_})

        flip-<-transitive : Eq.Transitive (flip _<_)
        flip-<-transitive = Eq.transitive (flip Eq.trans)

  _⋚_ : {_≶_ : A → A → Set} {{_ : Strict _≶_}} → A → A → Set
  _⋚_ {_≶_} x y = x ≶ y ∨ x ≃ y

  ltEq-⋚ : (_≶_ : A → A → Set) {{_ : Strict _≶_}} → Op.LtEq A
  ltEq-⋚ _ = Op.ltEq _⋚_

  gtEq-⋚ : (_≶_ : A → A → Set) {{_ : Strict _≶_}} → Op.GtEq A
  gtEq-⋚ _ = Op.gtEq _⋚_

  nonstrict-from-strict :
    {_≶_ : A → A → Set} {{_ : Strict _≶_}} → NonStrict _⋚_
  nonstrict-from-strict = nonstrict-intro ∨-introᴿ
    where
      instance
        ⋚-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _⋚_ _≃_ _⟨→⟩_
        ⋚-substitutiveᴸ = AA.substitutive₂ ⋚-substᴸ
          where
            ⋚-substᴸ : {x₁ x₂ y : A} → x₁ ≃ x₂ → x₁ ⋚ y → x₂ ⋚ y
            ⋚-substᴸ x₁≃x₂ (∨-introᴸ x₁≶y) =
              ∨-introᴸ (AA.subst₂ x₁≃x₂ x₁≶y)
            ⋚-substᴸ x₁≃x₂ (∨-introᴿ x₁≃y) =
              ∨-introᴿ (Eq.trans (Eq.sym x₁≃x₂) x₁≃y)

        ⋚-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _⋚_ _≃_ _⟨→⟩_
        ⋚-substitutiveᴿ = AA.substitutive₂ ⋚-substᴿ
          where
            ⋚-substᴿ : {x₁ x₂ y : A} → x₁ ≃ x₂ → y ⋚ x₁ → y ⋚ x₂
            ⋚-substᴿ x₁≃x₂ (∨-introᴸ y≶x₁) = ∨-introᴸ (AA.subst₂ x₁≃x₂ y≶x₁)
            ⋚-substᴿ x₁≃x₂ (∨-introᴿ y≃x₁) = ∨-introᴿ (Eq.trans y≃x₁ x₁≃x₂)

        ⋚-substitutive : AA.Substitutive² _⋚_ _≃_ _⟨→⟩_
        ⋚-substitutive = AA.substitutive²

        ⋚-reflexive : Eq.Reflexive _⋚_
        ⋚-reflexive = Eq.reflexive (∨-introᴿ Eq.refl)

        ⋚-transitive : Eq.Transitive _⋚_
        ⋚-transitive = Eq.transitive ⋚-trans
          where
            ⋚-trans : {x y z : A} → x ⋚ y → y ⋚ z → x ⋚ z
            ⋚-trans (∨-introᴸ x≶y) (∨-introᴸ y≶z) =
              ∨-introᴸ (Eq.trans x≶y y≶z)
            ⋚-trans (∨-introᴸ x≶y) (∨-introᴿ y≃z) =
              ∨-introᴸ (AA.subst₂ y≃z x≶y)
            ⋚-trans (∨-introᴿ x≃y) y⋚z =
              AA.subst₂ (Eq.sym x≃y) y⋚z

        ⋚-antisymmetric : AA.Antisymmetric _⋚_
        ⋚-antisymmetric = AA.antisymmetric ⋚-antisym
          where
            ⋚-antisym : {x y : A} → x ⋚ y → y ⋚ x → x ≃ y
            ⋚-antisym (∨-introᴸ x≶y) (∨-introᴸ y≶x) =
              let x≶x = Eq.trans x≶y y≶x
                  x≮x = AA.irrefl
               in x≶x ↯ x≮x
            ⋚-antisym (∨-introᴸ x≶y) (∨-introᴿ y≃x) =
              Eq.sym y≃x
            ⋚-antisym (∨-introᴿ x≃y) y⋚x =
              x≃y

  module _ {_≤_ : A → A → Set} {{lte : NonStrict _≤_}} where
    record _≤≄_ (x y : A) : Set where
      constructor ≤≄-intro
      field
        ≤-from-≤≄ : x ≤ y
        ≄-from-≤≄ : x ≄ y

    open _≤≄_ public using (≤-from-≤≄; ≄-from-≤≄)

    lt-≤≄ : Op.Lt A
    lt-≤≄ = Op.lt _≤≄_

    gt-flip-≤≄ : Op.Gt A
    gt-flip-≤≄ = Op.gt (flip _≤≄_)

    strict-from-nonstrict : Strict _≤≄_
    strict-from-nonstrict = strict-intro
      where
        instance
          ≤≄-substitutiveᴸ : AA.Substitutive₂ AA.handᴸ _≤≄_ _≃_ _⟨→⟩_
          ≤≄-substitutiveᴸ = AA.substitutive₂ ≤≄-substᴸ
            where
              ≤≄-substᴸ : {x₁ x₂ y : A} → x₁ ≃ x₂ → x₁ ≤≄ y → x₂ ≤≄ y
              ≤≄-substᴸ x₁≃x₂ (≤≄-intro x₁≤y x₁≄y) =
                ≤≄-intro (AA.subst₂ x₁≃x₂ x₁≤y) (AA.substᴸ x₁≃x₂ x₁≄y)

          ≤≄-substitutiveᴿ : AA.Substitutive₂ AA.handᴿ _≤≄_ _≃_ _⟨→⟩_
          ≤≄-substitutiveᴿ = AA.substitutive₂ ≤≄-substᴿ
            where
              ≤≄-substᴿ : {x₁ x₂ y : A} → x₁ ≃ x₂ → y ≤≄ x₁ → y ≤≄ x₂
              ≤≄-substᴿ x₁≃x₂ (≤≄-intro y≤x₁ y≄x₁) =
                ≤≄-intro (AA.subst₂ x₁≃x₂ y≤x₁) (AA.substᴿ x₁≃x₂ y≄x₁)

          ≤≄-substitutive : AA.Substitutive² _≤≄_ _≃_ _⟨→⟩_
          ≤≄-substitutive = AA.substitutive²

          ≤≄-irreflexive : AA.Irreflexive _≤≄_
          ≤≄-irreflexive = AA.irreflexive ≤≄-irrefl
            where
              ≤≄-irrefl : {x : A} → ¬ (x ≤≄ x)
              ≤≄-irrefl = ¬-intro λ { (≤≄-intro x≤x x≄x) → Eq.refl ↯ x≄x }

          ≤≄-transitive : Eq.Transitive _≤≄_
          ≤≄-transitive = Eq.transitive ≤≄-trans
            where
              ≤≄-trans : {x y z : A} → x ≤≄ y → y ≤≄ z → x ≤≄ z
              ≤≄-trans (≤≄-intro x≤y x≄y) (≤≄-intro y≤z y≄z) =
                let x≄z = Eq.≄-intro λ x≃z →
                      let y≤x = AA.subst₂ (Eq.sym x≃z) y≤z
                          x≃y = AA.antisym x≤y y≤x
                       in x≃y ↯ x≄y
                 in ≤≄-intro (Eq.trans x≤y y≤z) x≄z

    nonstrict²-from-nonstrict : NonStrict² _≤_ (flip _≤_)
    nonstrict²-from-nonstrict =
      let gte = nonstrict-flip
       in record { lte = lte ; gte = gte ; lte-flip = id ; gte-flip = id }

  strict²-from-strict :
    {_<_ : A → A → Set} {{lt : Strict _<_}} → Strict² _<_ (flip _<_)
  strict²-from-strict {{lt}} =
    let gt = strict-flip
     in record { lt = lt ; gt = gt ; lt-flip = id ; gt-flip = id }
