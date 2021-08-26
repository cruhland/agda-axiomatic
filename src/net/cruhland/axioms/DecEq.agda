open import Level using (_⊔_) renaming (suc to sℓ)
open import net.cruhland.axioms.Eq using (_≃_; _≄_; Eq)
open import net.cruhland.models.Logic
  using (⊤; Dec; False; True; toWitness; toWitnessFalse)

module net.cruhland.axioms.DecEq where

record DecEq_~_ {α} {β} (A : Set α) (C : A → A → Set β) : Set (sℓ α ⊔ β) where
  constructor DecEq-intro
  infix 4 _≃?_
  field
    {{eq}} : Eq A
    _≃?_ : (x y : A) {{_ : C x y}} → Dec (x ≃ y)

open DecEq_~_ {{...}} public

DecEq : ∀ {α} → Set α → Set (sℓ α)
DecEq A = DecEq A ~ λ _ _ → ⊤

≃-derive :
  {A : Set} {C : A → A → Set} {x y : A} {{deq : DecEq A ~ C}} {{c : C x y}}
  {{eq : True (x ≃? y)}} → x ≃ y
≃-derive {{eq = eq}} = toWitness eq

≄-derive :
  {A : Set} {C : A → A → Set} {x y : A} {{deq : DecEq A ~ C}} {{c : C x y}}
  {{neq : False (x ≃? y)}} → x ≄ y
≄-derive {{neq = neq}} = toWitnessFalse neq
