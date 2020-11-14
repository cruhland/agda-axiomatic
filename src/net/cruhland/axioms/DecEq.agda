module net.cruhland.axioms.DecEq where

open import Level using () renaming (suc to sℓ)
open import Relation.Nullary.Decidable using
  (False; toWitness; toWitnessFalse; True)
open import net.cruhland.axioms.Eq using (_≃_; _≄_; _≄ⁱ_; ≄ⁱ-intro; Eq)
open import net.cruhland.models.Logic using (Dec)

record DecEq {α} (A : Set α) : Set (sℓ α) where
  infix 4 _≃?_
  field
    {{eq}} : Eq A
    Constraint : A → A → Set α
    _≃?_ : (x y : A) {{_ : Constraint x y}} → Dec (x ≃ y)

open DecEq {{...}} public

≃-derive :
  {A : Set} {x y : A}
    {{deq : DecEq A}} {{c : Constraint x y}} {{eq : True (x ≃? y)}} →
      x ≃ y
≃-derive {{eq = eq}} = toWitness eq

≄-derive :
  {A : Set} {x y : A}
    {{deq : DecEq A}} {{c : Constraint x y}} {{neq : False (x ≃? y)}} →
      x ≄ y
≄-derive {{neq = neq}} = toWitnessFalse neq

≄ⁱ-derive :
  {A : Set} {x y : A}
    {{deq : DecEq A}} {{c : Constraint x y}} {{neq : False (x ≃? y)}} →
      x ≄ⁱ y
≄ⁱ-derive = ≄ⁱ-intro ≄-derive
