open import Level using (_⊔_; Level; Setω)
open import net.cruhland.axioms.DecEq using (_≃?_)
open import net.cruhland.axioms.Eq using (_≃_)
open import net.cruhland.axioms.Sets.Base using (SetAxioms)
import net.cruhland.axioms.Sets.Decidable as Decidable
import net.cruhland.axioms.Sets.Equality as Equality
open import net.cruhland.models.Logic
  using (_↔_; ↔-elimᴸ; ↔-elimᴿ; ↔-sym; ↔-trans; dec-map)
open import net.cruhland.models.Setoid using (DecSetoid; DecSetoid₀; El; Setoid)

module net.cruhland.axioms.Sets.Singleton where

-- If we want to have a singleton of another PSet, the first level
-- parameter must vary. And if it is a doubly nested PSet, the second
-- level parameter must also vary.
private
  variable
    σ₁ σ₂ : Level
    S : Setoid σ₁ σ₂

module SingletonDef (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; PSet)

  is-singleton : {S : Setoid σ₁ σ₂} → El S → PSet S → Set (σ₁ ⊔ σ₂)
  is-singleton {S = S} a A = ∀ {x} → x ∈ A ↔ a ≈ x
    where open Setoid S using (_≈_)

record SingletonSet (SA : SetAxioms) : Setω where
  open Decidable SA using (DecMembership; ∈?-intro)
  private
    open module SE = Equality SA using (≃-intro)
  open SetAxioms SA using (_∈_; PSet)
  open SingletonDef SA using (is-singleton)

  field
    singleton : El S → PSet S
    x∈sa↔a≈x :
      {S : Setoid σ₁ σ₂} {a : El S} → is-singleton {S = S} a (singleton a)

  module _ {S : Setoid σ₁ σ₂} where
    open Setoid S using (_≈_) renaming (refl to ≈-refl)

    private
      variable
        a x : El S

    x∈sa-elim : x ∈ singleton {S = S} a → a ≈ x
    x∈sa-elim = ↔-elimᴸ x∈sa↔a≈x

    x∈sa-intro : a ≈ x → x ∈ singleton a
    x∈sa-intro = ↔-elimᴿ x∈sa↔a≈x

    a∈sa : a ∈ singleton {S = S} a
    a∈sa = x∈sa-intro ≈-refl

    singleton-unique : {A : PSet S} → is-singleton a A → singleton a ≃ A
    singleton-unique x∈A↔a≈x = ≃-intro (↔-trans x∈sa↔a≈x (↔-sym x∈A↔a≈x))

  instance
    singleton-∈? :
      {{DS : DecSetoid₀}} →
        ∀ {a} → DecMembership (singleton {S = DecSetoid.setoid DS} a)
    singleton-∈? {{DS}} {a} =
      ∈?-intro (λ {x} → dec-map x∈sa-intro x∈sa-elim (a ≃? x))
