module net.cruhland.models.Sets.Predicate where

open import Function using (_∘_; const; flip; id)
open import Level using (_⊔_; Level; Setω) renaming (suc to sℓ)
open import net.cruhland.axioms.Sets using
  ( Complement; Comprehension; Difference; EmptySet; PairSet
  ; PairwiseIntersection; PairwiseUnion; Replacement; module ReplacementDefs
  ; SetAxioms; SetTheory; SingletonSet
  )
open import net.cruhland.axioms.Sets.Base using
  (α; β; σ₁; σ₂; El; S; Setoid; Setoid₀)
open import net.cruhland.models.Logic using
  (_∧_; ∧-map; _∨_; ∨-map; _↔_; ↔-elimᴿ; ↔-intro; ↔-refl; ⊥ᴸᴾ; ⊥ᴸᴾ-elim)

record PSet {σ₁ σ₂} (S : Setoid σ₁ σ₂) (α : Level) : Set (σ₁ ⊔ σ₂ ⊔ sℓ α) where
  open Setoid S using (_≈_)

  field
    ap : El S → Set α
    cong : ∀ {x y} → x ≈ y → ap x → ap y

open PSet using (cong)

setAxioms : SetAxioms
setAxioms = record
  { PSet = PSet
  ; _∈_ = flip PSet.ap
  ; PSet-cong = λ {_ _ _ _ _ _ A} → PSet.cong A
  }

open SetAxioms setAxioms using (_∈_; _∉_; PSet₀)
open ReplacementDefs setAxioms using (ReplMembership; ReplProp)

comprehension : Comprehension setAxioms
comprehension = record
  { ⟨_~_⟩ = λ ap cong → record { ap = ap ; cong = cong }
  ; x∈⟨P⟩↔Px = ↔-refl
  }

open Comprehension comprehension using (congProp)

∅ : PSet S α
∅ = record { ap = const ⊥ᴸᴾ ; cong = const id }

emptySet : EmptySet setAxioms
emptySet = record { ∅ = ∅ ; x∉∅ = ⊥ᴸᴾ-elim }

singleton : {S : Setoid σ₁ σ₂} → El S → PSet S σ₂
singleton {σ₂ = σ₂} {S} a = record { ap = in-singleton ; cong = singleton-cong }
  where
    open Setoid S using (_≈_) renaming (trans to ≈-trans)

    in-singleton : El S → Set σ₂
    in-singleton x = a ≈ x

    singleton-cong : {x y : El S} → x ≈ y → in-singleton x → in-singleton y
    singleton-cong = flip ≈-trans

singletonSet : SingletonSet setAxioms
singletonSet = record { singleton = singleton ; x∈sa↔a≈x = ↔-refl }

pair : {S : Setoid σ₁ σ₂} → El S → El S → PSet S σ₂
pair {σ₂ = σ₂} {S} a b = record { ap = in-pair ; cong = pair-cong }
  where
    open Setoid S using (_≈_) renaming (trans to ≈-trans)

    in-pair : El S → Set σ₂
    in-pair x = a ≈ x ∨ b ≈ x

    pair-cong : {x y : El S} → x ≈ y → in-pair x → in-pair y
    pair-cong x≈y = ∨-map (flip ≈-trans x≈y) (flip ≈-trans x≈y)

pairSet : PairSet setAxioms
pairSet = record { pair = pair ; x∈pab↔a≈x∨b≈x = ↔-refl }

_∪_ : PSet S α → PSet S β → PSet S (α ⊔ β)
_∪_ {S = S} {α} {β} A B = record { ap = in-union ; cong = union-cong }
  where
    open Setoid S using (_≈_)

    in-union : El S → Set (α ⊔ β)
    in-union x = x ∈ A ∨ x ∈ B

    union-cong : {x y : El S} → x ≈ y → in-union x → in-union y
    union-cong x≈y = ∨-map (cong A x≈y) (cong B x≈y)

pairwiseUnion : PairwiseUnion setAxioms emptySet
pairwiseUnion = record { _∪_ = _∪_ ; x∈A∪B↔x∈A∨x∈B = ↔-refl }

_∩_ : PSet S α → PSet S β → PSet S (α ⊔ β)
_∩_ {S = S} {α} {β} A B =
  record { ap = in-intersection ; cong = intersection-cong }
    where
      open Setoid S using (_≈_)

      in-intersection : El S → Set (α ⊔ β)
      in-intersection x = x ∈ A ∧ x ∈ B

      intersection-cong :
        {x y : El S} → x ≈ y → in-intersection x → in-intersection y
      intersection-cong x≈y = ∧-map (cong A x≈y) (cong B x≈y)

pairwiseIntersection : PairwiseIntersection setAxioms
pairwiseIntersection = record { _∩_ = _∩_ ; x∈A∩B↔x∈A∧x∈B = ↔-refl }

∁ : PSet S α → PSet S α
∁ {S = S} A = record
  { ap = λ x → x ∉ A
  ; cong = λ x≈y x∉A y∈A → x∉A (cong A (≈-sym x≈y) y∈A)
  }
  where open Setoid S using (_≈_) renaming (sym to ≈-sym)

complement : Complement setAxioms
complement = record { ∁ = ∁ ; x∈∁A↔x∉A = ↔-refl }

_∖_ : {S : Setoid σ₁ σ₂} → PSet S α → PSet S β → PSet S (α ⊔ β)
_∖_ {α = α} {β = β} {S = S} A B = record { ap = in-diff ; cong = diff-cong }
  where
    open Setoid S using (_≈_) renaming (sym to ≈-sym)

    in-diff : El S → Set (α ⊔ β)
    in-diff x = x ∈ A ∧ x ∉ B

    diff-cong : congProp {S = S} in-diff
    diff-cong x≈y = ∧-map (cong A x≈y) (_∘ cong B (≈-sym x≈y))

difference : Difference setAxioms
difference = record { _∖_ = _∖_ ; x∈A∖B↔x∈A∧x∉B = ↔-refl }

rep :
  {S T : Setoid₀} (P : El S → El T → Set) (A : PSet₀ S) →
    ReplProp {T = T} {A} P → PSet₀ T
rep {S = S} {T} P A rp =
  record { ap = λ x → ReplMembership x P ; cong = rep-cong }
    where
      open Setoid S using () renaming (refl to ≈ˢ-refl)
      open Setoid T using (_≈_)

      rep-cong :
        ∀ {x y} → x ≈ y → ReplMembership {T = T} {A} x P → ReplMembership y P
      rep-cong x≈y record { a = a ; a∈A = a∈A ; Pax = Pax } =
        record { a = a ; a∈A = a∈A ; Pax = ReplProp.P-cong rp ≈ˢ-refl x≈y Pax }

replacement : Replacement setAxioms emptySet pairwiseUnion singletonSet
replacement = record { replacement = rep ; x∈rep↔Pax = ↔-refl }

setTheory : SetTheory
setTheory = record
  { SA = setAxioms
  ; CM = complement
  ; ES = emptySet
  ; PS = pairSet
  ; PI = pairwiseIntersection
  ; PU = pairwiseUnion
  ; RE = replacement
  ; SC = comprehension
  ; SD = difference
  ; SS = singletonSet
  }
