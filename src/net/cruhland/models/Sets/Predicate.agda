module net.cruhland.models.Sets.Predicate where

open import Function using (const; flip; id)
open import Level using (_⊔_; Level; Setω) renaming (suc to lsuc)
open import net.cruhland.axioms.Sets using
  ( Comprehension; EmptySet; PairSet; PairwiseUnion
  ; SetAxioms; SetTheory; SingletonSet
  )
open import net.cruhland.axioms.Sets.Base using (α; β; σ₁; σ₂; El; S; Setoid)
open import net.cruhland.models.Logic using
  (_∨_; ∨-map; _↔_; ↔-intro; ↔-refl; ⊥ᴸᴾ; ⊥ᴸᴾ-elim)

record PSet {σ₁ σ₂} (S : Setoid σ₁ σ₂) (α : Level)
    : Set (σ₁ ⊔ σ₂ ⊔ lsuc α) where
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

open SetAxioms setAxioms using (_∈_)

comprehension : Comprehension setAxioms
comprehension = record { ⟨_~_⟩ = λ ap cong → record { ap = ap ; cong = cong } }

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

setTheory : SetTheory
setTheory = record
  { SA = setAxioms
  ; SC = comprehension
  ; ES = emptySet
  ; PS = pairSet
  ; PU = pairwiseUnion
  ; SS = singletonSet
  }