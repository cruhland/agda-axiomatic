module net.cruhland.models.Sets.Predicate where

open import Function using (_∘_; const; flip; id)
open import Function.Equivalence using (Equivalence)
open import Level using (_⊔_; Level; Setω) renaming (suc to sℓ)
open import net.cruhland.axioms.Sets using
  ( Complement; Comprehension; Difference; EmptySet; PairSet
  ; PairwiseIntersection; PairwiseUnion; Replacement; module ReplacementDefs
  ; SetAxioms; SetTheory; SingletonSet
  )
open import net.cruhland.axioms.Sets.Base using (α; β; σ₁; σ₂; S)
open import net.cruhland.models.Logic using
  (_∧_; ∧-map; _∨_; ∨-map; _↔_; ↔-elimᴿ; ↔-intro; ↔-refl; ⊥ᴸᴾ; ⊥ᴸᴾ-elim)
open import net.cruhland.models.Setoid
  using (_⟨$⟩_; El; Setoid; Setoid₀; SPred₀; SRel₀) renaming (cong to ⟶-cong)

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
open ReplacementDefs setAxioms using (ReplMem; ReplRel)

comprehension : Comprehension setAxioms
comprehension = record { ⟨_⟩ = SPred→PSet ; x∈⟨P⟩↔Px = ↔-refl }
  where
    SPred→PSet : {S : Setoid₀} → SPred₀ S → PSet₀ S
    SPred→PSet P =
      record { ap = _⟨$⟩_ P ; cong = _⟨$⟩_ ∘ Equivalence.to ∘ (⟶-cong P) }

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

_∪_ : PSet₀ S → PSet₀ S → PSet₀ S
_∪_ {S = S} A B = record { ap = in-union ; cong = union-cong }
  where
    open Setoid S using (_≈_)

    in-union : El S → Set
    in-union x = x ∈ A ∨ x ∈ B

    union-cong : {x y : El S} → x ≈ y → in-union x → in-union y
    union-cong x≈y = ∨-map (cong A x≈y) (cong B x≈y)

pairwiseUnion : PairwiseUnion setAxioms emptySet
pairwiseUnion = record { _∪_ = _∪_ ; x∈A∪B↔x∈A∨x∈B = ↔-refl }

_∩_ : PSet₀ S → PSet₀ S → PSet₀ S
_∩_ {S = S} A B =
  record { ap = in-intersection ; cong = intersection-cong }
    where
      open Setoid S using (_≈_)

      in-intersection : El S → Set
      in-intersection x = x ∈ A ∧ x ∈ B

      intersection-cong :
        {x y : El S} → x ≈ y → in-intersection x → in-intersection y
      intersection-cong x≈y = ∧-map (cong A x≈y) (cong B x≈y)

pairwiseIntersection : PairwiseIntersection setAxioms
pairwiseIntersection = record { _∩_ = _∩_ ; x∈A∩B↔x∈A∧x∈B = ↔-refl }

∁ : PSet₀ S → PSet₀ S
∁ {S = S} A = record
  { ap = λ x → x ∉ A
  ; cong = λ x≈y x∉A y∈A → x∉A (cong A (≈-sym x≈y) y∈A)
  }
  where open Setoid S using (_≈_) renaming (sym to ≈-sym)

complement : Complement setAxioms
complement = record { ∁ = ∁ ; x∈∁A↔x∉A = ↔-refl }

_∖_ : {S : Setoid₀} → PSet₀ S → PSet₀ S → PSet₀ S
_∖_ {S = S} A B = record { ap = in-diff ; cong = diff-cong }
  where
    open Setoid S using (_≈_) renaming (sym to ≈-sym)

    in-diff : El S → Set
    in-diff x = x ∈ A ∧ x ∉ B

    diff-cong : ∀ {x y} → x ≈ y → in-diff x → in-diff y
    diff-cong x≈y = ∧-map (cong A x≈y) (_∘ cong B (≈-sym x≈y))

difference : Difference setAxioms
difference = record { _∖_ = _∖_ ; x∈A∖B↔x∈A∧x∉B = ↔-refl }

rep : {S T : Setoid₀} (A : PSet₀ S) → ReplRel A T → PSet₀ T
rep {S = S} {T} A RR =
  record { ap = λ x → ReplMem x RR ; cong = rep-cong }
    where
      open Setoid S using () renaming (refl to ≈ˢ-refl)
      open Setoid T using (_≈_)
      open ReplRel RR using (R)

      rep-cong :
        ∀ {x y} → x ≈ y → ReplMem x RR → ReplMem y RR
      rep-cong x≈y record { a = a ; a∈A = a∈A ; Rax = Rax } = record
        { a = a
        ; a∈A = a∈A
        ; Rax = Equivalence.to (⟶-cong R ≈ˢ-refl x≈y) ⟨$⟩ Rax
        }

replacement : Replacement setAxioms emptySet pairwiseUnion singletonSet
replacement = record { replacement = rep ; x∈rep↔Rax = ↔-refl }

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
