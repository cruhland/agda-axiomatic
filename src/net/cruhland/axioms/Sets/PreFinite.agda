open import Data.List using ([]; _∷_; foldr; List)
open import Data.List.Relation.Unary.All
  using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Membership.Setoid as Setoidᴸ
open import net.cruhland.axioms.Eq as Eq using (_≃_)
open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.axioms.Sets.Empty using (EmptySet)
open import net.cruhland.axioms.Sets.Singleton using (SingletonSet)
import net.cruhland.axioms.Sets.Subset as Subset
open import net.cruhland.axioms.Sets.Union using (PairwiseUnion)
open import net.cruhland.models.Function using (_∘_)
open import net.cruhland.models.Logic using (∨-introᴸ; ∨-introᴿ; _↯_)
open import net.cruhland.models.Setoid
  using (El; DecSetoid; DecSetoid₀; Setoid₀)

module net.cruhland.axioms.Sets.PreFinite
    (SA : SetAxioms)
    (ES : EmptySet SA)
    (PU : PairwiseUnion SA ES)
    (SS : SingletonSet SA)
    where
  open EmptySet ES using (∅; x∉∅)
  open PairwiseUnion PU using (_∪_; x∈A∪B-elim; x∈A∪B-introᴸ; x∈A∪B-introᴿ)
  open SetAxioms SA using (_∈_; PSet₀)
  open SingletonSet SS using (singleton; x∈sa-elim; x∈sa-intro; a∈sa)
  open Subset SA using (_⊆_; ⊆-intro; ≃→⊆ᴸ)
  import net.cruhland.axioms.Sets.Equality SA as SE

  private
    variable
      S : Setoid₀

  finite : List (El S) → PSet₀ S
  finite = foldr (λ x acc → singleton x ∪ acc) ∅

  record Finite (A : PSet₀ S) : Set₁ where
    field
      elements : List (El S)
      same-set : finite elements ≃ A

  open Finite {{...}} public using (elements; same-set)

  toList : (A : PSet₀ S) {{_ : Finite A}} → List (El S)
  toList A = elements

  toList⊆A : (A : PSet₀ S) {{_ : Finite A}} → All (_∈ A) (toList A)
  toList⊆A {S = S} A = xs⊆A (toList A) (≃→⊆ᴸ same-set)
    where
      xs⊆A : (xs : List (El S)) → finite xs ⊆ A → All (_∈ A) xs
      xs⊆A [] fxs⊆A = []ᴬ
      xs⊆A (x ∷ xs) (⊆-intro ⊆-elim) =
        ⊆-elim (x∈A∪B-introᴸ a∈sa) ∷ᴬ xs⊆A xs (⊆-intro (⊆-elim ∘ x∈A∪B-introᴿ))

  module _ {DS : DecSetoid₀} where
    S′ = DecSetoid.setoid DS
    open Setoidᴸ S′ using () renaming (_∈_ to _∈ᴸ_)

    ∈fin→∈ᴸ : {a : El S′} {xs : List (El S′)} → a ∈ finite {S = S′} xs → a ∈ᴸ xs
    ∈fin→∈ᴸ {xs = []} a∈fxs = a∈fxs ↯ x∉∅
    ∈fin→∈ᴸ {xs = x ∷ xs} a∈fxs with x∈A∪B-elim a∈fxs
    ... | ∨-introᴸ a∈sx = here (Eq.sym (x∈sa-elim a∈sx))
    ... | ∨-introᴿ a∈fxs′ = there (∈fin→∈ᴸ a∈fxs′)

    ∈ᴸ→∈fin : {a : El S′} {xs : List (El S′)} → a ∈ᴸ xs → a ∈ finite {S = S′} xs
    ∈ᴸ→∈fin (here a≈x) = x∈A∪B-introᴸ (x∈sa-intro (Eq.sym a≈x))
    ∈ᴸ→∈fin (there a∈ᴸxs) = x∈A∪B-introᴿ (∈ᴸ→∈fin a∈ᴸxs)
