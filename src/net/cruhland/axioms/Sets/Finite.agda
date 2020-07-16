open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.axioms.Sets.Empty using (EmptySet)
open import net.cruhland.axioms.Sets.Union using (PairwiseUnion)
open import net.cruhland.axioms.Sets.Singleton using (SingletonSet)

module net.cruhland.axioms.Sets.Finite
    (SA : SetAxioms)
    (ES : EmptySet SA)
    (PU : PairwiseUnion SA)
    (SS : SingletonSet SA) where
  open SetAxioms SA using (_∈_; _∉_; PSet)
  open EmptySet ES using (∅; x∉∅)
  open PairwiseUnion PU using (_∪_; x∈A∪B↔x∈A∨x∈B)
  open SingletonSet SS using (singleton; x∈sa↔x≈a)

  open import Data.List using ([]; _∷_; foldr; List)
  open import Data.List.Relation.Unary.Any using (here; there)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Level using () renaming (zero to lzero)
  open import net.cruhland.axioms.Sets.Base using (α; El; S; Setoid; σ₁; σ₂)
  open import net.cruhland.models.Logic using
    (_∨_; ∨-introᴸ; ∨-introᴿ; _↔_; ↔-elimᴸ; ↔-elimᴿ; ⊥-elim)

  import Data.List.Membership.Setoid as Membership

  finite : List (El S) → PSet S lzero
  finite = foldr (λ x acc → singleton x ∪ acc) ∅

  a∈finite :
    {S : Setoid σ₁ σ₂} {a : El S} {xs : List (El S)} →
      let open Membership S using () renaming (_∈_ to _∈ᴸ_)
       in a ∈ᴸ xs → a ∈ finite {S = S} xs
  a∈finite {S = S} (here a≈x) =
    ↔-elimᴿ x∈A∪B↔x∈A∨x∈B (∨-introᴸ (↔-elimᴿ x∈sa↔x≈a a≈x))
      where open Setoid S using (_≈_)
  a∈finite {S = S} (there a∈ᴸxs) =
    ↔-elimᴿ x∈A∪B↔x∈A∨x∈B (∨-introᴿ (a∈finite a∈ᴸxs))
      where open Setoid S using (_≈_)

  a∈fxs→a∈ᴸxs :
    {S : Setoid σ₁ σ₂} {a : El S} {xs : List (El S)} →
      let open Membership S using () renaming (_∈_ to _∈ᴸ_)
       in a ∈ finite {S = S} xs → a ∈ᴸ xs
  a∈fxs→a∈ᴸxs {xs = []} a∈fxs = ⊥-elim (x∉∅ a∈fxs)
  a∈fxs→a∈ᴸxs {S = S} {xs = x ∷ xs} a∈fxs with ↔-elimᴸ x∈A∪B↔x∈A∨x∈B a∈fxs
  ... | ∨-introᴸ a∈sx = here (↔-elimᴸ x∈sa↔x≈a a∈sx)
    where open Setoid S using (_≈_)
  ... | ∨-introᴿ a∈fxs′ = there (a∈fxs→a∈ᴸxs a∈fxs′)
    where open Setoid S using (_≈_)

  a∉finite :
    {S : Setoid σ₁ σ₂} {a : El S} {xs : List (El S)} →
      let open Membership S using () renaming (_∉_ to _∉ᴸ_)
       in a ∉ᴸ xs → a ∉ finite {S = S} xs
  a∉finite a∉ᴸxs a∈xs = a∉ᴸxs (a∈fxs→a∈ᴸxs a∈xs)
