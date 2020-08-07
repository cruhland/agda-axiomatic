open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.axioms.Sets.Empty using (EmptySet)
open import net.cruhland.axioms.Sets.Union using (PairwiseUnion)
open import net.cruhland.axioms.Sets.Singleton using (SingletonSet)

module net.cruhland.axioms.Sets.Finite
    (SA : SetAxioms)
    (ES : EmptySet SA)
    (PU : PairwiseUnion SA ES)
    (SS : SingletonSet SA) where
  open SetAxioms SA using (_∈_; _∉_; PSet)
  open EmptySet ES using (∅; x∉∅)
  open PairwiseUnion PU using
    (_∪_; ∪-∅ᴸ; ∪-assoc; x∈A∪B-elim; x∈A∪B-introᴸ; x∈A∪B-introᴿ; ∪-substᴿ)
  open SingletonSet SS using (singleton; a∈sa; x∈sa-elim; x∈sa-intro)

  open import Data.List using ([]; _∷_; _++_; foldr; List)
  import Data.List.Membership.DecSetoid as DecMembership
  import Data.List.Membership.Setoid as Membership
  open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
  open import Data.List.Relation.Unary.All
    using (All; all; lookupAny) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
  open import Data.List.Relation.Unary.Any using
    (Any; here; index; lookup; map; there)
  open import Function using (_∘_)
  open import Level using (_⊔_)
  open import Relation.Binary using (Decidable; DecSetoid)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Relation.Nullary.Decidable using (map′)
  open import Relation.Nullary.Product using () renaming (_×-dec_ to _∧-dec_)
  open import net.cruhland.axioms.Sets.Base using (α; El; S; Setoid; σ₁; σ₂)
  open import net.cruhland.axioms.Sets.Equality SA using (_≃_; ≃-trans)
  open import net.cruhland.axioms.Sets.Properties SA ES PU using (∪-⊆ᴿ)
  open import net.cruhland.axioms.Sets.Subset SA using
    (_⊆_; ≃→⊆ᴸ; ≃→⊆ᴿ; ⊆-antisym; ⊆-intro)
  open import net.cruhland.models.Logic using
    ( _∧_; ∧-elimᴸ; ∧-elimᴿ; ∧-intro; uncurry
    ; _∨_; ∨-introᴸ; ∨-introᴿ
    ; ⊥-elim; Dec
    )

  finite : {S : Setoid σ₁ σ₂} → List (El S) → PSet S σ₂
  finite = foldr (λ x acc → singleton x ∪ acc) ∅

  module Memberᴸ {DS : DecSetoid σ₁ σ₂} where
    open DecMembership DS using () renaming (_∈_ to _∈ᴸ_; _∈?_ to _∈ᴸ?_)
    S′ = DecSetoid.setoid DS
    open Setoid S′ using (_≈_) renaming (sym to ≈-sym)

    ∈ᴸ→∈fin : {a : El S′} {xs : List (El S′)} → a ∈ᴸ xs → a ∈ finite {S = S′} xs
    ∈ᴸ→∈fin (here a≈x) = x∈A∪B-introᴸ (x∈sa-intro (≈-sym a≈x))
    ∈ᴸ→∈fin (there a∈ᴸxs) = x∈A∪B-introᴿ (∈ᴸ→∈fin a∈ᴸxs)

    ∈fin→∈ᴸ : {a : El S′} {xs : List (El S′)} → a ∈ finite {S = S′} xs → a ∈ᴸ xs
    ∈fin→∈ᴸ {xs = []} a∈fxs = ⊥-elim (x∉∅ a∈fxs)
    ∈fin→∈ᴸ {xs = x ∷ xs} a∈fxs with x∈A∪B-elim a∈fxs
    ... | ∨-introᴸ a∈sx = here (≈-sym (x∈sa-elim a∈sx))
    ... | ∨-introᴿ a∈fxs′ = there (∈fin→∈ᴸ a∈fxs′)

    _∈?_ : (a : El S′) (xs : List (El S′)) → Dec (a ∈ finite {S = S′} xs)
    a ∈? xs = map′ ∈ᴸ→∈fin ∈fin→∈ᴸ (a ∈ᴸ? xs)

  module Subsetᴸ {DS : DecSetoid σ₁ σ₂} where
    open Memberᴸ {DS = DS} using (∈ᴸ→∈fin; ∈fin→∈ᴸ)
    open DecMembership DS using () renaming (_∈_ to _∈ᴸ_; _∈?_ to _∈ᴸ?_)
    S′ = DecSetoid.setoid DS

    infix 4 _⊆ᴸ_ _⊆ᴸ?_ _⊆?_ _≃?_

    _⊆ᴸ_ : List (El S′) → List (El S′) → Set (σ₁ ⊔ σ₂)
    _⊆ᴸ_ xs ys = All (_∈ᴸ ys) xs

    _⊆ᴸ?_ : Decidable _⊆ᴸ_
    _⊆ᴸ?_ xs ys = all (_∈ᴸ? ys) xs

    ⊆ᴸ→⊆fin : {xs ys : List (El S′)} → xs ⊆ᴸ ys → finite {S = S′} xs ⊆ finite ys
    ⊆ᴸ→⊆fin {xs} {ys} xs⊆ᴸys = ⊆-intro (∈ᴸ→∈fin ∘ x∈ᴸxs→x∈ᴸys ∘ ∈fin→∈ᴸ)
      where
        open Setoid S′ using (_≈_; trans)

        x∈ᴸxs→x∈ᴸys : ∀ {x} → x ∈ᴸ xs → x ∈ᴸ ys
        x∈ᴸxs→x∈ᴸys x∈ᴸxs with lookupAny xs⊆ᴸys x∈ᴸxs
        ... | ∧-intro any[lookup≈]ys x≈lookup =
          map (trans x≈lookup) any[lookup≈]ys

    ⊆fin→⊆ᴸ : {xs ys : List (El S′)} → finite {S = S′} xs ⊆ finite ys → xs ⊆ᴸ ys
    ⊆fin→⊆ᴸ {xs = []} fxs⊆fys = []ᴬ
    ⊆fin→⊆ᴸ {xs = x ∷ xs} sx∪fxs⊆fys@(⊆-intro x∈fxs→x∈fys) = x∈ᴸys ∷ᴬ xs⊆ᴸys
      where
        x∈ᴸys = ∈fin→∈ᴸ (x∈fxs→x∈fys (x∈A∪B-introᴸ a∈sa))
        xs⊆ᴸys = ⊆fin→⊆ᴸ (∪-⊆ᴿ sx∪fxs⊆fys)

    _⊆?_ : (xs ys : List (El S′)) → Dec (finite {S = S′} xs ⊆ finite ys)
    xs ⊆? ys = map′ ⊆ᴸ→⊆fin ⊆fin→⊆ᴸ (xs ⊆ᴸ? ys)

    _≃?_ : (xs ys : List (El S′)) → Dec (finite {S = S′} xs ≃ finite ys)
    xs ≃? ys = map′ (uncurry ⊆-antisym) ≃→⊆⊇ ((xs ⊆? ys) ∧-dec (ys ⊆? xs))
      where
        ≃→⊆⊇ = λ A≃B → ∧-intro (≃→⊆ᴸ A≃B) (≃→⊆ᴿ A≃B)

  ∪-finite :
    {S : Setoid σ₁ σ₂} →
      (xs ys : List (El S)) → finite {S = S} xs ∪ finite ys ≃ finite (xs ++ ys)
  ∪-finite [] ys = ∪-∅ᴸ
  ∪-finite (x ∷ xs) ys = ≃-trans ∪-assoc (∪-substᴿ (∪-finite xs ys))