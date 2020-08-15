open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.axioms.Sets.Empty using (EmptySet)
open import net.cruhland.axioms.Sets.Intersection using (PairwiseIntersection)
open import net.cruhland.axioms.Sets.Union using (PairwiseUnion)
open import net.cruhland.axioms.Sets.Singleton using (SingletonSet)

module net.cruhland.axioms.Sets.Finite
    (SA : SetAxioms)
    (ES : EmptySet SA)
    (PI : PairwiseIntersection SA)
    (PU : PairwiseUnion SA ES)
    (SS : SingletonSet SA) where
  open SetAxioms SA using (_∈_; _∉_; PSet; PSet-cong)
  open EmptySet ES using (∅; x∉∅)
  open PairwiseIntersection PI using
    (_∩_; x∈A∩B-elim; x∈A∩B-elimᴸ; x∈A∩B-intro₂)
  open PairwiseUnion PU using
    ( _∪_; ∪-∅ᴸ; ∪-assoc; x∈A∪B-elim
    ; x∈A∪B-introᴸ; x∈A∪B-introᴿ; ∪-substᴸ; ∪-substᴿ
    )
  open SingletonSet SS using (singleton; a∈sa; x∈sa-elim; x∈sa-intro)

  open import Data.Bool using (false; true)
  open import Data.List using ([]; _∷_; _++_; any; filter; foldr; List)
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
  open import Relation.Nullary.Product using () renaming (_×-dec_ to _∧-dec_)
  open import net.cruhland.axioms.Sets.Base using (α; El; S; Setoid; σ₁; σ₂)
  open import net.cruhland.axioms.Sets.Equality SA using
    (_≃_; ≃-trans; module ≃-Reasoning)
  open ≃-Reasoning
  open import net.cruhland.axioms.Sets.Properties SA ES PI PU using
    (A⊆∅→A≃∅; ∪-⊆ᴿ; ∩-∅ᴸ; ∩-over-∪ᴿ)
  open import net.cruhland.axioms.Sets.Subset SA using
    (_⊆_; ≃→⊆ᴸ; ≃→⊆ᴿ; ⊆-antisym; ⊆-intro)
  open import net.cruhland.models.Logic using
    ( _∧_; ∧-elimᴸ; ∧-elimᴿ; ∧-intro; uncurry
    ; _∨_; ∨-introᴸ; ∨-introᴿ
    ; ⊥-elim; _because_; Dec; dec-map; does; ofⁿ; ofʸ
    )

  finite : {S : Setoid σ₁ σ₂} → List (El S) → PSet S σ₂
  finite = foldr (λ x acc → singleton x ∪ acc) ∅

  module Subsetᴸ {DS : DecSetoid σ₁ σ₂} where
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
    xs ⊆? ys = dec-map ⊆ᴸ→⊆fin ⊆fin→⊆ᴸ (xs ⊆ᴸ? ys)

    _≃?_ : (xs ys : List (El S′)) → Dec (finite {S = S′} xs ≃ finite ys)
    xs ≃? ys = dec-map (uncurry ⊆-antisym) ≃→⊆⊇ ((xs ⊆? ys) ∧-dec (ys ⊆? xs))
      where
        ≃→⊆⊇ = λ A≃B → ∧-intro (≃→⊆ᴸ A≃B) (≃→⊆ᴿ A≃B)

  ∪-finite :
    {S : Setoid σ₁ σ₂} →
      (xs ys : List (El S)) → finite {S = S} xs ∪ finite ys ≃ finite (xs ++ ys)
  ∪-finite [] ys = ∪-∅ᴸ
  ∪-finite (x ∷ xs) ys = ≃-trans ∪-assoc (∪-substᴿ (∪-finite xs ys))

  singleton-∈∩ᴸ :
    {S : Setoid σ₁ σ₂} {A : PSet S σ₂} {a : El S} →
      a ∈ A → singleton a ∩ A ≃ singleton a
  singleton-∈∩ᴸ {S = S} {A} {a} a∈A =
    ⊆-antisym (⊆-intro forward) (⊆-intro backward)
      where
        forward : ∀ {x} → x ∈ singleton a ∩ A → x ∈ singleton a
        forward x∈sa∩A = x∈A∩B-elimᴸ x∈sa∩A

        backward : ∀ {x} → x ∈ singleton a → x ∈ singleton a ∩ A
        backward x∈sa = x∈A∩B-intro₂ x∈sa (PSet-cong (x∈sa-elim x∈sa) a∈A)
          where open Setoid S using (_≈_)

  singleton-∉∩ᴸ :
    {S : Setoid σ₁ σ₂} {A : PSet S σ₂} {a : El S} → a ∉ A → singleton a ∩ A ≃ ∅
  singleton-∉∩ᴸ {S = S} {A} {a} a∉A = A⊆∅→A≃∅ (⊆-intro x∈sa∩A→x∈∅)
    where
      open Setoid S using (_≈_) renaming (sym to ≈-sym)

      x∈sa∩A→x∈∅ : ∀ {x} → x ∈ singleton a ∩ A → x ∈ ∅
      x∈sa∩A→x∈∅ x∈sa∩A =
        let ∧-intro x∈sa x∈A = x∈A∩B-elim x∈sa∩A
         in ⊥-elim (a∉A (PSet-cong (≈-sym (x∈sa-elim x∈sa)) x∈A))

  intersection :
    {DS : DecSetoid σ₁ σ₂} →
      let S′ = DecSetoid.setoid DS
       in List (El S′) → List (El S′) → List (El S′)
  intersection {DS = DS} xs ys = filter (_∈ᴸ? ys) xs
    where open DecMembership DS using () renaming (_∈?_ to _∈ᴸ?_)

  ∩-finite-lemma :
    {DS : DecSetoid σ₁ σ₂} →
      let S′ = DecSetoid.setoid DS
       in {x : El S′} (xs ys : List (El S′)) →
            let left₁ = singleton x ∩ finite ys
                left₂ = finite {S = S′} (intersection {DS = DS} xs ys)
                left = left₁ ∪ left₂
                right = finite (intersection {DS = DS} (x ∷ xs) ys)
             in left ≃ right
  ∩-finite-lemma {DS = DS} {x = x} xs ys with x ∈ᴸ? ys
    where open DecMembership DS using () renaming (_∈?_ to _∈ᴸ?_)
  ... | true because ofʸ x∈ᴸys = ∪-substᴸ (singleton-∈∩ᴸ (∈ᴸ→∈fin x∈ᴸys))
      where open Subsetᴸ {DS = DS} using (∈ᴸ→∈fin)
  ... | false because ofⁿ x∉ᴸys = ≃-trans (∪-substᴸ (singleton-∉∩ᴸ x∉fys)) ∪-∅ᴸ
    where
      open Subsetᴸ {DS = DS} using (∈fin→∈ᴸ)
      x∉fys = λ x∈fys → x∉ᴸys (∈fin→∈ᴸ x∈fys)

  ∩-finite :
    {DS : DecSetoid σ₁ σ₂} →
      let S′ = DecSetoid.setoid DS
       in (xs ys : List (El S′)) →
            let xs∩ys = intersection {DS = DS} xs ys
             in finite xs ∩ finite ys ≃ finite {S = S′} xs∩ys
  ∩-finite [] ys = ∩-∅ᴸ
  ∩-finite {DS = DS} (x ∷ xs) ys =
    begin
      finite (x ∷ xs) ∩ finite ys
    ≃⟨⟩
      (singleton x ∪ finite xs) ∩ finite ys
    ≃⟨ ∩-over-∪ᴿ ⟩
      singleton x ∩ finite ys ∪ finite xs ∩ finite ys
    ≃⟨ ∪-substᴿ (∩-finite xs ys) ⟩
      singleton x ∩ finite ys ∪ finite (intersection {DS = DS} xs ys)
    ≃⟨ ∩-finite-lemma xs ys ⟩
      finite (intersection {DS = DS} (x ∷ xs) ys)
    ∎
      where open DecMembership DS using () renaming (_∈?_ to _∈ᴸ?_)
