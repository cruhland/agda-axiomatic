open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.axioms.Sets.Complement using (Complement)
open import net.cruhland.axioms.Sets.Difference using (Difference)
open import net.cruhland.axioms.Sets.Empty using (EmptySet)
open import net.cruhland.axioms.Sets.Intersection using (PairwiseIntersection)
open import net.cruhland.axioms.Sets.Pair using (PairSet)
open import net.cruhland.axioms.Sets.Union using (PairwiseUnion)
open import net.cruhland.axioms.Sets.Singleton using (SingletonSet)

module net.cruhland.axioms.Sets.Finite
    (SA : SetAxioms)
    (CM : Complement SA)
    (ES : EmptySet SA)
    (PI : PairwiseIntersection SA)
    (PS : PairSet SA)
    (PU : PairwiseUnion SA ES)
    (SD : Difference SA)
    (SS : SingletonSet SA) where
  open SetAxioms SA using (_∈_; _∉_; PSet; PSet-cong)
  open Complement CM using (∁; ∁-∈?)
  open Difference SD using (_∖_)
  open EmptySet ES using (∅; x∉∅)
  open PairSet PS using (pair)
  open PairwiseIntersection PI using
    (_∩_; x∈A∩B-elim; x∈A∩B-elimᴸ; x∈A∩B-intro₂; ∩-substᴸ)
  open PairwiseUnion PU using
    ( _∪_; ∪-∅ᴸ; ∪-∅ᴿ; ∪-assoc; x∈A∪B-elim
    ; x∈A∪B-introᴸ; x∈A∪B-introᴿ; ∪-substᴸ; ∪-substᴿ
    )
  open SingletonSet SS using (singleton; a∈sa; x∈sa-elim; x∈sa-intro)

  open import Data.Bool using (false; true)
  open import Data.List using ([]; _∷_; _++_; any; filter; foldr; List)
  import Data.List.Membership.DecSetoid as DecSetoidᴸ
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
  open import net.cruhland.axioms.Sets.Base using (α; β; El; S; Setoid; σ₁; σ₂)
  open import net.cruhland.axioms.Sets.Decidable SA using (_∈?_; DecMembership)
  open import net.cruhland.axioms.Sets.Equality SA using
    (_≃_; ≃-refl; ≃-sym; ≃-trans; module ≃-Reasoning)
  open ≃-Reasoning
  open import net.cruhland.axioms.Sets.Properties SA CM ES PI PS PU SD SS using
    (A⊆∅→A≃∅; ∪⊆-elimᴿ; pab≃sa∪sb; ∩-∅ᴸ; ∩-over-∪ᴿ; A∖B≃A∩∁B)
  open import net.cruhland.axioms.Sets.Subset SA using
    (_⊆_; ≃→⊆ᴸ; ≃→⊆ᴿ; ⊆-antisym; ⊆-intro)
  open import net.cruhland.models.Logic using
    ( _∧_; _∧?_; ∧-elimᴸ; ∧-elimᴿ; ∧-intro; uncurry
    ; _∨_; ∨-introᴸ; ∨-introᴿ
    ; ⊥-elim; _because_; Dec; dec-map; does; ofⁿ; ofʸ
    )

  finite : {S : Setoid σ₁ σ₂} → List (El S) → PSet S σ₂
  finite = foldr (λ x acc → singleton x ∪ acc) ∅

  ∪-finite :
    {S : Setoid σ₁ σ₂} (xs ys : List (El S)) →
      finite {S = S} xs ∪ finite ys ≃ finite (xs ++ ys)
  ∪-finite [] ys = ∪-∅ᴸ
  ∪-finite (x ∷ xs) ys = ≃-trans ∪-assoc (∪-substᴿ (∪-finite xs ys))

  infixl 7 _∩ᴾ_

  _∩ᴾ_ :
    List (El S) → (A : PSet S α) → {{_ : DecMembership A}} → List (El S)
  xs ∩ᴾ A = filter (_∈? A) xs

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

  ∩-finite-lemma :
    {S : Setoid σ₁ σ₂} {x : El S} (xs : List (El S)) (A : PSet S σ₂) →
      {{_ : DecMembership A}} →
        singleton x ∩ A ∪ finite (xs ∩ᴾ A) ≃ finite ((x ∷ xs) ∩ᴾ A)
  ∩-finite-lemma {S = S} {x} xs A {{decMem}} with (x ∈? A) {{decMem}}
  ... | true because ofʸ x∈A = ∪-substᴸ (singleton-∈∩ᴸ x∈A)
  ... | false because ofⁿ x∉A = ≃-trans (∪-substᴸ (singleton-∉∩ᴸ x∉A)) ∪-∅ᴸ

  ∩-finite :
    {S : Setoid σ₁ σ₂} (xs : List (El S)) (A : PSet S σ₂) →
      {{_ : DecMembership A}} → finite xs ∩ A ≃ finite (xs ∩ᴾ A)
  ∩-finite [] A = ∩-∅ᴸ
  ∩-finite (x ∷ xs) A =
    begin
      finite (x ∷ xs) ∩ A
    ≃⟨⟩
      (singleton x ∪ finite xs) ∩ A
    ≃⟨ ∩-over-∪ᴿ ⟩
      singleton x ∩ A ∪ finite xs ∩ A
    ≃⟨ ∪-substᴿ (∩-finite xs A) ⟩
      singleton x ∩ A ∪ finite (xs ∩ᴾ A)
    ≃⟨ ∩-finite-lemma xs A ⟩
      finite ((x ∷ xs) ∩ᴾ A)
    ∎

  record Finite {S : Setoid σ₁ σ₂} (A : PSet S σ₂) : Set (σ₁ ⊔ σ₂) where
    field
      elements : List (El S)
      same-set : finite elements ≃ A

  open Finite {{...}} public using (elements; same-set)

  toList : (A : PSet S σ₂) {{_ : Finite A}} → List (El S)
  toList A = elements

  instance
    Finite-∅ : Finite (∅ {S = S} {α})
    Finite-∅ = record { elements = [] ; same-set = ≃-refl }

    Finite-singleton : ∀ {a} → Finite (singleton {S = S} a)
    Finite-singleton {a = a} = record { elements = a ∷ [] ; same-set = ∪-∅ᴿ }

    Finite-pair : ∀ {a b} → Finite (pair {S = S} a b)
    Finite-pair {a = a} {b} = record { elements = pair-list ; same-set = list≃pair }
      where
        pair-list = a ∷ b ∷ []
        list≃pair =
          begin
            finite pair-list
          ≃⟨⟩
            finite (a ∷ b ∷ [])
          ≃⟨⟩
            singleton a ∪ (singleton b ∪ ∅)
          ≃˘⟨ ∪-assoc ⟩
            singleton a ∪ singleton b ∪ ∅
          ≃⟨ ∪-∅ᴿ ⟩
            singleton a ∪ singleton b
          ≃˘⟨ pab≃sa∪sb ⟩
            pair a b
          ∎

    Finite-∪ :
      {A : PSet S α} {B : PSet S α} {{_ : Finite A}} {{_ : Finite B}} →
        Finite (A ∪ B)
    Finite-∪ {A = A} {B} = record { elements = ∪-list ; same-set = list≃∪ }
      where
        ∪-list = toList A ++ toList B

        list≃∪ =
          begin
            finite ∪-list
          ≃⟨⟩
            finite (toList A ++ toList B)
          ≃˘⟨ ∪-finite (toList A) (toList B) ⟩
            finite (toList A) ∪ finite (toList B)
          ≃⟨ ∪-substᴸ same-set ⟩
            A ∪ finite (toList B)
          ≃⟨ ∪-substᴿ same-set ⟩
            A ∪ B
          ∎

    Finite-∩ᴸ :
      {A : PSet S α} {B : PSet S α} {{_ : Finite A}} {{_ : DecMembership B}} →
        Finite (A ∩ B)
    Finite-∩ᴸ {A = A} {B} = record { elements = ∩-list ; same-set = list≃∩ }
      where
        ∩-list = toList A ∩ᴾ B

        list≃∩ =
          begin
            finite ∩-list
          ≃⟨⟩
            finite (toList A ∩ᴾ B)
          ≃˘⟨ ∩-finite (toList A) B ⟩
            finite (toList A) ∩ B
          ≃⟨ ∩-substᴸ same-set ⟩
            A ∩ B
          ∎

  module Subsetᴸ {DS : DecSetoid σ₁ σ₂} where
    open DecSetoidᴸ DS using () renaming (_∈_ to _∈ᴸ_; _∈?_ to _∈ᴸ?_)
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

    infix 4 _⊆ᴸ_ _⊆ᴾ_ _⊆ᴸ?_ _⊆ᴾ?_ _⊆?_ _⊆′?_ _≃?_

    _⊆ᴸ_ : List (El S′) → List (El S′) → Set (σ₁ ⊔ σ₂)
    _⊆ᴸ_ xs ys = All (_∈ᴸ ys) xs

    _⊆ᴾ_ : List (El S′) → PSet S′ α → Set (σ₁ ⊔ α)
    _⊆ᴾ_ xs A = All (_∈ A) xs

    _⊆ᴸ?_ : Decidable _⊆ᴸ_
    _⊆ᴸ?_ xs ys = all (_∈ᴸ? ys) xs

    _⊆ᴾ?_ :
      (xs : List (El S′)) → (A : PSet S′ α) →
        {{_ : DecMembership A}} → Dec (xs ⊆ᴾ A)
    _⊆ᴾ?_ xs A = all (_∈? A) xs

    ⊆ᴸ→⊆fin : {xs ys : List (El S′)} → xs ⊆ᴸ ys → finite {S = S′} xs ⊆ finite ys
    ⊆ᴸ→⊆fin {xs} {ys} xs⊆ᴸys = ⊆-intro (∈ᴸ→∈fin ∘ x∈ᴸxs→x∈ᴸys ∘ ∈fin→∈ᴸ)
      where
        open Setoid S′ using (_≈_; trans)

        x∈ᴸxs→x∈ᴸys : ∀ {x} → x ∈ᴸ xs → x ∈ᴸ ys
        x∈ᴸxs→x∈ᴸys x∈ᴸxs with lookupAny xs⊆ᴸys x∈ᴸxs
        ... | ∧-intro any[lookup≈]ys x≈lookup =
          map (trans x≈lookup) any[lookup≈]ys

    ⊆ᴾ→⊆fin :
      {xs : List (El S′)} {A : PSet S′ α} → xs ⊆ᴾ A → finite {S = S′} xs ⊆ A
    ⊆ᴾ→⊆fin {xs = xs} {A} xs⊆ᴾA = ⊆-intro (x∈ᴸxs→x∈A ∘ ∈fin→∈ᴸ)
      where
        x∈ᴸxs→x∈A : ∀ {x} → x ∈ᴸ xs → x ∈ A
        x∈ᴸxs→x∈A x∈ᴸxs with lookupAny xs⊆ᴾA x∈ᴸxs
        ... | ∧-intro lookup∈A x≈lookup = PSet-cong (≈-sym x≈lookup) lookup∈A

    ⊆fin→⊆ᴸ : {xs ys : List (El S′)} → finite {S = S′} xs ⊆ finite ys → xs ⊆ᴸ ys
    ⊆fin→⊆ᴸ {xs = []} fxs⊆fys = []ᴬ
    ⊆fin→⊆ᴸ {xs = x ∷ xs} sx∪fxs⊆fys@(⊆-intro x∈fxs→x∈fys) = x∈ᴸys ∷ᴬ xs⊆ᴸys
      where
        x∈ᴸys = ∈fin→∈ᴸ (x∈fxs→x∈fys (x∈A∪B-introᴸ a∈sa))
        xs⊆ᴸys = ⊆fin→⊆ᴸ (∪⊆-elimᴿ sx∪fxs⊆fys)

    ⊆fin→⊆ᴾ :
      {xs : List (El S′)} {A : PSet S′ α} → finite {S = S′} xs ⊆ A → xs ⊆ᴾ A
    ⊆fin→⊆ᴾ {xs = []} fxs⊆A = []ᴬ
    ⊆fin→⊆ᴾ {xs = x ∷ xs} sx∪fxs⊆A@(⊆-intro x∈fxs→x∈A) = x∈A ∷ᴬ xs⊆ᴾA
      where
        x∈A = x∈fxs→x∈A (x∈A∪B-introᴸ a∈sa)
        xs⊆ᴾA = ⊆fin→⊆ᴾ (∪⊆-elimᴿ sx∪fxs⊆A)

    _⊆′?_ : (xs ys : List (El S′)) → Dec (finite {S = S′} xs ⊆ finite ys)
    xs ⊆′? ys = dec-map ⊆ᴸ→⊆fin ⊆fin→⊆ᴸ (xs ⊆ᴸ? ys)

    _⊆?_ :
      (xs : List (El S′)) (A : PSet S′ α) {{_ : DecMembership A}} →
        Dec (finite {S = S′} xs ⊆ A)
    xs ⊆? A = dec-map ⊆ᴾ→⊆fin ⊆fin→⊆ᴾ (xs ⊆ᴾ? A)

    _≃?_ : (xs ys : List (El S′)) → Dec (finite {S = S′} xs ≃ finite ys)
    xs ≃? ys = dec-map (uncurry ⊆-antisym) ≃→⊆⊇ ((xs ⊆′? ys) ∧? (ys ⊆′? xs))
      where
        ≃→⊆⊇ = λ A≃B → ∧-intro (≃→⊆ᴸ A≃B) (≃→⊆ᴿ A≃B)

  ∖-finite :
    {S : Setoid σ₁ σ₂} (xs : List (El S)) (A : PSet S σ₂) →
      {{_ : DecMembership A}} → finite xs ∖ A ≃ finite (xs ∩ᴾ ∁ A)
  ∖-finite xs A = ≃-trans A∖B≃A∩∁B (∩-finite xs (∁ A))
