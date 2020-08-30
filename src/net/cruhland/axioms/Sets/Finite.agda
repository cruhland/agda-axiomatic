open import net.cruhland.axioms.Sets.Base using (SetAxioms)
open import net.cruhland.axioms.Sets.Complement using (Complement)
open import net.cruhland.axioms.Sets.Difference using (Difference)
open import net.cruhland.axioms.Sets.Empty using (EmptySet)
open import net.cruhland.axioms.Sets.Intersection using (PairwiseIntersection)
open import net.cruhland.axioms.Sets.Pair using (PairSet)
import net.cruhland.axioms.Sets.PreFinite as PreFinite
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
  open SetAxioms SA using (_∈_; _∉_; PSet; PSet₀; PSet-cong)
  open Complement CM using (∁; ∁-∈?)
  open Difference SD using (_∖_)
  open EmptySet ES using (∅; x∉∅)
  open PairSet PS using (pair)
  open PairwiseIntersection PI using
    (_∩_; ∩-comm; x∈A∩B-elim; x∈A∩B-elimᴸ; x∈A∩B-intro₂; ∩-substᴸ)
  open PairwiseUnion PU using
    ( _∪_; ∪-∅ᴸ; ∪-∅ᴿ; ∪-assoc; x∈A∪B-elim
    ; x∈A∪B-introᴸ; x∈A∪B-introᴿ; ∪-substᴸ; ∪-substᴿ
    )
  open PreFinite SA ES PU SS using (∈fin→∈ᴸ; Finite; finite; toList; same-set)
  open SingletonSet SS using (singleton; a∈sa; x∈sa-elim; x∈sa-intro)

  open import Data.List using ([]; _∷_; _++_; filter; foldr; List)
  import Data.List.Membership.DecSetoid as DecSetoidᴸ
  open import Data.List.Relation.Unary.All
    using (All; all; lookupAny) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
  open import Data.List.Relation.Unary.Any using (here; there)
  open import Function using (_∘_)
  open import Level using (_⊔_)
  open import Relation.Binary using (DecSetoid)
  open import net.cruhland.axioms.Sets.Base using
    (α; β; El; S; DecSetoid₀; Setoid; Setoid₀; σ₁; σ₂)
  open import net.cruhland.axioms.Sets.Decidable SA using (_∈?_; DecMembership)
  open import net.cruhland.axioms.Sets.Equality SA using
    (_≃_; ≃-refl; ∈-substᴿ; ≃-sym; ≃-trans; module ≃-Reasoning)
  open ≃-Reasoning
  open import net.cruhland.axioms.Sets.Properties SA CM ES PI PS PU SD SS using
    (A⊆∅→A≃∅; ∪⊆-elimᴿ; pab≃sa∪sb; ∩-∅ᴸ; ∩-over-∪ᴿ; A∖B≃A∩∁B)
  open import net.cruhland.axioms.Sets.Subset SA using
    (_⊆_; ≃→⊆ᴸ; ≃→⊆ᴿ; ⊆-antisym; ⊆-intro; ⊆-substᴸ)
  open import net.cruhland.models.Logic using
    ( _∧_; _∧?_; ∧-intro; uncurry
    ; _∨_; ∨-introᴸ; ∨-introᴿ
    ; ⊥-elim; Dec; dec-map; no; yes
    )

  ∪-finite :
    {S : Setoid₀} (xs ys : List (El S)) →
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
    {S : Setoid₀} {x : El S} (xs : List (El S)) (A : PSet₀ S) →
      {{_ : DecMembership A}} →
        singleton x ∩ A ∪ finite (xs ∩ᴾ A) ≃ finite ((x ∷ xs) ∩ᴾ A)
  ∩-finite-lemma {S = S} {x} xs A {{decMem}} with (x ∈? A) {{decMem}}
  ... | yes x∈A = ∪-substᴸ (singleton-∈∩ᴸ x∈A)
  ... | no x∉A = ≃-trans (∪-substᴸ (singleton-∉∩ᴸ x∉A)) ∪-∅ᴸ

  ∩-finite :
    {S : Setoid₀} (xs : List (El S)) (A : PSet₀ S) →
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

  instance
    Finite-∅ : Finite (∅ {S = S})
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
      {S : Setoid₀} {A B : PSet₀ S} {{_ : Finite A}} {{_ : Finite B}} →
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
      {A B : PSet₀ S} {{_ : Finite A}} {{_ : DecMembership B}} →
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

    Finite-∩ᴿ :
      {A B : PSet₀ S} {{_ : DecMembership A}} {{_ : Finite B}} →
        Finite (A ∩ B)
    Finite-∩ᴿ {A = A} {B} = record { elements = ∩-list ; same-set = list≃∩ }
      where
        ∩-list = toList B ∩ᴾ A

        list≃∩ =
          begin
            finite ∩-list
          ≃⟨⟩
            finite (toList B ∩ᴾ A)
          ≃⟨ same-set ⟩
            B ∩ A
          ≃⟨ ∩-comm ⟩
            A ∩ B
          ∎

    Finite-∖ :
      {A B : PSet₀ S} {{_ : Finite A}} {{_ : DecMembership B}} →
        Finite (A ∖ B)
    Finite-∖ {A = A} {B} = record { elements = ∖-list ; same-set = list≃∖ }
      where
        ∖-list = toList A ∩ᴾ ∁ B

        list≃∖ =
          begin
            finite ∖-list
          ≃⟨⟩
            finite (toList A ∩ᴾ ∁ B)
          ≃⟨ same-set {{Finite-∩ᴸ}} ⟩
            A ∩ ∁ B
          ≃˘⟨ A∖B≃A∩∁B ⟩
            A ∖ B
          ∎

  module Subsetᴸ {DS : DecSetoid₀} where
    open DecSetoidᴸ DS using () renaming (_∈_ to _∈ᴸ_)
    S′ = DecSetoid.setoid DS
    open Setoid S′ using (_≈_) renaming (sym to ≈-sym)

    infix 4 _⊆ᴸ_ _⊆ᴸ?_ _⊆?_ _≃?_

    _⊆ᴸ_ : List (El S′) → PSet₀ S′ → Set
    xs ⊆ᴸ B = All (_∈ B) xs

    _⊆ᴸ?_ :
      (xs : List (El S′)) (B : PSet₀ S′) →
        {{_ : DecMembership B}} → Dec (xs ⊆ᴸ B)
    xs ⊆ᴸ? B = all (_∈? B) xs

    ⊆ᴸ→⊆ :
      {A B : PSet₀ S′} {{_ : Finite A}} → toList A ⊆ᴸ B → A ⊆ B
    ⊆ᴸ→⊆ {A = A} {B} A⊆ᴸB =
      ⊆-intro (x∈ᴸlA→x∈B ∘ (∈fin→∈ᴸ {DS = DS}) ∘ ∈-substᴿ (≃-sym same-set))
        where
          x∈ᴸlA→x∈B : ∀ {x} → x ∈ᴸ toList A → x ∈ B
          x∈ᴸlA→x∈B x∈ᴸlA with lookupAny A⊆ᴸB x∈ᴸlA
          ... | ∧-intro lookup∈B x≈lookup = PSet-cong (≈-sym x≈lookup) lookup∈B

    ⊆fin→⊆ᴸ :
      {xs : List (El S′)} {A : PSet₀ S′} → finite {S = S′} xs ⊆ A → xs ⊆ᴸ A
    ⊆fin→⊆ᴸ {xs = []} fxs⊆A = []ᴬ
    ⊆fin→⊆ᴸ {xs = x ∷ xs} sx∪fxs⊆A@(⊆-intro x∈fxs→x∈A) = x∈A ∷ᴬ xs⊆ᴸA
      where
        x∈A = x∈fxs→x∈A (x∈A∪B-introᴸ a∈sa)
        xs⊆ᴸA = ⊆fin→⊆ᴸ (∪⊆-elimᴿ sx∪fxs⊆A)

    ⊆→⊆ᴸ :
      {A B : PSet₀ S′} {{_ : Finite A}} → A ⊆ B → toList A ⊆ᴸ B
    ⊆→⊆ᴸ {{finA}} = ⊆fin→⊆ᴸ ∘ ⊆-substᴸ (≃-sym same-set)

    _⊆?_ :
      (A B : PSet₀ S′) →
        {{_ : Finite A}} {{_ : DecMembership B}} → Dec (A ⊆ B)
    A ⊆? B = dec-map ⊆ᴸ→⊆ ⊆→⊆ᴸ (toList A ⊆ᴸ? B)

    _≃?_ :
      (A B : PSet₀ S′) →
      {{_ : DecMembership A}} {{_ : DecMembership B}} →
      {{_ : Finite A}} {{_ : Finite B}} →
      Dec (A ≃ B)
    A ≃? B = dec-map (uncurry ⊆-antisym) ≃→⊆⊇ ((A ⊆? B) ∧? (B ⊆? A))
      where
        ≃→⊆⊇ = λ A≃B → ∧-intro (≃→⊆ᴸ A≃B) (≃→⊆ᴿ A≃B)
