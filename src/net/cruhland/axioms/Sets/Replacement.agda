module net.cruhland.axioms.Sets.Replacement where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Setoid using (find)
open import Data.List.Relation.Unary.All
  using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any
  using (Any; any) renaming (map to map-any)
open import Function using (_∘_; const; flip)
open import Level using (_⊔_; 0ℓ; Setω) renaming (suc to sℓ)
open import Relation.Binary using (DecSetoid)
open import net.cruhland.axioms.Sets.Base using (α; β; σ₁; σ₂; S; SetAxioms)
import net.cruhland.axioms.Sets.Decidable as Decidable
open import net.cruhland.axioms.Sets.Empty using (EmptySet)
import net.cruhland.axioms.Sets.Equality as Equality
import net.cruhland.axioms.Sets.PreFinite as PreFinite
open import net.cruhland.axioms.Sets.Singleton using (SingletonSet)
import net.cruhland.axioms.Sets.Subset as Subset
open import net.cruhland.axioms.Sets.Union using (PairwiseUnion)
open import net.cruhland.models.Logic using
  ( ⊤; _∧?_; ∧-intro; uncurry; ∨-introᴸ; ∨-introᴿ
  ; _↔_; ↔-elimᴸ; ↔-elimᴿ; ⊥-elim; Dec; dec-map
  )
open import net.cruhland.models.Setoid using (DecSetoid₀; El; Setoid; Setoid₀)

module ReplacementDefs (SA : SetAxioms) where
  open SetAxioms SA using (_∈_; PSet; PSet₀)

  record ReplProp
      {S T : Setoid₀} {A : PSet₀ S} (P : El S → El T → Set) : Set where
    open Setoid S using () renaming (_≈_ to _≈ˢ_)
    open Setoid T using () renaming (_≈_ to _≈ᵀ_)

    field
      P-cong : ∀ {x₁ x₂ y₁ y₂} → x₁ ≈ˢ x₂ → y₁ ≈ᵀ y₂ → P x₁ y₁ → P x₂ y₂
      P-most : ∀ {x y} → x ∈ A → P x y → ∀ {z} → P x z → y ≈ᵀ z

  record ReplFun
      {S T : Setoid₀} {A : PSet₀ S} (P : El S → El T → Set) : Set where
    field
      f : El S → El T
      Pf : ∀ {x} → x ∈ A → P x (f x)

  record ReplMembership
      {S T : Setoid₀} {A : PSet₀ S} (x : El T) (P : El S → El T → Set)
        : Set where
    constructor ReplMembership-intro
    field
      {a} : El S
      a∈A : a ∈ A
      Pax : P a x

record Replacement
    (SA : SetAxioms)
    (ES : EmptySet SA)
    (PU : PairwiseUnion SA ES)
    (SS : SingletonSet SA)
      : Setω where
  open Decidable SA using (_∈?_; DecMembership; ∈?-intro)
  open EmptySet ES using (∅; x∉∅)
  open Equality SA using (_≃_; ∈-substᴿ; ≃-sym; ≃-trans; module ≃-Reasoning)
  open ≃-Reasoning
  open PairwiseUnion PU using
    (_∪_; x∈A∪B-elim; x∈A∪B-introᴸ; x∈A∪B-introᴿ; ∪-substᴿ)
  open PreFinite SA ES PU SS using
    (∈ᴸ→∈fin; ∈fin→∈ᴸ; Finite; finite; toList; toList⊆A; same-set)
  open ReplacementDefs SA public using
    (ReplFun; ReplMembership; ReplMembership-intro; ReplProp)
  open SetAxioms SA using (_∈_; PSet; PSet₀)
  open SingletonSet SS using (singleton; x∈sa-elim; x∈sa-intro; a∈sa)
  open Subset SA using (⊆-antisym; ⊆-intro)

  field
    replacement :
      {S T : Setoid₀} (P : El S → El T → Set) (A : PSet₀ S) → ReplProp P →
        PSet₀ T

    x∈rep↔Pax :
      {S T : Setoid₀} {x : El T} {A : PSet₀ S}
        {P : El S → El T → Set} {rp : ReplProp {T = T} P} →
          x ∈ replacement P A rp ↔ ReplMembership {T = T} x P

  x∈rep-elim :
    {S T : Setoid₀} {x : El T} {A : PSet₀ S} {P : El S → El T → Set}
      {rp : ReplProp {T = T} P} → x ∈ replacement P A rp → ReplMembership x P
  x∈rep-elim = ↔-elimᴸ x∈rep↔Pax

  x∈rep-intro :
    {S T : Setoid₀} {x : El T} {A : PSet₀ S} {P : El S → El T → Set}
      {rp : ReplProp {T = T} P} → ReplMembership x P → x ∈ replacement P A rp
  x∈rep-intro = ↔-elimᴿ x∈rep↔Pax

  ReplProp-subst :
    {S T : Setoid₀} {P : El S → El T → Set} {A₁ A₂ : PSet₀ S} →
      A₁ ≃ A₂ → ReplProp {T = T} {A₁} P → ReplProp {A = A₂} P
  ReplProp-subst A₁≃A₂ record { P-cong = P-cong ; P-most = P-most } = record
    { P-cong = P-cong
    ; P-most = λ x∈A₂ Pxy Pxz → P-most (∈-substᴿ (≃-sym A₁≃A₂) x∈A₂) Pxy Pxz
    }

  rep-subst :
    {S T : Setoid₀} {P : El S → El T → Set} {A₁ A₂ : PSet₀ S}
      {rp : ReplProp {T = T} {A₁} P} (A₁≃A₂ : A₁ ≃ A₂) →
        replacement P A₁ rp ≃ replacement P A₂ (ReplProp-subst A₁≃A₂ rp)
  rep-subst {P = P} {A₁} {A₂} {rp} A₁≃A₂ =
      ⊆-antisym (⊆-intro fwd) (⊆-intro rev)
    where
      fwd :
        ∀ {x} → x ∈ replacement P A₁ rp →
          x ∈ replacement P A₂ (ReplProp-subst A₁≃A₂ rp)
      fwd x∈rep₁ =
        let ReplMembership-intro a∈A₁ Pax = x∈rep-elim x∈rep₁
         in x∈rep-intro (ReplMembership-intro (∈-substᴿ A₁≃A₂ a∈A₁) Pax)

      rev :
        ∀ {x} → x ∈ replacement P A₂ (ReplProp-subst A₁≃A₂ rp) →
          x ∈ replacement P A₁ rp
      rev x∈rep₂ =
        let ReplMembership-intro a∈A₂ Pax = x∈rep-elim x∈rep₂
         in x∈rep-intro (ReplMembership-intro (∈-substᴿ (≃-sym A₁≃A₂) a∈A₂) Pax)

  instance
    rep-∈? :
      {{DS : DecSetoid₀}} {T : Setoid₀} →
        let S′ = DecSetoid.setoid DS
         in {A : PSet₀ S′} {P : El S′ → El T → Set} {rp : ReplProp {T = T} P}
              {{_ : Finite A}} {{_ : ∀ {x y} → Dec (P x y)}} →
                DecMembership (replacement {T = T} P A rp)
    rep-∈? {{DS}} {T} {A} {P} {rp} {{finA}} {{decP}} =
      ∈?-intro (dec-map x∈rep-intro x∈rep-elim ReplMembership?)
        where
          open DecSetoid DS using (_≈_)
          open Setoid T using () renaming (refl to ≈ᵀ-refl)

          ReplMembership? : ∀ {x} → Dec (ReplMembership x P)
          ReplMembership? {x} =
            dec-map fwd rev (any (λ a → decP {a} {x}) (toList A))
              where
                fwd : Any (flip P x) (toList A) → ReplMembership x P
                fwd Pax∈ᴸlA =
                  let S′ = DecSetoid.setoid DS
                      ∧-intro a (∧-intro a∈ᴸlA Pax) = find S′ Pax∈ᴸlA
                      a∈fin[lA] = ∈ᴸ→∈fin {DS = DS} a∈ᴸlA
                   in ReplMembership-intro (∈-substᴿ same-set a∈fin[lA]) Pax

                rev : ReplMembership x P → Any (flip P x) (toList A)
                rev record { a = a ; a∈A = a∈A ; Pax = Pax } =
                  let a∈fin[lA] = ∈-substᴿ (≃-sym same-set) a∈A
                      a∈ᴸlA = ∈fin→∈ᴸ {DS = DS} a∈fin[lA]
                      P-cong = ReplProp.P-cong
                   in map-any (λ a≈a′ → P-cong rp a≈a′ ≈ᵀ-refl Pax) a∈ᴸlA

    rep-finite :
      {S T : Setoid₀} {A : PSet₀ S} {P : El S → El T → Set} {rp : ReplProp P}
        {{finA : Finite A}} {{rf : ReplFun {T = T} P}} →
          Finite (replacement P A rp)
    rep-finite {S} {T} {A} {P} {rp} {{finA}} {{rf}} =
      let A≃flA = ≃-sym same-set
          fin-map-xs≃rep-fin-xs = same-xs (toList⊆A A) (ReplProp-subst A≃flA rp)
       in record
         { elements = elements
         ; same-set = ≃-trans fin-map-xs≃rep-fin-xs (≃-sym (rep-subst A≃flA))
         }
      where
        open Setoid S using () renaming
          (_≈_ to _≈ˢ_; refl to ≈ˢ-refl; sym to ≈ˢ-sym)
        open Setoid T using () renaming (_≈_ to _≈ᵀ_; refl to ≈ᵀ-refl)
        f = ReplFun.f rf
        elements = map f (toList A)

        same-xs :
          {xs : List (El S)} (Axs∈A : All (_∈ A) xs)
            (rpl : ReplProp {T = T} P) →
              finite (map f xs) ≃ replacement P (finite xs) rpl
        same-xs []ᴬ rpl = ⊆-antisym (⊆-intro fwd) (⊆-intro rev)
          where
            fwd : ∀ {x} → x ∈ ∅ → x ∈ replacement P ∅ rpl
            fwd x∈∅ = ⊥-elim (x∉∅ x∈∅)

            rev : ∀ {x} → x ∈ replacement P ∅ rpl → x ∈ ∅
            rev x∈rep =
              let ReplMembership-intro a∈∅ Pax = x∈rep-elim x∈rep
               in ⊥-elim (x∉∅ a∈∅)
        same-xs {x ∷ xs} (x∈A ∷ᴬ xs⊆A) rpl =
          begin
            finite (map f (x ∷ xs))
          ≃⟨⟩
            finite (f x ∷ map f xs)
          ≃⟨⟩
            singleton (f x) ∪ finite (map f xs)
          ≃⟨ ∪-substᴿ (same-xs xs⊆A rpl′) ⟩
            singleton (f x) ∪ replacement P (finite xs) rpl′
          ≃⟨ ⊆-antisym (⊆-intro fwd) (⊆-intro rev) ⟩
            replacement P (finite (x ∷ xs)) rpl
          ∎
          where
            rpl′ = record
              { P-cong = ReplProp.P-cong rpl
              ; P-most = λ w∈fxs Pwy Pwz →
                  ReplProp.P-most rpl (x∈A∪B-introᴿ w∈fxs) Pwy Pwz
              }

            fwd :
              ∀ {z} →
                z ∈ singleton (f x) ∪ replacement P (finite xs) rpl′ →
                z ∈ replacement P (finite (x ∷ xs)) rpl
            fwd z∈sfx∪rep′ with x∈A∪B-elim z∈sfx∪rep′
            ... | ∨-introᴸ z∈sfx =
              let fx≈z = x∈sa-elim z∈sfx
                  Pxfx = ReplFun.Pf rf x∈A
                  Pxz = ReplProp.P-cong rpl ≈ˢ-refl fx≈z Pxfx
               in x∈rep-intro (ReplMembership-intro (x∈A∪B-introᴸ a∈sa) Pxz)
            ... | ∨-introᴿ z∈rep′ =
              let ReplMembership-intro x∈fxs Pxz = x∈rep-elim z∈rep′
               in x∈rep-intro (ReplMembership-intro (x∈A∪B-introᴿ x∈fxs) Pxz)

            rev :
              ∀ {z} →
                z ∈ replacement P (finite (x ∷ xs)) rpl →
                z ∈ singleton (f x) ∪ replacement P (finite xs) rpl′
            rev z∈rep with x∈rep-elim z∈rep
            ... | ReplMembership-intro a∈f[x∷xs] Paz with x∈A∪B-elim a∈f[x∷xs]
            ... | ∨-introᴸ a∈sx =
              let x≈a = x∈sa-elim a∈sx
                  Pxz = ReplProp.P-cong rpl (≈ˢ-sym x≈a) ≈ᵀ-refl Paz
                  Px[fx] = ReplFun.Pf rf x∈A
                  fx≈z = ReplProp.P-most rpl (x∈A∪B-introᴸ a∈sa) Px[fx] Pxz
               in x∈A∪B-introᴸ (x∈sa-intro fx≈z)
            ... | ∨-introᴿ a∈fxs =
              x∈A∪B-introᴿ (x∈rep-intro (ReplMembership-intro a∈fxs Paz))
